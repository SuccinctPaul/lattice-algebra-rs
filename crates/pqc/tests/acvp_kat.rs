//! Official ACVP (NIST) known-answer tests for ML-DSA (FIPS 204).
//!
//! The fixtures under `tests/data/` are extracted from the official
//! ACVP-Server sample vectors (see `tests/data/README.md` for provenance and
//! the extraction script). Byte-exact equality is asserted for:
//!
//! - `keyGen`: seed → pk, sk (all three parameter sets);
//! - `sigGen` / `sigVer`, pure mode: deterministic and randomized signing
//!   (the randomized vectors fix the `rnd` input), accept and reject
//!   verification including empty/absent contexts;
//! - `sigGen` / `sigVer`, internal interface: signing/verifying a
//!   precomputed message representative μ (ACVP "external mu" mode), plus
//!   internal groups whose μ is H(tr ‖ message) without the pure-mode
//!   prefix (the ACVP-Server reference's `Sign(sk, m, rnd)` convention);
//! - `sigGen` / `sigVer`, external preHash groups: the OID-separated
//!   pre-hash composition `M' = 1 ‖ |ctx| ‖ ctx ‖ OID ‖ PH(M)` (ACVP draft
//!   variant — *not* the final FIPS 204 HashML-DSA composition, which the
//!   crate exposes as `sign_hash_mldsa`/`verify_hash_mldsa`; the harness
//!   composes the ACVP M' via `sign_m_prime`/`verify_m_prime`).
//!
//! These tests close the "official KAT/ACVP alignment" gap: any deviation in
//! the hash chain, `ExpandA`/`RejNTTPoly`, the samplers, the FIPS 204 NTT
//! convention, the rounding/hint logic or the wire encodings shows up here.

use pqc::mldsa::params::{MlDsa44, MlDsa65, MlDsa87, MlDsaParams};
use pqc::mldsa::{
    keygen_seed, sign_deterministic, sign_m_prime, sign_mu, sign_with_randomness, verify_core,
    verify_m_prime, verify_mu, SigningKey, VerifyingKey,
};
use serde_json::Value;
use sha2::Digest;
use sha2::{Sha224, Sha256, Sha384, Sha512, Sha512_224, Sha512_256};
use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Sha3_224, Sha3_256, Sha3_384, Sha3_512, Shake128, Shake256};

/// SHAKE256(x) squeezed to 64 bytes (the internal hash H of FIPS 204).
fn shake256_64(x: &[u8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    let mut s = Shake256::default();
    s.update(x);
    s.finalize_xof().read(&mut out);
    out
}

/// μ = H(tr ‖ m) — the internal-interface message representative.
fn mu_of(tr: &[u8], m: &[u8]) -> [u8; 64] {
    let mut s = Shake256::default();
    s.update(tr);
    s.update(m);
    let mut out = [0u8; 64];
    s.finalize_xof().read(&mut out);
    out
}

/// `PH(M)` with the ACVP-Server output lengths (its `ShaAttributes`):
/// the digest size for SHA-2/SHA-3, 256 bits for SHAKE-128 and 512 bits
/// for SHAKE-256 (the "XOF as PSS hash" lengths).
fn acvp_ph(hash_alg: &str, msg: &[u8]) -> Vec<u8> {
    match hash_alg {
        "SHA2-224" => Sha224::digest(msg).to_vec(),
        "SHA2-256" => Sha256::digest(msg).to_vec(),
        "SHA2-384" => Sha384::digest(msg).to_vec(),
        "SHA2-512" => Sha512::digest(msg).to_vec(),
        "SHA2-512/224" => Sha512_224::digest(msg).to_vec(),
        "SHA2-512/256" => Sha512_256::digest(msg).to_vec(),
        "SHA3-224" => Sha3_224::digest(msg).to_vec(),
        "SHA3-256" => Sha3_256::digest(msg).to_vec(),
        "SHA3-384" => Sha3_384::digest(msg).to_vec(),
        "SHA3-512" => Sha3_512::digest(msg).to_vec(),
        "SHAKE-128" => {
            let mut x = Shake128::default();
            x.update(msg);
            let mut out = vec![0u8; 32];
            x.finalize_xof().read(&mut out);
            out
        }
        "SHAKE-256" => {
            let mut x = Shake256::default();
            x.update(msg);
            let mut out = vec![0u8; 64];
            x.finalize_xof().read(&mut out);
            out
        }
        other => panic!("unhandled ACVP hashAlg {other}"),
    }
}

/// Full DER hash OIDs as carried by ACVP's `HashFunction.OID` (2.16.840.1.101.3.4.2.x).
fn acvp_oid(hash_alg: &str) -> Vec<u8> {
    let tail: u8 = match hash_alg {
        "SHA2-224" => 0x04,
        "SHA2-256" => 0x01,
        "SHA2-384" => 0x02,
        "SHA2-512" => 0x03,
        "SHA2-512/224" => 0x05,
        "SHA2-512/256" => 0x06,
        "SHA3-224" => 0x07,
        "SHA3-256" => 0x08,
        "SHA3-384" => 0x09,
        "SHA3-512" => 0x0A,
        "SHAKE-128" => 0x0B,
        "SHAKE-256" => 0x0C,
        other => panic!("unhandled ACVP hashAlg {other}"),
    };
    vec![
        0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, tail,
    ]
}

/// The ACVP preHash composition: `M' = 1 ‖ |ctx| ‖ ctx ‖ OID ‖ PH(M)`.
fn acvp_prehash_m_prime(hash_alg: &str, ctx: &[u8], msg: &[u8]) -> Vec<u8> {
    let mut m_prime = Vec::with_capacity(2 + ctx.len() + 11 + 64);
    m_prime.push(1u8);
    m_prime.push(ctx.len() as u8);
    m_prime.extend_from_slice(ctx);
    m_prime.extend_from_slice(&acvp_oid(hash_alg));
    m_prime.extend_from_slice(&acvp_ph(hash_alg, msg));
    m_prime
}

fn fixture(name: &str) -> Vec<Value> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");
    let text = std::fs::read_to_string(format!("{path}/{name}.json"))
        .unwrap_or_else(|e| panic!("missing ACVP fixture {name}.json (run extract_acvp.py): {e}"));
    let doc: Value = serde_json::from_str(&text).expect("fixture is valid JSON");
    doc["testCases"]
        .as_array()
        .expect("fixture carries testCases")
        .clone()
}

fn hex_decode(s: &str) -> Vec<u8> {
    assert!(s.len() % 2 == 0, "odd-length hex string");
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).expect("valid hex"))
        .collect()
}

fn ctx_of(rec: &Value) -> Vec<u8> {
    match rec["context"].as_str() {
        Some(s) => hex_decode(s),
        None => Vec::new(),
    }
}

fn seed32(rec: &Value, field: &str) -> [u8; 32] {
    hex_decode(rec[field].as_str().expect(field))
        .try_into()
        .expect("32-byte seed")
}

fn check_keygen<P: MlDsaParams, const K: usize, const L: usize>(rec: &Value) {
    let id = (
        rec["parameterSet"].as_str().unwrap(),
        rec["tcId"].as_i64().unwrap(),
    );
    let seed = seed32(rec, "seed");
    let (sk, vk) = keygen_seed::<P, K, L>(&seed);
    let want_pk = hex_decode(rec["pk"].as_str().unwrap());
    let want_sk = hex_decode(rec["sk"].as_str().unwrap());
    assert_eq!(vk.to_bytes(), want_pk, "pk mismatch for {id:?}");
    assert_eq!(sk.to_bytes(), want_sk, "sk mismatch for {id:?}");
}

fn check_siggen<P: MlDsaParams, const K: usize, const L: usize>(rec: &Value) {
    let id = (
        rec["parameterSet"].as_str().unwrap(),
        rec["tcId"].as_i64().unwrap(),
    );
    let sk =
        SigningKey::<P>::from_bytes(&hex_decode(rec["sk"].as_str().unwrap())).expect("valid sk");
    let msg = hex_decode(rec["message"].as_str().unwrap_or(""));
    let ctx = ctx_of(rec);
    let want = hex_decode(rec["signature"].as_str().unwrap());
    let got = if rec["deterministic"].as_bool().unwrap_or(true) {
        sign_deterministic::<P, K, L>(&sk, &ctx, &msg)
    } else {
        sign_with_randomness::<P, K, L>(&sk, &ctx, &msg, &seed32(rec, "rnd"))
    };
    assert_eq!(got, want, "signature mismatch for {id:?}");
}

fn check_sigver<P: MlDsaParams, const K: usize, const L: usize>(rec: &Value) {
    let id = (
        rec["parameterSet"].as_str().unwrap(),
        rec["tcId"].as_i64().unwrap(),
    );
    let vk =
        VerifyingKey::<P>::from_bytes(&hex_decode(rec["pk"].as_str().unwrap())).expect("valid pk");
    let msg = hex_decode(rec["message"].as_str().unwrap_or(""));
    let ctx = ctx_of(rec);
    let sigma = hex_decode(rec["signature"].as_str().unwrap());
    let accepted = verify_core::<P, K, L>(&vk, &ctx, &msg, &sigma);
    assert_eq!(
        accepted,
        rec["testPassed"].as_bool().unwrap(),
        "verify verdict mismatch for {id:?}"
    );
}

/// Deterministic signing fixes `rnd = 0^32`; randomized vectors carry it.
fn rnd_of(rec: &Value) -> [u8; 32] {
    if rec["deterministic"].as_bool().unwrap_or(true) {
        [0u8; 32]
    } else {
        seed32(rec, "rnd")
    }
}

fn check_siggen_internal<P: MlDsaParams, const K: usize, const L: usize>(rec: &Value) {
    let id = (
        rec["parameterSet"].as_str().unwrap(),
        rec["tcId"].as_i64().unwrap(),
    );
    let sk_bytes = hex_decode(rec["sk"].as_str().unwrap());
    let sk = SigningKey::<P>::from_bytes(&sk_bytes).expect("valid sk");
    let rnd = rnd_of(rec);
    let want = hex_decode(rec["signature"].as_str().unwrap());
    // externalMu groups hand over the 64-byte μ directly; the other internal
    // groups hash the raw message with tr (no pure-mode prefix), where tr is
    // the third field of skEncode (rho ‖ k ‖ tr ‖ ...).
    let mu: [u8; 64] = match rec["mu"].as_str() {
        Some(mu_hex) => hex_decode(mu_hex).try_into().expect("64-byte mu"),
        None => {
            let msg = hex_decode(rec["message"].as_str().unwrap_or(""));
            mu_of(&sk_bytes[64..128], &msg)
        }
    };
    assert_eq!(
        sign_mu::<P, K, L>(&sk, &mu, &rnd),
        want,
        "internal sigGen mismatch for {id:?}"
    );
}

fn check_sigver_internal<P: MlDsaParams, const K: usize, const L: usize>(rec: &Value) {
    let id = (
        rec["parameterSet"].as_str().unwrap(),
        rec["tcId"].as_i64().unwrap(),
    );
    let pk = hex_decode(rec["pk"].as_str().unwrap());
    let vk = VerifyingKey::<P>::from_bytes(&pk).expect("valid pk");
    let sigma = hex_decode(rec["signature"].as_str().unwrap());
    let mu: [u8; 64] = match rec["mu"].as_str() {
        Some(mu_hex) => hex_decode(mu_hex).try_into().expect("64-byte mu"),
        None => {
            let msg = hex_decode(rec["message"].as_str().unwrap_or(""));
            // tr' = H(pk), recomputed from the public key (pkEncode output).
            mu_of(&shake256_64(&pk), &msg)
        }
    };
    assert_eq!(
        verify_mu::<P, K, L>(&vk, &mu, &sigma),
        rec["testPassed"].as_bool().unwrap(),
        "internal sigVer verdict mismatch for {id:?}"
    );
}

fn check_siggen_prehash<P: MlDsaParams, const K: usize, const L: usize>(rec: &Value) {
    let id = (
        rec["parameterSet"].as_str().unwrap(),
        rec["tcId"].as_i64().unwrap(),
    );
    let sk =
        SigningKey::<P>::from_bytes(&hex_decode(rec["sk"].as_str().unwrap())).expect("valid sk");
    let msg = hex_decode(rec["message"].as_str().unwrap_or(""));
    let ctx = ctx_of(rec);
    let rnd = rnd_of(rec);
    let want = hex_decode(rec["signature"].as_str().unwrap());
    let m_prime = acvp_prehash_m_prime(rec["hashAlg"].as_str().unwrap(), &ctx, &msg);
    assert_eq!(
        sign_m_prime::<P, K, L>(&sk, &m_prime, &rnd),
        want,
        "preHash sigGen mismatch for {id:?}"
    );
}

fn check_sigver_prehash<P: MlDsaParams, const K: usize, const L: usize>(rec: &Value) {
    let id = (
        rec["parameterSet"].as_str().unwrap(),
        rec["tcId"].as_i64().unwrap(),
    );
    let vk =
        VerifyingKey::<P>::from_bytes(&hex_decode(rec["pk"].as_str().unwrap())).expect("valid pk");
    let msg = hex_decode(rec["message"].as_str().unwrap_or(""));
    let ctx = ctx_of(rec);
    let sigma = hex_decode(rec["signature"].as_str().unwrap());
    let m_prime = acvp_prehash_m_prime(rec["hashAlg"].as_str().unwrap(), &ctx, &msg);
    assert_eq!(
        verify_m_prime::<P, K, L>(&vk, &m_prime, &sigma),
        rec["testPassed"].as_bool().unwrap(),
        "preHash sigVer verdict mismatch for {id:?}"
    );
}

macro_rules! dispatch {
    ($rec:expr, $f:ident) => {
        match $rec["parameterSet"].as_str().unwrap() {
            "ML-DSA-44" => $f::<MlDsa44, 4, 4>($rec),
            "ML-DSA-65" => $f::<MlDsa65, 6, 5>($rec),
            "ML-DSA-87" => $f::<MlDsa87, 8, 7>($rec),
            other => panic!("unknown parameter set {other}"),
        }
    };
}

/// Runs `check` over every record and reports all failures at once (bounded)
/// so that regressions can be diagnosed in a single run.
fn run_cases(name: &str, check: impl Fn(&Value)) {
    let mut failures = Vec::new();
    for rec in fixture(name) {
        let id = (
            rec["parameterSet"].as_str().unwrap_or("?").to_string(),
            rec["tcId"].as_i64().unwrap_or(-1),
        );
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| check(&rec)));
        if let Err(e) = result {
            let detail = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "non-string panic".to_string());
            failures.push(format!("{id:?}: {detail}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} ACVP failures ({}):\n{}",
        name,
        failures.len(),
        failures.into_iter().take(20).collect::<Vec<_>>().join("\n")
    );
}

#[test]
fn acvp_keygen_vectors() {
    run_cases("acvp-keygen", |rec| dispatch!(rec, check_keygen));
}

#[test]
fn acvp_siggen_vectors() {
    run_cases("acvp-siggen", |rec| dispatch!(rec, check_siggen));
}

#[test]
fn acvp_sigver_vectors() {
    run_cases("acvp-sigver", |rec| dispatch!(rec, check_sigver));
}

#[test]
fn acvp_siggen_internal_vectors() {
    run_cases("acvp-siggen-internal", |rec| {
        dispatch!(rec, check_siggen_internal)
    });
}

#[test]
fn acvp_sigver_internal_vectors() {
    run_cases("acvp-sigver-internal", |rec| {
        dispatch!(rec, check_sigver_internal)
    });
}

#[test]
fn acvp_siggen_prehash_vectors() {
    run_cases("acvp-siggen-prehash", |rec| {
        dispatch!(rec, check_siggen_prehash)
    });
}

#[test]
fn acvp_sigver_prehash_vectors() {
    run_cases("acvp-sigver-prehash", |rec| {
        dispatch!(rec, check_sigver_prehash)
    });
}
