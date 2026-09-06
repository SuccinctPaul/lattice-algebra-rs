//! Official ACVP (NIST) known-answer tests for ML-DSA (FIPS 204, pure mode).
//!
//! The fixtures under `tests/data/` are extracted from the official
//! ACVP-Server sample vectors (see `tests/data/README.md` for provenance and
//! the extraction script). Byte-exact equality is asserted for:
//!
//! - `keyGen`: seed → pk, sk (all three parameter sets);
//! - `sigGen`: deterministic and randomized signing (the randomized vectors
//!   fix the `rnd` input);
//! - `sigVer`: accept and reject decisions, including empty/absent contexts.
//!
//! These tests close the "official KAT/ACVP alignment" gap: any deviation in
//! the hash chain, `ExpandA`/`RejNTTPoly`, the samplers, the FIPS 204 NTT
//! convention, the rounding/hint logic or the wire encodings shows up here.

use pqc::mldsa::params::{MlDsa44, MlDsa65, MlDsa87, MlDsaParams};
use pqc::mldsa::{
    keygen_seed, sign_deterministic, sign_with_randomness, verify_core, SigningKey, VerifyingKey,
};
use serde_json::Value;

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
