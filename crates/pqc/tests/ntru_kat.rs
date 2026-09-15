//! Byte-exact verification against the official NTRU round-3 submission
//! KAT vectors (NTRU-Round3.zip, `KAT/{ntruhps2048677,ntruhps4096821,
//! ntruhrss701}/PQCkemKAT_*.rsp`).
//!
//! The official KAT driver (`PQCgenKAT_kem.c`) seeds the Bassham
//! AES-256-CTR DRBG with the record's 48-byte seed and draws, in order:
//! one `randombytes(SAMPLE_FG_BYTES)` for the `(f, g)` seed, one
//! `randombytes(32)` for the PRF key, and one `randombytes(
//! SAMPLE_RM_BYTES)` for the encapsulation pair `(r, m)`. The shared DRBG
//! in `common` reproduces those draws.

mod common;

use common::{hex_decode, Drbg};
use pqc::ntru::{self, NtruParams};

fn run_case<P: NtruParams>(
    seed: &[u8; 48],
    expected: &(Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>),
    count: usize,
    set: &str,
) {
    let mut drbg = Drbg::new(seed);

    // keypair: randombytes(SAMPLE_FG_BYTES) then randombytes(32).
    let mut fg_seed = vec![0u8; P::SAMPLE_FG_BYTES];
    drbg.fill(&mut fg_seed);
    let mut prf_key = [0u8; 32];
    drbg.fill(&mut prf_key);

    let (sk, pk) = ntru::keygen::<P>(&fg_seed, &prf_key);
    assert_eq!(pk.to_bytes(), expected.0, "{set} count {count}: pk");
    assert_eq!(sk.to_bytes(), expected.1, "{set} count {count}: sk");

    // enc: randombytes(SAMPLE_RM_BYTES).
    let mut rm_seed = vec![0u8; P::SAMPLE_RM_BYTES];
    drbg.fill(&mut rm_seed);
    let (ct, ss) = ntru::encapsulate::<P>(&pk, &rm_seed);
    assert_eq!(ct, expected.2.as_slice(), "{set} count {count}: ct");
    assert_eq!(ss.as_bytes(), expected.3.as_slice(), "{set} count {count}: ss");

    // dec: re-derives the same shared secret.
    let ss2 = ntru::decapsulate::<P>(&sk, &ct);
    assert_eq!(ss2.as_bytes(), expected.3.as_slice(), "{set} count {count}: decaps");
}

fn run_set(set: &str) {
    let path = format!("{}/tests/data/ntru-kat.json", env!("CARGO_MANIFEST_DIR"));
    let doc: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let cases = doc["testCases"].as_array().unwrap();

    let mut ran = 0;
    for case in cases {
        if case["parameterSet"].as_str().unwrap() != set {
            continue;
        }
        let count = case["count"].as_u64().unwrap() as usize;
        let expected = (
            hex_decode(case["pk"].as_str().unwrap()),
            hex_decode(case["sk"].as_str().unwrap()),
            hex_decode(case["ct"].as_str().unwrap()),
            hex_decode(case["ss"].as_str().unwrap()),
        );
        let seed: [u8; 48] = hex_decode(case["seed"].as_str().unwrap())
            .try_into()
            .unwrap();
        match set {
            "ntruhps2048677" => {
                run_case::<pqc::ntru::NtruHps2048677>(&seed, &expected, count, set)
            }
            "ntruhps4096821" => {
                run_case::<pqc::ntru::NtruHps4096821>(&seed, &expected, count, set)
            }
            "ntruhrss701" => run_case::<pqc::ntru::NtruHrss701>(&seed, &expected, count, set),
            _ => unreachable!(),
        }
        ran += 1;
    }
    assert_eq!(ran, 3, "{set}: expected 3 KAT cases");
}

#[test]
fn kat_ntruhps2048677() {
    run_set("ntruhps2048677");
}

#[test]
fn kat_ntruhps4096821() {
    run_set("ntruhps4096821");
}

#[test]
fn kat_ntruhrss701() {
    run_set("ntruhrss701");
}
