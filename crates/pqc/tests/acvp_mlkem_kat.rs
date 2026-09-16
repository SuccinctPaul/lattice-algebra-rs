//! Official ACVP (NIST) known-answer tests for ML-KEM (FIPS 203).
//!
//! The fixtures under `tests/data/` are extracted from the official
//! ACVP-Server sample vectors (see `tests/data/README.md` for provenance
//! and the extraction script). Byte-exact equality is asserted for:
//!
//! - `keyGen`: (d, z) → ek, dk in the augmented FIPS 203 format (all three
//!   parameter sets) — this exercises the seven-layer NTT, `SampleNTT`,
//!   `SamplePolyCBD`, the encodings and the hash chain end-to-end;
//! - `encaps`: (ek, m) → c, K (FIPS 203 `Encaps_internal`);
//! - `decaps`: (dk, c) → K, including implicit-rejection cases;
//! - `keyCheck`: the optional `EncapsulationKeyCheck` /
//!   `DecapsulationKeyCheck` (length + modulus validation).

use pqc::mlkem::params::{MlKem1024, MlKem512, MlKem768, MlKemParams};
use pqc::mlkem::{keygen_internal, DecapsulationKey, EncapsulationKey};
use serde_json::Value;

fn fixture() -> Vec<Value> {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data");
    let text = std::fs::read_to_string(format!("{path}/acvp-mlkem.json")).unwrap_or_else(|e| {
        panic!("missing ACVP fixture acvp-mlkem.json (run extract_mlkem_acvp.py): {e}")
    });
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

fn bytes32(rec: &Value, field: &str) -> [u8; 32] {
    hex_decode(rec[field].as_str().expect(field))
        .try_into()
        .expect("32-byte field")
}

fn set_of(rec: &Value) -> &str {
    rec["parameterSet"].as_str().unwrap()
}

fn check_keygen<P: MlKemParams, const K: usize>(rec: &Value) {
    let id = (set_of(rec), rec["tcId"].as_i64().unwrap());
    let d = bytes32(rec, "d");
    let z = bytes32(rec, "z");
    let (dk, ek) = keygen_internal::<P, K>(&d, &z);
    assert_eq!(
        ek.to_bytes(),
        hex_decode(rec["ek"].as_str().unwrap()),
        "ek mismatch for {id:?}"
    );
    assert_eq!(
        dk.to_bytes(),
        hex_decode(rec["dk"].as_str().unwrap()),
        "dk mismatch for {id:?}"
    );
}

fn check_encaps<P: MlKemParams, const K: usize>(rec: &Value) {
    let id = (set_of(rec), rec["tcId"].as_i64().unwrap());
    let ek = EncapsulationKey::<P>::from_bytes(&hex_decode(rec["ek"].as_str().unwrap()))
        .unwrap_or_else(|| panic!("ek rejected by key check for {id:?}"));
    let m = bytes32(rec, "m");
    let (c, k) = pqc::mlkem::encapsulate_internal::<P, K>(&ek, &m);
    assert_eq!(
        c.as_bytes(),
        hex_decode(rec["c"].as_str().unwrap()).as_slice(),
        "ciphertext mismatch for {id:?}"
    );
    assert_eq!(
        k.as_bytes(),
        &bytes32(rec, "k"),
        "shared-secret mismatch for {id:?}"
    );
}

fn check_decaps<P: MlKemParams, const K: usize>(rec: &Value) {
    let id = (set_of(rec), rec["tcId"].as_i64().unwrap());
    let dk = DecapsulationKey::<P>::from_bytes(&hex_decode(rec["dk"].as_str().unwrap()))
        .unwrap_or_else(|| panic!("dk rejected by key check for {id:?}"));
    let c = pqc::mlkem::Ciphertext::<P>::from_bytes(&hex_decode(rec["c"].as_str().unwrap()))
        .unwrap_or_else(|| panic!("malformed ACVP ciphertext for {id:?}"));
    let k = pqc::mlkem::decapsulate::<P, K>(&dk, &c);
    assert_eq!(
        k.as_bytes(),
        &bytes32(rec, "k"),
        "shared-secret mismatch for {id:?}"
    );
}

fn check_keycheck<P: MlKemParams>(rec: &Value) {
    let id = (
        set_of(rec),
        rec["tcId"].as_i64().unwrap(),
        rec["check"].as_str().unwrap(),
    );
    let bytes = hex_decode(rec["key"].as_str().unwrap());
    let accepted = match rec["check"].as_str().unwrap() {
        "ek" => EncapsulationKey::<P>::from_bytes(&bytes).is_some(),
        "dk" => DecapsulationKey::<P>::from_bytes(&bytes).is_some(),
        other => panic!("unknown key check {other}"),
    };
    assert_eq!(
        accepted,
        rec["testPassed"].as_bool().unwrap(),
        "key check decision mismatch for {id:?}"
    );
}

#[test]
fn acvp_mlkem_vectors() {
    let mut counted = (0usize, 0usize, 0usize, 0usize);
    for rec in fixture() {
        match rec["kind"].as_str().unwrap() {
            "keyGen" => {
                counted.0 += 1;
                match set_of(&rec) {
                    "ML-KEM-512" => check_keygen::<MlKem512, 2>(&rec),
                    "ML-KEM-768" => check_keygen::<MlKem768, 3>(&rec),
                    "ML-KEM-1024" => check_keygen::<MlKem1024, 4>(&rec),
                    other => panic!("unknown parameter set {other}"),
                }
            }
            "encaps" => {
                counted.1 += 1;
                match set_of(&rec) {
                    "ML-KEM-512" => check_encaps::<MlKem512, 2>(&rec),
                    "ML-KEM-768" => check_encaps::<MlKem768, 3>(&rec),
                    "ML-KEM-1024" => check_encaps::<MlKem1024, 4>(&rec),
                    other => panic!("unknown parameter set {other}"),
                }
            }
            "decaps" => {
                counted.2 += 1;
                match set_of(&rec) {
                    "ML-KEM-512" => check_decaps::<MlKem512, 2>(&rec),
                    "ML-KEM-768" => check_decaps::<MlKem768, 3>(&rec),
                    "ML-KEM-1024" => check_decaps::<MlKem1024, 4>(&rec),
                    other => panic!("unknown parameter set {other}"),
                }
            }
            "keyCheck" => {
                counted.3 += 1;
                match set_of(&rec) {
                    "ML-KEM-512" => check_keycheck::<MlKem512>(&rec),
                    "ML-KEM-768" => check_keycheck::<MlKem768>(&rec),
                    "ML-KEM-1024" => check_keycheck::<MlKem1024>(&rec),
                    other => panic!("unknown parameter set {other}"),
                }
            }
            other => panic!("unknown case kind {other}"),
        }
    }
    assert_eq!(
        counted,
        (75, 24, 24, 60),
        "fixture case counts changed — update the extractor caps"
    );
}
