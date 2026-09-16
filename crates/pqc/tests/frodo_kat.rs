//! Byte-exact verification against the official FrodoKEM round-3
//! submission KAT vectors (FrodoKEM-Round3.zip, `KAT/PQCkemKAT_*.rsp` —
//! the AES128 and SHAKE128 matrix-`A` variants of all three parameter
//! sets).
//!
//! The official KAT driver (`PQCtestKAT_kem.c`) seeds the Bassham
//! AES-256-CTR DRBG with the record's 48-byte seed and draws, in order:
//! one `randombytes(2·SS + 16)` for the keygen inputs `(s ‖ seedSE ‖ z)`,
//! then one `randombytes(MU_BYTES)` for the encapsulation `μ`. The shared
//! DRBG in `common` reproduces those draws, so the crate's
//! explicit-randomness API is exercised exactly like the reference.

mod common;

use common::{hex_decode, Drbg};
use pqc::frodo::{self, FrodoParams};

fn run_case<P: FrodoParams>(
    seed: &[u8; 48],
    expected: &(Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>),
    count: usize,
    set: &str,
) {
    let mut drbg = Drbg::new(seed);

    // keypair: one randombytes(2·SS + 16) → (s ‖ seedSE ‖ z) with the
    // reference's `CRYPTO_BYTES`-sized sections: s at 0, seedSE at SS,
    // z at 2·SS (z itself is BYTES_SEED_A = 16 bytes).
    let mut keyrand = vec![0u8; 2 * P::SS_BYTES + 16];
    drbg.fill(&mut keyrand);
    let s = keyrand[..P::SS_BYTES].to_vec();
    let seed_se = keyrand[P::SS_BYTES..2 * P::SS_BYTES].to_vec();
    let mut z = [0u8; 16];
    z.copy_from_slice(&keyrand[2 * P::SS_BYTES..2 * P::SS_BYTES + 16]);

    let (sk, pk) = frodo::keygen::<P>(&s, &seed_se, &z).expect("DRBG-sized inputs");
    assert_eq!(pk.to_bytes(), expected.0, "{set} count {count}: pk");
    assert_eq!(sk.to_bytes(), expected.1, "{set} count {count}: sk");

    // enc: one randombytes(MU_BYTES) → mu.
    let mut mu = vec![0u8; P::MU_BYTES];
    drbg.fill(&mut mu);
    let (ct, ss) = frodo::encapsulate::<P>(&pk, &mu).expect("DRBG-sized inputs");
    assert_eq!(
        ct.as_bytes(),
        expected.2.as_slice(),
        "{set} count {count}: ct"
    );
    assert_eq!(
        ss.as_bytes(),
        expected.3.as_slice(),
        "{set} count {count}: ss"
    );

    // dec: re-derives the same shared secret.
    let ss2 = frodo::decapsulate::<P>(&sk, &ct);
    assert_eq!(
        ss2.as_bytes(),
        expected.3.as_slice(),
        "{set} count {count}: decaps"
    );
}

fn run_set(set: &str) {
    let path = format!("{}/tests/data/frodo-kat.json", env!("CARGO_MANIFEST_DIR"));
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
            "FrodoKEM-640-AES" => run_case::<pqc::frodo::Frodo640>(&seed, &expected, count, set),
            "FrodoKEM-640-SHAKE" => {
                run_case::<pqc::frodo::Frodo640Shake>(&seed, &expected, count, set)
            }
            "FrodoKEM-976-AES" => run_case::<pqc::frodo::Frodo976>(&seed, &expected, count, set),
            "FrodoKEM-976-SHAKE" => {
                run_case::<pqc::frodo::Frodo976Shake>(&seed, &expected, count, set)
            }
            "FrodoKEM-1344-AES" => run_case::<pqc::frodo::Frodo1344>(&seed, &expected, count, set),
            "FrodoKEM-1344-SHAKE" => {
                run_case::<pqc::frodo::Frodo1344Shake>(&seed, &expected, count, set)
            }
            _ => unreachable!(),
        }
        ran += 1;
    }
    assert_eq!(ran, 3, "{set}: expected 3 KAT cases");
}

#[test]
fn kat_frodo640_aes() {
    run_set("FrodoKEM-640-AES");
}

#[test]
fn kat_frodo640_shake() {
    run_set("FrodoKEM-640-SHAKE");
}

#[test]
fn kat_frodo976_aes() {
    run_set("FrodoKEM-976-AES");
}

#[test]
fn kat_frodo976_shake() {
    run_set("FrodoKEM-976-SHAKE");
}

#[test]
fn kat_frodo1344_aes() {
    run_set("FrodoKEM-1344-AES");
}

#[test]
fn kat_frodo1344_shake() {
    run_set("FrodoKEM-1344-SHAKE");
}
