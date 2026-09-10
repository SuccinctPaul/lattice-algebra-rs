//! End-to-end ML-KEM key encapsulation across all three parameter sets,
//! with implicit rejection and canonical key serialization.
//!
//! Run with: `cargo run -p lattice-pqc --example kem`

use pqc::mlkem::{mlkem_1024, mlkem_512, mlkem_768};

fn coins(tag: &[u8]) -> ([u8; 32], [u8; 32]) {
    let mut d = [0u8; 32];
    let mut z = [0u8; 32];
    d[..tag.len()].copy_from_slice(tag);
    z[..tag.len()].copy_from_slice(tag);
    d[0] = 0x11;
    z[0] = 0x22;
    (d, z)
}

fn main() {
    macro_rules! demo {
        ($name:literal, $api:ident, $params:ident) => {{
            println!("--- {} ---", $name);
            let (d, z) = coins(concat!($name, "-seed").as_bytes());

            // FIPS 203 ML-KEM.KeyGen(d, z).
            let (dk, ek) = $api::keygen(&d, &z);
            println!(
                "ek = {} B, dk = {} B",
                ek.to_bytes().len(),
                dk.to_bytes().len()
            );

            // Encapsulation with fresh randomness (FIPS 203 ML-KEM.Encaps).
            let m = [0xA5u8; 32];
            let (ciphertext, ss) = $api::encapsulate(&ek, &m);
            println!(
                "ct = {} B, ss = {:02X?}",
                ciphertext.len(),
                &ss.as_bytes()[..8]
            );

            // Decapsulation recovers the same secret (FIPS 203 ML-KEM.Decaps).
            let recovered = $api::decapsulate(&dk, &ciphertext);
            assert_eq!(recovered.as_bytes(), ss.as_bytes());

            // A flipped ciphertext bit triggers implicit rejection: a
            // deterministic, unrelated secret — never an error.
            let mut bad = ciphertext.clone();
            bad[0] ^= 0x01;
            let rejected = $api::decapsulate(&dk, &bad);
            assert_ne!(rejected.as_bytes(), ss.as_bytes());
            assert_eq!(rejected.as_bytes(), $api::decapsulate(&dk, &bad).as_bytes());

            // Canonical serialization roundtrips both keys.
            assert_eq!(
                pqc::mlkem::EncapsulationKey::<pqc::mlkem::params::$params>::from_bytes(
                    &ek.to_bytes()
                )
                .unwrap()
                .to_bytes(),
                ek.to_bytes()
            );
            assert_eq!(
                pqc::mlkem::DecapsulationKey::<pqc::mlkem::params::$params>::from_bytes(
                    &dk.to_bytes()
                )
                .unwrap()
                .to_bytes(),
                dk.to_bytes()
            );
            println!("encaps/decaps + implicit rejection + serialization ✓");
        }};
    }

    demo!("ML-KEM-512", mlkem_512, MlKem512);
    demo!("ML-KEM-768", mlkem_768, MlKem768);
    demo!("ML-KEM-1024", mlkem_1024, MlKem1024);
}
