//! End-to-end Falcon signing across both parameter sets, with tamper
//! detection and canonical key serialization.
//!
//! Run with: `cargo run -p lattice-pqc --example sign_falcon`
//!
//! Note: keygen/sign run on the reference's emulated floating point and
//! take a few seconds per operation.

use pqc::falcon::{falcon1024, falcon512};

fn coins(tag: &[u8]) -> ([u8; 48], [u8; 40], [u8; 48]) {
    let mut keygen_seed = [0u8; 48];
    let mut nonce = [0u8; 40];
    let mut sig_seed = [0u8; 48];
    keygen_seed[..tag.len()].copy_from_slice(tag);
    nonce[..tag.len()].copy_from_slice(tag);
    sig_seed[..tag.len()].copy_from_slice(tag);
    keygen_seed[0] = 0x11;
    nonce[0] = 0x22;
    sig_seed[0] = 0x33;
    (keygen_seed, nonce, sig_seed)
}

fn main() {
    macro_rules! demo {
        ($name:literal, $api:ident) => {{
            println!("--- {} ---", $name);
            let (keygen_seed, nonce, sig_seed) = coins(concat!($name, "-seed").as_bytes());

            // FIPS 206 (draft) / Falcon keygen: all entropy from the seed.
            let (sk, pk) = $api::keygen(&keygen_seed);
            println!(
                "pk = {} B, sk = {} B",
                pk.to_bytes().len(),
                sk.to_bytes().len()
            );

            // Signature over a message with fixed nonce/seed coins
            // (fresh uniform randomness per signature in real use).
            let msg = b"falcon signs this message";
            let esig = $api::sign(&sk, msg, &nonce, &sig_seed);
            println!("signature = {} B", esig.len());

            assert!($api::verify(&pk, msg, &nonce, &esig));

            // Tampered message → rejection.
            assert!(!$api::verify(&pk, b"tampered message", &nonce, &esig));

            // Canonical serialization roundtrips both keys.
            assert_eq!(
                $api::public_key_from_bytes(pk.to_bytes())
                    .unwrap()
                    .to_bytes(),
                pk.to_bytes()
            );
            assert_eq!(
                $api::secret_key_from_bytes(sk.to_bytes())
                    .unwrap()
                    .to_bytes(),
                sk.to_bytes()
            );
            println!("sign/verify + tamper rejection + serialization ✓");
        }};
    }

    demo!("Falcon-512", falcon512);
    demo!("Falcon-1024", falcon1024);
}
