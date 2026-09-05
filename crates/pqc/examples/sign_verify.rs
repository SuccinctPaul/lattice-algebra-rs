//! End-to-end ML-DSA signing across all three parameter sets, with tamper
//! detection and canonical key serialization.
//!
//! Run with: `cargo run -p lattice-pqc --example sign_verify`

use pqc::mldsa::{mldsa_44, mldsa_65, mldsa_87};

fn seed32(tag: &[u8]) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..tag.len()].copy_from_slice(tag);
    s
}

fn main() {
    let ctx = b"example-context";
    let msg = b"attack at dawn";

    macro_rules! demo {
        ($name:literal, $api:ident) => {{
            println!("--- {} ---", $name);
            let seed = seed32(concat!($name, "-seed").as_bytes());

            // Key generation from a 32-byte seed (FIPS 204 ML-DSA.KeyGen).
            let (sk, vk) = $api::keygen(&seed);

            // Deterministic signing: same key + same rnd ⇒ same signature.
            let sigma1 = $api::sign_deterministic(&sk, ctx, msg);
            let sigma2 = $api::sign_deterministic(&sk, ctx, msg);
            assert_eq!(sigma1, sigma2);

            // Hedged signing with explicit coins.
            let sigma3 = $api::sign_with_randomness(&sk, ctx, msg, &[9u8; 32]);
            assert!($api::verify(&vk, ctx, msg, &sigma3));

            println!("signature: {} bytes", sigma1.len());
            println!("public key: {} bytes", vk.to_bytes().len());

            // Verification accepts the honest signature…
            assert!($api::verify(&vk, ctx, msg, &sigma1));
            println!("verify(honest) = true");

            // …and rejects every tampering we can think of.
            assert!(!$api::verify(&vk, ctx, b"attack at dusk", &sigma1));
            assert!(!$api::verify(&vk, b"other-context", msg, &sigma1));
            println!("verify(tampered) = false");

            println!();
        }};
    }

    demo!("ML-DSA-44", mldsa_44);
    demo!("ML-DSA-65", mldsa_65);
    demo!("ML-DSA-87", mldsa_87);

    // Canonical key serialization: encode → decode → still interoperable.
    let (sk, vk) = mldsa_65::keygen(&seed32(b"serialization-seed"));
    let vk2 = pqc::mldsa::VerifyingKey::<pqc::mldsa::MlDsa65>::from_bytes(&vk.to_bytes())
        .expect("pk decodes");
    let sk2 = pqc::mldsa::SigningKey::<pqc::mldsa::MlDsa65>::from_bytes(&sk.to_bytes())
        .expect("sk decodes");
    let sigma = mldsa_65::sign_deterministic(&sk2, ctx, msg);
    assert!(mldsa_65::verify(&vk2, ctx, msg, &sigma));
    println!("key serialization roundtrip signs and verifies   ✓");

    println!("All three parameter sets round-trip and reject tampering.");
}
