//! Scheme-level contract tests for ML-DSA, exercised through the per-set
//! public APIs the way an integrator would use the crate.

use pqc::mldsa::{mldsa_44, mldsa_65, mldsa_87};

const MSG: &[u8] = b"contract-test message for ML-DSA";
const CTX: &[u8] = b"contract-context";

/// Expected (pk, signature, sk) byte lengths per FIPS 204.
const SIZES: &[(&str, usize, usize, usize)] = &[
    ("mldsa44", 1312, 2420, 2560),
    ("mldsa65", 1952, 3309, 4032),
    ("mldsa87", 2592, 4627, 4896),
];

fn seed32(tag: &[u8]) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..tag.len()].copy_from_slice(tag);
    s
}

#[test]
fn sign_verify_roundtrip_all_parameter_sets() {
    let seed = seed32(b"contract-seed");
    let (sk, vk) = mldsa_44::keygen(&seed);
    assert!(mldsa_44::verify(
        &vk,
        CTX,
        MSG,
        &mldsa_44::sign_deterministic(&sk, CTX, MSG)
    ));
    let (sk, vk) = mldsa_65::keygen(&seed);
    assert!(mldsa_65::verify(
        &vk,
        CTX,
        MSG,
        &mldsa_65::sign_deterministic(&sk, CTX, MSG)
    ));
    let (sk, vk) = mldsa_87::keygen(&seed);
    assert!(mldsa_87::verify(
        &vk,
        CTX,
        MSG,
        &mldsa_87::sign_deterministic(&sk, CTX, MSG)
    ));
}

#[test]
fn encodings_match_fips_204_sizes() {
    let seed = seed32(b"contract-seed");
    let (sk44, vk44) = mldsa_44::keygen(&seed);
    let (sk65, vk65) = mldsa_65::keygen(&seed);
    let (sk87, vk87) = mldsa_87::keygen(&seed);
    let sigs = [
        mldsa_44::sign_deterministic(&sk44, CTX, MSG).len(),
        mldsa_65::sign_deterministic(&sk65, CTX, MSG).len(),
        mldsa_87::sign_deterministic(&sk87, CTX, MSG).len(),
    ];
    let pks = [
        vk44.to_bytes().len(),
        vk65.to_bytes().len(),
        vk87.to_bytes().len(),
    ];
    let sks = [
        sk44.to_bytes().len(),
        sk65.to_bytes().len(),
        sk87.to_bytes().len(),
    ];

    for (i, (name, pk, sig, sk)) in SIZES.iter().enumerate() {
        assert_eq!(pks[i], *pk, "{name} public key size");
        assert_eq!(sigs[i], *sig, "{name} signature size");
        assert_eq!(sks[i], *sk, "{name} secret key size");
    }
}

#[test]
fn deterministic_signing_is_reproducible() {
    let seed = seed32(b"determinism-seed");
    let (sk, _) = mldsa_65::keygen(&seed);
    let s1 = mldsa_65::sign_deterministic(&sk, CTX, MSG);
    let s2 = mldsa_65::sign_deterministic(&sk, CTX, MSG);
    assert_eq!(s1, s2, "fixed rnd ⇒ identical signatures");

    // Different message ⇒ different signature (injective-enough μ).
    let other = mldsa_65::sign_deterministic(&sk, CTX, b"other message");
    assert_ne!(s1, other);
}

#[test]
fn randomized_signing_follows_the_coins() {
    let seed = seed32(b"randomness-seed");
    let (sk, _) = mldsa_44::keygen(&seed);

    let a = mldsa_44::sign_with_randomness(&sk, CTX, MSG, &[1u8; 32]);
    let b = mldsa_44::sign_with_randomness(&sk, CTX, MSG, &[1u8; 32]);
    let c = mldsa_44::sign_with_randomness(&sk, CTX, MSG, &[2u8; 32]);
    assert_eq!(a, b, "same rnd ⇒ same signature");
    assert_ne!(a, c, "different rnd ⇒ different signature");
}

#[test]
fn verify_rejects_tampering_and_wrong_keys() {
    let seed = seed32(b"tamper-seed");
    let (sk, vk) = mldsa_87::keygen(&seed);
    let sigma = mldsa_87::sign_deterministic(&sk, CTX, MSG);

    // Flipped message bit.
    assert!(!mldsa_87::verify(&vk, CTX, b"tampered message", &sigma));
    // Flipped context byte.
    assert!(!mldsa_87::verify(&vk, b"contract-contexu", MSG, &sigma));
    // Truncated and extended signatures.
    assert!(!mldsa_87::verify(&vk, CTX, MSG, &sigma[..sigma.len() - 1]));
    let mut extended = sigma.clone();
    extended.push(0);
    assert!(!mldsa_87::verify(&vk, CTX, MSG, &extended));
    // A different key must not verify this signature.
    let (_sk2, vk2) = mldsa_87::keygen(&seed32(b"another-seed"));
    assert!(!mldsa_87::verify(&vk2, CTX, MSG, &sigma));
}

#[test]
fn key_serialization_roundtrips() {
    let seed = seed32(b"serialization-seed");
    let (sk, vk) = mldsa_65::keygen(&seed);

    let sk2 = pqc::mldsa::SigningKey::<pqc::mldsa::MlDsa65>::from_bytes(&sk.to_bytes())
        .expect("valid sk encoding");
    let vk2 = pqc::mldsa::VerifyingKey::<pqc::mldsa::MlDsa65>::from_bytes(&vk.to_bytes())
        .expect("valid pk encoding");
    assert_eq!(sk, sk2);
    assert_eq!(vk, vk2);

    // Roundtripped keys still interoperate.
    let sigma = mldsa_65::sign_deterministic(&sk2, CTX, MSG);
    assert!(mldsa_65::verify(&vk2, CTX, MSG, &sigma));

    // FIPS 204 `pkDecode` validates length only — the encoding carries no
    // redundancy. A corrupted body therefore decodes to a *different* key
    // (which then fails verification), while a wrong length is rejected.
    let mut bad = vk.to_bytes();
    let mid = bad.len() / 2;
    bad[mid] ^= 0xFF;
    let corrupted = pqc::mldsa::VerifyingKey::<pqc::mldsa::MlDsa65>::from_bytes(&bad)
        .expect("length-valid encoding always decodes");
    assert_ne!(corrupted, vk);
    assert!(!mldsa_65::verify(&corrupted, CTX, MSG, &sigma));
    assert!(
        pqc::mldsa::VerifyingKey::<pqc::mldsa::MlDsa65>::from_bytes(&bad[..bad.len() - 1])
            .is_none()
    );
}

#[test]
fn keygen_spreads_over_seeds() {
    let (_sk1, vk1) = mldsa_65::keygen(&seed32(b"seed-one"));
    let (_sk2, vk2) = mldsa_65::keygen(&seed32(b"seed-two"));
    assert_ne!(vk1, vk2, "different ξ ⇒ different public keys");
}
