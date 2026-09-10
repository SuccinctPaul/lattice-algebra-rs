//! Guard: the quickstart snippets must compile and run verbatim.
use pqc::mldsa::mldsa_65 as mldsa;
use pqc::mlkem::mlkem_768 as mlkem;

#[test]
fn quickstart_mldsa_snippet() {
    let seed = [42u8; 32];
    let (sk, vk) = mldsa::keygen(&seed);
    let sigma = mldsa::sign_deterministic(&sk, b"context", b"hello lattice world");
    assert!(mldsa::verify(
        &vk,
        b"context",
        b"hello lattice world",
        &sigma
    ));
    assert_eq!(sigma.len(), 3309); // ML-DSA-65 signature size
    assert_eq!(vk.to_bytes().len(), 1952); // public key size
}

#[test]
fn quickstart_mlkem_snippet() {
    let (d, z) = ([42u8; 32], [7u8; 32]);
    let (dk, ek) = mlkem::keygen(&d, &z);

    let m = [9u8; 32];
    let (ciphertext, ss) = mlkem::encapsulate(&ek, &m);
    assert_eq!(ciphertext.len(), 1088);
    assert_eq!(
        mlkem::decapsulate(&dk, &ciphertext).as_bytes(),
        ss.as_bytes()
    );

    let mut bad = ciphertext.clone();
    bad[0] ^= 0x01;
    assert_ne!(mlkem::decapsulate(&dk, &bad).as_bytes(), ss.as_bytes());
    assert_eq!(ek.to_bytes().len(), 1184);
}
