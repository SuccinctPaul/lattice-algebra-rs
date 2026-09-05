//! Temporary guard: the quickstart snippets must compile and run verbatim.
use pqc::mldsa::mldsa_65 as mldsa;

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
