//! Guard: every "current API" snippet on the quickstart page
//! (`docs/src/pages/introduction/getting-started.mdx`) must compile and run.
//! The algebra-side snippets live here because only the facade can see all
//! three crates; the ML-DSA and Z1 snippets are guarded in
//! `crates/pqc/tests/doc_snippet_check.rs` and
//! `crates/zk/tests/doc_snippet_check.rs`. Keep this file in sync with the
//! page — if you rename what a snippet uses, update the page in the same PR.
//!
//! Lint allowances mirror the page, which shows bare statements (`Zq::TWO_ADICITY;`),
//! binds values without asserting on them, and imports the full capability-trait
//! kit even where the inherent `Zq::inverse` would suffice.
#![allow(unused_variables, path_statements, unused_imports)]

use lattice_algebra_rs::crypto::sampling::{sample_in_ball_signs, sample_rej_bounded, BitStream};
use lattice_algebra_rs::crypto::xof::{Shake128Xof, Shake256Xof, Xof};
use lattice_algebra_rs::module::{ModuleMatrixNtt, ModuleVector};
use lattice_algebra_rs::ntt::NttOperatorOptimized;
use lattice_algebra_rs::poly::sparse::SparsePolynomial;
use lattice_algebra_rs::ring::poly_ring::PolyRing;
use lattice_algebra_rs::ring::traits::{CenteredRing, Field, Ring, TwoAdicRing};
use lattice_algebra_rs::ring::zq::Zq;
use lattice_algebra_rs::ring::PolynomialQuotientRing;

type Zq17 = Zq<17>;
type R = PolyRing<Zq17, 8>;

#[test]
fn quickstart_scalar_ring_snippet() {
    let a = Zq17::new(5);
    let c = a + Zq17::new(13); // 18 mod 17 = 1
    assert_eq!(c, Zq17::new(1));
    let inv = Zq17::new(5).inverse(); // Field: Some(7)
    assert_eq!(inv, Some(Zq17::new(7)));
    let centered = Zq17::new(16).centered(); // −1  (CenteredRing)
    assert_eq!(centered, -1);
    let norm = Zq17::new(16).abs_infinity(); // 1
    assert_eq!(norm, 1);
    Zq17::TWO_ADICITY; // 4 (TwoAdicRing)
    assert_eq!(Zq17::TWO_ADICITY, 4);
    Zq17::IS_PRIME; // true, decided at compile time
    const { assert!(Zq17::IS_PRIME) };
}

#[test]
fn quickstart_polynomial_ring_snippet() {
    let a = R::from_coefficients(vec![Zq17::new(1), Zq17::new(2)]);
    let b = R::from_coefficients(vec![Zq17::new(3), Zq17::new(4)]);
    let prod = a.clone() * b.clone();

    // x^7 · x = x^8 ≡ −1 (mod X^8+1)
    let x7 = R::from_coefficients(
        vec![0, 0, 0, 0, 0, 0, 0, 1]
            .into_iter()
            .map(Zq17::new)
            .collect(),
    );
    let x = R::from_coefficients(vec![Zq17::ZERO, Zq17::ONE]);
    assert_eq!((x7 * x).coefficients(), vec![-Zq17::ONE]);

    // Explicit NTT-domain representation (M1)
    let op = NttOperatorOptimized::<Zq17, 8>::new();
    let via_ntt = R::from_ntt(a.to_ntt(&op).mul(&b.to_ntt(&op)), &op);
    assert_eq!(via_ntt, prod);
}

#[test]
fn quickstart_sparse_challenge_snippet() {
    let c = SparsePolynomial::<Zq17>::from_sign_vector(&[1, 0, 0, -1, 0, 0, 0, 0], 8);
    let dense = R::from_coefficients(vec![Zq17::new(1), Zq17::new(2)]);
    let _ = c.mul_dense(&dense); // O(τ·N), no NTT needed
}

#[test]
fn quickstart_xof_sampling_snippet() {
    let mut xof = Shake256Xof::new(b"my-scheme/sampler");
    let mut stream = BitStream::new(&mut xof);
    let v = sample_rej_bounded::<Zq17>(&mut stream, 2); // uniform on [−2, 2]
    assert!((-2..=2).contains(&v));
    let signs = sample_in_ball_signs(&mut stream, 39, 256); // τ-sparse ±1 challenge
    assert_eq!(signs.iter().filter(|&&s| s != 0).count(), 39);
    // Determinism: the same domain label replays the same stream.
    let mut replay = Shake256Xof::new(b"my-scheme/sampler");
    let mut replay_stream = BitStream::new(&mut replay);
    assert_eq!(sample_rej_bounded::<Zq17>(&mut replay_stream, 2), v);
}

#[test]
fn quickstart_module_lattice_snippet() {
    let op = NttOperatorOptimized::<Zq17, 8>::new();

    // Â derived from a seed, directly in the NTT domain (FIPS 204 ExpandA shape)
    let a_hat = ModuleMatrixNtt::<Zq17, 2, 2, 8>::expand_from_seed::<Shake128Xof>(&[7u8; 32]);
    let v = ModuleVector::<Zq17, 2, 8>::zero();
    let w = a_hat.mul_vec_ntt(&v.to_ntt(&op)).from_ntt(&op);
    assert_eq!(w.infinity_norm(), 0);
}
