//! Module-lattice arithmetic: `R_q^K` vectors and `R_q^{K×L}` matrices,
//! seed expansion (`ExpandA`), the NTT homomorphism between the two matrix
//! domains, FIPS-style rounding and infinity norms.
//!
//! Run with: `cargo run -p lattice-algebra --example module_lattices`

use algebra::crypto::sampling::{sample_rej_bounded, BitStream};
use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::module::{rounding, ModuleMatrix, ModuleMatrixNtt, ModuleVector};
use algebra::ntt::NttOperatorOptimized;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;

type ZqD = Zq<8380417>;
const N: usize = 256;
const K: usize = 4;
const L: usize = 5;

fn short_vector() -> ModuleVector<ZqD, L, N> {
    // A "secret"-shaped vector: small centered coefficients, like ML-DSA's s1.
    ModuleVector::from_fn(|i| {
        let mut x = Shake128Xof::new(b"module-example");
        x.absorb(&[i as u8]);
        let mut stream = BitStream::new(&mut x);
        let coeffs: Vec<ZqD> = (0..N)
            .map(|_| {
                ZqD::new(sample_rej_bounded::<ZqD>(&mut stream, 2).rem_euclid(8_380_417) as u64)
            })
            .collect();
        PolyRing::from_coefficients(coeffs)
    })
}

fn main() {
    let seed = [0x2Au8; 32];

    // ------------------------------------------------------------------
    // ExpandA: the commitment matrix, expanded straight into the NTT domain
    // (as ML-DSA does — the raw sampled values ARE the NTT-domain entries,
    // so no matrix-wide transform is ever spent).
    // ------------------------------------------------------------------
    let a_hat = ModuleMatrixNtt::<ZqD, K, L, N>::expand_from_seed::<Shake128Xof>(&seed);
    let s = short_vector();
    let op = NttOperatorOptimized::<ZqD, N>::new();
    let s_hat = s.to_ntt(&op);
    let w_hat = a_hat.mul_vec_ntt(&s_hat);
    println!(
        "Â·s computed in the NTT domain  ({}×{} matrix, n={})",
        K, L, N
    );

    // ------------------------------------------------------------------
    // The NTT is a ring homomorphism, so computing in the coefficient
    // domain — over the coefficient-domain view A = from_ntt(Â) — must give
    // exactly the same product:
    //     A·s  ==  from_ntt(Â·ntt(s))
    // ------------------------------------------------------------------
    let a_coeff = ModuleMatrix::<ZqD, K, L, N>::from_fn(|i, j| {
        PolyRing::from_ntt(a_hat.get(i, j).clone(), &op)
    });
    let w_coeff = a_coeff.mul_vec(&s);
    let w_back =
        ModuleVector::<ZqD, K, N>::from_fn(|i| PolyRing::from_ntt(w_hat.polys()[i].clone(), &op));
    assert_eq!(
        w_coeff, w_back,
        "coefficient-domain and NTT-domain products agree"
    );
    println!("A·s == from_ntt(Â·ntt(s))   ✓  (NTT homomorphism)");

    // ------------------------------------------------------------------
    // FIPS 204 rounding: high/low bits, hints
    // ------------------------------------------------------------------
    let (r1, r0) = rounding::power2round(8_380_000, 13);
    println!("power2round(8380000, d=13) = (high={r1}, low={r0})");

    let gamma2 = 95_232; // ML-DSA-44/65
    let q = 8_380_417;
    let (h1, h0) = rounding::decompose(4_190_208, gamma2, q);
    let hint = rounding::make_hint(h0, 4_190_300, gamma2, q);
    let recovered = rounding::use_hint(h1, hint, gamma2, q);
    println!("decompose → make_hint → use_hint recovers high bits: {recovered}");

    // ------------------------------------------------------------------
    // Norms: the verifier-side check that a witness is short
    // ------------------------------------------------------------------
    let norm = w_back.infinity_norm();
    println!("‖w‖∞ over Z_q = {norm} (max possible ≈ q/2)");
}
