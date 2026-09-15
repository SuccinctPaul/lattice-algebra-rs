//! Protocol-level samplers (L5 utilities): every random object a lattice
//! Σ-protocol / folding scheme needs, derived from a domain-separated XOF
//! stream.
//!
//! This layer composes the reference-exact distributions of
//! [`algebra::crypto::sampling`] into ring-shaped objects ([`PolyRing`]
//! elements, vectors, matrices) so protocols never hand-roll a squeeze loop.
//! Callers pass a [`BitStream`] (or an [`Xof`] for the raw-squeezing
//! challenges); randomness is never taken from a bare RNG, which keeps
//! proofs reproducible and KAT-friendly.
//!
//! Provided samplers:
//! - [`uniform_poly`]: uniform ring element over `[0, q)` via masked
//!   rejection. For `q = 2^32` (the `Z_{2^32}[X]/(X^64+1)` folding ring) the
//!   rejection never fires and this is exactly the raw 4-byte-per-coefficient
//!   expansion the Z2/Z3/Z4 protocols use.
//! - [`centered_bounded_poly`]: centered-uniform masks on `[-B, B]`
//!   (Lyubashevsky `y ← D_y`).
//! - [`cbd_poly`]: centered binomial noise (MLWE-style masks).
//! - [`in_ball_poly`]: `τ`-sparse ±1 challenge (FIPS 204 `SampleInBall`).
//! - [`nonunit_linear_poly`]: the soundness-critical challenge
//!   `C = X − a` with `a` odd — a guaranteed **non-unit** of
//!   `Z_{2^k}[X]/(X^N + 1)`; a unit challenge would make the batched-opening
//!   verifier equation vacuous (see the Z2 module notes).
//! - [`uniform_ring_from_seed`] / [`uniform_vec_from_seed`] /
//!   [`uniform_matrix_from_seed`]: seed-driven expansion with domain
//!   separation, for commitment keys and masks.
//! - [`from_centered`] / [`poly_from_centered`]: centered representatives →
//!   ring elements (witness construction, test vectors).

use algebra::crypto::sampling::{
    sample_cbd, sample_in_ball_signs, sample_rej_bounded, sample_uniform_coeff, BitStream,
};
use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::poly::sparse::SparsePolynomial;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;

/// Converts a centered representative `c ∈ (−q/2, q/2]` to a ring element.
pub fn from_centered<R: Ring>(c: i64) -> R {
    let q = i64::try_from(R::MODULUS).expect("modulus must fit in i64");
    R::from(c.rem_euclid(q) as u64)
}

/// Builds a ring element from centered representatives (ascending powers).
///
/// Length must match the ring dimension `N`; values are reduced into `[0, q)`.
pub fn poly_from_centered<R: Ring, const N: usize>(coeffs: &[i64]) -> PolyRing<R, N> {
    assert_eq!(coeffs.len(), N, "coefficient count must match dimension");
    PolyRing::from_coefficients(coeffs.iter().map(|&c| from_centered::<R>(c)).collect())
}

/// Draws one uniform ring element from a [`BitStream`] (masked rejection,
/// generalizes FIPS 204 `CoeffFromThreeBytes` to any modulus).
///
/// For `q = 2^32` this consumes exactly 4 raw bytes per coefficient and
/// rejects nothing — byte-identical to the raw expansion the folding
/// protocols historically used.
pub fn uniform_poly<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
) -> PolyRing<R, N> {
    let mut coeffs = Vec::with_capacity(N);
    for _ in 0..N {
        coeffs.push(sample_uniform_coeff::<R>(stream));
    }
    PolyRing::from_coefficients(coeffs)
}

/// Draws `len` uniform ring elements from one stream.
pub fn uniform_polys<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
    len: usize,
) -> Vec<PolyRing<R, N>> {
    (0..len).map(|_| uniform_poly::<R, X, N>(stream)).collect()
}

/// Derives one uniform ring element from a domain-separated seed
/// (`SHAKE128(domain ‖ seed)`).
pub fn uniform_ring_from_seed<R: Ring, const N: usize>(
    domain: &[u8],
    seed: &[u8],
) -> PolyRing<R, N> {
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(domain);
    xof.absorb(seed);
    uniform_poly::<R, _, N>(&mut BitStream::new(&mut xof))
}

/// Derives a uniform vector of ring elements from a domain-separated seed.
pub fn uniform_vec_from_seed<R: Ring, const N: usize>(
    domain: &[u8],
    seed: &[u8],
    len: usize,
) -> Vec<PolyRing<R, N>> {
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(domain);
    xof.absorb(seed);
    uniform_polys::<R, _, N>(&mut BitStream::new(&mut xof), len)
}

/// Derives a uniform `rows × cols` matrix of ring elements from a
/// domain-separated seed (row-major, one continuous stream — the Ajtai-key
/// expansion for the `Z_{2^32}` folding ring).
pub fn uniform_matrix_from_seed<R: Ring, const N: usize>(
    domain: &[u8],
    seed: &[u8],
    rows: usize,
    cols: usize,
) -> Vec<Vec<PolyRing<R, N>>> {
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(domain);
    xof.absorb(seed);
    uniform_polys::<R, _, N>(&mut BitStream::new(&mut xof), rows * cols)
        .chunks(cols)
        .map(<[PolyRing<R, N>]>::to_vec)
        .collect()
}

/// Draws one mask polynomial with centered-uniform coefficients on
/// `[-bound, bound]` (Lyubashevsky mask distribution, FIPS 204 `RejBoundedη`
/// generalized to arbitrary bounds).
pub fn centered_bounded_poly<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
    bound: u32,
) -> PolyRing<R, N> {
    let mut coeffs = Vec::with_capacity(N);
    for _ in 0..N {
        coeffs.push(from_centered::<R>(sample_rej_bounded::<R>(stream, bound)));
    }
    PolyRing::from_coefficients(coeffs)
}

/// Draws one noise polynomial with centered-binomial coefficients on
/// `[-eta, eta]` (FIPS 203 `CBDη`).
pub fn cbd_poly<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
    eta: u32,
) -> PolyRing<R, N> {
    let mut coeffs = Vec::with_capacity(N);
    for _ in 0..N {
        coeffs.push(from_centered::<R>(sample_cbd::<R>(stream, eta)));
    }
    PolyRing::from_coefficients(coeffs)
}

/// Draws a `τ`-sparse ±1 challenge polynomial (FIPS 204 `SampleInBall`):
/// exactly `τ` non-zero coefficients, each `±1` — the Lyubashevsky/FS
/// challenge shape with `‖c‖₁ = τ`.
///
/// # Panics
/// If `tau >= N` (the challenge must live in the ring) or `N > 256`.
pub fn in_ball_poly<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
    tau: u32,
) -> PolyRing<R, N> {
    let signs = sample_in_ball_signs(stream, tau, N);
    let sparse = SparsePolynomial::<R>::from_sign_vector(&signs, N);
    PolyRing::from_coefficients(sparse.to_coeff_vec())
}

/// Draws the linear non-unit challenge `C = X − a` with `a` odd, squeezed
/// raw from an [`Xof`].
///
/// In `Z_{2^k}[X]/(X^N + 1)` an element is a unit iff its coefficient sum is
/// odd; `C` has coefficients `(q − a, 1, 0, …)` with `q` even and `a` odd, so
/// the sum `q − a + 1` is even — a genuine non-unit. Protocols relying on
/// this (batched opening, gadget-IPA) need the challenge to be a non-unit:
/// the monomial `X` alone is always a unit (`X·(−X^{N−1}) = 1`), which would
/// let a cheater solve the verifier equation for any claim.
///
/// # Panics
/// If the modulus is not a power of two ≥ 4 (the parity argument needs the
/// `2`-adic structure) or `N < 2`.
pub fn nonunit_linear_poly<R: Ring, X: Xof, const N: usize>(xof: &mut X) -> PolyRing<R, N> {
    assert!(
        R::MODULUS.is_power_of_two() && R::MODULUS >= 4,
        "the non-unit parity argument requires a power-of-two modulus ≥ 4"
    );
    assert!(N >= 2, "C = X − a needs a coefficient slot for X");

    let nbytes = (R::MODULUS.trailing_zeros() / 8) as usize;
    let mut buf = [0u8; 8];
    xof.squeeze(&mut buf[..nbytes]);
    let mut a = 0u64;
    for (i, &b) in buf[..nbytes].iter().enumerate() {
        a |= (b as u64) << (8 * i);
    }
    a |= 1; // odd ⇒ X − a is a non-unit (see above)

    let mut coeffs = vec![R::ZERO; N];
    coeffs[0] = R::from(R::MODULUS - a);
    coeffs[1] = R::ONE;
    PolyRing::from_coefficients(coeffs)
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::crypto::xof::{Shake128Xof, Shake256Xof};
    use algebra::ring::traits::CenteredRing;
    use algebra::ring::zq::Zq;

    type Rq = Zq<8380417>;
    type R32 = Zq<4294967296>;
    type R17 = Zq<17>;

    #[test]
    fn uniform_is_deterministic_and_in_range() {
        fn draw() -> PolyRing<Rq, 64> {
            let mut x = Shake128Xof::new(&[]);
            x.absorb(b"uniform-poly");
            uniform_poly::<Rq, _, 64>(&mut BitStream::new(&mut x))
        }
        let a = draw();
        assert_eq!(a, draw(), "XOF-driven sampling must be deterministic");
        assert!(a.coefficients().iter().all(|c| c.to_u128() < 8_380_417));
    }

    #[test]
    fn uniform_degenerates_to_raw_expansion_on_power_of_two_modulus() {
        // For q = 2^32 the masked-rejection sampler must consume exactly four
        // raw bytes per coefficient — pinning byte-compatibility with the
        // historical Z2/Z3/Z4 raw expansion.
        let mut x = Shake128Xof::new(&[]);
        x.absorb(b"raw-equiv");
        let sampled = uniform_poly::<R32, _, 16>(&mut BitStream::new(&mut x));

        let mut y = Shake128Xof::new(&[]);
        y.absorb(b"raw-equiv");
        let mut raw = [0u32; 16];
        let mut buf = [0u8; 4];
        for c in &mut raw {
            y.squeeze(&mut buf);
            *c = u32::from_le_bytes(buf);
        }
        assert_eq!(
            sampled.coefficients(),
            raw.iter()
                .map(|&c| R32::from(u64::from(c)))
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn seed_expansion_is_domain_separated() {
        let a = uniform_ring_from_seed::<R17, 8>(b"domain-a", b"seed");
        let b = uniform_ring_from_seed::<R17, 8>(b"domain-b", b"seed");
        assert_ne!(a, b, "domains must separate streams");

        let m = uniform_matrix_from_seed::<R17, 4>(b"m", b"seed", 3, 5);
        assert_eq!(m.len(), 3);
        assert!(m.iter().all(|row| row.len() == 5));
        let m2 = uniform_matrix_from_seed::<R17, 4>(b"m", b"seed", 3, 5);
        assert_eq!(m, m2, "seed expansion must be deterministic");
    }

    #[test]
    fn centered_bounded_stays_in_range_and_uses_tails() {
        let mut x = Shake128Xof::new(&[]);
        let mut s = BitStream::new(&mut x);
        let mut negatives = 0;
        let mut positives = 0;
        for _ in 0..64 {
            let p = centered_bounded_poly::<R17, _, 16>(&mut s, 3);
            for c in p.coefficients() {
                let v = c.centered();
                assert!((-3..=3).contains(&v));
                negatives += (v < 0) as u32;
                positives += (v > 0) as u32;
            }
        }
        assert!(
            negatives > 200 && positives > 200,
            "distribution too skewed"
        );
    }

    #[test]
    fn cbd_stays_in_range() {
        let mut x = Shake128Xof::new(&[]);
        let mut s = BitStream::new(&mut x);
        for _ in 0..32 {
            let p = cbd_poly::<R17, _, 16>(&mut s, 2);
            for c in p.coefficients() {
                assert!((-2..=2).contains(&c.centered()));
            }
        }
    }

    #[test]
    fn in_ball_has_exactly_tau_nonzeros() {
        let mut x = Shake256Xof::new(&[]);
        let mut s = BitStream::new(&mut x);
        let c = in_ball_poly::<Rq, _, 256>(&mut s, 39);
        let nonzeros = c.coefficients().iter().filter(|&&v| v != Rq::ZERO).count();
        assert_eq!(nonzeros, 39);
        assert!(c.coefficients().iter().all(|&v| {
            let cv = v.centered();
            cv == 0 || cv == 1 || cv == -1
        }));
    }

    #[test]
    fn in_ball_matches_reference_bit_stream() {
        // Same derivation as the Z1 Σ-protocol used historically: signs via
        // sample_in_ball_signs over a dedicated stream, dense embedding.
        let mut xa = Shake256Xof::new(&[]);
        xa.absorb(b"c-tilde");
        let poly = in_ball_poly::<Rq, _, 256>(&mut BitStream::new(&mut xa), 39);

        let mut xb = Shake256Xof::new(&[]);
        xb.absorb(b"c-tilde");
        let mut stream = BitStream::new(&mut xb);
        let signs = sample_in_ball_signs(&mut stream, 39, 256);
        let sparse = SparsePolynomial::<Rq>::from_sign_vector(&signs, 256);
        let reference = PolyRing::<Rq, 256>::from_coefficients(sparse.to_coeff_vec());
        assert_eq!(poly, reference);
    }

    #[test]
    fn nonunit_linear_is_shape_and_parity_correct() {
        let mut x = Shake128Xof::new(&[]);
        x.absorb(b"nonunit");
        let c = nonunit_linear_poly::<R32, _, 64>(&mut x);

        let coeffs = c.coefficients();
        assert_eq!(coeffs[1], R32::ONE);
        assert!(coeffs[2..].iter().all(|&v| v == R32::ZERO));
        let a = (R32::MODULUS - coeffs[0].to_u128() as u64) | 1;
        assert_eq!(a % 2, 1, "scalar a must be odd");

        // The documented non-unit criterion: coefficient sum even.
        let parity_sum: u64 = coeffs.iter().map(|v| v.to_u128() as u64 & 1).sum();
        assert_eq!(parity_sum % 2, 0, "coefficient sum must be even ⇒ non-unit");
        assert_eq!(coeffs[0], R32::from(R32::MODULUS - a), "C = X − a");
    }

    #[test]
    fn nonunit_linear_is_deterministic() {
        let draw = || {
            let mut x = Shake128Xof::new(&[]);
            x.absorb(b"nonunit-det");
            nonunit_linear_poly::<R32, _, 64>(&mut x)
        };
        assert_eq!(draw(), draw());
    }

    #[test]
    fn from_centered_reduces_negative_representatives() {
        assert_eq!(from_centered::<R17>(-3), R17::from(14));
        assert_eq!(from_centered::<R17>(3), R17::from(3));
        let p = poly_from_centered::<R17, 4>(&[1, -1, 8, -8]);
        let expected: Vec<R17> = [1, 16, 8, 9].iter().map(|&v| R17::from(v)).collect();
        assert_eq!(p.coefficients(), expected);
    }
}
