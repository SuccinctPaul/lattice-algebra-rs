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
//! - [`fixed_weight_poly`]: fixed-Hamming-weight challenge with
//!   amplitude (MatRiCT `C^d_{w,p}`), generic over the dimension
//! - [`in_ball_poly`]: `τ`-sparse ±1 challenge (FIPS 204 `SampleInBall`).
//! - [`nonunit_linear_poly`]: the soundness-critical challenge
//!   `C = X − a` with `a` odd — a guaranteed **non-unit** of
//!   `Z_{2^k}[X]/(X^N + 1)`; a unit challenge would make the batched-opening
//!   verifier equation vacuous (see the Z2 module notes).
//! - [`hyperball_vec`]: LaBRADOR's challenge distribution — a whole vector
//!   of ring elements drawn from the restricted ball `‖β‖∞ ≤ b,
//!   ‖β‖₁ ≤ B`; the small-norm property is what keeps the norm accounting
//!   of batched openings and splitting queries provable.
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
use alloc::{vec, vec::Vec};

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

/// Draws a fixed-Hamming-weight sign vector with amplitude: exactly `w`
/// coefficients are non-zero, each `±1` — the general shape behind
/// MatRiCT's `C^d_{w,p}` challenge distribution (amplitude `p` applied by
/// the caller when building the ring element).
///
/// Positions are drawn by unbiased rejection (`u32` draws rejected above
/// the largest multiple of the remaining range), so every `w`-subset is
/// equiprobable; unlike [`sample_in_ball_signs`] this makes no `n ≤ 256`
/// assumption and costs `O(n)` scratch.
///
/// # Panics
/// If `w >= n` (the challenge must leave room for the zero coefficients).
pub fn fixed_weight_signs(stream: &mut BitStream<'_, impl Xof>, w: u32, n: usize) -> Vec<i8> {
    assert!(
        (w as usize) < n,
        "fixed-weight challenge needs w < n (zero room left otherwise)"
    );
    let w = w as usize;
    let mut idx: Vec<usize> = (0..n).collect();
    let mut signs = vec![0i8; n];
    let sign_bytes = w.div_ceil(8);
    let mut sign_bits = vec![0u8; sign_bytes];
    stream.read_bytes(&mut sign_bits);

    // partial Fisher–Yates: position i swaps with a uniformly drawn
    // j ∈ [i, n); unbiased via rejection above the largest multiple
    for i in 0..w {
        let range = (n - i) as u32;
        let limit = u32::MAX - (u32::MAX % range); // largest multiple of range
        let j = loop {
            let mut buf = [0u8; 4];
            stream.read_bytes(&mut buf);
            let v = u32::from_le_bytes(buf);
            if v < limit {
                break i + (v % range) as usize;
            }
        };
        signs[idx[j]] = if (sign_bits[i / 8] >> (i % 8)) & 1 == 1 {
            -1
        } else {
            1
        };
        idx.swap(i, j);
    }
    signs
}

/// Draws a fixed-Hamming-weight challenge polynomial with amplitude `p`:
/// exactly `w` coefficients are non-zero, each `±p` — MatRiCT's
/// `C^d_{w,p}` shape, which keeps `c·s` short *and* makes `c − c′`
/// non-zero (and hence invertible in the prime rings where that matters)
/// with high probability.
///
/// # Panics
/// If `w >= N` or the amplitude does not fit the modulus.
pub fn fixed_weight_poly<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
    w: u32,
    amplitude: u32,
) -> PolyRing<R, N> {
    let signs = fixed_weight_signs(stream, w, N);
    let coeffs: Vec<R> = signs
        .iter()
        .map(|&s| from_centered::<R>(i64::from(s) * i64::from(amplitude)))
        .collect();
    PolyRing::from_coefficients(coeffs)
}

/// Draws a **small non-unit** challenge: every coefficient in `{-1, 0, 1}`
/// (rejection-shaped draw), re-rolled until the coefficient sum is even.
///
/// This resolves the 2-adic challenge dilemma for Σ-protocols over
/// `Z_{2^k}[X]/(X^N+1)`: small challenges are otherwise always units (any
/// odd coefficient sum is invertible), which would make Σ-responses
/// unextractable — while the large `X − a` challenge blows up the response
/// norm (`‖C‖₁ ≈ 2^31`). Conditioning on even parity keeps `‖C‖₁ ≤ N` AND
/// non-invertibility (`χ(C) = 0`), so responses stay short and the
/// extractor's cancellation argument goes through.
///
/// # Panics
/// If the modulus is not a power of two ≥ 4 (the parity argument needs the
/// 2-adic structure) or `N < 2`.
pub fn nonunit_small_poly<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
) -> PolyRing<R, N> {
    assert!(
        R::MODULUS.is_power_of_two() && R::MODULUS >= 4,
        "the non-unit parity argument requires a power-of-two modulus ≥ 4"
    );
    assert!(N >= 2, "a parity-conditioned challenge needs N ≥ 2");
    let mut coeffs = Vec::with_capacity(N);
    let mut parity = 0u32;
    for _ in 0..N {
        // ternary draw: two bits, `11` rejected (masked rejection)
        let v = stream.read_bits(2);
        if v == 3 {
            coeffs.push(R::ZERO);
            continue;
        }
        let sign = if stream.read_bits(1) == 1 { -1 } else { 1 };
        parity ^= 1;
        coeffs.push(from_centered::<R>(i64::from(sign)));
    }
    if parity == 1 {
        // odd sum: zero the constant term (removes ±1, keeps smallness,
        // makes the sum even) — cheaper than a full re-roll and
        // statistically equivalent for challenge purposes
        coeffs[0] = R::ZERO;
    }
    PolyRing::from_coefficients(coeffs)
}

/// Draws a **strong-sampling-set** challenge: a uniform ring element with
/// odd coefficient sum — the LatticeFold notion of a challenge set `C`
/// where `a − b` is invertible for distinct draws (odd differences are
/// units of `Z_{2^k}[X]/(X^N+1)`).
///
/// # Panics
/// If the modulus is not a power of two (the parity structure is needed).
pub fn odd_sum_poly<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
) -> PolyRing<R, N> {
    assert!(
        R::MODULUS.is_power_of_two(),
        "the strong-sampling-set parity argument requires a power-of-two modulus"
    );
    let mut draws = Vec::with_capacity(N);
    for _ in 0..N {
        let mut buf = [0u8; 4];
        stream.read_bytes(&mut buf);
        draws.push(u32::from_le_bytes(buf));
    }
    if draws.iter().map(|v| v & 1).sum::<u32>() & 1 == 0 {
        draws[0] |= 1; // flip the constant term into the unit coset
    }
    PolyRing::from_coefficients(draws.iter().map(|v| R::from(u64::from(*v))).collect())
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

/// Draws a `k`-element challenge vector from the restricted ball
///
/// ```text
/// { β ∈ R^k : ‖β‖∞ ≤ b  and  ‖β‖₁ ≤ B }
/// ```
///
/// (LaBRADOR's *HyperBall* distribution: every coefficient uniform on
/// `[-b, b]`, the whole vector rejected until its total `l1` norm fits the
/// budget `B`.) The small-norm property is the soundness workhorse of the
/// batched-opening line: linear combinations `Σ βᵢ·wᵢ` inherit the norm
/// bound `‖Σ βᵢ·wᵢ‖∞ ≤ ‖β‖₁·max‖wᵢ‖∞`, which is exactly what makes the
/// norm accounting of LaBRADOR recursion and LatticeFold splitting queries
/// provable rather than heuristic.
///
/// Returns `None` if `max_attempts` draws all exceed the `l1` budget — for
/// sound parameter choices (`B` a reasonable fraction of `k·N·b`) the
/// acceptance probability is bounded away from zero and this is
/// statistically unreachable. Randomness continues from the same stream
/// across attempts (masked-rejection convention, like `RejBounded`).
/// # Example
///
/// ```rust
/// use algebra::crypto::sampling::BitStream;
/// use algebra::crypto::xof::{Shake128Xof, Xof};
/// use algebra::ring::PolynomialQuotientRing;
/// use zk::foundation::sampling::hyperball_vec;
/// use zk::instance::ring::Z2Coeff;
///
/// let mut xof = Shake128Xof::new(&[]);
/// xof.absorb(b"challenge");
/// let mut stream = BitStream::new(&mut xof);
/// let beta = hyperball_vec::<Z2Coeff, _, 64>(
///     &mut stream, 4, 1, 200, 4096,
/// ).expect("feasible budget");
/// assert_eq!(beta.len(), 4);
/// ```
pub fn hyperball_vec<R: Ring, X: Xof, const N: usize>(
    stream: &mut BitStream<'_, X>,
    k: usize,
    coeff_bound: u32,
    l1_bound: u64,
    max_attempts: usize,
) -> Option<Vec<PolyRing<R, N>>> {
    for _ in 0..max_attempts {
        let mut beta = Vec::with_capacity(k);
        let mut l1: u64 = 0;
        for _ in 0..k {
            let mut coeffs = Vec::with_capacity(N);
            for _ in 0..N {
                let c = sample_rej_bounded::<R>(stream, coeff_bound);
                l1 += c.unsigned_abs() as u64;
                coeffs.push(from_centered::<R>(c));
            }
            beta.push(PolyRing::from_coefficients(coeffs));
        }
        if l1 <= l1_bound {
            return Some(beta);
        }
    }
    None
}

/// Squeezes a single-element hyperball challenge (`‖ζ‖∞ ≤ b`, `‖ζ‖₁ ≤ B`)
/// from a domain-separated re-expansion of a transcript seed — the crate's
/// standard three-step Fiat–Shamir shape, shared by the shortness and
/// folding protocols so their challenge derivation cannot drift apart.
///
/// # Panics
/// If the rejection loop exhausts (statistically unreachable for sound
/// parameters).
pub fn hyperball_ring_from_seed<R: Ring, const N: usize>(
    domain: &[u8],
    seed: &[u8],
    coeff_bound: u32,
    l1_bound: u64,
) -> PolyRing<R, N> {
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(domain);
    xof.absorb(seed);
    let mut stream = BitStream::new(&mut xof);
    hyperball_vec::<R, Shake128Xof, N>(&mut stream, 1, coeff_bound, l1_bound, 1 << 20)
        .expect("hyperball challenge must sample for sound parameters")
        .remove(0)
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
    fn hyperball_respects_both_bounds() {
        let mut x = Shake128Xof::new(&[]);
        x.absorb(b"hyperball");
        let mut s = BitStream::new(&mut x);
        let beta = hyperball_vec::<R32, _, 64>(&mut s, 8, 1, 340, 1024)
            .expect("dense-enough ball must sample");

        assert_eq!(beta.len(), 8);
        for b in &beta {
            for c in b.coefficients() {
                assert!((-1..=1).contains(&c.centered()), "‖β‖∞ must be ≤ 1");
            }
        }
        let l1: u64 = beta
            .iter()
            .flat_map(|b| b.coefficients())
            .map(|c| c.centered().unsigned_abs())
            .sum();
        assert!(l1 <= 340, "‖β‖₁ = {l1} must respect the budget");
    }

    #[test]
    fn hyperball_is_deterministic() {
        let draw = || {
            let mut x = Shake128Xof::new(&[]);
            x.absorb(b"hyperball-det");
            let mut s = BitStream::new(&mut x);
            hyperball_vec::<R32, _, 64>(&mut s, 4, 2, 512, 1024)
        };
        assert_eq!(draw(), draw());
    }

    #[test]
    fn hyperball_rejection_loop_terminates_on_tight_budget() {
        // A tight budget with a small allowance still succeeds given enough
        // attempts (the rejection loop keeps drawing from the stream).
        let mut x = Shake128Xof::new(&[]);
        x.absorb(b"hyperball-tight");
        let mut s = BitStream::new(&mut x);
        let beta = hyperball_vec::<R32, _, 4>(&mut s, 2, 3, 8, 100_000);
        let beta = beta.expect("small ball with slack must sample");
        let l1: u64 = beta
            .iter()
            .flat_map(|b| b.coefficients())
            .map(|c| c.centered().unsigned_abs())
            .sum();
        assert!(l1 <= 8);
    }

    #[test]
    fn fixed_weight_has_exactly_w_entries_at_amplitude() {
        let mut x = Shake256Xof::new(&[]);
        let mut s = BitStream::new(&mut x);
        let c = fixed_weight_poly::<Rq, _, 256>(&mut s, 39, 7);
        let nonzeros: Vec<i64> = c
            .coefficients()
            .iter()
            .map(|v| v.centered())
            .filter(|v| *v != 0)
            .collect();
        assert_eq!(nonzeros.len(), 39);
        assert!(nonzeros.iter().all(|v| *v == 7 || *v == -7));

        // generic n beyond the SampleInBall byte limit
        let mut x = Shake128Xof::new(&[]);
        let mut s = BitStream::new(&mut x);
        let signs = fixed_weight_signs(&mut s, 3, 1000);
        assert_eq!(signs.iter().filter(|v| **v != 0).count(), 3);
    }

    #[test]
    fn fixed_weight_is_deterministic_and_uniform_enough() {
        let draw = |seed: &[u8]| {
            let mut x = Shake256Xof::new(&[]);
            x.absorb(seed);
            let mut s = BitStream::new(&mut x);
            fixed_weight_signs(&mut s, 4, 64)
        };
        assert_eq!(draw(b"a"), draw(b"a"));

        // position coverage: over many draws every slot turns non-zero
        let mut hits = vec![0u32; 64];
        for k in 0..200u8 {
            for (i, sg) in draw(&[k; 32]).iter().enumerate() {
                hits[i] += (*sg != 0) as u32;
            }
        }
        assert!(
            hits.iter().all(|h| *h > 0),
            "positions must rotate: {hits:?}"
        );
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
