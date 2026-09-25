//! Ring switching: the negacyclic **residual** that turns a relation over
//! `R_q` into a polynomial identity over `Z_q[X]` (Z7 support).
//!
//! Hachi (2026/156, §1.3 "Ring switching and sumcheck over extension fields")
//! lifts a linear relation `Σᵢ m·zᵢ = w` over `R_q = Z_q[X]/(X^d+1)` to
//!
//! ```text
//! Σᵢ mᵢ(X)·zᵢ(X)  =  ω(X) + (X^d + 1)·ρ(X)      in Z_q[X],   deg ρ ≤ d − 2
//! ```
//!
//! where the products on the left are **unreduced** (schoolbook) convolutions.
//! The point of carrying `ρ` is that the identity survives substituting any
//! `X = ζ` in any extension of `Z_q`: the verifier then checks
//!
//! ```text
//! Σᵢ mᵢ(ζ)·ẑᵢ(ζ)  =  ω̂(ζ) + (ζ^d + 1)·ρ̂(ζ)
//! ```
//!
//! which is an inner-product claim over the extension **field** `F_{q^k}` — and
//! therefore something a sumcheck can prove with `Õ(k)` base operations per
//! step instead of a full ring multiplication. That is where Hachi's
//! `√(2^ℓ·λ)`-sized verifier comes from, and why the residual is a capability
//! of its own rather than a detail of one scheme.
//!
//! `ρ` is not a free parameter: writing the unreduced product as
//! `P = Σ_k P_k X^k` with `P_k = 0` outside `0..2d−2`, the fold
//! `c_k = P_k − P_{k+d}` (which is exactly negacyclic multiplication, `X^d =
//! −1`) forces `ρ_j = P_{j+d}` for `j ≤ d−2`, so `deg ρ ≤ d − 2` and the
//! decomposition is unique. The tests below pin that uniqueness against an
//! independent reconstruction, and the substitution identity in
//! [`algebra::ring::extension::ExtField`].
//!
//! Layering: `pcs::switching` sits next to [`crate::instance::ring`]'s
//! modulus-switching helpers but is a different operation — `switch_ring` maps
//! between rings, this keeps the reduction error *explicit* so a prover can
//! commit to it.

use algebra::ring::extension::ExtField;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;
use alloc::vec;
use alloc::vec::Vec;

/// Why a residual operation refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SwitchingError {
    /// The two vectors being paired had different lengths.
    LengthMismatch {
        /// Length supplied.
        got: usize,
        /// Length required.
        expected: usize,
    },
    /// The claimed value did not match the relation, so no residual exists.
    NotARelation,
}

impl core::fmt::Display for SwitchingError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::LengthMismatch { got, expected } => write!(
                f,
                "pairwise relation needs equal lengths: got {got}, expected {expected}"
            ),
            Self::NotARelation => write!(
                f,
                "the claimed value does not satisfy the relation, so it has no residual"
            ),
        }
    }
}

/// The unreduced (schoolbook) product of two elements of `Z_q[X]` of degree
/// `< D`, as `2D − 1` coefficients.
pub fn schoolbook<R: Ring, const D: usize>(a: &PolyRing<R, D>, b: &PolyRing<R, D>) -> Vec<R> {
    let ac = a.coefficients();
    let bc = b.coefficients();
    let mut out = vec![R::ZERO; 2 * D - 1];
    for (i, &x) in ac.iter().enumerate() {
        for (j, &y) in bc.iter().enumerate() {
            out[i + j] = out[i + j] + x * y;
        }
    }
    out
}

/// Split the unreduced product into its negacyclic reduction and the residual:
/// `a·b = c + (X^D + 1)·ρ` in `Z_q[X]`, with `c` the ring product and `ρ` of
/// degree `≤ D − 2` (returned as `D − 1` coefficients, ascending).
pub fn negacyclic_residual<R: Ring, const D: usize>(
    a: &PolyRing<R, D>,
    b: &PolyRing<R, D>,
) -> (PolyRing<R, D>, Vec<R>) {
    let p = schoolbook(a, b);
    let mut c = vec![R::ZERO; D];
    let mut rho = vec![R::ZERO; D - 1];
    // `X^{k+D} = −X^k`, so the high half folds into the low half negated. The
    // unreduced product has 2D − 1 coefficients, so only `k ≤ D − 2` has a
    // partner at `k + D`: the top low-half coefficient is untouched, and that
    // is exactly why `deg ρ ≤ D − 2`.
    for k in 0..D - 1 {
        c[k] = p[k] - p[k + D];
    }
    c[D - 1] = p[D - 1];
    for j in 0..D - 1 {
        rho[j] = p[j + D];
    }
    (PolyRing::from_coefficients(c), rho)
}

/// The residual `ρ` of the lifted relation `Σᵢ m(X)·zᵢ(X) = ω(X) + (X^D+1)·ρ(X)`.
///
/// `w` must be the ring-side value `Σᵢ mᵢ·zᵢ mod (X^D + 1)`; the reduction is
/// recomputed here rather than trusted, so a caller that passes an unrelated
/// `w` gets [`SwitchingError::NotARelation`] instead of a residual that
/// silently proves nothing.
///
/// # Errors
/// [`SwitchingError::LengthMismatch`] if `ms` and `zs` differ in length, and
/// [`SwitchingError::NotARelation`] if `w` is not the relation's value.
pub fn relation_residual<R: Ring, const D: usize>(
    ms: &[PolyRing<R, D>],
    zs: &[PolyRing<R, D>],
    w: &PolyRing<R, D>,
) -> Result<Vec<R>, SwitchingError> {
    if ms.len() != zs.len() {
        return Err(SwitchingError::LengthMismatch {
            got: zs.len(),
            expected: ms.len(),
        });
    }
    let mut unreduced = vec![R::ZERO; 2 * D - 1];
    let mut folded = vec![R::ZERO; D];
    for (m, z) in ms.iter().zip(zs.iter()) {
        let p = schoolbook(m, z);
        for (acc, term) in unreduced.iter_mut().zip(p.iter()) {
            *acc = *acc + *term;
        }
        for k in 0..D - 1 {
            folded[k] = folded[k] + p[k] - p[k + D];
        }
        folded[D - 1] = folded[D - 1] + p[D - 1];
    }
    // Compare against the padded representation: `PolyRing` trims trailing
    // zeros, so a short `coefficients()` still denotes the same element.
    let mut padded = w.coefficients().to_vec();
    padded.resize(D, R::ZERO);
    if folded.as_slice() != padded.as_slice() {
        return Err(SwitchingError::NotARelation);
    }
    Ok((0..D - 1).map(|j| unreduced[j + D]).collect())
}

/// Evaluate `Σ_k coeffs[k]·X^k` at a point of an extension ring, by Horner.
///
/// This is the substitution step: with `ζ ∈ F_{q^k}` the relation becomes
/// `Σᵢ m̂ᵢ(ζ)·ẑᵢ(ζ) = ω̂(ζ) + (ζ^D + 1)·ρ̂(ζ)`, which is what a sumcheck over
/// the extension field proves.
pub fn evaluate_at_base<R: Ring, const K: usize, const A: u64>(
    coeffs: &[R],
    zeta: &ExtField<R, K, A>,
) -> ExtField<R, K, A> {
    let mut acc = ExtField::zero();
    for c in coeffs.iter().rev() {
        acc = acc * zeta.clone() + ExtField::from_base(*c);
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use algebra::ring::zq::Zq;

    /// `2³² − 99`: prime, `≡ 5 (mod 8)` — the congruence Hachi needs, and one
    /// where no NTT of degree ≥ 4 exists.
    type Q5 = Zq<4294967197>;
    const D: usize = 8;

    fn elt(seed: u64) -> PolyRing<Q5, D> {
        PolyRing::from_coefficients(
            (0..D)
                .map(|k| {
                    let v = (seed * 31 + k as u64 * 7) % 17;
                    from_centered::<Q5>(v as i64 - 8)
                })
                .collect(),
        )
    }

    #[test]
    fn schoolbook_product_has_the_full_unreduced_length() {
        let p = schoolbook(&elt(1), &elt(2));
        assert_eq!(p.len(), 2 * D - 1);
        // A hand-checkable case: (1 + X)·(1 − X) = 1 − X² unreduced.
        let a = PolyRing::<Q5, D>::from_coefficients(vec![Q5::ONE, Q5::ONE]);
        let b = PolyRing::<Q5, D>::from_coefficients(vec![Q5::ONE, Q5::ZERO - Q5::ONE]);
        let p = schoolbook(&a, &b);
        assert_eq!(p[0], Q5::ONE);
        assert_eq!(p[1], Q5::ZERO);
        assert_eq!(p[2], Q5::ZERO - Q5::ONE);
        assert!(p[3..].iter().all(|c| *c == Q5::ZERO));
    }

    #[test]
    fn residual_rebuilds_the_unreduced_product() {
        for seed in 0..6u64 {
            let a = elt(seed);
            let b = elt(seed + 100);
            let (c, rho) = negacyclic_residual(&a, &b);
            // `c` really is the ring product.
            assert_eq!(c, a.clone() * b.clone(), "seed {seed}: ring product");
            let mut cc = c.coefficients().to_vec();
            cc.resize(D, Q5::ZERO);
            let p = schoolbook(&a, &b);
            // `c + (X^D + 1)·ρ` is the unreduced product, low half first.
            for k in 0..D {
                let lifted = if k < rho.len() { cc[k] + rho[k] } else { cc[k] };
                assert_eq!(lifted, p[k], "seed {seed}: coefficient {k}");
            }
            // …and the high half is ρ itself, so deg ρ ≤ D − 2.
            for j in 0..D - 1 {
                assert_eq!(rho[j], p[j + D], "seed {seed}: residual {j}");
            }
            assert_eq!(rho.len(), D - 1);
        }
    }

    /// Hachi's whole reason to carry `ρ`: the lifted identity survives
    /// substituting `X = ζ` in the extension field, which is what turns the
    /// ring relation into a field inner-product claim a sumcheck can prove.
    #[test]
    fn the_lifted_identity_survives_substitution_in_the_extension_field() {
        const K: usize = 4;
        const A: u64 = 2;
        type F = ExtField<Q5, K, A>;

        for seed in 0..3u64 {
            let m = elt(seed);
            let z = elt(seed + 50);
            let (c, rho) = negacyclic_residual(&m, &z);
            for pow in [1u64, 3, 5, 7] {
                let zeta = F::z_generator().pow(pow);
                let lhs =
                    evaluate_at_base(&padded(&m), &zeta) * evaluate_at_base(&padded(&z), &zeta);
                let rhs = evaluate_at_base(&padded(&c), &zeta)
                    + (zeta.pow(D as u64) + F::one()) * evaluate_at_base(&rho, &zeta);
                assert_eq!(lhs, rhs, "seed {seed}, ζ = z^{pow}");
            }
        }
    }

    /// The padded coefficient vector of a ring element, length exactly `D`.
    fn padded<R: Ring, const D: usize>(p: &PolyRing<R, D>) -> Vec<R> {
        let mut v = p.coefficients().to_vec();
        v.resize(D, R::ZERO);
        v
    }

    #[test]
    fn relation_residual_matches_the_single_pair_case() {
        let m = elt(3);
        let z = elt(4);
        let w = m.clone() * z.clone();
        let rho = relation_residual(&[m.clone()], &[z.clone()], &w).expect("a relation");
        let (_, single) = negacyclic_residual(&m, &z);
        assert_eq!(rho, single);
    }

    #[test]
    fn relation_residual_accumulates_over_several_pairs() {
        let ms = [elt(1), elt(2), elt(3)];
        let zs = [elt(4), elt(5), elt(6)];
        let w = ms[0].clone() * zs[0].clone()
            + ms[1].clone() * zs[1].clone()
            + ms[2].clone() * zs[2].clone();
        let rho = relation_residual(&ms, &zs, &w).expect("a relation");
        // Rebuild the unreduced sum independently and check ρ against it.
        let mut unreduced = vec![Q5::ZERO; 2 * D - 1];
        for (m, z) in ms.iter().zip(zs.iter()) {
            for (acc, term) in unreduced.iter_mut().zip(schoolbook(m, z)) {
                *acc = *acc + term;
            }
        }
        for j in 0..D - 1 {
            assert_eq!(rho[j], unreduced[j + D]);
        }
    }

    #[test]
    fn a_value_that_is_not_the_relation_is_refused() {
        let ms = [elt(1)];
        let zs = [elt(2)];
        let wrong = elt(3) * elt(4);
        assert_eq!(
            relation_residual(&ms, &zs, &wrong),
            Err(SwitchingError::NotARelation)
        );
        let right = ms[0].clone() * zs[0].clone();
        assert_eq!(
            relation_residual(&ms, &[], &right),
            Err(SwitchingError::LengthMismatch {
                got: 0,
                expected: 1
            })
        );
    }

    #[test]
    fn a_sparse_relation_still_yields_a_residual() {
        // Zero high coefficients are exactly where a trimmed `PolyRing`
        // representation could hide a bug.
        let m = PolyRing::<Q5, D>::from_coefficients(vec![Q5::ONE]);
        let z = PolyRing::<Q5, D>::from_coefficients(vec![Q5::ONE]);
        let rho = relation_residual(&[m.clone()], &[z.clone()], &(m * z)).expect("a relation");
        assert!(rho.iter().all(|c| *c == Q5::ZERO));
    }
}
