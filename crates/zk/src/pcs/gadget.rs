//! Exact base-2 gadget decomposition (Z7, PCS support).
//!
//! The Greyhound gadget is `G_ℓ = I_ℓ ⊗ [1, 2, …, 2^{δ−1}] ∈ R^{ℓ×ℓδ}`:
//! it maps a digit vector (block layout `v[j·δ + k]` = digit `k` of value
//! `j`) to the value vector by digit recombination. Its inverse `G⁻¹`
//! splits every scalar coefficient of a ring element into its `δ = 23`
//! binary digits — the canonical representative `0..q` always fits, so the
//! split is *exact* (no slack, unlike the Z5 [`crate::shortness::gadget`]
//! flavor) and the output is binary with `‖·‖∞ = 1`.
//!
//! Greyhound applies the gadget three times: `sᵢ = G_m⁻¹(fᵢ)` on the
//! witness, `t̂ᵢ = G_n⁻¹(tᵢ)` on the inner commitments (which are not
//! short enough to feed the outer key), and `ŵ = G_r⁻¹(w)` on the row
//! combination — everywhere the verifier reconstructs values with `G`.

use crate::foundation::encoding::{ring_from_u32, ring_to_u32};
use crate::pcs::{RingElt, Z1Coeff, DELTA, DIM};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::{vec, vec::Vec};

/// Splits every scalar coefficient of each ring element into its `δ`
/// binary digits (block layout: `out[j·δ + k]` holds digit `k` of
/// `values[j]` at every coefficient position).
///
/// Exact inverse of [`recombine_digits`]; the output is always binary
/// (`‖·‖∞ = 1`), which is the soundness load of the norm gates.
pub fn decompose_digits(values: &[RingElt]) -> Vec<RingElt> {
    let mut out = Vec::with_capacity(values.len() * DELTA);
    for v in values {
        let rep = ring_to_u32::<Z1Coeff, DIM>(v);
        for k in 0..DELTA {
            let mut digits = [0u32; DIM];
            for (d, &c) in digits.iter_mut().zip(rep.iter()) {
                *d = (c >> k) & 1;
            }
            out.push(ring_from_u32::<Z1Coeff, DIM>(&digits));
        }
    }
    out
}

/// Recombines a block-layout digit vector into `digits.len() / δ` value
/// ring elements (the gadget map `G`). **Requires binary digits** — for
/// short-but-not-binary blocks (the folded opening `z`) use
/// [`recombine_digits_mod`].
///
/// Digit sums are computed in the `u32` representative domain: binary
/// digits across `δ = 23` positions sum to at most `2^23 − 1 < q`, so the
/// recombination is exact with no modular reduction.
///
/// # Panics
/// If `digits.len()` is zero or not a multiple of [`DELTA`] (debug builds
/// also reject non-binary digits, which would silently wrap in release).
pub fn recombine_digits(digits: &[RingElt]) -> Vec<RingElt> {
    assert!(
        !digits.is_empty() && digits.len() % DELTA == 0,
        "gadget digit vector must be a non-empty multiple of δ"
    );
    let reps: Vec<[u32; DIM]> = digits.iter().map(ring_to_u32::<Z1Coeff, DIM>).collect();
    (0..digits.len() / DELTA)
        .map(|j| {
            let mut rep = [0u32; DIM];
            for (k, block) in reps[j * DELTA..(j + 1) * DELTA].iter().enumerate() {
                for (r, &c) in rep.iter_mut().zip(block.iter()) {
                    debug_assert!(c <= 1, "recombine_digits requires binary digits");
                    *r += c << k;
                }
            }
            ring_from_u32::<Z1Coeff, DIM>(&rep)
        })
        .collect()
}

/// The gadget map `G` with **modular** digit recombination: output value
/// `j` is `Σ_k 2^k·digits[j·δ + k]` over `R_q`.
///
/// This is the variant for digit blocks that are short but not binary —
/// in the evaluation protocol that is the folded opening
/// `z = Σᵢ cᵢ·sᵢ` (norm `≤ r·d`, well below the gates, but far from
/// binary), where the `u32` shift path of [`recombine_digits`] would
/// overflow.
pub fn recombine_digits_mod(digits: &[RingElt]) -> Vec<RingElt> {
    assert!(
        !digits.is_empty() && digits.len() % DELTA == 0,
        "gadget digit vector must be a non-empty multiple of δ"
    );
    (0..digits.len() / DELTA)
        .map(|j| {
            // Horner from the top digit down: acc ← 2·acc + d_k, for
            // k = δ−1 … 0 (so d_0 ends with weight 2⁰).
            let mut acc = PolyRing::<Z1Coeff, DIM>::from_coefficients(vec![Z1Coeff::ZERO; DIM]);
            for (_, block) in digits[j * DELTA..(j + 1) * DELTA].iter().enumerate().rev() {
                let doubled = acc.clone() + &acc;
                acc = doubled + block.clone();
            }
            acc
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use algebra::ring::traits::CenteredRing;
    use algebra::ring::PolynomialQuotientRing;
    use alloc::vec;

    /// Deterministic test ring element with coefficients in `[-4, 4]`.
    fn test_elt(seed: u64) -> RingElt {
        let coeffs: Vec<_> = (0..DIM)
            .map(|j| from_centered::<Z1Coeff>(((seed as i64 * 7 + j as i64 * 5) % 9) - 4))
            .collect();
        algebra::ring::poly_ring::PolyRing::from_coefficients(coeffs)
    }

    #[test]
    fn decompose_recombine_is_exact_and_binary() {
        let values: Vec<RingElt> = (0..5).map(|i| test_elt(i + 1)).collect();
        let digits = decompose_digits(&values);
        assert_eq!(digits.len(), values.len() * DELTA);
        // every digit element is binary
        for d in &digits {
            for c in ring_to_u32::<Z1Coeff, DIM>(d) {
                assert!(c <= 1, "gadget digits must be binary");
            }
        }
        // recombination is the identity on the canonical representatives
        let rec = recombine_digits(&digits);
        assert_eq!(rec.len(), values.len());
        for (v, r) in values.iter().zip(&rec) {
            assert_eq!(
                ring_to_u32::<Z1Coeff, DIM>(v),
                ring_to_u32::<Z1Coeff, DIM>(r)
            );
        }
    }

    #[test]
    fn modular_recombine_matches_binary_path_and_wraps() {
        // On binary input both recombination paths agree exactly.
        let values: Vec<RingElt> = (0..3).map(|i| test_elt(i + 2)).collect();
        let digits = decompose_digits(&values);
        let fast = recombine_digits(&digits);
        let modular = recombine_digits_mod(&digits);
        for (f, m) in fast.iter().zip(&modular) {
            assert_eq!(
                ring_to_u32::<Z1Coeff, DIM>(f),
                ring_to_u32::<Z1Coeff, DIM>(m)
            );
        }

        // Short-but-not-binary digits: coefficients large enough to wrap
        // the u32 shift path (2^12 ≪ q) must reduce modulo q correctly.
        let mut heavy = [0u32; DIM];
        heavy[5] = 4096; // z-coefficient bound r·d ≪ 2^23
        let digit = ring_from_u32::<Z1Coeff, DIM>(&heavy);
        let block: Vec<RingElt> = (0..DELTA).map(|_| digit.clone()).collect();
        let out = &recombine_digits_mod(&block)[0];
        // coefficient 5 picks up Σ_k 2^k·4096 mod q, all others stay 0
        let expected = (4096u64 * ((1u64 << DELTA) - 1)) % 8_380_417;
        let rep = ring_to_u32::<Z1Coeff, DIM>(out);
        assert_eq!(rep[5], expected as u32);
        assert_eq!(rep[0], 0);
        assert_eq!(rep[6], 0);
    }

    #[test]
    fn recombine_rejects_bad_block_length() {
        let digits = decompose_digits(&[test_elt(1)]);
        let short = &digits[..digits.len() - 1];
        assert!(short.len() % DELTA != 0);
        let _ = std::panic::catch_unwind(|| recombine_digits(short))
            .expect_err("non-multiple of δ must panic");
    }

    #[test]
    fn digits_cover_full_coefficient_range() {
        // a coefficient at the top of the range needs all δ digits
        let mut coeffs = [0u32; DIM];
        coeffs[3] = 8_380_416; // q − 1
        let v = vec![ring_from_u32::<Z1Coeff, DIM>(&coeffs)];
        let rec = recombine_digits(&decompose_digits(&v));
        assert_eq!(ring_to_u32::<Z1Coeff, DIM>(&rec[0]), coeffs);
        // centered infinity norm of the digit elements is 1 everywhere
        for d in decompose_digits(&v) {
            for c in ring_to_u32::<Z1Coeff, DIM>(&d) {
                let centered = Z1Coeff::from(u64::from(c)).abs_infinity();
                assert!(centered <= 1);
            }
        }
    }
}
