//! Johnson–Lindenstrauss projection argument: `l2` shortness for committed
//! vectors (LaBRADOR's shortness layer, simplified ±1-entry variant).
//!
//! This is the *other* shortness mechanism in the LaBRADOR line, comple-
//! menting the digit-based one in [`crate::shortness::balanced`]: where the
//! digit argument certifies an `l∞` bound through decomposition, the
//! projection argument certifies an **`l2` bound** through random
//! dimensionality reduction (GHL21, modular Johnson–Lindenstrauss).
//!
//! # Statement
//!
//! The prover claims a committed vector `s ∈ R^m` (flattened to `m·D`
//! coefficients) satisfies `‖s‖₂ ≤ B`. The verifier draws a random
//! ±1-entry projection `Π: Z^{m·D} → Z^k` (from a seed, so no trusted
//! setup) and the prover reveals `p = Π·s`. Acceptance requires
//! `‖p‖₂ ≤ √(2k)·B`, which certifies `‖s‖₂ ≲ 2·B`:
//!
//! - **completeness**: for any fixed `s`, a random ±1 projection satisfies
//!   `E‖Πs‖₂² = k·‖s‖₂²` (cross terms vanish in expectation), so the
//!   honest `‖Πs‖₂` concentrates near `√k·‖s‖₂ ≤ √k·B < √(2k)·B`;
//! - **soundness**: for `s*` with `‖s*‖₂ ≥ β·B`, `‖Πs*‖ ≥ √(k/2)·‖s*‖₂ ≥
//!   β·√(k/2)·B` with probability `1 − e^{−Θ(k)}` (Hanson–Wright), which
//!   exceeds `√(2k)·B` whenever `β > 2` — the projection catches an
//!   inflated witness with probability increasing in `k`, *independent of
//!   the prover's adaptivity* (the projection is challenge, the response
//!   is a deterministic function of the fixed `s*`).
//!
//! LaBRADOR's own variant tunes the entry distribution to the tighter
//! `√(128/30) ≈ 2.07` gap and carries the correctness of `p` as extra
//! inner-product equations inside its amortized batch proof; here the
//! projection is a standalone, self-contained building block with a 2×
//! certified-bound gap and an explicit `k`-parameterized confidence.

use crate::foundation::sampling::uniform_matrix_from_seed;
use crate::instance::ring::{Z2Coeff, Z2Ring, D};
use algebra::ring::traits::CenteredRing;
use algebra::ring::PolynomialQuotientRing;

/// A ±1-entry projection matrix `Π ∈ {±1}^{k × dim}` derived from a seed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JLProjection {
    entries: Vec<Vec<i32>>,
    dim: usize,
}

impl JLProjection {
    /// Derives the projection from a seed. `k` rows (the reduced
    /// dimension), `dim` columns (the flattened coefficient count of the
    /// committed witness vectors).
    pub fn from_seed(seed: &[u8; 32], k: usize, dim: usize) -> Self {
        assert!(k > 0 && dim > 0);
        // ±1 entries from the raw-coefficient expansion (LSBs are uniform)
        let rows =
            uniform_matrix_from_seed::<Z2Coeff, D>(b"jl-projection", seed, k, dim.div_ceil(D));
        let entries = rows
            .iter()
            .map(|row| {
                let mut flat: Vec<i32> = row
                    .iter()
                    .flat_map(|r| r.coefficients())
                    .map(|c| if c.centered() % 2 == 0 { 1 } else { -1 })
                    .take(dim)
                    .collect();
                let pad = dim - flat.len();
                flat.extend(std::iter::repeat_n(1i32, pad));
                flat
            })
            .collect();
        Self { entries, dim }
    }

    /// Number of rows (reduced dimension `k`).
    pub fn rows(&self) -> usize {
        self.entries.len()
    }

    /// `p = Π·s` over the integers, with `s` given as centered
    /// representatives of the flattened coefficients.
    pub fn project(&self, s: &[i64]) -> Vec<i64> {
        assert_eq!(s.len(), self.dim, "projection input must be flattened");
        self.entries
            .iter()
            .map(|row| {
                row.iter()
                    .zip(s)
                    .map(|(e, c)| i64::from(*e) * c)
                    .sum::<i64>()
            })
            .collect()
    }
}

/// Flattens a ring vector to exactly `D` centered coefficients per element
/// (the stored coefficient slice may be truncated at trailing zeros).
fn centered_flat(r: &Z2Ring) -> Vec<i64> {
    let mut v: Vec<i64> = r.coefficients().iter().map(|c| c.centered()).collect();
    v.resize(D, 0);
    v
}

/// Prover side: flattens the centered coefficients of `s` and projects.
pub fn prove_l2_shortness(proj: &JLProjection, s: &[Z2Ring]) -> Vec<i64> {
    let flat: Vec<i64> = s.iter().flat_map(centered_flat).collect();
    proj.project(&flat)
}

/// Verifier side: acceptance certifies `‖s‖₂ ≲ 2·B` (see the module notes;
/// `√(2k)` acceptance threshold against the `√(k/2)` honest floor).
pub fn verify_l2_shortness(proj: &JLProjection, p: &[i64], claimed_bound: u64) -> bool {
    if p.len() != proj.rows() {
        return false;
    }
    let k = p.len() as u128;
    let b = u128::from(claimed_bound.max(1));
    // ‖p‖₂² ≤ 2k·B²  (integer math; the bound already carries the √2 slack)
    let square = p
        .iter()
        .map(|v| {
            let a = u128::from(v.unsigned_abs());
            a * a
        })
        .sum::<u128>();
    square <= 2 * k * b * b
}

/// The certified `l2` bound implied by acceptance: `2·B`.
pub fn certified_l2_bound(claimed_bound: u64) -> u64 {
    2 * claimed_bound
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::fixed_weight_poly;
    use algebra::crypto::sampling::BitStream;
    use algebra::crypto::xof::{Shake256Xof, Xof};

    const M: usize = 4;
    const K: usize = 64;

    /// Four ring elements, each carrying exactly one ±`c` coefficient:
    /// `‖s‖₂ = 2·|c|` exactly, so the honest/cheating split is arithmetic.
    fn sparse_vec(seed: u8, c: i64) -> Vec<Z2Ring> {
        let mut xof = Shake256Xof::new(&[seed]);
        let mut stream = BitStream::new(&mut xof);
        (0..M)
            .map(|_| fixed_weight_poly::<Z2Coeff, _, D>(&mut stream, 1, c.unsigned_abs() as u32))
            .collect()
    }

    #[test]
    fn honest_l2_bound_is_accepted() {
        let proj = JLProjection::from_seed(&[3u8; 32], K, M * D);
        let s = sparse_vec(9, 3); // ‖s‖₂ = 6
        let p = prove_l2_shortness(&proj, &s);
        assert!(verify_l2_shortness(&proj, &p, 64));
    }

    #[test]
    fn inflated_witness_is_rejected_with_high_probability() {
        // a 3.3× inflated norm (66 vs the claimed 20): β > 2, so the
        // projection must catch essentially every projection draw
        let mut caught = 0;
        for t in 0..20u8 {
            let proj = JLProjection::from_seed(&[t; 32], K, M * D);
            let s = sparse_vec(9, 33); // ‖s‖₂ = 66
            let p = prove_l2_shortness(&proj, &s);
            caught += u32::from(!verify_l2_shortness(&proj, &p, 20));
        }
        assert!(caught >= 19, "inflated witness caught only {caught}/20");
    }

    #[test]
    fn honest_bound_is_never_flagged_across_projections() {
        // the flip side: an honestly-bounded witness is never rejected
        for t in 0..20u8 {
            let proj = JLProjection::from_seed(&[t; 32], K, M * D);
            let s = sparse_vec(9, 3);
            let p = prove_l2_shortness(&proj, &s);
            assert!(
                verify_l2_shortness(&proj, &p, 64),
                "honest witness rejected by projection {t}"
            );
        }
    }
}
