//! Pairwise commitment folding (Z5, the base step of the LaBRADOR
//! amortized-compression route documented in `opening/mod.rs`).
//!
//! Two Ajtai-committed short vectors fold into one with a challenge
//! scalar, preserving the commitment by linearity
//! (`A·(s₁ + γ·s₂) = A·s₁ + γ·A·s₂`), and a JL projection certifies the
//! folded witness is short. This is the base step the log-depth pairwise
//! folding recursion is built from: level `i` folds pairs of level-`(i−1)`
//! commitments homomorphically, the bottom level reveals the folded
//! witness, and the JL certificate carries the shortness claim upward.

use crate::foundation::encoding::ring_to_u32;
use crate::instance::ring::{Z2Coeff, Z2Ring};
use crate::shortness::projection::{certified_l2_bound, verify_l2_shortness, JLProjection};
use crate::sumcheck::ipa::IpaKey;
use algebra::ring::traits::CenteredRing;
use alloc::vec::Vec;

/// A completed pairwise fold: the folded commitment, the folded witness
/// (revealed — the bottom level of a folding tree), and the JL certificate
/// of its shortness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoldedPair {
    /// `c* = c₁ + γ·c₂` — recomputable from the parent levels by linearity.
    pub c_star: Vec<Z2Ring>,
    /// `s* = s₁ + γ·s₂` — the folded witness (short, certified below).
    pub s_star: Vec<Z2Ring>,
    /// The claimed `l2` bound the JL certificate was checked against.
    pub claimed_bound: u64,
    /// The certified `l2` bound, from [`crate::shortness::projection::certified_l2_bound`]
    /// at *this* projection's row count — the GHL21 lower tail depends on how
    /// many rows were drawn, so a `None` here (too few rows, or the bound not
    /// fitting `u64`) refuses the fold rather than guessing a number.
    pub certified_bound: u64,
    /// `Π·s*` — the JL projection response (the shortness certificate's
    /// checkable data).
    pub proj_response: Vec<i64>,
}

/// Folds a pair of committed witnesses with the challenge:
/// `s* = s₁ + γ·s₂` (elementwise ring combination).
pub fn fold_pair(s1: &[Z2Ring], s2: &[Z2Ring], gamma: &Z2Ring) -> Vec<Z2Ring> {
    debug_assert_eq!(
        s1.len(),
        s2.len(),
        "folded witnesses must have equal length"
    );
    s1.iter()
        .zip(s2.iter())
        .map(|(a, b)| a.clone() + b.clone() * gamma)
        .collect()
}

/// Folds two commitment vectors the same way (`c* = c₁ + γ·c₂`).
pub fn fold_commitments(c1: &[Z2Ring], c2: &[Z2Ring], gamma: &Z2Ring) -> Vec<Z2Ring> {
    debug_assert_eq!(
        c1.len(),
        c2.len(),
        "folded commitments must have equal length"
    );
    c1.iter()
        .zip(c2.iter())
        .map(|(a, b)| a.clone() + b.clone() * gamma)
        .collect()
}

/// The centered integer coefficients of a ring element.
fn centered_coeffs(v: &Z2Ring) -> Vec<i64> {
    ring_to_u32(v)
        .iter()
        .map(|&c| Z2Coeff::from(u64::from(c)).centered())
        .collect()
}

/// Certifies the folded witness against the claimed `l2` bound through the
/// JL projection (the GHL21-tuned variant; see
/// [`crate::shortness::projection`]).
pub fn certify_short(proj: &JLProjection, s_star: &[Z2Ring], claimed_bound: u64) -> bool {
    let flat: Vec<i64> = s_star.iter().flat_map(centered_coeffs).collect();
    let response = proj.project(&flat);
    verify_l2_shortness(proj, &response, claimed_bound)
}

/// Runs one folding level: folds the pair, re-derives the folded
/// commitment by linearity, and certifies the folded witness is short
/// through the JL projection.
///
/// The parent commitments `c₁, c₂` must be the commitments of `s₁, s₂`
/// under `key` (the caller's recursion level supplies them; the check
/// re-derives the folded commitment by linearity).
///
/// # Errors
/// `None` if the JL certificate rejects (the folded witness is not short
/// at the claimed bound) — statistically increasing in the projection
/// dimension.
#[allow(clippy::too_many_arguments)]
pub fn fold_and_certify<const N: usize, const M: usize>(
    key: &IpaKey<N, M>,
    c1: &[Z2Ring],
    c2: &[Z2Ring],
    s1: &[Z2Ring],
    s2: &[Z2Ring],
    gamma: &Z2Ring,
    proj: &JLProjection,
    claimed_bound: u64,
) -> Option<FoldedPair> {
    let s_star = fold_pair(s1, s2, gamma);
    let c_star = fold_commitments(c1, c2, gamma);

    // the fold preserves the commitment (linearity of the Ajtai map)
    let recomputed = key.commit(&s_star);
    if recomputed.as_slice() != c_star.as_slice() {
        return None;
    }

    if !certify_short(proj, &s_star, claimed_bound) {
        return None;
    }
    let proj_response = proj.project(
        &s_star
            .iter()
            .flat_map(centered_coeffs)
            .collect::<Vec<i64>>(),
    );
    Some(FoldedPair {
        c_star,
        s_star,
        claimed_bound,
        certified_bound: certified_l2_bound(proj.rows(), claimed_bound)?,
        proj_response,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::encoding::ring_from_u32;
    use crate::foundation::sampling::centered_bounded_poly;
    use crate::instance::ring::D;
    use algebra::crypto::sampling::BitStream;
    use algebra::crypto::xof::{Shake256Xof, Xof};

    const N: usize = 8;
    const M: usize = 4;

    fn key_of(seed: u8) -> IpaKey<N, M> {
        IpaKey::setup(&[seed; 32])
    }

    /// The ring element with constant coefficient `v`.
    fn ring_elt(v: u64) -> Z2Ring {
        ring_from_u32(&{
            let mut c = [0u32; D];
            c[0] = v as u32;
            c
        })
    }

    /// Dense small-coefficient witness (each coefficient in [−b, b]).
    fn witness(seed: u8, b: u32) -> Vec<Z2Ring> {
        let mut xof = Shake256Xof::new(&[seed]);
        let mut stream = BitStream::new(&mut xof);
        (0..M)
            .map(|_| centered_bounded_poly::<Z2Coeff, _, D>(&mut stream, b))
            .collect()
    }

    fn commit(key: &IpaKey<N, M>, w: &[Z2Ring]) -> Vec<Z2Ring> {
        key.commit(w).to_vec()
    }

    #[test]
    fn fold_preserves_commitment_and_certifies_shortness() {
        let key = key_of(1);
        let s1 = witness(2, 3);
        let s2 = witness(3, 3);
        let c1 = commit(&key, &s1);
        let c2 = commit(&key, &s2);
        // a small unit-scale challenge keeps the folded witness within the
        // claimed bound (a random large γ scales the fold's norm by |γ|)
        let gamma = ring_elt(1);

        let s_star = fold_pair(&s1, &s2, &gamma);
        let c_star = fold_commitments(&c1, &c2, &gamma);
        let recomputed = key.commit(&s_star);
        assert_eq!(recomputed.as_slice(), c_star.as_slice());

        // 256 rows, not 128: `certified_l2_bound` refuses below
        // `GHL21_MIN_ROWS`, so a fold that is supposed to certify has to draw
        // enough projection rows to have a certificate at all.
        let proj = JLProjection::from_seed(
            &[5u8; 32],
            crate::shortness::projection::GHL21_MIN_ROWS,
            M * D,
        );
        let folded = fold_and_certify(&key, &c1, &c2, &s1, &s2, &gamma, &proj, 64);
        let folded = folded.expect("short fold must certify");
        assert_eq!(
            folded.certified_bound,
            certified_l2_bound(proj.rows(), 64).expect("the same row count certifies"),
            "the emitted bound must be the one the projection's rows support"
        );
        // the JL response is consistent with the folded witness
        let flat: Vec<i64> = s_star.iter().flat_map(centered_coeffs).collect();
        assert_eq!(folded.proj_response, proj.project(&flat));
    }

    #[test]
    fn inflated_fold_fails_the_jl_certificate() {
        let key = key_of(2);
        // s2 inflated (bound 30): the folded witness norm ≈ 8× claimed 40,
        // so the JL certificate must reject (β ≫ 2)
        let s1 = witness(4, 3);
        let s2 = witness(5, 30);
        let c1 = commit(&key, &s1);
        let c2 = commit(&key, &s2);
        let gamma = ring_elt(1);
        let proj = JLProjection::from_seed(
            &[6u8; 32],
            crate::shortness::projection::GHL21_MIN_ROWS,
            M * D,
        );

        // The floor must not be what makes this pass. Below
        // `GHL21_MIN_ROWS` every fold refuses for want of a certificate, and
        // the `is_none()` assertion below would then hold even if the norm gate
        // were removed entirely — so pin the gate itself, then the composite.
        assert!(
            crate::shortness::projection::certified_l2_bound(proj.rows(), 40).is_some(),
            "the fixture must sit above the certificate floor"
        );
        assert!(
            !certify_short(&proj, &fold_pair(&s1, &s2, &gamma), 40),
            "the JL norm gate itself must reject the inflated fold"
        );
        let folded = fold_and_certify(&key, &c1, &c2, &s1, &s2, &gamma, &proj, 40);
        assert!(
            folded.is_none(),
            "the inflated fold must fail the JL certificate"
        );

        // a genuinely short fold with the same claimed bound certifies
        let s_short = witness(9, 2);
        let c_short = commit(&key, &s_short);
        let short_fold = fold_and_certify(&key, &c1, &c_short, &s1, &s_short, &gamma, &proj, 40);
        assert!(
            short_fold.is_some(),
            "the same gate must accept a genuinely short fold at the same bound"
        );
    }

    #[test]
    fn fold_is_linear_in_the_challenge() {
        // folding twice composes: fold(s1, fold(s2, s3, γ2), γ1) preserves
        // the commitment chain Σ over the three witnesses
        let key = key_of(3);
        let s1 = witness(6, 2);
        let s2 = witness(7, 2);
        let s3 = witness(8, 2);
        let c1 = commit(&key, &s1);
        let c2 = commit(&key, &s2);
        let c3 = commit(&key, &s3);
        let g1 = ring_elt(11);
        let g2 = ring_elt(23);

        // fold (s2, s3) with g2, then fold s1 in with g1
        let s23 = fold_pair(&s2, &s3, &g2);
        let c23 = fold_commitments(&c2, &c3, &g2);
        let s_star = fold_pair(&s1, &s23, &g1);
        let c_star = fold_commitments(&c1, &c23, &g1);
        assert_eq!(key.commit(&s_star).as_slice(), c_star.as_slice());
    }
}
