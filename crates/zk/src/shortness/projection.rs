//! Johnson–Lindenstrauss projection argument: `l2` shortness for committed
//! vectors (LaBRADOR's shortness layer, GHL21-tuned entry distribution).
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
//! projection `Π: Z^{m·D} → Z^k` with **tuned entries** — `0` with
//! probability `1/2`, `±1` with probability `1/4` each (the GHL21
//! distribution; derived from a seed, so no trusted setup) — and the
//! prover reveals `p = Π·s`. Acceptance requires `‖p‖₂² ≤ k·B²`, which
//! certifies `‖s‖₂ ≲ √(128/30)·B ≈ 2.07·B`:
//!
//! - **completeness**: for any fixed `s`, the tuned projection satisfies
//!   `E‖Πs‖₂² = (k/2)·‖s‖₂²` (each entry kills its term with probability
//!   `1/2`), so the honest `‖Πs‖₂` concentrates near `√(k/2)·‖s‖₂ ≤
//!   √(k/2)·B < √k·B`;
//! - **soundness**: for `s*` with `‖s*‖₂ ≥ β·B`, `‖Πs*‖₂ ≥ √(k/4)·‖s*‖₂ ≥
//!   β·√(k/4)·B` with probability `1 − e^{−Θ(k)}` (Hanson–Wright), which
//!   exceeds `√k·B` whenever `β > 2` — the projection catches an inflated
//!   witness with probability increasing in `k`, *independent of the
//!   prover's adaptivity* (the projection is challenge, the response is a
//!   deterministic function of the fixed `s*`).
//!
//! The certified constant `√(128/30) ≈ 2.07` is the GHL21 extraction gap
//! for the tuned entry distribution (LaBRADOR's norm-check analysis; the
//! earlier revision of this module reported the cruder `2·B` closure of a
//! ±1-entry variant). `k` parameterizes the confidence; the sparse-cheater
//! rejection probability is `3^{−K}`-shaped (a single inflated coefficient
//! survives only if all `K` rows miss it). As in LaBRADOR, the correctness
//! of `p` can be carried as extra inner-product equations inside an
//! amortized batch proof; here the projection is a standalone,
//! self-contained building block with an explicit `k`-parameterized
//! confidence.

use crate::foundation::encoding::{ring_from_u32, ring_to_u32};
use crate::foundation::fs::absorb_rings;
use crate::foundation::sampling::{uniform_matrix_from_seed, uniform_ring_from_seed};
use crate::instance::ring::{Z2Coeff, Z2Ring, D};
use crate::sumcheck::ipa::{ipa_prove, ipa_verify, ring_inner_product, IpaKey, IpaProof};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::traits::CenteredRing;
use algebra::ring::PolynomialQuotientRing;
use alloc::{vec, vec::Vec};

/// Numerator of the conservative rational closure `1033/500 ≥ √(128/30)`
/// of the GHL21 extraction gap.
const GHL21_GAP_NUM: u64 = 1033;
/// Denominator of the conservative rational closure `1033/500 ≥ √(128/30)`.
const GHL21_GAP_DEN: u64 = 500;

/// A projection matrix `Π ∈ {0,±1}^{k × dim}` with the GHL21 tuned entry
/// distribution (`P(0) = 1/2`, `P(±1) = 1/4` each) derived from a seed.
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
        // two uniform bits per entry from the raw-coefficient expansion:
        // (hi, lo) = (0, 0) → 0, (0, 1) → +1, (1, 0) → −1, (1, 1) → 0 —
        // exactly P(0) = 1/2, P(±1) = 1/4
        let rows =
            uniform_matrix_from_seed::<Z2Coeff, D>(b"jl-projection", seed, k, dim.div_ceil(D));
        let entries = rows
            .iter()
            .map(|row| {
                let mut flat: Vec<i32> = row
                    .iter()
                    .flat_map(|r| r.coefficients())
                    .map(|c| {
                        let v = c.centered();
                        match (v & 2, v & 1) {
                            (0, 0) => 0,
                            (0, _) => 1,
                            (_, 0) => -1,
                            (_, _) => 0,
                        }
                    })
                    .take(dim)
                    .collect();
                let pad = dim - flat.len();
                // padding entries are the neutral 0 (contributes nothing to
                // the projection — unbiased under the tuned distribution)
                flat.extend(core::iter::repeat_n(0i32, pad));
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

/// Verifier side: acceptance certifies `‖s‖₂ ≲ √(128/30)·B ≈ 2.07·B` —
/// the GHL21 extraction gap for the tuned `{0,±1}` distribution (`√k`
/// acceptance threshold against the `√(k/4)` Hanson–Wright floor).
pub fn verify_l2_shortness(proj: &JLProjection, p: &[i64], claimed_bound: u64) -> bool {
    if p.len() != proj.rows() {
        return false;
    }
    let k = p.len() as u128;
    let b = u128::from(claimed_bound.max(1));
    // ‖p‖₂² ≤ k·B²  (integer math; twice the tuned expectation (k/2)·B²,
    // mirroring the acceptance slack of the GHL21 norm check)
    let square = p
        .iter()
        .map(|v| {
            let a = u128::from(v.unsigned_abs());
            a * a
        })
        .sum::<u128>();
    square <= k * b * b
}

/// The certified `l2` bound implied by acceptance: the GHL21 extraction
/// gap `⌈√(128/30)·B⌉ ≈ 2.07·B`, via the conservative rational closure
/// `1033/500 ≥ √(128/30)` (rounding up keeps the certificate sound).
pub fn certified_l2_bound(claimed_bound: u64) -> u64 {
    (claimed_bound
        .saturating_mul(GHL21_GAP_NUM)
        .saturating_add(GHL21_GAP_DEN - 1))
        / GHL21_GAP_DEN
}

/// **Amortized integration** (the LaBRADOR shape): the JL bound check on
/// the revealed response `p` is bound to the *committed* witness through
/// inner-product equations carried by the gadget-IPA line — all `k` row
/// claims `⟨πᵢ, s⟩ = pᵢ` amortize into **one** IPA on the γ-combined row
/// `Π_γ = Σ γⁱ·πᵢ` (survey row 17, "amortized integration").
///
/// The projection rows act coefficient-position-wise across the `M` ring
/// elements (`pᵢ[t] = Σⱼ πᵢ[j][t]·s[j][t]`), a structured JL family with
/// independent entries over `(row, element, position)` — the same
/// concentration accounting as the flat variant.
///
/// # Statement
///
/// Public: IPA commitment key, the projection rows, the witness
/// commitment `c = A_com·s`, the claimed bound `B`. Witness: `s` with
/// `‖s‖₂ ≤ B`. First message: `p = Π·s` (revealed, norm-gated); the
/// challenges derive after `(c, Π, p)`; the single IPA binds
/// `⟨Π_γ, s⟩ = Σ γⁱ·pᵢ`.
///
/// # Errors
/// `None` if the response fails the norm gate (the honest witness never
/// triggers it; an inflated witness is caught here without grinding).
pub fn prove_l2_bound_amortized<const N: usize, const M: usize>(
    key: &IpaKey<N, M>,
    key_seed: &[u8; 32],
    pi_rows: &[Vec<Z2Ring>],
    s: &[Z2Ring],
    claimed_bound: u64,
    mask_seed: &[u8; 32],
) -> Option<(Vec<Z2Ring>, AmortizedL2Proof<N>)> {
    let c = key.commit(s);
    let p: Vec<Z2Ring> = pi_rows
        .iter()
        .map(|row| ring_inner_product(row, s))
        .collect();

    // norm gate on the revealed response: ‖p‖₂² ≤ k·B² over all
    // coefficients (twice the tuned expectation (k/2)·B²)
    if response_square(&p) > norm_budget(pi_rows.len(), claimed_bound) {
        return None;
    }

    let gamma = amortized_gamma(key_seed, pi_rows, &c, &p);

    // Π_γ = Σ γⁱ·πᵢ (entry-wise γ-weighting) and P* = Σ γⁱ·pᵢ
    let mut pi_combined = vec![ring_zero(); s.len()];
    let mut p_comb = ring_zero();
    let mut weight = ring_one();
    for (row, p_i) in pi_rows.iter().zip(&p) {
        for (dst, entry) in pi_combined.iter_mut().zip(row.iter()) {
            *dst += entry.clone() * &weight;
        }
        p_comb += p_i.clone() * &weight;
        weight *= gamma.clone();
    }
    let ipa = ipa_prove(key, key_seed, s, &pi_combined, p_comb, mask_seed);
    Some((c, AmortizedL2Proof { p, gamma, ipa }))
}

/// Verifier side of the amortized integration: the norm gate on the
/// revealed `p`, and the single γ-combined IPA binding `p` to the
/// committed witness.
pub fn verify_l2_bound_amortized<const N: usize, const M: usize>(
    key: &IpaKey<N, M>,
    key_seed: &[u8; 32],
    pi_rows: &[Vec<Z2Ring>],
    c: &[Z2Ring],
    claimed_bound: u64,
    proof: &AmortizedL2Proof<N>,
) -> bool {
    if response_square(&proof.p) > norm_budget(pi_rows.len(), claimed_bound) {
        return false;
    }

    let gamma = amortized_gamma(key_seed, pi_rows, c, &proof.p);
    let mut pi_combined = vec![ring_zero(); M];
    let mut p_comb = ring_zero();
    let mut weight = ring_one();
    for (row, p_i) in pi_rows.iter().zip(&proof.p) {
        for (dst, entry) in pi_combined.iter_mut().zip(row.iter()) {
            *dst += entry.clone() * &weight;
        }
        p_comb += p_i.clone() * &weight;
        weight *= gamma.clone();
    }
    ipa_verify(key, key_seed, c, &pi_combined, p_comb, &proof.ipa)
}

/// The γ batch weight binding `(c, Π, p)` — the standard three-step
/// Fiat–Shamir shape (absorb → seed → labeled re-expansion).
fn amortized_gamma(
    key_seed: &[u8; 32],
    pi_rows: &[Vec<Z2Ring>],
    c: &[Z2Ring],
    p: &[Z2Ring],
) -> Z2Ring {
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z5/projection-amortized");
    tr.absorb(b"key", key_seed);
    let flat: Vec<Z2Ring> = pi_rows.iter().flatten().cloned().collect();
    absorb_rings(&mut tr, b"pi", &flat);
    absorb_rings(&mut tr, b"c", c);
    absorb_rings(&mut tr, b"p", p);
    let seed = tr.challenge_bytes(64);
    uniform_ring_from_seed::<Z2Coeff, D>(b"gamma", &seed)
}

/// `Σ coefficients of Π·s` squared: the response norm gate budget
/// `k·B²` over all `k·D` response coefficients.
fn norm_budget(rows: usize, claimed_bound: u64) -> u128 {
    let k = (rows * D) as u128;
    let b = u128::from(claimed_bound.max(1));
    k * b * b
}

/// `‖p‖₂²` over all response coefficients.
fn response_square(p: &[Z2Ring]) -> u128 {
    use algebra::ring::traits::CenteredRing;
    let mut square: u128 = 0;
    for elt in p {
        for &c in ring_to_u32(elt).iter() {
            let v = u128::from(Z2Coeff::from(u64::from(c)).centered().unsigned_abs());
            square += v * v;
        }
    }
    square
}

/// The zero ring element.
fn ring_zero() -> Z2Ring {
    ring_from_u32(&[0u32; D])
}

/// The multiplicative identity ring element.
fn ring_one() -> Z2Ring {
    ring_from_u32(&{
        let mut c = [0u32; D];
        c[0] = 1;
        c
    })
}

/// The amortized JL bound proof: revealed response `p`, the batch weight
/// `γ`, and the single IPA binding all `k` row claims at once.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AmortizedL2Proof<const N: usize> {
    /// The revealed response `p = Π·s` (norm-gated).
    pub p: Vec<Z2Ring>,
    /// The γ batch weight binding `(c, Π, p)`.
    pub gamma: Z2Ring,
    /// The one IPA: `⟨Π_γ, s⟩ = Σ γⁱ·pᵢ`.
    pub ipa: IpaProof<N>,
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

    #[test]
    fn certified_bound_is_the_ghl21_constant() {
        // ⌈√(128/30)·B⌉ via the conservative closure 1033/500 = 2.066
        assert_eq!(certified_l2_bound(1000), 2066);
        assert_eq!(certified_l2_bound(64), 133);
        assert_eq!(certified_l2_bound(1), 3);
        // monotone in the claimed bound
        assert!(certified_l2_bound(63) <= certified_l2_bound(64));
        assert!(certified_l2_bound(64) < certified_l2_bound(65));
    }

    #[test]
    fn entries_follow_the_tuned_distribution() {
        // the GHL21 distribution: half the entries are 0, a quarter each
        // ±1 (statistical bounds over a large derived matrix)
        let proj = JLProjection::from_seed(&[7u8; 32], 64, 8192);
        let mut zeros = 0u64;
        let mut plus = 0u64;
        let mut minus = 0u64;
        for row in &proj.entries {
            for &e in row {
                match e {
                    0 => zeros += 1,
                    1 => plus += 1,
                    -1 => minus += 1,
                    other => panic!("entry {other} outside {{0,±1}}"),
                }
            }
        }
        let total = (64 * 8192) as u64;
        let pct_zero = zeros * 100 / total;
        assert!(
            (48..=52).contains(&pct_zero),
            "P(0) ≈ 1/2, got {zeros}/{total}"
        );
        assert!(
            plus.abs_diff(minus) * 100 / total <= 2,
            "P(+1) ≈ P(−1) ≈ 1/4, got +{plus}/−{minus}"
        );
    }
    // --- amortized integration (`prove_l2_bound_amortized`) ---

    const AM_N: usize = 8;
    const AM_M: usize = 4;

    /// Dense honest witness: every coefficient centered-bounded in [−3, 3]
    /// (‖s‖₂ ≈ √(M·D)·1.8 ≈ 29 for M=4, D=64).
    fn dense_witness(seed: u8, bound: u32) -> Vec<Z2Ring> {
        let mut xof = Shake256Xof::new(&[seed]);
        let mut stream = BitStream::new(&mut xof);
        (0..AM_M)
            .map(|_| {
                crate::foundation::sampling::centered_bounded_poly::<Z2Coeff, _, D>(
                    &mut stream,
                    bound,
                )
            })
            .collect()
    }

    /// k projection rows, each a full `R^M` ring vector with dense
    /// coefficients in [−1, 1] (the block-circulant {0,±1}-style entry
    /// family: row `i` acts through the ring inner product).
    fn amortized_rows(seed: u8, k: usize) -> Vec<Vec<Z2Ring>> {
        (0..k)
            .map(|i| {
                let mut xof = Shake256Xof::new(&[seed, i as u8]);
                let mut stream = BitStream::new(&mut xof);
                (0..AM_M)
                    .map(|_| {
                        crate::foundation::sampling::centered_bounded_poly::<Z2Coeff, _, D>(
                            &mut stream,
                            1,
                        )
                    })
                    .collect()
            })
            .collect()
    }

    #[test]
    fn amortized_l2_bound_honest_roundtrip() {
        let key = IpaKey::<AM_N, AM_M>::setup(&[41u8; 32]);
        let key_seed = [42u8; 32];
        let rows = amortized_rows(1, 8);
        let s = dense_witness(5, 3);
        let claimed = 64;

        let (c, proof) = prove_l2_bound_amortized(&key, &key_seed, &rows, &s, claimed, &[7u8; 32])
            .expect("honest norm gate passes");
        assert!(verify_l2_bound_amortized(
            &key, &key_seed, &rows, &c, claimed, &proof
        ));

        // determinism
        let (c2, proof2) =
            prove_l2_bound_amortized(&key, &key_seed, &rows, &s, claimed, &[7u8; 32]).unwrap();
        assert_eq!(c, c2);
        assert_eq!(proof, proof2);

        // the amortization: ONE IPA response vector for all 8 row claims
        assert_eq!(proof.ipa.alpha_prime.len(), AM_M);
    }

    #[test]
    fn amortized_l2_bound_rejects_inflated_and_tampered() {
        let key = IpaKey::<AM_N, AM_M>::setup(&[43u8; 32]);
        let key_seed = [44u8; 32];
        let rows = amortized_rows(2, 8);
        let s = dense_witness(6, 3);
        // claimed 40 covers the honest norm (~29) with 8× of headroom in
        // the response budget, while an 8.7×-inflated witness cannot fit
        let claimed = 40;

        // a 16× inflated witness trips the norm gate immediately (no
        // proof is produced — the gate IS the check on the revealed p)
        // β = ‖big‖/claimed ≈ 8.7 > 2: the JL gate must reject w.h.p.
        let big = dense_witness(7, 60);
        assert!(
            prove_l2_bound_amortized(&key, &key_seed, &rows, &big, claimed, &[7u8; 32]).is_none()
        );

        // a valid-norm witness whose response is inconsistent with the
        // commitment fails the γ-combined IPA link
        let s_other = dense_witness(8, 2);
        let (_c2, proof_other) =
            prove_l2_bound_amortized(&key, &key_seed, &rows, &s_other, claimed, &[7u8; 32])
                .expect("in window");
        let (c, proof) =
            prove_l2_bound_amortized(&key, &key_seed, &rows, &s, claimed, &[7u8; 32]).unwrap();
        assert!(!verify_l2_bound_amortized(
            &key,
            &key_seed,
            &rows,
            &c,
            claimed,
            &proof_other
        ));
        assert!(verify_l2_bound_amortized(
            &key, &key_seed, &rows, &c, claimed, &proof
        ));

        // tampering with the revealed response breaks the IPA link
        let mut bad = proof.clone();
        let mut coeffs = crate::foundation::encoding::ring_to_u32(&bad.p[1]);
        coeffs[3] = coeffs[3].wrapping_add(5);
        bad.p[1] = crate::foundation::encoding::ring_from_u32(&coeffs);
        assert!(!verify_l2_bound_amortized(
            &key, &key_seed, &rows, &c, claimed, &bad
        ));
    }
}
