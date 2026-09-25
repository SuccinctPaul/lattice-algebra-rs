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
//! prover reveals `p = Π·s`. Acceptance requires `‖p‖₂² ≤ (k/2)·B²`, which
//! at `k = 256` is LaBRADOR's `‖p‖ ≤ √128·β` and certifies
//! `‖s‖₂ ≤ √(128/30)·B ≈ 2.07·B`:
//!
//! - **completeness**: for any fixed `s`, the tuned projection satisfies
//!   `E‖Πs‖₂² = (k/2)·‖s‖₂²` (each entry contributes with probability `1/2`),
//!   so the acceptance threshold sits *at the mean* and an honest prover clears
//!   it about half the time — LaBRADOR §4 "Projecting" (p. 12): "The verifier
//!   checks that `‖p⃗‖ ≤ √128 β`. **This is true with probability 1/2**, but the
//!   prover can request projection matrices until it is the case."
//! - **soundness**: GHL21 Corollary 3.2's lower tail, `Pr[‖Πw‖₂ < √30·‖w‖₂] ≲
//!   2^{−128}`, turns the same acceptance into `‖s‖₂² ≤ (k/2)B²/30`. At `k = 256`
//!   that is exactly `(128/30)B²`.
//!
//! # Where √(128/30) comes from, and why √(128/29) is not a correction to it
//!
//! GHL21 is **Gentry–Halevi–Lyubashevsky**, "Practical non-interactive
//! publicly verifiable secret sharing with thousands of parties", IACR ePrint
//! 2021/1397 (LaBRADOR's bibliography entry `GHL21`, and the citation
//! LaBRADOR §4 p. 9 attributes the modular JL lemma to: "Gentry, Halevi, and
//! Lyubashevsky argue that regardless of the vector `w⃗`, with overwhelming
//! probability, the ℓ2-norm cannot be much higher or lower"). The statement
//! this module implements is **Corollary 3.2** (GHL21 p. 16, restated as
//! LaBRADOR Lemma 4.1 p. 10):
//!
//! > "Let `D` be a distribution on `{0, ±1}` such that `D(1) = D(−1) = 1/4` and
//! > `D(0) = 1/2`. Under the heuristic substitution of `D` with `(1/√2)N`, for
//! > every vector `w ∈ Z^d`: `Pr_{R←D^{d×256}}[‖wR‖₂² < 30‖w‖₂²] ⪅ 2^{−128}`,
//! > `Pr_{R←D^{d×256}}[‖wR‖₂² > 337‖w‖₂²] ⪅ 2^{−128}`."
//!
//! Three facts are load-bearing and all three are now enforced here:
//!
//! 1. **the entry law**. `D(0) = 1/2`, `D(±1) = 1/4` — exactly
//!    [`JLProjection::from_seed`]'s distribution, so `√(128/30)` is *our*
//!    constant and needs no change. (The ratio is mean/floor = `128/30`: the
//!    mean of `‖wR‖²/‖w‖²` is `256·E[π²] = 128`, the certified floor is `30`;
//!    `337` is the matching upper tail, which is what Grand Danois' `√(337/30)`
//!    extractor slack reads from the same corollary.)
//! 2. **the row count**. The `30` is stated for `R ← D^{d×256}`. Measured here
//!    (numpy, 32 000 draws of `Π ∈ {0,±1}^{d×k}`, `d = 256`, uniform `w` with
//!    coordinates in `[−700, 700]`): the ratio `‖Πw‖²/‖w‖²` has mean `127.91`
//!    at `k = 256` (`= k/2`, as the corollary predicts) with minimum `83.60`,
//!    so `30` is a comfortable bound — but at `k = 64` the ratio falls below
//!    `30` in **38.0%** of draws and at `k = 8` in **100%**. The floor is
//!    therefore *not* available below 256 rows, and
//!    [`certified_l2_bound`] now refuses to name a gap for `k < 256`
//!    instead of quoting one.
//! 3. **the acceptance anchor**. `√128 = √(k/2)`, not `√k`. This module used to
//!    gate at `‖p‖₂² ≤ k·B²` while quoting `√(128/30)`; those two are
//!    inconsistent by a factor `√2` (the same floor licenses `√(k/60)·B =
//!    2.92·B` at `k = 256` against that threshold). The gate is now `(k/2)·B²`,
//!    which is *stricter* — it accepts a subset of what it used to — and is the
//!    anchor the citation is actually stated against. Confirmed by the same
//!    measurement: honest acceptance at `(k/2)B²` is `0.5157` at `k = 256`,
//!    i.e. LaBRADOR's "probability 1/2", whereas the old `kB²` threshold
//!    accepted with probability `1.0000`.
//!
//! Akita's `√(128/29)` (2026/1983 §13 p. 126, "Calibrating Greyhound": "the
//! original dense-sign projection does not match the distribution required by
//! the certified lower-tail bound. We replace it with a sparse-ternary
//! projection and use the corresponding norm slack `√128/29` in place of `2`")
//! is **not** a correction to this module. It is Akita's recalibration of
//! *Greyhound's* JL norm check — Akita itself "uses no Johnson–Lindenstrauss
//! projection" (p. 10) — and it moves from a dense `±1` projection to the
//! sparse-ternary law this module already draws. The measurement above
//! reproduces why that move was forced: for dense `±1` the mean of the ratio is
//! `k` (`256.0` measured at `k = 256`, minimum `174.7`), so a `√128·B` anchor
//! rejects an honest prover with probability `1.0000`. `29 < 30` also makes
//! their slack *looser*, not tighter, so adopting it here would only weaken a
//! correctly-derived bound; it is rejected.
//!
//! The modular caveat stays GHL21's own: Corollary 3.3 (p. 17) is the
//! `mod P` variant and needs `b ≤ P/(45d)`; LaBRADOR Lemma 4.2 (p. 10)
//! strengthens that to `b ≤ q/125` for a small modulus. Callers working mod `q`
//! must satisfy one of those, which is why the response here is revealed as
//! integers in [`prove_l2_shortness`] and the mod-`q` form is confined to the
//! amortized variant, whose `p` is committed.
//!
//! `k` parameterizes the confidence; the sparse-cheater rejection probability
//! is `3^{−K}`-shaped (a single inflated coefficient survives only if all `K`
//! rows miss it). As in LaBRADOR, the correctness of `p` can be carried as extra
//! inner-product equations inside an amortized batch proof; here the projection
//! is a standalone, self-contained building block with an explicit `k`-
//! parameterized confidence.

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

/// GHL21 Corollary 3.2 states its tails for `R ← D^{d×256}`: `256` rows is the
/// dimension the certified floor `√30` is licensed at, and more rows only help
/// (dropping rows cannot shrink `‖Πw‖₂²`, so the bound holds for every
/// `k ≥ 256`). Below it the floor is not available.
pub const GHL21_MIN_ROWS: usize = 256;

/// The certified lower tail of GHL21 Corollary 3.2, as a squared ratio:
/// `‖Πw‖₂² ≥ 30·‖w‖₂²` except with probability `≲ 2^{−128}`.
const GHL21_LOWER_TAIL_SQ: u128 = 30;

/// The honest mean of `‖Πw‖₂²/‖w‖₂²` per row under the tuned law
/// (`E[π²] = 1/2`), as a reciprocal: the acceptance anchor is `(k/2)·B²`, which
/// at `k = 256` is LaBRADOR's `128·B²`.
const TUNED_MEAN_HALF_ROWS: u128 = 2;

/// The smallest integer `c` with `denom·c² ≥ numer`, by bisection on `u128`.
///
/// Rounding *up* is what keeps a certified bound sound: `c` must never be
/// smaller than the real `√(numer/denom)`.
fn ceil_sqrt_ratio(numer: u128, denom: u128) -> Option<u128> {
    if denom == 0 {
        return None;
    }
    if numer == 0 {
        return Some(0);
    }
    // `c² ≤ numer/denom ≤ numer`, so `c ≤ √numer + 1 ≤ 2^64` for any `u128`.
    let mut lo = 0u128;
    let mut hi = 1u128 << 64;
    while lo + 1 < hi {
        let mid = lo + ((hi - lo) / 2);
        // Saturating, not `checked`: the first midpoint is `2^63`, so
        // `mid²·denom` overflows `u128` for *every* input with `denom ≥ 4`
        // (`2^126·60 > u128::MAX`). With `checked_mul` and `?` that aborted the
        // search and returned `None` unconditionally — which is how
        // `certified_l2_bound` came to refuse every honest fold in the crate.
        // Saturation is sound in the right direction: an overflowed product is
        // certainly `≥ numer`, so the bracket shrinks as it should.
        let square = mid.saturating_mul(mid).saturating_mul(denom);
        if square >= numer {
            hi = mid;
        } else {
            lo = mid;
        }
    }
    Some(hi)
}

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

/// Verifier side: `‖p‖₂² ≤ (k/2)·B²`, the GHL21/LaBRADOR anchor `√128·β` written
/// for a general row count (`√128 = √(256/2)` at `k = 256`). At `k = 256` an
/// honest prover meets it about half the time and can grind projections until it
/// does; the certified gap it buys is [`certified_l2_bound`].
pub fn verify_l2_shortness(proj: &JLProjection, p: &[i64], claimed_bound: u64) -> bool {
    if p.len() != proj.rows() {
        return false;
    }
    let k = p.len() as u128;
    let b = u128::from(claimed_bound.max(1));
    // ‖p‖₂² ≤ (k/2)·B², in integers as 2·‖p‖₂² ≤ k·B² (never a float, never a
    // rounding-down division: an odd `k` must not silently halve the budget).
    let square = p
        .iter()
        .map(|v| {
            let a = u128::from(v.unsigned_abs());
            a * a
        })
        .sum::<u128>();
    square.saturating_mul(TUNED_MEAN_HALF_ROWS) <= k.saturating_mul(b).saturating_mul(b)
}

/// The certified `l2` bound implied by acceptance, or `None` when acceptance
/// licenses no bound at all.
///
/// Derivation. GHL21 Corollary 3.2 gives `‖Πw‖₂² ≥ 30·‖w‖₂²` except with
/// probability `≲ 2^{−128}` for `Π ← D^{d×256}`; removing rows cannot lower
/// `‖Πw‖₂²`, so the same floor holds for every `rows ≥ 256`. Acceptance is
/// `‖p‖₂² ≤ (rows/2)·B²` by [`verify_l2_shortness`], hence
/// `‖w‖₂² ≤ rows·B²/60`, i.e. `‖w‖₂ ≤ B·√(rows/60)`. At `rows = 256` that is
/// `√(128/30)·B ≈ 2.07·B` — the literature constant, now derived from the same
/// anchor the verifier actually applies rather than asserted next to a
/// different one.
///
/// `None` for `rows < 256`: measured over 32 000 draws, the ratio `‖Πw‖₂²/‖w‖₂²`
/// drops below the corollary's `30` in 38% of `rows = 64` projections and in
/// every `rows = 8` one, so no gap can be quoted there without a new bound.
pub fn certified_l2_bound(rows: usize, claimed_bound: u64) -> Option<u64> {
    if rows < GHL21_MIN_ROWS {
        return None;
    }
    let b = u128::from(claimed_bound.max(1));
    let b_sq = b.checked_mul(b)?;
    // smallest c with 60·c² ≥ rows·B²
    let numer = u128::from(rows as u64).checked_mul(b_sq)?;
    let c = ceil_sqrt_ratio(numer, GHL21_LOWER_TAIL_SQ * TUNED_MEAN_HALF_ROWS)?;
    u64::try_from(c).ok()
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
/// `(k·D/2)·B²` over all `k·D` response coefficients — the GHL21 anchor
/// `√128·β` at `k·D = 256`, i.e. the tuned mean, not twice it.
///
/// The halving is a floor division, which is *exact* here over the integers:
/// `square ≤ (kD·B²)/2` iff `2·square ≤ kD·B²`.
fn norm_budget(rows: usize, claimed_bound: u64) -> u128 {
    let k = (rows * D) as u128;
    let b = u128::from(claimed_bound.max(1));
    k.saturating_mul(b).saturating_mul(b) / TUNED_MEAN_HALF_ROWS
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
    /// GHL21 Corollary 3.2's row count: the fixture must sit in the regime the
    /// certified floor is stated for, not merely in a regime where the gate
    /// happens to run.
    const K: usize = 256;

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
    fn certified_bound_is_the_ghl21_constant_at_its_own_row_count() {
        // The closure is "smallest c with 60 c^2 >= rows B^2"; at rows = 256
        // that is exactly ceil(sqrt(128/30) * B), the literature gap.
        assert_eq!(certified_l2_bound(256, 1000), Some(2066));
        assert_eq!(certified_l2_bound(256, 64), Some(133));
        assert_eq!(certified_l2_bound(256, 1), Some(3));
        // 2065 would be UNSOUND: 60 * 2065^2 < 256 * 1000^2, i.e. the floor
        // does not license a bound that tight. This is the pin that keeps the
        // constant from being "tidied" back into a rounding.
        assert!(60 * 2065u128 * 2065 < 256 * 1000u128 * 1000);
        assert!(60 * 2066u128 * 2066 >= 256 * 1000u128 * 1000);
        // monotone in the claimed bound
        assert!(certified_l2_bound(256, 63).unwrap() <= certified_l2_bound(256, 64).unwrap());
        assert!(certified_l2_bound(256, 64).unwrap() < certified_l2_bound(256, 65).unwrap());
        // more rows loosen the gap exactly as rows/2 grows, and stay licensable
        assert!(certified_l2_bound(512, 1000).unwrap() > certified_l2_bound(256, 1000).unwrap());
        assert!(60 * u128::from(certified_l2_bound(512, 1000).unwrap()).pow(2) >= 512 * 1000 * 1000);
    }

    #[test]
    fn no_gap_is_certified_below_the_stated_row_count() {
        // GHL21 states the floor for R <- D^{d x 256}. Measured (numpy, 32 000
        // draws): the ratio ||Pw||^2/||w||^2 falls below 30 in 38% of k = 64
        // projections and in 100% of k = 8 ones, so quoting sqrt(128/30) there
        // would be a fabricated bound. Refusing is the only sound answer.
        assert_eq!(certified_l2_bound(64, 1000), None);
        assert_eq!(certified_l2_bound(8, 1000), None);
        assert_eq!(certified_l2_bound(GHL21_MIN_ROWS - 1, 1000), None);
        assert!(certified_l2_bound(GHL21_MIN_ROWS, 1000).is_some());
        // the test fixture itself is at the licensed dimension
        assert_eq!(K, GHL21_MIN_ROWS);
    }

    #[test]
    fn the_acceptance_anchor_is_the_tuned_mean_not_twice_it() {
        // Regression pin for the sqrt(2) slip: acceptance must be
        // ||p||^2 <= (k/2) B^2. A response at exactly (k/2) B^2 is admitted, one
        // unit above is not, and the old k B^2 threshold would have admitted
        // both while still quoting sqrt(128/30).
        let proj = JLProjection::from_seed(&[5u8; 32], K, M * D);
        let k = K as u128;
        let b = 64u128;
        let mut p = vec![0i64; K];
        // concentrate (k/2) B^2 into one coordinate as far as i64 allows, spread
        // over eight coordinates so each stays representable
        let per = u64::try_from((k * b * b / 2) / 8).unwrap();
        for slot in p.iter_mut().take(8) {
            *slot = i64::try_from(per.isqrt()).unwrap();
        }
        let square: u128 = p.iter().map(|v| u128::from(v.unsigned_abs()).pow(2)).sum();
        assert!(square <= k * b * b / 2, "fixture must sit at the anchor");
        assert!(verify_l2_shortness(&proj, &p, 64), "at the anchor: accept");
        // one full unit past it: push a single coordinate up
        p[0] += 1;
        let square_past: u128 = p.iter().map(|v| u128::from(v.unsigned_abs()).pow(2)).sum();
        assert!(square_past > k * b * b / 2);
        assert!(
            !verify_l2_shortness(&proj, &p, 64),
            "past the anchor: refuse (the old k B^2 gate accepted this)"
        );
        // and the wrong anchor is exactly 2x looser
        assert!(square_past <= k * b * b, "the retired threshold would have passed");
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
