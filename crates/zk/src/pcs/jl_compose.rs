//! Composed (two-stage) structured Johnson–Lindenstrauss projections.
//!
//! [`crate::shortness::projection`] certifies an `l2` bound with a *flat*
//! random projection: `Π ∈ {0,±1}^{k×n}` with independent entries. That is the
//! cheapest soundness argument, but the projection has the same length as the
//! witness, so verifying `p = Πs` costs the verifier `Θ(n)` — fatal for a
//! polylogarithmic verifier.
//!
//! The structured fix (RoK and Roll, ASIACRYPT 2025) samples a *small*
//! projection and applies it to limbs of the witness in parallel; the cost is
//! that the projection dimension becomes linear in the witness length. The
//! composition studied here (eprint 2026/1196 §3.2, p. 17, lemmas 3.1–3.2) buys
//! the dimension back by stacking two independent stages:
//!
//! ```text
//! J, J′ ∈ {−1,0,1}^{m×mȷ}   drawn with P(±1) = 1/4, P(0) = 1/2 (lemma 2.5, p. 15)
//! Ĵ  := J′(I_ȷ ⊗ J)                    m × mȷ²      (Table 1, p. 11)
//! Π  := (I_r ⊗ J′)(I_{ȷr} ⊗ J)          m·r × m·r²      with r = ȷ²  (§3.2, p. 17)
//! ```
//!
//! Table 1 (p. 11) fixes `m = 256`, and §3.2 (p. 17) writes the projection as
//! `(I_r ⊗ J′)(I_{ȷr} ⊗ J) = Π` applied "to `s`", with `ȷ² = L2/d = r` (§3.1,
//! p. 15). Reading `Π` at its printed shape — `256r × 256r²`, and `Ĵ` at
//! `256 × 256ȷ²` — forces a condition the paper never states: `s ∈ R_q^{L1×r}`
//! flattens to `L1·r` entries and `Π` consumes `256r²`, so
//!
//! ```text
//! L1 · r = 256 · r²   ⟺   L1 = m·ȷ²                    (never written in the paper)
//! ```
//!
//! is exactly what makes "applying `Ĵ` to each `sᵢ`" (§1.3, p. 6: "`Πs` can be
//! seen as applying a smaller projection map `Ĵ` to each `sᵢ`, i.e., the
//! computation `Ĵ[s₁| … |s_r]`"; repeated at §3.2, p. 17) a legal description of
//! `Πs` rather than a different map. That alignment is item 1 below, and it is
//! pinned by `two_stage_map_equals_the_block_map_per_column` together with the
//! refusal for a mismatched `L1`.
//!
//! `Π` consumes the *whole* packed witness matrix `s ∈ R_q^{L1×r}` flattened
//! column-major (so `L1 = m·ȷ² = m·r`) and outputs `p ∈ R_q^{m·r}`. Two facts
//! make it usable, and both are tested here rather than assumed:
//!
//! 1. **Alignment.** `Π·flatten(s) = [Ĵ s₁ | … | Ĵ s_r]`: the two-stage map on
//!    the flattened witness is exactly the small block map applied per column,
//!    which is what gives `p` a tensor structure a verifier can fold. The
//!    identity holds *only* when `L1 = m·ȷ²` — a mismatched `L1` is the natural
//!    way to get a silently wrong `p`, so the tests pin both the identity, the
//!    block-diagonal support that licenses it, and the refusal.
//! 2. **Succinct partial evaluation.** §3.2.2 (p. 19) — "Consider the rows `Ĵ`.
//!    `Ĵ` has the structure that it is a diagonal block matrix with the block
//!    being `J′(Iȷ ⊗ J)` … Since `e` is tensor structured we can split it into
//!    `e′ ⊗ e″`, where `e′` matches the width of `J`. Now, we can compute `Je′`.
//!    Next, we compute `J′((Je′) ⊗ e″)`" — i.e. splitting the column point as
//!    `e = e_out ⊗ e_in` (`e_in` matching `J`'s width),
//!
//!    ```text
//!    Σ_b eq(b, e)·Ĵ[u, b]  =  J′(e_out ⊗ (J·e_in))[u]
//!    ```
//!
//!    so a row of `Ĵ` is evaluated with two small matrix–vector products instead
//!    of one length-`mȷ²` contraction. Two things the paper leaves open, resolved
//!    here by test rather than by taste: the §3.2.2 restatement on p. 20 prints
//!    the same expression as `J′((J′e′) ⊗ e″)` — a **typo**, since the first
//!    factor must be the *other* stage for the types to conform (`J′` is
//!    `m × mȷ`, so `J′e′` is undefined while `Je′` is), and the intro's p. 9
//!    spelling is the identity that holds; and neither passage says which of
//!    `e′, e″` is the fast Kronecker index, which `partial_evaluation` fixes and
//!    `partial_evaluation_matches_the_expansion` pins against a direct
//!    contraction of `Ĵ`.
//!
//! # What the composition costs
//!
//! Lemma 2.5 (§2.6, p. 15) is the modular-JL statement the stages are drawn
//! against: for `x ∈ [−q/2, q/2]^n` with `‖x‖₂ ≤ q/125` and `Π` a `256 × n`
//! matrix of that distribution, `Pr[‖Πx mod q‖₂ ≤ √30·‖x‖₂] ≤ 2^{−128}` and
//! `Pr[‖Πx mod q‖₂ ≥ √337·‖x‖₂] ≤ 2^{−128}`. Lemma 3.1 (p. 17, eq. (12)) lifts it
//! to a *block* projection `Π′ = I_{n/m} ⊗ Π` with error `2^{−128·n/m}`, and
//! Lemma 3.2 (p. 17, eq. (13)) unions the two stages: with
//! `Π̂ = I_{n/m} ⊗ Π`, `Π̂′ = I_{n/m²} ⊗ Π′`,
//!
//! ```text
//! Pr[ ‖Π̂′Π̂w mod q‖₂ / ‖w‖₂  ∈/ [30, 337] ]  ≤  2^{−128·(n/m + n/m²)}
//! ```
//!
//! Each stage therefore multiplies the `l2` norm by a factor in `[√30, √337]`, so
//! the composition lands in `[30, 337]` — the *squared* ratio windows
//! [`SINGLE_STAGE`] and [`TWO_STAGE`]. The verifier gates the revealed image with
//! [`projection_gate_ok`] (Fig. 1, p. 21: `‖pᵢ‖₂ ≤ 337ω`, i.e. `√337·ω` per
//! Theorem 3.3's p. 20 restatement) and the extractor then recovers a witness
//! bounded by [`extractor_slack_sq`] (Theorem 3.3's "norm slack `√(337/30) ≈
//! 3.35`"). All windows compare **squared** norms, so the decisions are exact
//! integer arithmetic with no square root in a soundness path. Note the windows
//! are statements about `m = 256`: at smaller heights the expected inflation
//! `√(m/2)` is outside them, and the tests therefore check the concentration at
//! the paper's `m` and the *structure* at a toy `m`.
//!
//! One more thing the paper leaves open: it never says what `ω` *is*. Fig. 1
//! (p. 21) bounds the projected limbs by `337ω` and separately bounds
//! `(ŵ,ˆt,ẑ)` by `√(b²(nAL₂δd + L₂δd) + (L₂κb′)²L₁d)`, using `κ` and `b′` that are
//! not defined anywhere; §3.2.4 (p. 22) is the case `L₁ ≤ 256`, where a
//! projection smaller than the witness is impossible without switching to a
//! smaller ring degree. Both bounds are assembled by the caller — see
//! `crates/zk/examples/grand_danois.rs`, which instantiates them and records the
//! choices.
//!
//! Layering: `foundation → pcs::projection → pcs::rotation → pcs::jl_compose`.

use crate::pcs::projection::FieldMat;
use crate::pcs::rotation::{evaluation_vector, powers};
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;

/// Domain label for the tuned-ternary derivation.
const JL_DOMAIN: &[u8] = b"lattice-algebra/Z7/structured-jl";

/// Lemma 2.5's entry distribution: `P(+1) = P(−1) = 1/4`, `P(0) = 1/2`.
///
/// [`FieldMat::ternary`] draws the three values with equal probability, which is
/// **not** this distribution: the concentration constants above, and the
/// expected inflation `√(m/2)`, depend on `P(0) = 1/2`. Taking two bits per
/// entry makes the distribution exact rather than approximate.
///
/// # Panics
/// If `rows` or `cols` is zero.
pub fn tuned_ternary<R: Ring>(
    label: &[u8],
    seed: &[u8; 32],
    rows: usize,
    cols: usize,
) -> FieldMat<R> {
    assert!(rows > 0 && cols > 0, "a projection needs entries");
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(JL_DOMAIN);
    xof.absorb(label);
    xof.absorb(seed);
    xof.absorb(&(rows as u64).to_le_bytes());
    xof.absorb(&(cols as u64).to_le_bytes());
    let entries = (0..rows * cols)
        .map(|_| {
            let mut buf = [0u8; 1];
            xof.squeeze(&mut buf);
            match buf[0] & 3 {
                0 | 1 => R::ZERO,
                2 => R::ONE,
                _ => R::ZERO - R::ONE,
            }
        })
        .collect();
    FieldMat::from_entries(rows, cols, entries)
}

/// `A ⊗ B` over the coefficient field, with `B`'s index the fast one:
/// `(A⊗B)[i·B.rows()+k, j·B.cols()+l] = A[i,j]·B[k,l]`.
pub fn kron<R: Ring>(a: &FieldMat<R>, b: &FieldMat<R>) -> FieldMat<R> {
    let mut data = Vec::with_capacity(a.rows() * b.rows() * a.cols() * b.cols());
    for i in 0..a.rows() {
        for k in 0..b.rows() {
            for j in 0..a.cols() {
                for l in 0..b.cols() {
                    data.push(*a.get(i, j).expect("in range") * *b.get(k, l).expect("in range"));
                }
            }
        }
    }
    FieldMat::from_entries(a.rows() * b.rows(), a.cols() * b.cols(), data)
}

/// The `n × n` identity over the coefficient field.
///
/// # Panics
/// If `n` is zero.
pub fn identity_mat<R: Ring>(n: usize) -> FieldMat<R> {
    assert!(n > 0, "the identity needs at least one row");
    let mut data = vec![R::ZERO; n * n];
    for i in 0..n {
        data[i * n + i] = R::ONE;
    }
    FieldMat::from_entries(n, n, data)
}

/// A two-stage structured projection `Π = (I_r ⊗ J′)(I_{ȷr} ⊗ J)`, with
/// `Ĵ = J′(I_ȷ ⊗ J)` its per-column block.
#[derive(Clone, PartialEq, Eq)]
pub struct StructuredProjection<R: Ring> {
    height: usize,
    jots: usize,
    j: FieldMat<R>,
    j_prime: FieldMat<R>,
}

impl<R: Ring> core::fmt::Debug for StructuredProjection<R> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "StructuredProjection(m={}, ȷ={}, Π={}×{})",
            self.height,
            self.jots,
            self.height * self.columns(),
            self.height * self.columns() * self.columns()
        )
    }
}

impl<R: Ring> StructuredProjection<R> {
    /// Draws `J, J′ ← D^{m×mȷ}` (lemma 2.5) from a seed, for a witness packed
    /// into `r = ȷ²` columns. `height` is the paper's `256`; the concentration
    /// window only holds at that size, so a smaller value is a *structural*
    /// choice and not a soundness parameter.
    ///
    /// # Panics
    /// If `height` or `jots` is zero.
    pub fn sample(label: &[u8], seed: &[u8; 32], height: usize, jots: usize) -> Self {
        assert!(height > 0 && jots > 0, "a projection needs a shape");
        Self {
            height,
            jots,
            j: tuned_ternary(&[label, b"/J"].concat(), seed, height, height * jots),
            j_prime: tuned_ternary(&[label, b"/J2"].concat(), seed, height, height * jots),
        }
    }

    /// Rows of each stage (`m`, the paper's `256`).
    pub const fn height(&self) -> usize {
        self.height
    }

    /// The splitting factor `ȷ`, with `r = ȷ²` packed columns.
    pub const fn jots(&self) -> usize {
        self.jots
    }

    /// `r = ȷ²`.
    pub fn columns(&self) -> usize {
        self.jots * self.jots
    }

    /// What one stage consumes: `m·ȷ` coefficients.
    pub fn stage_width(&self) -> usize {
        self.height * self.jots
    }

    /// The column count `L1 = m·ȷ²` a witness must have for this projection to
    /// align with it.
    pub fn aligned_height(&self) -> usize {
        self.height * self.columns()
    }

    /// `J`, the first stage.
    pub fn first_stage(&self) -> &FieldMat<R> {
        &self.j
    }

    /// `J′`, the second stage.
    pub fn second_stage(&self) -> &FieldMat<R> {
        &self.j_prime
    }

    /// `Ĵ = J′(I_ȷ ⊗ J)`: the `m × mȷ²` block applied to one column of `s`.
    pub fn block(&self) -> FieldMat<R> {
        self.j_prime
            .matmul(&kron(&identity_mat(self.jots), &self.j))
            .expect("conforming by construction")
    }

    /// `Π = (I_r ⊗ J′)(I_{ȷr} ⊗ J)`: the full `m·r × m·r²` map on the flattened
    /// witness. Materialising it costs `O(m²r³)`, which is why [`Self::apply_flat`]
    /// applies the stages blockwise instead.
    pub fn composed(&self) -> FieldMat<R> {
        let r = self.columns();
        let stage1 = kron(&identity_mat(self.jots * r), &self.j);
        let stage2 = kron(&identity_mat(r), &self.j_prime);
        stage2.matmul(&stage1).expect("conforming by construction")
    }

    /// `p = [Ĵ s₁ | … | Ĵ s_r]` on a witness matrix given as its `r` columns.
    ///
    /// # Panics
    /// Unless there are `columns()` columns of `aligned_height()` elements.
    pub fn apply_to_columns<const D: usize>(&self, s: &[&[PolyRing<R, D>]]) -> Vec<PolyRing<R, D>> {
        assert_eq!(s.len(), self.columns(), "one column per packed block");
        for c in s {
            assert_eq!(c.len(), self.aligned_height(), "L1 must be m·ȷ²");
        }
        let flat: Vec<PolyRing<R, D>> = s.iter().copied().flatten().cloned().collect();
        self.apply_ring(&flat)
    }

    /// `Π·s` on the column-major flattening of the witness matrix: `m·ȷ²·r` ring
    /// elements in, `m·r` out. The projection's field entries act as **constant
    /// polynomials**, which is what the paper's "implicitly embedded into `R_q`"
    /// sentence means — so each of the `D` coefficient planes is mapped
    /// independently, exactly as [`Self::apply_flat`] does on one plane.
    ///
    /// # Panics
    /// Unless `s.len() == m·ȷ²·r`.
    pub fn apply_ring<const D: usize>(&self, s: &[PolyRing<R, D>]) -> Vec<PolyRing<R, D>> {
        let r = self.columns();
        assert_eq!(
            s.len(),
            self.aligned_height() * r,
            "the projection input must be the whole flattened witness"
        );
        let stage1 = self.project_ring(&self.j, s, self.jots * r);
        self.project_ring(&self.j_prime, &stage1, r)
    }

    /// `(I_blocks ⊗ m)·v` with `m` a coefficient-level matrix and `v` a ring
    /// vector: the scalar entries multiply each ring element.
    ///
    /// # Panics
    /// Unless `v.len() == blocks·m.cols()`.
    fn project_ring<const D: usize>(
        &self,
        m: &FieldMat<R>,
        v: &[PolyRing<R, D>],
        blocks: usize,
    ) -> Vec<PolyRing<R, D>> {
        assert_eq!(
            v.len(),
            blocks * m.cols(),
            "the block count must tile the input"
        );
        let zero = PolyRing::from_coefficients(vec![R::ZERO; D]);
        let mut out = Vec::with_capacity(blocks * m.rows());
        for blk in v.chunks(m.cols()) {
            for row in 0..m.rows() {
                let mut acc = zero.clone();
                for (w, x) in m.row(row).iter().zip(blk) {
                    acc += PolyRing::from_coefficients(vec![*w]) * x.clone();
                }
                out.push(acc);
            }
        }
        out
    }

    /// `Π` on one coefficient plane: `m·ȷ²·r` field elements in, `m·r` out. This
    /// is the map [`Self::apply_ring`] applies to every plane.
    ///
    /// # Panics
    /// Unless `flat.len() == m·ȷ²·r`.
    pub fn apply_flat(&self, flat: &[R]) -> Vec<R> {
        let r = self.columns();
        assert_eq!(
            flat.len(),
            self.aligned_height() * r,
            "the projection input must be the whole flattened plane"
        );
        let stage1 = self
            .j
            .project_blocks(flat, self.jots * r)
            .expect("checked above");
        self.j_prime
            .project_blocks(&stage1, r)
            .expect("stage one is r blocks of m·ȷ")
    }

    /// `Σ_b eq(b, e)·Ĵ[u, b]` for every row `u`, with the column point split
    /// into `e_in` (`log₂(mȷ)` coordinates, matching `J`'s width) and `e_out`
    /// (`log₂ ȷ` coordinates, matching the blocks).
    ///
    /// # Panics
    /// Unless the point widths are `log₂(mȷ)` and `log₂ ȷ`.
    pub fn partial_evaluation(&self, e_in: &[R], e_out: &[R]) -> Vec<R> {
        assert_eq!(
            e_in.len(),
            log2(self.stage_width()),
            "e_in must match J's width"
        );
        assert_eq!(
            e_out.len(),
            log2(self.jots),
            "e_out must match the block count"
        );
        let ev_in = evaluation_vector(e_in);
        let ev_out = evaluation_vector(e_out);
        let je = self.j.apply(&ev_in).expect("square stage");
        let mut folded: Vec<R> = Vec::with_capacity(self.jots * self.height);
        for o in &ev_out {
            for v in &je {
                folded.push(*o * *v);
            }
        }
        self.j_prime.apply(&folded).expect("m·ȷ wide")
    }

    /// [`Self::partial_evaluation`] after the Vandermonde fold of eq. (17): the
    /// coefficient-level row vector a sumcheck verifier contracts against the
    /// witness, `m·d` entries with the `d` coefficients fastest per row.
    ///
    /// # Panics
    /// As [`Self::partial_evaluation`].
    pub fn folded_partial_evaluation<const D: usize>(
        &self,
        alpha: &R,
        e_in: &[R],
        e_out: &[R],
    ) -> Vec<R> {
        let pw = powers(alpha, D);
        self.partial_evaluation(e_in, e_out)
            .iter()
            .flat_map(|s| pw.iter().map(move |q| *s * *q))
            .collect()
    }
}

/// A squared `l2` ratio window `‖Πw‖² / ‖w‖² ∈ [low, high]`, compared as exact
/// integers via `low·‖w‖² ≤ ‖Πw‖² ≤ high·‖w‖²`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SquaredRatioWindow {
    /// Lower bound on the squared ratio.
    pub low: u64,
    /// Upper bound on the squared ratio.
    pub high: u64,
}

impl SquaredRatioWindow {
    /// Whether `projected_sq / witness_sq` lies inside the window.
    pub fn contains(self, projected_sq: u128, witness_sq: u128) -> bool {
        let low = u128::from(self.low);
        let high = u128::from(self.high);
        low * witness_sq <= projected_sq && projected_sq <= high * witness_sq
    }
}

/// Lemma 2.5: one stage keeps the norm ratio in `[√30, √337]`, i.e. the squared
/// ratio in `[30, 337]`.
pub const SINGLE_STAGE: SquaredRatioWindow = SquaredRatioWindow { low: 30, high: 337 };

/// Lemma 3.2: the composition keeps the ratio in `[30, 337]`, i.e. the squared
/// ratio in `[30², 337²]`.
pub const TWO_STAGE: SquaredRatioWindow = SquaredRatioWindow {
    low: 900,
    high: 113_569,
};

/// The composed upper ratio bound.
pub const RATIO_HIGH: u64 = 337;
/// The composed lower ratio bound.
pub const RATIO_LOW: u64 = 30;

/// The verifier's gate on a revealed projection limb: `‖p_i‖₂ ≤ 337·ω`,
/// compared on squared norms so no square root enters the decision.
///
/// `projected_sq` is the exact integer `ℓ2²` of the revealed limb's centered
/// coefficients and `witness_bound_sq` is `ω²`.
pub fn projection_gate_ok(projected_sq: u128, witness_bound_sq: u128) -> bool {
    projected_sq <= u128::from(RATIO_HIGH * RATIO_HIGH) * witness_bound_sq
}

/// The extraction slack of Theorem 3.3: acceptance certifies an extracted
/// witness of squared norm at most `⌈(337/30)·ω²⌉`, i.e. a norm at most
/// `√(337/30)·ω ≈ 3.35·ω`. Exact integer ceiling division on squared norms.
pub fn extractor_slack_sq(witness_bound_sq: u128) -> u128 {
    (u128::from(RATIO_HIGH) * witness_bound_sq).div_ceil(u128::from(RATIO_LOW))
}

/// The smallest integer whose square is at least `n`.
pub fn isqrt_ceil(n: u128) -> u128 {
    if n <= 1 {
        return n;
    }
    let mut lo = 1u128;
    let mut hi = n;
    while lo < hi {
        let mid = lo + (hi - lo) / 2;
        if mid.checked_mul(mid).is_none_or(|sq| sq >= n) {
            hi = mid;
        } else {
            lo = mid + 1;
        }
    }
    lo
}

/// `log₂(n)`.
///
/// # Panics
/// If `n` is not a power of two.
fn log2(n: usize) -> usize {
    assert!(
        n > 0 && n.is_power_of_two(),
        "width {n} is not a power of two"
    );
    n.trailing_zeros() as usize
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use crate::pcs::projection::{dot, to_coeffs};
    use crate::shortness::exact_l2::squared_norm;
    use algebra::ring::zq::Zq;

    type Q5 = Zq<4294967197>;
    const D: usize = 8;

    fn ring_col(salt: u64, len: usize) -> Vec<PolyRing<Q5, D>> {
        (0..len)
            .map(|i| {
                let coeffs = (0..D)
                    .map(|k| {
                        from_centered::<Q5>((salt as i64 * 17 + i as i64 * 5 + k as i64) % 9 - 4)
                    })
                    .collect();
                PolyRing::from_coefficients(coeffs)
            })
            .collect()
    }

    /// The alignment lemma: the two-stage map on the flattened witness matrix is
    /// the block map applied per column. This is what makes `p = Πs` a
    /// tensor-structured object, and it is the identity that breaks if
    /// `L1 ≠ m·ȷ²`.
    #[test]
    fn two_stage_map_equals_the_block_map_per_column() {
        let p = StructuredProjection::<Q5>::sample(b"align", &[1u8; 32], 4, 2);
        assert_eq!((p.columns(), p.aligned_height()), (4, 16));
        let cols = [
            ring_col(1, 16),
            ring_col(2, 16),
            ring_col(3, 16),
            ring_col(4, 16),
        ];
        let refs: Vec<&[PolyRing<Q5, D>]> = cols.iter().map(|c| c.as_slice()).collect();
        let block = p.block();
        let want = cols
            .iter()
            .flat_map(|c| ring_apply(&block, c))
            .collect::<Vec<_>>();
        assert_eq!(p.apply_ring(&cols.concat()), want, "the ring-level route");
        assert_eq!(p.apply_to_columns::<D>(&refs), want, "the per-column route");
        // and the materialised Π agrees, plane by plane
        for k in 0..D {
            let plane: Vec<Q5> = (0..p.aligned_height() * p.columns())
                .map(|e| to_coeffs(&[cols.concat()[e].clone()])[k])
                .collect();
            assert_eq!(
                p.composed().apply(&plane).expect("shaped"),
                p.apply_flat(&plane),
                "plane {k}: Π vs the staged application"
            );
        }
    }

    /// `m·v` with `m` coefficient-level and `v` a ring vector (constant-poly
    /// entries) — the independent reference the two routes are checked against.
    fn ring_apply<R: Ring, const D: usize>(
        m: &FieldMat<R>,
        v: &[PolyRing<R, D>],
    ) -> Vec<PolyRing<R, D>> {
        let zero = PolyRing::from_coefficients(vec![R::ZERO; D]);
        (0..m.rows())
            .map(|i| {
                let mut acc = zero.clone();
                for (w, x) in m.row(i).iter().zip(v) {
                    acc = acc + PolyRing::from_coefficients(vec![*w]) * x.clone();
                }
                acc
            })
            .collect()
    }

    /// A column of the wrong length is refused rather than silently
    /// mis-projected: `L1 = m·ȷ²` is a precondition of the lemma above.
    #[test]
    #[should_panic(expected = "whole flattened witness")]
    fn a_misaligned_ring_witness_is_refused() {
        let p = StructuredProjection::<Q5>::sample(b"align", &[1u8; 32], 4, 2);
        p.apply_ring(&ring_col(7, 63));
    }

    #[test]
    #[should_panic(expected = "whole flattened plane")]
    fn a_misaligned_plane_is_refused() {
        let p = StructuredProjection::<Q5>::sample(b"align", &[1u8; 32], 4, 2);
        p.apply_flat(&[Q5::ONE; 63]);
    }

    #[test]
    #[should_panic(expected = "L1 must be m")]
    fn a_misaligned_column_set_is_refused() {
        let p = StructuredProjection::<Q5>::sample(b"align", &[1u8; 32], 4, 2);
        let c = ring_col(1, 15);
        p.apply_to_columns::<D>(&[c.as_slice(), c.as_slice(), c.as_slice(), c.as_slice()]);
    }

    /// §3.2.2's structural premise — "`Ĵ` has the structure that it is a diagonal
    /// block matrix with the block being `J′(Iȷ ⊗ J)`" (p. 19) — read off the
    /// *materialised* `Π`: its support is `r` independent copies of `Ĵ`, so packed
    /// column `j` of the witness feeds output block `j` and nothing else. The
    /// alignment test above only shows the two maps agree on the particular
    /// `s` sampled; without *this* one, `[Ĵs₁ | … | Ĵs_r]` could still be a
    /// coincidence and the verifier's per-column fold would be unjustified.
    #[test]
    fn the_composed_map_is_block_diagonal_in_jhat() {
        let p = StructuredProjection::<Q5>::sample(b"blockdiag", &[11u8; 32], 4, 2);
        let big = p.composed();
        let block = p.block();
        let (m, r, l1) = (p.height(), p.columns(), p.aligned_height());
        assert_eq!(
            (big.rows(), big.cols()),
            (m * r, l1 * r),
            "Π's printed shape"
        );
        assert_eq!((block.rows(), block.cols()), (m, l1), "Ĵ is m × mȷ²");
        for j in 0..r {
            for t in 0..l1 {
                let mut unit = vec![Q5::ZERO; l1 * r];
                unit[j * l1 + t] = Q5::ONE;
                let got = big.apply(&unit).expect("shaped");
                for (i, v) in got.iter().enumerate() {
                    let (out_block, out_row) = (i / m, i % m);
                    let want = if out_block == j {
                        *block.get(out_row, t).expect("in range")
                    } else {
                        Q5::ZERO
                    };
                    assert_eq!(*v, want, "Π[:, {}·L1+{}] → output {i}", j, t);
                }
            }
        }
    }

    /// §3.2.2: the partial evaluation of `Ĵ` at a tensor point is two small
    /// matrix–vector products. Checked against the definition — a row of `Ĵ`
    /// contracted against the evaluation vector — so a swapped stage order, a
    /// wrong Kronecker orientation or a wrong point split all fail.
    #[test]
    fn partial_evaluation_matches_the_expansion() {
        let p = StructuredProjection::<Q5>::sample(b"pe", &[2u8; 32], 4, 2);
        let block = p.block();
        let e_in: Vec<Q5> = (0..3).map(|i| Q5::from(i as u64 + 2)).collect();
        let e_out: Vec<Q5> = (0..1).map(|i| Q5::from(i as u64 + 5)).collect();
        let ev_in = evaluation_vector(&e_in);
        let ev_out = evaluation_vector(&e_out);
        assert_eq!((ev_in.len(), ev_out.len()), (8, 2));
        let mut flat: Vec<Q5> = Vec::with_capacity(p.aligned_height());
        for o in &ev_out {
            for v in &ev_in {
                flat.push(*o * *v);
            }
        }
        assert_eq!(flat.len(), p.aligned_height());
        let naive = (0..p.height())
            .map(|u| dot(block.row(u), &flat))
            .collect::<Vec<_>>();
        assert_eq!(p.partial_evaluation(&e_in, &e_out), naive);
    }

    /// The fold of the block row: `Ĵ`'s entries are constant polynomials, so
    /// the coefficient-level image is the partial evaluation scaled by the
    /// Vandermonde row — and it must equal folding each `Ĵ` entry with the
    /// general machinery of [`fold_row`] and then contracting against the
    /// evaluation vector.
    #[test]
    fn folded_partial_evaluation_is_the_ring_fold() {
        use crate::pcs::rotation::fold_row;
        let p = StructuredProjection::<Q5>::sample(b"pe", &[2u8; 32], 4, 2);
        let e_in: Vec<Q5> = (0..3).map(|i| Q5::from(i as u64 + 2)).collect();
        let e_out: Vec<Q5> = (0..1).map(|i| Q5::from(i as u64 + 5)).collect();
        let alpha = Q5::from(9u64);
        let got = p.folded_partial_evaluation::<D>(&alpha, &e_in, &e_out);
        assert_eq!(got.len(), p.height() * D);
        let block = p.block();
        let ev_in = evaluation_vector(&e_in);
        let ev_out = evaluation_vector(&e_out);
        for u in 0..p.height() {
            let mut want = vec![Q5::ZERO; D];
            for j in 0..p.jots() {
                for c in 0..p.stage_width() {
                    let entry: PolyRing<Q5, D> =
                        PolyRing::from_coefficients(vec![block.row(u)[j * p.stage_width() + c]]);
                    let w = ev_out[j] * ev_in[c];
                    for (k, v) in fold_row(&alpha, &entry).iter().enumerate() {
                        want[k] += w * *v;
                    }
                }
            }
            assert_eq!(&got[u * D..(u + 1) * D], want.as_slice(), "row {u}");
        }
    }

    /// The lemma 2.5 distribution, exactly: half zeros, a quarter each ±1.
    #[test]
    fn entries_follow_the_tuned_distribution() {
        let j = tuned_ternary::<Q5>(b"J", &[3u8; 32], 256, 512);
        let neg = Q5::ZERO - Q5::ONE;
        let (mut zeros, mut plus, mut minus) = (0u64, 0u64, 0u64);
        for i in 0..j.rows() {
            for v in j.row(i) {
                if *v == Q5::ZERO {
                    zeros += 1;
                } else if *v == Q5::ONE {
                    plus += 1;
                } else if *v == neg {
                    minus += 1;
                } else {
                    panic!("projection entry outside the ternary set")
                }
            }
        }
        let total = (256 * 512) as u64;
        assert!(
            (49..=51).contains(&(zeros * 100 / total)),
            "P(0) ≈ 1/2, got {zeros}/{total}"
        );
        assert!(
            plus.abs_diff(minus) * 100 / total <= 1,
            "P(+1) ≈ P(−1), got +{plus}/−{minus}"
        );
    }

    /// The stages are independent draws and the label binds the stream.
    #[test]
    fn stages_and_labels_are_independent() {
        let a = StructuredProjection::<Q5>::sample(b"x", &[4u8; 32], 8, 2);
        let b = StructuredProjection::<Q5>::sample(b"x", &[4u8; 32], 8, 2);
        let c = StructuredProjection::<Q5>::sample(b"y", &[4u8; 32], 8, 2);
        assert_eq!(a, b, "sampling is deterministic in the seed");
        assert_ne!(a.first_stage(), c.first_stage(), "the label must bind");
        assert_ne!(
            a.first_stage(),
            a.second_stage(),
            "the two stages must be independent draws"
        );
    }

    /// Lemma 3.2 at the paper's size: with `m = 256` the composed squared ratio
    /// lands in `[30², 337²]`, while a *single* stage lands in `[30, 337]` — and
    /// therefore outside the two-stage window. That contrast is what makes this
    /// non-vacuous: an implementation that applies one stage, or scales the
    /// composition wrongly, leaves one of the two windows.
    #[test]
    fn composed_ratio_lands_in_the_lemma_32_window() {
        let p = StructuredProjection::<Q5>::sample(b"ratio", &[5u8; 32], 256, 2);
        let width = p.height() * p.jots() * p.jots() * p.columns();
        let limit = u128::from(Q5::MODULUS) / (125 * 19);
        for t in 0..4u64 {
            let w: Vec<Q5> = (0..width)
                .map(|i| from_centered::<Q5>(((t * 7919 + i as u64 * 31) % 81) as i64 - 40))
                .collect();
            let w_sq = squared_norm(&w).expect("in range");
            assert!(w_sq < limit * limit, "lemma 3.2 needs ‖w‖ ≤ q/(125√337)");
            let one = p
                .first_stage()
                .project_blocks(&w, p.jots() * p.columns())
                .expect("shaped");
            let one_sq = squared_norm(&one).expect("in range");
            let two_sq = squared_norm(&p.apply_flat(&w)).expect("in range");
            assert!(
                SINGLE_STAGE.contains(one_sq, w_sq),
                "stage 1 left [30,337]: {one_sq} vs {w_sq}"
            );
            assert!(
                TWO_STAGE.contains(two_sq, w_sq),
                "composition left [30,337]²: {two_sq} vs {w_sq}"
            );
            assert!(
                !TWO_STAGE.contains(one_sq, w_sq),
                "one stage must not satisfy the two-stage window"
            );
            assert!(
                !SINGLE_STAGE.contains(two_sq, w_sq),
                "two stages must not satisfy the single-stage window"
            );
        }
    }

    /// The gate and the slack it certifies.
    #[test]
    fn gate_accepts_honest_and_rejects_inflated() {
        let p = StructuredProjection::<Q5>::sample(b"gate", &[6u8; 32], 256, 2);
        let width = p.height() * p.jots() * p.jots() * p.columns();
        let w: Vec<Q5> = (0..width)
            .map(|i| from_centered::<Q5>((i as i64 % 7) - 3))
            .collect();
        let w_sq = squared_norm(&w).expect("in range");
        let bound_sq = w_sq + 1;
        let honest = squared_norm(&p.apply_flat(&w)).expect("in range");
        assert!(
            projection_gate_ok(honest, bound_sq),
            "an honest image must pass the 337ω gate"
        );
        assert!(
            !projection_gate_ok(honest * (337 * 337 + 1), bound_sq),
            "an inflated norm must fail the gate"
        );
        let slack_sq = extractor_slack_sq(bound_sq);
        assert!(
            30 * slack_sq >= 337 * bound_sq,
            "the slack must cover 337/30"
        );
        assert!(
            30 * (slack_sq - 1) < 337 * bound_sq,
            "the slack must be the smallest such integer"
        );
        // the paper's constant: ⌈√(337/30)·ω⌉ for ω = 1, 10, 100
        assert_eq!(isqrt_ceil(extractor_slack_sq(1)), 4);
        assert_eq!(isqrt_ceil(extractor_slack_sq(100)), 34);
        assert_eq!(isqrt_ceil(extractor_slack_sq(10_000)), 336);
        for n in [0u128, 1, 2, 3, 15, 16, 17, 999_999] {
            let s = isqrt_ceil(n);
            assert!(s * s >= n, "isqrt_ceil({n}) too small");
            // The `n <= 1` guard has to come *first*: at `n = 0` the root is `0`,
            // so `s - 1` underflows and the multiplication panics in a debug
            // build before a trailing `||` could short-circuit it.
            assert!(n <= 1 || (s - 1) * (s - 1) < n, "not minimal at {n}");
        }
    }

    /// `(I ⊗ J)·v` is `J` applied to each consecutive block — the reason the
    /// stages are cheap to apply.
    #[test]
    fn kron_matches_blockwise_application() {
        let j = tuned_ternary::<Q5>(b"J", &[7u8; 32], 4, 8);
        let v: Vec<Q5> = (0..48).map(|i| Q5::from(i as u64 + 1)).collect();
        let expanded = kron(&identity_mat::<Q5>(6), &j);
        let want = j.project_blocks(&v, 6).expect("shaped");
        assert_eq!(expanded.apply(&v).expect("shaped"), want);
        assert_eq!((expanded.rows(), expanded.cols()), (24, 48));
    }

    /// Applying the projection at the ring level (constant-polynomial entries)
    /// equals applying it coefficient-plane by coefficient-plane.
    #[test]
    fn ring_application_is_plane_wise() {
        let p = StructuredProjection::<Q5>::sample(b"plane", &[8u8; 32], 4, 2);
        let cols = [
            ring_col(1, 16),
            ring_col(2, 16),
            ring_col(3, 16),
            ring_col(4, 16),
        ];
        let refs: Vec<&[PolyRing<Q5, D>]> = cols.iter().map(|c| c.as_slice()).collect();
        let ring_side = to_coeffs(&p.apply_to_columns::<D>(&refs));
        let flat = to_coeffs(&cols.concat());
        let l1 = p.aligned_height();
        for k in 0..D {
            let plane: Vec<Q5> = (0..flat.len() / D).map(|e| flat[e * D + k]).collect();
            assert_eq!(plane.len(), p.columns() * l1);
            let projected = p.apply_flat(&plane);
            for (idx, v) in projected.iter().enumerate() {
                assert_eq!(
                    ring_side[idx * D + k],
                    *v,
                    "coefficient {k} of output {idx}"
                );
            }
        }
    }

    #[test]
    #[should_panic(expected = "not a power of two")]
    fn a_non_power_two_width_is_refused() {
        let p = StructuredProjection::<Q5>::sample(b"bad", &[9u8; 32], 6, 3);
        p.partial_evaluation(&[Q5::ONE; 8], &[Q5::ONE; 3]);
    }
}
