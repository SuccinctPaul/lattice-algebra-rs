//! Jindo — Hwang–Lee–Seo–Song, *Jindo: Practical Lattice-Based Polynomial
//! Commitments for Client-Side Proving*, eprint 2026/044 (rev. 2026-06) — as a
//! scheme assembly, focused on the paper's headline capability: **evaluation
//! hiding with sublinear masking**.
//!
//! This file holds no cryptographic logic. The masking layer — uniform value
//! masks, the augmented weight table, the split check, the Gaussian masking
//! block, Lyubashevsky's `Rej`, the witness-free simulator and the statistical
//! distance measurement — is [`zk::pcs::masking`]; the linear commitments and
//! their Σ opening are [`zk::pcs::mle`]; the shortness gate is
//! [`zk::shortness::exact_l2`]. What lives here is the instance, the message
//! order of Figs. 3 and 5–7, and the equations those figures print.
//!
//! # The base PCS the hiding layer is attached to
//!
//! [`zk::pcs::mle`] — the tall-key mode that verifies **arbitrary**
//! weight-table claims `y = ⟨w, F⟩` (the [`zk::pcs::WeightPcs`] shape, which
//! [`zk::pcs::MleKey`] implements and the assembly calls through). That is
//! exactly the shape Jindo's
//! `ŷ*ᵢ = v̂*₁ᵀF̂*ᵢŵ₀` flattens to, and `mle` is the repo's only mode admitting a
//! non-factored table ([`zk::pcs::batched`] documents why the √N split cannot
//! express it). Two consequences are documented rather than hidden:
//!
//! * `mle`'s Σ key is *transparent* (`MleLevels::preimage_freedom` is `0`
//!   there), so the protocol's accepting **transcript** delivers Hybrid
//!   Argument 0 of Theorem 7 (statistically close to a simulation — measured
//!   below) while the Σ line's `com` opens its own witness. The hiding half of
//!   Theorem 2 lives on the compressed line, whose commitment is Fig. 3's
//!   `tₖ = A f̂*ₖ + [B′ | I_μ] rₖ` (capability:
//!   [`zk::pcs::mle::MaskBlock`], the identity block B.5 (p. 18) hides with);
//!   the measurement section runs the statistical-distance machinery against
//!   *that* commitment. The shape change in the masking layer is
//!   [`masking::GaussianBlock::with_randomness`], which adds the
//!   `µ + ν` randomness rows Theorem 5's `B` counts; those rows are exactly
//!   what [`MleLevels`]' `B` masks.
//! * This reading takes `γ = n1 = 1` and `d = 1`, so `R_{X^γ−b} = Z_p` and
//!   Fig. 2's `Ecd` is the identity — the paper's own §2 presentation. It also
//!   collapses `p = q`, which the encoding exists to avoid: a mask uniform over
//!   `Z_p` is then *not* short in `R_q`, so the shortness gate covers the
//!   sub-polynomial rows only (`NORM` below). With the CELPC encoding
//!   (`b ≪ q`) the same gate covers the mask rows too, at no cost to hiding.
//!
//! # Steps covered
//!
//! Fig. 3 (`Setup`, `Split`, `EcdToMat`, `Com*`, `Open`), Fig. 5 (`ΠSplit`,
//! lines 1–11) and Fig. 6 (`ΠAgg`, lines 1–14, rejection sampling included)
//! run below. **All four of Fig. 7's verifier lines run natively**: the
//! prover sends what its lines 1–4 send — the stack `t̂` and `zᵀ := v̂*₁ᵀ F̂*`
//! (line 1), `f̂* := F̂*c` (line 3), `r := Rc` (line 4) — the verifier forms
//! the residuals the figure forms, `h := A f̂* + B r − B_t Ťc` (line 5, mod
//! `q`) and `s := D t̂ − B_u û` (line 6, mod the *outer* `q_o`), computes the
//! link equations `v̂*₁ᵀf̂* = zᵀc` (line 9) and `zᵀŵ₀ = ŷ*` (line 10), and
//! gates them through [`MleLevels::quad_report`], which returns the whole
//! failing set; every named check is tripped by some tamper below, and the
//! two response gates `L7`/`L8` each fail **alone**. The levels those
//! residuals live on are [`zk::pcs::mle::MleLevels`]' (Fig. 3's `Com*` steps
//! 3–4 with `B_t`, `B_u` from its `Setup`, p. 8) and the thresholds are
//! [`zk::pcs::mle::QuadParams`]' Theorem 3 → 5 → 6 chain (pp. 10–12),
//! computed from these parameters rather than tuned. `mle`'s Σ opening of the
//! aggregate claim still runs too — the base's own claim check, now carried
//! alongside lines 9–10 rather than in place of them.
//!
//! Two readings that the figure alone leaves open, both resolved against the
//! paper's own arithmetic:
//!
//! * Lines 7–8 gate a **sum of `ℓ2` norms**, not of squares. The glyph that
//!   looks like an exponent in the figure is the `ℓ2` subscript, and the
//!   proofs decide it that way: B.6 (p. 18) bounds each part by its `ℓ∞` bound
//!   times a root and *adds the roots* to get Theorem 3's
//!   `B = b√((m₁+1)d) + B_χ√((μ+ν)d) + B_t√(μd)`; B.8 (p. 19) and B.9 (p. 20)
//!   display the same left-hand side. A squared reading would leave those
//!   bounds measuring a different quantity than the gate.
//! * Theorem 5 prints `B = m₀B_C·B + …` with `B` on both sides. Read as a
//!   fixed point that is negative for any `m₀B_C > 1`, so B.8's derivation is
//!   the disambiguator: it is a **one-step relaxation** from the input
//!   relation's bound. The assembly therefore feeds Theorem 3's honest-opening
//!   value in and gets its `B`, `B_o` out.
//!
//! The hiding half that needs `B = [B′ | I_μ]` is now instantiated: the
//! compressed line's commitment *is* Fig. 3 `Com*` step 3's
//! `tₖ = A f̂*ₖ + [B′ | I_μ] rₖ (mod q)` (p. 9) — [`zk::pcs::mle::MaskBlock`]
//! is the pair, [`zk::pcs::mle::MleLevels::inner_apply`] applies it — and the
//! statistical-distance measurement below runs against *that* commitment,
//! fixed message column / fresh `rₖ ← χ^{μ+ν}` exactly as B.5's reduction
//! demands (p. 18). What the measurement can and cannot show is stated where
//! it prints: statistical distance at the bucketing resolution is what is
//! *measured*; the computational indistinguishability Theorem 2 claims is an
//! `MLWE_{q,ν,χ}` assumption, not a histogram. The plain Σ line keeps its own
//! transparent [`MleKey`] — `MleLevels::preimage_freedom` says which key
//! determines its message and which leaves it free.
//!
//! Run with: `cargo run -p lattice-zk --example jindo`

use algebra::crypto::sampling::{sample_rej_bounded, BitStream};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use std::time::Instant;
use zk::foundation::fs::seed_stream;
use zk::foundation::sampling::from_centered;
use zk::pcs::masking::{
    self, aggregate_blocks, aggregate_norm_bound, augmented_weight, linear_combination,
    linear_form, mask_evaluation, masked_claims, power_table, sample_masks, sigma_for,
    GaussianBlock, MaskShape,
};
use zk::pcs::mle::{MleLevels, MleQuadProof, QuadBounds, QuadCheck, QuadClaim, QuadParams, Shape};
use zk::pcs::projection::{from_coeffs, to_coeffs};
use zk::pcs::{
    commit_mle, open_mle_proof, verify_mle_proof, witness_of, MleCommitment, MleError, MleKey,
    MleOpenProof, Z1Coeff,
};
use zk::shortness::exact_l2;

/// The scalar-field reading of §2: `γ = n₁ = 1`, `d = 1`, so a "ring element"
/// is a field element and `Ecd` is the identity.
type E = PolyRing<Z1Coeff, 1>;

/// Batch dimension `m0` — one commitment per sub-polynomial.
const M0: usize = 3;
/// Rows per block `m1`.
const M1: usize = 4;
/// Columns per block `n0`.
const N0: usize = 3;
/// Encoding slots `n1 = γ` (1 = the scalar reading).
const N1: usize = 1;
/// `μ + ν` — the commitment-randomness rows of Fig. 3 `Com*` step 2 (p. 9),
/// `R ←$ χ^{(μ+ν)×n₀}`. `mle`'s tall key over-determines its witness instead
/// of masking with `B·r`, so the plain line has no such rows; the compressed
/// line of [`MleLevels`] does, and Theorem 5's `σ√(2(μ+ν)d)` term is about
/// them.
const RAND_ROWS: usize = 2;
/// `µ` of Fig. 3 `Setup`'s `B = [B′ | I_µ]` (p. 8): the entries one column
/// commitment `tₖ` carries, and the size of the identity block whose `µ` rows
/// of `rₖ` B.5 (p. 18) turns into the MLWE error. The compressed line of
/// [`MleLevels`] is built at these dimensions, and the Thm. 2 measurement
/// below runs against that line's own commitment.
const MASKED_MU: usize = 1;
/// `ν` of the same pair — the secret dimension of `MLWE_{q,ν,χ}`, the
/// hypothesis Theorem 2 (p. 10) names. `µ + ν = RAND_ROWS`: the same rows the
/// bounds count, now masked through `B` instead of through a column block of
/// the tall key.
const MASKED_NU: usize = 1;
const _: () = assert!(MASKED_MU + MASKED_NU == RAND_ROWS, "B masks the rows Thm. 5 counts");
/// `N = m0·m1·n0·n1` committed coefficients.
const N_DEG: usize = M0 * M1 * N0 * N1;
/// Entries of one column of the augmented matrix: `m1` sub-polynomial rows,
/// the `+1` value-mask row of `F̂*`, `μ + ν` randomness rows.
const ROWS: usize = M1 + 1 + RAND_ROWS;
/// Entries committed per block, i.e. the levelled `aug_len`.
const EXT_LEN: usize = ROWS * N0 * N1;
/// `b` of Lemma 7 (p. 8): the bound on every committed coefficient of `f`. The
/// scalar reading has no flattening to bound it (see the header), so this is
/// the instance's own `|f_t| ≤ B_F`.
const B_F: i64 = 2;
/// `B_χ` of Theorem 3 (p. 10): the entrywise bound of `χ`, the distribution the
/// input blocks' randomness rows are drawn from. `sample_rej_bounded(_, 1)` is
/// `{−1, 0, 1}`, so this is `1` and not a guess.
const B_CHI: i64 = 1;
/// `B_C`: the challenge bound, `‖α‖₁ ≤ B_C` (Fig. 6 line 7's `C`).
const B_C: i64 = 2;
/// `B_t`: the inner compression factor of Fig. 3's `Setup` (p. 8), which puts
/// an honest stack entry at `≈ q/(2B_t)` and is the only reason the `B_o` gate
/// of Fig. 7 line 8 can reject anything (`B_t = 1` makes it vacuous — see
/// [`zk::pcs::mle::round_div`]'s doc).
const B_T: u64 = 4096;
/// `B_u`: the outer compression factor, same `Setup` line.
const B_U: u64 = 8;
/// `ln M` of Lemma 2, so `Rej` accepts with probability `(1 − 2⁻¹²⁸)/M`.
const LOG_M: i64 = 1;
/// Buckets used by the hiding measurement.
const BINS: usize = 16;
/// Half-width of the bucketing window: the whole field.
const HALF: i64 = (Z1Coeff::MODULUS / 2) as i64;
/// Openings sampled per polynomial for the hiding measurement.
const TRIALS: usize = 400;

/// Why the assembly refused.
#[derive(Debug)]
enum Error {
    /// A proof component had the wrong shape.
    Malformed(&'static str),
    /// The first named equation that failed.
    Rejected(&'static str),
    /// The base PCS rejected the opening.
    Base(MleError),
    /// The exact-`l2` gate could not decide.
    Norm(exact_l2::ExactL2Error),
    /// The masking layer refused.
    Mask(masking::MaskError),
    /// The prover's rejection loop never terminated.
    Aborted,
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Malformed(what) => write!(f, "malformed proof: {what}"),
            Self::Rejected(name) => write!(f, "rejected by {name}"),
            Self::Base(e) => write!(f, "base PCS: {e:?}"),
            Self::Norm(e) => write!(f, "shortness gate: {e:?}"),
            Self::Mask(e) => write!(f, "masking layer: {e:?}"),
            Self::Aborted => write!(f, "the rejection loop never terminated"),
        }
    }
}

/// The public instance: Fig. 3's `Setup(1^λ, ρ)` plus the claim.
#[derive(Debug, Clone)]
struct Instance {
    shape: MaskShape,
    key: MleKey,
    /// The two compressed levels of Fig. 3's `Com*` (`A ∈ Z_q^{µ×(m₁+1)}`,
    /// `B = [B′ | I_µ]`, `D ∈ Z_{q_o}^{κ×µn₀}`, and the pair `B_t`, `B_u` of
    /// its `Setup`, p. 8) — the line whose commitment Theorem 2 hides.
    levels: MleLevels,
    /// Theorem 3 → 5 → 6 applied to this instance: the parameters the Fig. 7
    /// gates read.
    quad_params: QuadParams,
    /// `(B, B_o)`, computed from `quad_params` — no gate value in this file is
    /// a literal.
    bounds: QuadBounds,
    /// The evaluation point `x`.
    x: Z1Coeff,
    /// `v̂₁` — the shared block weight table (`m1·n0·n1` entries).
    claim_weight: Vec<E>,
    /// `ŵ₀` — the mask row's weight table (`n0·n1` entries).
    mask_weight: Vec<E>,
    /// `v₀ᵢ = x̃^{m1·n·i}` — the batch factors of Fig. 3.
    v0: Vec<E>,
    /// The claimed value `y = f(x)`.
    y: E,
    /// Theorem 5's per-column bound `B` on the aggregate witness.
    b_column: i64,
}

/// A second, independent key seed from the binding master seed. `MleKey` is
/// expanded from its seed alone, so the two levels must not share one.
fn retag(seed: &[u8; 32], tag: u8) -> [u8; 32] {
    let mut out = *seed;
    out[0] = out[0].wrapping_add(tag);
    out[31] = out[31].wrapping_add(tag);
    out
}

/// The transcript of `ΠSplit ∘ ΠAgg ∘ ΠQuad` (Figs. 5–7).
#[derive(Debug, Clone)]
struct Proof {
    /// `com = (û_i)_{i<m0}` — Fig. 3's `Com`.
    coms: Vec<MleCommitment>,
    /// `û_{m0}` — the masking outer commitment (Fig. 6 line 4).
    com_mask: MleCommitment,
    /// Fig. 3 `Com*` step 4's outer commitments `(û_i)_{i<m0}` of the
    /// compressed line: `ûᵢ = ⌊(D t̂ᵢ)/B_u⌉` per block. These are the `ûᵢ` that
    /// open ΠSplit's instance `x = ((ûᵢ), x, y)` (Fig. 5, p. 10).
    coms_out: Vec<Vec<i64>>,
    /// `û_{m0}` on the same level (Fig. 6 lines 2–4).
    com_out_mask: Vec<i64>,
    /// `y_g` (Fig. 5 line 4).
    y_g: E,
    /// `x*` (Fig. 5 line 5).
    xstar: E,
    /// `(ŷ*ᵢ)_{i<m0}` (Fig. 5 line 9).
    y_stars: Vec<E>,
    /// `ŷ*_{m0}` (Fig. 6 line 6).
    y_star_mask: E,
    /// `ααα` (Fig. 6 line 7).
    alphas: Vec<E>,
    /// `û` (Fig. 6 line 8) — sent, and re-derived by the verifier.
    u_hat: MleCommitment,
    /// `ŷ*` (Fig. 6 line 9) — sent, and re-derived.
    y_star: E,
    /// Fig. 7's response: `t̂` and `z` (line 1), `f̂* := F̂*c` (line 3),
    /// `r := Rc` (line 4). This is what lines 7–10 gate.
    quad: MleQuadProof,
    /// The Σ opening of the aggregate claim — this base's own claim check,
    /// now carried *alongside* Fig. 7's native lines 9–10 rather than
    /// standing in for them.
    open: MleOpenProof,
    /// `σ` used for the masking block, the retries the loop needed, and how
    /// many of them Fig. 6 line 14's `Rej` caused.
    sigma: i64,
    attempts: u32,
    rej_rejects: u32,
}

/// The constant ring element carrying `v` (centered representative).
fn el(v: i64) -> E {
    elt(from_centered::<Z1Coeff>(v))
}

/// A scalar as a ring element of the `d = 1` reading.
fn elt(c: Z1Coeff) -> E {
    PolyRing::from_coefficients(vec![c])
}

/// The scalar of a `d = 1` ring element.
fn coef(e: &E) -> Z1Coeff {
    e.coefficients()[0]
}

/// `f` with small coefficients — the committed polynomial (`|f_t| ≤ B_F`).
fn poly(tag: i64) -> Vec<E> {
    (0..N_DEG)
        .map(|t| el(((tag * 7 + t as i64 * 3) % (2 * B_F + 1)) - B_F))
        .collect()
}

fn to_scalars(v: &[E]) -> Vec<Z1Coeff> {
    to_coeffs::<Z1Coeff, 1>(v)
}

fn from_scalars(v: &[Z1Coeff]) -> Vec<E> {
    from_coeffs::<Z1Coeff, 1>(v)
}

/// Fig. 3 `Setup(1^λ, ρ)`: the keys, the shape, the weight tables and the
/// Theorem 5/6 bounds. The claim `y` is filled in per polynomial.
fn setup(seed: &[u8; 32], x: Z1Coeff) -> Instance {
    let shape = MaskShape::new(M0, M1, N0, N1).expect("non-zero shape");
    // The tall key covers the whole augmented matrix — randomness rows
    // included — so the Σ line and the compressed line open the *same* witness
    // rather than two unrelated ones.
    let key = MleKey::setup(seed, EXT_LEN);
    // Fig. 3's Setup on the paper's own shapes: `A ←$ Z_q^{µ×(m₁+1)}`,
    // `B = [B′ | I_µ]`, `D ←$ Z_{q_o}^{κ×µn₀}` — three matrices, three seeds,
    // none of them the tall key's. `counted_rows = m₁` for the `p = q` reason
    // the header and `NORM` give; the bounds and the gates move together.
    let levels = MleLevels::new(
        seed,
        &retag(seed, 0x42),
        &retag(seed, 0x51),
        &Shape {
            mu: MASKED_MU,
            nu: MASKED_NU,
            aug_rows: M1 + 1,
            cols: N0 * N1,
            counted_rows: M1,
            b_t: B_T,
            b_u: B_U,
        },
    );
    let claim_weight = power_table::<Z1Coeff, 1>(&elt(x), shape.block_len());
    let mask_weight = claim_weight[..shape.mask_len()].to_vec();
    // v₀ᵢ = x^{m1·n·i}: every `block_len`-th power of the same table.
    let powers = power_table::<Z1Coeff, 1>(&elt(x), shape.m0 * shape.block_len());
    let v0 = (0..shape.m0)
        .map(|i| powers[i * shape.block_len()].clone())
        .collect();
    let sigma = sigma_of(&shape);
    let b_column = bound_of(&shape, sigma);
    let quad_params = QuadParams {
        m0: shape.m0,
        n0: N0 * N1,
        rand_rows: RAND_ROWS,
        // Theorem 5's `σ√(2(m1+1)d)` counts `F̂*`'s rows; the value-mask row is
        // exempt here for the reason the header and `NORM` give — with `p = q`
        // a uniform mask is not short in `R_q`, and a bound that admits it
        // admits everything. `MleLevels` measures the same rows.
        counted_rows: M1,
        mu: levels.mu(),
        kappa: levels.kappa(),
        d: 1,
        b_entry: B_F as u64,
        b_chi: B_CHI as u64,
        b_c: B_C as u64,
        b_t: B_T,
        b_u: B_U,
        q: Z1Coeff::MODULUS,
        // The second modulus of Fig. 3's `Setup` (p. 8): `D`, `u = D t̂` and the
        // line 6 residual `s` live here, and Theorem 1's second MSIS
        // hypothesis is `MSIS_{q_o,κ,·}` — printed, not tuned away.
        q_o: zk::pcs::mle::Q_O,
        sigma: u128::try_from(sigma).expect("a positive width"),
    };
    let bounds = quad_params
        .gates()
        .expect("the toy bounds fit u128 — a larger instance must shrink B");
    Instance {
        shape,
        key,
        levels,
        quad_params,
        bounds,
        x,
        claim_weight,
        mask_weight,
        v0,
        y: el(0),
        b_column,
    }
}

/// Lemma 2's width `σ = 14·T/ln M` for `T = m0·√n0·B_C·B` (Theorem 5).
fn sigma_of(shape: &MaskShape) -> i64 {
    let t = aggregate_norm_bound(shape.m0, shape.n0, B_C, B_F).expect("toy bound");
    sigma_for(t, LOG_M).expect("toy sigma")
}

/// Theorem 5's per-column bound `B = m0·B_C·B + σ·⌈√(2(m1+1)d)⌉` at `d = 1`.
fn bound_of(shape: &MaskShape, sigma: i64) -> i64 {
    let rows = 2 * (shape.m1 + 1) as i64;
    let mut root = 1i64;
    while root * root < rows {
        root += 1;
    }
    (shape.m0 as i64) * B_C * B_F + sigma * root
}

/// The claim `y = f(x)` of Fig. 3's relation `R_Poly` (power-table reading).
fn claim_of(inst: &Instance, f: &[E]) -> E {
    let powers = power_table::<Z1Coeff, 1>(&elt(inst.x), inst.shape.coeffs());
    linear_form(&powers, f).expect("the polynomial is N long")
}

/// Fig. 3 `Split(f) → (f*₀, …, f*_{m0−1})`: the sub-polynomials and their
/// uniform mask rows, laid out as `EcdToMat`'s augmented blocks `F̂*ᵢ`.
fn split(inst: &Instance, f: &[E], mask_seed: &[u8; 32]) -> (Vec<Vec<E>>, Vec<Vec<E>>) {
    let blocks: Vec<Vec<E>> = (0..inst.shape.m0)
        .map(|i| f[i * inst.shape.block_len()..(i + 1) * inst.shape.block_len()].to_vec())
        .collect();
    let masks = sample_masks::<Z1Coeff, 1>(&inst.shape, mask_seed);
    (blocks, masks)
}

/// Fig. 3 `Com*(pp, f*) → (com*, op*)`: commit to one augmented block. The
/// opening `op* = (F̂*, R, t̂, 1, 1)` is the witness itself in this base, which
/// the tall key recovers exactly.
fn commit_star(inst: &Instance, aug: &[E]) -> MleCommitment {
    commit_mle(&inst.key, &to_scalars(aug)).expect("every block is EXT_LEN long")
}

/// Fig. 3 `Com*` step 2 (p. 9): `R = [r₀ | … | r_{n₀−1}] ←$ χ^{(μ+ν)×n₀}` — the
/// commitment randomness the tall-key line has no room for. The assembly's `χ`
/// is the centered-uniform `{−1, 0, 1}` ball, so Theorem 3's hypothesis
/// "‖r‖₁ ≤ B_χ for every r ←$ χ" (p. 10) holds *by construction* instead of by
/// tail-cutting a Gaussian, and `B_CHI` states the value it holds at.
fn randomness(seed: &[u8; 32], tag: usize) -> Vec<E> {
    let mut salted = *seed;
    salted[31] = salted[31].wrapping_add(u8::try_from(tag).unwrap_or(u8::MAX));
    let mut xof = seed_stream::<Shake256Xof>(b"jindo-chi", &salted);
    let mut stream = BitStream::new(&mut xof);
    (0..RAND_ROWS * N0 * N1)
        .map(|_| el(sample_rej_bounded::<Z1Coeff>(&mut stream, B_CHI as u32)))
        .collect()
}

/// A block as the compressed line commits to it: Fig. 3's `EcdToMat` output
/// `F̂* ∈ R^{(m1+1)×n0}` stacked with the `μ + ν` randomness rows of step 2,
/// row-major with row stride `n0·n1` — the layout `column()` below already
/// assumes, extended downwards.
fn augment(block: &[E], mask: &[E], rand: &[E]) -> Vec<E> {
    let mut out = block.to_vec();
    out.extend_from_slice(mask);
    out.extend_from_slice(rand);
    out
}

/// The weight table `v̂*₁` of Fig. 4 (p. 10) over an extended block: `F̂*`'s rows
/// carry the augmented weights, the randomness rows carry zeros — which is why
/// `ŷ* = ⟨v̂*₁, F̂*⟩(ŵ₀)` is the *same* claim on both levels, and why the
/// randomness rows are invisible to the claim and visible to the gates.
fn weight_ext(w_star: &[E]) -> Vec<E> {
    let mut out = w_star.to_vec();
    out.extend(vec![el(0); RAND_ROWS * N0 * N1]);
    out
}

/// The split `ŷ* = v̂*₁ᵀ F̂* ŵ₀` behind Fig. 7 lines 9–10 (p. 11), read off the
/// same flattened table the Σ line opens: `v1[j] = w*[j·n₀]` (row `j`'s weight
/// at column 0, whose own weight is `x⁰ = 1`) and `w0[k] = w*[k]` (row 0's
/// weights). The assert below is the honesty check — a power table factors as
/// `x^{j·n₀+k} = x^{j·n₀}·x^k` entrywise *because* `d = 1` makes Fig. 4's ring
/// products scalars, and if it ever stopped factoring, line 9 and line 10
/// would be statements about two different claims.
fn quad_weights(w_star: &[E]) -> (Vec<Z1Coeff>, Vec<Z1Coeff>) {
    let ws = to_scalars(w_star);
    let cols = N0 * N1;
    assert_eq!(ws.len(), (M1 + 1 + 0) * cols, "w_star is the m1+1 rows");
    let v1: Vec<Z1Coeff> = (0..M1 + 1).map(|j| ws[j * cols]).collect();
    let w0: Vec<Z1Coeff> = ws[..cols].to_vec();
    for (j, row) in ws.chunks(cols).enumerate() {
        for (k, cell) in row.iter().enumerate() {
            assert_eq!(
                *cell,
                v1[j] * w0[k],
                "row {j} column {k} of the weight table does not factor"
            );
        }
    }
    (v1, w0)
}

/// Fig. 3 `Com*` steps 3–4 for one block: the rounded inner stack `t̂ᵢ` and its
/// outer commitment `ûᵢ`.
fn commit_levels(inst: &Instance, aug: &[E]) -> (Vec<i64>, Vec<i64>) {
    let stack = inst.levels.stack(&to_scalars(aug));
    let outer = inst.levels.outer_commit(&stack);
    (stack, outer)
}

/// The Fiat–Shamir state: every public value is absorbed before the challenge
/// that depends on it, in the order Figs. 5–6 send them.
struct Fs;

impl Fs {
    fn transcript() -> Transcript<Shake256Xof> {
        let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/examples/jindo");
        tr.absorb(b"n", &(N_DEG as u64).to_le_bytes());
        tr.absorb(b"shape", &[M0 as u8, M1 as u8, N0 as u8, N1 as u8]);
        tr
    }

    fn scalars(tr: &mut Transcript<Shake256Xof>, label: &[u8], v: &[Z1Coeff]) {
        for c in v {
            tr.absorb(
                label,
                &(u64::try_from(c.to_u128()).expect("q ≤ 2^64")).to_le_bytes(),
            );
        }
    }

    fn els(tr: &mut Transcript<Shake256Xof>, label: &[u8], v: &[E]) {
        Self::scalars(tr, label, &to_scalars(v));
    }

    fn coms(tr: &mut Transcript<Shake256Xof>, label: &[u8], cs: &[MleCommitment]) {
        for c in cs {
            Self::scalars(tr, label, &c.c);
        }
    }

    /// Absorb an integer vector — the compressed line's `t̂` and `û` — through
    /// the **residue** it carries, not its integer width.
    ///
    /// Fig. 3 (p. 9) makes both of them ring elements (`t̂ ∈ R^{μn₀}`, `û ∈ R^κ`),
    /// so the transcript binds residues; the *integer* magnitude is precisely
    /// what Fig. 7 lines 7–8 measure. Keeping the two separate is what lets a
    /// prover add `q` to a stack entry without steering its own challenge — and
    /// adding `q` is exactly the move line 8 must catch, so a transcript that
    /// re-drew `c` over the width would fold the two gates back into one.
    fn ints(tr: &mut Transcript<Shake256Xof>, label: &[u8], v: &[i64]) {
        Self::scalars(
            tr,
            label,
            &v.iter()
                .map(|&x| from_centered::<Z1Coeff>(x))
                .collect::<Vec<_>>(),
        );
    }

    /// Fig. 7 line 2: `c ← C^{n0}`, Fiat–Shamir over everything the verifier
    /// holds when ΠQuad starts. ΠAgg's footer gives the instance
    /// `x* = (û, x*, ŷ*)` (Fig. 6, p. 11); the `û` absorbed here is the
    /// *outer* aggregate `Σᵢ αᵢûᵢ + û_{m0}` (line 8), because that is the
    /// commitment line 6 gates, and the `ααα` and per-block commitments behind
    /// it are absorbed too. Then ΠQuad's own first message — line 1's pair
    /// `(t̂, z)` — goes in last, in that order, so no prover can pick `c` after
    /// fixing the stack *or the `z` whose two readings lines 9–10 bind*.
    #[allow(clippy::too_many_arguments)]
    fn quad_challenge(
        coms: &[MleCommitment],
        coms_out: &[Vec<i64>],
        com_out_mask: &[i64],
        alphas: &[E],
        u_hat: &MleCommitment,
        y_star: &E,
        u_out: &[i64],
        t_hat: &[i64],
        z: &[Z1Coeff],
    ) -> Vec<E> {
        let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/examples/jindo-quad");
        tr.absorb(b"n", &(N_DEG as u64).to_le_bytes());
        tr.absorb(b"shape", &[M0 as u8, M1 as u8, N0 as u8, N1 as u8]);
        Self::coms(&mut tr, b"com", coms);
        Self::coms(&mut tr, b"uhat", std::slice::from_ref(u_hat));
        Self::els(&mut tr, b"alpha", alphas);
        Self::els(&mut tr, b"ystar", std::slice::from_ref(y_star));
        for c in coms_out {
            Self::ints(&mut tr, b"cout", c);
        }
        Self::ints(&mut tr, b"coutm", com_out_mask);
        Self::ints(&mut tr, b"uout", u_out);
        Self::ints(&mut tr, b"that", t_hat);
        Self::scalars(&mut tr, b"z", z);
        Self::challenges(&mut tr, N0 * N1, b"jindo-c")
    }

    /// `ααα ← C^{m0}` (Fig. 6 line 7), over the scalar reading's challenge set
    /// `{r : ‖r‖₁ ≤ B_C}`.
    fn challenges(tr: &mut Transcript<Shake256Xof>, count: usize, label: &[u8]) -> Vec<E> {
        let seed = tr.challenge_bytes(32);
        let mut xof = seed_stream::<Shake256Xof>(label, &seed);
        let mut stream = BitStream::new(&mut xof);
        (0..count)
            .map(|_| el(sample_rej_bounded::<Z1Coeff>(&mut stream, B_C as u32)))
            .collect()
    }

    /// `x* ← F×` (Fig. 5 line 5).
    fn unit(tr: &mut Transcript<Shake256Xof>) -> E {
        let seed = tr.challenge_bytes(32);
        let mut xof = seed_stream::<Shake256Xof>(b"jindo-xstar", &seed);
        loop {
            let mut buf = [0u8; 8];
            xof.squeeze(&mut buf);
            let cand = Z1Coeff::from(u64::from_le_bytes(buf) % Z1Coeff::MODULUS);
            if cand.inverse().is_some() {
                return elt(cand);
            }
        }
    }
}

/// The prover: Figs. 5, 6 and 7, end to end.
fn prove(inst: &Instance, f: &[E], mask_seed: &[u8; 32]) -> Result<Proof, Error> {
    prove_full(inst, f, mask_seed, false, ZMode::Honest)
}

/// The prover, with Fig. 6 line 14's rejection loop optionally skipped.
///
/// `skip_rejection_loop` models the *cheating* prover that never runs `Rej` and
/// so happily emits an aggregate whose norm violates Theorem 5's bound. That is
/// how the `NORM` gate is exercised from the verifier's side: an honest prover
/// never produces such a transcript, and the gate is the only thing standing
/// between it and an MSIS solution.
fn prove_with(
    inst: &Instance,
    f: &[E],
    mask_seed: &[u8; 32],
    skip_rejection_loop: bool,
) -> Result<Proof, Error> {
    prove_full(inst, f, mask_seed, skip_rejection_loop, ZMode::Honest)
}

/// How Fig. 7's `Quad.P` chooses the first message `z`.
///
/// The honest prover sends `zᵀ := v̂*₁ᵀ F̂*` and answers lines 3–4 under whatever
/// challenge the transcript then gives it. The two cheating modes move `z`
/// *inside the kernel of one of the two functionals lines 9–10 apply to it*,
/// which is the only way either line can fail alone:
///
/// * [`ZMode::Line9`] shifts `z` along a vector orthogonal to `ŵ₀`, so line 10's
///   equation `zᵀŵ₀ = ŷ*` is untouched while line 9's `zᵀc` is not — except for
///   the (vanishing) chance that the challenge the shift buys is orthogonal to
///   the shift too, which the search below rejects by testing both pairings.
/// * [`ZMode::Line10`] shifts `z` along `m·e_k` and *searches* for a transcript
///   whose challenge has `cₖ = 0`. That is not a trick of the fixture: the
///   challenge set is `C = {r : ‖r‖₁ ≤ B_C}` (Fig. 6 line 7, Fig. 7 line 2), and
///   `0 ∈ C`, so a zero coordinate happens with probability `1/|C|` and the
///   prover is entitled to wait for one. On such a transcript `⟨δz, c⟩ = m·cₖ = 0`
///   *exactly*, so line 9 holds while line 10 fails — the prover's `z` opens the
///   committed matrix correctly for the challenge it got and simply mis-states
///   the evaluation, which is precisely the statement line 10 and only line 10
///   excludes (B.9, p. 20: line 9 yields `v̂*₁ᵀf̂*ₖ = cₖzₖ` per column, and it is
///   line 10 that turns `z` into `ŷ*`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ZMode {
    Honest,
    /// `z + m·δ` with `⟨δ, ŵ₀⟩ = 0`: line 10 stays green, line 9 must fire.
    Line9,
    /// `z + m·eₖ` at a transcript whose `cₖ = 0`: line 9 stays green, line 10
    /// must fire.
    Line10,
}

/// `a + m·b` in the scalar field — the shifted `z` a cheating `Quad.P` sends.
fn add_scaled(a: &[Z1Coeff], b: &[Z1Coeff], m: i64) -> Vec<Z1Coeff> {
    let mm = from_centered::<Z1Coeff>(m);
    a.iter().zip(b).map(|(x, y)| *x + mm * *y).collect()
}

/// `Σᵢ aᵢbᵢ` — the functional lines 9 and 10 apply to `z`.
fn pairing(a: &[Z1Coeff], b: &[Z1Coeff]) -> Z1Coeff {
    a.iter()
        .zip(b)
        .fold(Z1Coeff::ZERO, |acc, (x, y)| acc + *x * *y)
}

/// The prover: Figs. 5, 6 and 7, with `Quad.P`'s choice of `z` under `mode`.
fn prove_full(
    inst: &Instance,
    f: &[E],
    mask_seed: &[u8; 32],
    skip_rejection_loop: bool,
    mode: ZMode,
) -> Result<Proof, Error> {
    let shape = &inst.shape;
    // Fig. 3: Split, then Com* on each augmented block. The block carries
    // `μ + ν` randomness rows on top of `F̂*ᵢ`, which is what gives Fig. 7
    // line 4's `r` something to be.
    let (blocks, masks) = split(inst, f, mask_seed);
    let augs: Vec<Vec<E>> = blocks
        .iter()
        .zip(masks.iter())
        .enumerate()
        .map(|(i, (b, g))| augment(b, g, &randomness(mask_seed, 0x10 + i * 7)))
        .collect();
    let coms: Vec<MleCommitment> = augs.iter().map(|a| commit_star(inst, a)).collect();
    // Fig. 3 `Com*` steps 3–4 per block. The stacks are not sent — they are the
    // opening `op* = (F̂*, R, t̂, c, α)` of Fig. 3 — but their outer commitments
    // are, and Fig. 6 line 13 aggregates the stacks themselves.
    let levelled: Vec<(Vec<i64>, Vec<i64>)> = augs.iter().map(|a| commit_levels(inst, a)).collect();
    let stacks: Vec<&[i64]> = levelled.iter().map(|(s, _)| s.as_slice()).collect();
    let outers: Vec<&[i64]> = levelled.iter().map(|(_, o)| o.as_slice()).collect();
    let coms_out: Vec<Vec<i64>> = levelled.iter().map(|(_, o)| o.clone()).collect();

    // Fig. 5 lines 1–2: fᵢ + X*·gᵢ := DcdToPoly(F̂*ᵢ, 1, 1).
    let ys: Vec<E> = blocks
        .iter()
        .map(|b| linear_form(&inst.claim_weight, b).expect("block length"))
        .collect();
    let mus: Vec<E> = masks
        .iter()
        .map(|g| linear_form(&inst.mask_weight, g).expect("mask length"))
        .collect();
    // Fig. 5 line 4: y_g = Σᵢ gᵢ(x)·v₀ᵢ.
    let y_g = mask_evaluation(&inst.v0, &mus).expect("one mask per block");

    let mut tr = Fs::transcript();
    Fs::coms(&mut tr, b"com", &coms);
    Fs::els(&mut tr, b"x", &[elt(inst.x)]);
    Fs::els(&mut tr, b"claim", std::slice::from_ref(&inst.y));
    Fs::els(&mut tr, b"yg", std::slice::from_ref(&y_g));
    // Fig. 5 line 5: x*.
    let xstar = Fs::unit(&mut tr);
    // Fig. 5 lines 6–7: v̂*₁ = (v̂₁, Ecd(x*)), and line 9's ŷ*ᵢ.
    let w_star = augmented_weight(shape, &inst.claim_weight, &inst.mask_weight, &xstar)
        .map_err(Error::Mask)?;
    let y_stars = masked_claims(&ys, &mus, &xstar).expect("one claim per block");
    Fs::els(&mut tr, b"xstar", std::slice::from_ref(&xstar));
    Fs::els(&mut tr, b"ystar", &y_stars);

    // Fig. 6 lines 1–14, retried until the rejection sampling accepts and the
    // aggregate is short enough for Theorem 5's bound — the prover rejection
    // loop every lattice Σ-protocol in this repo uses.
    let sigma = sigma_of(shape);
    let w_ext = weight_ext(&w_star);
    let zero_block = vec![el(0); EXT_LEN];
    let mut attempt = 0u32;
    let mut rej_rejects = 0u32;
    loop {
        attempt += 1;
        if attempt > 500 {
            return Err(Error::Aborted);
        }
        let mut seed = *mask_seed;
        for (i, s) in seed.iter_mut().enumerate().take(4) {
            *s ^= ((attempt as u64) >> (8 * i)) as u8;
        }
        // line 1: [F̂*_{m0}; R_{m0}] ← D_σ^{(m1+µ+ν+1)·n0·d}; line 5: f*_{m0}.
        let block = GaussianBlock::<Z1Coeff, 1>::with_randomness(shape, sigma, RAND_ROWS, &seed)
            .map_err(Error::Mask)?;
        let mut f_mask = block.committed.clone();
        f_mask.extend_from_slice(&block.randomness);
        // lines 2–4: the masking outer commitment, on both levels.
        let com_mask = commit_star(inst, &f_mask);
        let (stack_mask, outer_mask) = commit_levels(inst, &f_mask);
        // line 6: ŷ*_{m0} = v̂*ᵀF̂*_{m0}ŵ₀.
        let y_star_mask = linear_form(&w_ext, &f_mask).expect("augmented length");
        let mut tr2 = tr.clone();
        Fs::coms(&mut tr2, b"cmask", std::slice::from_ref(&com_mask));
        for o in &coms_out {
            Fs::ints(&mut tr2, b"cout", o);
        }
        Fs::ints(&mut tr2, b"coutm", &outer_mask);
        Fs::els(&mut tr2, b"ymask", std::slice::from_ref(&y_star_mask));
        // line 7: ααα.
        let alphas = Fs::challenges(&mut tr2, shape.m0, b"jindo-alpha");
        let alpha_ints: Vec<i64> = alphas.iter().map(|a| coef(a).centered()).collect();
        // line 10: `F̂* = Σᵢ α·F̂* + F̂*_{m0}`. The sum on its own is `Rej`'s
        // second argument, so both are formed.
        let v_part = aggregate_blocks(&alphas, &augs, &zero_block, EXT_LEN).map_err(Error::Mask)?;
        let agg = aggregate_blocks(&alphas, &augs, &f_mask, EXT_LEN).map_err(Error::Mask)?;
        // line 14: Rej(F̂*, ΣαᵢF̂*ᵢ, σ) over the *sub-polynomial* rows. The mask
        // rows are exempt for the same reason the shortness gate exempts them:
        // with `p = q` a uniform mask is not short, so it cannot enter a
        // Gaussian rejection test — but it is also uniform in the simulated
        // world, so it needs no rejection to be simulatable. Under Fig. 2's
        // encoding (`b ≪ q`) the whole augmented matrix goes in, as printed.
        let rows = shape.block_len();
        let coin = masking::rejection_coin(&seed, attempt);
        if !skip_rejection_loop
            && !masking::rejection_accept(
                &coeffs_of(&agg)[..rows],
                &coeffs_of(&v_part)[..rows],
                sigma,
                LOG_M,
                coin,
            )
            .map_err(Error::Mask)?
        {
            rej_rejects += 1;
            continue;
        }
        if !skip_rejection_loop && !columns_short(inst, &agg) {
            continue;
        }
        // lines 8–9: the reduced instance, computed by both sides.
        let u_hat = aggregate_com(&alphas, &coms, &com_mask);
        let y_star = linear_combination(&alphas, &y_stars, &y_star_mask).expect("one α per claim");
        // lines 12–13 on the compressed level: `t̂ = Σᵢ αᵢt̂ᵢ + t̂_{m0}` and
        // `û = Σᵢ αᵢûᵢ + û_{m0}`. Both are integer combinations, because the
        // paper aggregates the *rounded* values.
        let t_hat = MleLevels::integer_combination(&alpha_ints, &stacks, &stack_mask)
            .ok_or(Error::Malformed("the stack aggregate left i128"))?;
        let u_out = MleLevels::integer_combination(&alpha_ints, &outers, &outer_mask)
            .ok_or(Error::Malformed("the outer aggregate left i128"))?;
        // Fig. 7: one Σ opening of the aggregate claim against û.
        let open = open_mle_proof(&inst.key, &to_scalars(&agg), &to_scalars(&w_ext), &seed)
            .map_err(Error::Base)?;
        // …and Fig. 7's own response. Line 1's pair is `(t̂, z)` with
        // `zᵀ := v̂*₁ᵀ F̂*` over the *aggregated* matrix (the prover holds it —
        // this is what `preimage_freedom` leaves the commitment free to be),
        // sent before the challenge of line 2, which is drawn over it.
        let (v1, w0) = quad_weights(&w_star);
        let z_honest = inst
            .levels
            .quad_z(&to_scalars(&agg), &v1)
            .map_err(Error::Base)?;
        // The challenge and the lines 3–4 response are recomputed *for the `z`
        // actually sent*, which is the whole point: `z` is line 1's message, so
        // Fiat–Shamir puts it in `c`'s prefix (B.9's extractor rewinds a prover
        // that has already committed to `z`, p. 20), and a cheating `z` therefore
        // buys a different challenge whose contraction the honest prover answers
        // honestly. Lines 7–8 stay green under it by construction.
        let (z, c) = match mode {
            ZMode::Honest => {
                let c = Fs::quad_challenge(
                    &coms,
                    &coms_out,
                    &outer_mask,
                    &alphas,
                    &u_hat,
                    &y_star,
                    &u_out,
                    &t_hat,
                    &z_honest,
                );
                (z_honest, c)
            }
            ZMode::Line9 => {
                // δ ⊥ ŵ₀: `(ŵ₀₁, −ŵ₀₀, 0)` and `(0, ŵ₀₂, −ŵ₀₁)`, each scaled by a
                // small `m` so the shifted `z` buys a fresh challenge to test.
                let dirs = [
                    {
                        let mut d = vec![Z1Coeff::ZERO; w0.len()];
                        d[0] = w0[1];
                        d[1] = -w0[0];
                        d
                    },
                    {
                        let mut d = vec![Z1Coeff::ZERO; w0.len()];
                        d[1] = w0[2];
                        d[2] = -w0[1];
                        d
                    },
                ];
                let mut found = None;
                for d in dirs.iter() {
                    for m in 1i64..=6 {
                        let z = add_scaled(&z_honest, d, m);
                        let c = Fs::quad_challenge(
                            &coms,
                            &coms_out,
                            &outer_mask,
                            &alphas,
                            &u_hat,
                            &y_star,
                            &u_out,
                            &t_hat,
                            &z,
                        );
                        let cs = to_scalars(&c);
                        // ⟨δ,ŵ₀⟩ = 0 keeps line 10 green for every m; the shift
                        // must still move line 9, i.e. ⟨mδ,c⟩ ≠ 0.
                        if pairing(d, &w0) == Z1Coeff::ZERO && pairing(&cs, d) != Z1Coeff::ZERO {
                            found = Some((z, c));
                            break;
                        }
                    }
                    if found.is_some() {
                        break;
                    }
                }
                found.ok_or(Error::Malformed(
                    "no ŵ₀-orthogonal z shift moved the challenge pairing",
                ))?
            }
            ZMode::Line10 => {
                // δ = m·eₖ: line 9 stays green exactly when the challenge this
                // `z` buys has `cₖ = 0`, which `C = {‖r‖₁ ≤ B_C}` permits.
                let mut found = None;
                for k in 0..w0.len() {
                    for m in 1i64..=8 {
                        let d = {
                            let mut d = vec![Z1Coeff::ZERO; w0.len()];
                            d[k] = from_centered::<Z1Coeff>(m);
                            d
                        };
                        let z = add_scaled(&z_honest, &d, 1);
                        let c = Fs::quad_challenge(
                            &coms,
                            &coms_out,
                            &outer_mask,
                            &alphas,
                            &u_hat,
                            &y_star,
                            &u_out,
                            &t_hat,
                            &z,
                        );
                        let cs = to_scalars(&c);
                        if cs[k] == Z1Coeff::ZERO && pairing(&d, &w0) != Z1Coeff::ZERO {
                            found = Some((z, c));
                            break;
                        }
                    }
                    if found.is_some() {
                        break;
                    }
                }
                found.ok_or(Error::Malformed(
                    "no transcript in this search had a zero challenge coordinate",
                ))?
            }
        };
        let (f_star, r) = inst
            .levels
            .quad_contract(&to_scalars(&agg), &to_scalars(&c))
            .map_err(Error::Base)?;
        return Ok(Proof {
            coms,
            com_mask,
            coms_out,
            com_out_mask: outer_mask,
            y_g,
            xstar,
            y_stars,
            y_star_mask,
            alphas,
            u_hat,
            y_star,
            quad: MleQuadProof { t_hat, z, f_star, r },
            open,
            sigma,
            attempts: attempt,
            rej_rejects,
        });
    }
}

/// The centered integer coefficients of a ring-element vector — the `z`/`v`
/// arguments Fig. 1's `Rej` works over.
fn coeffs_of(v: &[E]) -> Vec<i64> {
    v.iter().map(|e| coef(e).centered()).collect()
}

/// Fig. 6 line 8: `û = Σᵢ αᵢ·ûᵢ + û_{m0}`.
fn aggregate_com(alphas: &[E], coms: &[MleCommitment], mask: &MleCommitment) -> MleCommitment {
    let mut out = mask.c.clone();
    for (a, c) in alphas.iter().zip(coms.iter()) {
        let a = coef(a);
        for (acc, x) in out.iter_mut().zip(c.c.iter()) {
            *acc += a * *x;
        }
    }
    MleCommitment { c: out }
}

/// Entry `(j, k)` of one augmented block: the flat index of Fig. 3's
/// `EcdToMat` layout is `n0·n1·j + n1·k + ℓ`, and the `m1` sub-polynomial rows
/// come before the mask row, so the gate reads rows `0..m1` only.
fn column(aug: &[E], k: usize, row: usize) -> Z1Coeff {
    coef(&aug[N0 * N1 * row + k])
}

/// Whether every column of the aggregate's sub-polynomial rows is within
/// Theorem 5's bound `B`.
fn columns_short(inst: &Instance, agg: &[E]) -> bool {
    let max = u128::from(inst.b_column as u64) * u128::from(inst.b_column as u64);
    (0..N0 * N1).all(|k| {
        let col: Vec<Z1Coeff> = (0..M1).map(|j| column(agg, k, j)).collect();
        exact_l2::squared_norm(&col)
            .and_then(|sq| exact_l2::exact_l2_gate(&col, sq, max).map(|_| ()))
            .is_ok()
    })
}

/// The named equations of Figs. 5–7 and the binding gate. ASCII on purpose:
/// combining diacritics render as dropped characters in a plain terminal, and
/// these strings are the tamper attribution a reader has to be able to read.
const UNIT: &str = "Fig.5 L5   x* in F* (invertible masking challenge)";
const L11: &str = "Fig.5 L11  y + x* yg == sum_i <Dcd(y*_i), w1> v0_i";
const AGGC: &str = "Fig.6 L8   u_hat == sum_i alpha_i u_i + u_mask";
const AGGY: &str = "Fig.6 L9   y* == sum_i alpha_i y*_i + y*_mask";
/// `pcs::mle`'s own Σ opening of the aggregate claim. It is **not** one of
/// Fig. 7's lines: ΠQuad's claim checks are the figure's own lines 9–10, which
/// this assembly now runs natively (`L9`, `L10`). What this check adds is the
/// base's — the link equation against `û` and the weighted-claim equation, i.e.
/// `Open*`'s first two conditions of Fig. 3 (p. 9) on the aggregate — and it is
/// why the aggregate witness is recoverable at all (`NORM` reads it back).
const OPEN: &str = "Base Σ   A z == d + X u_hat  and  <w*, z> == t + X y*  (pcs::mle's own opening; Fig.7's claim checks are L9/L10)";
const NORM: &str = "Thm.5 aggregate  every recovered u-hat column of the sub-polynomial rows has l2 <= B (the aggregate witness; the *response* gates are Fig.7 L7/L8 below)";
/// The four Fig. 7 verifier lines, named by `src` itself so the attribution
/// in a tamper's failing set cannot drift from the check that produced it.
const L7: &str = QuadCheck::InnerNorm.name();
const L8: &str = QuadCheck::OuterNorm.name();
const L9: &str = QuadCheck::Linearity.name();
const L10: &str = QuadCheck::Evaluation.name();

/// The compressed line's public state, re-derived from the transcript exactly
/// as the verifier of Fig. 7 does it: Fig. 6 line 8's outer aggregate
/// `û = Σᵢ αᵢûᵢ + û_{m0}`, line 2's challenge `c` — drawn over line 1's pair
/// `(t̂, z)`, so a re-chosen `z` re-draws `c` and the response stops opening —
/// and the instance `(v̂*₁, ŵ₀)` lines 9–10 read. Returned as one bundle
/// because `failing` and the reported slack in `main` must see the *same*
/// numbers.
fn quad_view(
    inst: &Instance,
    pr: &Proof,
    y_star: &E,
) -> Result<(Vec<E>, Vec<i64>, Vec<Z1Coeff>, Vec<Z1Coeff>), Error> {
    let shape = &inst.shape;
    let alpha_ints: Vec<i64> = pr.alphas.iter().map(|a| coef(a).centered()).collect();
    let refs: Vec<&[i64]> = pr.coms_out.iter().map(Vec::as_slice).collect();
    let u_out = MleLevels::integer_combination(&alpha_ints, &refs, &pr.com_out_mask)
        .ok_or(Error::Malformed("the outer aggregate left i128"))?;
    let w_star =
        augmented_weight(shape, &inst.claim_weight, &inst.mask_weight, &pr.xstar)
            .map_err(Error::Mask)?;
    let (v1, w0) = quad_weights(&w_star);
    let c = Fs::quad_challenge(
        &pr.coms,
        &pr.coms_out,
        &pr.com_out_mask,
        &pr.alphas,
        &pr.u_hat,
        y_star,
        &u_out,
        &pr.quad.t_hat,
        &pr.quad.z,
    );
    // A response of the wrong shape is refused here — `QuadClaim::validate` is
    // the same check `quad_report` runs, and the named checks below may only
    // be produced by a well-formed message.
    inst.levels
        .quad_measure(
            &QuadClaim {
                outer: &u_out,
                v1: &v1,
                w0: &w0,
                y_star: coef(y_star),
            },
            &to_scalars(&c),
            &pr.quad,
        )
        .map_err(Error::Base)?;
    Ok((c, u_out, v1, w0))
}

/// Every equation the transcript trips — never short-circuiting, so a tamper's
/// full failing set is visible.
fn failing(inst: &Instance, pr: &Proof) -> Result<Vec<&'static str>, Error> {
    let shape = &inst.shape;
    let levels = &inst.levels;
    let shapes_ok = pr.coms.len() == shape.m0
        && pr.y_stars.len() == shape.m0
        && pr.alphas.len() == shape.m0
        && pr.com_mask.c.len() == 2 * EXT_LEN
        && pr.u_hat.c.len() == 2 * EXT_LEN
        && pr.open.z.len() == EXT_LEN
        && pr.open.d.len() == 2 * EXT_LEN
        && pr.coms_out.len() == shape.m0
        && pr.coms_out.iter().all(|o| o.len() == levels.kappa())
        && pr.com_out_mask.len() == levels.kappa()
        && pr.quad.t_hat.len() == levels.stack_len()
        && pr.quad.z.len() == levels.cols()
        && pr.quad.f_star.len() == levels.aug_rows()
        && pr.quad.r.len() == levels.rand_rows();
    if !shapes_ok {
        return Err(Error::Malformed("a proof component has the wrong shape"));
    }
    if pr.sigma <= 0 || pr.sigma > masking::MAX_SIGMA {
        return Err(Error::Malformed(
            "the masking width is outside the samplable range",
        ));
    }
    let w_star = augmented_weight(shape, &inst.claim_weight, &inst.mask_weight, &pr.xstar)
        .map_err(Error::Mask)?;
    let mut bad: Vec<&'static str> = Vec::new();
    let mut check = |holds: bool, name: &'static str| {
        if !holds {
            bad.push(name);
        }
    };

    // Fig. 5 line 5: a non-invertible x* would let the mask be folded away.
    check(coef(&pr.xstar).inverse().is_some(), UNIT);

    // Fig. 5 line 11.
    let (lhs, rhs) = masking::split_check(&inst.y, &pr.y_g, &pr.xstar, &pr.y_stars, &inst.v0)
        .map_err(Error::Mask)?;
    check(lhs == rhs, L11);

    // Fig. 6 line 8: the aggregate commitment the opening must be against.
    check(
        aggregate_com(&pr.alphas, &pr.coms, &pr.com_mask) == pr.u_hat,
        AGGC,
    );

    // Fig. 6 line 9.
    let y_star = linear_combination(&pr.alphas, &pr.y_stars, &pr.y_star_mask)
        .expect("the shape check above sized these");
    check(y_star == pr.y_star, AGGY);

    // Fig. 7: the Σ opening of the aggregate claim, against û.
    check(
        verify_mle_proof(
            &inst.key,
            &pr.u_hat,
            &to_scalars(&weight_ext(&w_star)),
            coef(&y_star),
            &pr.open,
        )
        .is_ok(),
        OPEN,
    );

    // Fig. 7 lines 7–10: the two response gates and the two link checks, on
    // the message the prover sent under the challenge the transcript gives it.
    let (c, u_out, v1, w0) = quad_view(inst, pr, &y_star)?;
    let report = inst
        .levels
        .quad_report(
            &QuadClaim {
                outer: &u_out,
                v1: &v1,
                w0: &w0,
                y_star: coef(&y_star),
            },
            &to_scalars(&c),
            &pr.quad,
            &inst.bounds,
        )
        .map_err(Error::Base)?;
    for which in report {
        check(false, which.name());
    }

    // Binding: the witness the aggregate commitment pins down must be short.
    // The mask rows are exempt here — see the header on `p = q`.
    let recovered =
        from_scalars(&witness_of(&inst.key, &pr.u_hat).ok_or(Error::Base(MleError::Inconsistent))?);
    let max = u128::from(inst.b_column as u64) * u128::from(inst.b_column as u64);
    let mut norm_ok = true;
    for k in 0..N0 * N1 {
        let col: Vec<Z1Coeff> = (0..M1).map(|j| column(&recovered, k, j)).collect();
        let sq = exact_l2::squared_norm(&col).map_err(Error::Norm)?;
        if exact_l2::exact_l2_gate(&col, sq, max).is_err() {
            norm_ok = false;
        }
    }
    check(norm_ok, NORM);
    Ok(bad)
}

/// The verifier: accept only when every equation and gate holds.
fn verify(inst: &Instance, pr: &Proof) -> Result<(), Error> {
    match failing(inst, pr)? {
        empty if empty.is_empty() => Ok(()),
        bad => Err(Error::Rejected(bad[0])),
    }
}

thread_local! {
    /// Every check name some tamper has actually failed, collected by
    /// [`expect_reject`] and audited at the end of `main`.
    static TRIPPED: std::cell::RefCell<std::collections::BTreeSet<String>> =
        const { std::cell::RefCell::new(std::collections::BTreeSet::new()) };
}

/// Assert a tamper is rejected, that its failing set is exactly `expected`, and
/// print it. A bare `is_err()` would hide which equation is load-bearing, so
/// the whole set is compared.
fn expect_reject(label: &str, inst: &Instance, pr: &Proof, expected: &[&'static str]) {
    let bad = failing(inst, pr).unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(!bad.is_empty(), "{label}: the tamper was accepted");
    let mut got = bad.clone();
    got.sort_unstable();
    got.dedup();
    // Record what actually failed, so the module doc's claim that every named
    // check is tripped by some tamper is executed by `main`'s closing assertion
    // rather than asserted in prose. A name no tamper can trip is dead code, and
    // that is the failure mode this repo keeps finding in itself.
    TRIPPED.with(|t| {
        t.borrow_mut()
            .extend(got.iter().map(|name| (*name).to_string()));
    });
    let mut want = expected.to_vec();
    want.sort_unstable();
    want.dedup();
    assert_eq!(got, want, "{label}: failing set");
    match verify(inst, pr) {
        Err(Error::Rejected(name)) => assert_eq!(name, bad[0], "{label}: attribution"),
        other => panic!("{label}: expected a rejection, got {other:?}"),
    }
    println!("  {label}: rejected by {}", got.join(" | "));
}

/// The hiding measurement of Definition 10: `TRIALS` openings of `f` at one
/// point, returning the three quantities the statement is about — the value the
/// verifier actually sees (`ŷ*₀`), the value the mask hides (the bare per-block
/// claim `ŷ₀`, which a mask-free opening would have sent), and `S1`'s
/// witness-free `ŷ*₀`.
fn margins(inst: &Instance, f: &[E]) -> Margins {
    let mut seen = Vec::with_capacity(TRIALS);
    let mut sim = Vec::with_capacity(TRIALS);
    let mut raw = Vec::with_capacity(TRIALS);
    let mut proofs = 0usize;
    let mut rej_rejects = 0u32;
    let mut attempts = 0u32;
    let mut seed = [0u8; 32];
    for i in 0..TRIALS {
        seed[0] = i as u8;
        seed[1] = (i >> 8) as u8;
        let pr = prove(inst, f, &seed).expect("the honest prover terminates");
        proofs += 1;
        rej_rejects += pr.rej_rejects;
        attempts += pr.attempts;
        seen.push(coef(&pr.y_stars[0]));
        // What the mask hides: the bare per-block claim ŷ₀.
        let (blocks, _) = split(inst, f, &seed);
        raw.push(coef(
            &linear_form(&inst.claim_weight, &blocks[0]).expect("block length"),
        ));
        let inv = coef(&pr.xstar).inverse().expect("the transcript verified");
        let unit = masking::UnitChallenge::<Z1Coeff, 1>::new(pr.xstar.clone(), elt(inv))
            .expect("a field unit");
        let t = masking::simulate_split(&inst.y, &inst.v0, &unit, &seed).expect("simulate");
        sim.push(coef(&t.masked_claims[0]));
    }
    Margins {
        seen,
        raw,
        sim,
        proofs,
        rej_rejects,
        attempts,
    }
}

/// One polynomial's worth of openings, plus the rejection loop's accounting.
struct Margins {
    /// The masked claims `ŷ*₀` the verifier sees.
    seen: Vec<Z1Coeff>,
    /// The bare per-block claims `ŷ₀` the mask hides.
    raw: Vec<Z1Coeff>,
    /// `S1`'s witness-free `ŷ*₀`.
    sim: Vec<Z1Coeff>,
    /// Transcripts produced, and how many `ΠAgg` attempts and `Rej` rejections
    /// they cost — the empirical side of Lemma 2's `(1 − 2⁻¹²⁸)/M`.
    proofs: usize,
    rej_rejects: u32,
    attempts: u32,
}

/// How many distinct values a view takes across its trials: the sharpest form
/// of the hiding statement, with no sampling noise in it at all.
fn distinct(v: &[Z1Coeff]) -> usize {
    let mut sorted = v.to_vec();
    sorted.sort_unstable();
    sorted.dedup();
    sorted.len()
}

/// `count` uniform field elements — B.5's right-hand side ("a uniformly random
/// element of R_q^µ", p. 18), which the masked commitment is compared against
/// next to the two-message comparison.
fn uniform_coeffs(count: usize, seed: &[u8; 32]) -> Vec<Z1Coeff> {
    let mut xof = seed_stream::<Shake256Xof>(b"jindo-uniform", seed);
    (0..count)
        .map(|_| {
            let mut buf = [0u8; 8];
            xof.squeeze(&mut buf);
            Z1Coeff::from(u64::from_le_bytes(buf) % Z1Coeff::MODULUS)
        })
        .collect()
}

/// One experiment's pool of commitment entries: every column of every block
/// of one polynomial, committed once per trial.
struct Thm2View {
    /// `tₖ = A f̂*ₖ + [B′ | I_µ] rₖ` — the commitment Theorem 2 makes hiding.
    masked: Vec<Z1Coeff>,
    /// The same fresh-`r` commitment of the zero matrix — what a simulator
    /// with no witness would hand out.
    zero: Vec<Z1Coeff>,
    /// `tₖ = A f̂*ₖ + B′ r′ₖ` — the identity block cut out: *this assembly's*
    /// previous shape ("a column block of the same tall key rather than an
    /// MLWE sample", the header line this view replaces), as a control.
    no_identity: Vec<Z1Coeff>,
    /// `tₖ = A f̂*ₖ` — no randomness at all: what a mask-free commitment of
    /// the same message is, and the control the bucket-level distance of the
    /// masked view is only meaningful against.
    unmasked: Vec<Z1Coeff>,
    /// Uniform field elements of the same count.
    uniform: Vec<Z1Coeff>,
}

/// Theorem 2's hiding, measured the way B.5 reduces it (p. 18): fix one
/// message column and vary only `rₖ ← χ^{µ+ν}`. The message is held fixed
/// across trials on purpose — with a fresh uniform value mask per trial the
/// `p = q` reading would mask the commitment through the *message* and the
/// control would be indistinguishable too, measuring the encoding rather than
/// the block (see the header's `NORM` note). `χ` is the instance's own masking
/// width — the discrete Gaussian `D_σ` the masking layer samples at — and the
/// commitment is the one the protocol itself makes:
/// [`MleLevels::inner_apply`], i.e. Fig. 3 `Com*` step 3's
/// `tₖ = A f̂*ₖ + [B′ | I_µ] rₖ (mod q)` at this instance's `µ, ν`.
fn thm2_view(inst: &Instance, f: &[E], mask_seed: &[u8; 32]) -> Thm2View {
    let sigma = sigma_of(&inst.shape);
    let (blocks, masks) = split(inst, f, mask_seed);
    let width = MASKED_MU + MASKED_NU;
    let cols = N0 * N1;
    let mut masked = Vec::with_capacity(TRIALS * blocks.len() * cols * MASKED_MU);
    let mut zero = Vec::with_capacity(masked.capacity());
    let mut no_identity = Vec::with_capacity(masked.capacity());
    let mut unmasked = Vec::with_capacity(masked.capacity());
    let empty_msg = vec![Z1Coeff::ZERO; M1 + 1];
    for i in 0..TRIALS {
        let mut seed = *mask_seed;
        seed[0] ^= i as u8;
        seed[1] ^= (i >> 8) as u8;
        for (b, (block, mask)) in blocks.iter().zip(masks.iter()).enumerate() {
            let r_ints =
                masking::gaussian_coeffs(width * cols, sigma, &retag(&seed, 0x30 + b as u8))
                    .expect("the instance's own σ is samplable");
            // The commit-zero view draws its OWN `r` — a simulator shares no
            // randomness with the real commitment it is being compared to.
            let z_ints =
                masking::gaussian_coeffs(width * cols, sigma, &retag(&seed, 0x50 + b as u8))
                    .expect("the instance's own σ is samplable");
            for k in 0..cols {
                let mut msg: Vec<Z1Coeff> = (0..M1).map(|j| coef(&block[j * cols + k])).collect();
                msg.push(coef(&mask[k]));
                let r: Vec<Z1Coeff> = r_ints[k * width..(k + 1) * width]
                    .iter()
                    .map(|&v| from_centered::<Z1Coeff>(v))
                    .collect();
                let r_zero: Vec<Z1Coeff> = z_ints[k * width..(k + 1) * width]
                    .iter()
                    .map(|&v| from_centered::<Z1Coeff>(v))
                    .collect();
                // B without its identity block: subtract the identity part
                // back out of the same commitment (`I_µ rₖ` passes through).
                let mut cut = inst.levels.inner_apply(&msg, &r);
                for (t, e) in cut.iter_mut().zip(&r[MASKED_NU..]) {
                    *t -= *e;
                }
                masked.extend(inst.levels.inner_apply(&msg, &r));
                zero.extend(inst.levels.inner_apply(&empty_msg, &r_zero));
                no_identity.extend(cut);
                unmasked.extend(inst.levels.inner_apply(&msg, &vec![Z1Coeff::ZERO; width]));
            }
        }
    }
    let uniform = uniform_coeffs(masked.len(), &retag(mask_seed, 0x77));
    Thm2View {
        masked,
        zero,
        no_identity,
        unmasked,
        uniform,
    }
}

/// The resolution the *unmasked* comparison needs: a point mass is only visible
/// as one if the buckets are finer than the gap between the two claims.
const RAW_BINS: usize = 512;

fn main() {
    let t0 = Instant::now();
    let x = Z1Coeff::from(31u64);
    let mut inst = setup(&[0x4au8; 32], x);
    let f = poly(1);
    inst.y = claim_of(&inst, &f);
    let shape = inst.shape;

    println!(
        "Jindo 2026/044 — base PCS: zk::pcs::mle (tall-key weight-table claims); N = {N_DEG} coefficients, split ({},{},{},{})",
        shape.m0, shape.m1, shape.n0, shape.n1
    );
    println!(
        "  masking budget: {} value masks (= N/m1), masking block {} (= N/m0 + N/(m0·m1)), sublinear = {}",
        shape.value_masks(),
        shape.masking_block_len(),
        shape.is_sublinear()
    );

    // Completeness: the honest masked transcript verifies.
    let proof = prove(&inst, &f, &[7u8; 32]).expect("honest proof");
    verify(&inst, &proof).expect("honest proof rejected");
    let sigma = sigma_of(&shape);
    let t = aggregate_norm_bound(shape.m0, shape.n0, B_C, B_F).expect("toy bound");
    println!(
        "  honest proof verifies: σ = {sigma} = 14·T/ln M with T = {t}, B = {}, {} ΠAgg attempt(s)",
        inst.b_column, proof.attempts
    );
    // Fig. 7's four verifier lines, with the thresholds the instance's
    // parameters imply (Theorem 3 → 5 → 6) and the quantities the verifier
    // actually measured. `inner_sum_full` is the same line-7 sum with the
    // exempt mask row included — the number that says what the exemption was
    // worth — and the `q_o` line is Theorem 1's *second* MSIS hypothesis, the
    // one the compressed outer level earns its name from.
    let y_star = linear_combination(&proof.alphas, &proof.y_stars, &proof.y_star_mask)
        .expect("one α per claim");
    let (qc, u_out, v1, w0) = quad_view(&inst, &proof, &y_star)
        .expect("the honest response is well-formed");
    let qs = inst
        .levels
        .quad_measure(
            &QuadClaim {
                outer: &u_out,
                v1: &v1,
                w0: &w0,
                y_star: coef(&y_star),
            },
            &to_scalars(&qc),
            &proof.quad,
        )
        .expect("measure");
    println!(
        "  Fig.7 gates: L7 |f*|+|r|+|h| = {} <= B = {} (mask row exempt; incl. it: {}) | L8 |s|+|t_hat| = {} <= B_o = {} | L9 v1.f* == z.c: {} | L10 z.w0 == y*: {}",
        qs.inner_sum,
        inst.bounds.b,
        qs.inner_sum_full,
        qs.outer_sum,
        inst.bounds.b_o,
        qs.linearity_lhs == qs.linearity_rhs,
        qs.evaluation_lhs == qs.y_star,
    );
    println!(
        "  Outer level: q_o = {} ≠ q = {} (κ = {}, s reduced there, h in Z_q); preimage freedom of [A | B′ | I_µ] per column = {} (the Σ key's own is 0 — transparency)",
        zk::pcs::mle::Q_O,
        Z1Coeff::MODULUS,
        inst.levels.kappa(),
        inst.levels.preimage_freedom(),
    );
    let base = inst.quad_params.theorem3().expect("toy bounds fit");
    let sigma_want = inst
        .quad_params
        .sigma_required(base.b, u128::try_from(LOG_M).expect("positive"))
        .expect("a required width");
    println!(
        "  Thm.5's width: σ required = {sigma_want} (14·m0·√n0·B_C·B/ln M at the input bound B = {}), sampled σ = {sigma} — the toy samples far below it, so ΠAgg's rejection hypothesis is NOT met here",
        base.b
    );
    println!(
        "  claim y = f(x) = {} is the only value the transcript pins down; ŷ*₀ = {}",
        coef(&inst.y).to_u128(),
        coef(&proof.y_stars[0]).to_u128()
    );

    // Tamper attribution: every component is caught by its own equation.
    let bump = |e: &E| el(coef(e).to_u128() as i64 + 1);
    expect_reject(
        "false claim y",
        &Instance {
            y: bump(&inst.y),
            ..inst.clone()
        },
        &proof,
        &[L11],
    );
    expect_reject(
        "tampered y_g",
        &inst,
        &Proof {
            y_g: bump(&proof.y_g),
            ..proof.clone()
        },
        &[L11],
    );
    // The aggregate `ŷ* = Σᵢ αᵢŷ*ᵢ + ŷ*_{m0}` erases any block whose `αᵢ` is 0 —
    // the challenge set `‖·‖₁ ≤ B_C` includes 0 — so the tamper bumps a block
    // that survives the combination rather than a fixed index.
    let live = proof
        .alphas
        .iter()
        .position(|a| coef(a) != Z1Coeff::ZERO)
        .expect("ααα has a non-zero entry");
    expect_reject(
        &format!("tampered ŷ*_{live}")[..],
        &inst,
        &Proof {
            y_stars: {
                let mut v = proof.y_stars.clone();
                v[live] = bump(&v[live]);
                v
            },
            ..proof.clone()
        },
        // The Fig. 7 challenge `c` is derived over the instance ΠQuad receives,
        // so a re-chosen ŷ* changes `c` and the response no longer opens the
        // committed matrix: L7 fires on top of the equations it broke, and
        // lines 9–10 on top of that — the sent `f̂*, r` answer the old `c`, and
        // the sent `z` no longer sums to the re-derived claim.
        &[L11, AGGY, OPEN, L7, L9, L10],
    );
    expect_reject(
        "tampered ŷ*_{m0}",
        &inst,
        &Proof {
            y_star_mask: bump(&proof.y_star_mask),
            ..proof.clone()
        },
        // Same cascade as the previous case: `ŷ*` is in `c`'s prefix.
        &[AGGY, OPEN, L7, L9, L10],
    );
    expect_reject(
        "tampered masking commitment",
        &inst,
        &Proof {
            com_mask: MleCommitment {
                c: {
                    let mut c = proof.com_mask.c.clone();
                    c[0] += Z1Coeff::ONE;
                    c
                },
            },
            ..proof.clone()
        },
        &[AGGC],
    );
    expect_reject(
        "tampered aggregate commitment",
        &inst,
        &Proof {
            u_hat: MleCommitment {
                c: {
                    let mut c = proof.u_hat.c.clone();
                    c[1] += Z1Coeff::ONE;
                    c
                },
            },
            ..proof.clone()
        },
        // L7 and L9 too: `û` is the Σ instance, so its challenge changes and
        // the sent response and the sent `z` stop matching the recomputed `c`.
        // L8 stays green — `s` reads the *outer* aggregate and the sent
        // stack, neither of which this tamper touches.
        &[AGGC, NORM, OPEN, L7, L9],
    );
    expect_reject(
        "tampered Σ response",
        &inst,
        &Proof {
            open: MleOpenProof {
                z: {
                    let mut z = proof.open.z.clone();
                    z[0] += Z1Coeff::ONE;
                    z
                },
                ..proof.open.clone()
            },
            ..proof.clone()
        },
        &[OPEN],
    );
    expect_reject(
        "wrong masking challenge x*",
        &inst,
        &Proof {
            xstar: bump(&proof.xstar),
            ..proof.clone()
        },
        // L9 too: `x*` is the mask row's weight in `v̂*₁`, so re-deriving it
        // moves line 9's left side `v̂*₁ᵀf̂*` while `zᵀc` (whose `c` does not
        // read `x*`) stands still. Line 10 stays green — `ŵ₀` is row 0 of the
        // table, where no `x*` lives.
        &[L11, OPEN, L9],
    );
    // x* = 0 is not in F×: the mask term drops out of line 11 and the same
    // opening would then certify two different claims, which is exactly what
    // Fig. 5 line 5 rules out.
    expect_reject(
        "zero masking challenge x*",
        &inst,
        &Proof {
            xstar: el(0),
            ..proof.clone()
        },
        &[UNIT, L11, OPEN, L9],
    );
    expect_reject(
        "ααα re-chosen for another transcript",
        &inst,
        &Proof {
            alphas: {
                let mut a = proof.alphas.clone();
                a[1] = bump(&a[1]);
                a
            },
            ..proof.clone()
        },
        // NORM holds: û itself is untouched, so the witness the verifier
        // recovers from it — and its column norms — are the honest ones. Every
        // Fig. 7 line fires: the re-chosen `ααα` re-derives the outer
        // aggregate `û` (so `s` is no longer a rounding error: L8) and the
        // challenge `c` (so the sent response stops matching: L7), and it
        // re-derives `ŷ*` itself, which lines 9–10 split between `zᵀc` and
        // the claim `zᵀŵ₀ = ŷ*`.
        &[AGGC, AGGY, OPEN, L7, L8, L9, L10],
    );

    // Fig. 7 line 7 on its own. The contracted randomness `r := Rc` is read by
    // exactly one check: it enters line 7's sum (`‖r‖` plus the residual
    // `h := A f̂* + B r − B_t Ťc` whose `B r` term it supplies) and nothing
    // else. Bumping one entry by 1 keeps the sent `t̂`, `f̂*` and `z` — and so
    // the recomputed challenge `c` — untouched, so lines 8, 9 and 10 stay green
    // while `h` becomes a field element: precisely the response-length
    // condition line 7 prints, and the one Theorem 1's
    // `MSIS_{q,μ,2B_αB_C B}` hypothesis rests on.
    expect_reject(
        "long contracted randomness r (line 7 alone)",
        &inst,
        &Proof {
            quad: MleQuadProof {
                r: {
                    let mut v = proof.quad.r.clone();
                    v[0] += Z1Coeff::ONE;
                    v
                },
                ..proof.quad.clone()
            },
            ..proof.clone()
        },
        &[L7],
    );
    // Line 7 is not the only reader of `f̂*` once lines 9–10 run: bumping `f̂*`
    // also breaks line 9's `v̂*₁ᵀf̂* = zᵀc` (the left side moves, the right
    // does not), so the two fire together. Kept as the witness that L9 is
    // load-bearing and attributed, distinct from L7.
    expect_reject(
        "bumped f̂* (lines 7 and 9)",
        &inst,
        &Proof {
            quad: MleQuadProof {
                f_star: {
                    let mut v = proof.quad.f_star.clone();
                    v[0] += Z1Coeff::ONE;
                    v
                },
                ..proof.quad.clone()
            },
            ..proof.clone()
        },
        &[L7, L9],
    );
    // Fig. 7 line 8 on its own. Shifting one stack entry by a multiple of the
    // INNER modulus `q` leaves line 5's `h` — hence line 7 — and the
    // transcript-bound challenge `c` (which absorbs residues, not widths)
    // *identical*; lines 9 and 10 read only `z`, `c`, `f̂*` and the instance, so
    // they stand. With a second modulus the escape has to clear it too, so the
    // shift below is `q·q_o`: `s := D t̂ − B_u û (mod q_o)` is then *bit-for-bit*
    // the honest residual, and the only thing left to reject is the integer the
    // figure compares — `‖t̂‖₂` jumps by `q·q_o` past `B_o`. That is the escape
    // line 8 exists to close, in the paper's own words (p. 9): binding "is
    // preserved when rounding errors are explicitly bounded so that they still
    // yield a short MSIS solution". A `q`-only shift is caught twice over (the
    // stack *and* `s`, which no longer rounds to `û`), which is the other thing
    // the second modulus buys.
    expect_reject(
        "stack shifted by q·q_o (line 8 alone)",
        &inst,
        &Proof {
            quad: MleQuadProof {
                t_hat: {
                    let mut v = proof.quad.t_hat.clone();
                    v[0] += i64::try_from(Z1Coeff::MODULUS).expect("a toy modulus")
                        * i64::try_from(zk::pcs::mle::Q_O).expect("a u32 q_o");
                    v
                },
                ..proof.quad.clone()
            },
            ..proof.clone()
        },
        &[L8],
    );
    // Fig. 7 lines 9 and 10 each on its own. Both read the *same* message `z`,
    // so a message tamper that leaves the rest of the transcript alone cannot
    // separate them: `c` is drawn over `z` (line 1 precedes line 2), so shifting
    // `z` re-draws `c`, and a prover that then answers lines 3–4 honestly for the
    // challenge it bought keeps lines 7 and 8 green while one of the two link
    // equations goes. The two shifts below are the kernel moves that decide which
    // one: `z ⊕ δ` with `⟨δ, ŵ₀⟩ = 0` keeps line 10's `zᵀŵ₀ = ŷ*` and breaks line
    // 9's `v̂*₁ᵀf̂* = zᵀc`, and the reverse needs `⟨δ, c⟩ = 0` exactly, which the
    // challenge set `C = {r : ‖r‖₁ ≤ B_C}` supplies through its own zero element
    // (`0 ∈ C`, so a transcript with `cₖ = 0` occurs with probability `1/|C|` and
    // `δ = eₖ` is then orthogonal to `c`). This is B.9's reading of the pair
    // (p. 20): line 9 is what the rewinding extractor turns into
    // `v̂*₁ᵀf̂*ₖ = cₖzₖ` per column, and line 10 is what converts those into the
    // claimed `ŷ*`; neither follows from the other.
    let nine = prove_full(&inst, &f, &[0x9eu8; 32], false, ZMode::Line9)
        .expect("the ŵ₀-orthogonal Quad.P terminates");
    expect_reject(
        "z shifted inside ŵ₀'s kernel (line 9 alone)",
        &inst,
        &nine,
        &[L9],
    );
    let ten = prove_full(&inst, &f, &[0xa7u8; 32], false, ZMode::Line10)
        .expect("a transcript with a zero challenge coordinate occurs within the search");
    expect_reject(
        "z shifted inside the challenge's kernel (line 10 alone)",
        &inst,
        &ten,
        &[L10],
    );

    // A prover that commits to a *long* block: every algebraic equation still
    // holds and only the shortness gates stop it — the paper's Theorem 1
    // binding argument, where the gate is what keeps the extracted witness an
    // MSIS solution. Fig. 7 line 7 joins `NORM` here rather than staying apart:
    // the long entries sit in the sub-polynomial rows, which are exactly the
    // rows `f̂*` contracts, so a long *witness* and a long *inner response* are
    // the same violation seen twice. L8 stays green — the rounding of a long
    // column is still a short stack entry.
    let mut long = poly(1);
    let wide = i64::try_from(Z1Coeff::MODULUS / 4).expect("a toy modulus") + 1;
    for i in 0..M0 {
        // A different *slot* per block (row i, column i), so no α-combination
        // can cancel the three: each survives in its own column of the
        // aggregate. And `q/4` rather than `q/2`, because every multiple
        // `k·(q/4)` with `|k| ≤ 2` stays at least `q/4` from zero mod `q` —
        // a `q/2` entry is exactly the value that cancels itself.
        long[i * (M1 * N0 * N1) + (i % M1) * (N0 * N1) + (i % (N0 * N1))] = el(wide + i as i64);
    }
    let long_inst = Instance {
        y: claim_of(&inst, &long),
        ..inst.clone()
    };
    // An honest prover never gets here: its own rejection loop refuses a long
    // aggregate. A cheating one does, and then only the gate stops it — the
    // same transcript passes every algebraic equation.
    let cheat = prove_with(&long_inst, &long, &[11u8; 32], true).expect("cheating prover runs");
    expect_reject(
        "long committed witness (cheating prover)",
        &long_inst,
        &cheat,
        &[NORM, L7],
    );

    // Evaluation hiding, measured: two different committed polynomials opened
    // at the same point, and the witness-free simulation of B.10's S1.
    let g = poly(2);
    let mut inst_g = setup(&[0x4au8; 32], x);
    inst_g.y = claim_of(&inst_g, &g);
    assert_ne!(
        coef(&inst.y),
        coef(&inst_g.y),
        "the two polynomials differ at x"
    );
    let m_f = margins(&inst, &f);
    let m_g = margins(&inst_g, &g);
    let (masked_f, raw_f, sim_f) = (&m_f.seen, &m_f.raw, &m_f.sim);
    let (masked_g, raw_g) = (&m_g.seen, &m_g.raw);
    let h = |v: &[Z1Coeff], bins: usize| masking::bucket_counts(v, bins, HALF);
    let d_fg =
        masking::statistical_distance(&h(masked_f, BINS), &h(masked_g, BINS)).expect("distance");
    let d_sim =
        masking::statistical_distance(&h(masked_f, BINS), &h(sim_f, BINS)).expect("distance");
    let d_raw =
        masking::statistical_distance(&h(raw_f, RAW_BINS), &h(raw_g, RAW_BINS)).expect("distance");
    // Two independent uniform samples of TRIALS values in BINS buckets sit this
    // far apart from sampling noise alone, so the assertion is calibrated.
    let floor = ((BINS as f64) / (2.0 * TRIALS as f64)).sqrt();
    println!(
        "  hiding: {} openings of f and of g at one point — SD(ŷ*₀) = {d_fg:.3}, SD(ŷ*₀ vs S1) = {d_sim:.3} (noise floor {floor:.3})",
        TRIALS
    );
    println!(
        "  hiding: distinct values seen — ŷ*₀ {}, ŷ*₀ from S1 {}, bare claim ŷ₀ {}",
        distinct(masked_f),
        distinct(sim_f),
        distinct(raw_f)
    );
    println!(
        "  hiding: at {}-bucket resolution the *unmasked* ŷ₀ of the two polynomials sit at distance {d_raw:.3}",
        RAW_BINS
    );
    let rejects = m_f.rej_rejects + m_g.rej_rejects;
    let draws = (m_f.proofs + m_g.proofs + rejects as usize) as f64;
    let rate = ((m_f.proofs + m_g.proofs) as f64 / draws).max(0.0);
    println!(
        "  Rej: {} accepted transcripts from {} line-14 draws → rate {rate:.3}, Lemma 2's bound (1−2⁻¹²⁸)/M = {:.3} (mean {:.2} attempts per proof)",
        m_f.proofs + m_g.proofs,
        draws as usize,
        1.0 / std::f64::consts::E,
        (m_f.attempts + m_g.attempts) as f64 / (m_f.proofs + m_g.proofs) as f64
    );
    assert!(
        rate > 0.30,
        "σ = 14·T/ln M must keep the acceptance rate at or above 1/M ≈ 0.368, got {rate:.3}"
    );
    assert!(
        d_fg < 1.5 * floor && d_sim < 1.5 * floor,
        "the masked view must be indistinguishable between the two polynomials \
         and between the real and simulated runs"
    );
    assert_eq!(
        distinct(masked_f),
        TRIALS,
        "every masked opening must look like a fresh field element"
    );
    assert_eq!(distinct(raw_f), 1, "the unmasked claim is one fixed value");
    assert_ne!(
        raw_f[0], raw_g[0],
        "the two polynomials must differ on block 0"
    );
    assert!(
        d_raw > 0.9,
        "without the mask the two polynomials are trivially distinguishable"
    );

    // Theorem 2's hiding, run against *the commitment it states*: the same
    // bucketing machinery over `tₖ = A f̂*ₖ + [B′ | I_µ] rₖ` (Fig. 3 `Com*`
    // step 3, p. 9), fixed message column / fresh `rₖ ← D_σ^{µ+ν}` per trial
    // exactly as B.5 reduces the claim (p. 18). The numbers printed here are
    // the measurement, not the assumption: what is *measured* is statistical
    // distance at this resolution; the computational step ("`B rₖ` looks
    // uniform") is `MLWE_{q,ν,χ}` and no histogram can certify it.
    let v_f = thm2_view(&inst, &f, &[7u8; 32]);
    let v_g = thm2_view(&inst_g, &g, &[0xe3u8; 32]);
    let n_t = v_f.masked.len();
    let hb = |v: &[Z1Coeff]| masking::bucket_counts(v, BINS, HALF);
    let sd = |a: &[Z1Coeff], b: &[Z1Coeff]| {
        masking::statistical_distance(&hb(a), &hb(b)).expect("equally long views")
    };
    let floor_t = ((BINS as f64) / (2.0 * n_t as f64)).sqrt();
    let d_t_fg = sd(&v_f.masked, &v_g.masked);
    let d_t_zero = sd(&v_f.masked, &v_f.zero);
    let d_t_uni = sd(&v_f.masked, &v_f.uniform);
    let filled = |v: &[Z1Coeff]| hb(v).iter().filter(|&&c| c > 0).count();
    println!(
        "  Thm.2 (B=[B'|I_mu]: mu={MASKED_MU}, nu={MASKED_NU}, chi=D_{sigma}): {n_t} commitment entries per polynomial — SD(f,g) = {d_t_fg:.4}, SD(f, commit-zero) = {d_t_zero:.4}, SD(f, uniform) = {d_t_uni:.4} (noise floor {floor_t:.4}); buckets filled: f {}, g {}, commit-zero {}, uniform {} of {BINS}",
        filled(&v_f.masked),
        filled(&v_g.masked),
        filled(&v_f.zero),
        filled(&v_f.uniform),
    );
    // The two controls, printed apart because they fail at different
    // resolutions. `B` without the identity block still scatters into every
    // bucket — its exposure is at single-value resolution, where the mask's
    // support (≈ the `D_σ` atoms) caps the distinct count — and a commitment
    // with no randomness at all is a point mass on every bucket statistic.
    let d_noid = sd(&v_f.no_identity, &v_g.no_identity);
    let d_unmasked = sd(&v_f.unmasked, &v_g.unmasked);
    println!(
        "  Thm.2 controls: B without I_mu: SD(f,g) = {d_noid:.4} (bucket-blind) yet distinct {} of {n_t} — its mask spans {}-odd D_sigma atoms; no randomness: SD(f,g) = {d_unmasked:.3}, distinct {} (= one column per slot)",
        distinct(&v_f.no_identity),
        24 * sigma,
        distinct(&v_f.unmasked),
    );
    assert!(
        d_t_fg < 3.0 * floor_t && d_t_zero < 3.0 * floor_t && d_t_uni < 3.0 * floor_t,
        "the masked commitment's buckets must sit at the sampling-noise floor \
         against the other polynomial, the commit-zero simulator and uniform — \
         measured, not assumed"
    );
    assert!(
        d_unmasked > 3.0 * floor_t,
        "the mask-free view must sit far above the noise floor the masked view \
         achieved — measured: {d_unmasked:.3} against a floor of {floor_t:.4}; \
         its bucket distance is capped near 1 − 9/16, not 1, because the \
         message has 9 columns and two 9-point pools of 16 buckets overlap by \
         9²/16 draws — the SHARP form of the same fact is the distinct-count \
         assert below: 9 values where the masked commitment takes 3600"
    );
    assert_eq!(
        distinct(&v_f.unmasked),
        n_t / TRIALS,
        "a mask-free commitment repeats its message column exactly"
    );
    assert!(
        distinct(&v_f.masked) * 20 > n_t * 19,
        "with I_µ present the entries must be near-injectively spread over the pool"
    );
    // The honest limit of the bucket picture, printed rather than buried: a
    // `D_σ`-wide `B′r′` ALONE already scatters into every bucket at a
    // distinct-count near the masked one — no histogram at this scale
    // separates the error-free degeneration from the full `B = [B′ | I_µ]`.
    // What separates them *statistically* is exposure of the message offset:
    // Δ := A(f̂*_{f,k} − f̂*_{g,k}) is key arithmetic an honest verifier can
    // run, and `(t_f − t_g − Δ)/b′` is `δ′ + δ″/b′` with δ′, δ″ the two views'
    // `D_σ` coordinate-differences — which the identity term δ″ smears over
    // the whole field, while the error-free `B′`-only view (δ″ ≡ 0) leaves
    // the plain integer `r′_f − r′_g`, mass `≈ 24σ` wide, visible under the
    // inversion. B.5's MLWE step is exactly the assumption that a `B′` given
    // with its products hides even that; the toy can *see* the two views are
    // statistically distinct at fine resolution, so the example says so
    // rather than testing it away.
    let b_prime = {
        // B′'s single column, read through B itself: e₀ has zero identity
        // part, so `B·e₀ = B′[:,0]`.
        let mut e = vec![Z1Coeff::ZERO; MASKED_MU + MASKED_NU];
        e[0] = Z1Coeff::ONE;
        inst.levels.mask_block().apply(&e)[0]
    };
    let b_inv = b_prime.inverse().expect("a uniform B′ entry is nonzero");
    let offset_exposed = |a: &[Z1Coeff], b: &[Z1Coeff]| {
        a.iter()
            .zip(b.iter())
            .filter(|(x, y)| {
                let d: Z1Coeff = **x - **y;
                (d.centered() as i128).abs() < 24 * i128::from(sigma)
            })
            .count()
    };
    let delta = {
        let (blocks_f, masks_f) = split(&inst, &f, &[7u8; 32]);
        let (blocks_g, masks_g) = split(&inst_g, &g, &[0xe3u8; 32]);
        let mut d = Vec::new();
        for i in 0..M0 {
            let cols = N0 * N1;
            for k in 0..cols {
                let mut mf: Vec<Z1Coeff> =
                    (0..M1).map(|j| coef(&blocks_f[i][j * cols + k])).collect();
                mf.push(coef(&masks_f[i][k]));
                let mut mg: Vec<Z1Coeff> =
                    (0..M1).map(|j| coef(&blocks_g[i][j * cols + k])).collect();
                mg.push(coef(&masks_g[i][k]));
                // Δ = A·m_f − A·m_g from the instance's own A, no randomness.
                let no_r = vec![Z1Coeff::ZERO; MASKED_MU + MASKED_NU];
                let tf = inst.levels.inner_apply(&mf, &no_r);
                let tg = inst.levels.inner_apply(&mg, &no_r);
                d.extend(tf.iter().zip(&tg).map(|(x, y)| *x - *y));
            }
        }
        // The message is FIXED across trials (B.5's reduction), so pool entry
        // j of both views carries the same Δ as d[j mod 9].
        let per_trial = d.len();
        assert_eq!(per_trial * TRIALS, n_t, "one Δ per pool entry, repeated");
        d.into_iter().cycle().take(n_t).collect::<Vec<Z1Coeff>>()
    };
    let shift = |a: &[Z1Coeff], b: &[Z1Coeff], d: &[Z1Coeff]| {
        a.iter()
            .zip(b.iter())
            .zip(d.iter())
            .map(|((x, y), dd)| (*x - *y - *dd) * b_inv)
            .collect::<Vec<Z1Coeff>>()
    };
    let exp_noid = offset_exposed(
        &shift(&v_f.no_identity, &v_g.no_identity, &delta),
        &vec![Z1Coeff::ZERO; n_t],
    );
    let exp_masked = offset_exposed(
        &shift(&v_f.masked, &v_g.masked, &delta),
        &vec![Z1Coeff::ZERO; n_t],
    );
    let exp_unmasked = offset_exposed(
        &shift(&v_f.unmasked, &v_g.unmasked, &delta),
        &vec![Z1Coeff::ZERO; n_t],
    );
    println!(
        "  Thm.2 fine resolution: (t_f−t_g−Δ)/b′ is 24σ-centred for {exp_noid} / {n_t} B′-only pairs, {exp_masked} / {n_t} masked pairs and {exp_unmasked} / {n_t} without any randomness — the identity term is what smears the offset over the field; the error-free view's INDIFFERENTIABILITY from the masked one is B.5's MLWE ASSUMPTION, and at this toy scale it is measurably FALSE statistically ({exp_masked} vs {exp_noid} exposed), so the example reports the assumption rather than testing it away",
    );
    assert_eq!(
        exp_unmasked, n_t,
        "the no-randomness control must expose the offset on EVERY pair"
    );
    assert_eq!(
        exp_noid, n_t,
        "B′ alone (δ″ ≡ 0) leaves r′_f − r′_g visible on EVERY pair: this is \
         the shape the header says this assembly USED to commit with"
    );
    assert!(
        exp_masked * 100 < n_t,
        "with the identity block the exposed-offset rate must be a tail event \
         (24σ·b′⁻¹-smear against a field of q); measured {exp_masked} of {n_t}"
    );
    // The module doc promises every named check is tripped by some tamper. Executed
    // rather than promised: a check no tamper can fail is dead code, and this is the
    // only thing that would notice.
    {
        let named = [UNIT, L11, AGGC, AGGY, OPEN, NORM, L7, L8, L9, L10];
        let tripped = TRIPPED.with(|t| t.borrow().clone());
        let dead: Vec<&str> = named
            .iter()
            .filter(|n| !tripped.contains(&(**n).to_string()))
            .copied()
            .collect();
        assert!(
            dead.is_empty(),
            "no tamper ever tripped {dead:?} — those checks are untested, not verified"
        );
        println!(
            "coverage: all {} named checks tripped by some tamper ({} measured failing sets)",
            named.len(),
            tripped.len()
        );
    }
    println!("done in {:.2?}", t0.elapsed());
}
