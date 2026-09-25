//! The high-arity **folding reduction** Π^Fold (Cheng–Nguyen–Tyagi, eprint
//! 2026/2067 §2.2.2 / Protocol 4) over the Ajtai hash tree, with the
//! challenge-set accounting that decides how much norm the fold costs.
//!
//! # The step
//!
//! Given a tree evaluation claim `(t, u, v)` with witness `(s_i)_{i∈[ℓ]}`
//! (Protocol 4's `Input`), the prover opens `k` layers at once and folds the
//! resulting `2^k` subtrees into a single claim of height `ℓ − k`:
//!
//! ```text
//! s_{k+i} = s_{k+i,1} ‖ … ‖ s_{k+i,2^k}      (2^k chunks of 2^i·nα)
//! t*      = Σ_j c_j · (G_n · s_{k,j})         (Eq. 11)
//! s*_i    = Σ_j c_j · s_{k+i,j}               (Eq. 11)
//! v_bot   = Σ_j c_j · s̃_j(r)                  (Protocol 4 Step 3(c))
//! ```
//!
//! Maltese departs from CMNW's 2-to-1 folding in the two ways §2.2.2 states: it
//! folds `2^k`-to-1, and because the claim lives on the *concatenated* openings
//! `s = 0^{2nα}‖s_1‖…‖s_ℓ`, "the simple linear combination approach of Cini et
//! al. no longer applies". Splitting `ṽ(u)` into a top-tree claim and a
//! bottom-subtrees claim is Eq. (12); the weights that make each subtree claim
//! linear are the `q_{subs,j}` of Eq. (14), which the verifier can evaluate
//! itself (§5.2.1: "`V` can evaluate `ṽq_{subs,j}(X)` in `O(ℓ² + ℓm)` time") —
//! so [`subtree_weights_at_point`] is computed by both sides from one code path.
//!
//! # Protocol 4's statement, verbatim (§5.2.2, pp. 32–34)
//!
//! ```text
//! Input : x̃ = (t ∈ R_F^n, u ∈ R_F^{ℓ+1+m}, v ∈ R_F),  w = (s_i ∈ R_F^{2ⁱnα})_{i∈[ℓ]}  ∈ TE(1,ℓ,b)
//! Output: x̃_top = (t, r⃗', y_top),  w_top = (s_i)_{i∈[k]}          ∈ TE(1,k,b)
//!         x̃_bot = (t*, r⃗,  v_bot), w_bot = (s*_i)_{i∈[ℓ−k]}        ∈ TE(1,ℓ−k,B)
//!         x̃_subs= (t_subs, r⃗'_{[:k+m]}, y_subs, k), w_subs         ∈ PE(1,k,b)
//! where B = 2^k · T · b.
//! ```
//!
//! Three point-length facts follow, and [`fold_prove`]/[`fold_verify` enforce all
//! three rather than trusting a caller: the *input* is a `TE` point of
//! `ℓ+1+m` coordinates (this is why [`crate::pcs::tree_eval::concatenated_point`]
//! exists — Π^Fold consumes a TE claim and the cycle's head is a PE claim);
//! `r⃗ ∈ R_F^{ℓ−k+1+m}` is Eq. (15)'s sum-check output point and becomes the
//! folded claim's point; and the top claim's point is the **suffix**
//! `u_{[ℓ−k+1:]}` of length `k+1+m`, because Eq. (12) factors the *prefix* out:
//! `v = êq(0^{ℓ−k}, u_{[:ℓ−k]})·v_top + v_subs`, with `v_top = s̃_top(u_{[ℓ−k+1:]})`
//! ([`top_claim_factor`]). Step 5's `x̃_subs` uses the **prefix** `r⃗'_{[:k+m]}`
//! — a `PE` point, one coordinate shorter, which is the same ℓ+m / ℓ+1+m
//! distinction as §5's two relations.
//!
//! §5.4 (p. 39) then settles where the cycle stops: after `ω` cycles
//! "Π^Dec will output a base case claim in `PE(k,b)` … or the claim can be
//! **directly checked by opening the tree commitment and checking the
//! evaluation**". That base case is a `PE` claim on a `k`-layer tree, so the
//! direct check is [`crate::pcs::tree_eval::layer_claim`] against `Open` — no
//! point surgery anywhere.
//!
//! # The cost, which is the whole game
//!
//! ```text
//! B = 2^k · T · b        (Protocol 4's output bound; T = Def. 15 expansion factor)
//! ```
//!
//! [`ChallengeSet::expansion_factor`] instantiates Theorems 3 and 4, and
//! [`CycleShape`] reports Lemma 13's bookkeeping: with `h = log_b B` one cycle
//! maps `ℓ ↦ ℓ − k + 1 + ⌈log₂ h⌉`, so it only *progresses* when
//! `k > log h + 1` (§2.2). For P3 (`b = 2`, `C = C_sp(32,8)`, `T = 48`, `k = 7`)
//! that is `B = 12288`, `h = 14`, two layers removed per cycle; at `k ≤ 5` the
//! same `T` makes the cycle grow instead — the wall CMNW hits at constant `ℓ = 3`.
//!
//! [`ChallengeSet::deterministically_invertible`] evaluates Theorem 2's bound
//! `‖y‖∞ < q^{e/d}/√(d/e)` in exact integer arithmetic, which is what decides
//! Fig. 5's "Heuristic?" column: `true` for P3 (`C_sp(32,8)`, `d = 64`, `e = 8`,
//! `q = 2³²−99`), `false` for P2 (`e = 4`).
//!
//! # Index conventions
//!
//! Every index goes through [`crate::pcs::tree_eval::layer_range`] and
//! [`crate::pcs::tree_eval::bits_of`] (MSB-first), which is what makes
//! Eq. (12)'s `êq(0^{ℓ−k}, u)` factorization and Eq. (14)'s
//! `êq(0^{ℓ−(k+i)}‖1‖bits_k(j−1), u_{(:ℓ−i+1)})` prefix come out right.

use crate::pcs::tree_commit::{self, TreeError, TreeKey, TreeOpening};
use crate::pcs::tree_eval::{self, bits_of, eq_of_bits_point, eq_ring_table, zero_ring, EvalError};
use crate::sumcheck::circuit::{
    self, CircuitError, CircuitSumcheckProof, Composition, LinePoly,
};
use algebra::crypto::sampling::{sample_in_ball_signs, BitStream};
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::{CenteredRing, MatrixElement, Ring};
use algebra::ring::PolynomialQuotientRing;
use alloc::{vec, vec::Vec};
use core::fmt::{self, Display};

/// Why a folding round was refused, naming the equation of Protocol 4.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FoldError {
    /// Protocol 4 Step 1(b), Eq. (12):
    /// `v ≠ êq(0^{ℓ−k}, u_{(:ℓ−k)})·v_top + v_subs`.
    SplitClaimMismatch,
    /// Eq. (14)/(15): `v_subs ≠ Σ_j ⟨q_{subs,j}, s_j⟩`.
    SubtreeWeightsMismatch,
    /// The Fiat–Shamir sum-check of Step 2 did not verify.
    SumcheckRejected,
    /// The declared round-message width is smaller than the circuit Eq. (15)
    /// states needs: `q̃_{subs,j}(X)·s̃_j(X)` is a product of two multilinears, so
    /// `Δ = 2` and the width is [`FOLD_NC`] = 3. Unreachable while
    /// [`SubtreeCircuit`] and [`FOLD_NC`] agree — it reports an internal overrun,
    /// not a caller mistake, and truncating silently would be worse.
    DegreeUnderstated {
        /// Degree the circuit reaches.
        degree: usize,
        /// Degree the declared width supports.
        declared: usize,
    },
    /// Eq. (15)'s output claim: `y_subs ≠ Σ_j q̃_{subs,j}(r)·s̃_j(r)`.
    SubtreeEvaluationMismatch,
    /// Eq. (17): a subtree evaluation is not the recomposed slot of `t_subs`.
    SubtreeCommitmentMismatch {
        /// Subtree index whose slot disagreed.
        subtree: usize,
    },
    /// Eq. (11): `t*` is not the `c`-combination of the recomposed layer-`k`
    /// children.
    FoldedCommitmentMismatch,
    /// Eq. (19): the powers-batched form of the same fact disagrees.
    FoldedCommitmentBatchMismatch,
    /// Eq. (11): a folded layer opening is not `Σ_j c_j·s_{k+i,j}`.
    FoldedLayerMismatch {
        /// Layer index within the folded tree.
        level: usize,
    },
    /// Protocol 4 Step 3(c) / Eq. (18): `v_bot ≠ s̃_bot(r)`.
    FoldedEvaluationMismatch,
    /// Protocol 4's bound: `‖s*‖∞ > 2^k·T·b`, so the challenge set expanded the
    /// witness past what Module-SIS binding can absorb.
    NormGrowth {
        /// Observed norm of the folded openings.
        got: u64,
        /// `B = 2^k·T·b`.
        bound: u64,
    },
    /// `k` layers cannot be opened from a tree of this height.
    HeightTooSmall {
        /// Tree height `ℓ`.
        height: usize,
        /// Requested arity exponent `k`.
        k: usize,
    },
    /// A vector had the wrong length for its role in the fold.
    WrongLength {
        /// Length supplied.
        got: usize,
        /// Length required.
        expected: usize,
    },
    /// The tree commitment carried into the fold does not open.
    Tree(TreeError),
    /// The *subtree* commitment `t_subs` (Eq. 16) does not open — a different
    /// obligation from [`FoldError::Tree`], which is the witness the fold is applied
    /// to. They shared one variant until 2026-09-24, which made the two
    /// indistinguishable in any audit that names errors: forging `t_subs` and
    /// forging the input root produced the same check.
    SubtreeCommitInvalid(TreeError),
    /// An evaluation claim inside the fold was refused.
    Eval(EvalError),
}

impl fmt::Display for FoldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FoldError::SplitClaimMismatch => write!(
                f,
                "Eq. 12 fails: v ≠ êq(0^(ℓ−k), u)·v_top + v_subs, so the claim was not split honestly"
            ),
            FoldError::SubtreeWeightsMismatch => {
                write!(f, "Eq. 14/15 fails: v_subs is not Σ_j ⟨q_subs,j, s_j⟩")
            }
            FoldError::SumcheckRejected => write!(f, "the subtree sum-check transcript rejected"),
            FoldError::DegreeUnderstated { degree, declared } => write!(
                f,
                "Eq. 15's circuit reaches degree {degree} but the declared round width supports {declared}"
            ),
            FoldError::SubtreeEvaluationMismatch => write!(
                f,
                "Eq. 15's final claim y_subs ≠ Σ_j q̃_subs,j(r)·s̃_j(r)"
            ),
            FoldError::SubtreeCommitmentMismatch { subtree } => write!(
                f,
                "Eq. 17 fails: subtree {subtree}'s evaluation is not the recomposed t_subs slot"
            ),
            FoldError::FoldedCommitmentMismatch => {
                write!(f, "Eq. 11 fails: t* ≠ Σ_j c_j·G_n·s_k,j")
            }
            FoldError::FoldedCommitmentBatchMismatch => write!(
                f,
                "Eq. 19 fails: ⟨p_η,n,t*⟩ ≠ Σ_j c_j·⟨p_η,n⊗p_b,α, s_k,j⟩"
            ),
            FoldError::FoldedLayerMismatch { level } => {
                write!(f, "Eq. 11 fails: folded layer {level} ≠ Σ_j c_j·s_(k+{level}),j")
            }
            FoldError::FoldedEvaluationMismatch => {
                write!(f, "Eq. 18 fails: v_bot ≠ s̃_bot(r) for the folded concatenation")
            }
            FoldError::NormGrowth { got, bound } => write!(
                f,
                "folded openings have ‖·‖∞ = {got} > B = 2^k·T·b = {bound}: binding would be lost"
            ),
            FoldError::HeightTooSmall { height, k } => write!(
                f,
                "cannot fold k = {k} layers of a height-{height} tree (Protocol 4 needs ℓ > k)"
            ),
            FoldError::WrongLength { got, expected } => {
                write!(f, "vector of {got} elements, expected {expected}")
            }
            FoldError::Tree(err) => write!(f, "input tree commitment invalid: {err}"),
            FoldError::SubtreeCommitInvalid(err) => {
                write!(f, "t_subs (Eq. 16) does not open: {err}")
            }
            FoldError::Eval(err) => write!(f, "evaluation claim invalid: {err}"),
        }
    }
}

impl From<TreeError> for FoldError {
    fn from(err: TreeError) -> Self {
        FoldError::Tree(err)
    }
}

impl From<EvalError> for FoldError {
    fn from(err: EvalError) -> Self {
        FoldError::Eval(err)
    }
}

/// The folding challenge sets of §3.4, carrying the two numbers the analysis
/// needs: how large the set is, and how much a multiplication by one of its
/// elements expands a norm.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChallengeSet {
    /// Def. 11: the dense ternary set `Cter` of all `3^d` coefficient vectors in
    /// `{−1, 0, 1}^d`.
    DenseTernary,
    /// Def. 14: the sparse coefficient set `C_sp(τ₁, τ₂)` — exactly `τ₁`
    /// coefficients in `{−1,1}`, exactly `τ₂` in `{−2,2}`, the rest zero. P1, P3
    /// and P7 use `C_sp(32, 8)`.
    Sparse {
        /// Count of `±1` coefficients.
        tau1: u32,
        /// Count of `±2` coefficients.
        tau2: u32,
    },
}

impl ChallengeSet {
    /// The expansion factor `T_C` of Def. 15, bounded by Theorem 3
    /// (`T_Cter ≤ d`, `T_{Cter−Cter} ≤ 2d`) and Theorem 4
    /// (`T_{Csp(τ₁,τ₂)} ≤ τ₁ + 2τ₂`).
    pub const fn expansion_factor(&self, ring_degree: usize) -> u64 {
        match self {
            ChallengeSet::DenseTernary => ring_degree as u64,
            ChallengeSet::Sparse { tau1, tau2 } => *tau1 as u64 + 2 * *tau2 as u64,
        }
    }

    /// `max ‖a − b‖∞` over the difference set `C − C`: `2` for `Cter` and `4` for
    /// `Csp` (§3.4 states both bounds explicitly).
    pub const fn difference_norm(&self) -> u64 {
        match self {
            ChallengeSet::DenseTernary => 2,
            ChallengeSet::Sparse { .. } => 4,
        }
    }

    /// `log₂|C|` rounded to the nearest integer — Fig. 5's (p. 46) challenge-set
    /// size column, which is what a parameter sheet quotes as the soundness bits
    /// per challenge.
    ///
    /// Def. 14 gives `|C_sp(τ₁,τ₂)| = choose(d,τ₁)·choose(d−τ₁,τ₂)·2^{τ₁+τ₂}` and
    /// Def. 11 gives `|Cter| = 3^d`. Two things follow. Rounding must be
    /// **nearest**, not up: Fig. 5 prints `101` for `d = 64` ternary
    /// (`log₂ 3⁶⁴ = 101.44`) but `203` for `d = 128` (`202.88`), which no
    /// ceiling or floor reproduces from both. And the size cannot be held
    /// exactly — `3^128 ≈ 2^203` overflows `u128`, which is why this used to
    /// saturate and report `128`. [`BigLog2`] therefore carries a normalised
    /// 64-bit window and settles the `√2` boundary that rounding to nearest
    /// turns on.
    pub fn log2_size(&self, ring_degree: usize) -> u32 {
        let d = ring_degree as u32;
        match self {
            ChallengeSet::DenseTernary => {
                let mut acc = BigLog2::ONE;
                for _ in 0..d {
                    acc = acc.mul(3);
                }
                acc.rounded()
            }
            ChallengeSet::Sparse { tau1, tau2 } => {
                // Exact while it fits (every set Fig. 5 prints does), and the
                // windowed path above otherwise.
                let exact = binomial(d, *tau1)
                    .checked_mul(binomial(d - *tau1, *tau2))
                    .and_then(|v| v.checked_shl(*tau1 + *tau2));
                match exact {
                    Some(size) if size > 0 => {
                        let bits = u128::BITS - size.leading_zeros();
                        if bits > 64 {
                            let top = (size >> (bits - 33)) as u64;
                            bits - 1 + u32::from(top >= SQRT2_TIMES_2POW32)
                        } else {
                            // `size²` fits, so the boundary test is exact.
                            let floor = bits - 1;
                            let round_up = size
                                .checked_mul(size)
                                .is_some_and(|sq| sq >= (1u128 << (2 * floor + 1)));
                            u32::from(round_up) + u32::try_from(floor).expect("fits u32")
                        }
                    }
                    _ => {
                        let mut acc = BigLog2::ONE;
                        for i in 0..*tau1 {
                            acc = acc.mul(u128::from(d - i)).div(u128::from(i + 1));
                        }
                        for i in 0..*tau2 {
                            acc = acc.mul(u128::from(d - *tau1 - i)).div(u128::from(i + 1));
                        }
                        acc.rounded().saturating_add(*tau1 + *tau2)
                    }
                }
            }
        }
    }

    /// Theorem 2 (`[LS18]` Cor. 1.2): any `y ∈ R_F` with
    /// `0 < ‖y‖∞ < q^{e/d}·√(e/d)`… in the paper's exact form
    /// `‖y‖∞ < (1/√(d/e))·q^{e/d}` is invertible. Rearranged into integers —
    /// squaring and raising to `d/e` — the test is
    ///
    /// ```text
    /// (‖y‖∞² · (d/e))^(d/e) < q²
    /// ```
    ///
    /// with no floating point, because a wrong `e` would otherwise flip Fig. 5's
    /// heuristic column silently.
    ///
    /// Returns `false` when `e = 0` or `e` does not divide `d` (the factorisation
    /// the bound is stated over does not exist).
    pub fn deterministically_invertible(&self, q: u64, d: usize, e: usize) -> bool {
        if e == 0 || d % e != 0 {
            return false;
        }
        let ratio = (d / e) as u128;
        let y = u128::from(self.difference_norm());
        let base = y.saturating_mul(y).saturating_mul(ratio);
        let mut acc: u128 = 1;
        let mut power = ratio;
        let mut factor = base;
        while power > 0 {
            if power & 1 == 1 {
                acc = acc.saturating_mul(factor);
            }
            power >>= 1;
            if power > 0 {
                factor = factor.saturating_mul(factor);
            }
        }
        acc < (q as u128).saturating_mul(q as u128)
    }

    /// Draws one challenge from the set, deterministically from
    /// `(seed, index)` — the two sides call it with the same arguments, so the
    /// folding challenges cannot drift.
    ///
    /// For `C_sp` the support comes from the FIPS 204 `SampleInBall` sampler
    /// (uniform over `τ₁ + τ₂`-subsets with independent signs), and the first
    /// `τ₂` occupied positions carry the `±2` amplitude: exactly Def. 14's
    /// uniform choice over disjoint `S₁, S₂` with `|S₁| = τ₁`, `|S₂| = τ₂`.
    ///
    /// # Panics
    /// If `τ₁ + τ₂ ≥ d` (Def. 14 requires `1 ≤ τ₁ + τ₂ < d`) or `d > 256`
    /// (`SampleInBall` draws positions from one byte).
    pub fn sample<R: Ring, const D: usize>(&self, seed: &[u8; 32], index: u64) -> PolyRing<R, D> {
        let mut coefficients = vec![R::ZERO; D];
        match self {
            ChallengeSet::DenseTernary => {
                let mut xof = Shake256Xof::new(b"lattice-algebra/Z7/fold-challenge-ter");
                xof.absorb(seed);
                xof.absorb(&index.to_le_bytes());
                let mut stream = BitStream::new(&mut xof);
                for slot in coefficients.iter_mut() {
                    *slot = match stream.read_bits(8) % 3 {
                        0 => R::ONE,
                        1 => R::ONE.neg(),
                        _ => R::ZERO,
                    };
                }
            }
            ChallengeSet::Sparse { tau1, tau2 } => {
                let weight = *tau1 + *tau2;
                assert!(
                    (weight as usize) < D,
                    "Def. 14 needs τ₁ + τ₂ < d, got {weight} of {D}"
                );
                let mut xof = Shake256Xof::new(b"lattice-algebra/Z7/fold-challenge-sp");
                xof.absorb(seed);
                xof.absorb(&index.to_le_bytes());
                let mut stream = BitStream::new(&mut xof);
                let signs = sample_in_ball_signs(&mut stream, weight, D);
                let mut remaining_doubles = *tau2;
                for (i, sign) in signs.iter().enumerate() {
                    if *sign == 0 {
                        continue;
                    }
                    let magnitude = if remaining_doubles > 0 {
                        remaining_doubles -= 1;
                        2u64
                    } else {
                        1u64
                    };
                    coefficients[i] = if *sign > 0 {
                        R::from(magnitude)
                    } else {
                        R::from((u128::from(R::MODULUS) - u128::from(magnitude)) as u64)
                    };
                }
            }
        }
        PolyRing::from_coefficients(coefficients)
    }
}

/// `⌊√2 · 2³²⌋ = 6074001000`. Rounding `log₂ N` to the *nearest* integer is the
/// same as testing `N ≥ √2·2^{⌊log₂ N⌋}`, i.e. testing whether the top 33 bits of
/// `N` reach this value — which is how Fig. 5's printed `101`/`124`/`203` come out
/// of exact integer arithmetic with no floating point.
///
/// The test is permissive by one unit in `2³²` (the true boundary is
/// `6074001000.06…`), the same width as the truncation band of [`BigLog2`]'s
/// 64-bit window. No challenge-set size in this scheme comes anywhere near it.
const SQRT2_TIMES_2POW32: u64 = 6_074_001_000;

/// The top-64-bit window plus binary exponent behind
/// [`ChallengeSet::log2_size`], so a set size like `3^128 ≈ 2^203` — which fits
/// no machine integer — can still have its logarithm rounded correctly.
///
/// `hi` always has bit 63 set (the window is left-aligned on the value's leading
/// bit) and `bits` is the tracked bit length, so `N = hi · 2^{bits−64}` up to the
/// bits below the window.
struct BigLog2 {
    hi: u64,
    bits: u32,
}

impl BigLog2 {
    /// The value `1`.
    const ONE: Self = Self {
        hi: 1u64 << 63,
        bits: 1,
    };

    /// Multiplies by a positive factor below `2³²`, keeping the top 64 bits.
    fn mul(self, factor: u128) -> Self {
        debug_assert!(factor > 0 && factor < (1u128 << 32), "factor width");
        let product = u128::from(self.hi) * factor;
        let shift = u128::BITS - u32::try_from(product.leading_zeros()).expect("u128") - 64;
        Self {
            hi: (product >> shift) as u64,
            bits: self.bits + shift,
        }
    }

    /// Divides by a positive factor below `2³²`, scaling by `2³²` first so the
    /// quotient still carries 64 significant bits.
    fn div(self, factor: u128) -> Self {
        debug_assert!(factor > 0 && factor < (1u128 << 32), "factor width");
        let quotient = (u128::from(self.hi) << 32) / factor;
        let shift = u128::BITS - u32::try_from(quotient.leading_zeros()).expect("u128") - 64;
        Self {
            hi: (quotient >> shift) as u64,
            bits: self.bits + shift - 32,
        }
    }

    /// The nearest integer to `log₂` of the tracked value.
    fn rounded(&self) -> u32 {
        debug_assert!(self.bits >= 1);
        let floor = self.bits - 1;
        // `hi >> 31` is the value's top 33 bits, in `[2³², 2³³)`.
        floor + u32::from((self.hi >> 31) >= SQRT2_TIMES_2POW32)
    }
}

/// `choose(n, k)` in exact `u128` arithmetic, saturating.
fn binomial(n: u32, k: u32) -> u128 {
    if k > n {
        return 0;
    }
    let k = k.min(n - k);
    let mut acc: u128 = 1;
    for i in 0..k {
        acc = acc
            .saturating_mul(u128::from(n - i))
            .checked_div(u128::from(i + 1))
            .unwrap_or(u128::MAX);
    }
    acc
}

/// Lemma 13 / Protocol 4: the norm and height accounting of one folding cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CycleShape {
    /// Folding arity exponent `k`.
    pub k: usize,
    /// Challenge expansion factor `T`.
    pub expansion: u64,
    /// Output norm bound `B = 2^k·T·b`.
    pub bound: u64,
    /// `h = ⌈log_b B⌉`, the number of decomposition planes Π^Dec needs.
    pub planes: usize,
    /// `h` zero-padded to a power of two (Eq. 21's remark).
    pub padded_planes: usize,
}

impl CycleShape {
    /// Computes the accounting of one cycle from `k`, the challenge set's
    /// expansion factor and the gadget base `b`.
    ///
    /// # Panics
    /// If `k ≥ 64` (the `2^k` shift would be meaningless).
    pub const fn new(k: usize, expansion: u64, base: u64) -> Self {
        assert!(
            k < 64,
            "folding arity exponent beyond 63 is not addressable"
        );
        let bound = (1u64 << k).saturating_mul(expansion).saturating_mul(base);
        let planes = tree_eval::decomposition_planes(base, bound);
        Self {
            k,
            expansion,
            bound,
            planes,
            padded_planes: planes.next_power_of_two(),
        }
    }

    /// §2.2: "as long as `k > log log(B) + 1`, the folding cycle has made
    /// progress in reducing the size of the claim".
    pub const fn progresses(&self) -> bool {
        self.k > self.padded_planes.trailing_zeros() as usize + 1
    }

    /// The height after one cycle: `ℓ − k + 1 + ⌈log₂ h⌉` (Lemma 13's
    /// `PE(1, ℓ−k+1+log h, b)`).
    ///
    /// # Panics
    /// If the cycle would grow past `ℓ` (a caller that asked a non-progressing
    /// `k` for a short tree).
    pub const fn next_height(&self, height: usize) -> usize {
        let reduced = height - self.k;
        reduced + 1 + self.padded_planes.trailing_zeros() as usize
    }

    /// Layers removed per cycle; `0` when the cycle does not progress.
    pub const fn shrinks_by(&self) -> usize {
        let log_planes = self.padded_planes.trailing_zeros() as usize;
        if self.k > log_planes + 1 {
            self.k - 1 - log_planes
        } else {
            0
        }
    }
}

/// A tree evaluation claim: the statement `x = (t, u, v)` of `TE(1, ℓ, b)` /
/// `PE(1, ℓ, b)` (§5 "Relations").
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TreeClaim<R: Ring, const D: usize> {
    /// The committed root `t ∈ R_F^n`.
    pub t: Vec<PolyRing<R, D>>,
    /// The evaluation point: `ℓ + 1 + m` ring elements, `2^m = nα` for `TE`
    /// (`ℓ + m` for `PE`, whose claim is on the leaf layer only).
    pub u: Vec<PolyRing<R, D>>,
    /// The claimed value `v = s̃(u) ∈ R_F`.
    pub v: PolyRing<R, D>,
}

/// Eq. (15)'s sum-check circuit
///
/// ```text
/// G(X) = Σ_{j∈[2^k]} q̃_{subs,j}(X) · s̃_j(X)
/// ```
///
/// over the `2^{k+1}` multilinear oracles — the `q̃_{subs,j}` of Eq. (14) first,
/// then the subtree openings `s_j`. Each summand is a product of two
/// multilinears, so the round polynomial has degree `Δ = 2` and the message
/// width is `NC = 3`.
///
/// This is *not* a multilinear table sum-check and cannot be: at `NC = 1` the
/// protocol would end at `(x ↦ Σ_j q_j(x)s_j(x))̃(r)` instead of at
/// `Σ_j q̃_j(r)·s̃_j(r)`, and only the latter is what Step 2(c) sends and Eq. (17)
/// re-proves against `t_subs`. See [`crate::sumcheck::circuit`].
pub struct SubtreeCircuit<R: Ring + Display, const D: usize, const NC: usize> {
    /// `2^k`, the folding arity.
    arity: usize,
    _ring: core::marker::PhantomData<R>,
}

impl<R: Ring + Display, const D: usize, const NC: usize> SubtreeCircuit<R, D, NC> {
    /// The circuit over `2 · 2^k` oracles.
    pub fn new(arity: usize) -> Self {
        Self {
            arity,
            _ring: core::marker::PhantomData,
        }
    }
}

impl<R, const D: usize, const NC: usize> Composition<PolyRing<R, D>, NC>
    for SubtreeCircuit<R, D, NC>
where
    R: Ring + Display + MatrixElement,
{
    fn compose(
        &mut self,
        lines: &[LinePoly<PolyRing<R, D>, NC>],
        acc: &mut LinePoly<PolyRing<R, D>, NC>,
    ) -> Result<(), CircuitError> {
        if lines.len() != 2 * self.arity {
            return Err(CircuitError::WrongLength {
                got: lines.len(),
                expected: 2 * self.arity,
            });
        }
        for j in 0..self.arity {
            acc.add_assign(&lines[j].mul(&lines[self.arity + j])?);
        }
        Ok(())
    }
}

/// One folding round's messages (Protocol 4 Steps 1–3).
///
/// The `Display` bound is what lets the round carry a sum-check over `R_F`:
/// [`algebra`] implements [`MatrixElement`] for `PolyRing<R, D>` whenever
/// `R: Ring + Display`, and the folding sum-check's messages *are* ring elements
/// (§5.2.1 runs Eq. (15) over `R_F`, not over the field).
///
/// Note what is *not* a field here: `r` is derived by the verifier from the
/// transcript (Step 2(b)/(c): "P and V compute `r ← NTT⁻¹(h_K,…,h_K)`"), so it is
/// [`proof.sumcheck.point`](CircuitSumcheckProof::point) rather than a message,
/// and a prover cannot choose it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoldProof<R: Ring + Display, const D: usize, const NV: usize, const NC: usize> {
    /// `v_top = s̃_top(u_{(ℓ−k+1:)})` (Step 1(a)).
    pub v_top: PolyRing<R, D>,
    /// `v_subs` (Step 1(a), the claimed sum of Eq. 15).
    pub v_subs: PolyRing<R, D>,
    /// `y_subs`, Eq. (15)'s output evaluation (Step 2(c)).
    pub y_subs: PolyRing<R, D>,
    /// Step 2's `SC(v_subs, ℓ−k+1+m, Σ_j q̃_{subs,j}·s̃_j)` — Def. 9's degree-2
    /// sum-check. `sumcheck.point` is `r` and `sumcheck.final_eval` is `y_subs`.
    pub sumcheck: CircuitSumcheckProof<PolyRing<R, D>, NV, NC>,
    /// `(t_subs, (s_{subs,i}))`: the subtree-evaluation commitment (Eq. 16).
    pub subs: TreeOpening<R, D>,
    /// `t*`, the folded commitment (Step 3(b)).
    pub folded_root: Vec<PolyRing<R, D>>,
    /// `(s*_i)_{i∈[ℓ−k]}`, the folded openings (Eq. 11).
    pub folded_layers: Vec<Vec<PolyRing<R, D>>>,
    /// `v_bot = s̃_bot(r)` (Step 3(c)).
    pub v_bot: PolyRing<R, D>,
}

/// Domain label of the folding round's subtree sum-check.
pub const FOLD_DOMAIN: &[u8] = b"lattice-algebra/Z7/tree-fold";

/// Round-message width of Eq. (15)'s sum-check: `Δ + 1` with `Δ = 2`, because
/// every summand `q̃_{subs,j}(X)·s̃_j(X)` is a product of two multilinear oracles
/// (Def. 9, p. 17; Eq. (15), p. 31). This is a property of the protocol, not a
/// caller choice, so it is fixed here rather than passed in.
pub const FOLD_NC: usize = 3;

/// The `2^k` chunks of layer `k + inner` (Eq. 11's `s_{k+i,j}`), each
/// `2^inner·nα` long.
///
/// # Errors
/// [`FoldError::WrongLength`] if the layer is not `2^k · 2^inner · nα` wide.
pub fn chunks_of_layer<R: Ring, const D: usize>(
    layer: &[PolyRing<R, D>],
    slot_len: usize,
    k: usize,
    inner: usize,
) -> Result<Vec<&[PolyRing<R, D>]>, FoldError> {
    let size = (1usize << inner) * slot_len;
    if layer.len() != size << k {
        return Err(FoldError::WrongLength {
            got: layer.len(),
            expected: size << k,
        });
    }
    Ok(layer.chunks(size).collect())
}

/// `s_j = 0^{2nα} ‖ s_{k+1,j} ‖ … ‖ s_{ℓ,j}` (§5 "Commitment folding notation"):
/// the concatenated opening of subtree `j`.
///
/// # Errors
/// Propagates [`chunks_of_layer`].
pub fn subtree_vector<R: Ring, const D: usize>(
    slot_len: usize,
    layers: &[Vec<PolyRing<R, D>>],
    k: usize,
    j: usize,
) -> Result<Vec<PolyRing<R, D>>, FoldError> {
    let mut parts = Vec::with_capacity(layers.len() - k);
    for (inner, layer) in layers.iter().skip(k).enumerate() {
        parts.push(chunks_of_layer(layer, slot_len, k, inner + 1)?[j].to_vec());
    }
    Ok(tree_eval::concatenated(slot_len, &parts))
}

/// The weights `q_{subs,j}` of Eq. (14).
///
/// # Errors
/// [`FoldError::WrongLength`] if `u` is not `ℓ + 1 + m` long.
pub fn subtree_weights<R: Ring, const D: usize>(
    slot_len: usize,
    height: usize,
    k: usize,
    j: usize,
    u: &[PolyRing<R, D>],
) -> Result<Vec<PolyRing<R, D>>, FoldError> {
    let m = slot_len.trailing_zeros() as usize;
    if u.len() != height + 1 + m {
        return Err(FoldError::WrongLength {
            got: u.len(),
            expected: height + 1 + m,
        });
    }
    let mut parts = Vec::with_capacity(height - k);
    for i in 1..=height - k {
        // e_{i,j} = êq(0^{ℓ−(k+i)} ‖ 1 ‖ bits_k(j), u_{(:ℓ−i+1)})
        let mut prefix: Vec<bool> = vec![false; height - k - i];
        prefix.push(true);
        prefix.extend(bits_of(j, k));
        let weight = eq_of_bits_point(&prefix, &u[..prefix.len()])?;
        // f_i = êq(u_{(ℓ−i+2:)}, ·) over the last i + m coordinates.
        let tail = &u[u.len() - (i + m)..];
        let table = eq_ring_table(tail, (1usize << i) * slot_len)?;
        parts.push(
            table
                .iter()
                .map(|entry| entry.clone() * weight.clone())
                .collect::<Vec<_>>(),
        );
    }
    Ok(tree_eval::concatenated(slot_len, &parts))
}

/// `q̃_{subs,j}(r)`, computed by both sides from one code path (the paper notes
/// the verifier can do this itself in `O(ℓ² + ℓm)`).
///
/// # Errors
/// Propagates [`subtree_weights`] and the MLE's shape checks.
pub fn subtree_weights_at_point<R: Ring, const D: usize>(
    slot_len: usize,
    height: usize,
    k: usize,
    j: usize,
    u: &[PolyRing<R, D>],
    r: &[PolyRing<R, D>],
) -> Result<PolyRing<R, D>, FoldError> {
    let weights = subtree_weights(slot_len, height, k, j, u)?;
    Ok(tree_eval::mle_at_ring(&weights, r)?)
}

/// Eq. (12)'s factor `êq(0^{ℓ−k}, u_{(:ℓ−k)})`.
pub fn top_claim_factor<R: Ring, const D: usize>(
    height: usize,
    k: usize,
    u: &[PolyRing<R, D>],
) -> Result<PolyRing<R, D>, FoldError> {
    let zeros = vec![false; height - k];
    Ok(eq_of_bits_point(&zeros, &u[..height - k])?)
}

/// Π^Fold prover: Protocol 4 Steps 1–3, returning the proof together with the
/// three output claims (top / folded bottom / subtree) and their witnesses.
/// Eq. (15) runs as Def. 9's degree-2 sum-check with the fixed width
/// [`FOLD_NC`].
///
/// # Errors
/// [`FoldError::HeightTooSmall`], [`FoldError::WrongLength`],
/// [`FoldError::SplitClaimMismatch`], [`FoldError::SubtreeWeightsMismatch`],
/// [`FoldError::SumcheckRejected`], [`FoldError::NormGrowth`],
/// [`FoldError::Tree`], [`FoldError::Eval`].
#[allow(clippy::too_many_arguments)]
pub fn fold_prove<R, const D: usize, const BASE: u64, const ALPHA: usize, const NV: usize>(
    key: &TreeKey<R, D, BASE, ALPHA>,
    claim: &TreeClaim<R, D>,
    layers: &[Vec<PolyRing<R, D>>],
    k: usize,
    challenges: &[PolyRing<R, D>],
    shape: &CycleShape,
    binding: &[u8],
) -> Result<(FoldProof<R, D, NV, FOLD_NC>, TreeClaim<R, D>, TreeClaim<R, D>), FoldError>
where
    R: Ring + CenteredRing + Display + MatrixElement,
{
    let slot = key.slot_len();
    let height = layers.len();
    let m = slot.trailing_zeros() as usize;
    if height <= k {
        return Err(FoldError::HeightTooSmall { height, k });
    }
    if challenges.len() != 1usize << k {
        return Err(FoldError::WrongLength {
            got: challenges.len(),
            expected: 1usize << k,
        });
    }
    if claim.u.len() != height + 1 + m {
        return Err(FoldError::WrongLength {
            got: claim.u.len(),
            expected: height + 1 + m,
        });
    }
    let s = tree_eval::concatenated(slot, layers);
    let full_table = eq_ring_table(&claim.u, s.len())?;
    // Step 1(a): the split claims on s_top and on the bottom index range.
    let top_layers: Vec<Vec<PolyRing<R, D>>> = layers.iter().take(k).cloned().collect();
    let s_top = tree_eval::concatenated(slot, &top_layers);
    let tail = claim.u[height - k..].to_vec();
    let v_top = tree_eval::mle_at_ring(&s_top, &tail)?;
    let mut v_subs = zero_ring::<R, D>();
    for (index, weight) in full_table
        .iter()
        .enumerate()
        .skip((1usize << (k + 1)) * slot)
    {
        v_subs = v_subs + weight.clone() * s[index].clone();
    }
    // Step 1(b): a prover lying about the split is caught here.
    check_split(claim, layers, k, &v_top, &v_subs)?;
    // Step 2: Eq. (15) as Def. 9's degree-2 sum-check over the 2^{k+1} oracles
    // `q̃_{subs,j}` (Eq. 14) and `s̃_j`.
    let arity = challenges.len();
    let mut weight_tables: Vec<Vec<PolyRing<R, D>>> = Vec::with_capacity(arity);
    let mut subtree_tables: Vec<Vec<PolyRing<R, D>>> = Vec::with_capacity(arity);
    for j in 0..arity {
        subtree_tables.push(subtree_vector(slot, layers, k, j)?);
        weight_tables.push(subtree_weights(slot, height, k, j, &claim.u)?);
    }
    let oracles: Vec<&[PolyRing<R, D>]> = weight_tables
        .iter()
        .chain(subtree_tables.iter())
        .map(|table| table.as_slice())
        .collect();
    let mut circuit = SubtreeCircuit::<R, D, FOLD_NC>::new(arity);
    let sumcheck = circuit::prove::<PolyRing<R, D>, NV, FOLD_NC, _>(
        &oracles,
        &v_subs,
        FOLD_DOMAIN,
        binding,
        &mut circuit,
    )
    .map_err(|error| match error {
        CircuitError::WrongLength { got, expected } => FoldError::WrongLength { got, expected },
        CircuitError::DegreeOverflow { degree, declared } => {
            FoldError::DegreeUnderstated { degree, declared }
        }
        CircuitError::ClaimMismatch => FoldError::SubtreeWeightsMismatch,
        CircuitError::WrongRounds { .. }
        | CircuitError::RoundRejected { .. }
        | CircuitError::FinalMismatch => FoldError::SumcheckRejected,
    })?;
    let r = sumcheck.point.clone();
    let y_subs = sumcheck.final_eval.clone();
    // Step 2(c): `f_subs := s̃_1(r) ‖ … ‖ s̃_{2^k}(r) ‖ 0^{2^k(n−1)}` (Eq. 16,
    // p. 31) — the subtree evaluations first and the zero rows *after* them, so
    // that Eq. (17)/(18)'s `êq(X, 0^{log n} ‖ bits_k(j−1))` selector, which reads
    // the row bits as the leading ones, lands on subtree `j`.
    let mut f_subs: Vec<PolyRing<R, D>> = Vec::with_capacity(arity * key.rows());
    // The same `êq(r, ·)` table serves every subtree and the folded
    // concatenation below — see [`tree_eval::EqTables`].
    let mut at_r = tree_eval::EqTables::at(&r);
    for s_j in &subtree_tables {
        f_subs.push(at_r.mle(s_j)?);
    }
    f_subs.resize(arity * key.rows(), zero_ring::<R, D>());
    let subs = key.commit(&f_subs)?;
    // Step 3: fold (Eq. 11) and gate the norm growth.
    let children = chunks_of_layer(&layers[k - 1], slot, k, 0)?;
    let mut folded_root = vec![zero_ring::<R, D>(); key.rows()];
    for (c, child) in challenges.iter().zip(children.iter()) {
        let values = key.recompose(child);
        for (acc, value) in folded_root.iter_mut().zip(values.iter()) {
            *acc = acc.clone() + c.clone() * value.clone();
        }
    }
    let folded_layers = fold_layers(slot, layers, k, challenges)?;
    let got = folded_layers
        .iter()
        .map(|layer| tree_commit::max_norm(layer))
        .max()
        .unwrap_or(0);
    if got > shape.bound {
        return Err(FoldError::NormGrowth {
            got,
            bound: shape.bound,
        });
    }
    let s_bot = tree_eval::concatenated(slot, &folded_layers);
    let v_bot = at_r.mle(&s_bot)?;
    let top_claim = TreeClaim {
        t: claim.t.clone(),
        u: tail,
        v: v_top.clone(),
    };
    let bottom_claim = TreeClaim {
        t: folded_root.clone(),
        u: r.clone(),
        v: v_bot.clone(),
    };
    let proof = FoldProof {
        v_top,
        v_subs,
        y_subs,
        sumcheck,
        subs,
        folded_root,
        folded_layers,
        v_bot,
    };
    Ok((proof, top_claim, bottom_claim))
}

/// Eq. (11)'s folded openings `s*_i = Σ_j c_j·s_{k+i,j}`, for `i ∈ [ℓ−k]`.
///
/// # Errors
/// Propagates [`chunks_of_layer`].
pub fn fold_layers<R: Ring, const D: usize>(
    slot_len: usize,
    layers: &[Vec<PolyRing<R, D>>],
    k: usize,
    challenges: &[PolyRing<R, D>],
) -> Result<Vec<Vec<PolyRing<R, D>>>, FoldError> {
    let mut out = Vec::with_capacity(layers.len().saturating_sub(k));
    for inner in 1..=layers.len().saturating_sub(k) {
        let parts = chunks_of_layer(&layers[k - 1 + inner], slot_len, k, inner)?;
        let mut acc = vec![zero_ring::<R, D>(); (1usize << inner) * slot_len];
        for (c, part) in challenges.iter().zip(parts.iter()) {
            for (slot_index, value) in acc.iter_mut().zip(part.iter()) {
                *slot_index = slot_index.clone() + c.clone() * value.clone();
            }
        }
        out.push(acc);
    }
    Ok(out)
}

/// Protocol 4 Step 1(b), the one equation both sides must agree on before
/// anything else is believed:
/// `v = êq(0^{ℓ−k}, u_{(:ℓ−k)})·v_top + v_subs`.
///
/// # Errors
/// [`FoldError::SplitClaimMismatch`].
pub fn check_split<R: Ring, const D: usize>(
    claim: &TreeClaim<R, D>,
    layers: &[Vec<PolyRing<R, D>>],
    k: usize,
    v_top: &PolyRing<R, D>,
    v_subs: &PolyRing<R, D>,
) -> Result<(), FoldError> {
    let height = layers.len();
    if height <= k {
        return Err(FoldError::HeightTooSmall { height, k });
    }
    let factor = top_claim_factor(height, k, &claim.u)?;
    if factor * v_top.clone() + v_subs.clone() != claim.v {
        return Err(FoldError::SplitClaimMismatch);
    }
    Ok(())
}

/// **Every** verifier-side equation of Protocol 4, evaluated rather than taken
/// up to the first failure. An empty vector is an accepted round.
///
/// Checks, in protocol order:
/// 1. the input opening really opens (Def. 19 `Open`, so the fold starts from a
///    member of `TE`);
/// 2. shapes: arity, the `TE` point's `ℓ+1+m` coordinates, `t_subs`'s layer
///    count, and the folded opening's layer count;
/// 3. Step 1(b) Eq. (12) — the split of the evaluation claim;
/// 4. Eq. (14)/(15) — `v_subs` is also `Σ_j ⟨q_{subs,j}, s_j⟩`, the identity the
///    sum-check is *about*;
/// 5. Step 2 — the degree-2 sum-check of Def. 9, and that the carried `y_subs`
///    *is* its output claim `G(r)`;
/// 6. Eq. (17) — each `s̃_j(r)` is the slot of `t_subs` it claims to be, and
///    `y_subs = Σ_j q̃_{subs,j}(r)·s̃_j(r)` through those slots;
/// 7. that `t_subs` itself opens at the gadget bound;
/// 8. Eq. (11) `t* = Σ_j c_j·G_n·s_{k,j}`, its powers-batched form Eq. (19), and
///    each folded layer `s*_i = Σ_j c_j·s_{k+i,j}`;
/// 9. Protocol 4's norm gate `‖s*‖∞ ≤ B = 2^k·T·b`;
/// 10. Eq. (18) `v_bot = s̃_bot(r)`.
///
/// # Errors
/// See [`FoldError`]; each variant names the equation that owns it.
#[allow(clippy::too_many_arguments)]
pub fn fold_report<R, const D: usize, const BASE: u64, const ALPHA: usize, const NV: usize>(
    key: &TreeKey<R, D, BASE, ALPHA>,
    claim: &TreeClaim<R, D>,
    layers: &[Vec<PolyRing<R, D>>],
    proof: &FoldProof<R, D, NV, FOLD_NC>,
    k: usize,
    challenges: &[PolyRing<R, D>],
    binding: &[u8],
    shape: &CycleShape,
    eta: R,
) -> Vec<FoldError>
where
    R: Ring + CenteredRing + Display + MatrixElement,
{
    let mut bad: Vec<FoldError> = Vec::new();
    let mut push = |error: FoldError| {
        if !bad.contains(&error) {
            bad.push(error);
        }
    };
    let slot = key.slot_len();
    let height = layers.len();
    let m = slot.trailing_zeros() as usize;
    let opening = TreeOpening {
        root: claim.t.clone(),
        layers: layers.to_vec(),
    };
    // 1. Def. 19's `Open` on the witness the fold is applied to.
    if let Err(err) = key.open(&opening, BASE) {
        push(FoldError::Tree(err));
    }
    // 2. shapes. Everything below indexes `layers` by `k` or inner-products a
    //    weight against a subtree, so a mismatch here makes the rest unevaluable.
    if height <= k {
        push(FoldError::HeightTooSmall { height, k });
        return bad;
    }
    if challenges.len() != 1usize << k {
        push(FoldError::WrongLength {
            got: challenges.len(),
            expected: 1usize << k,
        });
    }
    if claim.u.len() != height + 1 + m {
        push(FoldError::WrongLength {
            got: claim.u.len(),
            expected: height + 1 + m,
        });
    }
    if proof.subs.layers.len() != k {
        push(FoldError::WrongLength {
            got: proof.subs.layers.len(),
            expected: k,
        });
    }
    if proof.folded_layers.len() != height - k {
        push(FoldError::WrongLength {
            got: proof.folded_layers.len(),
            expected: height - k,
        });
    }
    if challenges.len() != 1usize << k || claim.u.len() != height + 1 + m {
        return bad;
    }
    // 3. Eq. (12).
    if let Err(err) = check_split(claim, layers, k, &proof.v_top, &proof.v_subs) {
        push(err);
    }
    // 4. Eq. (15)'s claimed sum, by the weights' own inner products, and 6. the
    //    subtree evaluations read out of `t_subs` (Eq. 17).
    let r = proof.sumcheck.point.clone();
    let bottom = proof.subs.layers.get(k - 1);
    let mut by_weights = zero_ring::<R, D>();
    let mut y_check = zero_ring::<R, D>();
    let mut slots_ok = true;
    // `s̃_j(r)` and `q̃_{subs,j}(r)` share one `êq(r, ·)` table across the whole
    // `2^k`-subtree loop: rebuilding it per subtree is `2^k` times the ring
    // products the paper's verifier cost allows (§2.2.2, p. 8).
    let mut at_r = tree_eval::EqTables::at(&r);
    for j in 0..challenges.len() {
        let s_j = match subtree_vector(slot, layers, k, j) {
            Ok(vector) => vector,
            Err(err) => {
                push(err);
                return bad;
            }
        };
        let q_j = match subtree_weights(slot, height, k, j, &claim.u) {
            Ok(weights) => weights,
            Err(err) => {
                push(err);
                return bad;
            }
        };
        by_weights = by_weights + tree_eval::inner_product(&q_j, &s_j);
        let evaluation = match at_r.mle(&s_j) {
            Ok(value) => value,
            Err(err) => {
                push(FoldError::Eval(err));
                slots_ok = false;
                continue;
            }
        };
        // Eq. (16)/(17): subtree `j`'s evaluation is the `j`th *ring element* of
        // `f_subs`, i.e. `ALPHA` digits at offset `j·α` of the bottom digit layer
        // `s_{subs,k}` — the row bits lead, so the zero rows sit after the values.
        let slot_digits = bottom.and_then(|layer| layer.get(j * ALPHA..(j + 1) * ALPHA));
        match slot_digits {
            Some(digits) if key.recompose(digits).first() == Some(&evaluation) => {}
            Some(_) => push(FoldError::SubtreeCommitmentMismatch { subtree: j }),
            None => {
                push(FoldError::WrongLength {
                    got: bottom.map_or(0, |layer| layer.len()),
                    expected: (j + 1) * ALPHA,
                });
                slots_ok = false;
            }
        }
        match at_r.mle(&q_j) {
            Ok(weight) => y_check = y_check + weight * evaluation,
            Err(err) => {
                push(FoldError::Eval(err));
                slots_ok = false;
            }
        }
    }
    if by_weights != proof.v_subs {
        push(FoldError::SubtreeWeightsMismatch);
    }
    // 5. Step 2: Def. 9's degree-2 sum-check of Eq. (15) against `v_subs`.
    match circuit::verify::<PolyRing<R, D>, NV, FOLD_NC>(
        &proof.sumcheck,
        &proof.v_subs,
        FOLD_DOMAIN,
        binding,
    ) {
        Err(CircuitError::WrongLength { got, expected }) => {
            push(FoldError::WrongLength { got, expected })
        }
        Err(CircuitError::DegreeOverflow { degree, declared }) => {
            push(FoldError::DegreeUnderstated { degree, declared })
        }
        Err(CircuitError::ClaimMismatch) => push(FoldError::SubtreeWeightsMismatch),
        Err(_) => push(FoldError::SumcheckRejected),
        Ok((_, final_eval)) => {
            if final_eval != proof.y_subs {
                push(FoldError::SubtreeEvaluationMismatch);
            }
        }
    }
    // 6. `y_subs` re-proved through the committed slots.
    if slots_ok && y_check != proof.y_subs {
        push(FoldError::SubtreeEvaluationMismatch);
    }
    // 7. the subtree commitment opens.
    if let Err(err) = key.open(&proof.subs, BASE) {
        push(FoldError::SubtreeCommitInvalid(err));
    }
    // 8. Eq. (11) and its batched form Eq. (19).
    let children = match chunks_of_layer(layers.get(k - 1).map_or([].as_slice(), |l| l.as_slice()), slot, k, 0) {
        Ok(children) => children,
        Err(err) => {
            push(err);
            return bad;
        }
    };
    let mut expect_root = vec![zero_ring::<R, D>(); key.rows()];
    for (c, child) in challenges.iter().zip(children.iter()) {
        let values = key.recompose(child);
        for (acc, value) in expect_root.iter_mut().zip(values.iter()) {
            *acc = acc.clone() + c.clone() * value.clone();
        }
    }
    if expect_root != proof.folded_root {
        push(FoldError::FoldedCommitmentMismatch);
    }
    // Eq. (19): ⟨p_η,n, t*⟩ = Σ_j c_j·⟨p_η,n ⊗ p_{b,α}, s_{k,j}⟩, using the
    // paper's observation g_b^⊺ = p_{b,α}. Both sides are field-weighted, so the
    // weights are scalars and the products are `scalar_inner_product`s.
    let row_weights = tree_eval::powers_vector(eta, key.rows());
    let digit_weights = tree_eval::powers_vector(R::from(BASE), ALPHA);
    let batch_weights = tree_eval::tensor(&row_weights, &digit_weights);
    let lhs = tree_eval::scalar_inner_product(&row_weights, &proof.folded_root);
    let mut rhs = zero_ring::<R, D>();
    for (c, child) in challenges.iter().zip(children.iter()) {
        rhs = rhs + c.clone() * tree_eval::scalar_inner_product(&batch_weights, child);
    }
    if lhs != rhs {
        push(FoldError::FoldedCommitmentBatchMismatch);
    }
    match fold_layers(slot, layers, k, challenges) {
        Ok(expect_layers) => {
            for (inner, (expect, got)) in expect_layers
                .iter()
                .zip(proof.folded_layers.iter())
                .enumerate()
            {
                if expect != got {
                    push(FoldError::FoldedLayerMismatch { level: inner + 1 });
                }
            }
        }
        Err(err) => push(err),
    }
    // 9. the norm gate ‖s*‖∞ ≤ B = 2^k·T·b.
    let got = proof
        .folded_layers
        .iter()
        .map(|layer| tree_commit::max_norm(layer))
        .max()
        .unwrap_or(0);
    if got > shape.bound {
        push(FoldError::NormGrowth {
            got,
            bound: shape.bound,
        });
    }
    // 10. Eq. (18): v_bot is the folded concatenation's own evaluation.
    let s_bot = tree_eval::concatenated(slot, &proof.folded_layers);
    match at_r.mle(&s_bot) {
        Ok(value) => {
            if value != proof.v_bot {
                push(FoldError::FoldedEvaluationMismatch);
            }
        }
        Err(err) => push(FoldError::Eval(err)),
    }
    bad
}

/// Π^Fold verifier: [`fold_report`] followed by "take the first", which is all a
/// verifier needs.
///
/// # Errors
/// The first entry of [`fold_report`]; see it for the full list.
#[allow(clippy::too_many_arguments)]
pub fn fold_verify<R, const D: usize, const BASE: u64, const ALPHA: usize, const NV: usize>(
    key: &TreeKey<R, D, BASE, ALPHA>,
    claim: &TreeClaim<R, D>,
    layers: &[Vec<PolyRing<R, D>>],
    proof: &FoldProof<R, D, NV, FOLD_NC>,
    k: usize,
    challenges: &[PolyRing<R, D>],
    binding: &[u8],
    shape: &CycleShape,
    eta: R,
) -> Result<(), FoldError>
where
    R: Ring + CenteredRing + Display + MatrixElement,
{
    fold_report(key, claim, layers, proof, k, challenges, binding, shape, eta)
        .into_iter()
        .next()
        .map_or(Ok(()), Err)
}

/// The number of ring elements one folding round puts on the wire, for §6.2's
/// proof-size accounting: the two split claims, `y_subs`, the degree-2
/// sum-check's `NC` coefficients per round, `t_subs`, `t*`, and `v_bot`. The
/// challenge point `r` is *derived*, not sent. (Nor are the folded openings:
/// they are the witness the reduction forwards, which is the whole reason no
/// authentication path appears anywhere in the scheme.)
pub fn wire_size<R: Ring + Display, const D: usize, const NV: usize>(
    proof: &FoldProof<R, D, NV, FOLD_NC>,
) -> usize {
    3 + FOLD_NC * proof.sumcheck.rounds.len()
        + proof.subs.root.len()
        + proof.folded_root.len()
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    /// P3's field size: prime, `≡ 5 (mod 8)`, so `q − 1` has 2-adicity 2 and **no
    /// NTT of degree ≥ 4 exists** — every ring element product below is
    /// schoolbook, which is the point of the instance.
    type F = Zq<4294967197>;
    const D: usize = 8;
    const ALPHA: usize = 32;
    const K: usize = 2;
    const HEIGHT: usize = 3;
    /// Variables of Eq. (15)'s sum-check: (ℓ − k + 1) + m, m = log₂(nα) = 6.
    const NV: usize = HEIGHT - K + 1 + 6;
    /// Round-message width of Def. 9's degree-2 sum-check: `Δ + 1` with `Δ = 2`
    /// because Eq. (15)'s summand is a product of two multilinear oracles.
    const NC: usize = 3;

    type Key = TreeKey<F, D, 2, ALPHA>;
    type Proof = FoldProof<F, D, NV, NC>;

    fn key() -> Key {
        Key::setup(&[0x42u8; 32], 2)
    }

    fn poly_vec(len: usize) -> Vec<PolyRing<F, D>> {
        (0..len)
            .map(|i| {
                PolyRing::from_coefficients(
                    (0..D)
                        .map(|j| F::from(((i * 977 + j * 31) % 1009) as u64))
                        .collect(),
                )
            })
            .collect()
    }

    /// A committed tree, its TE claim at a random point, and the folding
    /// challenges the round consumes.
    fn instance() -> (
        Key,
        TreeClaim<F, D>,
        Vec<Vec<PolyRing<F, D>>>,
        Vec<PolyRing<F, D>>,
    ) {
        let key = key();
        let f = poly_vec((1usize << HEIGHT) * key.rows());
        let opening = key.commit(&f).expect("a height-3 tree");
        let slot = key.slot_len();
        let u = poly_vec(HEIGHT + 1 + slot.trailing_zeros() as usize);
        let s = tree_eval::concatenated(slot, &opening.layers);
        let v = tree_eval::mle_at_ring(&s, &u).expect("TE claim");
        let claim = TreeClaim {
            t: opening.root.clone(),
            u,
            v,
        };
        let challenges: Vec<PolyRing<F, D>> = (0..1usize << K)
            .map(|j| ChallengeSet::DenseTernary.sample(&[0x77u8; 32], j as u64))
            .collect();
        (key, claim, opening.layers, challenges)
    }

    fn shape() -> CycleShape {
        CycleShape::new(K, ChallengeSet::DenseTernary.expansion_factor(D), 2)
    }

    #[test]
    fn figure_5_challenge_set_sizes_are_reproduced_in_integers() {
        // Fig. 5 (p. 46) prints `log₂|C|` rounded to *nearest*: `101` for Cter at
        // d = 64 (log₂ 3⁶⁴ = 101.44) but `203` at d = 128 (202.88), and `124` for
        // C_sp(32,8) (123.99). No ceiling or floor gives all three, and `3^128`
        // does not fit a machine integer — which is what `log2_size` now handles.
        let sp = ChallengeSet::Sparse { tau1: 32, tau2: 8 };
        assert_eq!(sp.log2_size(64), 124, "P1/P3/P7's challenge set");
        assert_eq!(ChallengeSet::DenseTernary.log2_size(64), 101, "P2/P4");
        assert_eq!(
            ChallengeSet::DenseTernary.log2_size(128),
            203,
            "P5/P9's d = 128 — 3^128 ≈ 2^203 overflows u128"
        );
        // The windowed path must not drift for a set that does fit exactly.
        assert_eq!(ChallengeSet::DenseTernary.log2_size(32), 51);
        assert_eq!(ChallengeSet::DenseTernary.log2_size(16), 25);
        // Thm 3 / Thm 4's expansion factors.
        assert_eq!(sp.expansion_factor(64), 48);
        assert_eq!(ChallengeSet::DenseTernary.expansion_factor(64), 64);
        assert_eq!(sp.difference_norm(), 4);
        assert_eq!(ChallengeSet::DenseTernary.difference_norm(), 2);
    }

    #[test]
    fn theorem_2_decides_the_heuristic_column_without_floats() {
        let sp = ChallengeSet::Sparse { tau1: 32, tau2: 8 };
        let ter = ChallengeSet::DenseTernary;
        // P3 (d=64, e=8): deterministic, so Fig. 5 writes "no (Thm. 2)".
        assert!(sp.deterministically_invertible(4_294_967_197, 64, 8));
        assert!(ter.deterministically_invertible(4_294_967_197, 64, 8));
        // P2 (d=64, e=4): not deterministic — Fig. 5 writes "yes (Lem. 7)".
        assert!(!ter.deterministically_invertible(4_294_967_197, 64, 4));
        assert!(!sp.deterministically_invertible(4_294_967_197, 64, 4));
        // P5 (d=128, e=4) also needs the heuristic; a non-dividing e is refused.
        assert!(!ter.deterministically_invertible(4_294_967_197, 128, 4));
        assert!(!ter.deterministically_invertible(4_294_967_197, 64, 5));
    }

    #[test]
    fn sampled_challenges_are_in_the_set_and_obey_the_expansion_bound() {
        // Def. 14's shape: exactly τ₁ coefficients at ±1, τ₂ at ±2, rest zero —
        // and Theorem 4's ‖c‖∞ ≤ τ₁ + 2τ₂ applied to v = 1.
        //
        // The count runs over all `D` coefficients by index, not over
        // `coefficients()`: that accessor trims trailing zeros, so a challenge
        // whose top coefficient happens to be 0 would report one zero too few.
        let sp = ChallengeSet::Sparse { tau1: 3, tau2: 2 };
        for index in 0..6u64 {
            let c: PolyRing<F, D> = sp.sample(&[0x11u8; 32], index);
            let mut ones = 0;
            let mut twos = 0;
            for slot in 0..D {
                match tree_eval::coefficient_at(&c, slot).abs_infinity() {
                    0 => {}
                    1 => ones += 1,
                    2 => twos += 1,
                    other => panic!("a C_sp challenge coefficient of magnitude {other}"),
                }
            }
            assert_eq!(
                (ones, twos, D - ones - twos),
                (3, 2, D - 5),
                "index {index} must carry exactly τ₁ unit and τ₂ double coefficients, got {c:?}"
            );
            let other: PolyRing<F, D> = sp.sample(&[0x11u8; 32], index + 100);
            assert_ne!(c, other, "the index must reseed the draw");
        }
        // Def. 11: dense ternary, every coefficient in {−1,0,1}.
        let ter = ChallengeSet::DenseTernary;
        let c: PolyRing<F, D> = ter.sample(&[0x22u8; 32], 0);
        assert!(
            c.coefficients().iter().all(|x| x.abs_infinity() <= 1),
            "Cter coefficients are ternary"
        );
    }

    #[test]
    fn cycle_shape_reproduces_p3_and_detects_a_non_progressing_k() {
        // P3: b = 2, C = C_sp(32,8) ⇒ T = 48, k = 7 ⇒ B = 2^7·48·2 = 12288,
        // h = log₂ B = 14, so each cycle shortens the tree by 2 layers.
        let p3 = CycleShape::new(7, 48, 2);
        assert_eq!(p3.bound, 12_288);
        assert_eq!(p3.planes, 14);
        assert_eq!(p3.padded_planes, 16);
        assert!(p3.progresses());
        assert_eq!(p3.shrinks_by(), 2);
        assert_eq!(p3.next_height(25), 23, "Lemma 13's ℓ − k + 1 + log h");
        assert_eq!(p3.next_height(9), 7);
        // CMNW's regime: a small k with the same T makes the cycle grow.
        let stuck = CycleShape::new(3, 48, 2);
        assert!(!stuck.progresses());
        assert_eq!(stuck.shrinks_by(), 0);
        assert!(
            stuck.next_height(9) > 9,
            "the claim got longer, not shorter"
        );
        // The threshold between the two is exactly k > log h + 1.
        assert!(CycleShape::new(6, 48, 2).progresses());
        assert!(!CycleShape::new(5, 48, 2).progresses());
    }

    #[test]
    fn the_layer_split_is_the_same_number_by_both_routes() {
        // Eq. (12) vs Eq. (14)/(15): v_subs computed as the bottom index range of
        // the concatenated MLE must equal Σ_j ⟨q_subs,j, s_j⟩. Two independent
        // computations of the same quantity — the layout test of the module.
        let (key, claim, layers, _) = instance();
        let slot = key.slot_len();
        let s = tree_eval::concatenated(slot, &layers);
        let table = eq_ring_table(&claim.u, s.len()).expect("shape ok");
        let start = (1usize << (K + 1)) * slot;
        let direct: PolyRing<F, D> = table
            .iter()
            .enumerate()
            .skip(start)
            .map(|(i, w)| w.clone() * s[i].clone())
            .sum();
        let mut by_weights: PolyRing<F, D> = zero_ring();
        for j in 0..(1usize << K) {
            let s_j = subtree_vector(slot, &layers, K, j).expect("subtree");
            let q_j = subtree_weights(slot, HEIGHT, K, j, &claim.u).expect("weights");
            assert_eq!(
                s_j.len(),
                q_j.len(),
                "q_subs,j and s_j are claimed against each other"
            );
            by_weights = by_weights + tree_eval::inner_product(&q_j, &s_j);
        }
        assert_eq!(direct, by_weights);
        // …and the top factor closes the whole claim.
        let top_layers: Vec<Vec<PolyRing<F, D>>> = layers.iter().take(K).cloned().collect();
        let s_top = tree_eval::concatenated(slot, &top_layers);
        let v_top = tree_eval::mle_at_ring(&s_top, &claim.u[HEIGHT - K..]).expect("top mle");
        let factor = top_claim_factor(HEIGHT, K, &claim.u).expect("factor");
        assert_eq!(factor * v_top + by_weights, claim.v);
    }

    /// **Is Protocol 4's Eq. (18) checked here?** Not by its own name, and this
    /// test is why that is acceptable rather than a hole. The paper prints (18) as
    /// a sum-check over `t_subs`'s own digit layer
    /// `v_bot = Σ_{X_k,Y,X_g} c̃(X_k)·êq(Y,0^{log n})·ẽp_{b,α}(X_g)·s̃_{subs,k}(Y,X_k,X_g)`
    /// (p. 31), while step 10 of [`fold_report`] checks the *other* reading the
    /// same page states — "Observe that this is also an evaluation claim on
    /// `v_bot = s̃_bot(r)`" — against the folded concatenation. The two are one
    /// number **only because** step 6 pins every `t_subs` slot to `s̃_j(r)` (that is
    /// Eq. (17), row 0 of the `g_b^⊺` recomposition) and step 8 pins each folded
    /// layer to `Σ_j c_j·s_{k+i,j}` (Eq. 11). So the check below is an
    /// *implication test*: it fails the moment either leg is dropped, which is
    /// exactly what a future refactor of `fold_report` could do silently.
    #[test]
    fn eq_18_and_the_folded_reading_are_one_number_only_via_eq_17_and_11() {
        let (key, claim, layers, challenges) = instance();
        let binding = b"eq18-route".to_vec();
        let (proof, _, _): (Proof, _, _) = fold_prove::<F, D, 2, ALPHA, NV>(
            &key,
            &claim,
            &layers,
            K,
            &challenges,
            &shape(),
            &binding,
        )
        .expect("honest fold");
        let slot = key.slot_len();
        // Eq. (18)'s own route: c̃ at the hypercube vertices is `c_j`, and
        // Σ_{X_g} ẽp_{b,α}(X_g)·(·) over the digit block *is* `key.recompose`,
        // whose row 0 is what êq(Y, 0^{log n}) selects.
        let route_subs = |proof: &Proof| -> PolyRing<F, D> {
            let bottom = proof.subs.layers.get(K - 1).expect("k layers");
            challenges
                .iter()
                .enumerate()
                .map(|(j, c)| {
                    let digits = bottom
                        .get(j * ALPHA..(j + 1) * ALPHA)
                        .expect("one α-wide slot per subtree");
                    c.clone() * key.recompose(digits)[0].clone()
                })
                .sum()
        };
        let s_bot = tree_eval::concatenated(slot, &proof.folded_layers);
        let route_folded =
            tree_eval::mle_at_ring(&s_bot, &proof.sumcheck.point).expect("folded mle");
        assert_eq!(route_subs(&proof), route_folded);
        assert_eq!(
            route_folded, proof.v_bot,
            "and both readings are the claim the proof carries"
        );

        // Negative control: the equality is earned, not structural. Move one digit
        // of `t_subs`'s opening and Eq. (18)'s route leaves the folded reading…
        let mut forged = proof.clone();
        forged.subs.layers[K - 1][0] =
            forged.subs.layers[K - 1][0].clone() + tree_eval::embed::<F, D>(F::ONE);
        assert_ne!(
            route_subs(&forged),
            route_folded,
            "the two routes must be sensitive to t_subs's digits"
        );
        // …and the leg that supplies that sensitivity is Eq. (17)'s per-slot
        // read-out — the slot's recomposition no longer equals the `s̃_j(r)` the
        // proof carries — which `fold_report` really does run.
        let errors = fold_report::<F, D, 2, ALPHA, NV>(
            &key,
            &claim,
            &layers,
            &forged,
            K,
            &challenges,
            &binding,
            &shape(),
            F::from(12_345u64),
        );
        assert!(
            errors.contains(&FoldError::SubtreeCommitmentMismatch { subtree: 0 }),
            "Eq. (17)'s slot read-out is what stands in for Eq. (18); it must fire: {errors:?}"
        );
    }

    #[test]
    fn honest_fold_proves_and_verifies() {
        let (key, claim, layers, challenges) = instance();
        let binding = b"fold-test".to_vec();
        let (proof, top_claim, bottom_claim): (Proof, _, _) = fold_prove::<F, D, 2, ALPHA, NV>(
            &key,
            &claim,
            &layers,
            K,
            &challenges,
            &shape(),
            &binding,
        )
        .expect("honest fold");
        let eta = F::from(12_345u64);
        fold_verify::<F, D, 2, ALPHA, NV>(
            &key,
            &claim,
            &layers,
            &proof,
            K,
            &challenges,
            &binding,
            &shape(),
            eta,
        )
        .expect("every equation of Protocol 4 holds");
        // Non-short-circuiting: every check fires *empty*, i.e. each equation
        // holds simultaneously rather than being hidden behind an earlier one.
        assert_eq!(
            fold_report(&key, &claim, &layers, &proof, K, &challenges, &binding, &shape(), eta),
            Vec::new()
        );
        // The folded tree really is half-ish the size and its claim is at r.
        assert_eq!(proof.folded_layers.len(), HEIGHT - K);
        assert_eq!(bottom_claim.u.len(), proof.sumcheck.point.len());
        assert_eq!(
            proof.sumcheck.rounds.len(),
            NV,
            "Eq. (15) is over ℓ−k+1+m = {NV} variables"
        );
        assert_eq!(
            proof.sumcheck.rounds[0].len(),
            FOLD_NC,
            "and each round message carries the product's three coefficients"
        );
        assert_eq!(
            top_claim.u.len(),
            K + 1 + key.slot_len().trailing_zeros() as usize
        );
        // Protocol 4's bound is not vacuous: the folded openings sit inside it.
        let got = proof
            .folded_layers
            .iter()
            .map(|layer| tree_commit::max_norm(layer))
            .max()
            .unwrap_or(0);
        assert!(got <= shape().bound, "{got} vs {}", shape().bound);
        assert!(got > 1, "folding must actually grow the norm");
    }

    #[test]
    fn every_tampered_component_fails_its_own_named_check() {
        let (key, claim, layers, challenges) = instance();
        let binding = b"fold-test".to_vec();
        let eta = F::from(12_345u64);
        let verify = |proof: &Proof, claim: &TreeClaim<F, D>| {
            fold_verify::<F, D, 2, ALPHA, NV>(
                &key,
                claim,
                &layers,
                proof,
                K,
                &challenges,
                &binding,
                &shape(),
                eta,
            )
        };
        let (honest, _, _) = fold_prove::<F, D, 2, ALPHA, NV>(
            &key,
            &claim,
            &layers,
            K,
            &challenges,
            &shape(),
            &binding,
        )
        .expect("prove");

        // Eq. 12: a forged split.
        let mut forged = honest.clone();
        forged.v_subs = forged.v_subs + tree_eval::embed::<F, D>(F::ONE);
        assert_eq!(
            verify(&forged, &claim),
            Err(FoldError::SplitClaimMismatch),
            "a wrong v_subs breaks the split before anything else"
        );

        // Eq. 12 from the other direction: the prover refuses to fold a claim
        // that is not the sum of its own split.
        let forged_claim = TreeClaim {
            t: claim.t.clone(),
            u: claim.u.clone(),
            v: claim.v.clone() + tree_eval::embed::<F, D>(F::ONE),
        };
        assert_eq!(
            fold_prove::<F, D, 2, ALPHA, NV>(
                &key,
                &forged_claim,
                &layers,
                K,
                &challenges,
                &shape(),
                &binding,
            ),
            Err(FoldError::SplitClaimMismatch),
            "a claim that is not v_top's factor plus v_subs cannot be folded at all"
        );

        // Eq. 11's commitment: a corrupted folded root.
        let mut forged = honest.clone();
        forged.folded_root[0] = forged.folded_root[0].clone() + tree_eval::embed::<F, D>(F::ONE);
        assert_eq!(
            verify(&forged, &claim),
            Err(FoldError::FoldedCommitmentMismatch),
            "t* is recomputed from the layer-k children, so a swapped root is caught"
        );

        // Eq. 11's openings: a corrupted folded layer.
        let mut forged = honest.clone();
        forged.folded_layers[0][0] =
            forged.folded_layers[0][0].clone() + tree_eval::embed::<F, D>(F::ONE);
        assert_eq!(
            verify(&forged, &claim),
            Err(FoldError::FoldedLayerMismatch { level: 1 })
        );

        // Eq. 11's batched form: only the powers-claim, not the direct one, is
        // wrong. Fold a *different* challenge vector into the root only.
        let mut forged = honest.clone();
        forged.folded_root = vec![tree_eval::embed::<F, D>(F::from(3u64)); key.rows()];
        assert_eq!(
            verify(&forged, &claim),
            Err(FoldError::FoldedCommitmentMismatch),
            "the direct check runs first; Eq. 19 alone cannot be the only failure"
        );

        // Eq. 17: a subtree commitment that does not hold the evaluations. Named
        // separately from the *input* tree's `Open` since 2026-09-24 — before the
        // split these two obligations both came back as `FoldError::Tree`.
        let mut forged = honest.clone();
        forged.subs.root[0] = forged.subs.root[0].clone() + tree_eval::embed::<F, D>(F::ONE);
        assert!(
            matches!(
                verify(&forged, &claim),
                Err(FoldError::SubtreeCommitInvalid(_))
            ),
            "a corrupted t_subs must fail its own Open: {:?}",
            verify(&forged, &claim)
        );

        // Eq. 18: a forged folded evaluation.
        let mut forged = honest.clone();
        forged.v_bot = forged.v_bot + tree_eval::embed::<F, D>(F::ONE);
        assert_eq!(
            verify(&forged, &claim),
            Err(FoldError::FoldedEvaluationMismatch)
        );

        // The norm gate: the same fold checked against a smaller declared k.
        let tight = CycleShape::new(1, 1, 2);
        assert_eq!(
            fold_verify::<F, D, 2, ALPHA, NV>(
                &key,
                &claim,
                &layers,
                &honest,
                K,
                &challenges,
                &binding,
                &tight,
                eta
            ),
            Err(FoldError::NormGrowth {
                got: honest
                    .folded_layers
                    .iter()
                    .map(|l| tree_commit::max_norm(l))
                    .max()
                    .unwrap_or(0),
                bound: tight.bound
            }),
            "B = 2^k·T·b with a smaller T must reject the real witness"
        );
    }

    #[test]
    fn a_proof_does_not_survive_a_different_statement() {
        let (key, claim, layers, challenges) = instance();
        let binding = b"bind-a".to_vec();
        let other = b"bind-b".to_vec();
        let (proof, _, _) = fold_prove::<F, D, 2, ALPHA, NV>(
            &key,
            &claim,
            &layers,
            K,
            &challenges,
            &shape(),
            &binding,
        )
        .expect("prove");
        let eta = F::from(999u64);
        assert!(fold_verify::<F, D, 2, ALPHA, NV>(
            &key,
            &claim,
            &layers,
            &proof,
            K,
            &challenges,
            &other,
            &shape(),
            eta,
        )
        .is_err());
        // A different folding challenge set is a different statement too: Eq. 11
        // and Eq. 19 both stop holding.
        let swapped: Vec<PolyRing<F, D>> = challenges.iter().rev().cloned().collect();
        assert_eq!(
            fold_verify::<F, D, 2, ALPHA, NV>(
                &key,
                &claim,
                &layers,
                &proof,
                K,
                &swapped,
                &binding,
                &shape(),
                eta
            ),
            Err(FoldError::FoldedCommitmentMismatch)
        );
    }

    #[test]
    fn fold_rejects_a_tree_that_does_not_open() {
        // Protocol 4's `Input` is a member of `TE(1,ℓ,b)`, and the reduction is
        // only stated over such a member, so the verifier's first act is
        // Def. 19's `Open`. The prover is *not* asked to check that: it holds the
        // witness, and its own split (Eq. 12) is consistent with whatever layers
        // it was handed. So the claim here is re-read off the broken layers —
        // which lets `fold_prove` run and isolates the rejection in `Open`.
        let (key, honest, layers, challenges) = instance();
        let mut bad = layers.clone();
        // A digit move that stays inside `{0, ±1}`: editing layer 1 breaks the
        // root equation `t = A·s₁`, which `Open` checks before the layer links and
        // before the norm gate, so this is the one equation the fold must name.
        bad[0][0] = bad[0][0].clone() - tree_eval::embed::<F, D>(F::ONE);
        assert!(tree_commit::max_norm(&bad[0]) < 2, "the edit stays a digit");
        let slot = key.slot_len();
        let u = poly_vec(HEIGHT + 1 + slot.trailing_zeros() as usize);
        let s = tree_eval::concatenated(slot, &bad);
        let claim = TreeClaim {
            t: honest.t,
            u: u.clone(),
            v: tree_eval::mle_at_ring(&s, &u).expect("TE claim on the broken witness"),
        };
        let binding = b"fold-test".to_vec();
        let (proof, _, _) = fold_prove::<F, D, 2, ALPHA, NV>(
            &key,
            &claim,
            &bad,
            K,
            &challenges,
            &shape(),
            &binding,
        )
        .expect("the prover folds whatever split it can compute");
        let report = fold_report(
            &key,
            &claim,
            &bad,
            &proof,
            K,
            &challenges,
            &binding,
            &shape(),
            F::ONE,
        );
        assert_eq!(
            report,
            vec![FoldError::Tree(TreeError::RootMismatch { at: 0 })],
            "the broken input tree is what the fold refuses, and nothing else"
        );
    }
}
