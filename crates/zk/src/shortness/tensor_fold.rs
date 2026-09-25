//! Tensor-structured split-and-fold engine (the algebra under a unified
//! lattice argument).
//!
//! A single divide-and-conquer recursion can discharge four different
//! constraint families at once — a leveled commitment, a public-weight linear
//! claim, a self-inner-product norm claim, and a randomized binarity claim —
//! because after the coefficient-to-ring embedding all four are the *same*
//! shape: pairings of a witness vector against a weight vector that factors
//! along the halved axis. This module provides that shared machinery, generic
//! over the scalar ring and the ring degree (gap G1):
//!
//! - [`LinearWeights`]: the weight vectors of §"Linear Constraint Proof" and
//!   their tensor factorization. One constructor [`LinearWeights::from_vars`]
//!   covers the univariate power vector, the multilinear MLE vector and the
//!   plain power vectors the binarity check uses, because all three are
//!   "product of per-bit variables"; [`LinearWeights::digit_axis`] absorbs the
//!   base-2 digit weights so a claim about a value vector becomes a claim
//!   about its *decomposition* — which is what makes a committed preimage and
//!   the value it encodes checkable against each other.
//! - [`linear_msg`]/[`linear_expose`]/[`linear_recursion`]/[`linear_base`]:
//!   the four verifier checks of the linear recursion, in order.
//! - [`quad_msg`]/[`quad_weights`]/[`quad_expose`]/[`quad_recursion`]:
//!   the quadratic (self-inner-product) recursion in its **bilinear** form, so
//!   `⟨u, σ(v)⟩` with `u ≠ v` is expressible; `u = v` is the norm case that
//!   [`crate::shortness::self_ip`] implements concretely.
//! - [`NormAccounting`]: Theorem-1-shape norm growth under folding, and
//!   [`square_sum_admissible`]: the Lemma-2-shape condition under which an
//!   exact-integer norm claim stops being ambiguous mod `q`.
//! - [`pool_challenge`]: a challenge space of short ring elements whose
//!   pairwise differences stay inside the invertibility regime.
//!
//! # What is *not* here
//!
//! The composed relation — commitment + linear + quadratic + binarity over a
//! leveled commitment, with the per-repetition bookkeeping — lives in
//! [`crate::shortness::committed_norm`], and which constraints a given
//! polynomial commitment scheme has to prove is scheme work (`examples/`).
//!
//! # Where each piece comes from (eprint 2025/1903)
//!
//! | this module | the paper |
//! |---|---|
//! | [`LinearWeights`] and [`kron`] | §3.2 "Linear Constraint Proof", p. 11: `⟨coef(s), ⊗_{i<log N} a⃗_i⟩ = v = ct(⟨s⃗, (⊗_{i≥1} a⃗_i) ⊗ a⃗_0⟩)`, with `a⃗_0 ∈ Z_q^{2ℓd}` and `a⃗_i = (1, u^{2^{i-1}·2ℓd})` |
//! | the univariate/multilinear specialisations | §4, p. 22–23: `ū_uni = ⊗(1, u^{2^{i-1}·2d})`, `ū_mul = ⊗_{j<log(Nd)}(1, u_j)`, and the digit absorption `ū_•,0 ⊗ (1,2,…,2^{ℓ−1})` that turns a claim about values into one about the decomposition |
//! | [`linear_msg`]/[`linear_expose`]/[`linear_recursion`]/[`linear_base`] | Fig. 3 (p. 17) rows 1–3 of the `⟨a⃗, π^(lin)⟩` column |
//! | [`quad_msg`]/[`quad_weights`]/[`quad_carry`]/[`quad_base`] | §3.2 "Quadratic Constraint Proof", p. 12 + Fig. 3, p. 17. Fig. 3's weight order is the algebraically correct one; §3.2's display swaps the two cross entries (see [`crate::shortness::self_ip`]'s module doc) |
//! | [`hadamard`] and the binarity identity | §3.3 "Randomized binarity check", p. 13: `⟨α⃗∘s, s⃗⟩ = ⟨α⃗, s⃗⟩`, soundness error `Nℓd/q` |
//! | [`NormAccounting`] | Theorem 1, p. 18: `γ_{log N} = (2T)^{log N−1}`, `γ = √(2ℓd)·γ_{log N}`, `γ_{α,log N} = (σ_α/2)(2T)^{log N−1}`, `γ_α = √(2ι_α d)·γ_{α,log N}` |
//! | [`NormAccounting::msis_bounds`] | Theorem 2 / Eq. (4), p. 18–19: `β_M-SIS ≥ max(N·√(Nℓ)·γ_{log N}, N·√(Nℓι_α)·γ_{α,log N})` |
//! | [`pool_challenge`] | §3.6 "Challenge space", p. 20–21: the pool `P_{w0,w1,w2}`, `τ = √(w1+2w2)`, `T = ‖c‖₁ = w1+2w2`, `|P_w| = (d over w1)(d−w1 over w2)2^{w1+w2}`, invertibility via Lemma 1 (p. 8) |
//! | [`square_sum_admissible`] | Lemma 2, p. 8 (`q > 2Nℓd`), deferred to [`crate::shortness::exact_l2::direct_route_admissible`] |
//! | `repetitions` | §3.3 "Protocol repetition", p. 14 and Theorem 2, p. 19: `t = ⌈λ / log₂(q/(2Nℓd))⌉` |
//!
//! # Index convention
//!
//! A witness is a ring vector whose element index decomposes as
//! `p = n·block + e`, with `n` the axis being halved and `e` the inner axis;
//! each element carries `D` scalar coefficients. [`gadget::split`]
//! (`crate::pcs::gadget`) fixes the layout `out[j·DIGITS + k]`, so the digit
//! plane `k` is the *fast* index inside a block. Weights are written in that
//! layout, which is why [`LinearWeights::digit_axis`] takes `digits` and
//! `block` separately rather than one flat stride.

use crate::pcs::packing::sigma_of;
use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// One ring element of `R_q = Z_q[X]/(X^D + 1)`.
pub type Elt<R, const D: usize> = PolyRing<R, D>;

/// Why a split-and-fold step refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FoldError {
    /// A weight vector was not buildable: `block` must be a multiple of
    /// `digits`, both powers of two, and `vars` long enough to cover every
    /// axis bit.
    BadWeights {
        /// What the caller asked for, as a short tag.
        reason: &'static str,
    },
    /// A state/message pair had the wrong length for the round it was used in.
    WrongLength {
        /// Length supplied.
        got: usize,
        /// Length the round requires.
        expected: usize,
        /// Which slot.
        slot: &'static str,
    },
    /// Fig. 3 step 1 of the linear constraint: the round-1 message does not
    /// expose the public claim `v`.
    ClaimMismatch {
        /// Constant term the message implied.
        got: u64,
        /// The public claim.
        expected: u64,
    },
    /// Fig. 3 step 2: the round's own weight-contraction disagrees with the
    /// challenge-folded previous message.
    RecursionMismatch {
        /// Round index.
        round: usize,
    },
    /// The final round's base pairing disagrees with the last message.
    BaseMismatch,
    /// The quadratic claim `ct(L + R) = b` failed at the round that exposed it.
    NormClaimMismatch {
        /// Round index.
        round: usize,
        /// `ct(L + R)` for this round.
        got: u64,
        /// The claim carried into the round.
        expected: u64,
    },
    /// A challenge was drawn outside the declared pool (wrong coefficient
    /// multiplicity), so the invertibility argument does not apply.
    ChallengeOutOfPool,
    /// The exact-integer norm claim is not admissible mod `q`.
    NotAdmissible {
        /// Largest representable squared norm.
        limit: u128,
        /// The modulus.
        modulus: u64,
    },
    /// The revealed vector exceeded its Theorem-1 bound.
    NotShort {
        /// Its exact squared norm.
        norm_sq: u128,
        /// The admissible squared bound.
        bound_sq: u128,
    },
}

impl fmt::Display for FoldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FoldError::BadWeights { reason } => write!(f, "unbuildable weight vector: {reason}"),
            FoldError::WrongLength {
                got,
                expected,
                slot,
            } => {
                write!(f, "{slot}: got {got}, expected {expected}")
            }
            FoldError::ClaimMismatch { got, expected } => {
                write!(
                    f,
                    "linear exposure: message gives {got}, claim is {expected}"
                )
            }
            FoldError::RecursionMismatch { round } => {
                write!(f, "round {round}: linear recursion does not carry")
            }
            FoldError::BaseMismatch => write!(f, "final linear pairing disagrees with the tail"),
            FoldError::NormClaimMismatch {
                round,
                got,
                expected,
            } => write!(
                f,
                "round {round}: ct(L+R) = {got}, norm claim is {expected}"
            ),
            FoldError::ChallengeOutOfPool => {
                write!(f, "challenge outside the declared coefficient pool")
            }
            FoldError::NotAdmissible { limit, modulus } => write!(
                f,
                "sum of squares needs {limit} < q = {modulus} to stay unambiguous"
            ),
            FoldError::NotShort { norm_sq, bound_sq } => write!(
                f,
                "revealed squared norm {norm_sq} exceeds the admissible {bound_sq}"
            ),
        }
    }
}

/// The additive identity.
pub fn zero<R: Ring, const D: usize>() -> Elt<R, D> {
    PolyRing::from_coefficients(vec![R::ZERO; D])
}

/// A field element embedded as a constant ring element.
pub fn constant<R: Ring, const D: usize>(c: R) -> Elt<R, D> {
    let mut out = vec![R::ZERO; D];
    out[0] = c;
    PolyRing::from_coefficients(out)
}

/// `Σᵢ uᵢ·vᵢ` over the ring.
///
/// # Panics
/// If the vectors differ in length.
pub fn dot<R: Ring, const D: usize>(u: &[Elt<R, D>], v: &[Elt<R, D>]) -> Elt<R, D> {
    assert_eq!(u.len(), v.len(), "dot needs equal lengths");
    let mut acc = zero::<R, D>();
    for (a, b) in u.iter().zip(v.iter()) {
        acc += a.clone() * b.clone();
    }
    acc
}

/// `⟨u, σ(v)⟩ = Σᵢ uᵢ·σ(vᵢ)` with `σ: X ↦ X⁻¹`.
///
/// This is the generic form of [`crate::shortness::self_ip::hermitian`], which
/// is pinned to the crate's Z1 instance; `ring_matches_the_concrete_self_ip_form`
/// below asserts the two agree.
///
/// # Panics
/// If the vectors differ in length.
pub fn herm<R: Ring, const D: usize>(u: &[Elt<R, D>], v: &[Elt<R, D>]) -> Elt<R, D> {
    assert_eq!(u.len(), v.len(), "hermitian pairing needs equal lengths");
    let mut acc = zero::<R, D>();
    for (a, b) in u.iter().zip(v.iter()) {
        acc += a.clone() * sigma_of::<R, D>(b);
    }
    acc
}

/// The constant coefficient.
pub fn ct<R: Ring, const D: usize>(x: &Elt<R, D>) -> R {
    x.coefficients()[0]
}

/// `Σ_{i,t} u[i][t]·v[i][t]` as a ring scalar — i.e. `ct(⟨u, σ(v)⟩)`.
///
/// With `v = u` this is the integer sum of squares the norm gate consumes.
pub fn scalar_pairing<R: Ring, const D: usize>(u: &[Elt<R, D>], v: &[Elt<R, D>]) -> R {
    ct(&herm(u, v))
}

/// `u ∘ v`: the flat (coefficient-wise) Hadamard product of two ring vectors.
///
/// This is the Schur product the randomized binarity check needs —
/// `⟨α, s ∘ s⟩ = ⟨α, s⟩` holds exactly when every *flat coordinate* of `s` is
/// 0/1 — and it is deliberately **not** the ring product, which convolves the
/// coefficients and would make the identity fail for any witness with more than
/// one nonzero coefficient per element.
///
/// # Panics
/// If the vectors differ in length.
pub fn hadamard<R: Ring, const D: usize>(u: &[Elt<R, D>], v: &[Elt<R, D>]) -> Vec<Elt<R, D>> {
    assert_eq!(u.len(), v.len(), "hadamard needs equal lengths");
    u.iter()
        .zip(v.iter())
        .map(|(a, b)| {
            let ac = a.coefficients();
            let bc = b.coefficients();
            Elt::from_coefficients(
                (0..D)
                    .map(|k| {
                        let x = ac.get(k).copied().unwrap_or(R::ZERO);
                        let y = bc.get(k).copied().unwrap_or(R::ZERO);
                        x * y
                    })
                    .collect(),
            )
        })
        .collect()
}

/// Flattens to scalar coefficients (ascending powers, element-major).
pub fn flatten<R: Ring, const D: usize>(v: &[Elt<R, D>]) -> Vec<R> {
    v.iter()
        .flat_map(|e| e.coefficients().into_iter())
        .collect()
}

/// Groups `D` consecutive scalars per ring element.
///
/// # Panics
/// If `flat.len()` is not a multiple of `D`.
pub fn pack<R: Ring, const D: usize>(flat: &[R]) -> Vec<Elt<R, D>> {
    assert!(flat.len() % D == 0, "packing needs whole ring elements");
    flat.chunks(D)
        .map(|c| PolyRing::from_coefficients(c.to_vec()))
        .collect()
}

/// `a ⊗ b` for ring vectors, `a` slow: `[a₀b₀, a₀b₁, …, a₁b₀, …]`.
///
/// Halving a state along its outer axis peels the *left* factor, which is why
/// the slowest factor is the one a round consumes first.
pub fn kron<R: Ring, const D: usize>(a: &[Elt<R, D>], b: &[Elt<R, D>]) -> Vec<Elt<R, D>> {
    let mut out = Vec::with_capacity(a.len() * b.len());
    for x in a {
        for y in b {
            out.push(x.clone() * y.clone());
        }
    }
    out
}

/// The exact-integer squared norm of a vector's centered lifts (generic form
/// of [`crate::shortness::exact_l2::squared_norm`]).
///
/// # Errors
/// [`FoldError::NotAdmissible`] if the sum cannot be represented without
/// wrapping mod `q` — the caller must then fall back to a digit-expanded
/// route rather than trust the residue.
pub fn square_sum<R: CenteredRing, const D: usize>(v: &[Elt<R, D>]) -> Result<u128, FoldError> {
    let mut acc: u128 = 0;
    for c in flatten(v).iter() {
        let x = i128::from(c.centered());
        acc = acc
            .checked_add(u128::try_from(x * x).map_err(|_| FoldError::NotAdmissible {
                limit: u128::MAX,
                modulus: R::MODULUS,
            })?)
            .ok_or(FoldError::NotAdmissible {
                limit: u128::MAX,
                modulus: R::MODULUS,
            })?;
    }
    Ok(acc)
}

/// Whether a claim of the form `Σ (centered lift)² = b` is unambiguous mod `q`,
/// i.e. whether the *integer* value is pinned by its residue. The condition is
/// on the largest value the sum can take: with `count` coordinates each of
/// magnitude `≤ max_magnitude`, the sum reaches `count · max_magnitude²`, and
/// that must stay below `q`.
///
/// This is Serval's Lemma 2 window (`q > 2Nℓd` for a binary witness, p. 8) and
/// Akita's direct-route precondition, so the decision is *not* re-implemented
/// here: it defers to [`crate::shortness::exact_l2::direct_route_admissible`],
/// which owns the `S_max < q` statement.
#[must_use]
pub fn square_sum_admissible<R: CenteredRing>(count: usize, max_magnitude: u64) -> bool {
    let bound = u128::from(count as u64)
        .saturating_mul(u128::from(max_magnitude))
        .saturating_mul(u128::from(max_magnitude));
    crate::shortness::exact_l2::direct_route_admissible::<R>(bound)
}

/// The norm-growth and admissibility accounting of a `log N`-round fold.
///
/// Each round replaces a state by `c₀·s_L + c₁·s_R`, so with a challenge space
/// of `ℓ∞`-operator norm `T` the coordinate bound doubles and multiplies by
/// `T` per round: `γ_{i+1} = 2T·γ_i`. A revealed vector of `2·block` ring
/// elements then has `2·block·D` coordinates, giving the `√(2·block·D)` lift
/// from `ℓ∞` to `ℓ₂`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NormAccounting {
    /// Rounds of folding, `log N − 1`.
    pub rounds: usize,
    /// Challenge-space bound `T = ‖c‖_{op,∞}`.
    pub t_op: u64,
    /// Initial coordinate bound (`1` for a binary witness, `base/2` for
    /// balanced digits).
    pub initial: u64,
    /// Elements in a revealed base state.
    pub base_len: usize,
}

impl NormAccounting {
    /// The `ℓ∞` bound after all folds: `γ₁·(2T)^{rounds}`.
    ///
    /// # Panics
    /// On overflow — a bound that does not fit `u64` means the parameters are
    /// inadmissible, which the caller checks against the modulus.
    #[must_use]
    pub fn coord_bound(&self) -> u64 {
        self.initial
            .checked_mul(
                (2 * self.t_op)
                    .checked_pow(u32::try_from(self.rounds).expect("rounds fit u32"))
                    .expect("norm bound overflows u64: parameters are inadmissible"),
            )
            .expect("norm bound overflows u64: parameters are inadmissible")
    }

    /// The squared `ℓ₂` admissibility bound on the revealed base state:
    /// `2·base_len·γ²` (the `√(2·block·D)` lift, squared).
    #[must_use]
    pub fn bound_sq(&self) -> u128 {
        let g = u128::from(self.coord_bound());
        2 * u128::from(self.base_len as u64) * g * g
    }

    /// The `M-SIS` norm bound a binding argument for this fold has to assume,
    /// `N · max(√(N·ℓ)·γ_{log N}, N·√(N·ℓ·ι)·γ_{α,log N})`, where `ℓ` is the
    /// main witness's digit planes, `ι` the auxiliary witness's, and `N` the
    /// block count.
    ///
    /// Returned as `(main, auxiliary)` rounded **up**, so a caller comparing it
    /// against a hardness estimate never benefits from a rounding accident.
    #[must_use]
    pub fn msis_bounds(&self, blocks: usize, digits: usize, aux_digits: usize) -> (u128, u128) {
        let g = u128::from(self.coord_bound());
        let ga = u128::from(self.initial) * g;
        let n = u128::from(blocks as u64);
        let main = n * ceil_sqrt(n * u128::from(digits as u64)) * g;
        let aux = n * n * ceil_sqrt(n * u128::from((digits * aux_digits) as u64)) * ga;
        (main, aux)
    }

    /// The number of independent repetitions needed to push a per-round error
    /// of `err_num/err_den` below `2^{-target_bits}`, together with the
    /// error bits actually achieved.
    ///
    /// With `k = ⌊log₂(den/num)⌋ ≥ 1`, `t = ⌈target/k⌉` repetitions give
    /// `(num/den)^t ≤ 2^{-k·t} ≤ 2^{-target}`.
    ///
    /// Returns `None` when the check carries no advantage over guessing
    /// (`den <= num`), so a caller cannot silently "repeat" a useless check.
    #[must_use]
    pub fn repetitions(err_num: u64, err_den: u64, target_bits: u64) -> Option<(u64, u64)> {
        if err_num == 0 || err_den <= err_num {
            return None;
        }
        let mut k = 0u64;
        let mut scaled = err_num;
        while let Some(doubled) = scaled.checked_mul(2) {
            if doubled > err_den {
                break;
            }
            scaled = doubled;
            k += 1;
        }
        if k == 0 {
            return None;
        }
        let reps = target_bits.div_ceil(k);
        Some((reps, k * reps))
    }
}

/// The weight vector of a public-weight linear claim, stored as its tensor
/// factorization.
///
/// `vars` are the per-bit variables of the *scalar* index: the weight of
/// scalar position `i` with coefficient slot `t` is `∏_{b: bit b of (i) set}
/// vars[b]`, i.e. the multilinear extension vector over the bits of the flat
/// scalar index. Choosing `vars[b] = base^{2^b}` collapses that product to
/// `base^i`, which is the univariate power vector; choosing independent
/// `vars[b]` gives the multilinear point. See [`geometric_vars`].
#[derive(Clone, PartialEq, Eq)]
pub struct LinearWeights<R: Ring, const D: usize> {
    a0: Vec<Elt<R, D>>,
    ratios: Vec<R>,
    block: usize,
    rounds: usize,
}

impl<R: Ring, const D: usize> fmt::Debug for LinearWeights<R, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LinearWeights")
            .field("block", &self.block)
            .field("rounds", &self.rounds)
            .field("a0_len", &self.a0.len())
            .finish()
    }
}

/// `vars[b] = base^{2^b}` — the geometric specialization that turns the
/// multilinear weight vector into the power vector `(1, base, base², …)`.
pub fn geometric_vars<R: Ring>(base: R, count: usize) -> Vec<R> {
    let mut out = Vec::with_capacity(count);
    let mut cur = base;
    for _ in 0..count {
        out.push(cur);
        cur = cur.square();
    }
    out
}

/// `∏_{b: bit b of i is set} vars[b]` — the multilinear-extension value at the
/// Boolean point `i`.
///
/// # Errors
/// [`FoldError::BadWeights`] if `vars` does not cover the bits of `i`.
pub fn mle_value<R: Ring>(vars: &[R], i: usize) -> Result<R, FoldError> {
    // `ilog2` is undefined at 0, and index 0 is the all-zero Boolean point,
    // whose multilinear value is the empty product.
    let need = if i == 0 {
        0
    } else {
        usize::try_from(u64::from(i.ilog2()) + 1).unwrap_or(usize::MAX)
    };
    if need > vars.len() {
        return Err(FoldError::BadWeights {
            reason: "vars shorter than the index needs",
        });
    }
    let mut acc = R::ONE;
    for b in 0..need {
        if (i >> b) & 1 == 1 {
            acc *= vars[b];
        }
    }
    Ok(acc)
}

impl<R: Ring, const D: usize> LinearWeights<R, D> {
    /// Shared builder for the two specializations below.
    ///
    /// * innermost factor: `a0[e][t] = scale(e) · weight_at((e div digits)·D + t)`
    ///   over `e ∈ [0, 2·block)`, where `scale(e) = 2^{e mod digits}` is the
    ///   base-2 digit weight of the decomposition plane `e mod digits`;
    /// * outer factors: `α_{j+1} = (1, ratio_j)` with
    ///   `ratio_j = weight_at(2^{j+1} · (block/digits) · D)`, the multiplier the
    ///   fold bit `j` contributes to the *value* index.
    ///
    /// `weight_at` is supplied by the caller's specialization, which is why it
    /// is a closure rather than a stored table: the geometric case needs only a
    /// base, the multilinear case needs the whole variable vector.
    ///
    /// # Errors
    /// [`FoldError::BadWeights`] if `digits` does not divide `block`, either is
    /// not a power of two where one must be, or `weight_at` rejects an index.
    fn build<F, S>(
        digits: usize,
        block: usize,
        rounds: usize,
        weight_at: F,
        scale: S,
    ) -> Result<Self, FoldError>
    where
        F: Fn(usize) -> Result<R, FoldError>,
        S: Fn(usize) -> R,
    {
        // The only hard limit on the digit axis is the shift that forms the
        // plane weight `2^(e mod digits)`: a gadget with δ planes needs no
        // alignment between δ and the block, and Serval's own δ = ⌈log₂ q⌉ is
        // not a power of two. The multilinear builder adds its own alignment
        // requirements because a fold bit must be one constant factor there.
        if digits == 0 || digits > 64 {
            return Err(FoldError::BadWeights {
                reason: "digits must be in 1..=64 (the plane weight is 2^(e mod digits))",
            });
        }
        if block == 0 || block % digits != 0 {
            return Err(FoldError::BadWeights {
                reason: "digits must divide block",
            });
        }
        let stride = (block / digits) * D;
        let mut a0 = Vec::with_capacity(2 * block);
        for e in 0..2 * block {
            let value = e / digits;
            let mut coeffs = vec![R::ZERO; D];
            for t in 0..D {
                coeffs[t] = scale(e) * weight_at(value * D + t)?;
            }
            a0.push(PolyRing::from_coefficients(coeffs));
        }
        let ratios = (0..rounds)
            .map(|j| weight_at(stride << (j + 1)))
            .collect::<Result<Vec<R>, FoldError>>()?;
        Ok(Self {
            a0,
            ratios,
            block,
            rounds,
        })
    }

    /// The geometric specialization: `weight_at(i) = base^i`, which turns the
    /// tensor weight into the power vector `(1, base, base², …)` over the
    /// value index. This covers a univariate evaluation claim and every
    /// randomized power-vector check (binarity, range), for **any** digit and
    /// block split — no bit-alignment is required, because `base^{i+j} =
    /// base^i·base^j` unconditionally.
    ///
    /// # Errors
    /// As [`Self::build`].
    pub fn geometric(
        base: R,
        digits: usize,
        block: usize,
        rounds: usize,
    ) -> Result<Self, FoldError> {
        Self::build(
            digits,
            block,
            rounds,
            |i| Ok(base.pow(i as u64)),
            |e| R::from(1u64 << (e % digits)),
        )
    }

    /// The multilinear specialization: `weight_at(i) = ∏_{b: bit b of i set}
    /// vars[b]`, the evaluation vector of an `ℓ`-variate multilinear polynomial
    /// read at the Boolean point named by `i`.
    ///
    /// A fold bit is only expressible as a single constant factor when the
    /// value axis is bit-aligned, so this builder additionally requires
    /// `digits == 1` and `block·D` a power of two; the paper's multilinear
    /// instantiation (§4) satisfies both by folding the packed coefficient
    /// vector before decomposition.
    ///
    /// # Errors
    /// [`FoldError::BadWeights`] for a digit axis, a non-power-of-two
    /// `block·D`, or a `vars` vector shorter than the index needs.
    pub fn multilinear(vars: &[R], block: usize, rounds: usize) -> Result<Self, FoldError> {
        if block == 0 || !block.is_power_of_two() || !D.is_power_of_two() {
            return Err(FoldError::BadWeights {
                reason: "block and ring degree must be powers of two",
            });
        }
        if vars.len() < (block * D).trailing_zeros() as usize + 1 + rounds {
            return Err(FoldError::BadWeights {
                reason: "vars must cover every axis bit",
            });
        }
        Self::build(1, block, rounds, |i| mle_value(vars, i), |_| R::ONE)
    }

    /// The innermost factor (length `2·block`).
    pub fn a0(&self) -> &[Elt<R, D>] {
        &self.a0
    }

    /// The outer ratios, innermost first.
    pub fn ratios(&self) -> &[R] {
        &self.ratios
    }

    /// Elements per block on the halved axis.
    pub const fn block(&self) -> usize {
        self.block
    }

    /// Rounds of folding.
    pub const fn rounds(&self) -> usize {
        self.rounds
    }

    /// Witness length this weight applies to.
    pub fn len(&self) -> usize {
        self.a0.len() << self.rounds
    }

    /// Whether the weight table is empty (it never is for a built weight).
    pub fn is_empty(&self) -> bool {
        self.a0.is_empty()
    }

    /// The weight for a state that still has `outer` outer factors, i.e. for a
    /// state of length `2^outer · 2 · block`.
    ///
    /// # Errors
    /// [`FoldError::WrongLength`] if `outer > rounds`.
    pub fn weight(&self, outer: usize) -> Result<Vec<Elt<R, D>>, FoldError> {
        if outer > self.rounds {
            return Err(FoldError::WrongLength {
                got: outer,
                expected: self.rounds,
                slot: "weight nesting",
            });
        }
        let mut w = self.a0.clone();
        // Applied innermost-first, so `ratios[outer-1]` ends up the slow factor
        // — which is the one a round peels when it halves the state.
        for r in self.ratios[..outer].iter() {
            w = kron(&[constant::<R, D>(R::ONE), constant::<R, D>(*r)], &w);
        }
        Ok(w)
    }

    /// The `2`-element constant factor `α_{rounds−round+1} = (1, ρ)` a round
    /// consumes, for `round ∈ [1, rounds]`.
    ///
    /// # Errors
    /// [`FoldError::WrongLength`] for a round outside `[1, rounds]`.
    pub fn beta(&self, round: usize) -> Result<[Elt<R, D>; 2], FoldError> {
        if round == 0 || round > self.rounds {
            return Err(FoldError::WrongLength {
                got: round,
                expected: self.rounds,
                slot: "beta round",
            });
        }
        Ok([
            constant::<R, D>(R::ONE),
            constant::<R, D>(self.ratios[self.rounds - round]),
        ])
    }
}

/// One round's linear message `(v_L, v_R) = (⟨s_L, W'⟩, ⟨s_R, W'⟩)`.
///
/// `child` is the weight of the *halves*, i.e.
/// [`LinearWeights::weight`] at `outer − 1`.
///
/// # Errors
/// [`FoldError::WrongLength`] if `child` is not exactly half of `state`.
pub fn linear_msg<R: Ring, const D: usize>(
    state: &[Elt<R, D>],
    child: &[Elt<R, D>],
) -> Result<[Elt<R, D>; 2], FoldError> {
    if state.len() != 2 * child.len() || state.is_empty() {
        return Err(FoldError::WrongLength {
            got: state.len(),
            expected: 2 * child.len(),
            slot: "linear state",
        });
    }
    let half = state.len() / 2;
    Ok([herm(&state[..half], child), herm(&state[half..], child)])
}

/// Fig. 3 step 1: `ct(⟨α, (v_L, v_R)⟩) =? v`.
///
/// # Errors
/// [`FoldError::ClaimMismatch`] when the message exposes something else.
pub fn linear_expose<R: CenteredRing, const D: usize>(
    beta: &[Elt<R, D>; 2],
    msg: &[Elt<R, D>; 2],
    claim: R,
) -> Result<(), FoldError> {
    let got = ct(&dot(beta, msg));
    if got == claim {
        Ok(())
    } else {
        Err(FoldError::ClaimMismatch {
            got: u64::try_from(got.to_u128()).unwrap_or(u64::MAX),
            expected: u64::try_from(claim.to_u128()).unwrap_or(u64::MAX),
        })
    }
}

/// Fig. 3 step 2: `⟨α_{round}, msg⟩ =? ⟨c, prev⟩`.
///
/// # Errors
/// [`FoldError::RecursionMismatch`] when the claim does not carry.
pub fn linear_recursion<R: Ring, const D: usize>(
    beta: &[Elt<R, D>; 2],
    msg: &[Elt<R, D>; 2],
    prev: &[Elt<R, D>; 2],
    c: &[Elt<R, D>; 2],
    round: usize,
) -> Result<(), FoldError> {
    if dot(beta, msg) == dot(c, prev) {
        Ok(())
    } else {
        Err(FoldError::RecursionMismatch { round })
    }
}

/// The final round: `⟨s, a₀⟩ =? ⟨c, last msg⟩`.
///
/// # Errors
/// [`FoldError::BaseMismatch`] when the revealed tail does not pair to the
/// carried claim.
pub fn linear_base<R: Ring, const D: usize>(
    state: &[Elt<R, D>],
    a0: &[Elt<R, D>],
    prev: &[Elt<R, D>; 2],
    c: &[Elt<R, D>; 2],
) -> Result<(), FoldError> {
    if state.len() != a0.len() {
        return Err(FoldError::WrongLength {
            got: state.len(),
            expected: a0.len(),
            slot: "linear base state",
        });
    }
    if herm(state, a0) == dot(c, prev) {
        Ok(())
    } else {
        Err(FoldError::BaseMismatch)
    }
}

/// One round's quadratic message `(L, M₁, M₂, R) = (⟨u_L,σ(v_L)⟩,
/// ⟨u_L,σ(v_R)⟩, ⟨u_R,σ(v_L)⟩, ⟨u_R,σ(v_R)⟩)`.
///
/// # Errors
/// [`FoldError::WrongLength`] if the state is empty or `u` and `v` disagree.
pub fn quad_msg<R: Ring, const D: usize>(
    u: &[Elt<R, D>],
    v: &[Elt<R, D>],
) -> Result<[Elt<R, D>; 4], FoldError> {
    if u.len() != v.len() || u.is_empty() || u.len() % 2 != 0 {
        return Err(FoldError::WrongLength {
            got: u.len(),
            expected: v.len(),
            slot: "quadratic state",
        });
    }
    let half = u.len() / 2;
    Ok([
        herm(&u[..half], &v[..half]),
        herm(&u[..half], &v[half..]),
        herm(&u[half..], &v[..half]),
        herm(&u[half..], &v[half..]),
    ])
}

/// The weights `c̃ = (c₀σ(c₀), c₀σ(c₁), c₁σ(c₀), c₁σ(c₁))` matched to
/// [`quad_msg`]'s order.
pub fn quad_weights<R: Ring, const D: usize>(c: &[Elt<R, D>; 2]) -> [Elt<R, D>; 4] {
    let pair = |a: &Elt<R, D>, b: &Elt<R, D>| a.clone() * sigma_of::<R, D>(b);
    [
        pair(&c[0], &c[0]),
        pair(&c[0], &c[1]),
        pair(&c[1], &c[0]),
        pair(&c[1], &c[1]),
    ]
}

/// Fig. 3 step 1 of the quadratic constraint: `ct(L + R) =? b`.
///
/// # Errors
/// [`FoldError::NormClaimMismatch`] naming the round that lost the claim.
pub fn quad_expose<R: CenteredRing, const D: usize>(
    msg: &[Elt<R, D>; 4],
    claim: u64,
    round: usize,
) -> Result<(), FoldError> {
    let modulus = R::MODULUS;
    let l = u64::try_from(ct(&msg[0]).to_u128()).unwrap_or(0);
    let r = u64::try_from(ct(&msg[3]).to_u128()).unwrap_or(0);
    let got = (l + r) % modulus;
    if got == claim % modulus {
        Ok(())
    } else {
        Err(FoldError::NormClaimMismatch {
            round,
            got,
            expected: claim % modulus,
        })
    }
}

/// Fig. 3 step 2 of the quadratic constraint: this round's own `L + R` must
/// equal the previous round's message weighted by `c̃`.
///
/// This is the claim-carry form of the bilinear identity: the verifier never
/// sees the folded states, only the messages, so the identity
/// `⟨u', σ(v')⟩ = Σ c̃ⱼ·msgⱼ` is applied as
/// `L_i + R_i = Σ c̃ⱼ·(qua)_{i−1,j}`.
///
/// # Errors
/// [`FoldError::RecursionMismatch`] naming the round whose carry failed.
pub fn quad_carry<R: Ring, const D: usize>(
    msg: &[Elt<R, D>; 4],
    prev: &[Elt<R, D>; 4],
    c: &[Elt<R, D>; 2],
    round: usize,
) -> Result<(), FoldError> {
    let w = quad_weights(c);
    if msg[0].clone() + msg[3].clone() == dot(&w, prev) {
        Ok(())
    } else {
        Err(FoldError::RecursionMismatch { round })
    }
}

/// The final quadratic check: `⟨u, σ(v)⟩ = Σⱼ c̃ⱼ·msgⱼ` on the revealed tails.
///
/// # Errors
/// [`FoldError::BaseMismatch`] when the tails do not reproduce the carried
/// claim, [`FoldError::WrongLength`] on a mismatched tail.
pub fn quad_base<R: Ring, const D: usize>(
    u: &[Elt<R, D>],
    v: &[Elt<R, D>],
    msg: &[Elt<R, D>; 4],
    c: &[Elt<R, D>; 2],
) -> Result<(), FoldError> {
    if u.len() != v.len() || u.is_empty() {
        return Err(FoldError::WrongLength {
            got: u.len(),
            expected: v.len(),
            slot: "quadratic base",
        });
    }
    let w = quad_weights(c);
    if herm(u, v) == dot(&w, msg) {
        Ok(())
    } else {
        Err(FoldError::BaseMismatch)
    }
}

/// Draws one element of the challenge pool `P_{w₀,w₁,w₂}` — exactly `w₁`
/// coefficients of magnitude `1` and `w₂` of magnitude `2`, everything else
/// zero, signs uniform.
///
/// This is the shape whose pairwise differences stay inside the invertibility
/// regime (`0 < ‖c − c'‖₂ ≤ 4√(2(w₁+w₂)) < √(q/2)`), and whose
/// `ℓ∞`-operator norm is `T = w₁ + 2w₂` — the two facts the norm accounting
/// above depends on.
///
/// # Errors
/// [`FoldError::ChallengeOutOfPool`] if `w₁ + w₂ > D`.
pub fn pool_challenge<R: Ring, X: Xof, const D: usize>(
    stream: &mut BitStream<'_, X>,
    w1: u32,
    w2: u32,
) -> Result<Elt<R, D>, FoldError> {
    let total = w1 + w2;
    if usize::try_from(total).unwrap_or(usize::MAX) > D {
        return Err(FoldError::ChallengeOutOfPool);
    }
    if total == 0 {
        return Ok(zero::<R, D>());
    }
    let signs = crate::foundation::sampling::fixed_weight_signs(stream, total, D);
    // The first `w1` nonzero positions get amplitude 1, the rest amplitude 2;
    // `fixed_weight_signs` already chose the positions uniformly at random.
    let mut out = vec![R::ZERO; D];
    let mut seen = 0u32;
    for (i, s) in signs.iter().enumerate() {
        if *s == 0 {
            continue;
        }
        let amp = if seen < w1 { 1u64 } else { 2u64 };
        seen += 1;
        let v = i64::from(*s) * i64::try_from(amp).expect("amplitude fits");
        let q = i64::try_from(R::MODULUS).expect("modulus fits i64");
        out[i] = R::from(v.rem_euclid(q) as u64);
    }
    Ok(PolyRing::from_coefficients(out))
}

/// `‖c‖₂` of a ring element, in centered integer arithmetic.
#[must_use]
pub fn l2_norm<R: CenteredRing, const D: usize>(c: &Elt<R, D>) -> u64 {
    let sum: u64 = c
        .coefficients()
        .iter()
        .map(|x| {
            let v = i64::from(x.centered());
            (v * v) as u64
        })
        .sum();
    integer_sqrt(sum)
}

/// Floor square root (no `libm` needed, so it works in `no_std`).
#[must_use]
pub fn integer_sqrt(x: u64) -> u64 {
    if x < 2 {
        return x;
    }
    let mut r = x;
    let mut s = (x + 1) / 2;
    while s < r {
        r = s;
        s = (r + x / r) / 2;
    }
    r
}

/// Ceiling square root of a `u128`, by Newton iteration with an exact check,
/// so a bound rounded through it is never understated.
#[must_use]
pub fn ceil_sqrt(x: u128) -> u128 {
    if x < 2 {
        return x;
    }
    let mut r = x;
    let mut s = (r + 1) / 2;
    while s < r {
        r = s;
        s = (r + x / r) / 2;
    }
    if r * r == x {
        r
    } else {
        r + 1
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::encoding::{ring_from_u32, ring_to_u32};
    use crate::pcs::{RingElt, Z1Coeff, DIM};
    use algebra::crypto::xof::Shake256Xof;
    use algebra::ring::zq::Zq;

    /// Prime, `≡ 5 (mod 8)` (so `X^D + 1` has no NTT and Lemma 1's regime is
    /// the one the soundness argument lives in), small enough to keep the
    /// recursion interactive.
    type Q5 = Zq<4093>;
    const MOD8: u64 = 4_093;
    const DS: usize = 4;
    const L: usize = 12; // ceil(log2 4093)
    const N: usize = 8;

    fn c5(v: u64) -> Q5 {
        Q5::from(v % MOD8)
    }

    fn e5(coeffs: &[i64]) -> Elt<Q5, DS> {
        PolyRing::from_coefficients(
            coeffs
                .iter()
                .map(|&v| c5(v.rem_euclid(i64::try_from(MOD8).unwrap()) as u64))
                .collect(),
        )
    }

    /// A deterministic pseudo-random ring vector (LCG on the scalar slots).
    fn vec_of(len: usize, tag: u64) -> Vec<Elt<Q5, DS>> {
        (0..len)
            .map(|p| {
                let coeffs: Vec<i64> = (0..DS)
                    .map(|t| {
                        let x = tag
                            .wrapping_mul(6364136223846793005)
                            .wrapping_add(p as u64 * 31 + t as u64 * 17)
                            >> 33;
                        (x % MOD8) as i64
                    })
                    .collect();
                e5(&coeffs)
            })
            .collect()
    }

    fn vars_geometric(base: u64, count: usize) -> Vec<Q5> {
        geometric_vars::<Q5>(c5(base), count)
    }

    #[test]
    fn geometric_vars_collapse_the_mle_product_to_a_power() {
        // The equivalence the whole weight builder rests on: with
        // vars[b] = base^{2^b}, `mle_value(vars, i)` is `base^i`. If the bit
        // indexing were reversed this breaks for every non-power-of-two i.
        let vars = vars_geometric(7, 10);
        for i in 0..300usize {
            assert_eq!(
                mle_value(&vars, i).unwrap(),
                c5(7).pow(i as u64),
                "mle_value({i})"
            );
        }
    }

    #[test]
    fn mle_value_is_the_multilinear_extension_vector() {
        // Independent of `geometric_vars`: with per-bit variables, index i's
        // value must be the product of the variables its set bits name.
        let vars: Vec<Q5> = (0..6).map(|b| c5(2 + b as u64 * 3)).collect();
        assert_eq!(mle_value(&vars, 0).unwrap(), Q5::ONE);
        assert_eq!(mle_value(&vars, 1).unwrap(), vars[0]);
        assert_eq!(mle_value(&vars, 2).unwrap(), vars[1]);
        assert_eq!(mle_value(&vars, 5).unwrap(), vars[0] * vars[2]);
        let all: Q5 = vars.iter().fold(Q5::ONE, |acc, v| acc * *v);
        assert_eq!(mle_value(&vars, 63).unwrap(), all);
        // a variable beyond `vars` is refused, not silently truncated
        assert_eq!(
            mle_value(&vars[..2], 8),
            Err(FoldError::BadWeights {
                reason: "vars shorter than the index needs"
            })
        );
    }

    #[test]
    fn flat_weights_are_the_plain_power_vector_over_the_witness() {
        // The binarity/range weight: `digits = 1`, so the scalar index of
        // element p, slot t is p·D + t and its weight is base^(p·D+t).
        let base = 5u64;
        let block = L;
        let rounds = 3;
        let len = (1usize << rounds) * 2 * block;
        let w = LinearWeights::<Q5, DS>::geometric(c5(base), 1, block, rounds).expect("built");
        assert_eq!(w.len(), len);
        let full = w.weight(rounds).expect("full");
        for (p, e) in full.iter().enumerate() {
            for (t, coeff) in e.coefficients().iter().enumerate() {
                assert_eq!(*coeff, c5(base).pow((p * DS + t) as u64), "index {p},{t}");
            }
        }
    }

    #[test]
    fn digit_axis_absorbs_the_base_two_weights() {
        // The pulled-back weight: element index p = value·digits + k carries
        // 2^k · base^{value·D + t}. This is what lets a claim about a value
        // vector be re-expressed against its decomposition.
        let base = 3u64;
        let digits = L;
        let block = L;
        let rounds = 2;
        let w = LinearWeights::<Q5, DS>::geometric(c5(base), digits, block, rounds).expect("built");
        for (e_idx, e) in w.a0().iter().enumerate() {
            for (t, coeff) in e.coefficients().iter().enumerate() {
                let value = e_idx / digits;
                let k = e_idx % digits;
                assert_eq!(
                    *coeff,
                    c5(1u64 << k) * c5(base).pow((value * DS + t) as u64),
                    "a0[{e_idx},{t}]"
                );
            }
        }
    }

    #[test]
    fn nesting_a_weight_halves_it_exactly() {
        // The recursion's correctness depends on `weight(j-1)` being the *left
        // half* of `weight(j)`: that is what makes the child weight free.
        let w = LinearWeights::<Q5, DS>::geometric(c5(11), 1, L, 3).expect("built");
        for j in 1..=3usize {
            let big = w.weight(j).expect("nested");
            let small = w.weight(j - 1).expect("child");
            assert_eq!(big.len(), 2 * small.len());
            let half = big.len() / 2;
            assert_eq!(&big[..half], &small[..], "left half at nesting {j}");
        }
        assert_eq!(
            w.weight(4),
            Err(FoldError::WrongLength {
                got: 4,
                expected: 3,
                slot: "weight nesting"
            })
        );
    }

    #[test]
    fn beta_names_the_factor_the_round_peels() {
        let w = LinearWeights::<Q5, DS>::geometric(c5(6), 1, L, 3).expect("built");
        // alpha_{rounds-round+1} = (1, vars[... + rounds-round]) : round 1
        // peels the outermost (largest) factor.
        assert_eq!(w.beta(1).unwrap()[1].coefficients()[0], w.ratios()[2]);
        assert_eq!(w.beta(3).unwrap()[1].coefficients()[0], w.ratios()[0]);
        assert_eq!(w.beta(1).unwrap()[0], constant::<Q5, DS>(Q5::ONE));
        assert!(w.beta(0).is_err() && w.beta(4).is_err());
    }

    #[test]
    fn univariate_evaluation_is_a_linear_claim_on_the_decomposition() {
        // The load-bearing reduction: with a base-`2` decomposition `s` of the
        // coefficient vector, `ct(⟨s, W⟩) = f(u)` — the evaluation becomes a
        // public-weight linear constraint. A wrong `digit_axis` or a swapped
        // kron order breaks this.
        let u = 123u64;
        let f: Vec<Q5> = (0..N * DS)
            .map(|i| c5((i as u64 * 37 + 9) % MOD8))
            .collect();
        let values: Vec<Elt<Q5, DS>> = pack(&f);
        let s: Vec<Elt<Q5, DS>> = crate::pcs::gadget::split::<Q5, DS, 2, L>(&values);
        let rounds = (N / 2).trailing_zeros() as usize; // log N - 1
        let w = LinearWeights::<Q5, DS>::geometric(c5(u), L, L, rounds).expect("eval weights");
        assert_eq!(w.len(), s.len());
        let full = w.weight(rounds).expect("full");
        let direct: Q5 = f
            .iter()
            .enumerate()
            .fold(Q5::ZERO, |acc, (i, &v)| acc + v * c5(u).pow(i as u64));
        assert_eq!(scalar_pairing(&s, &full), direct, "ct<s,W> must be f(u)");
    }

    #[test]
    fn the_linear_recursion_carries_from_exposure_to_base() {
        // Full Fig. 3 sequence: expose, recurse `rounds-1` times, then the base
        // pairing on the folded state. Each of the four checks is exercised,
        // and the challenge used at each round is the one that folded the state.
        let w = LinearWeights::<Q5, DS>::geometric(c5(13), 1, L, 3).expect("built");
        let state0 = vec_of(w.len(), 4);
        let claim = scalar_pairing(&state0, &w.weight(3).unwrap());
        let cs: Vec<[Elt<Q5, DS>; 2]> = (0..3)
            .map(|i| [e5(&[3, 0, 0, 0]), e5(&[i as i64 + 2, 0, 0, 0])])
            .collect();
        let mut state = state0.clone();
        let mut msgs: Vec<[Elt<Q5, DS>; 2]> = Vec::new();
        for round in 1..=3usize {
            let child = w.weight(3 - round).unwrap();
            let msg = linear_msg(&state, &child).expect("sized");
            msgs.push(msg.clone());
            if round == 1 {
                linear_expose(&w.beta(1).unwrap(), &msg, claim).expect("exposure");
            } else {
                linear_recursion(
                    &w.beta(round).unwrap(),
                    &msg,
                    &msgs[round - 2],
                    &cs[round - 2],
                    round,
                )
                .expect("recursion");
            }
            let half = state.len() / 2;
            state = crate::pcs::leveled::fold_with(&state[..half], &state[half..], &cs[round - 1]);
        }
        linear_base(&state, w.a0(), &msgs[2], &cs[2]).expect("base pairing");

        // and a tampered message is caught by the *next* check, not silently
        let mut bad = msgs[1].clone();
        bad[0] = bad[0].clone() + e5(&[1, 0, 0, 0]);
        assert_eq!(
            linear_recursion(&w.beta(2).unwrap(), &bad, &msgs[0], &cs[0], 2),
            Err(FoldError::RecursionMismatch { round: 2 })
        );
    }

    #[test]
    fn exposure_rejects_a_false_claim_with_its_own_error() {
        let w = LinearWeights::<Q5, DS>::geometric(c5(13), 1, L, 1).expect("built");
        let state = vec_of(w.len(), 5);
        let msg = linear_msg(&state, w.a0()).expect("sized");
        let true_claim = scalar_pairing(&state, &w.weight(1).unwrap());
        linear_expose(&w.beta(1).unwrap(), &msg, true_claim).expect("honest");
        let wrong = true_claim + c5(1);
        assert!(matches!(
            linear_expose(&w.beta(1).unwrap(), &msg, wrong),
            Err(FoldError::ClaimMismatch { .. })
        ));
    }

    #[test]
    fn bilinear_fold_identity_holds_for_distinct_arguments() {
        // ⟨c₀u_L+c₁u_R, σ(c₀v_L+c₁v_R)⟩ == Σ c̃ⱼ·msgⱼ with `u ≠ v`. The repo's
        // concrete self_ip already tests `u = v`; the binarity sub-proof needs
        // the cross case, so it is asserted here rather than assumed.
        for tag in 0..3u64 {
            let u = vec_of(8, tag);
            let v = vec_of(8, tag + 100);
            let msg = quad_msg(&u, &v).expect("sized");
            let c = [e5(&[2, 1, 0, 3]), e5(&[0, 5, 1, 0])];
            let half = 4;
            let un = crate::pcs::leveled::fold_with(&u[..half], &u[half..], &c);
            let vn = crate::pcs::leveled::fold_with(&v[..half], &v[half..], &c);
            // the verifier's own carry: round i+1's L+R against c̃·(msg)_i
            let next = quad_msg(&un, &vn).expect("folded states halve");
            quad_carry(&next, &msg, &c, 2).expect("bilinear carry");
            quad_base(&un, &vn, &msg, &c).expect("base form of the same identity");
            // the exposure is ct(L+R) == ct(<u,σ(v)>)
            quad_expose(&msg, u64::try_from(ct(&herm(&u, &v)).to_u128()).unwrap(), 1)
                .expect("exposure");
        }
    }

    #[test]
    fn self_pairing_constant_term_is_the_integer_sum_of_squares() {
        // What turns the ring identity into a *norm* statement.
        let v = vec_of(5, 42);
        let flat = flatten(&v);
        let expect: u64 = flat
            .iter()
            .map(|x: &Q5| {
                let z = i64::from(x.centered());
                (z * z) as u64
            })
            .sum::<u64>()
            % MOD8;
        assert_eq!(
            u64::try_from(ct::<Q5, DS>(&herm(&v, &v)).to_u128()).unwrap(),
            expect
        );
        // `square_sum` keeps the *integer* value, not its residue.
        let exact: u128 = flat
            .iter()
            .map(|x: &Q5| u128::from(x.abs_infinity()) * u128::from(x.abs_infinity()))
            .sum();
        assert_eq!(square_sum(&v).unwrap(), exact);
    }

    #[test]
    fn generic_herm_matches_the_concrete_self_ip_form() {
        // `shortness::self_ip::hermitian` is pinned to the crate's Z1 ring; the
        // generic form here must be the same function, or the two would drift.
        let mk = |tag: u64| -> Vec<RingElt> {
            (0..4)
                .map(|p| {
                    let coeffs: Vec<u32> = (0..DIM)
                        .map(|t| ((tag * 977 + p as u64 * 71 + t as u64 * 13) % 5000) as u32)
                        .collect();
                    ring_from_u32::<Z1Coeff, DIM>(&coeffs.try_into().expect("DIM coeffs"))
                })
                .collect()
        };
        let u = mk(1);
        let v = mk(2);
        let generic = herm(&u, &v);
        let concrete = crate::shortness::self_ip::hermitian(&u, &v);
        assert_eq!(
            ring_to_u32::<Z1Coeff, DIM>(&generic),
            ring_to_u32::<Z1Coeff, DIM>(&concrete)
        );
        assert_eq!(
            u64::try_from(ct::<Z1Coeff, DIM>(&generic).to_u128()).expect("reduced"),
            crate::shortness::self_ip::constant_term(&generic)
        );
    }

    #[test]
    fn binarity_holds_under_the_randomized_identity_and_breaks_otherwise() {
        // The randomized check `⟨s̆∘α, s̆⟩ = ⟨s̆, α⟩` is equivalent to
        // `⟨α, s̆∘(s̆−1)⟩ = 0` — exact for binary vectors, and with a single
        // non-binary coordinate it is a nonzero polynomial in α of degree < the
        // coordinate count, so a fixed α must catch it.
        let alpha = c5(91);
        let block = 2;
        let s: Vec<Elt<Q5, DS>> = (0..8)
            .map(|p| e5(&[(p % 2) as i64, ((p / 2) % 2) as i64, 0, 1]))
            .collect();
        let w = LinearWeights::<Q5, DS>::geometric(alpha, 1, block, 1).expect("built");
        let full = w.weight(1).unwrap();
        let lhs = scalar_pairing(&hadamard(&s, &full), &s);
        let rhs = scalar_pairing(&s, &full);
        assert_eq!(lhs, rhs, "binary witness satisfies the identity");
        let mut bad = s.clone();
        bad[3] = bad[3].clone() + e5(&[1, 0, 0, 0]);
        assert_ne!(
            scalar_pairing(&hadamard(&bad, &full), &bad),
            scalar_pairing(&bad, &full),
            "one coordinate of magnitude 2 must break it at this alpha"
        );
    }

    #[test]
    fn norm_growth_follows_the_double_and_multiply_rule() {
        let na = NormAccounting {
            rounds: 3,
            t_op: 3,
            initial: 1,
            base_len: 2 * L,
        };
        // γ_{i+1} = 2T·γ_i from γ₁ = 1 ⇒ γ_logN = (2T)^rounds.
        assert_eq!(na.coord_bound(), 6u64.pow(3));
        assert_eq!(
            na.bound_sq(),
            2 * u128::from(2 * L as u64) * u128::from(6u64.pow(3)) * u128::from(6u64.pow(3))
        );
        // An operator norm of 1 keeps a binary witness binary.
        let mild = NormAccounting {
            rounds: 3,
            t_op: 1,
            initial: 1,
            base_len: 2,
        };
        assert_eq!(mild.coord_bound(), 8);
    }

    #[test]
    fn square_sum_admissibility_is_a_hard_window_not_a_warning() {
        // 384 coordinates of magnitude 1 square to 384 < q, so the direct
        // route decides; 2047 coordinates do not, and the gate must refuse.
        assert!(square_sum_admissible::<Q5>(384, 1));
        assert!(!square_sum_admissible::<Q5>(4093, 1));
        // The window is `count · max² < q`, so at magnitude 6 it closes at
        // count 114 (113·36 = 4068 < 4093 ≤ 4104 = 114·36).
        assert!(square_sum_admissible::<Q5>(100, 6));
        assert!(square_sum_admissible::<Q5>(113, 6));
        assert!(!square_sum_admissible::<Q5>(114, 6));
    }

    #[test]
    fn repetitions_meet_the_target_by_construction() {
        // t = ⌈target / log₂(den/num)⌉ and (num/den)^t <= 2^-target.
        let (reps, log_err) = NormAccounting::repetitions(768, MOD8, 8).expect("advantage");
        assert_eq!(reps, 4);
        assert!(log_err >= 8, "residual {log_err} bits, want >= 8");
        assert_eq!(
            NormAccounting::repetitions(5, 5, 8),
            None,
            "a check with no advantage cannot be repeated into soundness"
        );
        let (one, _) = NormAccounting::repetitions(1, 1024, 10).expect("strong");
        assert_eq!(
            one, 1,
            "a 2^-10 error needs one repetition for a 10-bit target"
        );
    }

    #[test]
    fn pool_challenges_have_the_declared_shape_and_operator_norm() {
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(b"pool");
        let mut stream = BitStream::new(&mut xof);
        for _ in 0..20 {
            let c: Elt<Q5, DS> = pool_challenge(&mut stream, 1, 1).expect("fits");
            let mut ones = 0;
            let mut twos = 0;
            let mut l1 = 0u64;
            for x in c.coefficients() {
                let m = x.abs_infinity();
                match m {
                    0 => {}
                    1 => ones += 1,
                    2 => twos += 1,
                    _ => panic!("coefficient {m} outside the pool"),
                }
                l1 += m;
            }
            assert_eq!(ones, 1);
            assert_eq!(twos, 1);
            // ‖c‖_{op,∞} <= ‖c‖₁ = w1 + 2w2, which is the T the accounting uses.
            assert_eq!(l1, 3);
        }
        assert_eq!(
            pool_challenge::<Q5, _, DS>(&mut stream, 3, 2),
            Err(FoldError::ChallengeOutOfPool),
            "more non-zero slots than the ring has must be refused"
        );
    }

    #[test]
    fn differences_of_pool_challenges_stay_invertible_bounded() {
        // Lemma 1's regime: 0 < ‖c − c'‖₂ <= 4·sqrt(2(w1+w2)) < sqrt(q/2).
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(b"diff");
        let mut stream = BitStream::new(&mut xof);
        let bound = 4 * integer_sqrt(2 * (1 + 1));
        assert!((u128::from(bound) * u128::from(bound)) < u128::from(MOD8 / 2));
        for _ in 0..30 {
            let a: Elt<Q5, DS> = pool_challenge(&mut stream, 1, 1).expect("a");
            let b: Elt<Q5, DS> = pool_challenge(&mut stream, 1, 1).expect("b");
            let d = a.clone() - b.clone();
            let n = l2_norm(&d);
            if a != b {
                assert!(n > 0 && n <= bound, "‖a−b‖₂ = {n} against {bound}");
            }
        }
    }

    #[test]
    fn weight_builders_refuse_impossible_axes() {
        assert_eq!(
            LinearWeights::<Q5, DS>::geometric(c5(3), 0, 12, 1),
            Err(FoldError::BadWeights {
                reason: "digits must be in 1..=64 (the plane weight is 2^(e mod digits))"
            })
        );
        assert_eq!(
            LinearWeights::<Q5, DS>::geometric(c5(3), 65, 130, 1),
            Err(FoldError::BadWeights {
                reason: "digits must be in 1..=64 (the plane weight is 2^(e mod digits))"
            }),
            "the shift that forms 2^(e mod digits) is the real limit"
        );
        // A digit axis that is not a power of two is legal: Serval's plane
        // count is ⌈log₂ q⌉, and the builder only divides and modulos by it.
        assert!(LinearWeights::<Q5, DS>::geometric(c5(3), 3, 12, 1).is_ok());
        assert_eq!(
            LinearWeights::<Q5, DS>::geometric(c5(3), 8, 4, 1),
            Err(FoldError::BadWeights {
                reason: "digits must divide block"
            })
        );
        // The multilinear builder refuses a variable list too short to name
        // every axis bit: `2·block·D` innermost elements doubled `rounds` times
        // need `1 + log₂(block·D) + rounds` variables.
        assert_eq!(
            LinearWeights::<Q5, DS>::multilinear(&vars_geometric(3, 4), 4, 4),
            Err(FoldError::BadWeights {
                reason: "vars must cover every axis bit"
            })
        );
        assert!(LinearWeights::<Q5, DS>::multilinear(&vars_geometric(3, 20), 4, 4).is_ok());
        assert_eq!(
            LinearWeights::<Q5, DS>::multilinear(&vars_geometric(3, 20), 3, 1),
            Err(FoldError::BadWeights {
                reason: "block and ring degree must be powers of two"
            })
        );
    }

    #[test]
    fn multilinear_on_geometric_vars_is_the_geometric_builder() {
        // The two specializations must agree where both are defined, so
        // `mle_value` cannot silently differ from `base^i`.
        let base = c5(17);
        let g = LinearWeights::<Q5, DS>::geometric(base, 1, 2, 3).expect("geom");
        let m = LinearWeights::<Q5, DS>::multilinear(&geometric_vars(base, 20), 2, 3).expect("mle");
        assert_eq!(g.a0(), m.a0());
        assert_eq!(g.ratios(), m.ratios());
    }

    #[test]
    fn multilinear_weights_are_the_mle_evaluation_vector() {
        // Independent of `geometric`: entry (e, t) of the innermost factor must
        // be the product of the variables that index e·D + t names.
        let vars: Vec<Q5> = (0..8).map(|b| c5(2 + b as u64 * 5)).collect();
        let w = LinearWeights::<Q5, DS>::multilinear(&vars, 1, 2).expect("built");
        // `len()` is the whole witness: `2·block` innermost elements, doubled
        // once per round.
        assert_eq!(w.len(), 8);
        for (e, row) in w.a0().iter().enumerate() {
            for (t, coeff) in row.coefficients().iter().enumerate() {
                assert_eq!(*coeff, mle_value(&vars, e * DS + t).unwrap(), "{e},{t}");
            }
        }
        // and the full weight really is the kron of the (1, ratio) pairs
        let full = w.weight(2).unwrap();
        assert_eq!(full.len(), 8);
        let expect = kron(
            &[
                constant::<Q5, DS>(Q5::ONE),
                constant::<Q5, DS>(w.ratios()[1]),
            ],
            &w.weight(1).unwrap(),
        );
        assert_eq!(full, expect, "the outer factor must be (1, ratio)");
        assert_eq!(w.beta(1).unwrap()[1].coefficients()[0], w.ratios()[1]);
    }

    #[test]
    fn linear_msg_rejects_a_weight_that_is_not_half_the_state() {
        assert!(matches!(
            linear_msg(&vec_of(8, 1), &vec_of(5, 2)),
            Err(FoldError::WrongLength { .. })
        ));
        assert!(matches!(
            linear_msg::<Q5, DS>(&[], &[]),
            Err(FoldError::WrongLength { .. })
        ));
    }

    #[test]
    fn quad_msg_rejects_an_odd_or_empty_state() {
        assert!(matches!(
            quad_msg::<Q5, DS>(&[], &[]),
            Err(FoldError::WrongLength { .. })
        ));
        let v = vec_of(3, 7);
        assert!(matches!(
            quad_msg(&v, &v),
            Err(FoldError::WrongLength { .. })
        ));
    }
}
