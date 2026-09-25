//! Quadratic dot-product constraints and the amortized opening that proves
//! them (LaBRADOR §5, eprint 2022/1341): the *principal relation* `R`, the
//! aggregation of its two function families, and the verifier's equation set.
//!
//! # What this module is
//!
//! [`crate::pcs`] is the home of claim structures — shapes a scheme commits
//! to and later proves statements about. [`Pcs`](crate::pcs::Pcs) proves
//! `y = f(x)`, [`WeightPcs`](crate::pcs::WeightPcs) proves `y = ⟨w, F⟩`, and
//! this module proves the shape LaBRADOR works in: a system of **quadratic
//! dot-product constraints**
//!
//! ```text
//! f(s_1..s_r) = Σ_{i,j} a_ij·⟨s_i, s_j⟩ + Σ_i ⟨φ_i, s_i⟩ − b = 0   in R_q
//! f'(s_1..s_r)                                        ct(…) = 0    in Z_q
//! ```
//!
//! over `R_q = Z_q[X]/(X^D + 1)`, with short `s_1, …, s_r ∈ R_q^n` satisfying
//! `Σ_i ‖s_i‖₂² ≤ β²`. That is the paper's Section 5.1 relation `R`: the
//! family `F` must vanish in `R_q`, the family `F'` only needs a zero
//! **constant term**, and the norm bound is one global `l2` budget.
//! Everything here is generic in the scalar ring `R` and the ring degree `D`.
//! The paper instantiates `D = 64` with a prime `q ≈ 2^32` for which `X^64+1`
//! splits into two degree-32 factors
//! ([`algebra::ring::number_theory::x_pow_d_plus_1_splitting`]); none of this
//! assumes the crate's `Z1`/`d = 256` constants.
//!
//! # The core argument (Figures 2 and 3)
//!
//! [`prove_core`] walks the paper's prover messages in order (committing the
//! inner `tᵢ = A·sᵢ` and the outer `u₁`, projecting, aggregating twice,
//! committing `u₂`, amortizing); [`verify_core_report`] evaluates Figure 3's
//! lines 3–20 and returns *every* rejection, of which [`verify_core`] reports
//! the first. Each check has its own rejection variant, so a tampered component
//! is attributable:
//!
//! | paper check | [`CoreError`] variant |
//! |---|---|
//! | Fig. 2 `‖p‖₂ ≤ √128·β` | `ProjectionNorm` |
//! | Fig. 2 `ct(b''(k)) = ⟨ω,p⟩ + Σψ·b'₀` | `AggregationConstantTerm` |
//! | 8, 9 `g_ij = g_ji`, `h_ij = h_ji` | `AsymmetricGarbage` |
//! | 10–13 digit decompositions recombine; every plane within `b/2` | `DigitRecombination`, `DigitBound` |
//! | 14 consolidated norm check (5) | `NormBudget` |
//! | 15 `A·z = Σ cᵢtᵢ` | `InnerLink` |
//! | 16 `⟨z,z⟩ = Σ g_ij cᵢc_j` | `SelfInnerProduct` |
//! | 17 `Σ⟨φᵢ,z⟩cᵢ = Σ h_ij cᵢc_j` | `LinearClaim` |
//! | 18 `Σ a_ij g_ij + Σ hᵢᵢ = b` | `Relation` |
//! | 19, 20 outer commitments `u₁`, `u₂` | `OuterCommitment1`, `OuterCommitment2` |
//!
//! Reporting the whole set is not a nicety: under Fiat–Shamir a tampered `u₁`
//! changes every later challenge, so a single-error verifier reports whichever
//! check happens to run first and leaves the checks behind it
//! indistinguishable from checks that never run. The tests enumerate which
//! rejections each tamper actually produces.
//!
//! # The recursion (§3 composed with §5.3)
//!
//! One execution is a proof-of-knowledge *reduction*: Figure 3 checks that its
//! last message is a witness for the *target relation*, which is another instance
//! of `R`, so Lemma 3.7 composes the protocol with itself and each level takes
//! the witness from `r·n` ring elements to `2n + m` (Sections 5.3, 5.7).
//! [`derive_view`] is the verifier's recomputation (Def. 3.5's `Ṽ`),
//! [`TargetShape`] is §5.3's reblocking, [`target_instance`] builds the
//! `κ+κ₁+κ₂+3` equations of eq. (6), and [`TargetInstance::check_honest`] *is*
//! the factoring condition. [`SizeModel`] and [`RecursionPlan`] then decide, in
//! §5.7's own arithmetic, whether a level should recurse at all, and
//! [`recursion_msis_norm_sq`] tracks the Module-SIS bound that Remark 5.2 makes
//! grow with depth.
//!
//! Still not here: driving several levels from inside the crate (an example wires
//! them), §5.6's last-level variant that drops the outer commitments and cuts the
//! garbage from `(r²+r)/2` to `2r−1` terms, and growing `κ, κ₁, κ₂` per level as
//! §6.1 does for 128-bit security. [`verify_core`] still checks the target
//! relation's norm directly (line 14), so a single execution leaves the prover
//! sending `z, t, g, h`. The same gap is recorded in
//! [`crate::pcs::greyhound`] and [`crate::opening`].
//!
//! # Norm accounting (§5.4, Theorem 5.1)
//!
//! [`NormBounds::derive`] implements the paper's parameter rules —
//! `b = (12·s²·r·τ)^{1/4}`, `t₁` the planes whose digit *span* covers `q/2`
//! (the paper's `⌈log q/log b⌉`, which the balanced digit set needs in span
//! form), `t₂ = ⌈log(√(24·n·d)·s²)/log b⌉`, `γ² = β²τ`,
//! `β'² = 2γ²/b² + γ₁² + γ₂²` — in exact integer arithmetic, and
//! [`prove_core`] restarts the projection draw when an honest run overruns
//! `β'`, which is the paper's own remedy ("the prover needs to either restart
//! the protocol until the vectors are short enough, or increase the commitment
//! parameters dynamically"). [`NormBounds::slack_condition`] is Theorem 5.1's
//! precondition `β ≤ √(30/128)·q/125`, which is what lets the verifier read
//! the projection response `p` back as an *integer* (Lemma 4.2).

use crate::foundation::sampling::{fixed_weight_signs, from_centered, uniform_vec_from_seed};
use crate::pcs::key::{apply_blockwise, RingMatrixKey};
use crate::pcs::packing::sigma_of;
use algebra::crypto::sampling::{sample_uniform_coeff, BitStream};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::{vec, vec::Vec};
use core::fmt;

/// One ring element of `R_q = Z_q[X]/(X^D + 1)`.
pub type Elt<R, const D: usize> = PolyRing<R, D>;
/// One witness vector `sᵢ ∈ R_q^n`, as `n` ring elements.
pub type WitnessVec<R, const D: usize> = Vec<Elt<R, D>>;

/// The additive identity of `R_q`.
pub fn zero_elt<R: Ring, const D: usize>() -> Elt<R, D> {
    PolyRing::from_coefficients(vec![R::ZERO; D])
}

/// The ring element with the integer `m` in its constant term.
pub fn const_elt<R: Ring, const D: usize>(m: i64) -> Elt<R, D> {
    let mut coeffs = vec![R::ZERO; D];
    coeffs[0] = from_centered::<R>(m);
    PolyRing::from_coefficients(coeffs)
}

/// The centered integer representatives of a ring element's coefficients.
pub fn centered_coeffs<R: Ring + CenteredRing, const D: usize>(x: &Elt<R, D>) -> [i64; D] {
    let mut out = [0i64; D];
    for (dst, c) in out.iter_mut().zip(x.coefficients().iter()) {
        *dst = c.centered();
    }
    out
}

/// `ct(·)`, the constant coefficient of a ring element.
pub fn constant_term<R: Ring, const D: usize>(x: &Elt<R, D>) -> R {
    x.coefficients().first().copied().unwrap_or(R::ZERO)
}

/// Squared `l2` norm of a ring vector over the centered integer
/// representatives — the norm the paper's `‖·‖₂` bounds quantify.
pub fn norm_sq<R: Ring + CenteredRing, const D: usize>(v: &WitnessVec<R, D>) -> u128 {
    squared_norm_of(v.iter().flat_map(|e| e.coefficients()))
}

fn squared_norm_of<R: Ring + CenteredRing>(cs: impl Iterator<Item = R>) -> u128 {
    cs.map(|c| {
        let a = u128::from(c.centered().unsigned_abs());
        a * a
    })
    .sum()
}

/// `Σᵢ ‖sᵢ‖₂²` over a whole witness.
pub fn witness_norm_sq<R: Ring + CenteredRing, const D: usize>(s: &[WitnessVec<R, D>]) -> u128 {
    s.iter().map(norm_sq).sum()
}

/// The ring-valued inner product `⟨a, b⟩ = Σ_k a_k·b_k ∈ R_q`.
pub fn inner_product<R: Ring, const D: usize>(a: &[Elt<R, D>], b: &[Elt<R, D>]) -> Elt<R, D> {
    assert_eq!(a.len(), b.len(), "inner product of mismatched vectors");
    let mut acc = zero_elt::<R, D>();
    for (x, y) in a.iter().zip(b.iter()) {
        acc += x.clone() * y.clone();
    }
    acc
}

/// The coefficient inner product `Σ_m a_m·b_m ∈ Z_q` of two ring vectors,
/// computed through the σ-pairing as the paper prescribes:
/// `⟨⃗a, ⃗b⟩ = ct(⟨σ⁻¹(a⃗), b⃗⟩)` with `σ: X ↦ X⁻¹` of order two.
pub fn scalar_inner_product<R: Ring + CenteredRing, const D: usize>(
    a: &WitnessVec<R, D>,
    b: &WitnessVec<R, D>,
) -> R {
    let mut acc = R::ZERO;
    for (x, y) in a.iter().zip(b.iter()) {
        acc += constant_term(&sigma_of(x).mul_ref(&y.clone()));
    }
    acc
}

/// `a·b` without consuming either side.
///
/// `PolyRing` only implements `Mul<Elt>` by value, so a by-reference product
/// needs the two clones; spelling it once keeps the call sites readable.
pub trait MulRef<R: Ring, const D: usize> {
    /// `self · other`.
    fn mul_ref(&self, other: &Elt<R, D>) -> Elt<R, D>;
}
impl<R: Ring, const D: usize> MulRef<R, D> for Elt<R, D> {
    fn mul_ref(&self, other: &Elt<R, D>) -> Elt<R, D> {
        self.clone() * other.clone()
    }
}

/// A family-`F` function: `Σ a_ij⟨sᵢ,sⱼ⟩ + Σ⟨φᵢ,sᵢ⟩ − b`, vanishing in `R_q`.
/// `(a_ij)` is symmetric, which the paper states is without loss of
/// generality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuadFn<R: Ring, const D: usize> {
    /// Symmetric coefficient matrix `(a_ij) ∈ R_q^{r×r}`.
    pub a: Vec<Vec<Elt<R, D>>>,
    /// Linear coefficients `(φᵢ) ∈ R_q^{r×n}`.
    pub phi: Vec<WitnessVec<R, D>>,
    /// Right-hand side `b ∈ R_q`.
    pub b: Elt<R, D>,
}

impl<R: Ring, const D: usize> QuadFn<R, D> {
    /// The zero-coefficient function of shape `(r, n)`.
    pub fn blank(r: usize, n: usize) -> Self {
        Self {
            a: vec![vec![zero_elt::<R, D>(); r]; r],
            phi: vec![vec![zero_elt::<R, D>(); n]; r],
            b: zero_elt::<R, D>(),
        }
    }

    /// `Σ a_ij⟨sᵢ,sⱼ⟩ + Σ⟨φᵢ,sᵢ⟩`, i.e. the function without its `− b`.
    pub fn lhs(&self, s: &[WitnessVec<R, D>]) -> Elt<R, D> {
        let mut acc = zero_elt::<R, D>();
        for (i, row) in self.a.iter().enumerate() {
            for (j, a_ij) in row.iter().enumerate() {
                if !a_ij.is_zero() {
                    acc += inner_product(&s[i], &s[j]).mul_ref(a_ij);
                }
            }
        }
        for (i, phi_i) in self.phi.iter().enumerate() {
            acc += inner_product(phi_i, &s[i]);
        }
        acc
    }

    /// The value `lhs(s) − b`.
    pub fn value(&self, s: &[WitnessVec<R, D>]) -> Elt<R, D> {
        self.lhs(s) - self.b.clone()
    }
}

/// A family-`F'` function: same shape, but only its **constant term** must
/// vanish (the paper omits the higher coefficients of `b'` from the statement,
/// which matters when there are many).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtFn<R: Ring, const D: usize> {
    /// Symmetric coefficient matrix `(a'_ij)`.
    pub a: Vec<Vec<Elt<R, D>>>,
    /// Linear coefficients `(φ'_ᵢ)`.
    pub phi: Vec<WitnessVec<R, D>>,
    /// Constant term of the right-hand side.
    pub b0: R,
}

impl<R: Ring, const D: usize> CtFn<R, D> {
    /// The zero-coefficient function of shape `(r, n)`.
    pub fn blank(r: usize, n: usize) -> Self {
        Self {
            a: vec![vec![zero_elt::<R, D>(); r]; r],
            phi: vec![vec![zero_elt::<R, D>(); n]; r],
            b0: R::ZERO,
        }
    }
}

impl<R: Ring + CenteredRing, const D: usize> CtFn<R, D> {
    /// `ct(f′(s))`: the constant term of the value **minus** the claimed
    /// `b′₀`, which is the quantity the relation requires to be zero. `F′`
    /// stores only that scalar of the right-hand side because the higher
    /// coefficients of `b′` are irrelevant to the claim — the saving the paper
    /// makes when there are many such functions.
    pub fn constant_term(&self, s: &[WitnessVec<R, D>]) -> R {
        let mut acc = R::ZERO;
        for (i, row) in self.a.iter().enumerate() {
            for (j, a_ij) in row.iter().enumerate() {
                if !a_ij.is_zero() {
                    acc += constant_term(&inner_product(&s[i], &s[j]).mul_ref(a_ij));
                }
            }
        }
        for (i, phi_i) in self.phi.iter().enumerate() {
            acc += constant_term(&inner_product(phi_i, &s[i]));
        }
        acc - self.b0
    }
}

/// Why a witness fails the principal relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RelationError {
    /// A vector had the wrong number of ring elements.
    WrongShape {
        /// Length supplied.
        got: usize,
        /// Length the relation requires.
        expected: usize,
    },
    /// A family-`F` function did not vanish in `R_q`.
    FullConstraintNonZero {
        /// Index into `F`.
        index: usize,
    },
    /// A family-`F'` function had a non-zero constant term.
    ConstantTermNonZero {
        /// Index into `F'`.
        index: usize,
    },
    /// `Σᵢ ‖sᵢ‖₂² > β²`.
    NormExceeded {
        /// The witness's `Σᵢ ‖sᵢ‖₂²`.
        norm_sq: u128,
        /// The required `β²`.
        bound_sq: u128,
    },
}

impl fmt::Display for RelationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongShape { got, expected } => {
                write!(f, "witness vector of {got} elements against {expected}")
            }
            Self::FullConstraintNonZero { index } => {
                write!(f, "family-F constraint {index} does not vanish in R_q")
            }
            Self::ConstantTermNonZero { index } => {
                write!(
                    f,
                    "family-F' constraint {index} has a non-zero constant term"
                )
            }
            Self::NormExceeded { norm_sq, bound_sq } => {
                write!(f, "‖s‖₂² = {norm_sq} exceeds β² = {bound_sq}")
            }
        }
    }
}

/// The principal relation `R`: two function families and one norm budget.
#[derive(Debug, Clone)]
pub struct Relation<R: Ring, const D: usize> {
    /// Witness rank `n` (ring elements per vector).
    pub rank: usize,
    /// Multiplicity `r` (number of witness vectors).
    pub multiplicity: usize,
    /// Family `F`: functions vanishing in `R_q`.
    pub full: Vec<QuadFn<R, D>>,
    /// Family `F'`: functions with a vanishing constant term.
    pub ct_only: Vec<CtFn<R, D>>,
    /// `β²` in `Σᵢ ‖sᵢ‖₂² ≤ β²`.
    pub norm_bound_sq: u128,
}

impl<R: Ring + CenteredRing, const D: usize> Relation<R, D> {
    /// Checks `F`, `F'` and the norm bound — the relation as stated, which is
    /// what the *last* recursion level verifies directly.
    ///
    /// # Errors
    /// [`RelationError`] naming which of the three clauses failed, with the
    /// offending index.
    pub fn check(&self, s: &[WitnessVec<R, D>]) -> Result<(), RelationError> {
        if s.len() != self.multiplicity {
            return Err(RelationError::WrongShape {
                got: s.len(),
                expected: self.multiplicity,
            });
        }
        for v in s {
            if v.len() != self.rank {
                return Err(RelationError::WrongShape {
                    got: v.len(),
                    expected: self.rank,
                });
            }
        }
        for (k, f) in self.full.iter().enumerate() {
            if !f.value(s).is_zero() {
                return Err(RelationError::FullConstraintNonZero { index: k });
            }
        }
        for (l, f) in self.ct_only.iter().enumerate() {
            if f.constant_term(s) != R::ZERO {
                return Err(RelationError::ConstantTermNonZero { index: l });
            }
        }
        let norm_sq = witness_norm_sq(s);
        if norm_sq > self.norm_bound_sq {
            return Err(RelationError::NormExceeded {
                norm_sq,
                bound_sq: self.norm_bound_sq,
            });
        }
        Ok(())
    }
}

/// Runtime base-`b` digit decomposition with centered digits — the paper's
/// `v = v⁽⁰⁾ + v⁽¹⁾·b₁ + ⋯`, `‖v⁽ᵏ⁾‖∞ ≤ b₁/2`.
///
/// This is [`crate::pcs::gadget::split`] with a *runtime* base and plane
/// count: §5.4 derives `b₁, b₂, t₁, t₂` from the instance at every recursion
/// level, so they are instance data rather than compile-time constants. A test
/// pins the two implementations against each other at equal `(base, digits)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Decomposition {
    /// Digit base `b ≥ 2`.
    pub base: u64,
    /// Plane count `t`, with `b^t > q` so the expansion of a canonical
    /// representative is exact.
    pub digits: usize,
}

/// A digit decomposition failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DigitError {
    /// The planes' span does not reach the representative window, so the
    /// expansion recomposes to a different value.
    CapacityTooSmall {
        /// `base^digits`, saturating.
        capacity: u128,
        /// The modulus.
        modulus: u64,
    },
    /// A batch carried the wrong number of planes.
    WrongPlaneCount {
        /// Planes supplied.
        got: usize,
        /// Planes required.
        expected: usize,
    },
    /// A digit plane exceeded the centered half-width `b/2`.
    PlaneTooWide {
        /// Offending plane index within the batch of the first value.
        plane: usize,
        /// Largest digit magnitude seen.
        magnitude: u64,
        /// The allowed half-width `b/2`.
        half_width: u64,
    },
    /// The planes do not recombine to the claimed value.
    Recombination,
}

impl fmt::Display for DigitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CapacityTooSmall { capacity, modulus } => write!(
                f,
                "digit capacity {capacity} does not span the representatives of Z_{modulus}"
            ),
            Self::WrongPlaneCount { got, expected } => {
                write!(f, "{got} digit planes against {expected}")
            }
            Self::PlaneTooWide {
                plane,
                magnitude,
                half_width,
            } => write!(
                f,
                "digit plane {plane} has magnitude {magnitude} above the half-width {half_width}"
            ),
            Self::Recombination => write!(f, "digit planes do not recombine to the value"),
        }
    }
}

impl Decomposition {
    /// A new decomposition; [`Self::validate`] is the gate on exactness.
    pub const fn new(base: u64, digits: usize) -> Self {
        Self { base, digits }
    }

    /// `base^digits`, saturating at `u128::MAX`.
    pub const fn capacity(&self) -> u128 {
        let mut acc: u128 = 1;
        let mut k = 0;
        while k < self.digits {
            acc = match acc.checked_mul(self.base as u128) {
                Some(v) => v,
                None => return u128::MAX,
            };
            k += 1;
        }
        acc
    }

    /// The largest magnitude `digits` planes over `base` recombine to.
    #[must_use]
    pub fn span(&self) -> u128 {
        crate::pcs::gadget::digit_span_of(self.base, self.digits)
    }

    /// Whether *every* residue class of `R` decomposes exactly: the
    /// representative window a balanced base expands is `(q − 1)/2`, so this is
    /// the condition on the planes that cover a uniform `Z_q` object (`t⃗`, `h⃗`).
    #[must_use]
    pub fn covers_every_residue<R: Ring>(&self) -> bool {
        self.base >= 2
            && self.digits >= 1
            && self.span() >= crate::pcs::gadget::representative_ceiling_of(self.base, R::MODULUS)
    }

    /// Whether the integers in `[−magnitude, magnitude]` all decompose exactly.
    /// This is the criterion for a **short** object such as LaBRADOR's garbage
    /// `g⃗`, whose plane count `t₂` is budgeted by its own magnitude rather than
    /// by `q` (§5.4).
    #[must_use]
    pub fn covers_magnitude(&self, magnitude: u128) -> bool {
        self.base >= 2 && self.digits >= 1 && self.span() >= magnitude
    }

    /// Checks the decomposition is a positional system that covers every
    /// residue of `R`.
    ///
    /// # Errors
    /// [`DigitError::CapacityTooSmall`] — below that a representative would not
    /// fit and the split would silently recompose to a different value.
    pub fn validate<R: Ring>(&self) -> Result<(), DigitError> {
        if self.covers_every_residue::<R>() {
            Ok(())
        } else {
            Err(DigitError::CapacityTooSmall {
                capacity: self.capacity(),
                modulus: R::MODULUS,
            })
        }
    }

    /// Splits `values` into planes, layout `out[j·digits + k]` = plane `k` of
    /// `values[j]` (the [`crate::pcs::gadget::split`] layout). This *is*
    /// [`crate::pcs::gadget::digit_planes`], so the runtime-base and
    /// const-generic gadgets cannot drift.
    ///
    /// # Panics
    /// If some coefficient's least-absolute representative exceeds
    /// [`Self::span`] — which [`Self::validate`] rules out for a uniform
    /// object, and a §5.4 plane count `t₂` is meant to rule out for a short one.
    pub fn split<R: Ring + CenteredRing, const D: usize>(
        &self,
        values: &[Elt<R, D>],
    ) -> Vec<Elt<R, D>> {
        crate::pcs::gadget::digit_planes::<R, D>(values, self.base, self.digits)
    }

    /// Recombines one value's planes: `Σ_k b^k·plane_k`.
    pub fn join<R: Ring + CenteredRing, const D: usize>(&self, planes: &[Elt<R, D>]) -> Elt<R, D> {
        let mut acc = zero_elt::<R, D>();
        let mut weight: i64 = 1;
        for plane in planes {
            acc += plane.clone().mul_ref(&const_elt::<R, D>(weight));
            weight = weight.saturating_mul(i64::try_from(self.base).expect("base fits i64"));
        }
        acc
    }

    /// Figure 3 lines 11–13: the batch recombines and *every* plane is
    /// centered-bounded by `b/2`, which is how the paper states it ("where
    /// centered representatives modulo `b₁` are used, i.e. ‖t⁽ᵏ⁾‖∞ ≤ b₁/2").
    /// A plane beyond that bound cannot be produced by an exact split of a
    /// covered value, so this is what catches a prover that recomposes a
    /// longer object than `digits` planes can hold.
    ///
    /// # Errors
    /// [`DigitError`] naming the plane-count, width, or recombination failure.
    pub fn check<R: Ring + CenteredRing, const D: usize>(
        &self,
        values: &[Elt<R, D>],
        planes: &[Elt<R, D>],
    ) -> Result<(), DigitError> {
        if planes.len() != values.len() * self.digits {
            return Err(DigitError::WrongPlaneCount {
                got: planes.len(),
                expected: values.len() * self.digits,
            });
        }
        let half_width = self.base / 2;
        for (j, value) in values.iter().enumerate() {
            let block = &planes[j * self.digits..(j + 1) * self.digits];
            if &self.join(block) != value {
                return Err(DigitError::Recombination);
            }
            for (k, plane) in block.iter().enumerate() {
                let mut magnitude = 0u64;
                for c in plane.coefficients() {
                    magnitude = magnitude.max(c.abs_infinity());
                }
                if magnitude > half_width {
                    return Err(DigitError::PlaneTooWide {
                        plane: k,
                        magnitude,
                        half_width,
                    });
                }
            }
        }
        Ok(())
    }

    /// `Σ` of the squared centered digits over a batch — one term of the
    /// consolidated norm check (5).
    pub fn norm_sq<R: Ring + CenteredRing, const D: usize>(&self, planes: &[Elt<R, D>]) -> u128 {
        squared_norm_of(planes.iter().flat_map(|e| e.coefficients()))
    }
}

/// The centered base-`b` digit of `x` (the remainder in `[-b/2, b/2]`).
fn centered_digit(x: i64, base: u64) -> i64 {
    let b = i64::try_from(base).expect("base fits i64");
    let half = b / 2;
    let mut d = x.rem_euclid(b);
    if d > half {
        d -= b;
    }
    d
}

/// The paper's two-plane split of the masked opening (§5.3):
/// `z = z⁽⁰⁾ + b·z⁽¹⁾` with `‖z⁽⁰⁾‖∞ ≤ b/2`, over the **integer**
/// representatives — `z` is short as an integer, unlike the mod-`q` objects
/// `t, g, h`, so this is not [`Decomposition::split`].
pub fn split_short<R: Ring + CenteredRing, const D: usize>(
    base: u64,
    v: &Elt<R, D>,
) -> (Elt<R, D>, Elt<R, D>) {
    let src = centered_coeffs::<R, D>(v);
    let mut lo = Vec::with_capacity(D);
    let mut hi = Vec::with_capacity(D);
    for &x in &src {
        let d = centered_digit(x, base);
        lo.push(from_centered::<R>(d));
        hi.push(from_centered::<R>(
            (x - d) / i64::try_from(base).expect("base fits i64"),
        ));
    }
    (
        PolyRing::from_coefficients(lo),
        PolyRing::from_coefficients(hi),
    )
}

/// The Section 5.4 norm bounds and decomposition parameters, held in
/// **squared** integer form so no floating point enters the accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NormBounds {
    /// Decomposition base `b ≈ b₁ ≈ b₂`, from `b = (12·s²·r·τ)^{1/4}`.
    pub base: u64,
    /// Planes for the uniform objects (`t⃗`, `h⃗`): `t₁ = ⌈log q/log b⌉`.
    pub t1: usize,
    /// Planes for the Gaussian object (`g⃗`):
    /// `t₂ = ⌈log(√(24·n·d)·s²)/log b⌉`.
    pub t2: usize,
    /// `γ² = β²·τ`, bounding `‖z‖₂²` for `z = Σ cᵢsᵢ`.
    pub gamma_sq: u128,
    /// `γ₁² = b²t₁/12·rκd + b²t₂/12·(r²+r)/2·d`, bounding `‖t ∥ g‖₂²`.
    pub gamma1_sq: u128,
    /// `γ₂² = b²t₁/12·(r²+r)/2·d`, bounding `‖h‖₂²`.
    pub gamma2_sq: u128,
    /// `(β')² = 2γ²/b² + γ₁² + γ₂²` — equation (5).
    pub beta_prime_sq: u128,
}

impl NormBounds {
    /// Derives the parameters from the instance shape.
    ///
    /// `s² = β²/(r·n·d)` is the modeled per-coefficient variance of the
    /// witness, `kappa` the inner commitment rank (rows of `A`), `tau` the
    /// squared `l2` bound of one challenge.
    #[must_use]
    pub fn derive(
        beta_sq: u128,
        modulus: u64,
        r: usize,
        n: usize,
        kappa: usize,
        d: usize,
        tau: u64,
    ) -> Self {
        let coefficients = wide((r * n * d).max(1));
        let s_sq = (beta_sq / coefficients).max(1);
        let base = integer_root4(12 * s_sq * wide(r) * wide(tau as usize)).max(2);
        let b128 = wide(base as usize);
        let t1 = planes_to_cover(base, u128::from((modulus - 1) / 2));
        // √(24·n·d)·s² is the modeled coefficient magnitude of `g`.
        let g_scale = isqrt_ceil(24 * wide(n) * wide(d)) * s_sq;
        let t2 = planes_to_cover(base, g_scale.max(b128));
        let gamma_sq = beta_sq.saturating_mul(wide(tau as usize));
        // A uniform centered digit in `[-b/2, b/2]` has variance b²/12, so a
        // batch of `entries` digits across `planes` levels contributes
        // b²·planes·entries/12 to the expected squared norm — the paper's
        // γ₁ = √(b₁²t₁/12·rκd + b₂²t₂/12·(r²+r)/2·d) and
        // γ₂ = √(b₁²t₁/12·(r²+r)/2·d). The division is applied to the whole
        // product (not to b²/12 first) to keep the budget from rounding *down*
        // below the honest expectation.
        let var12 = |planes: usize, entries: usize| {
            b128.saturating_mul(b128)
                .saturating_mul(wide(planes))
                .saturating_mul(wide(entries))
                / 12
        };
        let triangle = (r * r + r) / 2 * d;
        let gamma1_sq = var12(t1, r * kappa * d) + var12(t2, triangle);
        let gamma2_sq = var12(t1, triangle);
        let beta_prime_sq = (2 * gamma_sq) / (b128 * b128).max(1) + gamma1_sq + gamma2_sq;
        Self {
            base,
            t1,
            t2,
            gamma_sq,
            gamma1_sq,
            gamma2_sq,
            beta_prime_sq,
        }
    }

    /// Theorem 5.1's precondition `β ≤ √(30/128)·q/125`, squared:
    /// `128·125²·β² ≤ 30·q²`. It is what licenses reading the projection
    /// response back as an integer (Lemma 4.2).
    #[must_use]
    pub fn slack_condition(beta_sq: u128, modulus: u64) -> bool {
        let m = u128::from(modulus);
        beta_sq.saturating_mul(128 * 125 * 125) <= 30 * m * m
    }

    /// The Module-SIS norm requirements of Theorem 5.1, as squared integers:
    /// `[outer, inner]` = `[2β', max(8T(b+1)β', 2(b+1)β' + 4T·√(128/30)·β)]`.
    ///
    /// The `l2` bounds are closed with `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²` and the
    /// exact rational `128/30`, so the result is an upper bound computed
    /// without floating point.
    #[must_use]
    pub fn msis_norm_sq(&self, beta_sq: u128, operator_norm: u64) -> [u128; 2] {
        let t2 = u128::from(operator_norm) * u128::from(operator_norm);
        let bp = self.beta_prime_sq;
        let b1 = u128::from(self.base) + 1;
        let outer = 4 * bp;
        let first = 64 * t2 * b1 * b1 * bp;
        let slack = (beta_sq * 16 * t2 * 128 + 29) / 30;
        let second = 8 * b1 * b1 * bp + 2 * slack;
        [outer, first.max(second)]
    }
}

/// Widens a count or a small magnitude into the `u128` accounting domain.
///
/// Every norm budget in this module is a product of several `usize` counts
/// (`b² · t · r · κ · d`), which overflows `u64` at realistic shapes; `usize`
/// itself is only `u64`, so the widening has to be explicit and total.
fn wide(x: usize) -> u128 {
    u128::from(x as u64)
}

/// Smallest `t ≥ 2` whose digit span covers `magnitude`
/// (`t₁ ≥ 2` and `t₂ ≥ 2` are part of the paper's phrasing).
///
/// The target is a *span*, not a capacity: `b^t > target` is not enough for a
/// balanced digit set, whose `t` planes reach only
/// `⌊b/2⌋·(b^t − 1)/(b − 1)` — see [`crate::pcs::gadget::digit_span_of`].
fn planes_to_cover(base: u64, magnitude: u128) -> usize {
    let mut t = 0;
    while t < 128 {
        if crate::pcs::gadget::digit_span_of(base, t + 1) >= magnitude {
            break;
        }
        t += 1;
    }
    (t + 1).max(2)
}

/// Integer square root, floor.
fn isqrt_floor(v: u128) -> u128 {
    if v < 2 {
        return v;
    }
    let mut x = v;
    let mut y = (x + 1) / 2;
    while y < x {
        x = y;
        y = (x + v / x) / 2;
    }
    x
}

/// Integer square root, ceiling.
fn isqrt_ceil(v: u128) -> u128 {
    let x = isqrt_floor(v);
    if x * x < v {
        x + 1
    } else {
        x
    }
}

/// Smallest integer `x` with `x⁴ ≥ v`.
fn integer_root4(v: u128) -> u64 {
    if v < 2 {
        return 1;
    }
    let mut hi = 1u128;
    while hi.saturating_mul(hi).saturating_mul(hi.saturating_mul(hi)) < v {
        hi *= 2;
    }
    let mut lo = hi / 2;
    while lo + 1 < hi {
        let mid = lo + (hi - lo) / 2;
        let m2 = mid.saturating_mul(mid);
        if m2.saturating_mul(m2) < v {
            lo = mid;
        } else {
            hi = mid;
        }
    }
    let root = if lo.saturating_mul(lo).saturating_mul(lo.saturating_mul(lo)) >= v {
        lo
    } else {
        hi
    };
    root.min(u128::from(u64::MAX)) as u64
}

/// LaBRADOR's challenge space (§2): ring elements with exactly `zeros` zero
/// coefficients, `ones` coefficients at `±1`, `twos` coefficients at `±2`,
/// rejected until the operator norm fits.
///
/// Differences of distinct draws are invertible in the paper's stated regime
/// (small coefficients, `X^D + 1` splitting into two prime ideals of degree
/// `D/2`) by Lyubashevsky–Seiler, Corollary 1.2; `tau()` is the `l2` bound
/// `NormBounds` consumes and `operator_norm` the `T` in Theorem 5.1.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ChallengeSpace {
    /// Zero coefficients.
    pub zeros: usize,
    /// `±1` coefficients.
    pub ones: usize,
    /// `±2` coefficients.
    pub twos: usize,
    /// Operator-norm bound `T` of the rejection filter.
    pub operator_norm: u64,
}

/// A challenge-space configuration failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChallengeError {
    /// The counts do not add up to the ring degree.
    WrongDegree {
        /// `zeros + ones + twos`.
        got: usize,
        /// The ring degree.
        expected: usize,
    },
    /// The operator-norm filter never accepted within the draw budget.
    FilterTooTight {
        /// The bound that was rejected every time.
        bound: u64,
    },
}

impl ChallengeSpace {
    /// The paper's *shape* (§2): `d = 64`, 23 zeros, 31 `±1`, 10 `±2`, so
    /// `τ = ‖c‖₂² = 71`.
    ///
    /// The one number that cannot be copied is the filter bound. §2 restricts
    /// "by rejection sampling … to challenges with **operator norm** at most
    /// 15", i.e. to the true `sup_r ‖cr‖₂/‖r‖₂`, and notes that roughly one
    /// draw in six passes; measuring `σ_max` of the `64 × 64` negacyclic
    /// multiplication matrix over this shape reproduces that (`P = 0.15…0.17`).
    /// The bound this crate can decide **exactly, in integer arithmetic** is
    /// [`operator_norm_bound`]'s `⌈√‖g‖₁⌉`, which is a valid but looser
    /// upper bound: over the same distribution it has median 23 and minimum 20,
    /// so `15` would reject every draw. `24` is the smallest bound that keeps
    /// the acceptance rate near two thirds (`0.87` of draws at 24).
    ///
    /// The consequence is a parameter, not a soundness bug: every accepted
    /// challenge really has `‖c‖_op ≤ 24`, and `24` — not `15` — is what the
    /// Module-SIS budgets of [`NormBounds::msis_norm_sq`] must be evaluated
    /// with. Closing the gap needs a certified eigensolver, which is recorded
    /// as the open half of survey §4 gap G5.
    pub const PAPER: Self = Self {
        zeros: 23,
        ones: 31,
        twos: 10,
        operator_norm: 24,
    };

    /// Ring degree the space is defined over.
    pub const fn degree(&self) -> usize {
        self.zeros + self.ones + self.twos
    }

    /// `τ = ‖c‖₂² = ones + 4·twos` — the challenge variance the norm
    /// accounting uses.
    pub const fn tau(&self) -> u64 {
        self.ones as u64 + 4 * self.twos as u64
    }

    /// Draws one challenge, re-rolling until the operator-norm filter passes.
    ///
    /// The support is a uniform `(ones + twos)`-subset of the `D` positions
    /// with uniform signs (the unbiased partial Fisher–Yates recipe of
    /// [`fixed_weight_signs`]); the `±2` class is then a uniform `twos`-subset
    /// of that support, which is exactly the paper's distribution.
    ///
    /// # Errors
    /// [`ChallengeError::WrongDegree`] if the counts do not span the ring,
    /// [`ChallengeError::FilterTooTight`] if no draw fits within `2^16` rolls
    /// (the paper measures about one acceptance in six).
    pub fn sample<R: Ring + CenteredRing, const D: usize>(
        &self,
        stream: &mut BitStream<'_, impl Xof>,
    ) -> Result<Elt<R, D>, ChallengeError> {
        if self.degree() != D {
            return Err(ChallengeError::WrongDegree {
                got: self.degree(),
                expected: D,
            });
        }
        let support = self.ones + self.twos;
        for _ in 0..(1 << 16) {
            let signs = fixed_weight_signs(stream, support as u32, D);
            let heavy = heavy_positions(stream, &signs, self.twos);
            let coeffs: Vec<R> = signs
                .iter()
                .enumerate()
                .map(|(i, &s)| {
                    let amp = if heavy[i] { 2i64 } else { 1i64 };
                    from_centered::<R>(i64::from(s) * amp)
                })
                .collect();
            let c = PolyRing::from_coefficients(coeffs);
            if operator_norm_bound(&c) <= self.operator_norm {
                return Ok(c);
            }
        }
        Err(ChallengeError::FilterTooTight {
            bound: self.operator_norm,
        })
    }
}

/// A uniform `count`-subset of the non-zero positions of `signs`.
fn heavy_positions(stream: &mut BitStream<'_, impl Xof>, signs: &[i8], count: usize) -> Vec<bool> {
    let positions: Vec<usize> = (0..signs.len()).filter(|&i| signs[i] != 0).collect();
    let mut chosen = vec![false; signs.len()];
    let n = positions.len();
    let mut idx: Vec<usize> = (0..n).collect();
    for i in 0..count.min(n) {
        let range = (n - i) as u32;
        let limit = u32::MAX - (u32::MAX % range);
        let j = loop {
            let mut buf = [0u8; 4];
            stream.read_bytes(&mut buf);
            let v = u32::from_le_bytes(buf);
            if v < limit {
                break i + (v % range) as usize;
            }
        };
        idx.swap(i, j);
        chosen[positions[idx[i]]] = true;
    }
    chosen
}

/// A rigorous upper bound on the operator norm
/// `‖c‖_op = sup_r ‖c·r‖₂/‖r‖₂` of negacyclic multiplication by `c`.
///
/// Negacyclic multiplication matrices form a commutative algebra with
/// `M_a·M_b = M_{ab}`, and `M_cᵗ` is the matrix of the coefficient reversal,
/// so `M_c·M_cᵗ = M_g` where `g = c·τ(c)` is the **negacyclic
/// autocorrelation** of `c` (`g_k = Σ_m c_m·(±)c_{m+k}`, `g_0 = ‖c‖₂²`).
/// `M_g` is real symmetric positive semi-definite, so Gershgorin bounds its
/// largest eigenvalue by the largest absolute row sum, which for a
/// circulant-like matrix is `‖g‖₁`. Hence `‖c‖_op² ≤ ‖g‖₁`, and this returns
/// `⌈√‖g‖₁⌉`.
///
/// The bound is rigorous and exact to compute, but *loose*: over LaBRADOR's
/// challenge shape it sits a factor 1.35–1.5 above the true `‖c‖_op` (median
/// 23 against a true median of 16.9), which is why [`ChallengeSpace::PAPER`]
/// filters at 24 rather than at the paper's 15. Every row of `M_g` holds each
/// `|g_k|` exactly once, so no diagonal rescaling tightens the row sum: the
/// gap is the sign cancellation Gershgorin discards, not an implementation
/// slack.
pub fn operator_norm_bound<R: Ring + CenteredRing, const D: usize>(c: &Elt<R, D>) -> u64 {
    let a = centered_coeffs::<R, D>(c);
    let mut l1: u128 = 0;
    for k in 0..D {
        let mut acc: i128 = 0;
        for m in 0..D {
            let (idx, sign) = negacyclic_term(m, k, D);
            acc += i128::from(a[m]) * i128::from(a[idx]) * i128::from(sign);
        }
        l1 += u128::try_from(acc.unsigned_abs()).unwrap_or(u128::MAX);
    }
    isqrt_ceil(l1) as u64
}

/// The coefficient slot and sign contributed by `c_m · X^k` when the product
/// is reduced modulo `X^D + 1`.
fn negacyclic_term(m: usize, k: usize, d: usize) -> (usize, i32) {
    if m + k < d {
        (m + k, 1)
    } else {
        (m + k - d, -1)
    }
}

/// The random projection `Π ∈ {−1,0,1}^{rows × r·n·D}` of §5.2
/// ("Projecting"), generic over the ring instance.
///
/// Entries follow the GHL21-tuned distribution (`P(0) = 1/2`, `P(±1) = 1/4`
/// each) through the same two-bit recipe as
/// [`crate::shortness::projection::JLProjection`]. That type is pinned to the
/// Z2 ring and keeps its rows private, but the aggregation needs the rows as
/// **ring vectors** `σ⁻¹(πᵢ⁽ʲ⁾)`, so the matrix lives here.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Projection<R: Ring, const D: usize> {
    /// Rows of the flattened `0/±1` matrix.
    pub rows: Vec<Vec<i8>>,
    /// `r`, the multiplicity the rows are split by.
    pub multiplicity: usize,
    /// `n`, the rank each row block covers.
    pub rank: usize,
    /// The rows lifted to ring vectors with `σ⁻¹ = σ` applied:
    /// `sigma_rows[j][i] ∈ R_q^n`, the linear coefficient row `j` contributes
    /// to witness vector `i`.
    pub sigma_rows: Vec<Vec<WitnessVec<R, D>>>,
}

impl<R: Ring + CenteredRing, const D: usize> Projection<R, D> {
    /// Derives a `rows × (r·n·D)` projection from a seed.
    pub fn from_seed(seed: &[u8; 32], rows: usize, multiplicity: usize, rank: usize) -> Self {
        assert!(rows > 0 && multiplicity > 0 && rank > 0);
        let dim = multiplicity * rank * D;
        let mut xof = Shake256Xof::new(b"lattice-algebra/Z7/dotproduct-projection");
        xof.absorb(seed);
        let mut stream = BitStream::new(&mut xof);
        let mut out_rows = Vec::with_capacity(rows);
        for _ in 0..rows {
            let mut row = Vec::with_capacity(dim);
            for _ in 0..dim {
                // (hi, lo) = (0,0) -> 0, (0,1) -> +1, (1,0) -> -1, (1,1) -> 0
                let hi = stream.read_bits(1);
                let lo = stream.read_bits(1);
                row.push(match (hi, lo) {
                    (0, 1) => 1,
                    (1, 0) => -1,
                    _ => 0,
                });
            }
            out_rows.push(row);
        }
        let sigma_rows = out_rows
            .iter()
            .map(|row| {
                (0..multiplicity)
                    .map(|i| {
                        (0..rank)
                            .map(|k| {
                                let block = &row[i * rank * D + k * D..i * rank * D + (k + 1) * D];
                                let lifted: Elt<R, D> = PolyRing::from_coefficients(
                                    block
                                        .iter()
                                        .map(|&e| from_centered::<R>(i64::from(e)))
                                        .collect(),
                                );
                                sigma_of(&lifted)
                            })
                            .collect()
                    })
                    .collect()
            })
            .collect();
        Self {
            rows: out_rows,
            multiplicity,
            rank,
            sigma_rows,
        }
    }

    /// Number of rows (the reduced dimension; the paper uses 256).
    pub fn row_count(&self) -> usize {
        self.rows.len()
    }

    /// `p_j = Σᵢ ⟨πᵢ⁽ʲ⁾, sᵢ⟩` over the **integers**, on the flattened centered
    /// witness — the vector the verifier compares against `√128·β`.
    ///
    /// # Panics
    /// If the witness shape does not match the projection.
    pub fn project(&self, s: &[WitnessVec<R, D>]) -> Vec<i64> {
        assert_eq!(s.len(), self.multiplicity, "projection witness count");
        let flat: Vec<i64> = s
            .iter()
            .flat_map(|v| v.iter().flat_map(|e| centered_coeffs::<R, D>(e)))
            .collect();
        assert_eq!(flat.len(), self.rows[0].len(), "projection witness size");
        self.rows
            .iter()
            .map(|row| {
                row.iter()
                    .zip(flat.iter())
                    .map(|(&e, &c)| i64::from(e) * c)
                    .sum()
            })
            .collect()
    }
}

/// The verifier-side coefficients of one first-aggregation challenge:
/// `a''⁽ᵏ⁾ = Σ ψ·a'⁽ˡ⁾` and `φ''⁽ᵏ⁾ = Σ ψ·φ'⁽ˡ⁾ + Σ ω·σ⁻¹(π⁽ʲ⁾)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AggregatedCoeffs<R: Ring, const D: usize> {
    /// `a''⁽ᵏ⁾`.
    pub a: Vec<Vec<Elt<R, D>>>,
    /// `φ''⁽ᵏ⁾`.
    pub phi: Vec<WitnessVec<R, D>>,
}

/// Computes every `a''⁽ᵏ⁾, φ''⁽ᵏ⁾` (Figure 3 lines 3–4). The verifier needs
/// only these, because the prover supplies the missing `b''(k)` and the
/// verifier checks its constant term against public data.
///
/// # Errors
/// [`CoreError::WrongShape`] when a challenge vector has the wrong length.
pub fn aggregate_first<R: Ring + CenteredRing, const D: usize>(
    relation: &Relation<R, D>,
    projection: &Projection<R, D>,
    psi: &[Vec<R>],
    omega: &[Vec<R>],
) -> Result<Vec<AggregatedCoeffs<R, D>>, CoreError> {
    let r = relation.multiplicity;
    let n = relation.rank;
    if omega.len() != psi.len() {
        return Err(CoreError::WrongShape {
            got: omega.len(),
            expected: psi.len(),
        });
    }
    if projection.multiplicity != r || projection.rank != n {
        return Err(CoreError::WrongShape {
            got: projection.multiplicity,
            expected: r,
        });
    }
    if relation.rank == 0 || relation.multiplicity == 0 {
        return Err(CoreError::WrongShape {
            got: relation.multiplicity,
            expected: 1,
        });
    }
    let mut out = Vec::with_capacity(psi.len());
    for k in 0..psi.len() {
        if psi[k].len() != relation.ct_only.len() {
            return Err(CoreError::WrongShape {
                got: psi[k].len(),
                expected: relation.ct_only.len(),
            });
        }
        if omega[k].len() != projection.row_count() {
            return Err(CoreError::WrongShape {
                got: omega[k].len(),
                expected: projection.row_count(),
            });
        }
        let mut a = vec![vec![zero_elt::<R, D>(); r]; r];
        let mut phi: Vec<WitnessVec<R, D>> = vec![vec![zero_elt::<R, D>(); n]; r];
        for (l, ft) in relation.ct_only.iter().enumerate() {
            let w = scalar_as_elt::<R, D>(&psi[k][l]);
            for i in 0..r {
                for j in 0..r {
                    a[i][j] += ft.a[i][j].clone().mul_ref(&w);
                }
                for x in 0..n {
                    phi[i][x] += ft.phi[i][x].clone().mul_ref(&w);
                }
            }
        }
        for (j, w) in omega[k].iter().enumerate() {
            let w_ring = scalar_as_elt::<R, D>(w);
            for i in 0..r {
                for x in 0..n {
                    phi[i][x] += projection.sigma_rows[j][i][x].clone().mul_ref(&w_ring);
                }
            }
        }
        out.push(AggregatedCoeffs { a, phi });
    }
    Ok(out)
}

/// The scalar `s ∈ Z_q` as a constant ring element.
fn scalar_as_elt<R: Ring, const D: usize>(s: &R) -> Elt<R, D> {
    let mut coeffs = vec![R::ZERO; D];
    coeffs[0] = *s;
    PolyRing::from_coefficients(coeffs)
}

/// The verifier's side of the Figure 2 check
/// `b''(k)₀ =? ⟨ω⁽ᵏ⁾, p⟩ + Σₗ ψₗ⁽ᵏ⁾·b'₀⁽ˡ⁾`.
pub fn first_aggregation_claim<R: Ring, const D: usize>(
    relation: &Relation<R, D>,
    psi: &[Vec<R>],
    omega: &[Vec<R>],
    p_mod: &[R],
) -> Vec<R> {
    (0..psi.len())
        .map(|k| {
            let mut acc = R::ZERO;
            for (l, b0) in relation.ct_only.iter().map(|f| f.b0).enumerate() {
                acc += psi[k][l] * b0;
            }
            for (j, w) in omega[k].iter().enumerate() {
                acc += *w * p_mod[j];
            }
            acc
        })
        .collect()
}

/// The prover's `b''(k)`: the *full* value of the aggregated function at the
/// witness, which is what makes `f''(k)` vanish identically (Figure 2 sends
/// these and the verifier keeps only their constant terms).
pub fn prover_b_double<R: Ring + CenteredRing, const D: usize>(
    coeffs: &[AggregatedCoeffs<R, D>],
    s: &[WitnessVec<R, D>],
) -> Vec<Elt<R, D>> {
    coeffs
        .iter()
        .map(|c| {
            let f = QuadFn {
                a: c.a.clone(),
                phi: c.phi.clone(),
                b: zero_elt::<R, D>(),
            };
            f.lhs(s)
        })
        .collect()
}

/// The second aggregation (Figure 3 lines 5–7): fold `F` and `F''` into the
/// single function whose relation check is line 18.
pub fn aggregate_second<R: Ring + CenteredRing, const D: usize>(
    relation: &Relation<R, D>,
    coeffs: &[AggregatedCoeffs<R, D>],
    b_double: &[Elt<R, D>],
    alpha: &[Elt<R, D>],
    beta: &[Elt<R, D>],
) -> QuadFn<R, D> {
    let r = relation.multiplicity;
    let n = relation.rank;
    let mut a = vec![vec![zero_elt::<R, D>(); r]; r];
    let mut phi: Vec<WitnessVec<R, D>> = vec![vec![zero_elt::<R, D>(); n]; r];
    let mut b = zero_elt::<R, D>();
    for (f, w) in relation.full.iter().zip(alpha.iter()) {
        for i in 0..r {
            for j in 0..r {
                a[i][j] += f.a[i][j].clone().mul_ref(w);
            }
            for x in 0..n {
                phi[i][x] += f.phi[i][x].clone().mul_ref(w);
            }
        }
        b += f.b.clone().mul_ref(w);
    }
    for ((c, bv), w) in coeffs.iter().zip(b_double.iter()).zip(beta.iter()) {
        for i in 0..r {
            for j in 0..r {
                a[i][j] += c.a[i][j].clone().mul_ref(w);
            }
            for x in 0..n {
                phi[i][x] += c.phi[i][x].clone().mul_ref(w);
            }
        }
        b += bv.clone().mul_ref(w);
    }
    QuadFn { a, phi, b }
}

/// The quadratic garbage `g_ij = ⟨sᵢ,sⱼ⟩` of §5.2, as an `r × r` batch.
///
/// These are independent of *every* challenge, which is why the paper has the
/// prover compute them up front and fold them into the first outer commitment
/// `u₁` instead of `u₂`.
pub fn garbage_g<R: Ring, const D: usize>(s: &[WitnessVec<R, D>]) -> Vec<Elt<R, D>> {
    let r = s.len();
    let mut g = Vec::with_capacity(r * r);
    for i in 0..r {
        for j in 0..r {
            g.push(inner_product(&s[i], &s[j]));
        }
    }
    g
}

/// The linear garbage `h_ij = ½(⟨φᵢ,sⱼ⟩ + ⟨φⱼ,sᵢ⟩)` of §5.2, as an `r × r`
/// batch, where `(φᵢ)` is the *aggregated* linear coefficient of §5.2.
///
/// The symmetrized half is what makes `Σ_{i,j} h_ij cᵢc_j` equal
/// `Σ_i ⟨φᵢ,z⟩cᵢ` for `z = Σ cᵢsᵢ` (Figure 3 line 17) for arbitrary
/// challenges: the two orderings of each cross term are averaged, and
/// `2·½ = 1` in `R_q`.
///
/// # Panics
/// If `phi` does not carry one vector per witness vector.
pub fn garbage_h<R: Ring + CenteredRing, const D: usize>(
    s: &[WitnessVec<R, D>],
    phi: &[WitnessVec<R, D>],
) -> Vec<Elt<R, D>> {
    let r = s.len();
    assert_eq!(phi.len(), r, "one φ per witness vector");
    // ½ mod q: (q+1)/2 doubles to q+1 ≡ 1 for every odd modulus.
    let half = const_elt::<R, D>(i64::try_from((R::MODULUS + 1) / 2).expect("q fits i64"));
    let mut h = Vec::with_capacity(r * r);
    for i in 0..r {
        for j in 0..r {
            let cross = inner_product(&phi[i], &s[j]) + inner_product(&phi[j], &s[i]);
            h.push(cross.mul_ref(&half));
        }
    }
    h
}

/// Why the core argument was rejected — one variant per Figure 3 line (see
/// the module table).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CoreError {
    /// A vector had the wrong length for the instance shape.
    WrongShape {
        /// Length supplied.
        got: usize,
        /// Length required.
        expected: usize,
    },
    /// Figure 2: `‖p‖₂² > 128·β²`.
    ProjectionNorm {
        /// `‖p‖₂²` over the integers.
        norm_sq: u128,
        /// `128·β²`.
        budget: u128,
    },
    /// Figure 2: `ct(b''(k))` disagrees with the public combination.
    AggregationConstantTerm {
        /// Index of the aggregated function.
        index: usize,
    },
    /// Figure 3 lines 8/9: the garbage matrices are not symmetric.
    AsymmetricGarbage,
    /// Figure 3 lines 10–13: a digit batch does not recombine.
    DigitRecombination,
    /// Figure 3 lines 10–13: a digit plane is wider than `b/2`.
    DigitBound,
    /// Figure 3 line 14 / equation (5): the consolidated norm bound fails.
    NormBudget {
        /// The revealed total.
        actual: u128,
        /// `(β')²`.
        budget: u128,
    },
    /// Figure 3 line 15: `A·z ≠ Σ cᵢtᵢ`.
    InnerLink,
    /// Figure 3 line 16: `⟨z,z⟩ ≠ Σ g_ij cᵢc_j`.
    SelfInnerProduct,
    /// Figure 3 line 17: `Σᵢ⟨φᵢ,z⟩cᵢ ≠ Σ h_ij cᵢc_j`.
    LinearClaim,
    /// Figure 3 line 18: `Σ a_ij g_ij + Σ hᵢᵢ ≠ b`.
    Relation,
    /// Figure 3 line 19: `u₁` does not open.
    OuterCommitment1,
    /// Figure 3 line 20: `u₂` does not open.
    OuterCommitment2,
    /// Theorem 5.1's slack precondition on `β` is violated.
    SlackCondition,
    /// A digit decomposition does not fit the modulus.
    DigitCapacity,
    /// The challenge space configuration does not fit the ring.
    Challenge,
    /// §5.3's reblocking does not cover the level: `ν·n′ < n` or `μ·n′ < m`, so
    /// the target relation would silently drop part of the witness.
    TargetShape,
    /// The prover's witness itself violates `Σᵢ ‖sᵢ‖₂² ≤ β²`.
    WitnessNorm {
        /// The witness's `Σᵢ ‖sᵢ‖₂²`.
        norm_sq: u128,
        /// The claimed `β²`.
        bound_sq: u128,
    },
}

impl fmt::Display for CoreError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongShape { got, expected } => {
                write!(f, "vector of {got} entries against {expected}")
            }
            Self::ProjectionNorm { norm_sq, budget } => {
                write!(f, "‖p‖₂² = {norm_sq} exceeds 128β² = {budget}")
            }
            Self::AggregationConstantTerm { index } => {
                write!(f, "b''({index}) has the wrong constant term")
            }
            Self::AsymmetricGarbage => write!(f, "line 8/9: garbage is not symmetric"),
            Self::DigitRecombination => write!(f, "lines 10-13: digits do not recombine"),
            Self::DigitBound => write!(f, "lines 10-13: a digit plane exceeds b/2"),
            Self::NormBudget { actual, budget } => {
                write!(
                    f,
                    "line 14: revealed norm² {actual} exceeds (β')² = {budget}"
                )
            }
            Self::InnerLink => write!(f, "line 15: A·z != Σ cᵢtᵢ"),
            Self::SelfInnerProduct => write!(f, "line 16: ⟨z,z⟩ != Σ g_ij cᵢc_j"),
            Self::LinearClaim => write!(f, "line 17: Σ⟨φᵢ,z⟩cᵢ != Σ h_ij cᵢc_j"),
            Self::Relation => write!(f, "line 18: Σ a_ij g_ij + Σ hᵢᵢ != b"),
            Self::OuterCommitment1 => write!(f, "line 19: u₁ opening check failed"),
            Self::OuterCommitment2 => write!(f, "line 20: u₂ opening check failed"),
            Self::SlackCondition => write!(
                f,
                "β violates Theorem 5.1's precondition β <= sqrt(30/128)*q/125"
            ),
            Self::DigitCapacity => write!(f, "a digit capacity does not exceed the modulus"),
            Self::Challenge => write!(f, "the challenge space does not fit the ring"),
            Self::TargetShape => write!(
                f,
                "§5.3: the reblocking (ν·n′, μ·n′) does not cover the level's (n, m)"
            ),
            Self::WitnessNorm { norm_sq, bound_sq } => write!(
                f,
                "the witness has ‖s‖₂² = {norm_sq} against the claimed β² = {bound_sq}"
            ),
        }
    }
}

/// The public shape of one core-argument execution: the CRS keys, the
/// decompositions derived from §5.4, and the norm budget.
#[derive(Debug, Clone)]
pub struct CoreParams<R: Ring, const D: usize> {
    /// Inner Ajtai key `A ∈ R_q^{κ×n}`, applied blockwise to every `sᵢ`.
    pub inner_key: RingMatrixKey<R, D>,
    /// Outer key `B ∈ R_q^{κ₁×r·t₁·κ}` over the inner-commitment digits.
    pub key_b: RingMatrixKey<R, D>,
    /// Outer key `C ∈ R_q^{κ₁×t₂·r(r+1)/2}` over the `g` digits.
    pub key_c: RingMatrixKey<R, D>,
    /// Outer key `D ∈ R_q^{κ₂×t₁·r(r+1)/2}` over the `h` digits.
    pub key_d: RingMatrixKey<R, D>,
    /// Decomposition `(b₁, t₁)` of `t⃗` and `h⃗`.
    pub decomp1: Decomposition,
    /// Decomposition `(b₂, t₂)` of `g⃗`.
    pub decomp2: Decomposition,
    /// Section 5.4 norm bounds.
    pub bounds: NormBounds,
    /// Number of first-aggregation functions, `⌈128/log q⌉`.
    pub aggregation_count: usize,
}

impl<R: Ring + CenteredRing, const D: usize> CoreParams<R, D> {
    /// Checks Theorem 5.1's precondition `β ≤ √(30/128)·q/125` against the
    /// statement's own norm bound.
    ///
    /// # Errors
    /// [`CoreError::SlackCondition`] when it fails, in which case the
    /// projection response cannot be read back as an integer and the argument
    /// is unsound as stated.
    pub fn slack_ok(&self, relation: &Relation<R, D>) -> Result<(), CoreError> {
        if NormBounds::slack_condition(relation.norm_bound_sq, R::MODULUS) {
            Ok(())
        } else {
            Err(CoreError::SlackCondition)
        }
    }
}

/// What a core-argument execution needs: the CRS keys, decompositions and
/// budget, plus the challenge space `C ⊂ R_q` the amortization comes from.
#[derive(Debug, Clone)]
pub struct CoreSetup<R: Ring, const D: usize> {
    /// The keys, decompositions and norm budget.
    pub params: CoreParams<R, D>,
    /// The challenge space `C` (§2).
    pub space: ChallengeSpace,
}

/// `Σ xᵢ²` over the integers: the squared norm of the projection response,
/// which Figure 2 compares against `128·β²`.
fn integer_norm_sq(xs: &[i64]) -> u128 {
    xs.iter()
        .map(|v| {
            let a = u128::from(v.unsigned_abs());
            a * a
        })
        .sum()
}

/// The largest centered coefficient magnitude across a batch — the quantity a
/// digit decomposition must span to represent it exactly.
fn max_abs_coeff<R: Ring + CenteredRing, const D: usize>(batch: &[Elt<R, D>]) -> u128 {
    batch
        .iter()
        .flat_map(|e| e.coefficients())
        .map(|c| u128::from(c.abs_infinity()))
        .max()
        .unwrap_or(0)
}

/// A domain-separation label suffixed with an index, so parallel draws from
/// one transcript slot cannot collide.
fn label_index(label: &[u8], index: usize) -> Vec<u8> {
    let mut out = label.to_vec();
    out.extend_from_slice(&(index as u32).to_le_bytes());
    out
}

/// The prover messages of the core argument, in Figure 2's order.
///
/// The verifier's challenges (`ψ`, `ω`, `α`, `β`, `c₁…c_r`) and the projection
/// matrix are *not* carried: [`verify_core`] re-derives every one of them from
/// this message through [`CoreChallenger`], so a prover cannot choose
/// challenges that make a false claim hold.
#[derive(Debug, Clone)]
pub struct CoreMessage<R: Ring, const D: usize> {
    /// Outer commitment `u₁ ∈ R_q^{κ₁}`.
    pub u1: Vec<Elt<R, D>>,
    /// Outer commitment `u₂ ∈ R_q^{κ₂}`.
    pub u2: Vec<Elt<R, D>>,
    /// Projection response `p`, as integers (the slack condition keeps them
    /// inside the centered window).
    pub p: Vec<i64>,
    /// The prover's `b''(k)` polynomials.
    pub b_double: Vec<Elt<R, D>>,
    /// The amortized opening `z = Σ cᵢsᵢ`.
    pub z: WitnessVec<R, D>,
    /// `z` split into two base-`b` planes (`2·n` elements).
    pub z_digits: Vec<Elt<R, D>>,
    /// Inner commitments `t⃗ = (t₁, …, t_r)` concatenated (`r·κ` elements).
    pub t: Vec<Elt<R, D>>,
    /// Digit planes of `t⃗` (`r·κ·t₁` elements).
    pub t_digits: Vec<Elt<R, D>>,
    /// Garbage `g_ij` (`r²` elements, symmetric).
    pub g: Vec<Elt<R, D>>,
    /// Digit planes of the `i ≤ j` triangle of `g`.
    pub g_digits: Vec<Elt<R, D>>,
    /// Garbage `h_ij` (`r²` elements, symmetric).
    pub h: Vec<Elt<R, D>>,
    /// Digit planes of the `i ≤ j` triangle of `h`.
    pub h_digits: Vec<Elt<R, D>>,
}

/// The `i ≤ j` triangle of an `r × r` symmetric batch, in the order the outer
/// commitments consume it: `(0,0), (0,1), …, (0,r−1), (1,1), …`.
pub fn triangle<R: Ring, const D: usize>(batch: &[Elt<R, D>], r: usize) -> Vec<Elt<R, D>> {
    let mut out = Vec::with_capacity((r * r + r) / 2);
    for i in 0..r {
        for j in i..r {
            out.push(batch[i * r + j].clone());
        }
    }
    out
}

impl<R: Ring, const D: usize> CoreMessage<R, D> {
    /// Ring elements a verifier has to *receive* in the last round.
    ///
    /// `z, t, g, h` are recomputable from their digit planes (Figure 3 lines
    /// 10–13), so the planes are the payload; §5.7 charges `nd·log(12β√(τ/nd))`
    /// for `z⃗` and `rκ·d·log q` for `t⃗`, which is the same quantity expressed in
    /// the value's width rather than the plane count. This is the number the
    /// recursion drives down.
    #[must_use]
    pub fn last_message_planes(&self) -> usize {
        self.z_digits.len() + self.t_digits.len() + self.g_digits.len() + self.h_digits.len()
    }

    /// Ring elements before the last round: `u₁`, the `b″(k)`, `u₂` — the head a
    /// level sends whichever way its target is settled.
    #[must_use]
    pub fn head_elements(&self) -> usize {
        self.u1.len() + self.b_double.len() + self.u2.len()
    }
}

/// What a level puts on the wire *before* its last message: `u₁`, the projection
/// response `p`, the `⌈128/log q⌉` polynomials `b″(k)` and `u₂` — Figure 2's
/// first four prover messages.
///
/// This is Definition 3.5's input to `Ṽ`: a level's target statement is a
/// function of the statement, the CRS and this head **alone**, never of the last
/// message ([`derive_view_at_head`] is that function, and it consumes no field
/// but these four). That is precisely what licenses replacing the last message by
/// a proof of the target relation (§5.3 p.15: the verifier accepts iff `‖p‖ <
/// √128β`, `b″(k)₀` is correct, and the target relation holds).
#[derive(Debug, Clone)]
pub struct CoreHead<R: Ring, const D: usize> {
    /// Outer commitment `u₁ ∈ R_q^{κ₁}`.
    pub u1: Vec<Elt<R, D>>,
    /// Projection response `p`, as integers.
    pub p: Vec<i64>,
    /// The prover's `b″(k)` polynomials.
    pub b_double: Vec<Elt<R, D>>,
    /// Outer commitment `u₂ ∈ R_q^{κ₂}`.
    pub u2: Vec<Elt<R, D>>,
}

impl<R: Ring, const D: usize> CoreHead<R, D> {
    /// The head of a full [`CoreMessage`]: everything except `z, t, g, h` and
    /// their planes, which is the material the recursion stops sending.
    #[must_use]
    pub fn of(message: &CoreMessage<R, D>) -> Self {
        Self {
            u1: message.u1.clone(),
            p: message.p.clone(),
            b_double: message.b_double.clone(),
            u2: message.u2.clone(),
        }
    }

    /// Checks the head is exactly the four batches this level's public shape
    /// implies. Unevaluable transcripts are reported before any check that would
    /// read them, so a short head cannot be mistaken for a passing one.
    ///
    /// # Errors
    /// [`CoreError::WrongShape`] naming the first batch whose length is wrong.
    pub fn check_shape(&self, params: &CoreParams<R, D>) -> Result<(), CoreError> {
        let batches = [
            (self.u1.len(), params.key_b.rows()),
            (self.u2.len(), params.key_d.rows()),
            (self.b_double.len(), params.aggregation_count),
            (self.p.len(), PROJECTION_ROWS),
        ];
        if let Some((got, expected)) = batches.into_iter().find(|(g, e)| g != e) {
            return Err(CoreError::WrongShape { got, expected });
        }
        Ok(())
    }
}

/// Fiat–Shamir state for the core argument.
///
/// One type drives both sides: [`prove_core`] and [`verify_core`] call the
/// same four methods in the same order, so the prover's challenge stream and
/// the verifier's cannot drift apart, and no challenge can be chosen by a
/// prover who has not yet committed to the message it is supposed to bind.
///
/// The binding order is Figure 2's message order: the CRS seed and the
/// statement, then `u₁` (which fixes the projection matrix), then `p` (which
/// fixes `ψ, ω`), then `b''` (which fixes `α, β`), and finally `u₂` (which
/// fixes the amortization challenges `c₁…c_r`) — after the last one the prover
/// has nothing left to influence.
pub struct CoreChallenger<'a, R: Ring, const D: usize> {
    transcript: Transcript<Shake256Xof>,
    space: &'a ChallengeSpace,
    aggregation_count: usize,
    ct_len: usize,
    full_len: usize,
    rows: usize,
    marker: core::marker::PhantomData<fn() -> Elt<R, D>>,
}

impl<'a, R: Ring + CenteredRing, const D: usize> CoreChallenger<'a, R, D> {
    /// Binds the CRS seed, the challenge space and the relation statement.
    pub fn new(
        key_seed: &[u8; 32],
        space: &'a ChallengeSpace,
        relation: &Relation<R, D>,
        aggregation_count: usize,
        rows: usize,
    ) -> Self {
        let mut transcript = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/dotproduct-core");
        transcript.absorb(b"key", key_seed);
        transcript.absorb(b"tau", &space.tau().to_le_bytes());
        transcript.absorb(b"count", &(aggregation_count as u32).to_le_bytes());
        transcript.absorb(b"rows", &(rows as u32).to_le_bytes());
        absorb_relation(&mut transcript, relation);
        Self {
            transcript,
            space,
            aggregation_count,
            ct_len: relation.ct_only.len(),
            full_len: relation.full.len(),
            rows,
            marker: core::marker::PhantomData,
        }
    }

    /// Absorbs `u₁` and returns the seed the projection matrix is derived from.
    pub fn bind_outer1(&mut self, u1: &[Elt<R, D>]) -> [u8; 32] {
        absorb_elts(&mut self.transcript, b"u1", u1);
        let bytes = self.transcript.challenge_bytes(32);
        let mut seed = [0u8; 32];
        seed.copy_from_slice(&bytes[..32]);
        seed
    }

    /// Absorbs the projection response `p` and draws `ψ ∈ Z_q^{count×L}` and
    /// `ω ∈ Z_q^{count×rows}` — uniformly random `Z_q` entries, which is what
    /// the paper asks for ("uniformly random challenges from `Z_q`").
    pub fn bind_projection(&mut self, p: &[i64]) -> (Vec<Vec<R>>, Vec<Vec<R>>) {
        absorb_ints(&mut self.transcript, b"p", p);
        let psi = (0..self.aggregation_count)
            .map(|k| self.scalars(&label_index(b"psi", k), self.ct_len))
            .collect();
        let omega = (0..self.aggregation_count)
            .map(|k| self.scalars(&label_index(b"omega", k), self.rows))
            .collect();
        (psi, omega)
    }

    /// Absorbs the `b''(k)` polynomials and draws `α ∈ R_q^K`, `β ∈ R_q^count`.
    pub fn bind_aggregation(&mut self, b_double: &[Elt<R, D>]) -> (Vec<Elt<R, D>>, Vec<Elt<R, D>>) {
        absorb_elts(&mut self.transcript, b"b2", b_double);
        let alpha_seed = self.seed(b"alpha");
        let beta_seed = self.seed(b"beta");
        let alpha = uniform_vec_from_seed::<R, D>(b"alpha", &alpha_seed, self.full_len);
        let beta = uniform_vec_from_seed::<R, D>(b"beta", &beta_seed, self.aggregation_count);
        (alpha, beta)
    }

    /// Absorbs `u₂` and draws the `r` amortization challenges from the
    /// challenge space `C`.
    ///
    /// # Errors
    /// [`CoreError::Challenge`] if the operator-norm filter never accepts.
    pub fn bind_outer2(&mut self, u2: &[Elt<R, D>], r: usize) -> Result<Vec<Elt<R, D>>, CoreError> {
        absorb_elts(&mut self.transcript, b"u2", u2);
        let mut out = Vec::with_capacity(r);
        for i in 0..r {
            let seed = self.seed(&label_index(b"c", i));
            let mut xof = Shake256Xof::new(&[]);
            xof.absorb(&seed);
            let mut stream = BitStream::new(&mut xof);
            out.push(
                self.space
                    .sample::<R, D>(&mut stream)
                    .map_err(|_| CoreError::Challenge)?,
            );
        }
        Ok(out)
    }

    /// Squeezes the next labelled challenge seed. The transcript state
    /// advances on every call, so parallel draws cannot collide, and every
    /// seed is bound to everything absorbed before it.
    fn seed(&mut self, label: &[u8]) -> Vec<u8> {
        self.transcript.absorb(b"draw", label);
        self.transcript.challenge_bytes(64)
    }

    /// `len` uniform `Z_q` scalars from the next transcript draw.
    fn scalars(&mut self, label: &[u8], len: usize) -> Vec<R> {
        let seed = self.seed(label);
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(&seed);
        let mut stream = BitStream::new(&mut xof);
        (0..len)
            .map(|_| sample_uniform_coeff::<R>(&mut stream))
            .collect()
    }
}

/// Absorbs a relation statement (both families) into a transcript.
fn absorb_relation<R: Ring, const D: usize>(
    tr: &mut Transcript<Shake256Xof>,
    rel: &Relation<R, D>,
) {
    tr.absorb(b"rank", &(rel.rank as u32).to_le_bytes());
    tr.absorb(b"mult", &(rel.multiplicity as u32).to_le_bytes());
    tr.absorb(b"beta2", &rel.norm_bound_sq.to_le_bytes());
    for f in &rel.full {
        for row in &f.a {
            absorb_elts(tr, b"a", row);
        }
        for v in &f.phi {
            absorb_elts(tr, b"phi", v);
        }
        absorb_elts(tr, b"b", core::slice::from_ref(&f.b));
    }
    for f in &rel.ct_only {
        for row in &f.a {
            absorb_elts(tr, b"a", row);
        }
        for v in &f.phi {
            absorb_elts(tr, b"phi", v);
        }
        tr.absorb(b"b0", &scalar_bytes(f.b0));
    }
}

/// Absorbs a batch of ring elements.
fn absorb_elts<R: Ring, const D: usize>(
    tr: &mut Transcript<Shake256Xof>,
    label: &[u8],
    xs: &[Elt<R, D>],
) {
    let bytes: Vec<u8> = xs
        .iter()
        .flat_map(|x| x.coefficients())
        .flat_map(|c| scalar_bytes(c))
        .collect();
    tr.absorb(label, &bytes);
}

/// Absorbs a batch of integers (the projection response).
fn absorb_ints(tr: &mut Transcript<Shake256Xof>, label: &[u8], xs: &[i64]) {
    let bytes: Vec<u8> = xs.iter().flat_map(|v| v.to_le_bytes()).collect();
    tr.absorb(label, &bytes);
}

/// The canonical little-endian bytes of one scalar coefficient.
fn scalar_bytes<R: Ring>(c: R) -> [u8; 8] {
    (c.to_u128() as u64).to_le_bytes()
}

/// `⌈128/log₂ q⌉`, the number of functions the first aggregation collapses
/// `F'` and the projection identities into (§5.2).
#[must_use]
pub fn aggregation_count(modulus: u64) -> usize {
    let bits = u64::from(64 - modulus.saturating_sub(1).leading_zeros()).max(1);
    (128 + bits as usize - 1) / bits as usize
}

/// Runs Figure 2 as the prover.
///
/// `restart_limit` bounds the Section 5.4 remedy: when an honest run's revealed
/// digits overrun `(β')²`, or its projection response fails the `√128·β` gate,
/// the prover re-draws the projection (and hence every later challenge) rather
/// than proving a longer witness than it claimed.
///
/// # Errors
/// [`CoreError::WitnessNorm`] if the witness itself is longer than `β` (no
/// restart helps), [`CoreError::AggregationConstantTerm`] if the statement is
/// false (the honest prover cannot even assert its own `b''`), and
/// [`CoreError::NormBudget`] when the revealed digits overrun `(β')²` — the
/// Section 5.4 case where the paper's remedy is to restart the protocol (or
/// widen the commitment), so the caller re-runs with a fresh `key_seed` rather
/// than the prover silently proving a longer witness than it claimed.
pub fn prove_core<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    s: &[WitnessVec<R, D>],
) -> Result<CoreMessage<R, D>, CoreError> {
    let params = &setup.params;
    let r = relation.multiplicity;
    let n = relation.rank;
    params.slack_ok(relation)?;
    if s.len() != r || s.iter().any(|v| v.len() != n) {
        return Err(CoreError::WrongShape {
            got: s.len(),
            expected: r,
        });
    }
    let norm_sq = witness_norm_sq(s);
    if norm_sq > relation.norm_bound_sq {
        return Err(CoreError::WitnessNorm {
            norm_sq,
            bound_sq: relation.norm_bound_sq,
        });
    }
    // `t⃗` and `h⃗` are uniform in `Z_q`, so their planes must cover every
    // residue. `g⃗` is short, and §5.4 budgets its planes by its *magnitude*
    // instead — checked against the actual garbage below.
    params.decomp1.validate::<R>().map_err(map_digit)?;
    // u₁ is the *sum* of the two outer parts, so the keys must share its
    // height; zipping mismatched lengths would silently drop rows.
    if params.key_c.rows() != params.key_b.rows() {
        return Err(CoreError::WrongShape {
            got: params.key_c.rows(),
            expected: params.key_b.rows(),
        });
    }

    // Committing: tᵢ = A·sᵢ, then the outer commitment u₁ over the digit
    // planes of t⃗ *and* of the garbage g (which is challenge-independent, so
    // §5.2 folds it into u₁ rather than u₂).
    let groups: Vec<&[Elt<R, D>]> = s.iter().map(|v| v.as_slice()).collect();
    let t = apply_blockwise(&params.inner_key, &groups).map_err(|_| CoreError::WrongShape {
        got: n,
        expected: params.inner_key.cols(),
    })?;
    let t_digits = params.decomp1.split(&t);
    let g = garbage_g(s);
    let g_tri = triangle(&g, r);
    // §5.4 sizes `t₂` from the *modelled* Gaussian magnitude of `g`. If this
    // run's actual garbage is longer than the planes can hold, the split would
    // recompose to a different value, so the prover stops rather than proves a
    // longer object than it claimed (the paper's remedy is to widen `t₂`).
    if !params.decomp2.covers_magnitude(max_abs_coeff(&g_tri)) {
        return Err(CoreError::DigitCapacity);
    }
    let g_digits = params.decomp2.split(&g_tri);
    let mut u1 = params
        .key_b
        .matvec(&t_digits)
        .map_err(|_| CoreError::WrongShape {
            got: t_digits.len(),
            expected: params.key_b.cols(),
        })?;
    let c_part = params
        .key_c
        .matvec(&g_digits)
        .map_err(|_| CoreError::WrongShape {
            got: g_digits.len(),
            expected: params.key_c.cols(),
        })?;
    for (dst, src) in u1.iter_mut().zip(c_part.iter()) {
        *dst += src.clone();
    }

    let mut challenger = CoreChallenger::<R, D>::new(
        key_seed,
        &setup.space,
        relation,
        params.aggregation_count,
        PROJECTION_ROWS,
    );
    let projection_seed = challenger.bind_outer1(&u1);
    let projection = Projection::<R, D>::from_seed(&projection_seed, PROJECTION_ROWS, r, n);

    // Projecting.
    let p = projection.project(s);
    let budget_p = 128 * relation.norm_bound_sq;
    let p_sq = integer_norm_sq(&p);
    if p_sq > budget_p {
        return Err(CoreError::ProjectionNorm {
            norm_sq: p_sq,
            budget: budget_p,
        });
    }
    let p_mod: Vec<R> = p.iter().map(|v| reduce_scalar::<R>(*v)).collect();

    // Aggregating (twice).
    let (psi, omega) = challenger.bind_projection(&p);
    let coeffs = aggregate_first(relation, &projection, &psi, &omega)?;
    let b_double = prover_b_double(&coeffs, s);
    for (k, claim) in first_aggregation_claim(relation, &psi, &omega, &p_mod)
        .iter()
        .enumerate()
    {
        if constant_term(&b_double[k]) != *claim {
            return Err(CoreError::AggregationConstantTerm { index: k });
        }
    }
    let (alpha, beta) = challenger.bind_aggregation(&b_double);
    let statement = aggregate_second(relation, &coeffs, &b_double, &alpha, &beta);

    // Amortizing: the h garbage depends on the aggregated φ, so it is
    // committed separately as u₂, and only then do the cᵢ open everything.
    let h = garbage_h(s, &statement.phi);
    let h_digits = params.decomp1.split(&triangle(&h, r));
    let u2 = params
        .key_d
        .matvec(&h_digits)
        .map_err(|_| CoreError::WrongShape {
            got: h_digits.len(),
            expected: params.key_d.cols(),
        })?;
    let c = challenger.bind_outer2(&u2, r)?;
    let mut z: WitnessVec<R, D> = vec![zero_elt::<R, D>(); n];
    for i in 0..r {
        for x in 0..n {
            z[x] += s[i][x].clone() * c[i].clone();
        }
    }
    let (z_lo, z_hi) = split_z(params.bounds.base, &z);
    let z_digits = interleave_z(&z_lo, &z_hi);

    let message = CoreMessage {
        u1,
        u2,
        p,
        b_double,
        z,
        z_digits,
        t,
        t_digits,
        g,
        g_digits,
        h,
        h_digits,
    };
    // The prover checks its own proof: a norm overrun is the Section 5.4
    // event that calls for a restart, and anything else is a bug or a false
    // statement, never a proof to ship.
    verify_core(setup, relation, key_seed, &message)?;
    Ok(message)
}

/// Rows of the Johnson–Lindenstrauss projection: the paper fixes 256.
pub const PROJECTION_ROWS: usize = 256;

/// Runs Figure 3, lines 3–20, and returns **every** rejection the message
/// triggers, in the paper's line order. An empty vector is an accepted proof.
///
/// [`verify_core`] is this function followed by "take the first", which is all
/// a verifier needs. The full report exists because a scheme — and this
/// module's tests — has to know that each line *owns* a rejection: under
/// Fiat–Shamir one tampered component changes every later challenge, so a
/// single-error API reports whichever check happens to run first, and a check
/// that is only ever reached second is indistinguishable from one that never
/// runs.
///
/// # Errors
/// Each [`CoreError`] names its own Figure 3 line; see the module table. A
/// `WrongShape` or `Challenge` failure means the remaining checks could not be
/// evaluated at all, so it is returned alone.
pub fn verify_core_report<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    message: &CoreMessage<R, D>,
) -> Vec<CoreError> {
    let params = &setup.params;
    let r = relation.multiplicity;
    let n = relation.rank;
    let triangle_len = (r * r + r) / 2;
    if let Err(e) = params.slack_ok(relation) {
        return vec![e];
    }
    if message.z.len() != n
        || message.t.len() != r * params.inner_key.rows()
        || message.g.len() != r * r
        || message.h.len() != r * r
        || message.g_digits.len() != triangle_len * params.decomp2.digits
        || message.h_digits.len() != triangle_len * params.decomp1.digits
        || message.z_digits.len() != 2 * n
        || message.b_double.len() != params.aggregation_count
    {
        return vec![CoreError::WrongShape {
            got: message.z.len(),
            expected: n,
        }];
    }
    if message.p.len() != PROJECTION_ROWS {
        return vec![CoreError::WrongShape {
            got: message.p.len(),
            expected: PROJECTION_ROWS,
        }];
    }
    if params.key_c.rows() != params.key_b.rows() {
        return vec![CoreError::WrongShape {
            got: params.key_c.rows(),
            expected: params.key_b.rows(),
        }];
    }
    let mut failures: Vec<CoreError> = Vec::new();

    // Figure 2's projection gate and lines 8–14 need nothing from the
    // transcript, and neither do the outer commitments of lines 19–20, so they
    // are evaluated first. Every check below *pushes* rather than returns: see
    // the doc comment on why the report is the whole set.
    //
    // Figure 2: ‖p‖₂² ≤ 128·β² over the integers, which the slack condition
    // above licenses.
    let budget_p = 128 * relation.norm_bound_sq;
    let p_sq = integer_norm_sq(&message.p);
    if p_sq > budget_p {
        failures.push(CoreError::ProjectionNorm {
            norm_sq: p_sq,
            budget: budget_p,
        });
    }

    // Lines 8-9: symmetry.
    let mut asymmetric = false;
    for i in 0..r {
        for j in 0..r {
            if message.g[i * r + j] != message.g[j * r + i]
                || message.h[i * r + j] != message.h[j * r + i]
            {
                asymmetric = true;
            }
        }
    }
    if asymmetric {
        failures.push(CoreError::AsymmetricGarbage);
    }

    // Lines 10-13: the digit decompositions.
    let g_tri = triangle(&message.g, r);
    let h_tri = triangle(&message.h, r);
    for check in [
        check_digits(&params.decomp1, &message.t, &message.t_digits),
        check_digits(&params.decomp2, &g_tri, &message.g_digits),
        check_digits(&params.decomp1, &h_tri, &message.h_digits),
        check_short_split(params.bounds.base, &message.z, &message.z_digits),
    ] {
        if let Err(e) = check {
            failures.push(e);
        }
    }

    // Line 14, equation (5).
    let actual = params.decomp1.norm_sq(&message.z_digits)
        + params.decomp1.norm_sq(&message.t_digits)
        + params.decomp2.norm_sq(&message.g_digits)
        + params.decomp1.norm_sq(&message.h_digits);
    if actual > params.bounds.beta_prime_sq {
        failures.push(CoreError::NormBudget {
            actual,
            budget: params.bounds.beta_prime_sq,
        });
    }

    // Lines 19-20: the outer commitments, recomputed from the revealed digits.
    let mut u1 = match params.key_b.matvec(&message.t_digits) {
        Ok(v) => v,
        Err(_) => {
            return vec![CoreError::WrongShape {
                got: message.t_digits.len(),
                expected: params.key_b.cols(),
            }]
        }
    };
    let c_part = match params.key_c.matvec(&message.g_digits) {
        Ok(v) => v,
        Err(_) => {
            return vec![CoreError::WrongShape {
                got: message.g_digits.len(),
                expected: params.key_c.cols(),
            }]
        }
    };
    for (dst, src) in u1.iter_mut().zip(c_part.iter()) {
        *dst += src.clone();
    }
    if u1 != message.u1 {
        failures.push(CoreError::OuterCommitment1);
    }
    let u2 = match params.key_d.matvec(&message.h_digits) {
        Ok(v) => v,
        Err(_) => {
            return vec![CoreError::WrongShape {
                got: message.h_digits.len(),
                expected: params.key_d.cols(),
            }]
        }
    };
    if u2 != message.u2 {
        failures.push(CoreError::OuterCommitment2);
    }

    // Figure 3 lines 3-7 and the challenge draws of lines 15-18: the aggregated
    // coefficients, the projection matrix they are keyed to, and the `cᵢ`.
    // All derived, never taken from the wire, and all *shared* with the
    // recursion's target-relation builder through [`derive_view`] so the two
    // cannot drift into proving different statements.
    let view = match derive_view(setup, relation, key_seed, message) {
        Ok(v) => v,
        Err(e) => return vec![e],
    };
    for (k, claim) in view.claims.iter().enumerate() {
        if constant_term(&message.b_double[k]) != *claim {
            failures.push(CoreError::AggregationConstantTerm { index: k });
        }
    }
    let statement = &view.statement;
    let c = &view.c;

    // Line 15: A·z =? Σ cᵢtᵢ.
    let az = match params.inner_key.matvec(&message.z) {
        Ok(v) => v,
        Err(_) => {
            return vec![CoreError::WrongShape {
                got: n,
                expected: params.inner_key.cols(),
            }]
        }
    };
    let kappa = params.inner_key.rows();
    let mut rhs = vec![zero_elt::<R, D>(); kappa];
    for i in 0..r {
        for x in 0..kappa {
            rhs[x] += message.t[i * kappa + x].clone() * c[i].clone();
        }
    }
    if az != rhs {
        failures.push(CoreError::InnerLink);
    }

    // Line 16: ⟨z,z⟩ =? Σ g_ij cᵢc_j.
    let zz = inner_product(&message.z, &message.z);
    let mut acc = zero_elt::<R, D>();
    for i in 0..r {
        for j in 0..r {
            let cc = c[i].clone() * c[j].clone();
            acc += message.g[i * r + j].clone() * cc;
        }
    }
    if zz != acc {
        failures.push(CoreError::SelfInnerProduct);
    }

    // Line 17: Σᵢ⟨φᵢ,z⟩cᵢ =? Σ h_ij cᵢc_j.
    let mut lhs = zero_elt::<R, D>();
    for i in 0..r {
        lhs += inner_product(&statement.phi[i], &message.z).mul_ref(&c[i]);
    }
    let mut acc = zero_elt::<R, D>();
    for i in 0..r {
        for j in 0..r {
            let cc = c[i].clone() * c[j].clone();
            acc += message.h[i * r + j].clone() * cc;
        }
    }
    if lhs != acc {
        failures.push(CoreError::LinearClaim);
    }

    // Line 18: Σ a_ij g_ij + Σ hᵢᵢ =? b.
    let mut acc = zero_elt::<R, D>();
    for i in 0..r {
        for j in 0..r {
            acc += statement.a[i][j].clone().mul_ref(&message.g[i * r + j]);
        }
    }
    for i in 0..r {
        acc += message.h[i * r + i].clone();
    }
    if acc != statement.b {
        failures.push(CoreError::Relation);
    }
    failures
}

/// [`verify_core_report`] reduced to what a verifier acts on: the first
/// rejection, or `Ok(())` when the report is empty.
///
/// # Errors
/// A [`CoreError`] naming the first check that failed; see the module table.
pub fn verify_core<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    message: &CoreMessage<R, D>,
) -> Result<(), CoreError> {
    match verify_core_report(setup, relation, key_seed, message)
        .into_iter()
        .next()
    {
        Some(err) => Err(err),
        None => Ok(()),
    }
}

/// Maps a digit failure onto the core-argument error type.
fn map_digit(err: DigitError) -> CoreError {
    match err {
        DigitError::CapacityTooSmall { .. } => CoreError::DigitCapacity,
        DigitError::WrongPlaneCount { .. } => CoreError::DigitRecombination,
        DigitError::PlaneTooWide { .. } => CoreError::DigitBound,
        DigitError::Recombination => CoreError::DigitRecombination,
    }
}

/// The digit check of Figure 3 lines 11–13 as named rejections.
fn check_digits<R: Ring + CenteredRing, const D: usize>(
    decomp: &Decomposition,
    values: &[Elt<R, D>],
    planes: &[Elt<R, D>],
) -> Result<(), CoreError> {
    decomp.check(values, planes).map_err(map_digit)
}

/// Figure 3 line 10: `z = z⁽⁰⁾ + b·z⁽¹⁾` with `‖z⁽⁰⁾‖∞ ≤ b/2`.
fn check_short_split<R: Ring + CenteredRing, const D: usize>(
    base: u64,
    z: &WitnessVec<R, D>,
    planes: &[Elt<R, D>],
) -> Result<(), CoreError> {
    if planes.len() != 2 * z.len() {
        return Err(CoreError::DigitRecombination);
    }
    let weight = const_elt::<R, D>(i64::try_from(base).expect("base fits i64"));
    for (j, v) in z.iter().enumerate() {
        let lo = &planes[2 * j];
        let hi = &planes[2 * j + 1];
        if lo.clone() + hi.clone().mul_ref(&weight) != *v {
            return Err(CoreError::DigitRecombination);
        }
        for c in lo.coefficients() {
            if c.abs_infinity() > base / 2 {
                return Err(CoreError::DigitBound);
            }
        }
    }
    Ok(())
}

/// Reduces a projection response coordinate into `Z_q` as a canonical
/// representative.
fn reduce_scalar<R: Ring>(v: i64) -> R {
    let modulus = i64::try_from(R::MODULUS).expect("q fits i64");
    from_centered::<R>(v.rem_euclid(modulus))
}

// ────────────────────────────── §5.3: recursion ────────────────────────────
//
// Section 5.3 (printed pp.14–15) is the compaction step, and Figure 3's caption
// states what it is: *"the algorithm checks that the last prover message is a
// witness for the target relation, which is an instance of the principal
// relation"*. One execution of the core argument is therefore a
// proof-of-knowledge *reduction* (Def. 3.5, p.7) from its own statement to that
// target instance, and Lemma 3.7 (p.8) composes it with another execution,
// adding soundness errors. That is why the step needs no new algebra, only new
// bookkeeping:
//
// * **committed at a level** ([`CoreMessage`]): `u₁`, the projection response
//   `p`, the `⌈128/log q⌉` polynomials `b″(k)`, `u₂`, and — at the last level
//   only — `z, t, g, h`. The `t⃗, g⃗, h⃗` of §5.2 *are* the digit planes
//   ("let `t⃗ ∈ R_q^{rt₁κ}` be a concatenation of all the decomposition parts",
//   p.12), so a level's target witness is exactly `(z⁽⁰⁾, z⁽¹⁾, v)` with
//   `v = t‖g‖h` (p.15).
// * **recomputed by the verifier** ([`derive_view`]): `Π`, `ψ`, `ω`, `a″`,
//   `φ″`, `α`, `β`, the aggregated `(a_ij, φ_i, b)` and the `c_i`, all from the
//   transcript — Definition 3.5's `Ṽ(x₁, c₁, …, c_k, z₁, …, z_{k′})`.
// * **the target instance** ([`target_instance`]): `K′ = κ+κ₁+κ₂+3` equations
//   (eq. (6)), an **empty** `F′` family, and one consolidated budget
//   `(β′)² = 2γ²/b² + γ₁² + γ₂²` (eq. (5)).
//
// Where the norm budget grows, and what the challenge set must supply:
//
// * Amortization multiplies the norm by the challenge *energy*: `‖z‖ ≤ γ = β√τ`
//   (§5.4, p.19), so `τ` is paid **per level**, together with the decomposition
//   base `b`, which §5.4 fixes by balancing the digit widths.
// * The bound the commitments must be binding *for* is `(b+1)β′`, because (5)
//   only implies `‖z‖ = ‖z⁽⁰⁾ + bz⁽¹⁾‖ ≤ (1+b)β′` (p.15), and Appendix B
//   (pp.32–33) extracts weak openings of norms `2(b+1)β′`, `4T(b+1)β′` and
//   `(b+1)β′ + 2T√(128/30)·β`. Theorem 5.1 (p.19) therefore needs Module-SIS for
//   rank `κ` and norm `max(8T(b+1)β′, 2(b+1)β′ + 4T√(128/30)·β)` — so the
//   challenge *operator norm* `T` multiplies the hardness bound, and Remark 5.2
//   (p.20) grows it again by `√(128/30)` for every level whose norm is no longer
//   checked directly: [`recursion_msis_norm_sq`]. The witness norm *shrinks*
//   (`b ≥ 2`); the hardness bound is what grows, and it is why §6.1 (p.27)
//   recomputes `κ, κ₁, κ₂` "in each level so that Module-SIS meets our desired
//   security level of 128 bits".
// * Challenge requirements, §2 p.6 verbatim: `C ⊂ R` with **`c₁ − c₂`
//   invertible for any pair of distinct `c₁, c₂ ∈ C`**, and `‖c‖₂² ≤ τ`,
//   `‖c‖_op ≤ T`; concretely 23 zero, 31 `±1` and 10 `±2` coefficients
//   (`τ = 71`), rejected until `‖c‖_op ≤ 15` (≈ 6 draws), with invertibility of
//   differences cited to [LS18, Cor. 1.2]. **The unit the extraction divides by
//   is the difference `c̄ᵢ = cᵢ − c′ᵢ`, never `cᵢ` itself** — Appendix B p.32
//   recovers `s∗ᵢ = (z − z′)/c̄ᵢ` — so a challenge with 23 zero coefficients is
//   fine precisely because nothing demands it be a unit, and no annihilator is
//   ever invoked. The recursion inherits this unchanged, since every level
//   re-draws its `cᵢ` from the same `C`.
//
// What the step costs, and whether it pays, is decided by the §5.7 model
// ([`SizeModel`], [`RecursionPlan`]) in exact integer arithmetic.

/// Everything a level's verifier recomputes from the transcript.
///
/// This is Definition 3.5's `Ṽ` output: the target statement of one execution is
/// a function of the source statement and exactly this data, which is why
/// [`target_instance`] consumes a [`CoreView`] instead of re-deriving challenges.
#[derive(Debug, Clone)]
pub struct CoreView<R: Ring, const D: usize> {
    /// The Johnson–Lindenstrauss matrix `Π`, keyed to `u₁` (§5.2 "Projecting").
    pub projection: Projection<R, D>,
    /// `ψ⁽ᵏ⁾ ∈ Z_q^L`, the weights over `F′` (Fig. 3 line 3).
    pub psi: Vec<Vec<R>>,
    /// `ω⁽ᵏ⁾ ∈ Z_q^256`, the weights over the projection rows (line 4).
    pub omega: Vec<Vec<R>>,
    /// `a″⁽ᵏ⁾`, `φ″⁽ᵏ⁾` (Fig. 3 lines 3–4).
    pub coeffs: Vec<AggregatedCoeffs<R, D>>,
    /// The verifier's own side of `b″(k)₀ =? ⟨ω⁽ᵏ⁾, p⟩ + Σₗ ψₗ⁽ᵏ⁾ b′₀⁽ˡ⁾` (Fig. 2).
    pub claims: Vec<R>,
    /// The single aggregated function `F = Σ α_k f⁽ᵏ⁾ + Σ β_k f″⁽ᵏ⁾` (lines 5–7).
    pub statement: QuadFn<R, D>,
    /// The `r` amortization challenges `cᵢ ∈ C` (§5.2 "Amortizing").
    pub c: Vec<Elt<R, D>>,
}

/// Replays Figure 3 lines 3–7 plus the challenge draws behind lines 15–18.
///
/// Extracted from [`verify_core_report`] so the two share one code path: under
/// Fiat–Shamir the target relation *is* defined by these values, and a second
/// derivation could drift into a recursion that proves a different statement
/// than the one the verifier checked.
///
/// # Errors
/// [`CoreError::WrongShape`] or [`CoreError::Challenge`] when the transcript
/// cannot be replayed at all, in which case no later check is meaningful.
pub fn derive_view<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    message: &CoreMessage<R, D>,
) -> Result<CoreView<R, D>, CoreError> {
    derive_view_at_head(setup, relation, key_seed, &CoreHead::of(message))
}

/// [`derive_view`], reading only the head.
///
/// The split is the content of Definition 3.5, not a code-organization choice:
/// every value the target statement is built from — `Π`, `ψ`, `ω`, `a″`, `φ″`,
/// `α`, `β`, the aggregated `(a_ij, φ_i, b)` and the `cᵢ` — is derived here, and
/// nothing here reads `z, t, g, h` or their planes. A level's target is therefore
/// fixed before its last message exists, which is what lets that message be
/// *proved* by the next level instead of sent.
///
/// # Errors
/// [`CoreError::WrongShape`] or [`CoreError::Challenge`] when the transcript
/// cannot be replayed at all, in which case no later check is meaningful.
pub fn derive_view_at_head<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    head: &CoreHead<R, D>,
) -> Result<CoreView<R, D>, CoreError> {
    let params = &setup.params;
    let r = relation.multiplicity;
    let mut challenger = CoreChallenger::<R, D>::new(
        key_seed,
        &setup.space,
        relation,
        params.aggregation_count,
        PROJECTION_ROWS,
    );
    let projection_seed = challenger.bind_outer1(&head.u1);
    let projection =
        Projection::<R, D>::from_seed(&projection_seed, PROJECTION_ROWS, r, relation.rank);
    let p_mod: Vec<R> = head.p.iter().map(|v| reduce_scalar::<R>(*v)).collect();
    let (psi, omega) = challenger.bind_projection(&head.p);
    let coeffs = aggregate_first(relation, &projection, &psi, &omega)?;
    let claims = first_aggregation_claim(relation, &psi, &omega, &p_mod);
    let (alpha, beta) = challenger.bind_aggregation(&head.b_double);
    let statement = aggregate_second(relation, &coeffs, &head.b_double, &alpha, &beta);
    let c = challenger.bind_outer2(&head.u2, r)?;
    Ok(CoreView {
        projection,
        psi,
        omega,
        coeffs,
        claims,
        statement,
        c,
    })
}

/// Which Figure 3 line a target-relation equation restates (§5.3, eq. (6)).
///
/// The recursion adds no *new* arithmetic claim — that is its whole point — so a
/// failure at level `i+1` must be attributable to the level-`i` line it came
/// from, and each variant is its own rejection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TargetEquation {
    /// Level line 15, `A·z = Σᵢ cᵢtᵢ`: one equation per row of `A`.
    InnerLink {
        /// Row of `A`.
        row: usize,
    },
    /// Level line 19, `u₁ = B·t⁽ᵏ⁾ + C·g⁽ᵏ⁾`: one per row of `B`.
    OuterCommitment1 {
        /// Row of `B`/`C`.
        row: usize,
    },
    /// Level line 20, `u₂ = D·h⁽ᵏ⁾`: one per row of `D`.
    OuterCommitment2 {
        /// Row of `D`.
        row: usize,
    },
    /// Level line 16, `⟨z,z⟩ = Σ g_ij cᵢc_j` — the only quadratic equation.
    SelfInnerProduct,
    /// Level line 17, `Σᵢ⟨φᵢ,z⟩cᵢ = Σ h_ij cᵢc_j`.
    LinearClaim,
    /// Level line 18, `Σ a_ij g_ij + Σᵢ h_ii = b`.
    Relation,
}

impl TargetEquation {
    /// The paper's own wording, so a rejection names its line.
    #[must_use]
    pub fn name(&self) -> &'static str {
        match self {
            Self::InnerLink { .. } => "target eq. (line 15): A·z = Σ cᵢtᵢ",
            Self::OuterCommitment1 { .. } => "target eq. (line 19): u₁ = B·t + C·g",
            Self::OuterCommitment2 { .. } => "target eq. (line 20): u₂ = D·h",
            Self::SelfInnerProduct => "target eq. (line 16): ⟨z,z⟩ = Σ g_ij cᵢc_j",
            Self::LinearClaim => "target eq. (line 17): Σ⟨φᵢ,z⟩cᵢ = Σ h_ij cᵢc_j",
            Self::Relation => "target eq. (line 18): Σ a_ij g_ij + Σ hᵢᵢ = b",
        }
    }
}

/// §5.3's reblocking of a level's target witness, plus §5.7's rule for choosing
/// it.
///
/// `z⁽⁰⁾ = s′₁‖⋯‖s′_ν`, `z⁽¹⁾ = s′_{ν+1}‖⋯‖s′_{2ν}`, and
/// `v = s′_{2ν+1}‖⋯‖s′_{2ν+μ}`, all zero-padded to the common rank
/// `n′ = max{⌈n/ν⌉, ⌈m/μ⌉}`, so the target has `r′ = 2ν + μ` vectors (p.15).
/// §5.3 asks for `n/ν ≈ m/μ` "to avoid padding too much" and §5.7 (p.21) for
/// `2ν ≈ m`; [`TargetShape::derive`] makes that an explicit search over `(ν, μ)`
/// minimizing the target's own §5.7 proof size, because padding is the only
/// thing that can make the target *wider* than the `2n + m` elements it must
/// hold.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TargetShape {
    /// `ν ≥ 1`: the number of blocks `z⁽⁰⁾` (and `z⁽¹⁾`) is cut into.
    pub nu: usize,
    /// `μ ≥ 1`: the number of blocks `v` is cut into.
    pub mu: usize,
    /// `n′`, the target rank.
    pub rank: usize,
    /// `m`, the width of `v = t‖g‖h` in ring elements.
    pub v_width: usize,
    /// `n`, the source rank, kept so [`Self::fits`] can be re-checked.
    pub source_rank: usize,
}

impl TargetShape {
    /// `m = r·t₁·κ + (t₁+t₂)·(r²+r)/2`: the width of `v`, counting *planes* —
    /// which is what the prover transmits (pp.12, 15).
    #[must_use]
    pub const fn width_v(r: usize, t1: usize, t2: usize, kappa: usize) -> usize {
        r * t1 * kappa + (t1 + t2) * (r * r + r) / 2
    }

    /// `r′ = 2ν + μ`, the target multiplicity.
    #[must_use]
    pub const fn multiplicity(&self) -> usize {
        2 * self.nu + self.mu
    }

    /// `K′ = κ + κ₁ + κ₂ + 3`, the number of family-`F` equations of (6).
    #[must_use]
    pub const fn equation_count(kappa: usize, kappa1: usize, kappa2: usize) -> usize {
        kappa + kappa1 + kappa2 + 3
    }

    /// The padded width `(2ν+μ)·n′` of the target witness.
    #[must_use]
    pub const fn target_width(&self) -> usize {
        self.multiplicity() * self.rank
    }

    /// Whether the blocks actually cover the source: `ν·n′ ≥ n` and `μ·n′ ≥ m`.
    /// §5.3's zero-padding is only sound when it is *large* enough to hold
    /// everything, so a shape that does not fit describes a relation the honest
    /// witness is not in.
    #[must_use]
    pub const fn fits(&self) -> bool {
        self.nu >= 1
            && self.mu >= 1
            && self.rank >= 1
            && self.source_rank >= 1
            && self.nu * self.rank >= self.source_rank
            && self.mu * self.rank >= self.v_width
    }

    /// Concatenated offset of `z⁽¹⁾` in the target witness.
    #[must_use]
    pub const fn off_z1(&self) -> usize {
        self.nu * self.rank
    }

    /// Concatenated offset of `v` in the target witness.
    #[must_use]
    pub const fn off_v(&self) -> usize {
        2 * self.nu * self.rank
    }

    /// Searches the target rank `n′` minimizing the target's §5.7 proof size.
    ///
    /// `n′` is the only real degree of freedom: once it is fixed, §5.3's rule
    /// gives the *fewest* blocks that cover the witness, `ν = ⌈n/n′⌉` and
    /// `μ = ⌈m/n′⌉`, so `r′ = 2ν + μ` is minimal too. Small `n′` therefore buys a
    /// narrow witness but pays `O(r′²)` garbage planes at the next level, and
    /// large `n′` the other way round; the candidate set below is the set of
    /// breakpoints where either count changes, which is where the optimum lives.
    #[must_use]
    pub fn derive(
        source_rank: usize,
        v_width: usize,
        target_beta_sq: u128,
        model: &SizeModel,
    ) -> Self {
        let n = source_rank.max(1);
        let m = v_width.max(1);
        let mut candidates: Vec<usize> = vec![1, n, m, 2 * n + m];
        // Every rank at which `⌈n/ν⌉` or `⌈m/μ⌉` is still small, plus the §5.3
        // balance `n/ν ≈ m/μ` itself for each ν.
        for k in 1..=256usize {
            candidates.push(ceil_usize(n, k));
            candidates.push(ceil_usize(m, k));
            candidates.push(ceil_usize(m * k, n));
        }
        let mut best: Option<(u128, usize, Self)> = None;
        for rank in candidates {
            if rank == 0 || rank > 2 * n + m {
                continue;
            }
            let shape = Self {
                nu: ceil_usize(n, rank),
                mu: ceil_usize(m, rank),
                rank,
                v_width,
                source_rank,
            };
            if !shape.fits() {
                continue;
            }
            let cost = model
                .size(shape.multiplicity(), shape.rank, target_beta_sq)
                .total_bits();
            let better = match best {
                None => true,
                Some((c, w, _)) => (cost, shape.target_width()) < (c, w),
            };
            if better {
                best = Some((cost, shape.target_width(), shape));
            }
        }
        best.expect("rank = 2n+m gives nu = mu = 1, which always fits")
            .2
    }
}

/// The §5.7 size model, evaluated in exact integer arithmetic.
///
/// ```text
/// core = (κ₁+κ₂)·d·log q + 256·log(12β/√2) + ⌈128/log q⌉·d·log q + 4·128
/// last = n·d·log(12β√(τ/(nd)))                 masked opening z⃗
///      + r·κ·d·log q                           inner commitments t⃗ᵢ
///      + (r²+r)/2·d·log(12√(2/(r²nd))·β²)      garbage g_ij
///      + (r²+r)/2·d·log q                      garbage h_ij
/// ```
///
/// Every width is a ceiling over the integers, so the model never *under*-reports
/// a size. The `last` column is the target relation's witness, so terminating a
/// level costs `last` and recursing costs `core + last` of the target: the
/// paper's stop rule (§5.7 p.21, §6.1 p.27 — recurse "until the size of the last
/// prover message is not anymore bigger than an optimal proof for it") is exactly
/// `last ≤ core_target + last_target`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SizeModel {
    /// `q`.
    pub modulus: u64,
    /// `d`.
    pub degree: usize,
    /// `τ = ‖c‖₂²` of the challenge space.
    pub tau: u64,
    /// Inner commitment rank `κ`.
    pub kappa: usize,
    /// Outer rank `κ₁`.
    pub kappa1: usize,
    /// Outer rank `κ₂`.
    pub kappa2: usize,
    /// `⌈128/log q⌉`.
    pub aggregation_count: usize,
    /// Rows of the projection — the paper's 256.
    pub projection_rows: usize,
}

/// The bits one execution puts on the wire (§5.7).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LevelSize {
    /// `u₁, u₂, p, b″(k)` and the challenge seeds.
    pub core_bits: u128,
    /// `z⃗, t⃗ᵢ, g_ij, h_ij` — which *is* the target relation's witness.
    pub last_message_bits: u128,
}

impl LevelSize {
    /// `core + last`: the cost of proving a statement of this shape with one
    /// execution and then revealing its target witness.
    #[must_use]
    pub const fn total_bits(&self) -> u128 {
        self.core_bits + self.last_message_bits
    }
}

impl SizeModel {
    /// The model implied by a live level: its ring, its challenge space's `τ`, and
    /// the three commitment ranks its CRS actually has. Reading the shape off the
    /// setup rather than restating it is what keeps §5.7's decision and the
    /// transcript's own commitments about each other.
    #[must_use]
    pub fn of<R: Ring + CenteredRing, const D: usize>(setup: &CoreSetup<R, D>) -> Self {
        let params = &setup.params;
        Self {
            modulus: R::MODULUS,
            degree: D,
            tau: setup.space.tau(),
            kappa: params.inner_key.rows(),
            kappa1: params.key_b.rows(),
            kappa2: params.key_d.rows(),
            aggregation_count: params.aggregation_count,
            projection_rows: PROJECTION_ROWS,
        }
    }

    /// The §5.7 sizes of a relation of shape `(r, n, β²)`.
    #[must_use]
    pub fn size(&self, r: usize, n: usize, beta_sq: u128) -> LevelSize {
        let q_width = log2_ceil_u128(u128::from(self.modulus));
        let d = wide(self.degree);
        let nd = wide(n.saturating_mul(self.degree)).max(1);
        let r_w = wide(r).max(1);
        let tri = wide((r * r + r) / 2).max(1);
        // A width, never a magnitude: each `log…` below is the *bit* count §5.7
        // charges per coefficient, so the ceiling of log₂ of the modelled
        // magnitude is the term — the magnitudes themselves are √'s of ratios and
        // are rounded *up* so the width can only over-state.
        let p_width = log2_ceil_u128(isqrt_ceil(72u128.saturating_mul(beta_sq).max(1)));
        let core_bits = wide(self.kappa1 + self.kappa2) * d * q_width
            + wide(self.projection_rows) * p_width
            + wide(self.aggregation_count) * d * q_width
            + 4 * 128;
        // log(12β√(τ/(nd))) = log√(144β²τ/(nd))
        let z_width = log2_ceil_u128(isqrt_ceil(ceil_div(
            144u128
                .saturating_mul(beta_sq)
                .saturating_mul(wide(self.tau as usize)),
            nd,
        )));
        // log(12√(2β⁴/(r²nd))) = log√(288β⁴/(r²nd))
        let g_width = log2_ceil_u128(isqrt_ceil(ceil_div(
            288u128.saturating_mul(beta_sq).saturating_mul(beta_sq),
            r_w.saturating_mul(r_w).saturating_mul(nd).max(1),
        )));
        LevelSize {
            core_bits,
            last_message_bits: nd * z_width
                + r_w * wide(self.kappa) * d * q_width
                + tri * d * g_width
                + tri * d * q_width,
        }
    }
}

/// What one recursion level decides, in the §5.7 stop rule.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RecursionPlan {
    /// The chosen reblocking `(ν, μ, n′, m)`.
    pub shape: TargetShape,
    /// The source level's §5.4 bounds, whose `(β′)²` is the target's budget.
    pub bounds: NormBounds,
    /// Cost of running the target through one more execution.
    pub recursed: LevelSize,
    /// `last_message_bits` of the source level: what terminating now costs.
    pub terminate_bits: u128,
}

impl RecursionPlan {
    /// Derives the plan for one level of shape `(r, n, β²)`, with §5.4's bounds
    /// recomputed for that shape — which is what a *hypothetical* level needs.
    #[must_use]
    pub fn derive(model: &SizeModel, r: usize, n: usize, beta_sq: u128) -> Self {
        let bounds = NormBounds::derive(
            beta_sq,
            model.modulus,
            r,
            n,
            model.kappa,
            model.degree,
            model.tau,
        );
        Self::with_bounds(model, r, n, beta_sq, bounds)
    }

    /// The same decision for a level whose §5.4 bounds are already fixed — i.e.
    /// the bounds its CRS was actually built with. Taking them from the level
    /// rather than recomputing them is what keeps the plan's `(t₁, t₂, β′)` equal
    /// to the ones the transcript committed to.
    #[must_use]
    pub fn with_bounds(
        model: &SizeModel,
        r: usize,
        n: usize,
        beta_sq: u128,
        bounds: NormBounds,
    ) -> Self {
        let v_width = TargetShape::width_v(r, bounds.t1, bounds.t2, model.kappa);
        let shape = TargetShape::derive(n, v_width, bounds.beta_prime_sq, model);
        let here = model.size(r, n, beta_sq);
        Self {
            shape,
            bounds,
            recursed: model.size(shape.multiplicity(), shape.rank, bounds.beta_prime_sq),
            terminate_bits: here.last_message_bits,
        }
    }

    /// The plan of a *live* level: its own size model, its own bounds, its own
    /// statement. Both sides of the recursion call this, so the reblocking is
    /// never data a prover gets to choose.
    #[must_use]
    pub fn of<R: Ring + CenteredRing, const D: usize>(
        setup: &CoreSetup<R, D>,
        relation: &Relation<R, D>,
    ) -> Self {
        Self::with_bounds(
            &SizeModel::of(setup),
            relation.multiplicity,
            relation.rank,
            relation.norm_bound_sq,
            setup.params.bounds,
        )
    }

    /// Whether taking this recursion step is smaller than terminating now.
    #[must_use]
    pub fn compacts(&self) -> bool {
        self.recursed.total_bits() < self.terminate_bits
    }

    /// Bits saved by this level's recursion step; negative when it costs.
    #[must_use]
    pub fn saving_bits(&self) -> i128 {
        self.terminate_bits as i128 - self.recursed.total_bits() as i128
    }
}

/// The `i ≤ j` triangle position of `(i, j)`, in [`triangle`]'s order.
///
/// The row start is `i·r − i(i−1)/2`, written `i·r − (i²−i)/2` so that `i = 0`
/// cannot underflow an unsigned intermediate.
fn triangle_pos(r: usize, i: usize, j: usize) -> usize {
    i * r - (i * i - i) / 2 + (j - i)
}

/// `⌈a/b⌉` for the accounting domain; `b = 0` is treated as `b = 1`.
fn ceil_div(a: u128, b: u128) -> u128 {
    if b <= 1 {
        return a;
    }
    (a / b) + if a % b == 0 { 0 } else { 1 }
}

/// `⌈a/b⌉` for counts, `b ≥ 1`.
fn ceil_usize(a: usize, b: usize) -> usize {
    if a == 0 {
        return 0;
    }
    (a - 1) / b + 1
}

/// `⌈log₂(v + 1)⌉`, at least 1: the bits a magnitude `v` needs.
fn log2_ceil_u128(v: u128) -> u128 {
    let mut bits = 1u128;
    while bits < 128 && (1u128 << bits) <= v {
        bits += 1;
    }
    bits
}

/// `-e`, in `R_q`.
fn neg_elt<R: Ring, const D: usize>(e: &Elt<R, D>) -> Elt<R, D> {
    zero_elt::<R, D>() - e.clone()
}

/// The `(b+1)`- and `T`-scaled Module-SIS bounds of Theorem 5.1 after `depth`
/// *further* recursion levels.
///
/// Remark 5.2 (p.20): once the verifier no longer checks a level's norm but only
/// receives a proof of it with slack `√(128/30)`, "the bounds for the Module-SIS
/// hardness must also be increased by this factor". `depth = 0` reproduces
/// [`NormBounds::msis_norm_sq`] exactly.
#[must_use]
pub fn recursion_msis_norm_sq(
    bounds: &NormBounds,
    beta_sq: u128,
    operator_norm: u64,
    depth: usize,
) -> [u128; 2] {
    let base = bounds.msis_norm_sq(beta_sq, operator_norm);
    let mut out = [0u128; 2];
    for (dst, src) in out.iter_mut().zip(base.iter()) {
        let mut v = *src;
        for _ in 0..depth {
            // ×128/30, rounded up, saturating rather than wrapping: an
            // unreachable bound is reported as unreachable, never as small.
            v = ceil_div(v.saturating_mul(128), 30);
        }
        *dst = v;
    }
    out
}

/// §5.3's split of the masked opening into the two vectors the target relation
/// contains: `z⁽⁰⁾` (centered residues mod `b`) and `z⁽¹⁾`.
///
/// [`Decomposition::split`] is *not* this: `t⃗, g⃗, h⃗` are uniform mod `q` and
/// decomposed into `t₁`/`t₂` planes, while `z⃗` is short over the integers and
/// split into exactly two additive parts (pp.14–15).
#[must_use]
pub fn split_z<R: Ring + CenteredRing, const D: usize>(
    base: u64,
    z: &WitnessVec<R, D>,
) -> (WitnessVec<R, D>, WitnessVec<R, D>) {
    let mut lo = Vec::with_capacity(z.len());
    let mut hi = Vec::with_capacity(z.len());
    for v in z {
        let (a, b) = split_short(base, v);
        lo.push(a);
        hi.push(b);
    }
    (lo, hi)
}

/// The wire layout of [`CoreMessage::z_digits`]: `z⁽⁰⁾, z⁽¹⁾` interleaved per
/// ring element, which is what [`check_short_split`] consumes.
#[must_use]
pub fn interleave_z<R: Ring, const D: usize>(
    lo: &[Elt<R, D>],
    hi: &[Elt<R, D>],
) -> Vec<Elt<R, D>> {
    let mut out = Vec::with_capacity(lo.len() + hi.len());
    for (a, b) in lo.iter().zip(hi.iter()) {
        out.push(a.clone());
        out.push(b.clone());
    }
    out
}

/// §5.3's reblocking: the target witness `(z⁽⁰⁾, z⁽¹⁾, v)` cut into
/// `r′ = 2ν + μ` vectors of rank `n′`, zero-padded.
#[must_use]
pub fn target_witness<R: Ring, const D: usize>(
    shape: &TargetShape,
    z_lo: &[Elt<R, D>],
    z_hi: &[Elt<R, D>],
    v: &[Elt<R, D>],
) -> Vec<WitnessVec<R, D>> {
    let mut out: Vec<WitnessVec<R, D>> =
        vec![vec![zero_elt::<R, D>(); shape.rank]; shape.multiplicity()];
    let one = const_elt::<R, D>(1);
    scatter(&mut out, 0, z_lo, &one);
    scatter(&mut out, shape.off_z1(), z_hi, &one);
    scatter(&mut out, shape.off_v(), v, &one);
    out
}

/// Writes `src` into the reblocked matrix at concatenated offset `start`,
/// scaled by `scale`. This is the one place that knows the layout, so the
/// witness and every equation coefficient are placed identically.
fn scatter<R, const D: usize>(
    dst: &mut [WitnessVec<R, D>],
    start: usize,
    src: &[Elt<R, D>],
    scale: &Elt<R, D>,
) where
    R: Ring,
{
    let rank = dst.first().map(|v| v.len()).expect("a row");
    for (i, e) in src.iter().enumerate() {
        let t = start + i;
        let cell = &mut dst[t / rank][t % rank];
        *cell = cell.clone() + e.clone().mul_ref(scale);
    }
}

/// Writes `addend · scale` at one concatenated position.
fn scatter_one<R, const D: usize>(
    dst: &mut [WitnessVec<R, D>],
    start: usize,
    scale: &Elt<R, D>,
    addend: &Elt<R, D>,
) where
    R: Ring,
{
    let rank = dst.first().map(|v| v.len()).expect("a row");
    let cell = &mut dst[start / rank][start % rank];
    *cell = cell.clone() + addend.clone().mul_ref(scale);
}

/// The target instance of one core execution: `(G, {}, β′)` and the witness
/// Figure 3's last message encodes.
#[derive(Debug, Clone)]
pub struct TargetInstance<R: Ring, const D: usize> {
    /// The `κ+κ₁+κ₂+3` equations of (6), the empty second family, and the
    /// consolidated budget (5).
    pub relation: Relation<R, D>,
    /// The honest target witness.
    pub witness: Vec<WitnessVec<R, D>>,
    /// The reblocking this instance was built under.
    pub shape: TargetShape,
    /// `κ`: how many line-15 equations there are.
    pub inner_rows: usize,
    /// `κ₁`: how many line-19 equations.
    pub outer1_rows: usize,
    /// `κ₂`: how many line-20 equations.
    pub outer2_rows: usize,
}

impl<R: Ring + CenteredRing, const D: usize> TargetInstance<R, D> {
    /// Maps a family-`F` index of the target relation back to the Figure 3 line
    /// of the source level it restates.
    #[must_use]
    pub fn equation(&self, index: usize) -> Option<TargetEquation> {
        if index < self.inner_rows {
            return Some(TargetEquation::InnerLink { row: index });
        }
        let i = index - self.inner_rows;
        if i < self.outer1_rows {
            return Some(TargetEquation::OuterCommitment1 { row: i });
        }
        let i = i - self.outer1_rows;
        if i < self.outer2_rows {
            return Some(TargetEquation::OuterCommitment2 { row: i });
        }
        match i - self.outer2_rows {
            0 => Some(TargetEquation::SelfInnerProduct),
            1 => Some(TargetEquation::LinearClaim),
            2 => Some(TargetEquation::Relation),
            _ => None,
        }
    }

    /// Definition 3.5's factoring condition, evaluated on the honest data: the
    /// level's verification predicate *is* membership of the last message in the
    /// target relation.
    ///
    /// # Errors
    /// [`RelationError`] naming the clause that failed;
    /// [`Self::equation`] maps a `FullConstraintNonZero` index back to its
    /// Figure 3 line.
    pub fn check_honest(&self) -> Result<(), RelationError> {
        self.relation.check(&self.witness)
    }
}

/// Builds §5.3's target instance from one level's data.
///
/// Each equation of (6) restates one Figure 3 line in the reblocked coordinates,
/// with the level's challenges and commitments as *public* coefficients:
///
/// | target equations | source line | shape |
/// |---|---|---|
/// | `A·z − Σᵢ cᵢtᵢ = 0` | 15 | linear, `κ` of them |
/// | `B·t⁽ᵏ⁾ + C·g⁽ᵏ⁾ − u₁ = 0` | 19 | linear, `κ₁` |
/// | `D·h⁽ᵏ⁾ − u₂ = 0` | 20 | linear, `κ₂` |
/// | `⟨z,z⟩ − Σ g_ij cᵢc_j = 0` | 16 | the only quadratic one |
/// | `Σᵢ⟨φᵢ,z⟩cᵢ − Σ h_ij cᵢc_j = 0` | 17 | linear |
/// | `Σ a_ij g_ij + Σᵢ h_ii − b = 0` | 18 | linear |
///
/// `z = z⁽⁰⁾ + b·z⁽¹⁾` turns the quadratic term into
/// `⟨z⁰,z⁰⟩ + 2b⟨z¹,z⁰⟩ + b²⟨z¹,z¹⟩` (p.15), so `(a′_ij)` is nonzero only among
/// the `2ν` blocks of `z`, is symmetric, and vanishes unless `i, j ≤ 2ν` — the
/// structural claims §5.3 makes about (6).
///
/// # Errors
/// [`CoreError::TargetShape`] if the shape does not cover `(n, m)`, and
/// [`CoreError::WrongShape`] if any batch is not the plane count this level's
/// own decompositions imply — which would mean the message is not a witness for
/// *this* statement.
#[allow(clippy::too_many_arguments)]
pub fn target_instance<R: Ring + CenteredRing, const D: usize>(
    relation: &Relation<R, D>,
    view: &CoreView<R, D>,
    params: &CoreParams<R, D>,
    shape: &TargetShape,
    u1: &[Elt<R, D>],
    u2: &[Elt<R, D>],
    z: &WitnessVec<R, D>,
    t_planes: &[Elt<R, D>],
    g_planes: &[Elt<R, D>],
    h_planes: &[Elt<R, D>],
) -> Result<TargetInstance<R, D>, CoreError> {
    let r = relation.multiplicity;
    let n = relation.rank;
    let kappa = params.inner_key.rows();
    let kappa1 = params.key_b.rows();
    let kappa2 = params.key_d.rows();
    let t1 = params.decomp1.digits;
    let t2 = params.decomp2.digits;
    let base = params.bounds.base;
    let triangle_len = (r * r + r) / 2;
    if !shape.fits()
        || shape.source_rank != n
        || shape.v_width != TargetShape::width_v(r, t1, t2, kappa)
    {
        return Err(CoreError::TargetShape);
    }
    let t_expect = r * kappa * t1;
    let g_expect = triangle_len * t2;
    let h_expect = triangle_len * t1;
    let bad = [
        (z.len(), n),
        (t_planes.len(), t_expect),
        (g_planes.len(), g_expect),
        (h_planes.len(), h_expect),
    ];
    if let Some((got, expected)) = bad.into_iter().find(|(g, e)| g != e) {
        return Err(CoreError::WrongShape { got, expected });
    }

    // v = t‖g‖h: the concatenation of every decomposition part (p.15), and the
    // two-plane split of `z` — §5.3's target witness, in the reblocked layout.
    let mut v: Vec<Elt<R, D>> =
        Vec::with_capacity(t_planes.len() + g_planes.len() + h_planes.len());
    v.extend_from_slice(t_planes);
    v.extend_from_slice(g_planes);
    v.extend_from_slice(h_planes);
    let (z_lo, z_hi) = split_z(base, z);
    let witness = target_witness(shape, &z_lo, &z_hi, &v);

    // One construction path for the equations, shared with the verifier, which
    // reaches it through [`target_statement`] without ever seeing `witness`.
    let statement = target_statement(relation, view, params, shape, u1, u2)?;
    Ok(TargetInstance {
        relation: statement,
        witness,
        shape: *shape,
        inner_rows: kappa,
        outer1_rows: kappa1,
        outer2_rows: kappa2,
    })
}

/// §5.3's target *statement*: the `κ+κ₁+κ₂+3` equations of (6), the empty second
/// family, and the consolidated budget (5), built from a level's head alone.
///
/// This is Definition 3.5's `Ṽ(x₁, c₁,…,c_k, z₁,…,z_{k′})` — the output is the
/// next instance of `R`, and nothing below reads `z, t, g, h` or their planes, so
/// a level's target is fully determined before its last message exists. Each
/// equation restates one Figure 3 line in the reblocked coordinates, with the
/// level's challenges and commitments as *public* coefficients:
///
/// | target equations | source line | shape |
/// |---|---|---|
/// | `A·z − Σᵢ cᵢtᵢ = 0` | 15 | linear, `κ` of them |
/// | `B·t⁽ᵏ⁾ + C·g⁽ᵏ⁾ − u₁ = 0` | 19 | linear, `κ₁` |
/// | `D·h⁽ᵏ⁾ − u₂ = 0` | 20 | linear, `κ₂` |
/// | `⟨z,z⟩ − Σ g_ij cᵢc_j = 0` | 16 | the only quadratic one |
/// | `Σᵢ⟨φᵢ,z⟩cᵢ − Σ h_ij cᵢc_j = 0` | 17 | linear |
/// | `Σ a_ij g_ij + Σᵢ h_ii − b = 0` | 18 | linear |
///
/// `z = z⁽⁰⁾ + b·z⁽¹⁾` turns the quadratic term into
/// `⟨z⁰,z⁰⟩ + 2b⟨z¹,z⁰⟩ + b²⟨z¹,z¹⟩` (p.15), so `(a′_ij)` is nonzero only among
/// the `2ν` blocks of `z`, is symmetric, and vanishes unless `i, j ≤ 2ν` — the
/// structural claims §5.3 makes about (6), pinned by the tests.
///
/// # Errors
/// [`CoreError::TargetShape`] if the shape does not cover `(n, m)`, and
/// [`CoreError::WrongShape`] if the head or the view is not this level's.
#[must_use]
pub fn target_statement<R: Ring + CenteredRing, const D: usize>(
    relation: &Relation<R, D>,
    view: &CoreView<R, D>,
    params: &CoreParams<R, D>,
    shape: &TargetShape,
    u1: &[Elt<R, D>],
    u2: &[Elt<R, D>],
) -> Result<Relation<R, D>, CoreError> {
    let r = relation.multiplicity;
    let n = relation.rank;
    let kappa = params.inner_key.rows();
    let kappa1 = params.key_b.rows();
    let kappa2 = params.key_d.rows();
    let t1 = params.decomp1.digits;
    let t2 = params.decomp2.digits;
    let base = params.bounds.base;
    let triangle_len = (r * r + r) / 2;
    if !shape.fits()
        || shape.source_rank != n
        || shape.v_width != TargetShape::width_v(r, t1, t2, kappa)
    {
        return Err(CoreError::TargetShape);
    }
    let bad = [
        (u1.len(), kappa1),
        (u2.len(), kappa2),
        (view.c.len(), r),
        (view.statement.phi.len(), r),
        (view.statement.a.len(), r),
        (params.key_b.cols(), r * kappa * t1),
        (params.key_c.cols(), triangle_len * t2),
        (params.key_d.cols(), triangle_len * t1),
    ];
    if let Some((got, expected)) = bad.into_iter().find(|(g, e)| g != e) {
        return Err(CoreError::WrongShape { got, expected });
    }
    let rank = shape.rank;
    let rp = shape.multiplicity();
    let off_v = shape.off_v();
    let off_g = off_v + r * kappa * t1;
    let off_h = off_g + triangle_len * t2;
    let one = const_elt::<R, D>(1);
    let two = const_elt::<R, D>(2);
    let b_elt = const_elt::<R, D>(i64::try_from(base).expect("base fits i64"));
    let b_sq = b_elt.clone().mul_ref(&b_elt);

    // Powers of the base, so a value is the sum of its planes.
    let mut pow1 = vec![one.clone(); t1];
    for k in 1..t1 {
        pow1[k] = pow1[k - 1].clone().mul_ref(&b_elt);
    }
    let mut pow2 = vec![one.clone(); t2];
    for k in 1..t2 {
        pow2[k] = pow2[k - 1].clone().mul_ref(&b_elt);
    }

    // Σᵢ cᵢφᵢ: the coefficient of `z` in Figure 3 line 17.
    let mut cz: WitnessVec<R, D> = vec![zero_elt::<R, D>(); n];
    for i in 0..r {
        for x in 0..n {
            cz[x] += view.statement.phi[i][x].clone().mul_ref(&view.c[i]);
        }
    }

    let k_prime = TargetShape::equation_count(kappa, kappa1, kappa2);
    let mut full: Vec<QuadFn<R, D>> = Vec::with_capacity(k_prime);

    // Line 15 → κ linear equations, A·z = Σᵢ cᵢtᵢ with z = z⁰ + b·z¹.
    for x in 0..kappa {
        let mut f = QuadFn::blank(rp, rank);
        let row = params.inner_key.row(x);
        scatter(&mut f.phi, 0, row, &one);
        scatter(&mut f.phi, shape.off_z1(), row, &b_elt);
        for i in 0..r {
            for k in 0..t1 {
                let coef = view.c[i].clone().mul_ref(&pow1[k]);
                scatter_one(&mut f.phi, off_v + (i * kappa + x) * t1 + k, &coef, &neg_elt(&one));
            }
        }
        full.push(f);
    }

    // Line 19 → κ₁ equations over the t and g planes, public constant u₁.
    for x in 0..kappa1 {
        let mut f = QuadFn::blank(rp, rank);
        scatter(&mut f.phi, off_v, params.key_b.row(x), &one);
        scatter(&mut f.phi, off_g, params.key_c.row(x), &one);
        f.b = u1[x].clone();
        full.push(f);
    }

    // Line 20 → κ₂ equations over the h planes, public constant u₂.
    for x in 0..kappa2 {
        let mut f = QuadFn::blank(rp, rank);
        scatter(&mut f.phi, off_h, params.key_d.row(x), &one);
        f.b = u2[x].clone();
        full.push(f);
    }

    // Line 16 → the single quadratic equation.
    {
        let mut f = QuadFn::blank(rp, rank);
        for p in 0..shape.nu {
            f.a[p][p] = f.a[p][p].clone() + one.clone();
            f.a[p][shape.nu + p] = f.a[p][shape.nu + p].clone() + b_elt.clone();
            f.a[shape.nu + p][p] = f.a[shape.nu + p][p].clone() + b_elt.clone();
            f.a[shape.nu + p][shape.nu + p] =
                f.a[shape.nu + p][shape.nu + p].clone() + b_sq.clone();
        }
        for i in 0..r {
            for j in i..r {
                // Only the i ≤ j triangle is transmitted, so the symmetric
                // cross terms carry their factor of two.
                let cc = view.c[i]
                    .clone()
                    .mul_ref(&view.c[j])
                    .mul_ref(if i == j { &one } else { &two });
                for k in 0..t2 {
                    let coef = cc.clone().mul_ref(&pow2[k]);
                    scatter_one(
                        &mut f.phi,
                        off_g + triangle_pos(r, i, j) * t2 + k,
                        &coef,
                        &neg_elt(&one),
                    );
                }
            }
        }
        full.push(f);
    }

    // Line 17 → linear in z and in the h planes.
    {
        let mut f = QuadFn::blank(rp, rank);
        scatter(&mut f.phi, 0, &cz, &one);
        scatter(&mut f.phi, shape.off_z1(), &cz, &b_elt);
        for i in 0..r {
            for j in i..r {
                let cc = view.c[i]
                    .clone()
                    .mul_ref(&view.c[j])
                    .mul_ref(if i == j { &one } else { &two });
                for k in 0..t1 {
                    let coef = cc.clone().mul_ref(&pow1[k]);
                    scatter_one(
                        &mut f.phi,
                        off_h + triangle_pos(r, i, j) * t1 + k,
                        &coef,
                        &neg_elt(&one),
                    );
                }
            }
        }
        full.push(f);
    }

    // Line 18 → linear in g and in the diagonal h's, public constant b.
    {
        let mut f = QuadFn::blank(rp, rank);
        for i in 0..r {
            for j in i..r {
                // Σ_{i,j} a_ij g_ij over the *full* matrix, with only the i ≤ j
                // planes transmitted and g symmetric (line 8): an off-diagonal
                // triangle entry carries both halves, `a_ij + a_ji`, while the
                // diagonal appears exactly once in the double sum and carries
                // `a_ii` alone. Writing `a_ij + a_ji` everywhere would double the
                // diagonal — invisible when `(a_ij)` is diagonal-free, and a
                // broken line 18 the moment it is not.
                let a_ij = if i == j {
                    view.statement.a[i][i].clone()
                } else {
                    view.statement.a[i][j].clone() + view.statement.a[j][i].clone()
                };
                for k in 0..t2 {
                    let coef = a_ij.clone().mul_ref(&pow2[k]);
                    scatter_one(&mut f.phi, off_g + triangle_pos(r, i, j) * t2 + k, &coef, &one);
                }
                if i == j {
                    for k in 0..t1 {
                        scatter_one(
                            &mut f.phi,
                            off_h + triangle_pos(r, i, j) * t1 + k,
                            &pow1[k],
                            &one,
                        );
                    }
                }
            }
        }
        f.b = view.statement.b.clone();
        full.push(f);
    }

    debug_assert_eq!(full.len(), k_prime, "eq. (6) counts κ+κ₁+κ₂+3");
    Ok(Relation {
        rank,
        multiplicity: rp,
        full,
        ct_only: Vec::new(),
        norm_bound_sq: params.bounds.beta_prime_sq,
    })
}

/// §5.2's remedy "the prover can request projection matrices until it is the
/// case", in Fiat–Shamir form: each request re-derives the level's CRS seed, so
/// the projection matrix — and with it every challenge — is redrawn, and the
/// verifier replays the same derivation from the index the prover records.
/// Bounded, so a prover cannot search CRSs without limit.
pub const MAX_PROJECTION_REROLLS: u32 = 8;

/// The CRS seed of the level that proves a level's target relation.
#[must_use]
pub fn level_seed(base: &[u8; 32], reroll: u32) -> [u8; 32] {
    let mut transcript = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/dotproduct-level");
    transcript.absorb(b"base", base);
    transcript.absorb(b"reroll", &reroll.to_le_bytes());
    let bytes = transcript.challenge_bytes(32);
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&bytes[..32]);
    seed
}

/// §6.1's per-level parameter step: the next level's CRS keys, decompositions and
/// budget, derived from the target relation's *own* shape `(r′, n′, β′²)`.
///
/// §5.4's rules are applied to the target, not copied from the source: `b′` is
/// re-derived from the target's per-coefficient variance `s′² = β′²/(r′n′d)`, and
/// `t₁′, t₂′` from that base. The three commitment ranks stay at the source
/// level's `κ, κ₁, κ₂` — §6.1 grows them per level to hold 128-bit security, and
/// [`recursion_msis_norm_sq`] reports the bound that growth has to cover.
///
/// # Errors
/// [`CoreError::SlackCondition`] if `β′²` violates Theorem 5.1's precondition at
/// the target's own scale, and [`CoreError::DigitCapacity`] if §5.4's base and
/// plane count cannot span `Z_q` — either way the level is *not instantiable*,
/// and that answer is the honest one.
pub fn next_level_setup<R: Ring + CenteredRing, const D: usize>(
    source: &CoreSetup<R, D>,
    target: &Relation<R, D>,
    seed: &[u8; 32],
) -> Result<CoreSetup<R, D>, CoreError> {
    let model = SizeModel::of(source);
    let r = target.multiplicity;
    let n = target.rank;
    if r == 0 || n == 0 {
        return Err(CoreError::WrongShape { got: 0, expected: 1 });
    }
    if !NormBounds::slack_condition(target.norm_bound_sq, R::MODULUS) {
        return Err(CoreError::SlackCondition);
    }
    let bounds = NormBounds::derive(
        target.norm_bound_sq,
        R::MODULUS,
        r,
        n,
        model.kappa,
        D,
        source.space.tau(),
    );
    let decomp1 = Decomposition::new(bounds.base, bounds.t1);
    let decomp2 = Decomposition::new(bounds.base, bounds.t2);
    // `t⃗′` and `h⃗′` are uniform mod `q`, so their planes must cover every
    // residue; `g⃗′`'s are gated by its magnitude inside `prove_core`.
    decomp1.validate::<R>().map_err(|_| CoreError::DigitCapacity)?;
    let triangle = (r * r + r) / 2;
    Ok(CoreSetup {
        params: CoreParams {
            inner_key: RingMatrixKey::setup(b"inner-A", seed, model.kappa, n),
            key_b: RingMatrixKey::setup(b"outer-B", seed, model.kappa1, r * bounds.t1 * model.kappa),
            key_c: RingMatrixKey::setup(b"outer-C", seed, model.kappa1, bounds.t2 * triangle),
            key_d: RingMatrixKey::setup(b"outer-D", seed, model.kappa2, bounds.t1 * triangle),
            decomp1,
            decomp2,
            bounds,
            aggregation_count: aggregation_count(R::MODULUS),
        },
        space: source.space,
    })
}

/// Definition 3.6's composition of the core argument with itself, one level deep.
///
/// The source level's last message is *absent by construction*: what is sent is
/// its head, then a proof that the head's target relation has a short witness.
/// Schematically
///
/// ```text
/// direct   : head₀ │ z₀ t₀ g₀ h₀            (+ their digit planes)
/// composed : head₀ │ head₁ │ z₁ t₁ g₁ h₁    (+ level 1's digit planes)
/// ```
///
/// and the second is smaller exactly when §5.7 says it is — see
/// [`RecursionPlan::compacts`].
#[derive(Debug, Clone)]
pub struct ComposedProof<R: Ring, const D: usize> {
    /// Level 0's `u₁, p, b″(k), u₂`: everything `Ṽ` reads.
    pub head: CoreHead<R, D>,
    /// The reblocking the target was built under. The verifier re-derives it from
    /// public data and rejects a mismatch — it is not the prover's to choose.
    pub shape: TargetShape,
    /// Which projection draw of the next level this proof is for, in
    /// `0..MAX_PROJECTION_REROLLS` (§5.2's re-roll).
    pub reroll: u32,
    /// The next level's message: *its* last message is the one that finally goes
    /// on the wire, and it is short precisely because level 0 folded.
    pub next: CoreMessage<R, D>,
    /// Figure 3 line 14's quantity for a level whose last message is not sent: the
    /// consolidated budget (5) that the next level's projection gate now stands
    /// in for. It is public — it *is* the target relation's `β′²` — and stating it
    /// in the proof is what keeps the trade visible: the composed argument proves
    /// `Σ‖z⁽⁰⁾‖² + Σ‖z⁽¹⁾‖² + Σ‖v‖² ≤ (β′)²` instead of reading it off the wire, so
    /// the witness it extracts is only within `√(128/30)` of it (Remark 5.2, and
    /// [`recursion_msis_norm_sq`]).
    pub target_norm_bound_sq: u128,
}

impl<R: Ring, const D: usize> ComposedProof<R, D> {
    /// Ring elements the composed argument sends in its last message — level 1's
    /// `z, t, g, h` planes, which is the only `z, t, g, h` on the wire.
    #[must_use]
    pub fn last_message_planes(&self) -> usize {
        self.next.last_message_planes()
    }
}

/// Why a composed argument failed, naming the level and the line.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RecursionError {
    /// `reroll` is out of range, so the next level's CRS cannot be replayed and
    /// nothing else could be evaluated. Reported alone.
    Reroll {
        /// The index the proof carried.
        got: u32,
    },
    /// A check on the source level's own head: Figure 2's `‖p‖ ≤ √128β` gate, its
    /// `b″(k)₀` claims, or a head that is not the shape this level's CRS implies.
    /// These are §5.3 p.15's two *direct* conditions on `Ṽ`.
    Head(CoreError),
    /// The carried reblocking is not the one §5.3 derives from this level's public
    /// data, so the statement the next level proved would be a different — and
    /// possibly smaller — relation. Reported alone.
    Shape {
        /// `ν` the proof claimed.
        nu: usize,
        /// `μ` the proof claimed.
        mu: usize,
        /// `n′` the proof claimed.
        rank: usize,
    },
    /// The budget (5) the proof declares is not the source level's own
    /// `(β′)² = 2γ²/b² + γ₁² + γ₂²`, so the norm statement level 1 is proving is
    /// not the one level 0 needs. Reported alone.
    Budget {
        /// The squared bound the proof declared.
        claimed: u128,
        /// The one this level's §5.4 parameters imply.
        derived: u128,
    },
    /// The next level's parameters cannot be instantiated for the derived target
    /// shape at all — §5.4's decomposition does not span `q`, or `β′` breaks
    /// Theorem 5.1's slack precondition. This is an arithmetic verdict, not a
    /// prover's failure.
    NextSetup(CoreError),
    /// The proof of the target relation failed Figure 3, at the next level. Every
    /// source-level line — 15 through 20 — reaches the verifier through one of
    /// these, which is what "proved rather than re-sent" means.
    NextLevel(CoreError),
}

impl fmt::Display for RecursionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reroll { got } => write!(
                f,
                "level 1: projection re-roll {got} is outside 0..{MAX_PROJECTION_REROLLS}"
            ),
            Self::Head(e) => write!(f, "level 0 head: {e}"),
            Self::Shape { nu, mu, rank } => write!(
                f,
                "level 0 target: reblocking (ν={nu}, μ={mu}, n′={rank}) is not the one §5.3 derives"
            ),
            Self::Budget { claimed, derived } => write!(
                f,
                "level 0 target: declared (β′)² = {claimed} is not this level's {derived}"
            ),
            Self::NextSetup(e) => write!(f, "level 1 not instantiable: {e}"),
            Self::NextLevel(e) => write!(f, "level 1 proves R′ wrong: {e}"),
        }
    }
}

/// Runs one level of the recursion: Figure 2 at level 0, then Figure 2 again at
/// level 1 on the target relation level 0's head defines.
///
/// The level-1 CRS is derived from [`level_seed`], and the projection is redrawn
/// (a fresh `reroll`, hence a fresh level-1 CRS and projection matrix) while
/// §5.2's gates reject an honest run, which is the paper's own remedy rather than
/// a widening of any bound.
///
/// # Errors
/// The level-0 [`CoreError`]s of [`prove_core`], or the level-1 failure that
/// survived every re-roll: [`CoreError::ProjectionNorm`] (the JL gate rejecting
/// each draw) or [`CoreError::NormBudget`].
pub fn prove_composed<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    s: &[WitnessVec<R, D>],
) -> Result<ComposedProof<R, D>, CoreError> {
    let message = prove_core(setup, relation, key_seed, s)?;
    prove_composed_from(setup, relation, key_seed, &message)
}

/// [`prove_composed`] for a prover that already holds the level's message — which
/// is every real prover, since the message's planes *are* the target witness.
///
/// Splitting it out is not a convenience: a caller that recomputed level 0 would
/// be sampling a second, different transcript and composing it against a target
/// relation nobody derived.
///
/// # Errors
/// As [`prove_composed`], minus level 0's own failures.
pub fn prove_composed_from<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    message: &CoreMessage<R, D>,
) -> Result<ComposedProof<R, D>, CoreError> {
    let params = &setup.params;
    let view = derive_view(setup, relation, key_seed, message)?;
    let plan = RecursionPlan::of(setup, relation);
    let instance = target_instance(
        relation,
        &view,
        params,
        &plan.shape,
        &message.u1,
        &message.u2,
        &message.z,
        &message.t_digits,
        &message.g_digits,
        &message.h_digits,
    )?;
    let mut last_err = CoreError::TargetShape;
    for reroll in 0..MAX_PROJECTION_REROLLS {
        let seed = level_seed(key_seed, reroll);
        let next_setup = match next_level_setup(setup, &instance.relation, &seed) {
            Ok(s) => s,
            Err(e) => return Err(e),
        };
        match prove_core(&next_setup, &instance.relation, &seed, &instance.witness) {
            Ok(next) => {
                return Ok(ComposedProof {
                    head: CoreHead::of(message),
                    shape: plan.shape,
                    reroll,
                    next,
                    target_norm_bound_sq: instance.relation.norm_bound_sq,
                })
            }
            // A target witness that is genuinely too long is not a re-roll
            // problem: no projection draw shortens it.
            Err(e @ CoreError::WitnessNorm { .. }) | Err(e @ CoreError::WrongShape { .. }) => {
                return Err(e)
            }
            Err(e) => last_err = e,
        }
    }
    Err(last_err)
}

/// What a composed verifier is *actually* guaranteed about the level whose last
/// message it never saw.
///
/// Level 1's projection gate is `‖p′‖₂² ≤ 128·(β′)²`, and Lemma 4.2 (p.10) turns a
/// passing `p′` into `Σᵢ‖s′ᵢ‖² ≤ (128/30)·(β′)²` with overwhelming probability —
/// that is where `√(128/30) ≈ 2.07` of slack enters, and why Remark 5.2 (p.20)
/// raises the Module-SIS norms by the same factor per level
/// ([`recursion_msis_norm_sq`]). A terminating verifier reads line 14 off the wire
/// and gets `(β′)²` exactly; a composed one gets this, in squared norm, and it is
/// not a number to argue with by widening a check.
#[must_use]
pub fn composed_norm_bound_sq(target_norm_bound_sq: u128) -> u128 {
    ceil_div(target_norm_bound_sq.saturating_mul(128), 30)
}

/// Runs the composed verification and returns **every** rejection.
///
/// §5.3 p.15 states the three-part shape of what the verifier does, and this
/// function is that sentence: accept iff `‖p‖ < √128β`, each `b″(k)₀` is the
/// public combination, and the next level's proof holds for `Ṽ`'s output. The
/// target statement is *built here*, never received, which is the only reason the
/// last message need not be sent; the whole set is reported for the same reason
/// [`verify_core_report`] exists — under Fiat–Shamir a bad head moves the target
/// relation, so a single-error verifier hides which line owned the rejection.
#[must_use]
pub fn verify_composed_report<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    proof: &ComposedProof<R, D>,
) -> Vec<RecursionError> {
    let params = &setup.params;
    if proof.reroll >= MAX_PROJECTION_REROLLS {
        return vec![RecursionError::Reroll { got: proof.reroll }];
    }
    if let Err(e) = proof.head.check_shape(params) {
        return vec![RecursionError::Head(e)];
    }
    // The reblocking is derived, so a prover cannot pick the shape that makes its
    // own target smallest.
    let plan = RecursionPlan::of(setup, relation);
    if proof.shape != plan.shape || !proof.shape.fits() {
        return vec![RecursionError::Shape {
            nu: proof.shape.nu,
            mu: proof.shape.mu,
            rank: proof.shape.rank,
        }];
    }
    let view = match derive_view_at_head(setup, relation, key_seed, &proof.head) {
        Ok(v) => v,
        Err(e) => return vec![RecursionError::Head(e)],
    };
    let mut failures: Vec<RecursionError> = Vec::new();

    // The proof's own declaration of the norm statement it took over must be the
    // one this level's §5.4 parameters imply; otherwise level 1 is proving a
    // smaller (or merely different) bound than level 0's line 14 needs.
    if proof.target_norm_bound_sq != plan.bounds.beta_prime_sq {
        failures.push(RecursionError::Budget {
            claimed: proof.target_norm_bound_sq,
            derived: plan.bounds.beta_prime_sq,
        });
    }

    // Condition 1: ‖p‖₂² ≤ 128·β², over the integers — the same gate Figure 2
    // puts before the aggregation, and the one the next level cannot prove.
    let budget_p = 128 * relation.norm_bound_sq;
    let p_sq = integer_norm_sq(&proof.head.p);
    if p_sq > budget_p {
        failures.push(RecursionError::Head(CoreError::ProjectionNorm {
            norm_sq: p_sq,
            budget: budget_p,
        }));
    }
    // Condition 2: every b″(k)₀ equals the public combination of `p` and the `F′`
    // right-hand sides.
    for (k, claim) in view.claims.iter().enumerate() {
        if constant_term(&proof.head.b_double[k]) != *claim {
            failures.push(RecursionError::Head(CoreError::AggregationConstantTerm {
                index: k,
            }));
        }
    }
    // Condition 3: the next level's proof, against the statement derived here.
    let target = match target_statement(relation, &view, params, &plan.shape, &proof.head.u1, &proof.head.u2) {
        Ok(t) => t,
        Err(e) => {
            failures.push(RecursionError::Head(e));
            return failures;
        }
    };
    let seed = level_seed(key_seed, proof.reroll);
    let next_setup = match next_level_setup(setup, &target, &seed) {
        Ok(s) => s,
        Err(e) => {
            failures.push(RecursionError::NextSetup(e));
            return failures;
        }
    };
    failures.extend(
        verify_core_report(&next_setup, &target, &seed, &proof.next)
            .into_iter()
            .map(RecursionError::NextLevel),
    );
    failures
}

/// [`verify_composed_report`] reduced to what a verifier acts on.
///
/// # Errors
/// The first rejection of the composed report.
pub fn verify_composed<R: Ring + CenteredRing, const D: usize>(
    setup: &CoreSetup<R, D>,
    relation: &Relation<R, D>,
    key_seed: &[u8; 32],
    proof: &ComposedProof<R, D>,
) -> Result<(), RecursionError> {
    match verify_composed_report(setup, relation, key_seed, proof).into_iter().next() {
        Some(e) => Err(e),
        None => Ok(()),
    }
}

/// A satisfiable instance of §5.1's `R` at a requested shape `(r, n, β²)`.
///
/// The witness has `0/1` coefficients — the shape §6's lifted binary R1CS
/// produces, so `Σᵢ‖sᵢ‖₂² ≤ r·n·d` — and every right-hand side is *computed*
/// from it, so the statement holds by construction. This is the honest way to
/// reach a rank where §5.7 says a recursion level pays without paying the
/// `O(ℓ·k²)` cost of the Figure 4 reduction to get there: the recursion's
/// economics are a function of `(r, n, β², κ, κ₁, κ₂, q, d, τ)` alone, and none
/// of those is the number of constraints.
///
/// `norm_bound_sq` is the caller's claim, not this function's: pass one the
/// witness actually satisfies, or [`Relation::check`] says so.
#[must_use]
pub fn sample_instance<R: Ring + CenteredRing, const D: usize>(
    seed: &[u8; 32],
    multiplicity: usize,
    rank: usize,
    full: usize,
    ct_only: usize,
    norm_bound_sq: u128,
) -> (Relation<R, D>, Vec<WitnessVec<R, D>>) {
    assert!(multiplicity > 0 && rank > 0, "R needs r, n ≥ 1");
    let mut xof = Shake256Xof::new(b"lattice-algebra/Z7/dotproduct-instance");
    xof.absorb(seed);
    xof.absorb(&(multiplicity as u64).to_le_bytes());
    xof.absorb(&(rank as u64).to_le_bytes());
    let mut stream = BitStream::new(&mut xof);
    let s: Vec<WitnessVec<R, D>> = (0..multiplicity)
        .map(|_| {
            (0..rank)
                .map(|_| {
                    let coeffs: Vec<R> = (0..D)
                        .map(|_| {
                            let mut byte = [0u8; 1];
                            stream.read_bytes(&mut byte);
                            R::from(u64::from(byte[0] & 1))
                        })
                        .collect();
                    PolyRing::from_coefficients(coeffs)
                })
                .collect()
        })
        .collect();
    // Domain-separated draws: one seed per (label, slot), so a coefficient of
    // function `k` can never be the same element as function `k′`'s by accident.
    let slot_seed = |label: &[u8], slot: usize| -> [u8; 32] {
        let mut inner = Shake256Xof::new(label);
        inner.absorb(seed);
        inner.absorb(&(slot as u64).to_le_bytes());
        let mut bytes = [0u8; 32];
        BitStream::new(&mut inner).read_bytes(&mut bytes);
        bytes
    };
    let scalar = |label: &[u8], slot: usize| -> Elt<R, D> {
        uniform_vec_from_seed::<R, D>(label, &slot_seed(label, slot), 1)
            .into_iter()
            .next()
            .expect("one element asked for")
    };
    let mut full_fns = Vec::with_capacity(full);
    for k in 0..full {
        let mut f = QuadFn::<R, D>::blank(multiplicity, rank);
        for i in 0..multiplicity {
            for j in i..multiplicity {
                let a_ij = scalar(b"a", k * multiplicity * multiplicity + i * multiplicity + j);
                // §5.1 takes `(a_ij)` symmetric without loss of generality, and
                // `QuadFn::lhs` sums over all pairs, so both halves carry it.
                f.a[j][i] = a_ij.clone();
                f.a[i][j] = a_ij;
            }
            f.phi[i] = uniform_vec_from_seed::<R, D>(b"phi", &slot_seed(b"phi", k * multiplicity + i), rank);
        }
        f.b = f.lhs(&s);
        full_fns.push(f);
    }
    let mut ct_fns = Vec::with_capacity(ct_only);
    for l in 0..ct_only {
        let mut f = CtFn::<R, D>::blank(multiplicity, rank);
        let base = full * multiplicity * multiplicity + multiplicity + l * multiplicity;
        for i in 0..multiplicity {
            for j in i..multiplicity {
                let a_ij = scalar(b"a", base + i * multiplicity + j);
                f.a[j][i] = a_ij.clone();
                f.a[i][j] = a_ij;
            }
            f.phi[i] = uniform_vec_from_seed::<R, D>(b"phi", &slot_seed(b"phi", base + i), rank);
        }
        let lhs = QuadFn {
            a: f.a.clone(),
            phi: f.phi.clone(),
            b: zero_elt::<R, D>(),
        }
        .lhs(&s);
        f.b0 = constant_term(&lhs);
        ct_fns.push(f);
    }
    (
        Relation {
            rank,
            multiplicity,
            full: full_fns,
            ct_only: ct_fns,
            norm_bound_sq,
        },
        s,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::gadget;
    use algebra::ring::zq::Zq;

    /// LaBRADOR's own regime: `q = 2³² − 99`, prime, `≡ 5 (mod 8)`, so
    /// `ord_128(q) = 32` and `X⁶⁴ + 1` splits into two degree-32 factors — the
    /// §2 hypothesis, and a ring with **no NTT of degree ≥ 4**.
    type QL = Zq<4_294_967_197>;
    /// A small odd modulus in the same two-factor regime (`≡ 3 mod 8`), used
    /// where a test only needs arithmetic, not the wire ceiling.
    type QS = Zq<1_000_000_007>;
    const D: usize = 64;

    fn elt(centered: &[i64]) -> Elt<QL, D> {
        let mut coeffs: Vec<QL> = (0..D).map(|_| QL::ZERO).collect();
        for (i, &v) in centered.iter().enumerate() {
            coeffs[i] = from_centered::<QL>(v);
        }
        Elt::<QL, D>::from_coefficients(coeffs)
    }

    fn vec_of(values: &[&[i64]]) -> WitnessVec<QL, D> {
        values.iter().map(|v| elt(v)).collect()
    }

    /// A one-ring-element witness vector with a single coefficient set.
    fn mono(v: i64) -> WitnessVec<QL, D> {
        vec_of(&[core::slice::from_ref(&v)])
    }

    #[test]
    fn the_ring_is_the_two_factor_non_ntt_one_the_paper_assumes() {
        use algebra::ring::number_theory::x_pow_d_plus_1_splitting;
        assert!(QL::IS_PRIME);
        let split = x_pow_d_plus_1_splitting(QL::MODULUS, D as u64).expect("odd prime, d = 2^e");
        assert!(
            split.is_two_half_degrees(D as u64),
            "§2 needs X⁶⁴+1 as two degree-32 factors, got {split:?}"
        );
        assert!(
            !split.is_split_completely(),
            "hence no NTT-backed key exists"
        );
    }

    #[test]
    fn relation_check_names_each_clause_separately() {
        let s = vec![mono(3), mono(5)];
        // f(s) = 2·⟨s₁,s₂⟩ − 30: honest for (3, 5). The `(a_ij)` of §5.1 is
        // symmetric w.l.o.g., so both off-diagonal entries carry the 1 and the
        // pair is counted twice — a `b` of 15 would make the "honest" witness
        // false.
        let mut f = QuadFn::<QL, D>::blank(2, 1);
        f.a[0][1] = elt(&[1]);
        f.a[1][0] = elt(&[1]);
        f.b = elt(&[30]);
        // f'(s) = ⟨s₁, s₁⟩ − 9: only its constant term must vanish.
        let mut g = CtFn::<QL, D>::blank(2, 1);
        g.a[0][0] = elt(&[1]);
        g.b0 = from_centered::<QL>(9);
        let rel = Relation {
            rank: 1,
            multiplicity: 2,
            full: vec![f.clone()],
            ct_only: vec![g.clone()],
            norm_bound_sq: 64,
        };
        assert!(rel.check(&s).is_ok(), "honest witness must satisfy R");
        // Wrong number of vectors, wrong rank, a false F, a false F′ and an
        // over-long witness each fail with its own variant.
        assert_eq!(
            rel.check(&[mono(3)]),
            Err(RelationError::WrongShape {
                got: 1,
                expected: 2
            })
        );
        assert_eq!(
            rel.check(&[vec_of(&[&[3i64], &[0i64]]), mono(5)]),
            Err(RelationError::WrongShape {
                got: 2,
                expected: 1
            })
        );
        let bad_f = Relation {
            full: vec![QuadFn {
                a: f.a.clone(),
                phi: f.phi.clone(),
                b: elt(&[31]),
            }],
            ..rel.clone()
        };
        assert_eq!(
            bad_f.check(&s),
            Err(RelationError::FullConstraintNonZero { index: 0 })
        );
        let bad_g = Relation {
            ct_only: vec![CtFn {
                b0: QL::ONE,
                ..g.clone()
            }],
            ..rel.clone()
        };
        assert_eq!(
            bad_g.check(&s),
            Err(RelationError::ConstantTermNonZero { index: 0 })
        );
        // The norm budget is the third failure mode, and it needs a witness
        // that *satisfies* both equations — otherwise a constraint failure
        // fires first and the gate goes untested. (3, 5) satisfies them at
        // ‖s‖₂² = 34, so a claim of 30 isolates the norm.
        let tight = Relation {
            norm_bound_sq: 30,
            ..rel.clone()
        };
        assert_eq!(
            tight.check(&s),
            Err(RelationError::NormExceeded {
                norm_sq: 34,
                bound_sq: 30
            })
        );
    }

    #[test]
    fn figure3_line16_holds_by_the_symmetric_garbage_identity() {
        // ⟨z,z⟩ = Σ_{i,j} g_ij cᵢcⱼ for g_ij = ⟨sᵢ,sⱼ⟩ and z = Σ cᵢsᵢ. Written
        // out twice, once through garbage_g and once term by term, so a wrong
        // index convention cannot cancel out.
        let s = vec![mono(2), mono(3), mono(5)];
        let c: Vec<Elt<QL, D>> = (0..3).map(|i| elt(&[(i as i64) - 1])).collect();
        let g = garbage_g(&s);
        let mut z: WitnessVec<QL, D> = vec![elt(&[0])];
        for i in 0..3 {
            z[0] = z[0].clone() + s[i][0].clone() * c[i].clone();
        }
        let mut acc = elt(&[0]);
        for i in 0..3 {
            for j in 0..3 {
                acc = acc + g[i * 3 + j].clone() * c[i].clone() * c[j].clone();
            }
        }
        assert_eq!(inner_product(&z, &z), acc, "Figure 3 line 16");
        // The scalar version of the same claim, through the σ-pairing.
        let mut expect = 0i64;
        for i in 0..3 {
            for j in 0..3 {
                expect += [2i64, 3, 5][i]
                    * [2i64, 3, 5][j]
                    * [c[i].clone(), c[j].clone()]
                        .iter()
                        .map(|e| e.coefficients()[0].centered())
                        .product::<i64>();
            }
        }
        assert_eq!(
            constant_term(&acc).centered(),
            from_centered::<QL>(expect).centered(),
            "the ring claim must agree with the integer one"
        );
    }

    #[test]
    fn figure3_line17_needs_the_symmetrized_half() {
        // Σᵢ⟨φᵢ,z⟩cᵢ = Σ h_ij cᵢcⱼ with h_ij = ½(⟨φᵢ,sⱼ⟩+⟨φⱼ,sᵢ⟩). Dropping the
        // ½ (or the symmetrization) breaks this for asymmetric φ.
        let s = vec![mono(2), mono(7)];
        let phi = vec![vec_of(&[&[3i64]]), vec_of(&[&[11i64]])];
        let c = vec![elt(&[4]), elt(&[-2])];
        let h = garbage_h(&s, &phi);
        let mut z: WitnessVec<QL, D> = vec![elt(&[0])];
        for i in 0..2 {
            z[0] = z[0].clone() + s[i][0].clone() * c[i].clone();
        }
        let mut lhs = elt(&[0]);
        for i in 0..2 {
            lhs = lhs + inner_product(&phi[i], &z).mul_ref(&c[i]);
        }
        let mut rhs = elt(&[0]);
        for i in 0..2 {
            for j in 0..2 {
                rhs = rhs + h[i * 2 + j].clone() * c[i].clone() * c[j].clone();
            }
        }
        assert_eq!(lhs, rhs, "Figure 3 line 17");
        // and the diagonal really is ⟨φᵢ,sᵢ⟩, which line 18 relies on.
        for i in 0..2 {
            assert_eq!(h[i * 2 + i], inner_product(&phi[i], &s[i]));
        }
        assert_eq!(h[0 * 2 + 1], h[1 * 2 + 0], "h must be symmetric");
    }

    #[test]
    fn figure3_line18_reproduces_the_aggregated_relation() {
        // Σ a_ij g_ij + Σ hᵢᵢ − b = 0 ⟺ f(s₁..s_r) = 0.
        let s = vec![mono(2), mono(7)];
        let phi = vec![vec_of(&[&[3i64]]), vec_of(&[&[11i64]])];
        let mut f = QuadFn::<QL, D>::blank(2, 1);
        f.a[0][1] = elt(&[5]);
        f.a[1][0] = elt(&[5]);
        f.phi = phi.clone();
        let g = garbage_g(&s);
        let h = garbage_h(&s, &phi);
        let mut acc = elt(&[0]);
        for i in 0..2 {
            for j in 0..2 {
                acc = acc + f.a[i][j].clone().mul_ref(&g[i * 2 + j]);
            }
        }
        for i in 0..2 {
            acc = acc + h[i * 2 + i].clone();
        }
        // Line 18's claim is `Σ a_ij g_ij + Σ hᵢᵢ = b`; with a[0][1] = a[1][0]
        // = 5, s = (2, 7) and φ = (3, 11) that value is 5·14 + 5·14 + 6 + 77.
        f.b = elt(&[223]);
        assert_eq!(acc, f.lhs(&s), "Figure 3 line 18 must equal f's own value");
        assert_eq!(acc, f.b, "and the garbage form must reach the same claim");
        assert_eq!(
            f.value(&[mono(2), mono(7)]),
            zero_elt::<QL, D>(),
            "hence f vanishes on the honest witness"
        );
    }

    #[test]
    fn digit_split_matches_the_const_generic_gadget() {
        // The runtime-base decomposition must be the same function as
        // `pcs::gadget::split` at equal (base, digits), otherwise this module
        // is a second, drifting implementation of the gadget.
        const BASE: u64 = 16;
        const DIGITS: usize = 8; // 16⁸ ≫ q
        let values: Vec<Elt<QL, D>> = (0..4)
            .map(|i| {
                let coeffs: Vec<QL> = (0..D)
                    .map(|j| from_centered::<QL>(((i * 31 + j * 7) % 5001) as i64 - 2500))
                    .collect();
                Elt::<QL, D>::from_coefficients(coeffs)
            })
            .collect();
        let runtime = Decomposition::new(BASE, DIGITS).split(&values);
        let generic = gadget::split::<QL, D, BASE, DIGITS>(&values);
        assert_eq!(runtime, generic, "same digits, two call sites");
        assert!(Decomposition::new(BASE, DIGITS)
            .check(&values, &runtime)
            .is_ok());
    }

    #[test]
    fn digit_check_rejects_capacity_width_and_recombination_apart() {
        let values = vec![elt(&[12345]), elt(&[-99])];
        let decomp = Decomposition::new(16, 8);
        let mut planes = decomp.split(&values);
        assert!(decomp.check(&values, &planes).is_ok());
        // (a) too wide but still recombining: push `base` into plane 0 and take
        // one unit out of plane 1, which leaves Σ 16^k·plane_k untouched. Only
        // the width check can catch this — the recombination check cannot.
        // Plane 0 of 12345 holds the centered digit −7 (12345 = −7 + 16·772),
        // so the tamper puts it at +9: over the half-width, still |9| < 16.
        let shifted = {
            let mut out = planes.clone();
            out[0] = &out[0] + &const_elt::<QL, D>(16);
            out[1] = &out[1] - &elt(&[1]);
            out
        };
        assert_eq!(
            decomp.check(&values, &shifted),
            Err(DigitError::PlaneTooWide {
                plane: 0,
                magnitude: 9,
                half_width: 8
            }),
            "an equal-value but wider digit must trip the bound, not the sum"
        );
        // (b) a plane batch that no longer reconstructs the value.
        planes[8] = &planes[8] + &elt(&[1]);
        assert_eq!(
            decomp.check(&values, &planes),
            Err(DigitError::Recombination)
        );
        // (c) a capacity that cannot hold the modulus must be refused up front.
        assert_eq!(
            Decomposition::new(2, 3).validate::<QL>(),
            Err(DigitError::CapacityTooSmall {
                capacity: 8,
                modulus: QL::MODULUS
            })
        );
        assert_eq!(
            Decomposition::new(16, 8).check(&values[..1], &values[..1]),
            Err(DigitError::WrongPlaneCount {
                got: 1,
                expected: 8
            })
        );
    }

    #[test]
    fn short_split_reconstructs_and_stays_in_the_half_width() {
        // Figure 3 line 10: z = z⁽⁰⁾ + b·z⁽¹⁾ over the *integers*, with
        // ‖z⁽⁰⁾‖∞ ≤ b/2. Exercised on the boundary values, where an off-by-one
        // in the centered remainder shows up.
        let base = 372u64;
        for v in [
            0i64, 1, -1, 185, 186, 187, -185, -186, -187, 5000, -5000, 999_999, -999_999,
        ] {
            let z = mono(v);
            let (lo, hi) = split_short(base, &z[0]);
            let planes = vec![lo.clone(), hi.clone()];
            check_short_split::<QL, D>(base, &z, &planes)
                .unwrap_or_else(|e| panic!("{v}: split rejected by {e}"));
            // Exactly one of the two centered digits is on the boundary side.
            let lo_int = lo.coefficients()[0].centered();
            let hi_int = hi.coefficients()[0].centered();
            assert!(lo_int.abs() <= (base / 2) as i64, "{v}: {lo_int} too wide");
            assert_eq!(lo_int + hi_int * base as i64, v, "{v} must reconstruct");
        }
        // A claimed split of a *different* value is rejected: the honest
        // two-plane split always reconstructs its own value, so only a
        // mismatch trips this check (an over-long-but-consistent z is line 14's
        // norm budget to catch, not line 10's).
        let (lo, hi) = split_short(base, &mono(999_999)[0]);
        let other = mono(1_000_000);
        assert_eq!(
            check_short_split::<QL, D>(base, &other, &[lo, hi]),
            Err(CoreError::DigitRecombination)
        );
    }

    #[test]
    fn norm_bounds_follow_the_section_54_formulas() {
        let beta_sq = u128::from(QL::MODULUS);
        let (r, n, kappa, d, tau) = (8usize, 3usize, 4usize, 64usize, 71u64);
        let b = NormBounds::derive(beta_sq, QL::MODULUS, r, n, kappa, d, tau);
        // b = (12·s²·r·τ)^{1/4} with s² = β²/(r·n·d) = 2 796 202.
        assert_eq!(beta_sq / u128::from((r * n * d) as u64), 2_796_202);
        assert_eq!(b.base, 372, "the fourth root rule of §5.4");
        assert_eq!(b.t1, 4, "t₁ = ⌈log q / log b⌉");
        assert_eq!(b.t2, 4, "t₂ from the Gaussian g magnitude");
        assert_eq!(b.gamma_sq, beta_sq * 71, "γ = β√τ");
        // γ₁² = b²t₁/12·rκd + b²t₂/12·(r²+r)/2·d, recomputed by hand.
        let b2 = u128::from(b.base) * u128::from(b.base);
        let hand1 = b2 * 4 * 2048 / 12 + b2 * 4 * 2304 / 12;
        let hand2 = b2 * 4 * 2304 / 12;
        assert_eq!(b.gamma1_sq, hand1);
        assert_eq!(b.gamma2_sq, hand2);
        assert_eq!(b.beta_prime_sq, 2 * b.gamma_sq / b2 + hand1 + hand2);
        assert!(b.base.pow(b.t1 as u32) as u128 > u128::from(QL::MODULUS));
    }

    #[test]
    fn slack_condition_is_theorem_51s_window() {
        let q = u128::from(QL::MODULUS);
        // β = √q, Figure 4's bound: comfortably inside β ≤ √(30/128)·q/125.
        assert!(NormBounds::slack_condition(q, QL::MODULUS));
        // At the boundary itself the honest projection can no longer be read
        // back as an integer, so the predicate must flip.
        let edge = 30 * q * q / (128 * 125 * 125);
        assert!(NormBounds::slack_condition(edge, QL::MODULUS));
        assert!(!NormBounds::slack_condition(edge + 1, QL::MODULUS));
        // β = q is far outside the window (the bound is ≈ q/145, so β² is ≈
        // q²/21000) — a *small* β never breaks it, which is why the test below
        // refuses a long witness through `WitnessNorm`, not through this gate.
        assert!(!NormBounds::slack_condition(q * q, QL::MODULUS));
    }

    #[test]
    fn msis_bounds_match_the_theorem_51_expressions() {
        let beta_sq = u128::from(QL::MODULUS);
        let b = NormBounds::derive(beta_sq, QL::MODULUS, 8, 3, 4, 64, 71);
        let [outer, inner] = b.msis_norm_sq(beta_sq, 15);
        assert_eq!(outer, 4 * b.beta_prime_sq, "the outer rank needs norm 2β′");
        // The inner bound is the max of the theorem's two terms.
        let bp = b.beta_prime_sq;
        let (t, bb) = (
            u128::from(15u64) * 15,
            u128::try_from(b.base).expect("a digit base is positive") + 1,
        );
        assert!(
            inner >= 64 * t * bb * bb * bp,
            "8T(b+1)β′ term must fit inside"
        );
        assert!(inner >= 8 * bb * bb * bp, "2(b+1)β′ term must fit inside");
    }

    #[test]
    fn challenge_space_matches_the_paper_shape_and_bounds() {
        assert_eq!(ChallengeSpace::PAPER.degree(), 64);
        assert_eq!(ChallengeSpace::PAPER.tau(), 71, "31·1 + 10·4");
        // The filter value is the crate's deviation from §2, and it must stay
        // visible: the paper bounds the *true* ‖c‖_op by 15, this space bounds
        // the certified ⌈√‖g‖₁⌉ by 24. See ChallengeSpace::PAPER's doc.
        assert_eq!(ChallengeSpace::PAPER.operator_norm, 24);
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(b"challenges");
        let mut stream = BitStream::new(&mut xof);
        for _ in 0..40 {
            let c: Elt<QL, D> = ChallengeSpace::PAPER
                .sample(&mut stream)
                .expect("filter accepts");
            let coeffs: Vec<i64> = centered_coeffs::<QL, D>(&c).to_vec();
            let (mut zeros, mut ones, mut twos) = (0usize, 0usize, 0usize);
            for &x in &coeffs {
                match x.abs() {
                    0 => zeros += 1,
                    1 => ones += 1,
                    2 => twos += 1,
                    other => panic!("coefficient of magnitude {other} outside the space"),
                }
            }
            assert_eq!((zeros, ones, twos), (23, 31, 10), "§2's exact shape");
            let square: i64 = coeffs.iter().map(|x| x * x).sum();
            assert_eq!(square, 71, "‖c‖₂² must be exactly tau");
            assert!(operator_norm_bound(&c) <= 24, "the operator-norm filter");
        }
        // A filter nobody can pass must be a typed rejection, not a hang.
        let tight = ChallengeSpace {
            operator_norm: 0,
            ..ChallengeSpace::PAPER
        };
        assert_eq!(
            tight.sample::<QL, D>(&mut stream),
            Err(ChallengeError::FilterTooTight { bound: 0 })
        );
        assert_eq!(
            ChallengeSpace {
                zeros: 22,
                ..ChallengeSpace::PAPER
            }
            .sample::<QL, D>(&mut stream),
            Err(ChallengeError::WrongDegree {
                got: 63,
                expected: 64
            })
        );
        // The filter must actually filter: bound 1 rejects every draw of §2's
        // shape, which is what makes 15 unusable as a certified threshold.
        assert_eq!(
            ChallengeSpace {
                operator_norm: 15,
                ..ChallengeSpace::PAPER
            }
            .sample::<QL, D>(&mut stream),
            Err(ChallengeError::FilterTooTight { bound: 15 }),
            "a 15-threshold on the certified bound accepts nothing"
        );
    }

    #[test]
    fn operator_norm_bound_dominates_real_products() {
        // The bound is only useful if ‖c·r‖₂ ≤ bound·‖r‖₂ really holds, so it is
        // checked against explicit products rather than against itself.
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(b"opnorm");
        let mut stream = BitStream::new(&mut xof);
        let c: Elt<QL, D> = ChallengeSpace::PAPER.sample(&mut stream).unwrap();
        let bound = operator_norm_bound(&c);
        for trial in 0..12u64 {
            let r: Elt<QL, D> = Elt::<QL, D>::from_coefficients(
                (0..D)
                    .map(|j| from_centered::<QL>(((trial * 37 + (j as u64) * 11) % 41) as i64 - 20))
                    .collect(),
            );
            let cr = r.clone() * c.clone();
            let square = |x: &Elt<QL, D>| -> u128 {
                x.coefficients()
                    .iter()
                    .map(|c| {
                        let a = u128::from(c.centered().unsigned_abs());
                        a * a
                    })
                    .sum()
            };
            let (sr, sc) = (square(&r), square(&cr));
            assert_ne!(sr, 0, "the test vector must not be zero");
            assert!(
                sc <= u128::from(bound) * u128::from(bound) * sr,
                "trial {trial}: ‖c·r‖² = {sc} above {}·‖r‖² = {}",
                bound * bound,
                u128::from(bound) * u128::from(bound) * sr
            );
        }
        // Multiplication by a monomial is an isometry, so the bound must also
        // sit at or above every ‖c‖₂ — a bound below it would be unsound.
        assert!(u128::from(bound) * u128::from(bound) >= square_norm_of(&c));
    }

    fn square_norm_of<R: Ring + CenteredRing, const D: usize>(x: &Elt<R, D>) -> u128 {
        x.coefficients()
            .iter()
            .map(|c| {
                let a = u128::from(c.centered().unsigned_abs());
                a * a
            })
            .sum()
    }

    #[test]
    fn projection_rows_satisfy_the_f_prime_identity() {
        // §5.2: p_j = Σᵢ⟨πᵢ⁽ʲ⁾, sᵢ⟩ must equal ct(Σᵢ⟨σ⁻¹(πᵢ⁽ʲ⁾), sᵢ⟩), i.e. the
        // projection really does become a family-F′ constraint. Checked on the
        // ring side and the integer side independently.
        let s: Vec<WitnessVec<QL, D>> = vec![
            vec_of(&[&[1i64, 2], &[0i64, -1], &[3i64]]),
            vec_of(&[&[-4i64], &[2i64, 0, 0, 5], &[1i64]]),
        ];
        let proj = Projection::<QL, D>::from_seed(&[9u8; 32], 6, 2, 3);
        let p = proj.project(&s);
        for j in 0..6 {
            let mut ring_side = QL::ZERO;
            for i in 0..2 {
                ring_side += constant_term(&inner_product(&proj.sigma_rows[j][i], &s[i]));
            }
            assert_eq!(
                ring_side,
                from_centered::<QL>(p[j]),
                "row {j}: the ct form must reproduce the integer projection"
            );
        }
        // Tuned distribution: about half the entries are zero, ±1 balanced.
        let (mut zeros, mut plus, mut minus) = (0u32, 0u32, 0u32);
        for row in &proj.rows {
            for &e in row {
                match e {
                    0 => zeros += 1,
                    1 => plus += 1,
                    -1 => minus += 1,
                    other => panic!("entry {other} outside {{0,±1}}"),
                }
            }
        }
        let total = zeros + plus + minus;
        assert!(
            (zeros * 100 / total).abs_diff(50) < 5,
            "P(0) should sit near 1/2, got {zeros}/{total}"
        );
    }

    #[test]
    fn aggregation_claims_track_the_witness() {
        // The verifier's `b''(k)` claim must equal the prover's own constant
        // term exactly when the F′ claims hold, and not when they do not.
        let s = vec![mono(2), mono(7)];
        // Two F′ claims, so ψ⁽ᵏ⁾ really is a 2-vector and the aggregation sums
        // two different weights rather than multiplying by one.
        let mut f = CtFn::<QL, D>::blank(2, 1);
        f.a[0][1] = elt(&[1]);
        f.b0 = from_centered::<QL>(14); // ⟨s₁,s₂⟩ = 14
        let mut f2 = CtFn::<QL, D>::blank(2, 1);
        f2.a[1][0] = elt(&[3]);
        f2.b0 = from_centered::<QL>(42); // 3·⟨s₂,s₁⟩ = 42
        let rel = Relation {
            rank: 1,
            multiplicity: 2,
            full: Vec::new(),
            ct_only: vec![f, f2],
            norm_bound_sq: 1000,
        };
        let proj = Projection::<QL, D>::from_seed(&[1u8; 32], 4, 2, 1);
        let psi = vec![vec![from_centered::<QL>(3), from_centered::<QL>(5)]];
        let omega = vec![proj.rows.iter().map(|_| from_centered::<QL>(2)).collect()];
        let coeffs = aggregate_first(&rel, &proj, &psi, &omega).expect("shapes agree");
        let b_double = prover_b_double(&coeffs, &s);
        let p = proj.project(&s);
        let p_mod: Vec<QL> = p.iter().map(|v| from_centered::<QL>(*v)).collect();
        let claim = first_aggregation_claim(&rel, &psi, &omega, &p_mod);
        assert_eq!(
            constant_term(&b_double[0]),
            claim[0],
            "an honest witness must satisfy Figure 2's constant-term check"
        );
        // A statement the witness does not satisfy breaks the same check.
        let broken = Relation {
            ct_only: vec![
                CtFn {
                    b0: from_centered::<QL>(15),
                    ..rel.ct_only[0].clone()
                },
                rel.ct_only[1].clone(),
            ],
            ..rel.clone()
        };
        let coeffs = aggregate_first(&broken, &proj, &psi, &omega).expect("shapes agree");
        let b_double = prover_b_double(&coeffs, &s);
        let claim = first_aggregation_claim(&broken, &psi, &omega, &p_mod);
        assert_ne!(constant_term(&b_double[0]), claim[0]);
    }

    #[test]
    fn aggregation_count_is_the_papers_ceiling_over_log_q() {
        assert_eq!(aggregation_count(QL::MODULUS), 4, "⌈128/32⌉");
        assert_eq!(aggregation_count(17), 26, "⌈128/5⌉ for a 5-bit modulus");
        // ⌈log₂ 2⁶³⌉ = 63, and 128/63 rounds up to 3, not 2.
        assert_eq!(aggregation_count(1 << 63), 3);
    }

    /// A tiny but complete core-argument instance: `r = 2` vectors of rank 1,
    /// one linear `F` claim, one `F′` claim, and the Figure 3 checks wired to
    /// the three outer keys.
    fn mini_setup(beta_sq: u128) -> (CoreSetup<QL, D>, Relation<QL, D>, Vec<WitnessVec<QL, D>>) {
        let (r, n, kappa) = (2usize, 1usize, 4usize);
        let s = vec![mono(2), mono(7)];
        let inner_key = RingMatrixKey::<QL, D>::setup(b"inner", &[1u8; 32], kappa, n);
        let bounds = NormBounds::derive(beta_sq, QL::MODULUS, r, n, kappa, D, 71);
        let decomp1 = Decomposition::new(bounds.base, bounds.t1);
        let decomp2 = Decomposition::new(bounds.base, bounds.t2);
        // `t⃗`/`h⃗` are uniform, so `t₁` planes must span every residue; `g⃗`'s
        // planes are gated by its magnitude inside `prove_core` instead.
        assert!(decomp1.validate::<QL>().is_ok());
        assert!(decomp2.base >= 2 && decomp2.digits >= 2);
        let triangle = (r * r + r) / 2;
        let params = CoreParams {
            inner_key: inner_key.clone(),
            bounds,
            decomp1,
            decomp2,
            key_b: RingMatrixKey::setup(b"b", &[2u8; 32], kappa, r * bounds.t1 * kappa),
            key_c: RingMatrixKey::setup(b"c", &[3u8; 32], kappa, bounds.t2 * triangle),
            key_d: RingMatrixKey::setup(b"d", &[4u8; 32], kappa, bounds.t1 * triangle),
            aggregation_count: aggregation_count(QL::MODULUS),
        };
        let mut f = QuadFn::<QL, D>::blank(r, n);
        f.phi[0][0] = elt(&[1]);
        f.b = inner_product(&f.phi[0], &s[0]);
        let mut g = CtFn::<QL, D>::blank(r, n);
        g.a[0][1] = elt(&[1]);
        g.b0 = from_centered::<QL>(14);
        let relation = Relation {
            rank: n,
            multiplicity: r,
            full: vec![f],
            ct_only: vec![g],
            norm_bound_sq: beta_sq,
        };
        (
            CoreSetup {
                params,
                space: ChallengeSpace::PAPER,
            },
            relation,
            s,
        )
    }

    /// A `mini_setup` whose inner commitment rank the caller picks.
    ///
    /// `κ` is the one parameter that sets the width of a level's `v = t‖g‖h`
    /// (through `r·t₁·κ`), so it decides how big the *next* level's relation is.
    /// The composition test uses `κ = 1` to keep a second execution cheap enough
    /// to run in a unit test; nothing about the argument's shape changes.
    fn mini_setup_k(beta_sq: u128, kappa: usize) -> (CoreSetup<QL, D>, Relation<QL, D>, Vec<WitnessVec<QL, D>>) {
        assert_ne!(kappa, 0, "A has at least one row");
        let (r, n) = (2usize, 1usize);
        let s = vec![mono(2), mono(7)];
        let inner_key = RingMatrixKey::<QL, D>::setup(b"inner", &[1u8; 32], kappa, n);
        let bounds = NormBounds::derive(beta_sq, QL::MODULUS, r, n, kappa, D, 71);
        let decomp1 = Decomposition::new(bounds.base, bounds.t1);
        let decomp2 = Decomposition::new(bounds.base, bounds.t2);
        // `t⃗`/`h⃗` are uniform, so `t₁` planes must span every residue; `g⃗`'s
        // planes are gated by its magnitude inside `prove_core` instead.
        assert!(decomp1.validate::<QL>().is_ok());
        assert!(decomp2.base >= 2 && decomp2.digits >= 2);
        let triangle = (r * r + r) / 2;
        let params = CoreParams {
            inner_key: inner_key.clone(),
            bounds,
            decomp1,
            decomp2,
            key_b: RingMatrixKey::setup(b"b", &[2u8; 32], kappa, r * bounds.t1 * kappa),
            key_c: RingMatrixKey::setup(b"c", &[3u8; 32], kappa, bounds.t2 * triangle),
            key_d: RingMatrixKey::setup(b"d", &[4u8; 32], kappa, bounds.t1 * triangle),
            aggregation_count: aggregation_count(QL::MODULUS),
        };
        let mut f = QuadFn::<QL, D>::blank(r, n);
        f.phi[0][0] = elt(&[1]);
        f.b = inner_product(&f.phi[0], &s[0]);
        let mut g = CtFn::<QL, D>::blank(r, n);
        g.a[0][1] = elt(&[1]);
        g.b0 = from_centered::<QL>(14);
        let relation = Relation {
            rank: n,
            multiplicity: r,
            full: vec![f],
            ct_only: vec![g],
            norm_bound_sq: beta_sq,
        };
        (
            CoreSetup {
                params,
                space: ChallengeSpace::PAPER,
            },
            relation,
            s,
        )
    }

    #[test]
    fn honest_core_argument_verifies_end_to_end() {
        let beta_sq = u128::from(QL::MODULUS);
        let (setup, relation, s) = mini_setup(beta_sq);
        assert!(relation.check(&s).is_ok(), "the mini statement must hold");
        let message = prove_core(&setup, &relation, &[7u8; 32], &s).expect("honest proof");
        verify_core(&setup, &relation, &[7u8; 32], &message).expect("and verifies");
        // Sizes: the proof is u₁, u₂, p and b''; the last message is z, t, g, h.
        assert_eq!(message.p.len(), PROJECTION_ROWS);
        assert_eq!(message.u1.len(), setup.params.inner_key.rows());
        // A different statement seed must not accept this transcript.
        assert!(verify_core(&setup, &relation, &[8u8; 32], &message).is_err());
    }

    #[test]
    fn each_tampered_component_fails_its_own_named_check() {
        let beta_sq = u128::from(QL::MODULUS);
        let (setup, relation, s) = mini_setup(beta_sq);
        let honest = prove_core(&setup, &relation, &[7u8; 32], &s).expect("honest proof");

        // Every case names the check it expects; a bare `is_err()` would also
        // pass when an unrelated earlier guard fires.
        let cases: Vec<(&str, CoreMessage<QL, D>, CoreError)> = {
            let mut v = Vec::new();

            let mut m = honest.clone();
            m.u1[0] = &m.u1[0] + &elt(&[1]);
            v.push(("u₁", m, CoreError::OuterCommitment1));

            let mut m = honest.clone();
            m.u2[0] = &m.u2[0] + &elt(&[1]);
            v.push(("u₂", m, CoreError::OuterCommitment2));

            let mut m = honest.clone();
            m.p[0] += 1;
            v.push(("p", m, CoreError::AggregationConstantTerm { index: 0 }));

            let mut m = honest.clone();
            m.b_double[0] = &m.b_double[0] + &elt(&[1]);
            v.push(("b''", m, CoreError::AggregationConstantTerm { index: 0 }));

            let mut m = honest.clone();
            m.g[1] = &m.g[1] + &elt(&[1]);
            v.push(("g asymmetry", m, CoreError::AsymmetricGarbage));

            let mut m = honest.clone();
            m.h[1] = &m.h[1] + &elt(&[1]);
            v.push(("h asymmetry", m, CoreError::AsymmetricGarbage));

            // A `g` that disagrees with its own committed planes is caught by
            // lines 11–12, *before* line 16 can read it. That is not a gap in
            // line 16: `g` is bound twice over (its digits and, through them,
            // `u₁`, which fixes every later challenge), so no message-only
            // tamper can leave lines 10–13 and 19–20 satisfied while line 16's
            // equation fails. The same argument shields lines 16 and 17 for a
            // tampered `h`.
            let mut m = honest.clone();
            m.g[0] = &m.g[0] + &elt(&[1]);
            v.push(("g vs its digit planes", m, CoreError::DigitRecombination));

            let mut m = honest.clone();
            m.t_digits[0] = &m.t_digits[0] + &elt(&[1]);
            v.push(("t digits", m, CoreError::DigitRecombination));

            let mut m = honest.clone();
            m.z[0] = &m.z[0] + &elt(&[1]);
            v.push(("z vs its two-plane split", m, CoreError::DigitRecombination));

            // Line 15 in isolation: move `z` *and* its split consistently, so
            // lines 10 and 14 still hold and the first failure is the inner
            // commitment link `A·z = Σ cᵢtᵢ`.
            let mut m = honest.clone();
            m.z[0] = &m.z[0] + &elt(&[1]);
            let (lo, hi) = split_short(setup.params.bounds.base, &m.z[0]);
            m.z_digits[0] = lo;
            m.z_digits[1] = hi;
            v.push(("A·z = Σcᵢtᵢ", m, CoreError::InnerLink));

            // Self-consistent edits: value and planes move together, so lines
            // 10–13 stay satisfied. Moving `g`'s planes also moves `u₁`, so the
            // *head* of the report is the commitment check; what these two
            // cases exist to prove is that lines 16 and 17 appear in the
            // report at all — no single-error API can reach them, and the
            // coverage assertion below is what stops them being dead code.
            let mut m = honest.clone();
            m.g[0] = &m.g[0] + &elt(&[1]);
            m.g_digits[0] = &m.g_digits[0] + &elt(&[1]);
            v.push((
                "g + its digits (line 16 in the tail)",
                m,
                CoreError::OuterCommitment1,
            ));

            let mut m = honest.clone();
            m.h[0] = &m.h[0] + &elt(&[1]);
            m.h_digits[0] = &m.h_digits[0] + &elt(&[1]);
            v.push((
                "h + its digits (line 17 in the tail)",
                m,
                CoreError::OuterCommitment2,
            ));

            let mut m = honest.clone();
            m.t[0] = &m.t[0] + &elt(&[1]);
            v.push(("t", m, CoreError::DigitRecombination));

            // Figure 2's projection gate: a `p` long enough to break
            // ‖p‖₂² ≤ 128·β². The gate is what licenses reading `p` back as an
            // integer, so it must fire before anything looks at `p` mod q.
            let mut m = honest.clone();
            m.p[0] = 1_000_000;
            v.push((
                "p beyond √128·β",
                m,
                CoreError::ProjectionNorm {
                    norm_sq: 0,
                    budget: 0,
                },
            ));

            // Figure 3 line 13: a digit plane pushed past the centered
            // half-width with the next plane compensating, so the value still
            // recombines. Only the width bound sees it.
            let mut m = honest.clone();
            m.t_digits[0] = &m.t_digits[0] + &const_elt::<QL, D>(setup.params.bounds.base as i64);
            m.t_digits[1] = &m.t_digits[1] - &elt(&[1]);
            v.push(("wide digit plane", m, CoreError::DigitBound));
            v
        };
        let mut covered: Vec<CoreError> = Vec::new();
        for (label, message, expected) in cases {
            let got = verify_core_report(&setup, &relation, &[7u8; 32], &message);
            assert!(!got.is_empty(), "tampering with {label} was accepted");
            let head = got[0].clone();
            if matches!(expected, CoreError::ProjectionNorm { .. }) {
                // The struct fields are the run's own numbers, so only the
                // variant can be predicted here.
                assert!(
                    matches!(head, CoreError::ProjectionNorm { .. }),
                    "{label}: expected the projection gate, got {head}"
                );
            } else {
                assert_eq!(head, expected, "{label}: wrong check fired");
            }
            assert_eq!(
                verify_core(&setup, &relation, &[7u8; 32], &message),
                Err(head),
                "{label}: verify_core must report the head of the same list"
            );
            for err in got {
                if !covered.contains(&err) {
                    covered.push(err);
                }
            }
        }
        // Every named rejection must fire in *some* report. Firing as the head
        // is asked for case by case above; here the weaker bar is the right one,
        // because a check like line 18 sits behind equations that a
        // statement-level edit also breaks, and "never appears" is the failure
        // mode that actually hides a stub.
        //
        // Two rejections are deliberately not in this list because no *message*
        // edit can produce them: line 14's budget has its own test
        // (`line_14_is_the_consolidated_norm_gate`), which proves its
        // sensitivity by moving the budget, and `Relation` needs a false
        // *statement* (`false_statement_is_rejected_by_line_18`).
        let named = [
            CoreError::ProjectionNorm {
                norm_sq: 0,
                budget: 0,
            },
            CoreError::AggregationConstantTerm { index: 0 },
            CoreError::AsymmetricGarbage,
            CoreError::DigitRecombination,
            CoreError::DigitBound,
            CoreError::InnerLink,
            CoreError::SelfInnerProduct,
            CoreError::LinearClaim,
            CoreError::OuterCommitment1,
            CoreError::OuterCommitment2,
        ];
        let variant = |e: &CoreError| match e {
            CoreError::ProjectionNorm { .. } => 0,
            CoreError::AggregationConstantTerm { .. } => 1,
            CoreError::AsymmetricGarbage => 2,
            CoreError::DigitRecombination => 3,
            CoreError::DigitBound => 4,
            CoreError::NormBudget { .. } => 5,
            CoreError::InnerLink => 6,
            CoreError::SelfInnerProduct => 7,
            CoreError::LinearClaim => 8,
            CoreError::Relation => 9,
            CoreError::OuterCommitment1 => 10,
            CoreError::OuterCommitment2 => 11,
            _ => 99,
        };
        for want in named {
            assert!(
                covered.iter().any(|got| variant(got) == variant(&want)),
                "no tamper ever makes {want} fire, so the check is untested"
            );
        }
    }

    #[test]
    fn line_14_is_the_consolidated_norm_gate() {
        // Equation (5) is the only check that bounds the *revealed* digits as a
        // whole, so its sensitivity is proved by moving its budget rather than
        // by finding a tamper that reaches it: an honest message that passes
        // every other line must be rejected by line 14 alone once the budget
        // drops below the digits' actual squared norm.
        let beta_sq = u128::from(QL::MODULUS);
        let (setup, relation, s) = mini_setup(beta_sq);
        let honest = prove_core(&setup, &relation, &[7u8; 32], &s).expect("honest proof");
        let params = &setup.params;
        let actual = params.decomp1.norm_sq(&honest.z_digits)
            + params.decomp1.norm_sq(&honest.t_digits)
            + params.decomp2.norm_sq(&honest.g_digits)
            + params.decomp1.norm_sq(&honest.h_digits);
        assert!(
            actual <= params.bounds.beta_prime_sq,
            "the honest run must fit the budget it claims (got {actual})"
        );
        assert!(actual > 0, "a zero batch would make this test vacuous");
        let mut tight = setup.clone();
        tight.params.bounds.beta_prime_sq = actual - 1;
        assert_eq!(
            verify_core(&tight, &relation, &[7u8; 32], &honest),
            Err(CoreError::NormBudget {
                actual,
                budget: actual - 1
            }),
            "line 14 must be the failure, not some earlier guard"
        );
    }

    #[test]
    fn false_statement_is_rejected_by_line_18() {
        // Line 18 is the relation itself, so it needs a false *claim*, not an
        // edited message. Bumping one `F` right-hand side changes the
        // transcript, and with it every Fiat–Shamir challenge: the honest
        // message then fails the whole downstream chain, of which line 18 is one
        // member. That cascade is exactly why `verify_core`'s single rejection
        // can never name line 18, and why the report has to be checked as a set.
        let beta_sq = u128::from(QL::MODULUS);
        let (setup, relation, s) = mini_setup(beta_sq);
        let honest = prove_core(&setup, &relation, &[7u8; 32], &s).expect("honest proof");
        let broken = Relation {
            full: relation
                .full
                .iter()
                .map(|f| QuadFn {
                    a: f.a.clone(),
                    phi: f.phi.clone(),
                    b: &f.b + &elt(&[1]),
                })
                .collect(),
            ..relation.clone()
        };
        assert_eq!(
            broken.check(&s),
            Err(RelationError::FullConstraintNonZero { index: 0 }),
            "the edited claim must really be false for this witness"
        );
        let report = verify_core_report(&setup, &broken, &[7u8; 32], &honest);
        assert!(
            report.contains(&CoreError::Relation),
            "line 18 must fire against a false claim; the report was {report:?}"
        );
        assert!(verify_core(&setup, &broken, &[7u8; 32], &honest).is_err());
        // The same message must still verify against the claim it was built for.
        assert_eq!(verify_core(&setup, &relation, &[7u8; 32], &honest), Ok(()));
    }

    #[test]
    fn a_witness_longer_than_the_claim_is_refused_on_both_sides() {
        let beta_sq = 4u128; // ‖s‖₂² = 4 + 49 = 53 already exceeds it
        let (setup, relation, s) = mini_setup(beta_sq);
        assert_eq!(
            relation.check(&s),
            Err(RelationError::NormExceeded {
                norm_sq: 53,
                bound_sq: 4
            })
        );
        // The prover runs the same gate before it commits anything. A small β
        // does *not* trip Theorem 5.1's window (that is a large-β condition),
        // so the refusal has to come from the norm itself.
        assert!(
            matches!(
                prove_core(&setup, &relation, &[7u8; 32], &s),
                Err(CoreError::WitnessNorm {
                    norm_sq: 53,
                    bound_sq: 4
                })
            ),
            "the prover must refuse, naming the norm it refused on"
        );
    }

    #[test]
    fn the_same_machinery_runs_on_a_second_scalar_ring() {
        // A different odd prime: nothing here is specialised to one modulus.
        // Only the ring-generic pieces are exercised — the digit gadget, the
        // garbage identities and the relation check — because the *splitting*
        // requirement of §2 is a property of `(q, d)`, asserted separately
        // above for LaBRADOR's own prime.
        assert_eq!(QS::MODULUS % 2, 1);
        let values: Vec<Elt<QS, 8>> = (0..3)
            .map(|i| {
                Elt::<QS, 8>::from_coefficients(
                    (0..8)
                        .map(|j| from_centered::<QS>(((i * 977 + j * 31) % 4001) as i64 - 2000))
                        .collect(),
                )
            })
            .collect();
        let decomp = Decomposition::new(16, 8); // 16⁸ ≫ 10⁹+7
        let planes = decomp.split(&values);
        assert!(decomp.check(&values, &planes).is_ok());
        // Garbage identities hold over this ring too. Every `sᵢ` has the same
        // rank `n` (the relation's shape), and so does every `φᵢ`.
        let s: Vec<WitnessVec<QS, 8>> = vec![
            values[..2].to_vec(),
            vec![
                Elt::<QS, 8>::from_coefficients((0..8).map(|j| QS::from((j + 1) as u64)).collect()),
                values[2].clone(),
            ],
        ];
        let phi: Vec<WitnessVec<QS, 8>> = vec![s[1].clone(), s[0].clone()];
        let g = garbage_g(&s);
        assert_eq!(g[0 * 2 + 1], g[1 * 2 + 0]);
        let h = garbage_h(&s, &phi);
        assert_eq!(h[0 * 2 + 1], h[1 * 2 + 0]);
        for i in 0..2 {
            assert_eq!(h[i * 2 + i], inner_product(&phi[i], &s[i]));
        }
    }

    #[test]
    fn sigma_pairing_reproduces_the_coefficient_dot_at_d64() {
        // ⟨⃗a,⃗b⟩ = ct(⟨σ⁻¹(a⃗), b⃗⟩) — the identity §2 uses to talk about dot
        // products of coefficient vectors inside R_q, checked against an
        // independent integer accumulation.
        let a: WitnessVec<QL, D> = (0..3)
            .map(|i| {
                Elt::<QL, D>::from_coefficients(
                    (0..D)
                        .map(|j| from_centered::<QL>(((i * 13 + j * 29) % 211) as i64 - 105))
                        .collect(),
                )
            })
            .collect();
        let b: WitnessVec<QL, D> = (0..3)
            .map(|i| {
                Elt::<QL, D>::from_coefficients(
                    (0..D)
                        .map(|j| from_centered::<QL>(((i * 7 + j * 41) % 97) as i64 - 48))
                        .collect(),
                )
            })
            .collect();
        let mut expect = 0i128;
        let modulus = i128::from(QL::MODULUS);
        for (x, y) in a.iter().zip(b.iter()) {
            for (xc, yc) in centered_coeffs::<QL, D>(x)
                .iter()
                .zip(centered_coeffs::<QL, D>(y))
            {
                let (xr, yr) = (i128::from(*xc), i128::from(yc));
                expect += xr.rem_euclid(modulus) * yr.rem_euclid(modulus);
            }
        }
        let got = scalar_inner_product(&a, &b);
        assert_eq!(
            got.to_u128() as u64,
            (expect.rem_euclid(modulus)) as u64,
            "the σ-pairing must equal the flattened coefficient dot"
        );
    }

    #[test]
    fn triangle_picks_the_upper_batch_once() {
        let r = 3usize;
        let batch: Vec<Elt<QL, D>> = (0..r * r).map(|i| elt(&[i as i64])).collect();
        let got = triangle(&batch, r);
        let expect: Vec<i64> = vec![0, 1, 2, 4, 5, 8];
        assert_eq!(got.len(), 6);
        for (i, e) in expect.into_iter().enumerate() {
            assert_eq!(constant_term(&got[i]).centered(), e, "slot {i}");
        }
    }

    // ────────────────────── §5.3: the recursion's target step ──────────────────────

    /// One level's worth of data: the honest message, the verifier's recomputed
    /// view, and the target instance §5.3 builds out of them.
    fn one_level(
        beta_sq: u128,
    ) -> (
        CoreSetup<QL, D>,
        Relation<QL, D>,
        CoreMessage<QL, D>,
        CoreView<QL, D>,
        TargetInstance<QL, D>,
        RecursionPlan,
    ) {
        let seed = [7u8; 32];
        let (setup, relation, s) = mini_setup(beta_sq);
        let message = prove_core(&setup, &relation, &seed, &s).expect("honest proof");
        let view = derive_view(&setup, &relation, &seed, &message).expect("the transcript replays");
        let params = &setup.params;
        let model = size_model(params);
        let plan = RecursionPlan::derive(
            &model,
            relation.multiplicity,
            relation.rank,
            relation.norm_bound_sq,
        );
        let instance = target_instance(
            &relation,
            &view,
            params,
            &plan.shape,
            &message.u1,
            &message.u2,
            &message.z,
            &message.t_digits,
            &message.g_digits,
            &message.h_digits,
        )
        .expect("the target instance");
        (setup, relation, message, view, instance, plan)
    }

    /// The [`SizeModel`] implied by a level's own parameters.
    fn size_model<R: Ring + CenteredRing, const DD: usize>(
        params: &CoreParams<R, DD>,
    ) -> SizeModel {
        SizeModel {
            modulus: R::MODULUS,
            degree: DD,
            tau: ChallengeSpace::PAPER.tau(),
            kappa: params.inner_key.rows(),
            kappa1: params.key_b.rows(),
            kappa2: params.key_d.rows(),
            aggregation_count: params.aggregation_count,
            projection_rows: PROJECTION_ROWS,
        }
    }

    /// The failing family-`F` indices of a witness against a relation.
    fn failing(relation: &Relation<QL, D>, witness: &[WitnessVec<QL, D>]) -> Vec<usize> {
        (0..relation.full.len())
            .filter(|k| !relation.full[*k].value(witness).is_zero())
            .collect()
    }

    #[test]
    fn triangle_pos_is_the_index_triangle_emits() {
        // Every §5.3 coefficient is placed by `triangle_pos`, so it has to agree
        // with the batch `triangle()` actually produces or the target relation
        // would pair each garbage polynomial with the wrong challenges.
        for r in 1..12usize {
            let batch: Vec<Elt<QL, D>> = (0..r * r).map(|i| elt(&[i as i64])).collect();
            let tri = triangle(&batch, r);
            assert_eq!(tri.len(), (r * r + r) / 2);
            for i in 0..r {
                for j in i..r {
                    let p = triangle_pos(r, i, j);
                    assert_eq!(
                        constant_term(&tri[p]),
                        constant_term(&batch[i * r + j]),
                        "r={r}, entry ({i},{j})"
                    );
                }
            }
        }
    }

    #[test]
    fn one_recursion_level_produces_an_instance_of_r() {
        // §5.3: "we obtain a protocol … whose target relation is exactly another
        // instance of R", and Figure 3's caption: the last message *is* a witness
        // for it. Everything below is the paper's own shape claim, not a property
        // of this implementation.
        let (setup, relation, message, _view, instance, plan) = one_level(u128::from(QL::MODULUS));
        let params = &setup.params;
        let r = relation.multiplicity;
        let kappa = params.inner_key.rows();
        let shape = instance.shape;

        instance
            .check_honest()
            .expect("the honest last message must be a witness for the target relation");
        assert_eq!(
            failing(&instance.relation, &instance.witness),
            Vec::<usize>::new(),
            "no equation of (6) may fail on the honest data"
        );
        // (G, {}, β′): the second family is *empty*, which is why the next level
        // needs no `b″(k)` aggregation of its own.
        assert!(instance.relation.ct_only.is_empty(), "F′ must be empty");
        assert_eq!(
            instance.relation.full.len(),
            TargetShape::equation_count(kappa, params.key_b.rows(), params.key_d.rows()),
            "eq. (6) has κ+κ₁+κ₂+3 equations"
        );
        assert_eq!(instance.relation.rank, shape.rank);
        assert_eq!(instance.relation.multiplicity, 2 * shape.nu + shape.mu);
        assert_eq!(
            instance.relation.norm_bound_sq,
            params.bounds.beta_prime_sq,
            "the target's budget is eq. (5)'s (β′)²"
        );
        // §5.3's structural claims about (a′): symmetric, and nonzero only among
        // the 2ν blocks of z — the quadratic part is line 16 alone.
        let line16 = instance.inner_rows + instance.outer1_rows + instance.outer2_rows;
        let quadratic: Vec<usize> = instance
            .relation
            .full
            .iter()
            .enumerate()
            .filter(|(_, f)| f.a.iter().any(|row| row.iter().any(|c| !c.is_zero())))
            .map(|(i, _)| i)
            .collect();
        assert_eq!(
            quadratic,
            vec![line16],
            "exactly one equation of (6) is quadratic, and it is line 16"
        );
        assert_eq!(
            instance.equation(line16),
            Some(TargetEquation::SelfInnerProduct)
        );
        for f in &instance.relation.full {
            for i in 0..f.a.len() {
                for j in 0..f.a.len() {
                    assert_eq!(f.a[i][j], f.a[j][i], "(a′) must be symmetric");
                    if i > 2 * shape.nu || j > 2 * shape.nu {
                        assert!(
                            f.a[i][j].is_zero(),
                            "a′_ij must vanish off the 2ν blocks of z"
                        );
                    }
                }
            }
        }
        // The reblocking holds every element the prover sent: 2·n planes of z plus
        // the m = rt₁κ + (t₁+t₂)(r²+r)/2 planes of v, and nothing more.
        let m = TargetShape::width_v(r, params.decomp1.digits, params.decomp2.digits, kappa);
        assert_eq!(shape.v_width, m);
        assert_eq!(
            message.z_digits.len() + message.t_digits.len() + message.g_digits.len()
                + message.h_digits.len(),
            2 * relation.rank + m,
            "the target witness holds exactly z⁽⁰⁾, z⁽¹⁾ and v"
        );
        assert!(shape.fits());
        assert_eq!(plan.shape, shape, "the plan and the build must agree");
    }

    #[test]
    fn each_target_equation_owns_a_distinct_tamper() {
        // Definition 3.5's factoring is only useful if a *wrong* last message
        // fails a named clause: each family-`F` index maps back to the Figure 3
        // line it restates, and each line is trippable.
        let (_setup, relation, message, view, instance, _plan) = one_level(u128::from(QL::MODULUS));
        let params = _setup.params.clone();
        let kappa = params.inner_key.rows();
        let k1 = params.key_b.rows();
        let k2 = params.key_d.rows();
        let line16 = kappa + k1 + k2;
        let rebuild = |m: &CoreMessage<QL, D>| {
            target_instance(
                &relation,
                &view,
                &params,
                &instance.shape,
                &m.u1,
                &m.u2,
                &m.z,
                &m.t_digits,
                &m.g_digits,
                &m.h_digits,
            )
            .expect("rebuild")
        };

        // u₁[x] appears in exactly one equation, so it owns it alone.
        for x in 0..k1 {
            let mut m = message.clone();
            m.u1[x] = &m.u1[x] + &elt(&[1]);
            let built = rebuild(&m);
            assert_eq!(
                failing(&built.relation, &built.witness),
                vec![kappa + x],
                "u₁[{x}] must fail only the line-19 equation of row {x}"
            );
            assert_eq!(
                built.equation(kappa + x),
                Some(TargetEquation::OuterCommitment1 { row: x })
            );
        }
        for x in 0..k2 {
            let mut m = message.clone();
            m.u2[x] = &m.u2[x] + &elt(&[1]);
            let built = rebuild(&m);
            assert_eq!(
                failing(&built.relation, &built.witness),
                vec![kappa + k1 + x],
                "u₂[{x}] must fail only the line-20 equation of row {x}"
            );
        }
        // Each remaining batch is a coefficient of a *predictable* subset, and
        // the subset is exactly which equations read it (line 18's `a` is zero on
        // the diagonal in this fixture, which is why the `g` edit does not reach
        // it and the diagonal `h` edit does).
        let line16 = kappa + k1 + k2;
        let line17 = line16 + 1;
        let line18 = line17 + 1;
        let rows: Vec<usize> = (0..kappa).collect();
        let outer1: Vec<usize> = (kappa..kappa + k1).collect();
        let outer2: Vec<usize> = (kappa + k1..kappa + k1 + k2).collect();
        for (label, edit, expect) in [
            (
                "z",
                0usize,
                rows.iter()
                    .chain([line16].iter())
                    .chain([line17].iter())
                    .copied()
                    .collect::<Vec<_>>(),
            ),
            (
                "t",
                0usize,
                [0usize].iter().chain(outer1.iter()).copied().collect(),
            ),
            (
                "g",
                2usize,
                outer1.iter().chain([line16].iter()).copied().collect(),
            ),
            (
                "h",
                2usize,
                outer2
                    .iter()
                    .chain([line17].iter())
                    .chain([line18].iter())
                    .copied()
                    .collect(),
            ),
        ] {
            let mut m = message.clone();
            match label {
                "z" => m.z[0] = &m.z[0] + &elt(&[1]),
                "t" => m.t_digits[edit] = &m.t_digits[edit] + &elt(&[1]),
                "g" => m.g_digits[edit] = &m.g_digits[edit] + &elt(&[1]),
                _ => m.h_digits[edit] = &m.h_digits[edit] + &elt(&[1]),
            }
            let built = rebuild(&m);
            let names: Vec<&str> = failing(&built.relation, &built.witness)
                .iter()
                .map(|i| built.equation(*i).expect("named").name())
                .collect();
            assert_eq!(
                failing(&built.relation, &built.witness),
                expect,
                "{label}[{edit}] trips {names:?}"
            );
        }
        // Across the whole battery every family of (6) is tripped by something, so
        // none of them is dead code reached only after another check has failed.
        assert_eq!(
            instance.equation(line18),
            Some(TargetEquation::Relation),
            "line 18's index must be the last equation of (6)"
        );
        // Every index the builder can produce names a line, and one past the end
        // names nothing: the map is total over (6).
        for i in 0..(kappa + k1 + k2 + 3) {
            assert!(
                rebuild(&message).equation(i).is_some(),
                "equation {i} must be named"
            );
        }
        assert_eq!(rebuild(&message).equation(kappa + k1 + k2 + 3), None);
    }

    #[test]
    fn target_norm_budget_fails_alone_and_is_tight() {
        // eq. (5) is the one clause of the target relation that is not an
        // equation, so it has to be falsifiable by itself. The way to see that is
        // to tighten *only* the budget: if the equations were carrying the
        // rejection, the honest witness would already be failing one of them, and
        // if the budget were vacuous no tightening would matter.
        let (_setup, _relation, _message, _view, instance, plan) = one_level(u128::from(QL::MODULUS));
        let budget = instance.relation.norm_bound_sq;
        let honest = witness_norm_sq(&instance.witness);
        assert!(
            honest <= budget,
            "the honest target has Σ‖s′‖² = {honest} against (β′)² = {budget}"
        );
        assert!(honest > 0, "a zero target norm would make the gate vacuous");
        assert!(
            budget < u128::MAX / 4,
            "(β′)² must be a real bound, not a saturated one"
        );
        assert_eq!(plan.bounds.beta_prime_sq, budget);
        assert_eq!(failing(&instance.relation, &instance.witness).len(), 0);
        let mut tight = instance.relation.clone();
        tight.norm_bound_sq = honest - 1;
        assert_eq!(
            tight.check(&instance.witness),
            Err(RelationError::NormExceeded {
                norm_sq: honest,
                bound_sq: honest - 1
            }),
            "one unit below the honest norm, and only the budget rejects"
        );
        assert_eq!(
            failing(&tight, &instance.witness).len(),
            0,
            "every equation of (6) still vanishes: the norm clause is independent"
        );
    }

    #[test]
    fn target_shape_must_cover_the_level() {
        // A reblocking that cannot hold `n` or `m` elements would silently drop
        // part of the witness, so the builder refuses it by name.
        let (setup, relation, message, view, instance, _plan) = one_level(u128::from(QL::MODULUS));
        let params = setup.params.clone();
        let good = instance.shape;
        assert!(good.fits());
        for bad in [
            TargetShape {
                mu: 0,
                ..good
            },
            TargetShape {
                nu: 0,
                ..good
            },
            TargetShape {
                rank: good.rank.saturating_sub(1).max(1),
                ..good
            },
            TargetShape {
                source_rank: good.source_rank + 100,
                ..good
            },
        ] {
            let fits = bad.fits();
            let got = target_instance(
                &relation,
                &view,
                &params,
                &bad,
                &message.u1,
                &message.u2,
                &message.z,
                &message.t_digits,
                &message.g_digits,
                &message.h_digits,
            );
            if fits {
                // A shape that still covers is accepted, even if wasteful.
                assert!(got.is_ok(), "a covering shape must build: {bad:?}");
            } else {
                assert_eq!(
                    got.err(),
                    Some(CoreError::TargetShape),
                    "a non-covering shape must be refused: {bad:?}"
                );
            }
        }
        // A plane batch that is not this level's plane count is a different
        // message, not a bigger one: the builder reports both lengths.
        let mut short = message.clone();
        short.t_digits.pop();
        let t_expect = relation.multiplicity * setup.params.inner_key.rows()
            * setup.params.decomp1.digits;
        assert_eq!(
            target_instance(
                &relation,
                &view,
                &params,
                &good,
                &short.u1,
                &short.u2,
                &short.z,
                &short.t_digits,
                &short.g_digits,
                &short.h_digits,
            )
            .err(),
            Some(CoreError::WrongShape {
                got: t_expect - 1,
                expected: t_expect
            }),
            "a truncated plane batch must name the length it wanted"
        );
        // Whatever the search returns always covers, over a wide range of shapes.
        let model = size_model(&params);
        for n in 1..40usize {
            for m in [1usize, 7, 33, 400, 5000] {
                let shape = TargetShape::derive(n, m, u128::from(QL::MODULUS), &model);
                assert!(shape.fits(), "derive must return a covering shape (n={n}, m={m})");
                assert!(shape.target_width() >= 2 * n + m, "padding can only add");
            }
        }
    }

    #[test]
    fn derive_view_reproduces_what_the_verifier_checks() {
        // The refactor of Figure 3 lines 3–7 into `derive_view` must return the
        // very data lines 15–18 consume, or the recursion would be built from a
        // statement nobody verified. Each equality below is one of those lines.
        let (setup, relation, message, view, _instance, _plan) = one_level(u128::from(QL::MODULUS));
        let params = &setup.params;
        let r = relation.multiplicity;
        assert_eq!(view.c.len(), r);
        assert_eq!(view.claims.len(), params.aggregation_count);
        for (k, claim) in view.claims.iter().enumerate() {
            assert_eq!(
                constant_term(&message.b_double[k]),
                *claim,
                "line b″(k)₀ must hold for the view's own claim"
            );
        }
        // Line 15: A·z = Σ cᵢtᵢ, using only the view's challenges.
        assert_eq!(
            params.inner_key.matvec(&message.z).expect("shape"),
            {
                let mut rhs = vec![zero_elt::<QL, D>(); params.inner_key.rows()];
                for i in 0..r {
                    for x in 0..params.inner_key.rows() {
                        rhs[x] += message.t[i * params.inner_key.rows() + x].clone() * view.c[i].clone();
                    }
                }
                rhs
            },
            "the view's cᵢ must satisfy line 15"
        );
        // Line 18: Σ aᵢⱼgᵢⱼ + Σ hᵢᵢ = b, using only the view's statement.
        let mut acc = zero_elt::<QL, D>();
        for i in 0..r {
            for j in 0..r {
                acc += view.statement.a[i][j].clone().mul_ref(&message.g[i * r + j]);
            }
        }
        for i in 0..r {
            acc += message.h[i * r + i].clone();
        }
        assert_eq!(acc, view.statement.b, "the view's b must be line 18's");
        // Line 16 with the view's challenges: ⟨z,z⟩ = Σ gᵢⱼcᵢcⱼ.
        let mut rhs = zero_elt::<QL, D>();
        for i in 0..r {
            for j in 0..r {
                rhs += message.g[i * r + j].clone() * (view.c[i].clone() * view.c[j].clone());
            }
        }
        assert_eq!(inner_product(&message.z, &message.z), rhs);
    }

    #[test]
    fn size_model_is_the_section_57_sum_of_four_and_four_terms() {
        // §5.7's two formulas, term by term, with every width a ceiling.
        let setup = mini_setup(u128::from(QL::MODULUS)).0;
        let params = &setup.params;
        let model = size_model(params);
        let beta_sq = u128::from(QL::MODULUS);
        let (r, n) = (2usize, 1usize);
        let got = model.size(r, n, beta_sq);

        let q_width = log2_ceil_u128(u128::from(QL::MODULUS));
        assert_eq!(q_width, 32, "q ≈ 2³² encodes in 32 bits");
        let d = wide(D);
        // 12β/√2 = √(72β²) = 556_092 for β = √q, which is 20 bits, not 556_092:
        // pinning the log keeps a magnitude from sneaking in as a width.
        assert_eq!(isqrt_ceil(72 * beta_sq), 556_092);
        assert_eq!(log2_ceil_u128(556_092), 20);
        let core = wide(model.kappa1 + model.kappa2) * d * q_width
            + wide(PROJECTION_ROWS) * log2_ceil_u128(isqrt_ceil(72 * beta_sq))
            + wide(model.aggregation_count) * d * q_width
            + 4 * 128;
        assert_eq!(got.core_bits, core, "the four core terms of §5.7");
        // (κ₁+κ₂)d·log q + 256·20 + ⌈128/log q⌉·d·log q + 4·128, in bits:
        // 8·64·32 + 5120 + 4·64·32 + 512. Term-by-term so a width-as-magnitude
        // regression cannot hide inside the sum.
        assert_eq!(
            got.core_bits,
            8 * 64 * 32 + 256 * 20 + 4 * 64 * 32 + 512,
            "(κ₁+κ₂)d log q + 256·log(12β/√2) + ⌈128/log q⌉·d·log q + 4·128"
        );
        let nd = wide(n * D);
        let tri = wide((r * r + r) / 2);
        let last = nd * log2_ceil_u128(isqrt_ceil(ceil_div(144 * beta_sq * 71, nd)))
            + wide(r) * wide(model.kappa) * d * q_width
            + tri * d * log2_ceil_u128(isqrt_ceil(ceil_div(288 * beta_sq * beta_sq, wide(r * r) * nd)))
            + tri * d * q_width;
        assert_eq!(got.last_message_bits, last, "the four last-message terms");
        assert!(got.total_bits() > got.last_message_bits);
        // Growing the rank must grow the message, and doubling β must not shrink
        // anything: the model is monotone, so a "saving" can never be an artefact
        // of a width rounding down.
        assert!(model.size(r, n + 1, beta_sq).last_message_bits > last);
        assert!(model.size(r, n, beta_sq * 4).last_message_bits > last);
        assert!(model.size(r + 1, n, beta_sq).last_message_bits > last);
    }

    #[test]
    fn recursion_compacts_only_above_a_shape_threshold() {
        // The quantitative question §6.1's Table 3 answers: a level pays when
        // `core_target + last_target < last_this`. The witness width has to beat
        // the level's own commitment and garbage overhead, `m = rt₁κ +
        // (t₁+t₂)(r²+r)/2`, which does not shrink with `n`.
        let setup = mini_setup(u128::from(QL::MODULUS)).0;
        let model = size_model(&setup.params);
        let beta_sq = u128::from(QL::MODULUS);
        let mut first_winning = None;
        for n in 1..=400usize {
            let plan = RecursionPlan::derive(&model, 8, n, beta_sq);
            assert!(plan.shape.fits());
            if plan.compacts() {
                first_winning.get_or_insert(n);
            } else if n >= 40 {
                assert!(
                    plan.saving_bits() < 0,
                    "a non-compacting level at n={n} must report a cost, got {}",
                    plan.saving_bits()
                );
            }
        }
        let threshold = first_winning.unwrap_or(usize::MAX);
        assert!(
            threshold > 3,
            "at this crate's κ and t₁, one level cannot pay for a rank-3 relation"
        );
        // The shape the paper's own table lands on (r = 8, n in the hundreds) does
        // compact, and monotonically so from the threshold up.
        assert!(
            threshold <= 400,
            "no shape up to n = 400 compacts at κ = {}, t₁ = {}: the recursion would \
             need an instance larger than this crate's toy regime",
            model.kappa,
            setup.params.bounds.t1
        );
        for n in threshold..=400usize {
            assert!(
                RecursionPlan::derive(&model, 8, n, beta_sq).compacts(),
                "compaction must not switch back off at n = {n} (threshold {threshold})"
            );
        }
        // And at the tiny shape the toy R1CS reduces to, it is a *loss*: this is
        // the number that decides whether the example can shrink.
        let plan = RecursionPlan::derive(&model, 8, 3, beta_sq);
        assert!(!plan.compacts());
        assert!(plan.saving_bits() < 0);
    }

    #[test]
    fn the_second_level_proves_the_first_levels_target() {
        // Lemma 3.7 in code: run the protocol on the target relation of a first
        // run, and the two together prove the original statement. This is the
        // only place the recursion is *executed* rather than constructed, so it is
        // also the check that `target_instance` returns a relation `prove_core` can
        // consume — same type, same norm discipline, smaller witness.
        //
        // κ = 1 keeps the second execution's projection inside a unit test's
        // budget; see `mini_setup_k`.
        let beta_sq = u128::from(QL::MODULUS);
        let (setup, relation, s) = mini_setup_k(beta_sq, 1);
        let seed = [7u8; 32];
        let m0 = prove_core(&setup, &relation, &seed, &s).expect("level 0");
        let view = derive_view(&setup, &relation, &seed, &m0).expect("level 0 replays");
        let model = SizeModel {
            modulus: QL::MODULUS,
            degree: D,
            tau: ChallengeSpace::PAPER.tau(),
            kappa: 1,
            kappa1: setup.params.key_b.rows(),
            kappa2: setup.params.key_d.rows(),
            aggregation_count: setup.params.aggregation_count,
            projection_rows: PROJECTION_ROWS,
        };
        let plan = RecursionPlan::derive(&model, relation.multiplicity, relation.rank, beta_sq);
        let target = target_instance(
            &relation,
            &view,
            &setup.params,
            &plan.shape,
            &m0.u1,
            &m0.u2,
            &m0.z,
            &m0.t_digits,
            &m0.g_digits,
            &m0.h_digits,
        )
        .expect("level 0's target");
        target
            .check_honest()
            .expect("and it is really a witness for it");

        // Level 1's own CRS and §5.4 parameters, sized by the target shape.
        //
        // Note what is NOT asserted here: that the target witness is *shorter*
        // than the source. §5.3's target is `2n + m` ring elements, and `m` — the
        // digit planes of t, g, h — does not shrink with `n`, so at a toy shape
        // (`r·n = 2`, `m = 32`) recursion is a size *loss*; that question is
        // `recursion_compacts_only_above_a_shape_threshold`, and answering it here
        // would conflate "the level composes" with "the level pays".
        let r1 = target.relation.multiplicity;
        let n1 = target.relation.rank;
        assert!(
            target.relation.multiplicity * target.relation.rank
                >= 2 * relation.rank + plan.shape.v_width,
            "the reblocking can pad but never drop: {}·{} < 2·{} + {}",
            r1,
            n1,
            relation.rank,
            plan.shape.v_width
        );
        let bounds1 = NormBounds::derive(
            target.relation.norm_bound_sq,
            QL::MODULUS,
            r1,
            n1,
            1,
            D,
            ChallengeSpace::PAPER.tau(),
        );
        let decomp1 = Decomposition::new(bounds1.base, bounds1.t1);
        let decomp2 = Decomposition::new(bounds1.base, bounds1.t2);
        decomp1.validate::<QL>().expect("t₁ planes cover q at level 1");
        let tri1 = (r1 * r1 + r1) / 2;
        let setup1 = CoreSetup {
            params: CoreParams {
                inner_key: RingMatrixKey::setup(b"l1-A", &[9u8; 32], 1, n1),
                key_b: RingMatrixKey::setup(b"l1-B", &[10u8; 32], 1, r1 * bounds1.t1),
                key_c: RingMatrixKey::setup(b"l1-C", &[11u8; 32], 1, bounds1.t2 * tri1),
                key_d: RingMatrixKey::setup(b"l1-D", &[12u8; 32], 1, bounds1.t1 * tri1),
                decomp1,
                decomp2,
                bounds: bounds1,
                aggregation_count: setup.params.aggregation_count,
            },
            space: ChallengeSpace::PAPER,
        };
        assert_eq!(setup1.params.key_b.cols(), r1 * 1 * setup1.params.decomp1.digits);

        // §5.4's remedy for an honest run whose *heuristic* bounds are overrun is
        // to restart the protocol with a fresh projection (which re-draws every
        // later challenge), not to widen a check. The loop is that remedy; a
        // restart that was needed is reported, and a non-heuristic failure is a
        // bug and panics.
        let mut restarts = 0u32;
        let mut level1_seed = [11u8; 32];
        let m1 = loop {
            match prove_core(&setup1, &target.relation, &level1_seed, &target.witness) {
                Ok(m) => break m,
                Err(e)
                    if matches!(
                        e,
                        CoreError::NormBudget { .. }
                            | CoreError::ProjectionNorm { .. }
                            | CoreError::DigitCapacity
                    ) =>
                {
                    restarts += 1;
                    assert!(restarts <= 4, "level 1 never fitted its bounds: {e}");
                    level1_seed = [11u8 + restarts as u8; 32];
                }
                Err(e) => panic!("level 1 failed for a non-heuristic reason: {e}"),
            }
        };
        verify_core(&setup1, &target.relation, &level1_seed, &m1).expect("and verifies");
        // Level 1 is itself a well-formed instance with its own §5.4 budget, which
        // is what makes the chain extendable. Whether each link is *smaller* is
        // the shape question the sweep test answers, not this one.
        let level1 = model.size(r1, n1, target.relation.norm_bound_sq);
        assert!(level1.total_bits() > 0);
        assert!(setup1.params.bounds.beta_prime_sq > 0);
        assert!(setup1.params.bounds.beta_prime_sq <= target.relation.norm_bound_sq);
        // And the composed proof is verifiable end to end: a tampered level-1
        // message dies by its own named check, exactly as at level 0.
        let mut bad = m1.clone();
        bad.u1[0] = &bad.u1[0] + &elt(&[1]);
        assert_eq!(
            verify_core(&setup1, &target.relation, &level1_seed, &bad),
            Err(CoreError::OuterCommitment1),
            "level 1's outer commitment is its own gate"
        );
        let mut bad = m1.clone();
        bad.z[0] = &bad.z[0] + &elt(&[1]);
        assert!(verify_core(&setup1, &target.relation, &level1_seed, &bad).is_err());
        assert!(restarts <= 4, "restarts = {restarts}");
    }

    /// The level-0 statement §5.3's `Ṽ` outputs for a composed proof's head.
    fn target_of(
        setup: &CoreSetup<QL, D>,
        relation: &Relation<QL, D>,
        seed: &[u8; 32],
        proof: &ComposedProof<QL, D>,
    ) -> Relation<QL, D> {
        let view = derive_view_at_head(setup, relation, seed, &proof.head).expect("replays");
        target_statement(
            relation,
            &view,
            &setup.params,
            &proof.shape,
            &proof.head.u1,
            &proof.head.u2,
        )
        .expect("the target statement is derivable from the head alone")
    }

    #[test]
    fn sampled_instance_holds_at_its_requested_shape_and_budget() {
        // The recursion's economics are a function of `(r, n, β²)` and the CRS
        // ranks, so a statement of a *requested* shape has to be available
        // without the §6 reduction. What `sample_instance` promises is that the
        // promise is real: satisfiable, symmetric where §5.1 says it may be, and
        // bounded by the budget the caller — not the sampler — chose.
        let beta_sq = u128::from(QL::MODULUS);
        let (relation, s) = sample_instance::<QL, D>(&[3u8; 32], 3, 2, 2, 2, beta_sq);
        assert_eq!(relation.multiplicity, 3);
        assert_eq!(relation.rank, 2);
        assert_eq!(relation.full.len(), 2);
        assert_eq!(relation.ct_only.len(), 2);
        assert_eq!(relation.norm_bound_sq, beta_sq);
        relation
            .check(&s)
            .expect("the sampled statement is satisfiable by its own witness");
        for f in &relation.full {
            for i in 0..3 {
                for j in 0..3 {
                    assert_eq!(f.a[i][j], f.a[j][i], "(a_ij) must be symmetric");
                }
            }
        }
        for f in &relation.ct_only {
            for i in 0..3 {
                for j in 0..3 {
                    assert_eq!(f.a[i][j], f.a[j][i], "so must F''s");
                }
            }
        }
        // One unit under the honest norm and only the budget clause rejects: the
        // sampler cannot be used to hand out a free `β`.
        let honest = witness_norm_sq(&s);
        let tight = Relation {
            norm_bound_sq: honest - 1,
            ..relation.clone()
        };
        assert_eq!(
            tight.check(&s),
            Err(RelationError::NormExceeded {
                norm_sq: honest,
                bound_sq: honest - 1
            })
        );
        // A moved witness names a constraint, so the equations are real too.
        let mut bad = s.clone();
        bad[0][0] = &bad[0][0] + &elt(&[1]);
        assert!(matches!(
            relation.check(&bad),
            Err(RelationError::FullConstraintNonZero { .. })
                | Err(RelationError::ConstantTermNonZero { .. })
        ));
        // Deterministic in the seed, and a different seed is a different statement.
        let (again, _) = sample_instance::<QL, D>(&[3u8; 32], 3, 2, 2, 2, beta_sq);
        assert_eq!(again.full[0].b, relation.full[0].b);
        let (other, _) = sample_instance::<QL, D>(&[4u8; 32], 3, 2, 2, 2, beta_sq);
        assert_ne!(other.full[0].b, relation.full[0].b);
    }

    #[test]
    fn target_relation_survives_a_diagonal_a_matrix() {
        // Figure 3 line 18 is `Σ_{i,j} a_ij g_ij + Σᵢ h_ii = b` over the *full*
        // matrix, but only the `i ≤ j` triangle of `g` is transmitted, so the
        // target's restatement must weight off-diagonal planes by `a_ij + a_ji`
        // and diagonal ones by `a_ii`. A statement with a zero diagonal — which is
        // what the §6 reduction happens to produce — cannot tell the two apart,
        // and the composition would then be proving a *different* relation than
        // the one level 0 verified. `sample_instance` fills the diagonal, so this
        // is the case that catches it.
        let beta_sq = u128::from(QL::MODULUS);
        let (relation, s) = sample_instance::<QL, D>(&[5u8; 32], 3, 2, 2, 2, beta_sq);
        let diagonal: Vec<Elt<QL, D>> = relation.full[0]
            .a
            .iter()
            .enumerate()
            .map(|(i, row)| row[i].clone())
            .collect();
        assert!(
            diagonal.iter().any(|d| !d.is_zero()),
            "the fixture must actually exercise a_ii ≠ 0"
        );
        relation.check(&s).expect("and be satisfiable");
        let kappa = 4usize;
        let bounds = NormBounds::derive(beta_sq, QL::MODULUS, 3, 2, kappa, D, ChallengeSpace::PAPER.tau());
        let decomp1 = Decomposition::new(bounds.base, bounds.t1);
        let decomp2 = Decomposition::new(bounds.base, bounds.t2);
        decomp1.validate::<QL>().expect("the planes span q");
        let triangle = (3 * 3 + 3) / 2;
        let setup = CoreSetup {
            params: CoreParams {
                inner_key: RingMatrixKey::setup(b"inner", &[1u8; 32], kappa, 2),
                key_b: RingMatrixKey::setup(b"b", &[2u8; 32], kappa, 3 * bounds.t1 * kappa),
                key_c: RingMatrixKey::setup(b"c", &[3u8; 32], kappa, bounds.t2 * triangle),
                key_d: RingMatrixKey::setup(b"d", &[4u8; 32], kappa, bounds.t1 * triangle),
                decomp1,
                decomp2,
                bounds,
                aggregation_count: aggregation_count(QL::MODULUS),
            },
            space: ChallengeSpace::PAPER,
        };
        let seed = [6u8; 32];
        let message = prove_core(&setup, &relation, &seed, &s).expect("level 0 runs");
        let view = derive_view(&setup, &relation, &seed, &message).expect("it replays");
        let plan = RecursionPlan::of(&setup, &relation);
        let instance = target_instance(
            &relation,
            &view,
            &setup.params,
            &plan.shape,
            &message.u1,
            &message.u2,
            &message.z,
            &message.t_digits,
            &message.g_digits,
            &message.h_digits,
        )
        .expect("the target builds");
        instance.check_honest().expect("with a diagonal a, the honest last message is still a witness for R′");
        assert_eq!(
            failing(&instance.relation, &instance.witness),
            Vec::<usize>::new(),
            "and no equation of (6) fails"
        );
        // The composed verifier accepts the same chain, so level 1 really proves
        // the level-0 claims rather than a shifted copy of them.
        let proof = prove_composed(&setup, &relation, &seed, &s).expect("one composed level");
        let report = verify_composed_report(&setup, &relation, &seed, &proof);
        assert!(report.is_empty(), "diagonal-a composition: {report:?}");
    }

    #[test]
    fn composed_proof_carries_no_last_message_and_verifies() {
        // Definition 3.6 in one call: level 0's head, then a proof of the target
        // relation that head defines. §5.3 p.15's accept condition is exactly
        // ‖p‖ < √128β, correct b″(k)₀, and that proof — which is why the
        // `z, t, g, h` a terminating verifier needs are absent from the type.
        let beta_sq = u128::from(QL::MODULUS);
        let (setup, relation, s) = mini_setup_k(beta_sq, 1);
        let seed = [7u8; 32];
        let direct = prove_core(&setup, &relation, &seed, &s).expect("level 0");
        let proof = prove_composed(&setup, &relation, &seed, &s).expect("one composed level");
        let report = verify_composed_report(&setup, &relation, &seed, &proof);
        assert!(report.is_empty(), "the honest composition: {report:?}");
        verify_composed(&setup, &relation, &seed, &proof).expect("accepted");

        // The head is precisely Figure 2's four pre-last-message prover messages.
        assert_eq!(proof.head.u1.len(), setup.params.key_b.rows());
        assert_eq!(proof.head.u2.len(), setup.params.key_d.rows());
        assert_eq!(proof.head.b_double.len(), setup.params.aggregation_count);
        assert_eq!(proof.head.p.len(), PROJECTION_ROWS);
        for (a, b) in proof.head.u1.iter().zip(direct.u1.iter()) {
            assert_eq!(a, b, "the head is the transcript the direct run produced");
        }
        assert_eq!(proof.head.p, direct.p);
        // What a terminating verifier would have had to receive, versus what the
        // composed one receives as *proof*: level 0's planes are gone, and the
        // last message on the wire is now the target level's own.
        let plan = RecursionPlan::of(&setup, &relation);
        assert_eq!(proof.shape, plan.shape, "the reblocking is derived, not sent");
        assert_eq!(
            direct.last_message_planes(),
            2 * relation.rank + plan.shape.v_width,
            "z⁽⁰⁾,z⁽¹⁾ and v = t‖g‖h, in planes"
        );
        assert!(proof.last_message_planes() > 0);
        let target = target_of(&setup, &relation, &seed, &proof);
        assert_eq!(proof.next.z.len(), target.rank, "level 1 opens its own z⃗′");
        assert_eq!(
            proof.next.t.len(),
            target.multiplicity * setup.params.inner_key.rows(),
            "and its own r′·κ inner commitments"
        );
        let next = next_level_setup(&setup, &target, &level_seed(&seed, proof.reroll))
            .expect("level 1 instantiates here");
        let tri1 = (target.multiplicity * target.multiplicity + target.multiplicity) / 2;
        assert_eq!(proof.next.z_digits.len(), 2 * target.rank);
        assert_eq!(
            proof.next.t_digits.len(),
            target.multiplicity * next.params.inner_key.rows() * next.params.decomp1.digits
        );
        assert_eq!(proof.next.g_digits.len(), tri1 * next.params.decomp2.digits);
        assert_eq!(proof.next.h_digits.len(), tri1 * next.params.decomp1.digits);
        // A different CRS seed derives a different target, so the same proof dies.
        assert!(!verify_composed_report(&setup, &relation, &[8u8; 32], &proof).is_empty());
        // And a different statement does too: the target is a function of both.
        let mut moved = relation.clone();
        moved.full[0].b = &moved.full[0].b + &elt(&[1]);
        assert!(!verify_composed_report(&setup, &moved, &seed, &proof).is_empty());
    }

    #[test]
    fn every_composed_check_owns_a_tamper() {
        // Each RecursionError variant must be reachable by some edit, and the
        // report must be a *set*: a head that moves also moves the target
        // relation, so several levels of rejection are legitimately live at once.
        let beta_sq = u128::from(QL::MODULUS);
        let (setup, relation, s) = mini_setup_k(beta_sq, 1);
        let seed = [7u8; 32];
        let proof = prove_composed(&setup, &relation, &seed, &s).expect("composed proof");
        let kinds = |r: &Vec<RecursionError>| -> Vec<&'static str> {
            r.iter()
                .map(|e| match e {
                    RecursionError::Reroll { .. } => "reroll",
                    RecursionError::Head(CoreError::ProjectionNorm { .. }) => "head-norm",
                    RecursionError::Head(CoreError::AggregationConstantTerm { .. }) => "head-ct",
                    RecursionError::Head(_) => "head-other",
                    RecursionError::Shape { .. } => "shape",
                    RecursionError::Budget { .. } => "budget",
                    RecursionError::NextSetup(_) => "next-setup",
                    RecursionError::NextLevel(_) => "next-level",
                })
                .collect()
        };
        let mut seen: Vec<&'static str> = Vec::new();

        // Out-of-range re-roll: the next level's CRS cannot be replayed, so this
        // is reported alone rather than as a wall of downstream failures.
        let mut p = proof.clone();
        p.reroll = MAX_PROJECTION_REROLLS;
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert_eq!(r, vec![RecursionError::Reroll { got: MAX_PROJECTION_REROLLS }]);
        seen.extend(kinds(&r));

        // A reblocking the prover chose instead of derived.
        let mut p = proof.clone();
        p.shape.nu += 1;
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert_eq!(
            r,
            vec![RecursionError::Shape {
                nu: p.shape.nu,
                mu: p.shape.mu,
                rank: p.shape.rank,
            }],
            "a chosen shape must be refused on its own, before anything reads it"
        );
        seen.extend(kinds(&r));

        // A short head cannot be mistaken for a passing one.
        let mut p = proof.clone();
        p.head.u1.pop();
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert!(matches!(
            r.as_slice(),
            [RecursionError::Head(CoreError::WrongShape { .. })]
        ));
        seen.extend(kinds(&r));

        // §5.3's first direct condition.
        let mut p = proof.clone();
        for v in p.head.p.iter_mut() {
            *v *= 1 << 20;
        }
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert!(
            r.contains(&RecursionError::Head(CoreError::ProjectionNorm {
                norm_sq: p.head.p.iter().map(|v| u128::from(v.unsigned_abs()) * u128::from(v.unsigned_abs())).sum(),
                budget: 128 * beta_sq,
            })),
            "‖p‖² ≤ 128β² is the composed verifier's own gate: {r:?}"
        );
        seen.extend(kinds(&r));

        // …and the second: one b″(k) out of place.
        let mut p = proof.clone();
        p.head.b_double[0] = &p.head.b_double[0] + &elt(&[1]);
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert!(r.contains(&RecursionError::Head(CoreError::AggregationConstantTerm { index: 0 })));
        seen.extend(kinds(&r));

        // The norm statement the recursion took off the wire: a proof that
        // declares someone else's `(β′)²` must be refused, and by that alone —
        // nothing else about it is inconsistent, which is exactly why the check
        // has to exist.
        let mut p = proof.clone();
        p.target_norm_bound_sq -= 1;
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert_eq!(
            r,
            vec![RecursionError::Budget {
                claimed: proof.target_norm_bound_sq - 1,
                derived: setup.params.bounds.beta_prime_sq,
            }],
            "a tightened declared budget must be the only thing reported: {r:?}"
        );
        seen.extend(kinds(&r));
        assert!(
            composed_norm_bound_sq(proof.target_norm_bound_sq) > proof.target_norm_bound_sq,
            "what the composed verifier is guaranteed is strictly weaker than line 14's"
        );
        assert_eq!(
            composed_norm_bound_sq(30),
            128,
            "the slack is exactly 128/30, rounded up"
        );
        assert_eq!(composed_norm_bound_sq(31), ceil_div(31 * 128, 30));

        // The claims that used to be re-sent are now *proved*: editing level 0's
        // last message is no longer possible (there is no such field), so the
        // corresponding forgeries are edits of level 1's message, and each dies
        // inside the NextLevel report.
        let mut p = proof.clone();
        p.next.u1[0] = &p.next.u1[0] + &elt(&[1]);
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert!(r.contains(&RecursionError::NextLevel(CoreError::OuterCommitment1)));
        seen.extend(kinds(&r));

        let mut p = proof.clone();
        p.next.z_digits[0] = &p.next.z_digits[0] + &elt(&[1]);
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert!(r.iter().any(|e| matches!(e, RecursionError::NextLevel(_))));
        seen.extend(kinds(&r));

        // Level 1's inner link — the composed form of "A₀·z₀ = Σ cᵢtᵢ,₀", which the
        // composed verifier now believes only because level 1 proves it.
        let mut p = proof.clone();
        p.next.t_digits[0] = &p.next.t_digits[0] + &elt(&[1]);
        let r = verify_composed_report(&setup, &relation, &seed, &p);
        assert!(!r.is_empty(), "a moved plane cannot leave the chain satisfied");
        seen.extend(kinds(&r));

        for kind in [
            "reroll",
            "shape",
            "budget",
            "head-other",
            "head-norm",
            "head-ct",
            "next-level",
        ] {
            assert!(
                seen.contains(&kind),
                "no tamper ever produces {kind}, so that check could be dead code"
            );
        }
    }

    #[test]
    fn next_level_setup_derives_the_target_shape_or_refuses_the_level() {
        // §6.1's per-level parameter step, and the two ways it says *no*.
        let beta_sq = u128::from(QL::MODULUS);
        let (setup, relation, s) = mini_setup_k(beta_sq, 1);
        let seed = [7u8; 32];
        let proof = prove_composed(&setup, &relation, &seed, &s).expect("composed proof");
        let target = target_of(&setup, &relation, &seed, &proof);
        assert!(target.ct_only.is_empty(), "§5.3: the target is (G, ∅, β′)");
        assert_eq!(target.norm_bound_sq, setup.params.bounds.beta_prime_sq);
        let next = next_level_setup(&setup, &target, &level_seed(&seed, proof.reroll))
            .expect("the level instantiates here");
        let r1 = target.multiplicity;
        let tri1 = (r1 * r1 + r1) / 2;
        assert_eq!(next.params.inner_key.rows(), setup.params.inner_key.rows());
        assert_eq!(next.params.inner_key.cols(), target.rank, "A′ is κ×n′");
        assert_eq!(next.params.key_b.rows(), setup.params.key_b.rows());
        assert_eq!(
            next.params.key_b.cols(),
            r1 * next.params.decomp1.digits * next.params.inner_key.rows(),
            "B′ covers r′·t₁′·κ′ planes"
        );
        assert_eq!(next.params.key_c.cols(), next.params.decomp2.digits * tri1);
        assert_eq!(next.params.key_d.cols(), next.params.decomp1.digits * tri1);
        assert_eq!(next.space, setup.space, "the same challenge space C, §2");
        assert!(
            NormBounds::slack_condition(target.norm_bound_sq, QL::MODULUS),
            "the gate below is the one that bounds this"
        );

        // Refusal 1, alone: a target whose β′ breaks Theorem 5.1's precondition
        // cannot be projected soundly, so no CRS makes the level correct. The
        // boundary is exact — one unit of *squared* norm either side of it is the
        // difference between a level that exists and `SlackCondition` — and this
        // is the gate that decides whether LaBRADOR's recursion is instantiable at
        // all for a level whose budget is β′.
        let ceiling = 30 * u128::from(QL::MODULUS) * u128::from(QL::MODULUS) / (128 * 125 * 125);
        let mut at_limit = target.clone();
        at_limit.norm_bound_sq = ceiling;
        let mut too_long = target.clone();
        too_long.norm_bound_sq = ceiling + 1;
        assert!(NormBounds::slack_condition(ceiling, QL::MODULUS));
        assert!(!NormBounds::slack_condition(ceiling + 1, QL::MODULUS));
        assert!(target.norm_bound_sq <= ceiling, "and the real target is inside it: {} > {}", target.norm_bound_sq, ceiling);
        assert!(next_level_setup(&setup, &at_limit, &seed).is_ok());
        assert_eq!(
            next_level_setup(&setup, &too_long, &seed).err(),
            Some(CoreError::SlackCondition),
            "one unit past Theorem 5.1's window must refuse, alone"
        );
        // Refusal 2: an empty relation is not an instance of R at all.
        let empty = Relation {
            rank: 0,
            ..target.clone()
        };
        assert_eq!(
            next_level_setup(&setup, &empty, &seed).err(),
            Some(CoreError::WrongShape { got: 0, expected: 1 })
        );
        // level_seed is the deterministic replay both sides need.
        assert_ne!(level_seed(&seed, 0), level_seed(&seed, 1));
        assert_eq!(level_seed(&seed, 2), level_seed(&seed, 2));
    }

    #[test]
    fn recursion_msis_bound_grows_by_128_over_30_per_level() {
        // Remark 5.2: every level whose norm is only *proved* (never checked)
        // scales the Module-SIS hardness bound by 128/30 in squared norm.
        let beta_sq = u128::from(QL::MODULUS);
        let setup = mini_setup(beta_sq).0;
        let bounds = setup.params.bounds;
        let t = ChallengeSpace::PAPER.operator_norm;
        let base = bounds.msis_norm_sq(beta_sq, t);
        assert_eq!(recursion_msis_norm_sq(&bounds, beta_sq, t, 0), base);
        let one = recursion_msis_norm_sq(&bounds, beta_sq, t, 1);
        for i in 0..2 {
            assert_eq!(one[i], ceil_div(base[i] * 128, 30), "term {i}");
            assert!(one[i] > base[i], "the hardness bound must grow");
        }
        let two = recursion_msis_norm_sq(&bounds, beta_sq, t, 2);
        assert!(two[0] > one[0] && two[1] > one[1]);
        // A depth so large the bound is out of reach saturates rather than
        // wrapping to something a caller could mistake for a small norm.
        let huge = recursion_msis_norm_sq(&bounds, beta_sq, t, 400);
        assert!(huge[0] >= one[0] && huge[0] <= u128::MAX);
    }
}
