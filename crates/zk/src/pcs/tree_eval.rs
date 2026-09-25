//! The hypercube arithmetization the tree claims are stated over, plus the two
//! **norm-control reductions** of the Maltese folding cycle: the norm check
//! Π^PE_NC (Protocol 3) and the norm decomposition Π^Dec (Protocol 5).
//!
//! # Why this module exists
//!
//! [`crate::pcs::tree_commit`] gives the commitment and
//! [`crate::pcs::tree_fold`] gives succinctness, but neither is sound on its
//! own, because folding is what makes the *witness* grow:
//!
//! > "At every folding round, the norm of the witnesses grows from `b` to
//! > `b + T·b` where `T` is the expansion factor of the challenge space; if the
//! > norm grows too large, binding of the commitment is lost and the protocol
//! > becomes unsound." (§2.2)
//!
//! * **Π^Dec** (§5.3) resets the *forward* growth: it re-commits a high-norm
//!   concatenated opening `s` inside a fresh low-norm tree, by decomposing
//!   `s = Σ_{j∈[h]} b^{j−1}·s_{dec,j}` (Def. 1) and proving the tree's linear
//!   constraints against the *new* commitment through the batched claims
//!   `v_A`, `v_G` of Eq. (25)–(29).
//! * **Π^PE_NC** (§5.1) resets the *extraction* growth: it proves every field
//!   coefficient of `s` has `‖·‖∞ < b` by the zero-check of Eq. (8) with the
//!   norm polynomial `N_b` of Eq. (7), and consolidates the `d` claims the
//!   sum-check leaves behind into one ring claim by **Lemma 14**.
//!
//! # The layer layout every indexing lemma rests on
//!
//! A tree evaluation claim is on the *concatenated* opening
//!
//! ```text
//! s := 0^{2nα} ‖ s_1 ‖ … ‖ s_ℓ  ∈ R_F^{2^{ℓ+1}nα}
//! ```
//!
//! so layer `i` occupies `[(2^i)nα, (2^{i+1})nα)` and an index's leading bits
//! (MSB-first) select the tree slot. That is the fact Eq. (12) pulls the
//! `êq(0^{ℓ−k}, u)` factor out of, and the reason Eq. (25)'s two sides share
//! their exponent ranges: `ξ^{2^i+p−1}` is simultaneously a gadget-side *node*
//! index of layer `i` and an `A`-side *block* index of layer `i+1`.
//! [`layer_range`] is the one definition of the layout, shared with
//! [`crate::pcs::tree_fold`].
//!
//! # The two relations, verbatim (§5 "Relations", p. 25)
//!
//! With `m := log(nα)`:
//!
//! ```text
//! PE(L, ℓ, b⃗): x := ((t_l ∈ R_F^n)_l∈[L], u ∈ R_F^{ℓ+m}, (v_l ∈ R_F)_l∈[L]),
//!              w := ((s_{i,l} ∈ R_F^{2ⁱnα})_i∈[], l∈[L]) :
//!                ∀l, Open(A, b_l, t_l, (s_{i,l})_i∈[ℓ]) = 1  and  s̃_{ℓ,l}(u) = v_l
//! TE(L, ℓ, b⃗): x := ((t_l)_l∈[L], u ∈ R_F^{ℓ+1+m}, (v_l)_l∈[L]),  same w :
//!                ∀l, Open(A, b_l, t_l, (s_{i,l})) = 1,
//!                s_l := 0^{2nα} ‖ s_{1,l} ‖ … ‖ s_{ℓ,l} ∈ R_F^{2^{ℓ+1}nα},
//!                s̃_l(u) = v_l
//! ```
//!
//! The two points differ by exactly one coordinate, and that is the whole
//! content of [`concatenated_point`]: the PE claim is on the *bottom layer*, the
//! TE claim is on the concatenation, and layer `ℓ` is the concatenation's second
//! half, so the TE point is `(1, u)`. Everything downstream (the `ℓ+1+m`-variable
//! norm-check sum-check, Eq. (12)'s split, Protocol 5's input point
//! `u ∈ R_F^{ℓ+1} × R_F^m`) is read off those two lines.
//!
//! # Protocol 3 — `Π^PE_NC : PE(L,ℓ,b⃗) → TE(L,ℓ,b⃗)` (§5.1, pp. 26–28)
//!
//! Transcribed literally, with `L = 1`:
//!
//! 1. `V` samples `ξ ←$ K`, `r ←$ K^{ℓ+1+m}`; `Q_N(X) := Σ_{l∈[L]} Σ_{k∈[0,d−1]}
//!    ξ^{(l−1)·d+k}·N_{b_l}(ĉf(s_l)_k(X))`; run the sum-check (Def. 9) to get
//!    `(r_N ∈ K^{ℓ+1+m}, y_N ∈ K) ← SC(0, ℓ+1+m, êq(X,r)·Q_N(X))`.
//! 2. `P` sends `a_l := s̃_l(r_N) ∈ R_K`, and `V` checks
//!    `y_N =? êq(r_N, r)·Σ_{l,k} ξ^{(l−1)d+k}·N_{b_l}(a_{l,k})` — this module's
//!    [`NormCheckProof::packed`] is that `a`. The equation is enforceable *as
//!    printed* only because Step 1(c)'s sum-check is [`crate::sumcheck::circuit`]'s
//!    degree-`2b` protocol, whose output claim is the circuit value `G(r_N)`; on a
//!    multilinear table sum-check it would read `0 =? N_b(â) ≠ 0` for every
//!    honest prover (see [`EvalError::PackedNormMismatch`]). Lemma 14 (p. 27) is
//!    what lets the `d` coefficient claims be read back as one ring claim, and
//!    [`packing_certificate`] checks it coefficient by coefficient.
//! 3. `ShiftSC` folds Eq. (9) `a_l = Σ_X êq(r_N,X)·s̃_l(X)` and Eq. (10)
//!    `v_l = Σ_X êq(X₁,1)·êq(u,X_{[2:]})·s̃_l(X)` into `r⃗' ∈ R_F^{ℓ+1+m}` and
//!    `(y₁,…,y_L)`. Step 3(b) *is* Eq. (10), which is why `norm_check_prove` and
//!    `norm_check_verify` take the PE split `(u, v)` alongside `(r, ξ)` and run
//!    [`layer_claim`] on it.
//! 4. Output `((t_l), r⃗', (y_l)), (s_{i,l})` — a `TE` statement.
//!
//! Eq. (7): `N_b(X) := X·Π_{j=1}^{b−1}((X−j)(X+j))`, degree `2b−1`
//! ([`norm_polynomial`]). Eq. (8) is the zero-check that [`norm_check_table`]
//! batches with `ξ`.
//!
//! # Protocol 5 — `Π^Dec : TE(1,ℓ,b^h) → PE(1, ℓ̃, b)` (§5.3, pp. 35–38)
//!
//! Parameters (p. 37): `ℓ` layers, input bound `b^h`, base `b`, `h` factors,
//! `m := log(nα)`, `ℓ̃ := ℓ+1+log h`. Input point is the *split*
//! `u ∈ R_F^{ℓ+1} × R_F^m` (the TE point). Eq. (21) is [`split_balanced`] plus
//! [`concat_planes`]; the fresh commitment is `Commit_A(s_dec)` — a tree of
//! height `ℓ̃`, because `s_dec` has `h·2^{ℓ+1}nα = 2^{ℓ̃}·nα` entries. The five
//! verifier-side facts [`decompose_verify`] checks are Eq. (25)
//! (`ξ·Σ_r η^{r−1}t(r) + v_G = v_A`, whose `ξ⁰` slot deliberately lands on the
//! `0^{2nα}` prefix — "we begin the powers of ξ with ξ¹ rather than ξ⁰ = 1
//! because we will be writing this in terms of the concatenated opening vector",
//! p. 35), Eq. (26)/(28) (`q_A`/`q_G` vs `q_{dec,A}`/`q_{dec,G}`), Eq. (30)
//! (`v = Σ_{j∈[h]} b^{j−1}·s̃_{dec,j}(u)`), and Eq. (31) (the zero prefix).
//! Step 3's output point is the **prefix** `r_{[:ℓ̃+m]}` of the `BatchSC` point,
//! which is why the caller supplies `r_new` rather than reusing an older point.
//!
//! # Compilation this instance leaves out
//!
//! The paper discharges these claims with `BatchSC`/`ShiftSC` (§4, Protocols
//! 1–2), which batch `a` claims over `R_F` into one sum-check over a degree-`e`
//! extension `K` using `R_F ≅ K^{d/e}` and `R_K ≅ R_F^e`. That needs an
//! extension field (which [`algebra`] exposes only outside its `Ring` trait) and
//! `X^d + 1` splitting into degree-`e` factors — false for `q ≡ 5 (mod 8)`, the
//! congruence this scheme family requires. So here `K = F` and:
//!
//! * the norm-check sum-check is genuinely run over `F` through
//!   [`crate::sumcheck::circuit`] — Def. 9's degree-`Δ` form, at `Δ = 2b` here —
//!   with Fiat–Shamir binding to the statement *and* to Step 1(a)'s `ξ, r`, and
//!   it pays `log₂ q` bits of soundness per batching challenge instead of
//!   `e·log₂ q`;
//! * what `BatchSC`/`ShiftSC` buy — `d/e` extension-field claims per `R_F` claim
//!   and `e` per `R_K` claim — is absent, so a claim is bound to `F`'s size
//!   rather than `K`'s. The *shape* of the reductions (Eq. (8)–(10), Step 2(b),
//!   Eq. (25)–(31)) is the paper's, read literally.
//! * Π^Dec's four claims are checked as the *verifier equations* they are
//!   (Eq. (25), (30), (31) plus the digit-shortness gate), not as rounds.
//!
//! [`algebra`]: algebra::ring

use crate::foundation::fs::{absorb_rings, seed_stream};
use crate::pcs::tree_commit::{coefficient_column, max_norm, TreeError, TreeKey, TreeOpening};
use crate::sumcheck::circuit::{
    self, CircuitError, CircuitSumcheckProof, Composition, LinePoly,
};
use algebra::crypto::sampling::{sample_uniform_coeff, BitStream};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::{CenteredRing, MatrixElement, Ring};
use algebra::ring::PolynomialQuotientRing;
use alloc::{string::ToString, vec, vec::Vec};
use core::fmt;

/// Why a claim in this module was rejected. Each variant names the equation it
/// corresponds to, so a tampered component identifies itself.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum EvalError {
    /// A point had a different coordinate count than the vector's variables.
    WrongVariableCount {
        /// Coordinates supplied.
        got: usize,
        /// Coordinates the vector needs.
        expected: usize,
    },
    /// A vector had the wrong length for its role.
    WrongLength {
        /// Length supplied.
        got: usize,
        /// Length required.
        expected: usize,
    },
    /// The Fiat–Shamir sum-check did not verify, or the point/evaluation it
    /// derived disagree with the ones carried in the proof.
    SumcheckRejected,
    /// Lemma 14 failed: `cf(ṽ(r))_k ≠ ĉf(v)_k(r)` for some coefficient `k`.
    PackingMismatch {
        /// The coefficient index that disagreed.
        coefficient: usize,
    },
    /// Protocol 3's norm content fails, in either of its two forms: Eq. (8)'s
    /// `ξ`-batched `N_b` does not vanish at some point of the openings'
    /// hypercube, or Step 2(b)'s
    /// `y_N ≠ êq(r_N, r)·Σ_k ξ^k·N_b(cf(a)_k)` at the sent `a`.
    ///
    /// Step 2(b) is enforceable *as printed* because this module runs the
    /// reduction's sum-check as Def. 9's degree-`2b` protocol, whose output
    /// claim is the circuit value `G(r_N)`. On the crate's multilinear
    /// table sum-check the honest `y_N` would instead be the extension of an
    /// identically-zero table — `0` — against a right-hand side that is not, so
    /// every honest prover would be rejected. See [`crate::sumcheck::circuit`].
    PackedNormMismatch,
    /// The round-message width declared for a reduction is smaller than its
    /// circuit's degree needs: `NC = Δ + 1` with `Δ = 2b` for Π^PE_NC (Eq. (7)
    /// gives `N_b` degree `2b − 1`, times the `êq` factor) and `Δ = 2` for
    /// Π^Fold's product of two multilinears (Eq. (15)).
    DegreeUnderstated {
        /// Degree the circuit reaches.
        degree: usize,
        /// Degree the declared width supports.
        declared: usize,
    },
    /// Eq. (10): the claimed layer value is not that layer's MLE at `u`.
    LayerClaimMismatch {
        /// Layer the claim was made about.
        level: usize,
    },
    /// Eq. (25): `ξ·⟨p_η,n, t⟩ + v_G ≠ v_A`, i.e. a tree constraint is violated.
    ConstraintBatchMismatch,
    /// Eq. (26)/(28): a digit-side inner product disagrees with the value-side
    /// one, so `s_dec` is not a decomposition of `s` (or a claim was forged).
    DecompositionSideMismatch,
    /// `Σ_j b^{j−1}·s_{dec,j}` differs from the concatenated opening `s`.
    DecompositionMismatch {
        /// First recomposed element that disagreed.
        at: usize,
    },
    /// Protocol 5 Step 1(a)'s *other* half (p. 35): the prover "commits to the
    /// concatenated decomposed openings vector `s_dec`", so `t*_dec` must be a
    /// commitment to **the planes this proof shows**, not merely some well-formed
    /// low-norm tree. Without it every equation of Π^Dec holds — Eq. (21)'s sum
    /// reads the planes against the *input* opening, Eq. (25)–(30) read the planes
    /// and the claims, and `Open` checks the new tree only against itself — while
    /// the tree the next cycle continues on is unrelated. Found by attack, 2026-09-24.
    DecomposedCommitmentMismatch {
        /// First leaf element that disagreed.
        at: usize,
    },
    /// Eq. (31): the concatenated opening does not start with `0^{2nα}`.
    PrefixNotZero {
        /// Index inside the prefix that is non-zero.
        at: usize,
    },
    /// `split_b` could not fit a coefficient into the requested digit count.
    DigitOverflow {
        /// Flattened coefficient index whose residual failed to vanish.
        at: usize,
    },
    /// A decomposition plane exceeded the gadget base: `‖s_{dec,j}‖∞ ≥ b`.
    PlaneNotShort {
        /// Plane index.
        plane: usize,
        /// Observed norm.
        got: u64,
        /// Bound `b`.
        bound: u64,
    },
    /// A tree commitment carried inside a reduction failed to open.
    Tree(TreeError),
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::WrongVariableCount { got, expected } => {
                write!(f, "point of {got} coordinates, vector needs {expected}")
            }
            EvalError::WrongLength { got, expected } => {
                write!(f, "vector of {got} elements, expected {expected}")
            }
            EvalError::SumcheckRejected => write!(f, "sum-check transcript rejected"),
            EvalError::PackingMismatch { coefficient } => write!(
                f,
                "Lemma 14 fails at coefficient {coefficient}: cf(ṽ(r)) ≠ ĉf(v)(r)"
            ),
            EvalError::PackedNormMismatch => {
                write!(
                    f,
                    "Protocol 3: Eq. (8)'s batched norm polynomial does not vanish over the openings' hypercube, or Step 2(b) fails at the sent a"
                )
            }
            EvalError::DegreeUnderstated { degree, declared } => write!(
                f,
                "the reduction's circuit reaches degree {degree} but the declared round width supports {declared}"
            ),
            EvalError::LayerClaimMismatch { level } => {
                write!(f, "layer {level} evaluation claim (Eq. 10) does not hold")
            }
            EvalError::ConstraintBatchMismatch => write!(
                f,
                "Eq. 25 fails: ξ·⟨p_η,n,t⟩ + v_G ≠ v_A, so a tree constraint is violated"
            ),
            EvalError::DecompositionSideMismatch => write!(
                f,
                "Eq. 26/28: a digit-side inner product differs from the value-side one"
            ),
            EvalError::DecompositionMismatch { at } => {
                write!(f, "Σ b^(j−1)·s_dec,j differs from s at element {at}")
            }
            EvalError::DecomposedCommitmentMismatch { at } => write!(
                f,
                "Prot. 5 Step 1(a): t*_dec is not a commitment to the planes shown (leaf {at})"
            ),
            EvalError::PrefixNotZero { at } => {
                write!(
                    f,
                    "the 0²ⁿᵃ prefix of the concatenated opening is non-zero at {at}"
                )
            }
            EvalError::DigitOverflow { at } => {
                write!(f, "coefficient {at} does not fit the requested digit count")
            }
            EvalError::PlaneNotShort { plane, got, bound } => write!(
                f,
                "decomposition plane {plane} has ‖·‖∞ = {got}, base demands < {bound}"
            ),
            EvalError::Tree(err) => write!(f, "inner tree commitment invalid: {err}"),
        }
    }
}

/// The bit representation `bits_η(x)` of §2.2.2: `η` bits, **most significant
/// first**, so the leading bits of an index are the tree-slot bits that
/// [`layer_range`] and Eq. (12)/Eq. (14) factor out.
pub fn bits_of(value: usize, width: usize) -> Vec<bool> {
    (0..width)
        .map(|i| (value >> (width - 1 - i)) & 1 == 1)
        .collect()
}

/// The `êq(r, ·)` table over the hypercube, built by doubling: entry `x` is
/// `Πᵢ ((1 − bits(x)ᵢ) + bits(x)ᵢ·rᵢ)`, MSB-first. Doubling costs `2·len`
/// products overall rather than `len·nv`, which is what makes these tables
/// usable with schoolbook arithmetic.
///
/// # Errors
/// [`EvalError::WrongVariableCount`] unless `2^{r.len()} == len`.
pub fn eq_field_table<R: Ring>(r: &[R], len: usize) -> Result<Vec<R>, EvalError> {
    if !len.is_power_of_two() || r.len() != len.trailing_zeros() as usize {
        return Err(EvalError::WrongVariableCount {
            got: r.len(),
            expected: len.trailing_zeros() as usize,
        });
    }
    let mut table = vec![R::ONE];
    for coordinate in r.iter() {
        let complement = R::ONE - *coordinate;
        let mut next = Vec::with_capacity(table.len() * 2);
        for value in table.iter() {
            next.push(*value * complement);
            next.push(*value * *coordinate);
        }
        table = next;
    }
    Ok(table)
}

/// The `êq(point, ·)` table over a **ring** point (`R_F^{nv}`).
///
/// # Errors
/// [`EvalError::WrongVariableCount`] unless `2^{point.len()} == len`.
pub fn eq_ring_table<R: Ring, const D: usize>(
    point: &[PolyRing<R, D>],
    len: usize,
) -> Result<Vec<PolyRing<R, D>>, EvalError> {
    if !len.is_power_of_two() || point.len() != len.trailing_zeros() as usize {
        return Err(EvalError::WrongVariableCount {
            got: point.len(),
            expected: len.trailing_zeros() as usize,
        });
    }
    let one = embed::<R, D>(R::ONE);
    let mut table = vec![one.clone()];
    for coordinate in point.iter() {
        let complement = one.clone() - coordinate.clone();
        let mut next = Vec::with_capacity(table.len() * 2);
        for value in table.iter() {
            next.push(value.clone() * complement.clone());
            next.push(value.clone() * coordinate.clone());
        }
        table = next;
    }
    Ok(table)
}

/// `c · x` for a field scalar `c` acting on a ring element — the action Lemma
/// 14's proof calls "multiplication corresponds to scaling all coefficients by
/// r̂ᵢ", a factor `D` cheaper than a ring product.
pub fn scale_by_scalar<R: Ring, const D: usize>(x: &PolyRing<R, D>, c: R) -> PolyRing<R, D> {
    PolyRing::from_coefficients(x.coefficients().into_iter().map(|k| k * c).collect())
}

/// Embeds a field element as the **constant polynomial** `c ∈ R_F ⊆ R_K`, i.e.
/// coefficient `0` is `c` and every other coefficient is `0`.
///
/// This is the `c ∈ K` of Lemma 14's proof, where the paper says "Equality (2)
/// holds because `r̂ᵢ ∈ K` is a *constant* in `R_K` and multiplication
/// corresponds to scaling all coefficients by `r̂ᵢ`" (§5.1.1, p. 27). It is the
/// same map as [`crate::pcs::tree_commit::scalar_into_ring`], and it must be a
/// constant: `R_F`'s multiplicative identity is `1·X⁰`, so any other reading of
/// "embed" turns [`eq_ring_table`]'s running product into something that is not
/// `êq`, breaks `Σ_X êq(u,X) = 1`, and silently desynchronises prover and
/// verifier of every ring-valued claim in this module.
pub fn embed<R: Ring, const D: usize>(c: R) -> PolyRing<R, D> {
    let mut coefficients = vec![R::ZERO; D];
    coefficients[0] = c;
    PolyRing::from_coefficients(coefficients)
}

/// The zero of `R_F`.
pub fn zero_ring<R: Ring, const D: usize>() -> PolyRing<R, D> {
    PolyRing::from_coefficients(vec![R::ZERO; D])
}

/// The multilinear extension of a ring vector at a **field** point:
/// `ṽ(r) = ⟨v, êq(bits(·), r)⟩` — Lemma 14's left side.
///
/// # Errors
/// [`EvalError::WrongVariableCount`] unless `2^{r.len()} == |v|`.
pub fn mle_at_field<R: Ring, const D: usize>(
    values: &[PolyRing<R, D>],
    r: &[R],
) -> Result<PolyRing<R, D>, EvalError> {
    let table = eq_field_table(r, values.len())?;
    let mut acc = zero_ring::<R, D>();
    for (weight, value) in table.iter().zip(values.iter()) {
        acc += scale_by_scalar(value, *weight);
    }
    Ok(acc)
}

/// The multilinear extension of a ring vector at a **ring** point — the shape
/// the TE/PE claims and every sum-check output take.
///
/// # Errors
/// [`EvalError::WrongVariableCount`] unless `2^{point.len()} == |values|`.
pub fn mle_at_ring<R: Ring, const D: usize>(
    values: &[PolyRing<R, D>],
    point: &[PolyRing<R, D>],
) -> Result<PolyRing<R, D>, EvalError> {
    let table = eq_ring_table(point, values.len())?;
    Ok(inner_product(&table, values))
}

/// `êq(point, ·)` tables for **one fixed point**, built at most once per length.
///
/// Π^Fold's verifier needs `s̃_j(r)` and `q̃_{subs,j}(r)` for *every* subtree
/// `j ∈ [0, 2^k)`, and the claim only type-checks when
/// `|s_j| = |q_j| = 2^{|r|}`, so the same table is needed `2^{k+1}` times. Each
/// build costs `2^{|r|+1}` ring products, which is `2^k` times more work than the
/// `O(ℓ² + ℓm)` the paper's §2.2.2 (p. 8) allows the verifier for
/// `q̃_{subs,j}(r)` — the reuse is what makes that count reachable. [`mle_at_ring`]
/// stays the one-shot entry point and this type is the same function on a shared
/// table, so a caller cannot drift from it.
pub struct EqTables<R: Ring, const D: usize> {
    point: Vec<PolyRing<R, D>>,
    built: Vec<(usize, Vec<PolyRing<R, D>>)>,
}

impl<R: Ring, const D: usize> EqTables<R, D> {
    /// Bind to `point`; the tables themselves are built lazily by [`Self::mle`].
    pub fn at(point: &[PolyRing<R, D>]) -> Self {
        Self {
            point: point.to_vec(),
            built: Vec::new(),
        }
    }

    /// The bound point — the `r` every cached table is over.
    pub fn point(&self) -> &[PolyRing<R, D>] {
        &self.point
    }

    /// `⟨values, êq(point, ·)⟩`, identical to
    /// `mle_at_ring(values, self.point())` but sharing one table per length.
    ///
    /// # Errors
    /// [`EvalError::WrongVariableCount`] exactly as [`eq_ring_table`] does.
    pub fn mle(&mut self, values: &[PolyRing<R, D>]) -> Result<PolyRing<R, D>, EvalError> {
        let len = values.len();
        let index = match self.built.iter().position(|(n, _)| *n == len) {
            Some(index) => index,
            None => {
                let table = eq_ring_table(&self.point, len)?;
                self.built.push((len, table));
                self.built.len() - 1
            }
        };
        Ok(inner_product(&self.built[index].1, values))
    }
}

/// `p_{η,2^ν} = (1, η, …, η^{2^ν−1})`, the powers vector of Eq. (13).
///
/// # Panics
/// If `len` is not a power of two.
pub fn powers_vector<R: Ring>(eta: R, len: usize) -> Vec<R> {
    assert!(
        len.is_power_of_two(),
        "powers vectors have power-of-two length"
    );
    let mut out = Vec::with_capacity(len);
    let mut acc = R::ONE;
    for _ in 0..len {
        out.push(acc);
        acc *= eta;
    }
    out
}

/// The efficiently computable multilinear extension of Eq. (13):
/// `êp_{η,2^ν}(Y) = Π_{i∈[ν]} ((1 − Yᵢ) + Yᵢ·η^{2^{ν−i}})`.
///
/// # Errors
/// [`EvalError::WrongVariableCount`] unless `2^{y.len()} == len`.
pub fn powers_mle<R: Ring>(eta: R, len: usize, y: &[R]) -> Result<R, EvalError> {
    if !len.is_power_of_two() || y.len() != len.trailing_zeros() as usize {
        return Err(EvalError::WrongVariableCount {
            got: y.len(),
            expected: len.trailing_zeros() as usize,
        });
    }
    let mut acc = R::ONE;
    for (i, yi) in y.iter().enumerate() {
        let power = eta.pow(1u64 << (y.len() - 1 - i) as u64);
        acc *= (R::ONE - *yi) + (*yi * power);
    }
    Ok(acc)
}

/// `⊗`: `out[i·|b| + j] = a[i]·b[j]`, the tensor product Eq. (25)–(28) use to
/// batch their weights.
pub fn tensor<R: Ring>(a: &[R], b: &[R]) -> Vec<R> {
    let mut out = Vec::with_capacity(a.len() * b.len());
    for x in a {
        for y in b {
            out.push(*x * *y);
        }
    }
    out
}

/// The ring-element tensor product of Eq. (26).
pub fn tensor_ring<R: Ring, const D: usize>(
    a: &[PolyRing<R, D>],
    b: &[PolyRing<R, D>],
) -> Vec<PolyRing<R, D>> {
    let mut out = Vec::with_capacity(a.len() * b.len());
    for x in a {
        for y in b {
            out.push(x.clone() * y.clone());
        }
    }
    out
}

/// `⟨a, b⟩ = Σ aᵢ·bᵢ` over the ring.
///
/// # Panics
/// If the lengths differ — a silently truncated inner product would pass
/// vacuously, which is worse than one that panics.
pub fn inner_product<R: Ring, const D: usize>(
    a: &[PolyRing<R, D>],
    b: &[PolyRing<R, D>],
) -> PolyRing<R, D> {
    assert_eq!(a.len(), b.len(), "inner products need equal lengths");
    let mut acc = zero_ring::<R, D>();
    for (x, y) in a.iter().zip(b.iter()) {
        acc += x.clone() * y.clone();
    }
    acc
}

/// `Σ cᵢ·zᵢ` with field weights `c` and ring values `z` — the shape Eq. (29)'s
/// inner product has, and `D×` cheaper per term than a ring product.
pub fn scalar_inner_product<R: Ring, const D: usize>(
    weights: &[R],
    values: &[PolyRing<R, D>],
) -> PolyRing<R, D> {
    assert_eq!(
        weights.len(),
        values.len(),
        "weights must match the values they batch"
    );
    let mut acc = zero_ring::<R, D>();
    for (weight, value) in weights.iter().zip(values.iter()) {
        acc += scale_by_scalar(value, *weight);
    }
    acc
}

/// Layer `level` (1-based, the paper's `s_level`) occupies
/// `[2^level·nα, 2^{level+1}·nα)` inside the concatenated opening `s`.
///
/// # Panics
/// If `level ≥ 32` (the shift would be meaningless).
pub fn layer_range(slot_len: usize, level: usize) -> core::ops::Range<usize> {
    assert!(
        level < 32,
        "tree height beyond 32 layers is not addressable"
    );
    let size = slot_len << level;
    size..size * 2
}

/// `s := 0^{2nα} ‖ s_1 ‖ … ‖ s_ℓ` (§5 "Relations"), the vector a TE claim is on.
pub fn concatenated<R: Ring, const D: usize>(
    slot_len: usize,
    layers: &[Vec<PolyRing<R, D>>],
) -> Vec<PolyRing<R, D>> {
    let zero = zero_ring::<R, D>();
    let mut out = Vec::with_capacity((2usize << layers.len()) * slot_len);
    out.resize(2 * slot_len, zero);
    for layer in layers {
        out.extend_from_slice(layer);
    }
    out
}

/// The slice of the concatenated vector holding layer `level`.
///
/// # Errors
/// [`EvalError::WrongLength`] if the concatenated vector is too short.
pub fn layer_of<'s, R: Ring, const D: usize>(
    s: &'s [PolyRing<R, D>],
    slot_len: usize,
    level: usize,
) -> Result<&'s [PolyRing<R, D>], EvalError> {
    let range = layer_range(slot_len, level);
    if s.len() < range.end {
        return Err(EvalError::WrongLength {
            got: s.len(),
            expected: range.end,
        });
    }
    Ok(&s[range])
}

/// The norm polynomial `N_b(X) = X · Π_{j=1}^{b−1}((X − j)(X + j))` of Eq. (7),
/// of degree `2b − 1`.
///
/// Over a field its roots are exactly `{0, ±1, …, ±(b−1)}`, so the zero-check of
/// Eq. (8) certifies `‖·‖∞ < b` — see [`norm_polynomial_wraps`] for when that
/// stops being true.
pub fn norm_polynomial<R: Ring>(bound: u64, x: R) -> R {
    let mut acc = x;
    for j in 1..bound {
        let j = R::from(j);
        acc *= (x - j) * (x + j);
    }
    acc
}

/// `2b > q`: above this a value could reduce into `N_b`'s root set and the
/// zero-check would certify nothing.
pub const fn norm_polynomial_wraps(bound: u64, modulus: u64) -> bool {
    2 * bound > modulus
}

/// Def. 3's `cf(z)_k` for a **single** ring element, read over all of `[0, d)`.
///
/// `PolyRing::coefficients()` trims trailing zeros, so `cf`'s high columns are
/// *absent* rather than zero; indexing the trimmed vector panics on exactly the
/// low-norm witnesses this scheme is full of.
/// [`crate::pcs::tree_commit::coefficient_column`] is the same fix column-wise.
pub fn coefficient_at<R: Ring, const D: usize>(z: &PolyRing<R, D>, k: usize) -> R {
    debug_assert!(k < D, "coefficient index beyond the ring degree");
    z.coefficients().into_iter().nth(k).unwrap_or(R::ZERO)
}

/// The `ξ`-batched norm-check polynomial `Q_N` of Protocol 3 Step 1(b) for
/// `L = 1` commitment (the PCS case),
///
/// ```text
/// Q_N(X) = Σ_{k∈[0,d−1]} ξ^k · N_b( ĉf(s)_k (X) ),
/// ```
///
/// returned as the table of `Q_N` and of `êq(X, r)·Q_N(X)`, whose hypercube sum
/// the sum-check of Step 1(c) claims is `0` (Lem. 4).
///
/// # Errors
/// [`EvalError::WrongVariableCount`] if `r.len()` is not `log₂|s|`.
pub fn norm_check_table<R, const D: usize>(
    s: &[PolyRing<R, D>],
    r: &[R],
    xi: R,
    bound: u64,
) -> Result<(Vec<R>, Vec<R>), EvalError>
where
    R: Ring + CenteredRing,
{
    let (weights, columns) = norm_check_oracles(s, r)?;
    Ok(norm_check_batched(&weights, &columns, xi, bound))
}

/// The `ξ`-batching of Eq. (8) given the oracles of [`norm_check_oracles`],
/// returning `(Q_N(x))_x` and the sum-check's summand `(êq(x,r)·Q_N(x))_x`.
///
/// Split out so a caller that already holds the oracles does not rebuild them:
/// `norm_check_report` needs `Q_N` pointwise *and* the prover needs the weighted
/// table, and batching from the same two vectors is what keeps those the same
/// polynomial.
pub fn norm_check_batched<R: Ring>(
    weights: &[R],
    columns: &[Vec<R>],
    xi: R,
    bound: u64,
) -> (Vec<R>, Vec<R>) {
    let mut q = vec![R::ZERO; weights.len()];
    let mut xi_power = R::ONE;
    for column in columns {
        for (point, value) in q.iter_mut().zip(column.iter()) {
            *point += xi_power * norm_polynomial(bound, *value);
        }
        xi_power *= xi;
    }
    let table = q.iter().zip(weights.iter()).map(|(a, b)| *a * *b).collect();
    (q, table)
}

/// The `d + 1` multilinear oracles Protocol 3 Step 1(b) sums over, in the
/// order [`NormCheckCircuit`] expects: the `êq(X, r)` table, then the
/// coefficient columns `ĉf(s)_k` of Def. 3 for `k ∈ [0, d)`.
///
/// # Errors
/// [`EvalError::WrongVariableCount`] if `r` does not index `s`'s hypercube.
pub fn norm_check_oracles<R, const D: usize>(
    s: &[PolyRing<R, D>],
    r: &[R],
) -> Result<(Vec<R>, Vec<Vec<R>>), EvalError>
where
    R: Ring,
{
    let weights = eq_field_table(r, s.len())?;
    let columns = (0..D)
        .map(|k| coefficient_column(s, k))
        .collect::<Vec<_>>();
    Ok((weights, columns))
}

/// The Step 1(b) circuit `Q_N` batched by `êq`:
///
/// ```text
/// G(X) = êq(X, r) · Σ_{k∈[0,d−1]} ξ^k · N_b( ĉf(s)_k(X) )
/// ```
///
/// with `N_b` of Eq. (7). Its per-variable degree is `1 + (2b − 1) = 2b`, so a
/// round message carries `2b + 1` coefficients — which is why this reduction
/// cannot run on [`crate::sumcheck`]'s multilinear table sum-check at all (see
/// [`crate::sumcheck::circuit`]).
pub struct NormCheckCircuit<R: Ring, const NC: usize> {
    /// `ξ^k` for `k ∈ [0, d)`: the batching weights of Step 1(b) at `L = 1`.
    powers: Vec<R>,
    /// The norm bound `b`, so `N_b` has degree `2b − 1`.
    bound: u64,
}

impl<R: Ring, const NC: usize> NormCheckCircuit<R, NC> {
    /// The circuit of Eq. (8)'s `ξ`-batching over `d` coefficient oracles.
    pub fn new(xi: R, bound: u64, d: usize) -> Self {
        let mut powers = Vec::with_capacity(d);
        let mut acc = R::ONE;
        for _ in 0..d {
            powers.push(acc);
            acc *= xi;
        }
        Self { powers, bound }
    }
}

impl<R, const NC: usize> Composition<R, NC> for NormCheckCircuit<R, NC>
where
    R: Ring + MatrixElement,
{
    fn compose(
        &mut self,
        lines: &[LinePoly<R, NC>],
        acc: &mut LinePoly<R, NC>,
    ) -> Result<(), CircuitError> {
        if lines.len() != self.powers.len() + 1 {
            return Err(CircuitError::WrongLength {
                got: lines.len(),
                expected: self.powers.len() + 1,
            });
        }
        let mut batched = LinePoly::<R, NC>::zero();
        for (power, line) in self.powers.iter().zip(lines[1..].iter()) {
            // Eq. (7): N_b(X) = X · Π_{j=1}^{b−1} ((X − j)(X + j)).
            let mut norm = line.clone();
            for j in 1..self.bound {
                let up = R::from(j);
                let down = R::ZERO - up;
                norm = norm.mul(&line.offset(down))?.mul(&line.offset(up))?;
            }
            batched.add_assign(&norm.scaled(power));
        }
        acc.add_assign(&lines[0].mul(&batched)?);
        Ok(())
    }
}

/// A completed norm-check reduction (Protocol 3 Steps 1–2): the Def. 9 sum-check
/// transcript with the point and evaluation it reduces to, and the packed ring
/// claim `a = s̃(r_N)` of Step 2(a).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NormCheckProof<R: Ring + MatrixElement, const D: usize, const NV: usize, const NC: usize>
{
    /// `SC(0, ℓ+1+m, êq(X,r)·Q_N(X))` (Step 1(c)), whose output claim is
    /// `y_N = G(r_N)`. `sumcheck.point` is `r_N`, `sumcheck.final_eval` is `y_N`.
    pub sumcheck: CircuitSumcheckProof<R, NV, NC>,
    /// `a := s̃(r_N) ∈ R_F` (Step 2(a)).
    pub packed: PolyRing<R, D>,
}

/// Domain label shared by the norm-check prover and verifier.
pub const NORM_CHECK_DOMAIN: &[u8] = b"lattice-algebra/Z7/tree-norm-check";

/// Encodes Protocol 3 Step 1(a)'s verifier messages (`ξ` and `r`) into one
/// byte string, so the sum-check transcript is bound to them.
///
/// This is not decoration: `r` *is* the `Z` of Lemma 4's zero-check, and a
/// transcript that omits it lets a prover replay a proof built under one `r`
/// against a verifier holding another.
fn step_one_messages<R: MatrixElement>(xi: R, r: &[R]) -> Vec<u8> {
    let mut transcript = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/tree-norm-messages");
    let mut encoded = Vec::new();
    let mut values = vec![xi];
    values.extend_from_slice(r);
    for value in values {
        let text = value.to_string();
        encoded.extend_from_slice(&(text.len() as u64).to_le_bytes());
        encoded.extend_from_slice(text.as_bytes());
    }
    transcript.absorb(b"xi,r", &encoded);
    transcript.challenge_bytes(32)
}

/// The statement material plus Protocol 3 Step 1(a)'s `ξ` and `r`, which the
/// sum-check transcript must bind.
fn norm_check_bound<R: MatrixElement>(binding: &[u8], xi: R, r: &[R]) -> Vec<u8> {
    let mut out = binding.to_vec();
    out.extend_from_slice(&step_one_messages(xi, r));
    out
}

/// The `ℓ` of a concatenated opening `s ∈ R_F^{2^{ℓ+1}nα}`, i.e. the height of
/// the tree `s` came from. [`concatenated_point`] and every claim gate in this
/// module read the layout through it.
///
/// # Errors
/// [`EvalError::WrongLength`] if `s` is not `2^{ℓ+1}·slot_len` long, or
/// `slot_len` is not a power of two (`m = log(nα)` must exist).
pub fn concatenation_height<R: Ring, const D: usize>(
    s: &[PolyRing<R, D>],
    slot_len: usize,
) -> Result<usize, EvalError> {
    if slot_len == 0 || !slot_len.is_power_of_two() {
        return Err(EvalError::WrongLength {
            got: slot_len,
            expected: slot_len.next_power_of_two(),
        });
    }
    if s.len() % (2 * slot_len) != 0 {
        return Err(EvalError::WrongLength {
            got: s.len(),
            expected: (s.len() / (2 * slot_len)) * 2 * slot_len,
        });
    }
    let blocks = s.len() / (2 * slot_len);
    if !blocks.is_power_of_two() {
        return Err(EvalError::WrongLength {
            got: s.len(),
            expected: 2 * slot_len * blocks.next_power_of_two(),
        });
    }
    Ok(blocks.trailing_zeros() as usize)
}

/// **Every** check Protocol 3 leaves on the verifier's side, evaluated in
/// protocol order rather than up to the first failure. An empty vector is an
/// accepted proof.
///
/// In order:
/// 1. the shape of the concatenated opening and of the `êq(·, r)` table
///    (`ℓ+1+m` variables, Eq. (8));
/// 2. Eq. (10) — the input `PE` claim `s̃_ℓ(u) = v`, which Step 3(b) batches
///    alongside the norm claims;
/// 3. Step 1(c) — `SC(0, ℓ+1+m, êq(X,r)·Q_N(X))`, the degree-`2b` sum-check of
///    Def. 9, bound to the statement *and* to Step 1(a)'s `ξ, r`;
/// 4. Eq. (8) — the `ξ`-batched norm polynomial of the openings actually handed
///    over vanishes at **every** cube point (Lemma 4's right-hand side, which is
///    decidable here because this compilation gives the verifier the witness);
/// 5. Step 2(b) — `y_N =? êq(r_N, r)·Σ_{k} ξ^k·N_b(cf(a)_k)`, the equation that
///    ties the sum-check's output claim to the sent `a`;
/// 6. Lemma 14 — `cf(s̃(r_N))_k = ĉf(s)_k(r_N)` for each `k`, which is what makes
///    reading `a` as *one* ring claim (rather than `d` field claims) legitimate.
///
/// A failure in one does not hide another, which is the point: under
/// Fiat–Shamir a single edited message re-derives every later challenge, so a
/// one-error API reports whichever check happens to run first and cannot show
/// that the others are live.
#[allow(clippy::too_many_arguments)]
pub fn norm_check_report<R, const D: usize, const NV: usize, const NC: usize>(
    proof: &NormCheckProof<R, D, NV, NC>,
    s: &[PolyRing<R, D>],
    r: &[R],
    xi: R,
    bound: u64,
    binding: &[u8],
    slot_len: usize,
    u: &[PolyRing<R, D>],
    v: &PolyRing<R, D>,
) -> Vec<EvalError>
where
    R: Ring + CenteredRing + MatrixElement,
{
    let mut bad: Vec<EvalError> = Vec::new();
    let mut push = |error: EvalError| {
        if !bad.contains(&error) {
            bad.push(error);
        }
    };
    // 1. shapes.
    let height = match concatenation_height(s, slot_len) {
        Ok(height) => Some(height),
        Err(error) => {
            push(error);
            None
        }
    };
    let oracles = norm_check_oracles(s, r);
    if let Err(error) = &oracles {
        push(*error);
    }
    // 2. Eq. (10).
    if let Some(height) = height {
        if let Err(error) = layer_claim(s, slot_len, height, u, v) {
            push(error);
        }
    }
    // 3. Step 1(c): the degree-`2b` sum-check of the zero claim.
    let derived = circuit::verify::<R, NV, NC>(
        &proof.sumcheck,
        &R::ZERO,
        NORM_CHECK_DOMAIN,
        &norm_check_bound(binding, xi, r),
    );
    if let Err(error) = derived {
        push(match error {
            CircuitError::WrongLength { got, expected } => EvalError::WrongLength { got, expected },
            CircuitError::DegreeOverflow { degree, declared } => {
                EvalError::DegreeUnderstated { degree, declared }
            }
            other => {
                debug_assert!(matches!(
                    other,
                    CircuitError::ClaimMismatch
                        | CircuitError::WrongRounds { .. }
                        | CircuitError::RoundRejected { .. }
                        | CircuitError::FinalMismatch
                ));
                EvalError::SumcheckRejected
            }
        });
    }
    let r_n = proof.sumcheck.point.clone();
    // 4. Eq. (8) over the witness the reduction was handed.
    if let Ok((_, q)) = norm_check_table(s, r, xi, bound) {
        if q.iter().any(|value| *value != R::ZERO) {
            push(EvalError::PackedNormMismatch);
        }
    }
    // 5. Step 2(b), read literally: Def. 9's output claim *is* `G(r_N)`.
    match eq_of_field_points(&r_n, r) {
        Ok(peak) => {
            let mut batched = R::ZERO;
            let mut power = R::ONE;
            for k in 0..D {
                batched += power * norm_polynomial(bound, coefficient_at(&proof.packed, k));
                power *= xi;
            }
            if proof.sumcheck.final_eval != peak * batched {
                push(EvalError::PackedNormMismatch);
            }
        }
        Err(error) => push(error),
    }
    // 6. Lemma 14.
    if let Err(error) = packing_certificate(s, &r_n, &proof.packed) {
        push(error);
    }
    bad
}

/// Π^PE_NC verifier (Protocol 3 Steps 1(c) + 2(b) + 3(b)): [`norm_check_report`]
/// followed by "take the first", which is all a verifier needs.
///
/// # Errors
/// The first entry of [`norm_check_report`]; see it for the full list.
#[allow(clippy::too_many_arguments)]
pub fn norm_check_verify<R, const D: usize, const NV: usize, const NC: usize>(
    proof: &NormCheckProof<R, D, NV, NC>,
    s: &[PolyRing<R, D>],
    r: &[R],
    xi: R,
    bound: u64,
    binding: &[u8],
    slot_len: usize,
    u: &[PolyRing<R, D>],
    v: &PolyRing<R, D>,
) -> Result<(), EvalError>
where
    R: Ring + CenteredRing + MatrixElement,
{
    norm_check_report(proof, s, r, xi, bound, binding, slot_len, u, v)
        .into_iter()
        .next()
        .map_or(Ok(()), Err)
}

/// Π^PE_NC prover (Protocol 3 Steps 1–2): run Eq. (8)'s zero-check as Def. 9's
/// degree-`2b` sum-check, then pack its `d` output claims into one ring claim
/// through Lemma 14.
///
/// `r` is the verifier's hypercube point and `xi` its batching challenge (both
/// from [`challenges`], so the sides cannot drift); `binding` is the statement
/// material absorbed into the transcript (see [`statement_bytes`]). `NC` is the
/// round-message width and must be `2·bound + 1`, i.e. `Δ + 1` for `Δ = 2b`.
///
/// The prover runs [`norm_check_report`] on its own output before returning it:
/// a reduction that ships a proof its verifier would refuse is a bug in this
/// module, not a case for the caller to discover.
///
/// # Errors
/// Whatever [`norm_check_report`] reports for the proof just built —
/// [`EvalError::PackedNormMismatch`] when the openings are not `bound`-short
/// (Eq. (8) is then false and no honest proof exists),
/// [`EvalError::DegreeUnderstated`] when `NC` is too small for `bound`,
/// [`EvalError::WrongVariableCount`] / [`EvalError::WrongLength`] on a shape
/// mismatch, [`EvalError::LayerClaimMismatch`] on a false Eq. (10).
#[allow(clippy::too_many_arguments)]
pub fn norm_check_prove<R, const D: usize, const NV: usize, const NC: usize>(
    s: &[PolyRing<R, D>],
    r: &[R],
    xi: R,
    bound: u64,
    binding: &[u8],
    slot_len: usize,
    u: &[PolyRing<R, D>],
    v: &PolyRing<R, D>,
) -> Result<NormCheckProof<R, D, NV, NC>, EvalError>
where
    R: Ring + CenteredRing + MatrixElement,
{
    let height = concatenation_height(s, slot_len)?;
    layer_claim(s, slot_len, height, u, v)?;
    let degree = 2 * bound as usize + 1;
    if NC != degree {
        return Err(EvalError::DegreeUnderstated {
            degree: degree - 1,
            declared: NC - 1,
        });
    }
    let (weights, columns) = norm_check_oracles(s, r)?;
    // The prover refuses to run a sum-check whose claim it cannot honour: Eq. (8)
    // holds only when every opening really is `bound`-short.
    let (q, _) = norm_check_table(s, r, xi, bound)?;
    if q.iter().any(|value| *value != R::ZERO) {
        return Err(EvalError::PackedNormMismatch);
    }
    let mut tables: Vec<&[R]> = Vec::with_capacity(D + 1);
    tables.push(&weights);
    tables.extend(columns.iter().map(|column| column.as_slice()));
    let mut circuit = NormCheckCircuit::<R, NC>::new(xi, bound, D);
    let sumcheck = circuit::prove::<R, NV, NC, _>(
        &tables,
        &R::ZERO,
        NORM_CHECK_DOMAIN,
        &norm_check_bound(binding, xi, r),
        &mut circuit,
    )
    .map_err(|error| match error {
        CircuitError::WrongLength { got, expected } => EvalError::WrongLength { got, expected },
        CircuitError::DegreeOverflow { degree, declared } => {
            EvalError::DegreeUnderstated { degree, declared }
        }
        CircuitError::ClaimMismatch => EvalError::PackedNormMismatch,
        CircuitError::WrongRounds { .. }
        | CircuitError::RoundRejected { .. }
        | CircuitError::FinalMismatch => EvalError::SumcheckRejected,
    })?;
    let packed = mle_at_field(s, &sumcheck.point)?;
    let proof = NormCheckProof { sumcheck, packed };
    if let Some(error) =
        norm_check_report(&proof, s, r, xi, bound, binding, slot_len, u, v).into_iter().next()
    {
        return Err(error);
    }
    Ok(proof)
}

/// `êq(r, r')` between two field points of equal length.
///
/// # Errors
/// [`EvalError::WrongLength`] if the points differ in length.
pub fn eq_of_field_points<R: Ring>(r: &[R], other: &[R]) -> Result<R, EvalError> {
    if r.len() != other.len() {
        return Err(EvalError::WrongLength {
            got: other.len(),
            expected: r.len(),
        });
    }
    let mut acc = R::ONE;
    for (a, b) in r.iter().zip(other.iter()) {
        acc *= (*a * *b) + ((R::ONE - *a) * (R::ONE - *b));
    }
    Ok(acc)
}

/// `êq(bits, point) = Πᵢ (bits[i] ? pointᵢ : 1 − pointᵢ)` for an explicit bit
/// string — the shape of Eq. (14)'s `e_{i,j}` and Eq. (12)'s
/// `êq(0^{ℓ−k}, u_{(:ℓ−k)})`.
///
/// # Errors
/// [`EvalError::WrongLength`] if the bit string is longer than the point.
pub fn eq_of_bits_point<R: Ring, const D: usize>(
    bits: &[bool],
    point: &[PolyRing<R, D>],
) -> Result<PolyRing<R, D>, EvalError> {
    if bits.len() > point.len() {
        return Err(EvalError::WrongLength {
            got: bits.len(),
            expected: point.len(),
        });
    }
    let one = embed::<R, D>(R::ONE);
    let mut acc = one.clone();
    for (bit, coordinate) in bits.iter().zip(point.iter()) {
        acc *= if *bit {
            coordinate.clone()
        } else {
            one.clone() - coordinate.clone()
        };
    }
    Ok(acc)
}

/// The bridge from a `PE(1, ℓ, b)` claim to the `TE(1, ℓ, b)` claim Π^Fold
/// consumes (§5 "Relations").
///
/// The leaf layer `s_ℓ` occupies slots `[2^ℓ, 2^{ℓ+1})` of the concatenated
/// vector, i.e. exactly the indices whose most significant slot bit is `1`, so
/// `s̃_ℓ(u) = s̃(1 ‖ u)` — which is Eq. (10)'s `êq(X₁,1)` selector written as a
/// point. The returned point has one more coordinate than `u`.
pub fn pe_to_te_point<R: Ring, const D: usize>(u: &[PolyRing<R, D>]) -> Vec<PolyRing<R, D>> {
    let mut out = Vec::with_capacity(u.len() + 1);
    out.push(embed::<R, D>(R::ONE));
    out.extend_from_slice(u);
    out
}

/// The same bridge, **checked against the concatenated vector it is being
/// pointed at**: `u` is a `PE(1, ℓ, b)` point and `s` must be that tree's
/// `s := 0^{2nα} ‖ s_1 ‖ … ‖ s_ℓ`, and the returned point is the
/// `TE(1, ℓ, b)` point `s̃` is evaluated at.
///
/// # Why the selector is a prepended `1` and nothing else
///
/// §5 "Relations" (p. 25) defines the two relations' points at different
/// lengths — `PE`'s `u ∈ R_F^{ℓ+m}` (the claim is on the bottom layer `s_ℓ`
/// alone) and `TE`'s `u ∈ R_F^{ℓ+1+m}` (the claim is on `s`, twice as long). The
/// bridge is not a free choice, because `s`'s *layout* fixes which index bits
/// select layer `ℓ`: the zero prefix is `2nα` long and layer `i` is
/// `2ⁱ·nα` long, so layer `ℓ` starts at
///
/// ```text
/// 2nα + Σ_{i∈[ℓ−1]} 2ⁱ·nα = 2nα + (2^ℓ − 2)nα = 2^ℓ·nα
/// ```
///
/// which is exactly the midpoint of the `2^{ℓ+1}nα`-element `s`. Layer `ℓ` is
/// therefore "the second half", i.e. the indices whose *most significant*
/// (first) coordinate is `1` — and Protocol 3 writes precisely that as Eq. (10)
/// (p. 27), `v_l = Σ_{X∈{0,1}^{ℓ+1+m}} êq(X₁,1)·êq(u, X_{[2:]})·s̃_l(X)`, whose
/// own gloss is "*the first input bit X₁ = 1 selects for s_{ℓ,l}, as s_{ℓ,l}*
/// *makes up the second half of s_l*". Reading `X_{[2:]}` as `êq(u, ·)` is the
/// point `(1, u)`.
///
/// The alternatives are each wrong in a way this signature makes impossible:
/// *appending* the `1` would pin the last (within-slot) bit and select the odd
/// coordinates of *every* layer; *prepending a `0`* would bind the claim to
/// `s_top`, the vector Protocol 4 Eq. (12) factors out; and "aligning the two
/// point vectors by `slot_len` and concatenating" has no referent at all,
/// because a point's coordinates are one per *index bit*, not one per slot —
/// `slot_len` enters here only as the divisor that recovers `ℓ` from `|s|`.
///
/// # Errors
/// [`EvalError::WrongLength`] if `s` is not `2^{ℓ+1}·slot_len` long (so it is
/// not a concatenated opening), or if `u` does not have exactly `ℓ+m`
/// coordinates for that `s`.
pub fn concatenated_point<R: Ring, const D: usize>(
    u: &[PolyRing<R, D>],
    s: &[PolyRing<R, D>],
    slot_len: usize,
) -> Result<Vec<PolyRing<R, D>>, EvalError> {
    let height = concatenation_height(s, slot_len)?;
    let m = slot_len.trailing_zeros() as usize;
    let want = height + m;
    if u.len() != want {
        return Err(EvalError::WrongVariableCount {
            got: u.len(),
            expected: want,
        });
    }
    let point = pe_to_te_point(u);
    debug_assert_eq!(point.len(), height + 1 + m, "the TE point is one bit longer");
    Ok(point)
}

/// Squeezes `count` uniform **ring** elements from a Fiat–Shamir transcript
/// bound to `binding`.
///
/// [`challenges`] does the field-element half of this job; the reductions here
/// also need points in `R_F^{ℓ+1+m}` — Protocol 3's `u`, Protocol 4's output
/// point `r ∈ R_F^{ℓ−k+1+m}`, Protocol 5's `r_{[:ℓ̃+m]}` — and those must be
/// drawn *after* the prover's messages are absorbed, exactly like the field
/// challenges, or a prover could pick its own evaluation point. Built from the
/// same [`crate::foundation::sampling::uniform_vec_from_seed`] the rest of the
/// crate uses, so the two sides stay bit-identical.
pub fn ring_challenges<R: Ring, const D: usize>(
    domain: &[u8],
    binding: &[u8],
    count: usize,
) -> Vec<PolyRing<R, D>> {
    let mut tr = Transcript::<Shake256Xof>::new(domain);
    tr.absorb(b"binding", binding);
    let seed = tr.challenge_bytes(32);
    crate::foundation::sampling::uniform_vec_from_seed::<R, D>(domain, &seed, count)
}

/// Lemma 14: `cf(ṽ(r))_k = ĉf(v)_k(r)` for every `k ∈ [0, d)`.
///
/// The only place where the `d` field claims a sum-check leaves behind are
/// *identified* with the single ring claim the folding consumes, so it is checked
/// coefficient by coefficient: a wrong bit order or a transposed coefficient map
/// fails immediately.
///
/// # Errors
/// [`EvalError::PackingMismatch`] naming the first disagreeing coefficient.
pub fn packing_certificate<R: Ring, const D: usize>(
    v: &[PolyRing<R, D>],
    r: &[R],
    packed: &PolyRing<R, D>,
) -> Result<(), EvalError> {
    let table = eq_field_table(r, v.len())?;
    for k in 0..D {
        let column = coefficient_column(v, k);
        let mut acc = R::ZERO;
        for (weight, value) in table.iter().zip(column.iter()) {
            acc += *weight * *value;
        }
        if acc != coefficient_at(packed, k) {
            return Err(EvalError::PackingMismatch { coefficient: k });
        }
    }
    Ok(())
}

/// Eq. (10): the value the `PE(1, ℓ, b)` claim is supposed to make, computed from
/// the concatenated opening — the counterpart of [`layer_claim`], kept separate
/// so an assembly can *make* a claim without also *checking* it.
///
/// # Errors
/// [`EvalError::WrongVariableCount`] if `u` is not `ℓ+m` long, and
/// [`EvalError::WrongLength`] if `s` does not contain layer `level`.
pub fn layer_value<R: Ring, const D: usize>(
    s: &[PolyRing<R, D>],
    slot_len: usize,
    level: usize,
    u: &[PolyRing<R, D>],
) -> Result<PolyRing<R, D>, EvalError> {
    mle_at_ring(layer_of(s, slot_len, level)?, u)
}

/// Eq. (10): the PE claim `ṽ(u) = value` on layer `level` of the concatenated
/// vector, checked as that layer's MLE.
///
/// # Errors
/// [`EvalError::LayerClaimMismatch`] naming the layer.
pub fn layer_claim<R: Ring, const D: usize>(
    s: &[PolyRing<R, D>],
    slot_len: usize,
    level: usize,
    u: &[PolyRing<R, D>],
    claimed: &PolyRing<R, D>,
) -> Result<(), EvalError> {
    let layer = layer_of(s, slot_len, level)?;
    if mle_at_ring(layer, u)? != *claimed {
        return Err(EvalError::LayerClaimMismatch { level });
    }
    Ok(())
}

/// Def. 1: `split_b(z)` — the base-`BASE` decomposition of a **high-norm**
/// vector into `digits` planes with `z = Σ_{i} b^{i−1}·z_i` and `‖z_i‖∞ < b`.
///
/// Deliberately **not** [`crate::pcs::gadget::split`]: that one takes the
/// canonical representative in `[0, q)` and requires `BASE^DIGITS > q`, while
/// Π^Dec decomposes integer values of norm `< b^h` into `h ≈ log_b B ≪ α`
/// digits. Such a value can be *negative*, so the digits here are centered, and
/// a coefficient that does not fit is reported rather than wrapped.
///
/// # Errors
/// [`EvalError::DigitOverflow`] if some coefficient needs more than `digits`
/// planes.
///
/// # Panics
/// If `base < 2` or `digits == 0`.
pub fn split_balanced<R, const D: usize>(
    values: &[PolyRing<R, D>],
    base: u64,
    digits: usize,
) -> Result<Vec<Vec<PolyRing<R, D>>>, EvalError>
where
    R: Ring + CenteredRing,
{
    assert!(
        base >= 2 && digits >= 1,
        "a positional system needs base ≥ 2 and at least one digit"
    );
    let base_i = i128::from(base);
    let half = i128::from(base / 2);
    let modulus = i128::from(R::MODULUS);
    let mut planes = vec![vec![R::ZERO; values.len() * D]; digits];
    for (index, value) in values.iter().enumerate() {
        for (power, coefficient) in value.coefficients().into_iter().enumerate() {
            let raw = coefficient.centered();
            let negative = raw < 0;
            let mut remaining = i128::from(coefficient.centered().unsigned_abs());
            for plane in planes.iter_mut() {
                if remaining == 0 {
                    break;
                }
                let mut digit = remaining % base_i;
                if digit > half {
                    digit -= base_i;
                }
                // The invariant is `|x| = Σ_i base^i·digit_i` over the integers,
                // so the residual is the *exact* quotient `(remaining − digit)/b`.
                // A centered digit can itself be negative (`d > ⌊b/2⌋` carries),
                // *and* the coefficient can be negative; the stored digit is the
                // product of the two signs. Dropping the digit's own sign — as
                // this function used to — makes the recomposition read `7` as
                // `1 + 4·2 = 9`, so Π^Dec would recommit a different `s`.
                remaining = (remaining - digit) / base_i;
                let signed = if negative { -digit } else { digit };
                let stored = signed.rem_euclid(modulus);
                plane[index * D + power] = R::from(stored as u64);
            }
            if remaining != 0 {
                return Err(EvalError::DigitOverflow {
                    at: index * D + power,
                });
            }
        }
    }
    Ok(planes
        .into_iter()
        .map(|flat| {
            flat.chunks(D)
                .map(|c| PolyRing::from_coefficients(c.to_vec()))
                .collect()
        })
        .collect())
}

/// The recomposition `z = Σ_{i} b^{i−1}·z_i` inverse to [`split_balanced`].
///
/// # Panics
/// If `planes` is empty.
pub fn recompose_planes<R: Ring, const D: usize>(
    planes: &[Vec<PolyRing<R, D>>],
    base: u64,
) -> Vec<PolyRing<R, D>> {
    assert!(!planes.is_empty(), "recomposition needs at least one plane");
    let mut out = vec![zero_ring::<R, D>(); planes[0].len()];
    let mut weight = R::ONE;
    for plane in planes {
        for (acc, digit) in out.iter_mut().zip(plane.iter()) {
            *acc += scale_by_scalar(digit, weight);
        }
        weight *= R::from(base);
    }
    out
}

/// The number of base-`b` planes Π^Dec needs for a vector of norm `< bound`:
/// Lemma 13's `h := log_b B`, rounded up.
pub const fn decomposition_planes(base: u64, bound: u64) -> usize {
    let mut planes = 0usize;
    let mut capacity = 1u128;
    let target = bound as u128;
    while capacity < target {
        planes += 1;
        capacity = capacity.saturating_mul(base as u128);
    }
    // `max` on `usize` is not (yet) callable in a `const fn`.
    if planes == 0 {
        1
    } else {
        planes
    }
}

/// `q_A` of Eq. (26): `⊗_{r∈[n]} (p_{ξ,2^ℓ} ⊗ a_r)`, the batched `A`-matrix
/// constraint weights against `p_{η,n} ⊗ s`.
pub fn q_a_vector<R: Ring + CenteredRing, const D: usize, const BASE: u64, const ALPHA: usize>(
    key: &TreeKey<R, D, BASE, ALPHA>,
    height: usize,
    xi: R,
) -> Vec<PolyRing<R, D>> {
    let powers: Vec<PolyRing<R, D>> = powers_vector(xi, 1usize << height)
        .iter()
        .map(|p| embed::<R, D>(*p))
        .collect();
    let mut out = Vec::with_capacity(key.rows() * powers.len() * 2 * key.slot_len());
    for r in 0..key.rows() {
        out.extend(tensor_ring(&powers, key.matrix().row(r)));
    }
    out
}

/// `q_G` of Eq. (28): `(p_{ξ,2^ℓ} ⊗ p_{η,n}) ⊗ p_{b,α} ‖ 0^{2^ℓ nα}`.
///
/// Its exponent granularity is a *node* (`nα` digits) where `q_A` indexes
/// `2nα` blocks — precisely why Eq. (25)'s two sides share the ranges
/// `[2^i, 2^{i+1})`: a gadget-side node of layer `i` pairs with an `A`-side
/// block of layer `i+1`. The zero suffix is why the leaf layer `s_ℓ` never
/// appears on the gadget side, and the `ξ⁰` weight lands on the `0^{2nα}`
/// prefix that Eq. (31) forces to zero.
pub fn q_g_vector<R: Ring>(
    slot_len: usize,
    rows: usize,
    height: usize,
    base: u64,
    alpha: usize,
    xi: R,
    eta: R,
) -> Vec<R> {
    let nodes = tensor(
        &powers_vector(xi, 1usize << height),
        &powers_vector(eta, rows),
    );
    let mut out = tensor(&nodes, &powers_vector(R::from(base), alpha));
    debug_assert_eq!(out.len(), (1usize << height) * slot_len);
    out.resize(slot_len << (height + 1), R::ZERO);
    out
}

/// `q_dec,A` of Eq. (26): `⊗_{r∈[n]} (p_{b,h} ⊗ p_{ξ,2^ℓ} ⊗ a_r)`, the same
/// constraints lifted onto the decomposition planes.
pub fn q_dec_a_vector<
    R: Ring + CenteredRing,
    const D: usize,
    const BASE: u64,
    const ALPHA: usize,
>(
    key: &TreeKey<R, D, BASE, ALPHA>,
    height: usize,
    planes: usize,
    xi: R,
) -> Vec<PolyRing<R, D>> {
    let powers: Vec<PolyRing<R, D>> = tensor(
        &powers_vector(R::from(BASE), planes),
        &powers_vector(xi, 1usize << height),
    )
    .iter()
    .map(|p| embed::<R, D>(*p))
    .collect();
    let mut out = Vec::with_capacity(key.rows() * powers.len() * 2 * key.slot_len());
    for r in 0..key.rows() {
        out.extend(tensor_ring(&powers, key.matrix().row(r)));
    }
    out
}

/// `q_dec,G` of Eq. (28): `p_{b,h} ⊗ q_G`.
pub fn q_dec_g_vector<R: Ring>(
    slot_len: usize,
    rows: usize,
    height: usize,
    planes: usize,
    base: u64,
    alpha: usize,
    xi: R,
    eta: R,
) -> Vec<R> {
    tensor(
        &powers_vector(R::from(base), planes),
        &q_g_vector(slot_len, rows, height, base, alpha, xi, eta),
    )
}

/// [`concat_planes`]: `s_dec = s_{dec,1} ‖ … ‖ s_{dec,h}` as one vector (Eq. 21).
pub fn concat_planes<R: Ring, const D: usize>(
    planes: &[Vec<PolyRing<R, D>>],
) -> Vec<PolyRing<R, D>> {
    let mut out = Vec::with_capacity(planes.iter().map(Vec::len).sum());
    for plane in planes {
        out.extend_from_slice(plane);
    }
    out
}

/// Eq. (21)'s message `s_dec = s_{dec,1} ‖ … ‖ s_{dec,h}`, zero-extended to a
/// power-of-two length because the plane count is (`p_{b,h}`'s remark).
///
/// Protocol 5's Step 1(a) (p. 35) commits *this* vector, so both sides must build it
/// identically: [`decompose_prove`] hands it to `Commit`, and [`decompose_report`]
/// checks it with Def. 19's `Open_F` (`G_{2^µ n}·s_µ = s_dec`). Sharing one function
/// is what keeps the verifier from accepting a well-formed but unrelated `t*_dec`.
pub fn decomposed_leaves<R: Ring, const D: usize>(
    planes: &[Vec<PolyRing<R, D>>],
) -> Vec<PolyRing<R, D>> {
    let mut leaves = concat_planes(planes);
    let target = leaves.len().next_power_of_two();
    leaves.resize(target, zero_ring::<R, D>());
    leaves
}

/// Eq. (30): `ṽ(u) = Σ_{j∈[h]} b^{j−1}·s̃_{dec,j}(u)`, the input evaluation claim
/// re-read through the decomposition planes.
///
/// # Errors
/// [`EvalError::WrongLength`] if the planes differ in length.
pub fn mle_at_planes<R: Ring, const D: usize>(
    planes: &[Vec<PolyRing<R, D>>],
    u: &[PolyRing<R, D>],
    base: u64,
) -> Result<PolyRing<R, D>, EvalError> {
    let mut acc = zero_ring::<R, D>();
    let mut weight = R::ONE;
    for plane in planes {
        if plane.len() != planes[0].len() {
            return Err(EvalError::WrongLength {
                got: plane.len(),
                expected: planes[0].len(),
            });
        }
        acc += scale_by_scalar(&mle_at_ring(plane, u)?, weight);
        weight *= R::from(base);
    }
    Ok(acc)
}

/// Everything Π^Dec sends and forwards (Protocol 5): the decomposition planes,
/// the fresh low-norm tree commitment, and the two batched constraint claims.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DecompositionProof<R: Ring, const D: usize> {
    /// The `h` planes of `s_dec` (Eq. 21), each `0^{2nα} ‖ s_{dec,i,j}`.
    pub planes: Vec<Vec<PolyRing<R, D>>>,
    /// `(t*_dec, (s*_{dec,i}))`: the new tree commitment (Step 1).
    pub commitment: TreeOpening<R, D>,
    /// `v_A` of Eq. (27).
    pub v_a: PolyRing<R, D>,
    /// `v_G` of Eq. (29).
    pub v_g: PolyRing<R, D>,
}

/// Π^Dec prover (Protocol 5 Steps 1–2): decompose the concatenated opening into
/// `digits` planes, pad it to a power-of-two leaf count (the paper: "we could
/// pad `s_dec` and `p_{b,h}` with zeros at the end"), commit it in a fresh tree,
/// and form the batched claims.
///
/// # Errors
/// [`EvalError::DigitOverflow`] if `digits` is too small for the input norm,
/// [`EvalError::Tree`] if the padded vector is not a legal tree,
/// [`EvalError::WrongLength`] on an impossible shape.
pub fn decompose_prove<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    key: &TreeKey<R, D, BASE, ALPHA>,
    opening: &TreeOpening<R, D>,
    digits: usize,
    xi: R,
    eta: R,
) -> Result<DecompositionProof<R, D>, EvalError>
where
    R: Ring + CenteredRing,
{
    let slot = key.slot_len();
    let height = opening.layers.len();
    let s = concatenated(slot, &opening.layers);
    if s.len() != (2usize << height) * slot {
        return Err(EvalError::WrongLength {
            got: s.len(),
            expected: (2usize << height) * slot,
        });
    }
    let planes = split_balanced(&s, BASE, digits)?;
    // `p_{b,h}` is padded to `h` a power of two (Eq. 21's remark), so the planes
    // are zero-extended first: that keeps the batch weights aligned.
    let padded_planes = pad_planes(&planes, s.len())?;
    let leaves = decomposed_leaves(&padded_planes);
    let commitment = key.commit_digits(&leaves).map_err(EvalError::Tree)?;
    let q_a = q_a_vector::<R, D, BASE, ALPHA>(key, height, xi);
    let lifted = tensor_ring(&powers_ring(eta, key.rows()), &s);
    let v_a = inner_product(&lifted, &q_a);
    let q_dec_g = q_dec_g_vector(
        slot,
        key.rows(),
        height,
        padded_planes.len(),
        BASE,
        ALPHA,
        xi,
        eta,
    );
    let v_g = scalar_inner_product(&q_dec_g, &concat_planes(&padded_planes));
    Ok(DecompositionProof {
        planes: padded_planes,
        commitment,
        v_a,
        v_g,
    })
}

/// Zero-extends every plane to `len` entries (Eq. 21's padding, so the `0^{2nα}`
/// prefix assumption of the batched claims holds for the *new* tree too).
///
/// # Errors
/// [`EvalError::WrongLength`] if a plane is longer than `len`.
pub fn pad_planes<R: Ring, const D: usize>(
    planes: &[Vec<PolyRing<R, D>>],
    len: usize,
) -> Result<Vec<Vec<PolyRing<R, D>>>, EvalError> {
    planes
        .iter()
        .map(|plane| {
            if plane.len() > len {
                return Err(EvalError::WrongLength {
                    got: plane.len(),
                    expected: len,
                });
            }
            let mut out = plane.clone();
            out.resize(len, zero_ring::<R, D>());
            Ok(out)
        })
        .collect()
}

/// `p_{η,n}` lifted into the ring.
fn powers_ring<R: Ring, const D: usize>(eta: R, len: usize) -> Vec<PolyRing<R, D>> {
    powers_vector(eta, len)
        .iter()
        .map(|p| embed::<R, D>(*p))
        .collect()
}

/// **Every** equation Protocol 5 leaves on the verifier's side, evaluated rather
/// than taken up to the first failure. An empty vector is an accepted proof.
///
/// In protocol order:
/// 1. shapes: `s` is a concatenation, and `proof.planes` has the declared `h`
///    planes of the declared length (Eq. (21));
/// 2. Eq. (21)'s shortness: `‖s_{dec,j}‖∞ < b` for every plane;
/// 3. Eq. (31): no plane touches the `0^{2nα}` prefix. The paper runs this as a
///    sum-check because its verifier only ever sees `s̃_dec`; here the openings
///    are handed over, so it is decidable point by point. With `b^h < q` it is
///    *implied* by 1–2 (a `b`-short set of planes recomposing to `0` is all-zero
///    by the uniqueness of the balanced expansion), and it stops being implied
///    exactly when `b^h ≥ q` lets the recomposition wrap — which is why the gate
///    stays.
/// 4. the fresh commitment opens at `b` (Step 1's `t*_dec` is a real commitment);
/// 5. Eq. (21)'s sum: `s = Σ_{j∈[h]} b^{j−1}·s_{dec,j}`;
/// 6. Eq. (26)/(28): the digit-side and value-side batched constraints agree
///    with each other *and* with the sent `v_A`, `v_G`;
/// 7. Eq. (25): `ξ·⟨p_η,n, t⟩ + v_G = v_A`, which is what binds the input
///    commitment's own constraints into the reduction;
/// 8. Eq. (30): `v = Σ_{j∈[h]} b^{j−1}·s̃_{dec,j}(u)`, the input evaluation claim
///    re-read through the planes.
#[allow(clippy::too_many_arguments)]
pub fn decompose_report<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    key: &TreeKey<R, D, BASE, ALPHA>,
    proof: &DecompositionProof<R, D>,
    u: &[PolyRing<R, D>],
    v: &PolyRing<R, D>,
    opening: &TreeOpening<R, D>,
    digits: usize,
    xi: R,
    eta: R,
) -> Vec<EvalError>
where
    R: Ring + CenteredRing,
{
    let mut bad: Vec<EvalError> = Vec::new();
    let mut push = |error: EvalError| {
        if !bad.contains(&error) {
            bad.push(error);
        }
    };
    let slot = key.slot_len();
    let height = opening.layers.len();
    let s = concatenated(slot, &opening.layers);
    // 1. shapes. Everything below that indexes `s` alongside a plane needs these
    //    first, or an inner product would silently truncate.
    let want = (2usize << height).checked_mul(slot);
    let shape_ok = want == Some(s.len());
    if !shape_ok {
        push(EvalError::WrongLength {
            got: s.len(),
            expected: want.unwrap_or(usize::MAX),
        });
    }
    if proof.planes.len() != digits {
        push(EvalError::WrongLength {
            got: proof.planes.len(),
            expected: digits,
        });
    }
    let aligned = shape_ok
        && proof.planes.len() == digits
        && proof.planes.iter().all(|plane| plane.len() == s.len());
    // 2. Eq. (21)'s premise, plane by plane.
    for (plane_index, plane) in proof.planes.iter().enumerate() {
        let got = max_norm(plane);
        if got >= BASE {
            push(EvalError::PlaneNotShort {
                plane: plane_index,
                got,
                bound: BASE,
            });
        }
    }
    // 3. Eq. (31).
    for plane in proof.planes.iter() {
        for (at, value) in plane.iter().take(2 * slot).enumerate() {
            if value.coefficients().into_iter().any(|c| c != R::ZERO) {
                push(EvalError::PrefixNotZero { at });
            }
        }
    }
    // 4. the new tree opens.
    if let Err(err) = key.open(&proof.commitment, BASE) {
        push(EvalError::Tree(err));
    }
    // 4b. …and Step 1(a)'s other half: the new tree's own bottom layer **is** these
    //     planes. `TreeKey::commit_digits` takes the already-low-norm layer `s_µ`
    //     directly (Def. 19's second variant), and Protocol 5's Step 1 sets
    //     `s_µ := s_dec`, so equality of that layer is the binding. `Open` alone is
    //     self-consistency: an unrelated well-formed `t*_dec` sailed through every
    //     equation of Π^Dec — measured 2026-09-24, see
    //     [`EvalError::DecomposedCommitmentMismatch`].
    let expected = decomposed_leaves(&proof.planes);
    match proof.commitment.layers.last() {
        None => push(EvalError::Tree(TreeError::EmptyLayers)),
        Some(bottom) => {
            if bottom.len() != expected.len() {
                push(EvalError::WrongLength {
                    got: bottom.len(),
                    expected: expected.len(),
                });
            } else if let Some(at) = bottom
                .iter()
                .zip(expected.iter())
                .position(|(got, want)| got != want)
            {
                push(EvalError::DecomposedCommitmentMismatch { at });
            }
        }
    }
    if !aligned {
        return bad;
    }
    // 5. Eq. (21)'s sum.
    let recomposed = recompose_planes(&proof.planes, BASE);
    for (at, (got, want)) in recomposed.iter().zip(s.iter()).enumerate() {
        if got != want {
            push(EvalError::DecompositionMismatch { at });
            break;
        }
    }
    // 6. Eq. (26)/(28).
    let q_a = q_a_vector::<R, D, BASE, ALPHA>(key, height, xi);
    let q_dec_a = q_dec_a_vector::<R, D, BASE, ALPHA>(key, height, digits, xi);
    let lifted_s = tensor_ring(&powers_ring(eta, key.rows()), &s);
    let value_side_a = inner_product(&lifted_s, &q_a);
    let digit_side_a = inner_product(
        &tensor_ring(&powers_ring(eta, key.rows()), &concat_planes(&proof.planes)),
        &q_dec_a,
    );
    if value_side_a != digit_side_a || value_side_a != proof.v_a {
        push(EvalError::DecompositionSideMismatch);
    }
    let q_g = q_g_vector(slot, key.rows(), height, BASE, ALPHA, xi, eta);
    let q_dec_g = q_dec_g_vector(slot, key.rows(), height, digits, BASE, ALPHA, xi, eta);
    let value_side_g = scalar_inner_product(&q_g, &s);
    let digit_side_g = scalar_inner_product(&q_dec_g, &concat_planes(&proof.planes));
    if value_side_g != digit_side_g || value_side_g != proof.v_g {
        push(EvalError::DecompositionSideMismatch);
    }
    // 7. Eq. (25): `ξ · Σ_r η^(r−1) · t(r) + v_G = v_A`, i.e. the powers vector
    //    `p_{η,n}` scaled by `ξ` — *not* `p_{ξ·η,n}`.
    let mut root_weights = powers_vector(eta, key.rows());
    for weight in root_weights.iter_mut() {
        *weight *= xi;
    }
    let root_term = scalar_inner_product(&root_weights, &opening.root);
    if root_term + proof.v_g.clone() != proof.v_a {
        push(EvalError::ConstraintBatchMismatch);
    }
    // 8. Eq. (30).
    match mle_at_planes(&proof.planes, u, BASE) {
        Ok(reclaim) => {
            if reclaim != *v {
                push(EvalError::LayerClaimMismatch { level: height });
            }
        }
        Err(error) => push(error),
    }
    bad
}

/// Π^Dec verifier: [`decompose_report`] followed by "take the first", and then —
/// only if every equation held — Protocol 5's Step 3 output claim.
///
/// The forwarded claim is the evaluation of the *new* leaf vector
/// `s_dec = s_{dec,1} ‖ … ‖ s_{dec,h}` (Eq. (21), zero-padded to `2^µ·nα`) at
/// `r_new`, which has `µ + m` coordinates. It is bound to `t*_dec` because the
/// planes were just checked against that commitment's own leaf layer, and bound
/// to the input `t` by Eq. (25) — which is what makes the next cycle's
/// [`layer_claim`] of this value non-vacuous.
///
/// # Errors
/// The first entry of [`decompose_report`], plus
/// [`EvalError::WrongVariableCount`] when `r_new` does not index the new tree.
#[allow(clippy::too_many_arguments)]
pub fn decompose_verify<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    key: &TreeKey<R, D, BASE, ALPHA>,
    proof: &DecompositionProof<R, D>,
    u: &[PolyRing<R, D>],
    v: &PolyRing<R, D>,
    opening: &TreeOpening<R, D>,
    digits: usize,
    xi: R,
    eta: R,
    r_new: &[PolyRing<R, D>],
) -> Result<(Vec<PolyRing<R, D>>, PolyRing<R, D>), EvalError>
where
    R: Ring + CenteredRing,
{
    if let Some(error) = decompose_report(key, proof, u, v, opening, digits, xi, eta)
        .into_iter()
        .next()
    {
        return Err(error);
    }
    let mut padded = concat_planes(&proof.planes);
    let target = padded.len().next_power_of_two();
    padded.resize(target, zero_ring::<R, D>());
    Ok((r_new.to_vec(), mle_at_ring(&padded, r_new)?))
}

/// Squeezes `count` uniform field challenges from a Fiat–Shamir transcript bound
/// to `binding`, from one labeled stream (rejection sampled, so no modulus bias).
pub fn challenges<R: Ring>(domain: &[u8], binding: &[u8], count: usize) -> Vec<R> {
    let mut tr = Transcript::<Shake256Xof>::new(domain);
    tr.absorb(b"binding", binding);
    let seed = tr.challenge_bytes(32);
    let mut xof = seed_stream::<Shake256Xof>(domain, &seed);
    let mut stream = BitStream::new(&mut xof);
    (0..count)
        .map(|_| sample_uniform_coeff::<R>(&mut stream))
        .collect()
}

/// The transcript binding of one reduction: key seed, every commitment (root and
/// layers), every claimed value and point, in protocol order.
pub fn statement_bytes<R: Ring, const D: usize>(
    key_seed: &[u8; 32],
    commitments: &[&TreeOpening<R, D>],
    claims: &[PolyRing<R, D>],
    points: &[&[PolyRing<R, D>]],
) -> Vec<u8> {
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/tree-reduction");
    tr.absorb(b"key", key_seed);
    for opening in commitments {
        absorb_rings(&mut tr, b"t", &opening.root);
        for layer in &opening.layers {
            absorb_rings(&mut tr, b"s", layer);
        }
    }
    absorb_rings(&mut tr, b"v", claims);
    for point in points {
        absorb_rings(&mut tr, b"u", point);
    }
    tr.challenge_bytes(32)
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    type F = Zq<4294967197>;
    const D: usize = 8;
    /// `ℓ+1+m` for a height-`1` tree over `nα = 64` slots: Eq. (8)'s variable
    /// count with `ℓ = 1` and `m = log₂(nα) = 6`.
    const NV_TE: usize = 8;
    /// Eq. (15)/Step 1(c)'s round-message width at `b = 2`: `Δ + 1` with
    /// `Δ = 1 + (2b − 1) = 2b`, so `NC = 5`.
    const NC_TE: usize = (2 * BASE_TE + 1) as usize;
    /// The gadget base of [`key`]'s tree.
    const BASE_TE: u64 = 2;
    /// `m = log₂(nα)` for [`key`]: `nα = 2·32 = 64`.
    const M: usize = 6;
    type Key = TreeKey<F, D, 2, 32>;

    fn ring_vec(len: usize) -> Vec<PolyRing<F, D>> {
        (0..len)
            .map(|i| {
                PolyRing::from_coefficients(
                    (0..D)
                        .map(|j| F::from(((i * 131 + j * 17) % 31) as u64))
                        .collect(),
                )
            })
            .collect()
    }

    fn field_vec(len: usize) -> Vec<F> {
        (0..len)
            .map(|i| F::from((i as u64 * 7 + 1) % 1_000_003))
            .collect()
    }

    /// A genuinely `bound`-short ring vector: every coefficient is a *centered*
    /// value in `{0, ±1, …, ±⌊(bound−1)/2⌋}`, so `N_b` of Eq. (7) vanishes on it
    /// and `‖·‖∞ < bound` holds. [`ring_vec`] is not usable for the norm tests —
    /// its coefficients run up to 30.
    fn short_ring_vec(len: usize, bound: u64) -> Vec<PolyRing<F, D>> {
        let reach = i64::from(((bound - 1) / 2) as u32);
        let modulus = i64::try_from(F::MODULUS).expect("a 32-bit modulus fits i64");
        (0..len)
            .map(|i| {
                PolyRing::from_coefficients(
                    (0..D)
                        .map(|j| {
                            let raw = i64::try_from((i * 7 + j) as u64).expect("small")
                                % (2 * reach + 1)
                                - reach;
                            F::from(raw.rem_euclid(modulus) as u64)
                        })
                        .collect(),
                )
            })
            .collect()
    }

    fn key() -> Key {
        Key::setup(&[0x21u8; 32], 2)
    }

    #[test]
    fn eq_table_matches_the_msb_first_bit_convention() {
        // The layout of Eq. (12)/(14) only factors if the leading index bits are
        // the leading point coordinates: pin a hand-computed 2-variable case.
        let r = [F::from(3u64), F::from(5u64)];
        let table = eq_field_table(&r, 4).expect("2 variables");
        assert_eq!(table[2], F::from(3u64) * (F::ONE - F::from(5u64)));
        assert_eq!(table[1], (F::ONE - F::from(3u64)) * F::from(5u64));
        assert_eq!(table[3], r[0] * r[1]);
        assert_eq!(table[0], (F::ONE - r[0]) * (F::ONE - r[1]));
        assert_eq!(bits_of(2, 2), vec![true, false]);
        assert_eq!(
            eq_field_table(&r, 8),
            Err(EvalError::WrongVariableCount {
                got: 2,
                expected: 3
            })
        );
    }

    #[test]
    fn eq_table_is_a_partition_of_unity() {
        let table = eq_field_table(&field_vec(3), 8).expect("3 variables");
        assert_eq!(table.iter().fold(F::ZERO, |a, b| a + *b), F::ONE);
        let at = eq_field_table(&vec![F::ONE; 3], 8).expect("vertex");
        for (i, w) in at.iter().enumerate() {
            assert_eq!(*w, if i == 7 { F::ONE } else { F::ZERO }, "index {i}");
        }
        let ring_point = ring_vec(2);
        let ring_table = eq_ring_table(&ring_point, 4).expect("ring table");
        assert_eq!(
            ring_table
                .iter()
                .fold(zero_ring::<F, D>(), |a, b| a + b.clone()),
            embed::<F, D>(F::ONE)
        );
    }

    #[test]
    fn lemma_14_packing_holds_coefficient_by_coefficient() {
        let v = ring_vec(8);
        let r = field_vec(3);
        let packed = mle_at_field(&v, &r).expect("mle");
        let table = eq_field_table(&r, 8).expect("table");
        for k in 0..D {
            let column = coefficient_column(&v, k);
            let mut acc = F::ZERO;
            for (weight, value) in table.iter().zip(column.iter()) {
                acc += *weight * *value;
            }
            assert_eq!(coefficient_at(&packed, k), acc, "coefficient {k}");
        }
        packing_certificate(&v, &r, &packed).expect("certificate");
        let mut bad = packed.clone();
        bad += embed::<F, D>(F::ONE);
        assert_eq!(
            packing_certificate(&v, &r, &bad),
            Err(EvalError::PackingMismatch { coefficient: 0 })
        );
    }

    #[test]
    fn mle_at_ring_matches_a_hand_computed_two_variable_sum() {
        let v = ring_vec(4);
        let point = ring_vec(2);
        let one = embed::<F, D>(F::ONE);
        let mut expect = zero_ring::<F, D>();
        for (x, value) in v.iter().enumerate() {
            let mut w = one.clone();
            for (i, bit) in bits_of(x, 2).iter().enumerate() {
                w *= if *bit {
                    point[i].clone()
                } else {
                    one.clone() - point[i].clone()
                };
            }
            expect += w * value.clone();
        }
        assert_eq!(mle_at_ring(&v, &point).expect("mle"), expect);
        assert_eq!(
            mle_at_ring(&v, &ring_vec(3)),
            Err(EvalError::WrongVariableCount {
                got: 3,
                expected: 2
            })
        );
    }

    #[test]
    fn cached_eq_tables_agree_with_the_one_shot_mle() {
        let v = ring_vec(4);
        let w = ring_vec(4);
        let point = ring_vec(2);
        let mut cache = EqTables::at(&point);
        assert_eq!(cache.point(), point.as_slice());
        assert_eq!(
            cache.mle(&v).expect("cached mle"),
            mle_at_ring(&v, &point).expect("one-shot mle")
        );
        // A second vector on the *same* cached table: the first inner product must
        // not disturb it, or `fold_report`'s 2^k-subtree loop would silently read
        // stale weights.
        assert_eq!(
            cache.mle(&w).expect("reused cached mle"),
            mle_at_ring(&w, &point).expect("one-shot mle")
        );
        // The shape check lives in the build, so a cache that already holds a good
        // table must still refuse a wrong-length vector.
        assert_eq!(
            cache.mle(&ring_vec(8)),
            Err(EvalError::WrongVariableCount {
                got: 2,
                expected: 3
            })
        );
    }

    #[test]
    fn powers_mle_extends_the_powers_vector() {
        // Eq. (13): êp must reproduce p at hypercube vertices — the identity the
        // batching claims of Eq. (17)–(19) and Eq. (26)/(28) rest on.
        let eta = F::from(11u64);
        let p = powers_vector(eta, 8);
        assert_eq!(p[0], F::ONE);
        assert_eq!(p[3], eta.pow(3));
        for x in 0..8usize {
            let point: Vec<F> = bits_of(x, 3)
                .iter()
                .map(|b| if *b { F::ONE } else { F::ZERO })
                .collect();
            assert_eq!(powers_mle(eta, 8, &point).expect("mle"), p[x], "vertex {x}");
        }
        assert_eq!(
            powers_mle(eta, 8, &[eta, eta]),
            Err(EvalError::WrongVariableCount {
                got: 2,
                expected: 3
            })
        );
    }

    #[test]
    fn norm_polynomial_vanishes_exactly_on_the_bounded_values() {
        let bound = 4u64;
        assert!(!norm_polynomial_wraps(bound, F::MODULUS));
        for v in 0..bound {
            for sign in [1i64, -1] {
                let raw = (v as i64 * sign).rem_euclid(F::MODULUS as i64) as u64;
                assert_eq!(norm_polynomial(bound, F::from(raw)), F::ZERO, "±{v}");
            }
        }
        for v in bound..bound + 6 {
            assert_ne!(
                norm_polynomial(bound, F::from(v)),
                F::ZERO,
                "{v} must not vanish"
            );
        }
        assert!(norm_polynomial_wraps(F::MODULUS / 2 + 1, F::MODULUS));
    }

    #[test]
    fn norm_check_table_is_the_xi_batching_of_eq_8() {
        // Eq. (8) claims `Σ_X N_{b_l}(ĉf(s_l)_k(X)) = 0`, which is only an honest
        // claim for a vector that really is `b`-short — so the test data must be.
        // `ring_vec`'s coefficients run to 30, which is why this test previously
        // asserted a zero sum it could not have.
        let s = short_ring_vec(4, 4);
        let r = field_vec(2);
        let xi = F::from(7u64);
        let bound = 4u64;
        let (q, table) = norm_check_table(&s, &r, xi, bound).expect("2 variables");
        let weights = eq_field_table(&r, 4).expect("weights");
        for (index, entry) in q.iter().enumerate() {
            let mut expect = F::ZERO;
            let mut power = F::ONE;
            for k in 0..D {
                expect += power * norm_polynomial(bound, coefficient_at(&s[index], k));
                power *= xi;
            }
            assert_eq!(*entry, expect, "table entry {index}");
            assert_eq!(table[index], expect * weights[index]);
        }
        assert_eq!(
            q.iter().fold(F::ZERO, |a, b| a + *b),
            F::ZERO,
            "every coefficient is < 4 by construction, so each N_b vanishes"
        );
        assert_eq!(
            table.iter().fold(F::ZERO, |a, b| a + *b),
            F::ZERO,
            "…and so does the êq-weighted sum the sum-check is about"
        );
    }

    #[test]
    fn a_long_vector_breaks_the_norm_zero_check() {
        // Non-vacuity: starting from a genuinely 4-short vector, one coefficient
        // at 9 makes Eq. (8)'s batched polynomial non-zero *at that point*.
        let mut s = short_ring_vec(4, 4);
        let first = s[0].coefficients()[0];
        s[0] += embed::<F, D>(F::from(9u64) - first);
        assert!(max_norm(&s) >= 9, "the tamper is really out of range");
        let r = field_vec(2);
        let (q, batched) = norm_check_table(&s, &r, F::from(7u64), 4).expect("shape ok");
        assert_ne!(q[0], F::ZERO, "N_4(9) ≠ 0, so Q_N is non-zero at index 0");
        assert!(
            q[1..].iter().all(|value| *value == F::ZERO),
            "and non-zero *only* there: every other entry is still 4-short"
        );
        // …which is why the verifier's gate is pointwise rather than the
        // êq-weighted sum Lemma 4 states. That equivalence needs a *random* `Z`;
        // this test's `r` has `r₀ = 1 ∈ {0,1}`, so êq(r, ·) vanishes on the whole
        // x₀ = 0 face and the tampered point drops out of the sum entirely.
        assert_eq!(r[0], F::ONE, "the degenerate coordinate the gate must survive");
        assert_eq!(
            batched.iter().fold(F::ZERO, |a, b| a + *b),
            F::ZERO,
            "the weighted sum really is zero, so Eq. (8)'s claim would pass"
        );
    }

    #[test]
    fn split_balanced_round_trips_signed_high_norm_vectors() {
        let values: Vec<PolyRing<F, D>> = (0..3)
            .map(|i| {
                PolyRing::from_coefficients(
                    (0..D)
                        .map(|j| {
                            let raw = match (i + j) % 4 {
                                0 => 12_287i64,
                                1 => -12_287,
                                2 => -1,
                                _ => 0,
                            };
                            F::from(raw.rem_euclid(F::MODULUS as i64) as u64)
                        })
                        .collect(),
                )
            })
            .collect();
        let planes = split_balanced(&values, 2, 14).expect("14 binary planes cover 2^14");
        assert_eq!(planes.len(), 14);
        for plane in &planes {
            assert!(max_norm(plane) < 2, "digits stay binary");
        }
        assert_eq!(recompose_planes(&planes, 2), values);
        assert!(matches!(
            split_balanced(&values, 2, 13),
            Err(EvalError::DigitOverflow { .. })
        ));
    }

    #[test]
    fn split_balanced_matches_a_hand_computed_base_4_expansion() {
        // Centered base 4 has digits in `[−⌊b/2⌋, ⌊b/2⌋] = [−2, 2]`, so a
        // coefficient of 3 must *carry*: `7 = −1 + 4·2`, not `−3 + 4·1` (−3 is not
        // a base-4 digit). `6 = 2 + 4·1` needs no carry. The sign handling is what
        // a canonical mod-q split like [`crate::pcs::gadget::split`] gets wrong,
        // because Π^Dec decomposes integer values of norm `< b^h`, not residues.
        let values = vec![embed::<F, D>(F::from(7u64)), embed::<F, D>(F::from(6u64))];
        let planes = split_balanced(&values, 4, 3).expect("3 base-4 planes");
        assert_eq!(planes[0][0].coefficients()[0].centered(), -1);
        assert_eq!(planes[1][0].coefficients()[0].centered(), 2);
        assert_eq!(planes[0][1].coefficients()[0].centered(), 2);
        assert_eq!(planes[1][1].coefficients()[0].centered(), 1);
        assert_eq!(planes[2], vec![zero_ring::<F, D>(); 2], "the top plane is spare");
        for plane in &planes {
            assert!(max_norm(plane) < 4, "Eq. 21's ‖s_dec,j‖∞ < b");
        }
        assert_eq!(recompose_planes(&planes, 4), values);
        // A negative value keeps its own sign in *every* plane, which is what
        // makes `Σ b^{j−1}·s_{dec,j}` reproduce it exactly.
        let signed = vec![embed::<F, D>(F::from(7u64)), embed::<F, D>(F::ONE)];
        let negated: Vec<PolyRing<F, D>> = signed
            .iter()
            .map(|z| zero_ring::<F, D>() - z.clone())
            .collect();
        let planes = split_balanced(&negated, 4, 3).expect("−7 needs the same 3 planes");
        assert_eq!(planes[0][0].coefficients()[0].centered(), 1, "−(−1)");
        assert_eq!(planes[1][0].coefficients()[0].centered(), -2, "−(+2)");
        assert_eq!(recompose_planes(&planes, 4), negated);
    }

    #[test]
    fn decomposition_planes_is_the_logs_of_lemma_13() {
        assert_eq!(decomposition_planes(2, 12_288), 14);
        assert_eq!(decomposition_planes(2, 2), 1);
        assert_eq!(decomposition_planes(2, 3), 2);
        assert_eq!(decomposition_planes(4, 16), 2);
    }

    #[test]
    fn layer_range_is_the_layout_eq_12_factors_over() {
        let slot = 8usize;
        assert_eq!(layer_range(slot, 1), 16..32);
        assert_eq!(layer_range(slot, 2), 32..64);
        let s = concatenated(
            slot,
            &[
                vec![embed::<F, D>(F::from(1u64)); 16],
                vec![embed::<F, D>(F::from(2u64)); 32],
            ],
        );
        assert_eq!(s.len(), 64, "prefix(16) + 16 + 32");
        assert_eq!(
            layer_of(&s, slot, 1).expect("layer 1")[0].coefficients()[0],
            F::from(1u64)
        );
        assert_eq!(
            layer_of(&s, slot, 2).expect("layer 2")[0].coefficients()[0],
            F::from(2u64)
        );
        assert!(s[..2 * slot]
            .iter()
            .all(|z| z.coefficients().into_iter().all(|c| c == F::ZERO)));
        // Layer 3 of a 2-layer tree is out of range: `layer_range(8, 3)` is
        // 64..128 and `s` stops at 64, so the error names the *needed* end.
        assert_eq!(
            layer_of(&s, slot, 3),
            Err(EvalError::WrongLength {
                got: 64,
                expected: 128
            })
        );
        // Layer 2 is the concatenation's second half — the fact Eq. (10)'s
        // `êq(X₁,1)` selector and `concatenated_point` both rest on.
        assert_eq!(layer_range(slot, 2), 32..64);
        assert_eq!(layer_range(slot, 2).start, s.len() / 2);
    }

    #[test]
    fn q_g_and_q_a_use_the_exponent_ranges_eq_25_claims() {
        // A gadget-side node of layer i and an A-side block of layer i+1 must
        // carry the same ξ power, and ξ⁰ must land on the zero prefix.
        let rows = 2usize;
        let alpha = 2usize;
        let slot = rows * alpha; // nα
        let height = 3usize; // ℓ
        let xi = F::from(5u64);
        let eta = F::from(3u64);
        let qg = q_g_vector::<F>(slot, rows, height, 4, alpha, xi, eta);
        assert_eq!(qg.len(), slot << (height + 1), "q_G is as long as s");
        for e in 0..(1usize << height) {
            for r in 0..rows {
                for j in 0..alpha {
                    let expect = xi.pow(e as u64) * eta.pow(r as u64) * F::from(4u64).pow(j as u64);
                    assert_eq!(
                        qg[e * slot + r * alpha + j],
                        expect,
                        "node {e} row {r} digit {j}"
                    );
                }
            }
        }
        let live = (1usize << height) * slot;
        assert!(
            qg[live..].iter().all(|x| *x == F::ZERO),
            "Eq. 28's suffix: s_ℓ never appears on the gadget side"
        );
        assert_eq!(qg[0], F::ONE, "the prefix slot carries ξ⁰·η⁰·b⁰");

        let key = key();
        let powers: Vec<PolyRing<F, D>> = powers_vector(xi, 1usize << height)
            .iter()
            .map(|p| embed::<F, D>(*p))
            .collect();
        let mut q_a_short: Vec<PolyRing<F, D>> = Vec::new();
        for r in 0..rows {
            q_a_short.extend(tensor_ring(&powers, key.matrix().row(r)));
        }
        assert_eq!(
            q_a_short.len(),
            rows * (1usize << height) * 2 * key.slot_len(),
            "q_A spans n · 2^ℓ blocks of width 2nα"
        );
        // Its first 2nα entries are a₀ (ξ⁰), the next 2nα are ξ·a₀, …
        for r in 0..rows {
            for e in 0..(1usize << height) {
                let start = r * (1usize << height) * 2 * key.slot_len() + e * 2 * key.slot_len();
                let block = &q_a_short[start..start + 2 * key.slot_len()];
                let row = key.matrix().row(r);
                for (k, entry) in block.iter().enumerate() {
                    assert_eq!(
                        *entry,
                        embed::<F, D>(xi.pow(e as u64)) * row[k].clone(),
                        "row {r} block {e}"
                    );
                }
            }
        }
    }

    #[test]
    fn inner_product_panics_on_mismatched_lengths() {
        let a = ring_vec(4);
        let b = ring_vec(3);
        assert!(std::panic::catch_unwind(|| inner_product(&a, &b)).is_err());
    }

    #[test]
    fn challenges_are_deterministic_and_domain_separated() {
        let binding = b"statement";
        let a: Vec<F> = challenges(b"sc", binding, 4);
        let b: Vec<F> = challenges(b"sc", binding, 4);
        let c: Vec<F> = challenges(b"folding", binding, 4);
        assert_eq!(a, b, "same transcript, same challenges");
        assert_ne!(a, c, "the domain label must separate reductions");
        assert_eq!(a.len(), 4);
        assert_ne!(a[0], a[1]);
    }

    #[test]
    fn scalar_inner_product_matches_the_ring_product_for_constant_weights() {
        let weights = field_vec(4);
        let values: Vec<PolyRing<F, D>> = weights.iter().map(|w| embed::<F, D>(*w)).collect();
        let cheap = scalar_inner_product(&weights, &values);
        let ring_weights: Vec<PolyRing<F, D>> = weights.iter().map(|w| embed::<F, D>(*w)).collect();
        assert_eq!(cheap, inner_product(&ring_weights, &values));
    }

    /// Protocol 3 on a real tree: `s = 0^{2nα} ‖ s₁` for a height-`1` tree is
    /// `2^{1+1}·nα = 2⁷·… ` entries, so the norm-check sum-check runs over
    /// `ℓ+1+m = 8` variables (Eq. (8)), and the PE point has `ℓ+m = 7`.
    #[test]
    fn norm_check_proves_and_verifies_a_real_tree_opening() {
        let key = key();
        let slot = key.slot_len();
        let f = ring_vec(2 * key.rows());
        let opening = key.commit(&f).expect("a height-1 tree over 2n elements");
        assert_eq!(opening.layers.len(), 1);
        let s = concatenated(slot, &opening.layers);
        assert_eq!(s.len(), 4 * slot, "s = 0²ⁿᵠ ‖ s₁");
        let binding = statement_bytes(key.seed(), &[&opening], &[], &[]);
        let drawn = challenges::<F>(b"test-norm", &binding, NV_TE + D);
        let r = drawn[..NV_TE].to_vec();
        let xi = drawn[NV_TE];
        // The PE claim Eq. (10) puts into Protocol 3's Step 3(b): a point of
        // ℓ+m = 7 coordinates on the *bottom layer*, and its value.
        let u = ring_vec(NV_TE - 1);
        let v = mle_at_ring(layer_of(&s, slot, 1).expect("layer 1"), &u).expect("PE claim");
        let proof =
            norm_check_prove::<F, D, NV_TE, NC_TE>(&s, &r, xi, key.base(), &binding, slot, &u, &v)
                .expect("prove");
        assert_eq!(proof.sumcheck.point.len(), NV_TE, "r_N has ℓ+1+m coordinates");
        assert_eq!(
            proof.sumcheck.rounds.len(),
            NV_TE,
            "one degree-{} message per variable",
            NC_TE - 1
        );
        assert_eq!(proof.sumcheck.rounds[0].len(), NC_TE);
        assert!(
            norm_check_report(
                &proof, &s, &r, xi, key.base(), &binding, slot, &u, &v
            )
            .is_empty(),
            "the prover's self-check and the verifier agree: an honest proof \
             satisfies every equation at once"
        );
        norm_check_verify::<F, D, NV_TE, NC_TE>(
            &proof, &s, &r, xi, key.base(), &binding, slot, &u, &v,
        )
        .expect("an honest norm check verifies");
        // The same proof under a different statement must be refused.
        let other = statement_bytes(key.seed(), &[&opening], &[embed::<F, D>(F::ONE)], &[]);
        assert_eq!(
            norm_check_verify::<F, D, NV_TE, NC_TE>(
                &proof, &s, &r, xi, key.base(), &other, slot, &u, &v
            ),
            Err(EvalError::SumcheckRejected)
        );
        // …and so must the same proof under a *different* `r`, which Step 1(a)
        // makes a verifier message and the transcript therefore binds.
        let mut shifted = r.clone();
        shifted[0] += F::ONE;
        assert_eq!(
            norm_check_verify::<F, D, NV_TE, NC_TE>(
                &proof, &s, &shifted, xi, key.base(), &binding, slot, &u, &v
            ),
            Err(EvalError::SumcheckRejected),
            "r is Lemma 4's Z: replaying a proof under another Z is a replay of \
             the zero-check, so it must be refused"
        );
    }

    #[test]
    fn norm_check_rejects_a_forged_evaluation_and_a_bad_packing() {
        let key = key();
        let slot = key.slot_len();
        let f = ring_vec(2 * key.rows());
        let opening = key.commit(&f).expect("commit");
        let s = concatenated(slot, &opening.layers);
        let binding = statement_bytes(key.seed(), &[&opening], &[], &[]);
        let drawn = challenges::<F>(b"test-norm", &binding, NV_TE + D);
        let r = drawn[..NV_TE].to_vec();
        let xi = drawn[NV_TE];
        let u = ring_vec(NV_TE - 1);
        let v = mle_at_ring(layer_of(&s, slot, 1).expect("layer 1"), &u).expect("PE claim");
        let prove = || {
            norm_check_prove::<F, D, NV_TE, NC_TE>(
                &s, &r, xi, key.base(), &binding, slot, &u, &v,
            )
            .expect("prove")
        };
        let report = |proof: &NormCheckProof<F, D, NV_TE, NC_TE>| {
            norm_check_report(proof, &s, &r, xi, key.base(), &binding, slot, &u, &v)
        };
        let check = |proof: &NormCheckProof<F, D, NV_TE, NC_TE>| {
            norm_check_verify::<F, D, NV_TE, NC_TE>(
                proof, &s, &r, xi, key.base(), &binding, slot, &u, &v,
            )
        };
        assert_eq!(report(&prove()), Vec::new(), "the honest proof is clean");

        // A forged `y_N` fails the transcript *and* Step 2(b)'s equation, which is
        // the point of reporting both: the second names the equation that owns
        // `y_N`, the first only says the message does not replay.
        let mut forged_y = prove();
        forged_y.sumcheck.final_eval += F::ONE;
        assert_eq!(
            report(&forged_y),
            vec![
                EvalError::SumcheckRejected,
                EvalError::PackedNormMismatch,
            ],
            "y_N is bound twice over"
        );
        assert_eq!(check(&forged_y), Err(EvalError::SumcheckRejected));

        // Step 2(a)'s `a` must be the packing Lemma 14 identifies with the
        // sum-check's `d` coefficient claims, *and* a root of `N_b`.
        let mut forged_packed = prove();
        forged_packed.packed = forged_packed.packed + embed::<F, D>(F::from(2u64));
        let forged = report(&forged_packed);
        assert_eq!(forged.len(), 2, "{forged:?}");
        assert!(forged.contains(&EvalError::PackedNormMismatch), "{forged:?}");
        assert!(
            matches!(
                forged.iter().find(|e| matches!(e, EvalError::PackingMismatch { .. })),
                Some(EvalError::PackingMismatch { .. })
            ),
            "{forged:?}"
        );

        // r_N is derived by the transcript, not sent.
        let mut forged_point = prove();
        forged_point.sumcheck.point[0] += F::ONE;
        let forged = report(&forged_point);
        assert_eq!(forged[0], EvalError::SumcheckRejected, "{forged:?}");
        assert!(forged.contains(&EvalError::PackedNormMismatch), "{forged:?}");
        assert!(
            forged
                .iter()
                .any(|e| matches!(e, EvalError::PackingMismatch { .. })),
            "{forged:?}"
        );

        // A forged *input* claim is caught by Eq. (10), before any sum-check.
        assert_eq!(
            norm_check_verify::<F, D, NV_TE, NC_TE>(
                &prove(),
                &s,
                &r,
                xi,
                key.base(),
                &binding,
                slot,
                &u,
                &(v.clone() + embed::<F, D>(F::ONE)),
            ),
            Err(EvalError::LayerClaimMismatch { level: 1 }),
            "Protocol 3's input is a PE claim; a wrong v is not in TE"
        );
        // …and a point of the wrong length names the length the relation wants.
        assert_eq!(
            norm_check_prove::<F, D, NV_TE, NC_TE>(
                &s,
                &r,
                xi,
                key.base(),
                &binding,
                slot,
                &ring_vec(NV_TE),
                &v
            ),
            Err(EvalError::WrongVariableCount {
                got: NV_TE,
                expected: NV_TE - 1
            }),
            "a PE point is ℓ+m, one shorter than the ℓ+1+m TE point"
        );
        // Eq. (8) is the reduction's whole content: a witness with one coefficient
        // out of range makes the batched polynomial non-zero, and the prover will
        // not even build the transcript.
        let mut unsound = s.clone();
        let before = coefficient_at(&unsound[2 * slot], 0);
        unsound[2 * slot] = unsound[2 * slot].clone() + embed::<F, D>(F::from(9u64) - before);
        assert!(max_norm(&unsound) >= 9);
        let v_bad = layer_value(&unsound, slot, 1, &u).expect("re-claim");
        assert_eq!(
            norm_check_prove::<F, D, NV_TE, NC_TE>(
                &unsound,
                &r,
                xi,
                key.base(),
                &binding,
                slot,
                &u,
                &v_bad
            ),
            Err(EvalError::PackedNormMismatch),
            "the honest sum-check claim is 0 only for a b-short opening"
        );
        // The declared round width must match `N_b`'s degree: `NC = 2b + 1`.
        assert_eq!(
            norm_check_prove::<F, D, NV_TE, 3>(
                &s,
                &r,
                xi,
                key.base(),
                &binding,
                slot,
                &u,
                &v
            ),
            Err(EvalError::DegreeUnderstated {
                degree: 4,
                declared: 2
            }),
            "a linear round message cannot carry a degree-4 circuit"
        );
    }

    #[test]
    fn concatenated_point_binds_the_pe_claim_to_the_concatenation() {
        // §5 "Relations" (p. 25) is the whole content of this function: `PE`'s
        // point has ℓ+m coordinates and is evaluated on `s_ℓ`, `TE`'s has
        // ℓ+1+m and is evaluated on `s`. The extra coordinate is the `êq(X₁,1)`
        // selector of Eq. (10) (p. 27), and `s_ℓ` is the concatenation's second
        // half because the zero prefix is `2nα` and `Σ_{i<ℓ}2ⁱnα = (2^ℓ−2)nα`.
        let key = key();
        let slot = key.slot_len();
        let f = ring_vec(8 * key.rows());
        let opening = key.commit(&f).expect("a height-3 tree");
        let height = opening.layers.len();
        let s = concatenated(slot, &opening.layers);
        assert_eq!(s.len(), (2usize << height) * slot);
        let u = ring_vec(height + slot.trailing_zeros() as usize);
        let point = concatenated_point(&u, &s, slot).expect("the shapes line up");
        assert_eq!(point.len(), u.len() + 1, "the TE point is one bit longer");
        assert_eq!(point[0], embed::<F, D>(F::ONE), "…and the bit is a 1");
        assert_eq!(&point[1..], &u[..], "the rest is the PE point, in order");
        // The two readings of the claim must agree, or the bridge is a lie.
        let v = mle_at_ring(layer_of(&s, slot, height).expect("bottom layer"), &u).expect("PE");
        assert_eq!(
            mle_at_ring(&s, &point).expect("TE"),
            v,
            "s̃(1‖u) = s̃_ℓ(u) — Eq. (10)'s selector as a point"
        );
        // The wrong shapes are refused rather than silently re-binding the claim.
        assert_eq!(
            concatenated_point(&u, &s[..s.len() / 2], slot),
            Err(EvalError::WrongVariableCount {
                got: u.len(),
                expected: u.len() - 1
            }),
            "a shorter s is a shorter tree, so u is now one coordinate too long"
        );
        assert_eq!(
            concatenated_point(&u[..u.len() - 1], &s, slot),
            Err(EvalError::WrongVariableCount {
                got: u.len() - 1,
                expected: u.len()
            })
        );
        assert_eq!(
            concatenated_point(&u, &s, slot * 3 / 2),
            Err(EvalError::WrongLength {
                got: slot * 3 / 2,
                expected: slot * 2
            }),
            "nα must be a power of two for m = log(nα) to exist"
        );
    }

    /// Protocol 5 Step 1(a) (p. 35) has the prover **commit** to
    /// `s_dec = s_{dec,1} ‖ … ‖ s_{dec,h}`, so the verifier owes a check that the tree
    /// it receives commits to the planes it was shown. It did not have one: this
    /// attack — keep the planes and every claim, swap `t*_dec` for an unrelated
    /// well-formed tree of the same height — used to return an empty failing set, and
    /// `EvalError::DecomposedCommitmentMismatch` is what now answers it.
    #[test]
    fn an_unrelated_new_tree_is_refused_by_the_decomposition() {
        let key = key();
        let slot = key.slot_len();
        let f = ring_vec(8 * key.rows());
        let opening = key.commit(&f).expect("a height-3 tree");
        let height = opening.layers.len();
        let s = concatenated(slot, &opening.layers);
        let binding = statement_bytes(key.seed(), &[&opening], &[], &[]);
        let drawn = challenges::<F>(b"test-dec", &binding, 3);
        let (xi, eta) = (drawn[0], drawn[1]);
        let proof = decompose_prove::<F, D, 2, 32>(&key, &opening, 2, xi, eta)
            .expect("a binary opening needs two planes");
        let u = ring_vec(height + 1 + M);
        let v = mle_at_ring(&s, &u).expect("TE claim");
        let honest_planes = concat_planes(&proof.planes);
        // The decoy: a *different* short message of the same width, committed by the
        // same capability `decompose_prove` uses, so it is a perfectly well-formed
        // `t*_dec` that simply is not a commitment to the planes being shown.
        let mut decoy_leaves = vec![zero_ring::<F, D>(); honest_planes.len()];
        decoy_leaves[0] = embed::<F, D>(F::ONE);
        decoy_leaves[1] = embed::<F, D>(F::ONE);
        let decoy = key
            .commit_digits(&decoy_leaves)
            .expect("another short message, same width");
        assert_eq!(
            decoy.layers.len(),
            proof.commitment.layers.len(),
            "same height, so the shape checks cannot be what rejects it"
        );
        let mut forged = proof.clone();
        forged.commitment = decoy;
        let bad = decompose_report::<F, D, 2, 32>(&key, &forged, &u, &v, &opening, 2, xi, eta);
        assert!(
            bad.iter()
                .any(|e| matches!(e, EvalError::DecomposedCommitmentMismatch { .. })),
            "the swapped `t*_dec` must be refused *by name*: {bad:?}"
        );
        assert!(
            decompose_report::<F, D, 2, 32>(&key, &proof, &u, &v, &opening, 2, xi, eta).is_empty(),
            "the honest decomposition must still pass the new leaf equation"
        );
    }

    #[test]
    fn decomposition_round_trips_and_checks_eq_25() {
        let key = key();
        let slot = key.slot_len();
        let f = ring_vec(8 * key.rows());
        let opening = key.commit(&f).expect("a height-3 tree");
        let height = opening.layers.len();
        let s = concatenated(slot, &opening.layers);
        let binding = statement_bytes(key.seed(), &[&opening], &[], &[]);
        let drawn = challenges::<F>(b"test-dec", &binding, 3);
        let (xi, eta) = (drawn[0], drawn[1]);
        // `h = 2` planes for a binary opening: the lower plane is `s` and the
        // spare plane is zero, which is Eq. (21)'s shape at its cheapest.
        let proof = decompose_prove::<F, D, 2, 32>(&key, &opening, 2, xi, eta)
            .expect("a binary opening needs two planes");
        assert_eq!(proof.planes.len(), 2);
        assert_eq!(proof.planes[0], s, "the b⁰ plane");
        assert_eq!(proof.planes[1], vec![zero_ring::<F, D>(); s.len()]);
        assert_eq!(
            recompose_planes(&proof.planes, 2),
            s,
            "Eq. (21): s = Σⱼ bʲ⁻¹·s_dec,j"
        );
        // Protocol 5's parameters (p. 37): ℓ̃ := ℓ+1+log h, and Step 1 commits
        // `s_dec ∈ R^{h·2^{ℓ+1}nα}`, a tree of exactly that height.
        let new_height = height + 1 + 1;
        assert_eq!(
            proof.commitment.layers.len(),
            new_height,
            "ℓ̃ = ℓ+1+log₂ h"
        );
        // Protocol 5's input is a TE claim: the point has ℓ+1+m coordinates and
        // the value is the *concatenation*'s MLE, not a layer's.
        let u = ring_vec(height + 1 + M);
        let v = mle_at_ring(&s, &u).expect("TE claim");
        let r_new = ring_challenges::<F, D>(b"test-dec-point", &binding, new_height + M);
        let (point, y_dec) = decompose_verify::<F, D, 2, 32>(
            &key, &proof, &u, &v, &opening, 2, xi, eta, &r_new,
        )
        .expect("Eq. 25/26/28/30/31 all hold for an honest decomposition");
        assert_eq!(point, r_new, "the output point is the prefix Step 3 names");
        // Protocol 5's Step 3 claim is the MLE of the *new* leaf vector
        // `s_dec = s_{dec,1} ‖ … ‖ s_{dec,h}` (Eq. 21's concatenation, `µ+m`
        // coordinates) at `r_new`. That is *not* Eq. (30)'s reading, which
        // evaluates each plane at the input TE point `u` with `ℓ+1+m`
        // coordinates: the concatenation is indexed by its leading `log h`
        // bits, so the two differ by exactly that selector.
        let log_planes = proof.planes.len().trailing_zeros() as usize;
        let mut expect = zero_ring::<F, D>();
        for (index, plane) in proof.planes.iter().enumerate() {
            let selector = eq_of_bits_point(&bits_of(index, log_planes), &r_new).expect("weight");
            expect += selector * mle_at_ring(plane, &r_new[log_planes..]).expect("plane at the tail");
        }
        assert_eq!(
            y_dec, expect,
            "the forwarded claim is the *new* tree's own evaluation"
        );
    }

    #[test]
    fn decomposition_reports_the_equation_a_tamper_breaks() {
        let key = key();
        let slot = key.slot_len();
        let f = ring_vec(8 * key.rows());
        let opening = key.commit(&f).expect("commit");
        let height = opening.layers.len();
        let new_height = height + 1 + 1;
        let binding = statement_bytes(key.seed(), &[&opening], &[], &[]);
        let drawn = challenges::<F>(b"test-dec", &binding, 3);
        let (xi, eta) = (drawn[0], drawn[1]);
        let s = concatenated(slot, &opening.layers);
        let u = ring_vec(height + 1 + M);
        let v = mle_at_ring(&s, &u).expect("TE claim");
        let r_new = ring_challenges::<F, D>(b"test-dec-point", &binding, new_height + M);
        let proof = decompose_prove::<F, D, 2, 32>(&key, &opening, 2, xi, eta).expect("prove");
        let check = |proof: &DecompositionProof<F, D>, opening: &TreeOpening<F, D>, v| {
            decompose_verify::<F, D, 2, 32>(&key, proof, &u, &v, opening, 2, xi, eta, &r_new)
        };
        let honest = check(&proof, &opening, v.clone());
        assert!(honest.is_ok(), "{honest:?}");

        // (1) a plane that is not b-short
        let mut not_short = proof.clone();
        not_short.planes[0][0] = not_short.planes[0][0].clone() + embed::<F, D>(F::from(9u64));
        assert_eq!(
            check(&not_short, &opening, v.clone()),
            Err(EvalError::PlaneNotShort {
                plane: 0,
                got: 9,
                bound: 2
            })
        );

        // (2) a plane that is short but is not a decomposition of s. The edit sits
        // at index 0, inside the `0^{2nα}` prefix Eq. (31) guards, so that gate is
        // what `decompose_verify` reports — and it is a real constraint, not a
        // formality: a `b`-short set of planes is forced to recompose to a zero
        // prefix only while `b^h < q`, which is exactly the regime Eq. (31) states.
        let mut wrong_plane = proof.clone();
        wrong_plane.planes[0][0] = embed::<F, D>(F::ONE);
        let report = decompose_report(&key, &wrong_plane, &u, &v, &opening, 2, xi, eta);
        assert_eq!(report[0], EvalError::PrefixNotZero { at: 0 }, "{report:?}");
        assert_eq!(
            check(&wrong_plane, &opening, v.clone()),
            Err(EvalError::PrefixNotZero { at: 0 })
        );
        assert!(
            report.contains(&EvalError::DecompositionMismatch { at: 0 }),
            "{report:?}"
        );
        assert!(
            report.contains(&EvalError::DecompositionSideMismatch),
            "{report:?}"
        );
        assert!(
            report.contains(&EvalError::LayerClaimMismatch { level: height }),
            "{report:?}"
        );

        // (3) a forged constraint claim v_A
        let mut forged_a = proof.clone();
        forged_a.v_a = forged_a.v_a + embed::<F, D>(F::ONE);
        assert_eq!(
            check(&forged_a, &opening, v.clone()),
            Err(EvalError::DecompositionSideMismatch),
            "v_A must equal both inner products, so a forged claim is caught"
        );
        let mut forged_g = proof.clone();
        forged_g.v_g = forged_g.v_g + embed::<F, D>(F::ONE);
        assert_eq!(
            check(&forged_g, &opening, v.clone()),
            Err(EvalError::DecompositionSideMismatch)
        );

        // (4) a forged evaluation claim v — Eq. (30), read through the planes
        assert_eq!(
            check(&proof, &opening, v.clone() + embed::<F, D>(F::ONE)),
            Err(EvalError::LayerClaimMismatch { level: height }),
            "Eq. 30 is the only place the input claim is consumed"
        );

        // (5) a broken tree. Protocol 5 never re-opens the input commitment: it
        // *proves* the input's constraints through Eq. (25), so that is what a
        // severed link must trip — and nothing else.
        let mut broken = opening.clone();
        broken.layers[0][0] = broken.layers[0][0].clone() + embed::<F, D>(F::ONE);
        assert!(
            key.open(&broken, key.base()).is_err(),
            "the tamper really does break Def. 19's link"
        );
        let fresh = decompose_prove::<F, D, 2, 32>(&key, &broken, 2, xi, eta);
        match fresh {
            Ok(fresh) => {
                let broken_v = mle_at_ring(&concatenated(slot, &broken.layers), &u).expect("mle");
                assert_eq!(
                    check(&fresh, &broken, broken_v),
                    Err(EvalError::ConstraintBatchMismatch),
                    "Eq. 25 is what a broken link violates"
                );
            }
            Err(err) => panic!("a single flipped binary digit still decomposes: {err}"),
        }
        // …and with the *honest* planes against the broken tree, the recompose
        // check is what fires first, because `s` no longer recomposes to them.
        assert_eq!(
            check(&proof, &broken, v.clone()),
            Err(EvalError::DecompositionMismatch { at: 2 * slot }),
            "the edit is at the start of layer 1, past the 2nα zero prefix"
        );
    }

    #[test]
    fn pad_planes_refuses_an_overlong_plane() {
        let planes = vec![ring_vec(8), ring_vec(4)];
        let padded = pad_planes(&planes, 8).expect("padding is legal");
        assert_eq!(padded[1].len(), 8);
        assert_eq!(padded[1][4], zero_ring::<F, D>());
        assert_eq!(
            pad_planes(&planes, 6),
            Err(EvalError::WrongLength {
                got: 8,
                expected: 6
            })
        );
    }
}
