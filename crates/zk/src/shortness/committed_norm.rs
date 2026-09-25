//! A committed, norm-certifying argument over a leveled Ajtai commitment.
//!
//! This is the composed relation a self-inner-product norm proof needs in
//! *committed* form: knowledge of a short binary witness `s` such that
//!
//! ```text
//! Com(s)          = cm                      (commitment constraint)
//! ⟨coef(s), W⟩    = v                       (public-weight linear constraint)
//! ct(⟨s, σ(s)⟩)   = b   ∧   b ≤ B²          (exact ℓ2 norm constraint)
//! coef(s) ∈ {0,1}                           (binarity, through the repetitions)
//! ```
//!
//! all folded by **one** challenge sequence, so every sub-proof refers to the
//! same surviving witness and no cross-consistency checks are needed. That is
//! what closes the gap [`crate::shortness::self_ip`] documents: the round
//! messages here are the *intermediate commitments of the leveled chain*, so an
//! extractor gets a short kernel vector against values the prover is bound to
//! rather than against a free-floating witness.
//!
//! # Rounds
//!
//! `log N` rounds. Round `i ∈ [1, log N − 1]` sends
//!
//! ```text
//! π_i = ( (cm)_i , (lin)_i , (qua)_i , ( (cm̆)_i , (lin1)_i , (lin2)_i , (lin3)_i , (quă)_i )_j )
//! ```
//!
//! with `2κ·δ + 2 + 4` ring elements for the main witness and `2κ·δ + 6 + 4`
//! per binary repetition; the final round reveals the folded main witness plus
//! one folded auxiliary witness per repetition. [`verify`] runs the check
//! families in this order:
//!
//! 1. statement-level, independent of the transcript: `b ≤ B²`, and per
//!    repetition `v_r = v_r'`;
//! 2. round 1: root opening `A_{log N−1}(cm)_1 = cm`, linear exposure
//!    `ct⟨α, (lin)_1⟩ = v`, quadratic exposure `ct(L₁+R₁) = b`, and the four
//!    auxiliary exposures;
//! 3. rounds `2 … log N − 1`: each family's recursion against the previous
//!    message, weighted by the previous challenge;
//! 4. final round: the base openings, the base pairings against `a₀`, the
//!    quadratic base identities, and the two norm-admissibility gates.
//!
//! # The binary repetition
//!
//! Binarity is checked through the randomized identity
//! `⟨s̆∘α, s̆⟩ = ⟨s̆, α⟩` of [`crate::shortness::tensor_fold`], written as four
//! constraints over `s̆ := coef(s)`, `s̃ := embed(s̆∘α)` and `s̆_de := G⁻¹(s̃)`:
//!
//! ```text
//! (lin1)  <coef(s), r_alpha> = v_r       [main witness, the r-times-alpha vector]
//! (lin2)  <coef(G s_de), r> = v_r'       v_r = v_r'  binds G s_de to s o alpha
//! (lin3)  ⟨coef(s),   α    ⟩  = v_α      (quă) ct⟨s̃, σ(s)⟩ = v_α
//! ```
//!
//! `(quă)` is genuinely **bilinear**: its two slots are the auxiliary value
//! vector and the *main* witness, so `ct⟨s̃, σ(s)⟩ = ⟨s̆∘α, s̆⟩`, which equals
//! `v_α` exactly when `s̆` is binary. `(lin1)` is the *same* functional read on
//! the **main** witness, because `r⃗ ∘ α = (1, rα, (rα)², …)` is again a power
//! vector; `(lin2)` reads it off the committed decomposition. Their equality is
//! therefore a randomized fingerprint (in `r`, drawn **after** `cm̆` is fixed —
//! §3.3 "Commitment order", p. 13) of `G·s̆_de = s̃ = s̆ ∘ α`, which is what makes
//! `(quă)` read `Σ αₖ sₖ² = Σ αₖ sₖ`, i.e. binarity. Comparing the decomposition
//! against a *prover-supplied* `s̃` instead — which is what this module did
//! before — is an identity in the prover's own free variable: it holds for
//! every `s̃`, leaves `s̃` unbound to `s`, and a prover with a non-binary `s`
//! escapes by sending `s̃ := s∘α + β⃗` with `⟨β⃗, s⟩ = 0`.
//! `a_non_binary_witness_with_a_crafted_auxiliary_vector_is_caught_by_r` is the
//! regression test.
//!
//! Each randomized reduction costs `≤ 2·(Nd)/q` in soundness, so a scheme
//! repeats it `t` times with fresh variables and checks each repetition's own
//! claims; [`crate::shortness::tensor_fold::NormAccounting::repetitions`]
//! derives `t`.
//!
//! # What the last message round does *not* check (Fig. 3, p. 17)
//!
//! For `i ∈ [2 : log N − 1]` the quadratic column is
//! `(1,0,0,1) · π_i =? <c_qua(i−1), π_(i−1)>`: only `L_i + R_i` of the *current*
//! message is constrained, and the cross terms `M1_i`, `M2_i` are checked
//! **nowhere else at round `i`**. They are pinned one step later — by the next
//! round's right-hand side, and for the *last* message round by the final-round
//! identities `<s_log N, σ(s_log N)> = <c_qua, π_(log N − 1)>` and
//! `<G ŝ_α,log N, σ(s_log N)> = <c_qua, π^(qua,α)_(log N−1)>`, whose weight
//! vector `c_qua = (c₀σ(c₀), c₀σ(c₁), c₁σ(c₀), c₁σ(c₁))` has all four entries
//! non-zero. Appendix C step II (p. 40) says why there is no per-round claim for
//! them: the four components are recovered as the coefficients of a degree-2
//! polynomial in the challenge, so *that* identity is the check, at a cost of
//! `2 log N/|C|`. A tamper on the last message round's `quad[1]` is therefore
//! reported by [`verify_report`] as `aux-quadratic` **at the final round**, not
//! as a mismatch at its own round — which is what
//! `a_later_round_forgery_is_caught_by_the_recursion` asserts, for both
//! tampers, as an exact set.
//!
//! That is a reading of the paper, not a convenience. Case 2's header is
//! `i ∈ {2, …, log N − 1}`, so the last *message* round is quantified in like
//! any other and the only asymmetry is that no later round exists to read its
//! `M₁, M₂` — which is precisely what case 3's two quadratic identities are
//! for. Adding a per-round claim on the cross terms would be a check the paper
//! does not specify, and the assertion that `aux-quadratic` is **absent** at
//! round `log N − 1` is what stops this module from inventing one.
//!
//! # Reporting every failure
//!
//! [`verify`] returns the first rejection; [`verify_report`] returns all of them
//! with [`NormError::check_id`]. Under Fiat–Shamir every message is absorbed
//! before the next challenge, so one tamper cascades and trips many checks:
//! a single-error verifier cannot distinguish "checked and failed" from "never
//! reached", and a check that never fires is indistinguishable from dead code.
//! Same reasoning as `pcs::dotproduct::verify_core_report` and the
//! `examples/cmnw.rs` assembly.

use crate::pcs::gadget::join;
use crate::pcs::leveled::{fold_with, LeveledAjtai, LeveledError};
use crate::shortness::tensor_fold::{
    ct, flatten, herm, linear_base, linear_expose, linear_msg, linear_recursion, quad_base,
    quad_carry, quad_expose, quad_msg, square_sum, Elt, FoldError, LinearWeights,
};
use algebra::crypto::sampling::BitStream;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::traits::CenteredRing;
use algebra::ring::Ring;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Which chain a message belongs to: the main witness, or binary repetition
/// number `j`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Chain {
    /// The committed witness itself.
    Main,
    /// Auxiliary witness of binary repetition `j`.
    Binary(usize),
}

impl fmt::Display for Chain {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Chain::Main => write!(f, "main"),
            Chain::Binary(j) => write!(f, "binary[{j}]"),
        }
    }
}

/// Which constraint family rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Family {
    /// The public-weight linear claim on the main witness.
    Linear,
    /// The self-inner-product (norm) claim on the main witness.
    Quadratic,
    /// `lin1`: `<coef(s), r*alpha>` on the MAIN witness — the value side of the
    /// well-formedness fingerprint (§3.3 item 3).
    AuxValue,
    /// `lin2`: `⟨coef(s̆_de), α_r'⟩` (the `r`-weight on the digit planes), the same functional as `(lin1)`, read
    /// through the committed decomposition (§3.3 item 4).
    AuxDigit,
    /// `lin3`: `⟨coef(s), α⟩`, the binarity claim.
    AuxBinarity,
    /// `(quă)`: the bilinear `ct⟨s̃, σ(s)⟩`.
    AuxQuadratic,
}

impl Family {
    /// The family's name, as it appears in a [`CheckId`].
    #[must_use]
    pub const fn name(&self) -> &'static str {
        match self {
            Family::Linear => "linear",
            Family::Quadratic => "quadratic",
            Family::AuxValue => "aux-value",
            Family::AuxDigit => "aux-digit",
            Family::AuxBinarity => "aux-binarity",
            Family::AuxQuadratic => "aux-quadratic",
        }
    }
}

impl fmt::Display for Family {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name())
    }
}

/// Which named check of Fig. 3 rejected, with the observed values stripped.
///
/// A tamper under Fiat-Shamir moves every later challenge, so several checks
/// fail at once and only the *set* of their identities says which ones actually
/// ran. Compare [`crate::pcs::dotproduct::verify_core_report`] and the
/// `examples/cmnw.rs` assembly.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CheckId {
    /// The check lane: a [`Family`] name, or one of `"commitment"`,
    /// `"statement-bound"`, `"wraparound"`, `"well-formed"`, `"tail-short"`,
    /// `"shape"`, `"setup"`.
    pub lane: &'static str,
    /// Which chain.
    pub chain: Chain,
    /// Fig. 3's round index, `1 ..= log N`; `0` for the statement-level checks,
    /// which have no round.
    pub round: usize,
}

impl fmt::Display for CheckId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.round == 0 {
            write!(f, "{}/{}", self.chain, self.lane)
        } else {
            write!(f, "{}/{}@{}", self.chain, self.lane, self.round)
        }
    }
}

/// Why the argument refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum NormError {
    /// A message did not have the shape the round requires.
    Length {
        /// Length supplied.
        got: usize,
        /// Length the round requires.
        expected: usize,
        /// Which slot.
        slot: &'static str,
    },
    /// The norm claim is above the declared bound, so nothing is certified.
    StatementBound {
        /// The claimed squared norm.
        claim: u128,
        /// `B²`.
        max: u128,
    },
    /// Lemma 2 (p. 8) is only an `ℓ2` statement while the claim cannot wrap:
    /// the bound reaches the modulus, so `ct(⟨s,σ(s)⟩) = b` is satisfied by
    /// `b` and by `b + q` and the proof certifies neither.
    NotAdmissible {
        /// The bound `B²` that failed to stay under the modulus.
        limit: u128,
        /// The modulus.
        modulus: u64,
    },
    /// A leveled-chain consistency check failed.
    Commitment {
        /// Which chain.
        chain: Chain,
        /// Round index.
        round: usize,
        /// The specific chain check that failed.
        source: LeveledError,
    },
    /// A linear or quadratic check failed.
    Constraint {
        /// Which family.
        family: Family,
        /// Which chain (binary repetitions are indexed).
        chain: Chain,
        /// Round index.
        round: usize,
        /// The engine's own diagnosis.
        source: FoldError,
    },
    /// `v_r ≠ v_r'`: the committed auxiliary witness is not a decomposition of
    /// the value vector the other constraints refer to.
    WellFormed {
        /// Repetition index.
        repetition: usize,
        /// What the value-side claim said.
        v_r: u64,
        /// What the digit-side claim said.
        v_r_prime: u64,
    },
    /// A revealed tail exceeded its admissible norm, so the binding argument
    /// does not apply to it.
    NotShort {
        /// Which chain's tail.
        chain: Chain,
        /// Exact squared norm of the tail.
        norm_sq: u128,
        /// Admissible squared bound.
        bound_sq: u128,
    },
    /// Two objects the caller passed in disagree, so no proof could mean
    /// anything.
    BadSetup(&'static str),
    /// A chain refused to commit its witness at all: the shapes handed in do
    /// not form a chain. Carries the chain's own diagnosis.
    CommitmentSetup(LeveledError),
}

impl fmt::Display for NormError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NormError::Length {
                got,
                expected,
                slot,
            } => {
                write!(f, "{slot}: got {got}, expected {expected}")
            }
            NormError::StatementBound { claim, max } => {
                write!(f, "norm claim {claim} exceeds the bound {max}")
            }
            NormError::NotAdmissible { limit, modulus } => write!(
                f,
                "the bound {limit} reaches q = {modulus}, so the norm claim is ambiguous mod q"
            ),
            NormError::Commitment {
                chain,
                round,
                source,
            } => write!(f, "{chain} chain, round {round}: {source}"),
            NormError::Constraint {
                family,
                chain,
                round,
                source,
            } => write!(f, "{chain} {family} constraint, round {round}: {source}"),
            NormError::WellFormed {
                repetition,
                v_r,
                v_r_prime,
            } => write!(
                f,
                "binary[{repetition}]: v_r = {v_r} but the digit-side claim is {v_r_prime}"
            ),
            NormError::NotShort {
                chain,
                norm_sq,
                bound_sq,
            } => write!(
                f,
                "{chain} tail has squared norm {norm_sq}, above the admissible {bound_sq}"
            ),
            NormError::BadSetup(why) => write!(f, "inconsistent setup: {why}"),
            NormError::CommitmentSetup(source) => {
                write!(f, "chain could not be built: {source}")
            }
        }
    }
}

impl NormError {
    /// Which named check produced this rejection.
    ///
    /// `final_round` is `log N`, the index Fig. 3 gives the base-opening and
    /// admissibility checks; the variants themselves do not carry it.
    #[must_use]
    pub fn check_id(&self, final_round: usize) -> CheckId {
        let (lane, chain, round) = match self {
            NormError::Length { .. } => ("shape", Chain::Main, 0),
            NormError::StatementBound { .. } => ("statement-bound", Chain::Main, 0),
            NormError::NotAdmissible { .. } => ("wraparound", Chain::Main, 0),
            NormError::Commitment { chain, round, .. } => ("commitment", *chain, *round),
            NormError::Constraint {
                family,
                chain,
                round,
                ..
            } => (family.name(), *chain, *round),
            NormError::WellFormed { repetition, .. } => {
                ("well-formed", Chain::Binary(*repetition), 0)
            }
            NormError::NotShort { chain, .. } => ("tail-short", *chain, final_round),
            NormError::BadSetup(_) | NormError::CommitmentSetup(_) => ("setup", Chain::Main, 0),
        };
        CheckId { lane, chain, round }
    }
}

/// The main witness, its leveled commitment and the linear claim's weights.
///
/// Built by [`MainBundle::new`], which runs the chain and keeps the prover's
/// private intermediate states — the objects the round messages are folded
/// from.
#[derive(Clone)]
pub struct MainBundle<R: Ring, const D: usize, const DIGITS: usize> {
    chain: LeveledAjtai<R, D, DIGITS>,
    witness: Vec<Elt<R, D>>,
    states: Vec<Vec<Elt<R, D>>>,
    root: Vec<Elt<R, D>>,
    weights: LinearWeights<R, D>,
    bound_sq: u128,
    tail_bound_sq: u128,
}

impl<R, const D: usize, const DIGITS: usize> MainBundle<R, D, DIGITS>
where
    R: CenteredRing,
{
    /// Commits `witness` through `chain` and binds the linear weight table to
    /// it.
    ///
    /// `bound_sq` is `B²`, the largest squared norm the *claim* may assert;
    /// `tail_bound_sq` is the admissibility bound on the *revealed* folded
    /// witness, which is a different quantity (the former is a statement about
    /// the committed vector, the latter the growth the folding causes).
    ///
    /// # Errors
    /// [`NormError::Length`] if the witness or the weight table does not match
    /// the chain, [`NormError::BadSetup`] if the chain's states do not line up
    /// with its level count or the weight table has the wrong length,
    /// [`NormError::NotAdmissible`] if `bound_sq` reaches the modulus (Lemma 2,
    /// p. 8 — the claim would be ambiguous mod `q`).
    pub fn new(
        chain: LeveledAjtai<R, D, DIGITS>,
        witness: &[Elt<R, D>],
        weights: LinearWeights<R, D>,
        bound_sq: u128,
        tail_bound_sq: u128,
    ) -> Result<Self, NormError> {
        if witness.len() != chain.witness_len() {
            return Err(NormError::Length {
                got: witness.len(),
                expected: chain.witness_len(),
                slot: "main witness",
            });
        }
        if weights.len() != witness.len() {
            return Err(NormError::BadSetup(
                "linear weight length differs from the witness",
            ));
        }
        if !crate::shortness::exact_l2::direct_route_admissible::<R>(bound_sq) {
            return Err(NormError::NotAdmissible {
                limit: bound_sq,
                modulus: R::MODULUS,
            });
        }
        let (root, states) = chain.commit(witness).map_err(NormError::CommitmentSetup)?;
        if states.len() + 1 != chain.levels() {
            return Err(NormError::BadSetup(
                "chain produced the wrong number of states",
            ));
        }
        Ok(Self {
            chain,
            witness: witness.to_vec(),
            states,
            root,
            weights,
            bound_sq,
            tail_bound_sq,
        })
    }

    /// The chain.
    pub fn chain(&self) -> &LeveledAjtai<R, D, DIGITS> {
        &self.chain
    }

    /// The committed witness.
    pub fn witness(&self) -> &[Elt<R, D>] {
        &self.witness
    }

    /// The commitment root.
    pub fn root(&self) -> &[Elt<R, D>] {
        &self.root
    }

    /// The linear weight table.
    pub fn weights(&self) -> &LinearWeights<R, D> {
        &self.weights
    }

    /// `B²`.
    pub fn bound_sq(&self) -> u128 {
        self.bound_sq
    }

    /// The admissibility bound on the revealed folded tail, `B_tail²` — the
    /// growth the folding itself causes, which is what [`verify`] gates the
    /// final round against.
    pub fn tail_bound_sq(&self) -> u128 {
        self.tail_bound_sq
    }

    /// The exact integer squared norm of the witness — the honest value of the
    /// claim `b`.
    ///
    /// # Errors
    /// [`NormError::NotShort`] if it is above `B²`, so a prover cannot even
    /// build a statement for an oversized witness.
    pub fn norm_claim(&self) -> Result<u64, NormError> {
        let sq = square_sum(&self.witness).map_err(|_| NormError::BadSetup("norm overflow"))?;
        if sq > self.bound_sq {
            return Err(NormError::NotShort {
                chain: Chain::Main,
                norm_sq: sq,
                bound_sq: self.bound_sq,
            });
        }
        u64::try_from(sq).map_err(|_| NormError::BadSetup("norm claim exceeds u64"))
    }
}

/// One binary-check repetition: the committed auxiliary decomposition and the
/// three weight tables it is checked through.
#[derive(Clone)]
pub struct BinaryBundle<R: Ring, const D: usize, const DIGITS: usize> {
    chain: LeveledAjtai<R, D, DIGITS>,
    digits: Vec<Elt<R, D>>,
    tilde: Vec<Elt<R, D>>,
    states: Vec<Vec<Elt<R, D>>>,
    root: Vec<Elt<R, D>>,
    w_value: LinearWeights<R, D>,
    w_digit: LinearWeights<R, D>,
    w_binarity: LinearWeights<R, D>,
    tail_bound_sq: u128,
}

impl<R, const D: usize, const DIGITS: usize> BinaryBundle<R, D, DIGITS>
where
    R: CenteredRing,
{
    /// Decomposes `tilde` with the chain's gadget and commits the result.
    ///
    /// `tilde` is `embed(coef(s)∘α)`: the binarity weight applied
    /// coefficient-wise to the main witness. Its decomposition is what the
    /// auxiliary chain binds, and the *only* thing that binds `tilde` itself to
    /// the main witness is the `r`-fingerprint of §3.3 item 4 — which is why
    /// `w_value` must be the weight of the **main** witness (the `r ∘ α` power
    /// vector, i.e. base `r·α`), not a second reading of `tilde`.
    ///
    /// There is deliberately no statement-level norm bound here: Fig. 3 has no
    /// `b_α ≤ B_α²` check, because the auxiliary claims `v_r`, `v_{r_α}`, `v_α`
    /// are ring equalities, and §3.3 (p. 13) only needs "a loose norm bound on
    /// ŝ_α", which is what `tail_bound_sq` supplies at the base opening.
    ///
    /// # Errors
    /// As [`MainBundle::new`].
    #[allow(clippy::too_many_arguments, reason = "one bundle carries every lane")]
    pub fn new(
        chain: LeveledAjtai<R, D, DIGITS>,
        tilde: &[Elt<R, D>],
        w_value: LinearWeights<R, D>,
        w_digit: LinearWeights<R, D>,
        w_binarity: LinearWeights<R, D>,
        tail_bound_sq: u128,
    ) -> Result<Self, NormError> {
        if tilde.len() * DIGITS != chain.witness_len() {
            return Err(NormError::Length {
                got: tilde.len(),
                expected: chain.witness_len() / DIGITS,
                slot: "auxiliary value vector",
            });
        }
        if w_value.len() != tilde.len() {
            return Err(NormError::BadSetup(
                "value weight length differs from the main witness",
            ));
        }
        if w_binarity.len() != tilde.len() {
            return Err(NormError::BadSetup(
                "binarity weight length differs from s~",
            ));
        }
        let digits = crate::pcs::gadget::split::<R, D, 2, DIGITS>(tilde);
        if w_digit.len() != digits.len() {
            return Err(NormError::BadSetup(
                "digit weight length differs from the decomposition",
            ));
        }
        let (root, states) = chain.commit(&digits).map_err(NormError::CommitmentSetup)?;
        if states.len() + 1 != chain.levels() {
            return Err(NormError::BadSetup("auxiliary chain states disagree"));
        }
        Ok(Self {
            chain,
            digits,
            tilde: tilde.to_vec(),
            states,
            root,
            w_value,
            w_digit,
            w_binarity,
            tail_bound_sq,
        })
    }

    /// The admissibility bound on this repetition's revealed folded tail.
    pub fn tail_bound_sq(&self) -> u128 {
        self.tail_bound_sq
    }

    /// The auxiliary commitment root.
    pub fn root(&self) -> &[Elt<R, D>] {
        &self.root
    }

    /// The weight table of the binarity claim `α`.
    pub fn w_binarity(&self) -> &LinearWeights<R, D> {
        &self.w_binarity
    }

    /// `v_α = ⟨coef(s), α⃗⟩` and `v_r = ⟨coef(s), r⃗  α⃗⟩` for the main witness,
    /// and `v_r' = ⟨coef(G ŝ_α), r⃗⟩` for this repetition's committed
    /// decomposition. All three are derived here, never supplied by a caller.
    ///
    /// `v_r` and `v_r'` are the two sides of §3.3 item 4 and they live on
    /// **different** witnesses: their equality is the fingerprint, so the
    /// verifier's `v_r = v_r'` gate is what binds `cm̆` to `s`.
    ///
    /// # Errors
    /// [`NormError::Constraint`] if a weight table cannot be built for the
    /// round it is first needed in.
    pub fn claims(&self, main: &MainBundle<R, D, DIGITS>) -> Result<AuxClaims<R>, NormError> {
        let rounds = main.chain().levels() - 1;
        let full = |w: &LinearWeights<R, D>| w.weight(rounds);
        let v_alpha = ct(&herm(
            main.witness(),
            &full(&self.w_binarity).map_err(|e| err(Family::AuxBinarity, Chain::Main, 1, e))?,
        ));
        let v_r = ct(&herm(
            main.witness(),
            &full(&self.w_value).map_err(|e| err(Family::AuxValue, Chain::Main, 1, e))?,
        ));
        let v_r_prime = ct(&herm(
            &self.digits,
            &full(&self.w_digit).map_err(|e| err(Family::AuxDigit, Chain::Main, 1, e))?,
        ));
        Ok(AuxClaims {
            v_alpha,
            v_r,
            v_r_prime,
        })
    }
}

/// Public statement: everything the verifier holds before the proof.
#[derive(Clone, PartialEq, Eq)]
pub struct Statement<R: Ring, const D: usize> {
    /// Commitment to the witness.
    pub cm: Vec<Elt<R, D>>,
    /// The linear claim, e.g. an evaluation value.
    pub v: R,
    /// The squared-norm claim, as an exact integer.
    pub b: u64,
    /// Per-repetition auxiliary commitment and claims.
    pub aux: Vec<AuxStatement<R, D>>,
}

impl<R: Ring, const D: usize> fmt::Debug for Statement<R, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Statement")
            .field("cm_len", &self.cm.len())
            .field("b", &self.b)
            .field("repetitions", &self.aux.len())
            .finish()
    }
}

/// The three scalar claims of one binary repetition.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AuxClaims<R> {
    /// `v_α = ⟨coef(s), α⟩`, the binarity claim.
    pub v_alpha: R,
    /// `v_r = <coef(s), r*alpha>` on the MAIN witness (§3.3 item 3).
    pub v_r: R,
    /// `v_r' = <coef(G s_de), r>` on the committed decomposition, which must
    /// equal `v_r` — the fingerprint that binds the two (§3.3 item 4).
    pub v_r_prime: R,
}

/// One repetition's public claims, including its commitment.
#[derive(Clone, PartialEq, Eq)]
pub struct AuxStatement<R: Ring, const D: usize> {
    /// Commitment to the auxiliary decomposition.
    pub root: Vec<Elt<R, D>>,
    /// The three scalar claims.
    pub claims: AuxClaims<R>,
}

/// One round's message.
#[derive(Clone, PartialEq, Eq)]
pub struct RoundMessage<R: Ring, const D: usize> {
    /// Folded intermediate commitment of the main chain.
    pub commit: Vec<Elt<R, D>>,
    /// `(v_L, v_R)` of the linear claim.
    pub linear: [Elt<R, D>; 2],
    /// `(L, M₁, M₂, R)` of the norm claim.
    pub quad: [Elt<R, D>; 4],
    /// One entry per binary repetition.
    pub aux: Vec<AuxRoundMessage<R, D>>,
}

/// A binary repetition's round message.
#[derive(Clone, PartialEq, Eq)]
pub struct AuxRoundMessage<R: Ring, const D: usize> {
    /// Folded intermediate commitment of the auxiliary chain.
    pub commit: Vec<Elt<R, D>>,
    /// `(lin1, lin2, lin3)`.
    pub lin: [[Elt<R, D>; 2]; 3],
    /// The bilinear message pairing `s̃` (slot 1) with `s` (slot 2).
    pub quad: [Elt<R, D>; 4],
}

/// A completed argument: `log N − 1` rounds plus the revealed tails.
#[derive(Clone, PartialEq, Eq)]
pub struct NormProof<R: Ring, const D: usize> {
    /// Rounds `1 … log N − 1`.
    pub rounds: Vec<RoundMessage<R, D>>,
    /// The folded main witness.
    pub tail: Vec<Elt<R, D>>,
    /// One folded auxiliary decomposition per repetition.
    pub aux_tails: Vec<Vec<Elt<R, D>>>,
}

/// Proof size in ring elements, counted from the message shapes.
///
/// §3.6, p. 21 counts the transcript as `(2κι + 6) + t·(2κι + 10)` ring
/// elements per message round plus `2ℓ + 2tℓια` in the final round. The `+6` is
/// `π^(lin)` (2 elements) plus `π^(qua)` (4); the `+10` is §3.3, p. 14's
/// `π_i^(bin) = (π^(cm,α), π^(lin1,α), π^(lin2,α), π^(lin3,α), π^(qua,α)) ∈
/// R_q^{2κι+10}`, i.e. **three** 2-element linear openings plus the 4-element
/// bilinear one. Counting the arrays instead of restating those constants is the
/// point: a hardcoded `+8` here silently dropped one of the three linear pairs
/// and desynchronised this number from the paper by `2 · t · (log N − 1)`
/// elements. A caller asserts the paper's shape against this measurement, so the
/// two cannot drift together.
#[must_use]
pub fn proof_size<R: Ring, const D: usize>(proof: &NormProof<R, D>) -> usize {
    let pair_count = |pairs: &[[Elt<R, D>; 2]]| pairs.iter().map(|p| p.len()).sum::<usize>();
    proof
        .rounds
        .iter()
        .map(|r| {
            r.commit.len()
                + r.linear.len()
                + r.quad.len()
                + r.aux
                    .iter()
                    .map(|a| a.commit.len() + pair_count(&a.lin) + a.quad.len())
                    .sum::<usize>()
        })
        .sum::<usize>()
        + proof.tail.len()
        + proof.aux_tails.iter().map(|t| t.len()).sum::<usize>()
}

/// Transcript domain separation for the challenge sequence.
const FS_DOMAIN: &[u8] = b"lattice-algebra/Z5/committed-norm";

/// Absorbs a vector of ring elements as raw coefficient bytes.
fn absorb<R: Ring, const D: usize>(tr: &mut Transcript<Shake256Xof>, slot: &[u8], v: &[Elt<R, D>]) {
    for e in v {
        let bytes: Vec<u8> = flatten(&[e.clone()])
            .iter()
            .flat_map(|c| u64::try_from(c.to_u128()).unwrap_or(0).to_le_bytes())
            .collect();
        tr.absorb(slot, &bytes);
    }
}

fn absorb_scalar(tr: &mut Transcript<Shake256Xof>, slot: &[u8], v: u64) {
    tr.absorb(slot, &v.to_le_bytes());
}

/// Derives the round challenge bound to the statement and to every message up
/// to and including `π_through`, so no message can be chosen after its own
/// challenge is known.
fn challenge_at<R, const D: usize>(
    statement: &Statement<R, D>,
    rounds: &[RoundMessage<R, D>],
    through: usize,
    w1: u32,
    w2: u32,
) -> [Elt<R, D>; 2]
where
    R: Ring,
{
    let mut tr = Transcript::<Shake256Xof>::new(FS_DOMAIN);
    absorb(&mut tr, b"cm", &statement.cm);
    absorb_scalar(&mut tr, b"b", statement.b);
    absorb_scalar(
        &mut tr,
        b"v",
        u64::try_from(statement.v.to_u128()).unwrap_or(0),
    );
    for a in &statement.aux {
        absorb(&mut tr, b"aux-cm", &a.root);
        absorb_scalar(
            &mut tr,
            b"v-alpha",
            u64::try_from(a.claims.v_alpha.to_u128()).unwrap_or(0),
        );
        absorb_scalar(
            &mut tr,
            b"v-r",
            u64::try_from(a.claims.v_r.to_u128()).unwrap_or(0),
        );
        absorb_scalar(
            &mut tr,
            b"v-r-prime",
            u64::try_from(a.claims.v_r_prime.to_u128()).unwrap_or(0),
        );
    }
    for msg in rounds.iter().take(through) {
        absorb(&mut tr, b"commit", &msg.commit);
        absorb(&mut tr, b"lin", &msg.linear);
        absorb(&mut tr, b"quad", &msg.quad);
        for a in &msg.aux {
            absorb(&mut tr, b"aux-commit", &a.commit);
            for pair in &a.lin {
                absorb(&mut tr, b"aux-lin", pair);
            }
            absorb(&mut tr, b"aux-quad", &a.quad);
        }
    }
    absorb_scalar(&mut tr, b"through", through as u64);
    let seed = tr.challenge_bytes(64);
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(b"C");
    xof.absorb(&seed);
    let mut stream = BitStream::new(&mut xof);
    let draw = |stream: &mut BitStream<'_, Shake256Xof>| {
        crate::shortness::tensor_fold::pool_challenge::<R, Shake256Xof, D>(stream, w1, w2)
    };
    let c0 = draw(&mut stream).expect("challenge pool must fit the ring degree");
    let c1 = draw(&mut stream).expect("challenge pool must fit the ring degree");
    [c0, c1]
}

/// The full challenge sequence for `log N − 1` rounds, each bound to every
/// message sent before it.
fn challenges<R, const D: usize>(
    statement: &Statement<R, D>,
    rounds: &[RoundMessage<R, D>],
    w1: u32,
    w2: u32,
) -> Vec<[Elt<R, D>; 2]>
where
    R: Ring,
{
    (1..=rounds.len())
        .map(|i| challenge_at(statement, rounds, i, w1, w2))
        .collect()
}

/// Proves the relation, returning the statement the proof satisfies and the
/// proof. Every claim is computed from the witness, so a prover cannot ask to
/// prove a value it does not have.
///
/// `w1`/`w2` size the challenge pool (see
/// [`crate::shortness::tensor_fold::pool_challenge`]).
///
/// # Errors
/// [`NormError::BadSetup`] for inconsistent inputs, [`NormError::Length`] when
/// a state cannot be halved, [`NormError::Constraint`] when a weight table
/// cannot be built.
pub fn prove<R, const D: usize, const DIGITS: usize>(
    main: &MainBundle<R, D, DIGITS>,
    binary: &[BinaryBundle<R, D, DIGITS>],
    w1: u32,
    w2: u32,
) -> Result<(Statement<R, D>, NormProof<R, D>), NormError>
where
    R: CenteredRing,
{
    let levels = main.chain().levels();
    if levels < 2 {
        return Err(NormError::BadSetup("the chain needs at least two levels"));
    }
    let rounds = levels - 1;
    let statement = {
        let mut aux = Vec::with_capacity(binary.len());
        for bundle in binary {
            aux.push(AuxStatement {
                root: bundle.root().to_vec(),
                claims: bundle.claims(main)?,
            });
        }
        Statement {
            cm: main.root().to_vec(),
            v: ct(&herm(
                main.witness(),
                &main
                    .weights()
                    .weight(rounds)
                    .map_err(|e| err(Family::Linear, Chain::Main, 1, e))?,
            )),
            b: main.norm_claim()?,
            aux,
        }
    };

    let mut msgs: Vec<RoundMessage<R, D>> = Vec::with_capacity(rounds);
    let mut state = main.witness().to_vec();
    let mut tildes: Vec<Vec<Elt<R, D>>> = binary.iter().map(|b| b.tilde.clone()).collect();
    let mut digits: Vec<Vec<Elt<R, D>>> = binary.iter().map(|b| b.digits.clone()).collect();
    let mut cs: Vec<[Elt<R, D>; 2]> = Vec::with_capacity(rounds);
    for i in 0..rounds {
        let half = state.len() / 2;
        let commit = main.chain.fold_state(&main.states[levels - 2 - i], &cs);
        let child = main
            .weights
            .weight(rounds - 1 - i)
            .map_err(|e| err(Family::Linear, Chain::Main, i + 1, e))?;
        if child.len() * 2 != state.len() {
            return Err(NormError::BadSetup(
                "linear weight does not halve with the state",
            ));
        }
        let linear =
            linear_msg(&state, &child).map_err(|e| err(Family::Linear, Chain::Main, i + 1, e))?;
        let quad =
            quad_msg(&state, &state).map_err(|e| err(Family::Quadratic, Chain::Main, i + 1, e))?;
        let mut aux_msgs = Vec::with_capacity(binary.len());
        for (j, bundle) in binary.iter().enumerate() {
            let a_commit = bundle.chain.fold_state(&bundle.states[levels - 2 - i], &cs);
            let tilde = tildes[j].clone();
            let digit = digits[j].clone();
            // `lin1` is the fingerprint's *value* side, which §3.3 item 3 puts
            // on the main witness: `w_value` is the `r ∘ α` power vector, so
            // `v_r = Σ sₖ (rα)ᵏ`. Reading it off `tilde` instead — what this
            // line used to do — makes `v_r = v_r'` an identity in the prover's
            // own free variable and unbinds the auxiliary commitment from `s`.
            let lin1 = aux_linear(
                &state,
                &bundle.w_value,
                rounds - 1 - i,
                Family::AuxValue,
                j,
                i + 1,
            )?;
            let lin2 = aux_linear(
                &digit,
                &bundle.w_digit,
                rounds - 1 - i,
                Family::AuxDigit,
                j,
                i + 1,
            )?;
            // `lin3` is the binarity claim, which lives on the *main* witness.
            let lin3 = aux_linear(
                &state,
                &bundle.w_binarity,
                rounds - 1 - i,
                Family::AuxBinarity,
                j,
                i + 1,
            )?;
            let a_quad = quad_msg(&tilde, &state)
                .map_err(|e| err(Family::AuxQuadratic, Chain::Binary(j), i + 1, e))?;
            aux_msgs.push(AuxRoundMessage {
                commit: a_commit,
                lin: [lin1, lin2, lin3],
                quad: a_quad,
            });
        }
        msgs.push(RoundMessage {
            commit,
            linear,
            quad,
            aux: aux_msgs,
        });
        let c = challenge_at(&statement, &msgs, msgs.len(), w1, w2);
        cs.push(c.clone());
        state = fold_with(&state[..half], &state[half..], &c);
        for tilde in &mut tildes {
            let h = tilde.len() / 2;
            *tilde = fold_with(&tilde[..h], &tilde[h..], &c);
        }
        for digit in &mut digits {
            let h = digit.len() / 2;
            *digit = fold_with(&digit[..h], &digit[h..], &c);
        }
    }
    Ok((
        statement,
        NormProof {
            rounds: msgs,
            tail: state,
            aux_tails: digits,
        },
    ))
}

/// One round of an auxiliary linear lane: the message pair of `state` against
/// the weight table at nesting `outer`.
///
/// # Errors
/// [`NormError::Length`] if the state does not halve with the weight table,
/// [`NormError::Constraint`] carrying the round's own failure.
fn aux_linear<R, const D: usize>(
    state: &[Elt<R, D>],
    weights: &LinearWeights<R, D>,
    outer: usize,
    family: Family,
    repetition: usize,
    round: usize,
) -> Result<[Elt<R, D>; 2], NormError>
where
    R: CenteredRing,
{
    let child = weights
        .weight(outer)
        .map_err(|e| err(family, Chain::Binary(repetition), round, e))?;
    if child.len() * 2 != state.len() {
        return Err(NormError::Length {
            got: state.len(),
            expected: child.len() * 2,
            slot: "auxiliary linear state",
        });
    }
    linear_msg(state, &child).map_err(|e| err(family, Chain::Binary(repetition), round, e))
}

fn err(family: Family, chain: Chain, round: usize, source: FoldError) -> NormError {
    NormError::Constraint {
        family,
        chain,
        round,
        source,
    }
}

fn commit_err(chain: Chain, round: usize, source: LeveledError) -> NormError {
    NormError::Commitment {
        chain,
        round,
        source,
    }
}

fn to_u64<R: Ring>(c: R) -> u64 {
    u64::try_from(c.to_u128()).unwrap_or(u64::MAX)
}

/// Records one check's refusal, so the report can hold them all.
fn record(out: &mut Vec<NormError>, check: Result<(), NormError>) {
    if let Err(e) = check {
        out.push(e);
    }
}

/// Verifier: **every** check Fig. 3 prints, in check order, as a set.
///
/// The families run in this order: statement-level gates, then per round the
/// chain step / linear step / quadratic step of the main witness and of each
/// repetition, then the final round's base openings and admissibility gates.
/// Shape gates return early — nothing below them is well-defined — and every
/// other refusal is collected.
///
/// # Errors
/// See [`NormError`]. Each rejection names its chain, family and round, and
/// [`NormError::check_id`] turns it into the identity to assert against.
#[must_use]
pub fn verify_report<R, const D: usize, const DIGITS: usize>(
    statement: &Statement<R, D>,
    proof: &NormProof<R, D>,
    main: &MainBundle<R, D, DIGITS>,
    binary: &[BinaryBundle<R, D, DIGITS>],
    w1: u32,
    w2: u32,
) -> Vec<NormError>
where
    R: CenteredRing,
{
    let levels = main.chain().levels();
    let rounds = levels - 1;
    if proof.rounds.len() != rounds {
        return vec![NormError::Length {
            got: proof.rounds.len(),
            expected: rounds,
            slot: "round count",
        }];
    }
    if proof.aux_tails.len() != binary.len() || statement.aux.len() != binary.len() {
        return vec![NormError::Length {
            got: statement.aux.len(),
            expected: binary.len(),
            slot: "repetition count",
        }];
    }
    if proof.rounds.iter().any(|msg| msg.aux.len() != binary.len()) {
        return vec![NormError::Length {
            got: proof.rounds.first().map_or(0, |msg| msg.aux.len()),
            expected: binary.len(),
            slot: "per-round repetitions",
        }];
    }
    let mut out = Vec::new();
    // --- 1. statement-level checks, independent of the transcript ---
    record(
        &mut out,
        (|| {
            // Lemma 2 (p. 8): the self-inner-product claim *is* an `ℓ2` statement
            // only while it cannot wrap, so a bound that reaches `q` voids the
            // argument no matter what the transcript says.
            if crate::shortness::exact_l2::direct_route_admissible::<R>(main.bound_sq()) {
                Ok(())
            } else {
                Err(NormError::NotAdmissible {
                    limit: main.bound_sq(),
                    modulus: R::MODULUS,
                })
            }
        })(),
    );
    record(
        &mut out,
        (|| {
            if u128::from(statement.b) > main.bound_sq() {
                return Err(NormError::StatementBound {
                    claim: u128::from(statement.b),
                    max: main.bound_sq(),
                });
            }
            Ok(())
        })(),
    );
    for (j, a) in statement.aux.iter().enumerate() {
        record(
            &mut out,
            (|| {
                if a.root.len() != binary[j].root().len() {
                    return Err(NormError::Length {
                        got: a.root.len(),
                        expected: binary[j].root().len(),
                        slot: "auxiliary root",
                    });
                }
                Ok(())
            })(),
        );
        record(
            &mut out,
            (|| {
                if a.claims.v_r != a.claims.v_r_prime {
                    return Err(NormError::WellFormed {
                        repetition: j,
                        v_r: to_u64(a.claims.v_r),
                        v_r_prime: to_u64(a.claims.v_r_prime),
                    });
                }
                Ok(())
            })(),
        );
    }

    let cs = challenges(statement, &proof.rounds, w1, w2);
    for i in 0..proof.rounds.len() {
        let msg = &proof.rounds[i];
        let round = i + 1;
        // --- 2. round 1 exposes every claim; later rounds carry them ---
        if round == 1 {
            record(
                &mut out,
                (|| {
                    main.chain()
                        .check_root(&msg.commit, &statement.cm)
                        .map_err(|e| commit_err(Chain::Main, round, e))
                })(),
            );
            record(
                &mut out,
                (|| {
                    let beta = main
                        .weights()
                        .beta(1)
                        .map_err(|e| err(Family::Linear, Chain::Main, round, e))?;
                    linear_expose(&beta, &msg.linear, statement.v)
                        .map_err(|e| err(Family::Linear, Chain::Main, round, e))
                })(),
            );
            record(
                &mut out,
                (|| {
                    quad_expose::<R, D>(&msg.quad, statement.b % R::MODULUS, round)
                        .map_err(|e| err(Family::Quadratic, Chain::Main, round, e))
                })(),
            );
            for (j, bundle) in binary.iter().enumerate() {
                let slot = Chain::Binary(j);
                let claims = statement.aux[j].claims;
                record(
                    &mut out,
                    (|| {
                        bundle
                            .chain
                            .check_root(&msg.aux[j].commit, &statement.aux[j].root)
                            .map_err(|e| commit_err(slot, round, e))
                    })(),
                );
                for (k, (weights, family, claim)) in [
                    (&bundle.w_value, Family::AuxValue, claims.v_r),
                    (&bundle.w_digit, Family::AuxDigit, claims.v_r_prime),
                    (&bundle.w_binarity, Family::AuxBinarity, claims.v_alpha),
                ]
                .into_iter()
                .enumerate()
                {
                    record(
                        &mut out,
                        (|| {
                            let beta = weights.beta(1).map_err(|e| err(family, slot, round, e))?;
                            linear_expose(&beta, &msg.aux[j].lin[k], claim)
                                .map_err(|e| err(family, slot, round, e))
                        })(),
                    );
                }
                record(
                    &mut out,
                    (|| {
                        quad_expose::<R, D>(
                            &msg.aux[j].quad,
                            to_u64(claims.v_alpha) % R::MODULUS,
                            round,
                        )
                        .map_err(|e| err(Family::AuxQuadratic, slot, round, e))
                    })(),
                );
            }
        } else {
            let level = levels - 1 - i;
            let prev = &proof.rounds[i - 1];
            let c = cs[i - 1].clone();
            record(
                &mut out,
                (|| {
                    main.chain()
                        .check_level(level, &msg.commit, &prev.commit, &c)
                        .map_err(|e| commit_err(Chain::Main, round, e))
                })(),
            );
            record(
                &mut out,
                (|| {
                    let beta = main
                        .weights()
                        .beta(round)
                        .map_err(|e| err(Family::Linear, Chain::Main, round, e))?;
                    linear_recursion(&beta, &msg.linear, &prev.linear, &c, round)
                        .map_err(|e| err(Family::Linear, Chain::Main, round, e))
                })(),
            );
            record(
                &mut out,
                (|| {
                    quad_carry(&msg.quad, &prev.quad, &c, round)
                        .map_err(|e| err(Family::Quadratic, Chain::Main, round, e))
                })(),
            );
            for (j, bundle) in binary.iter().enumerate() {
                let slot = Chain::Binary(j);
                record(
                    &mut out,
                    (|| {
                        bundle
                            .chain
                            .check_level(level, &msg.aux[j].commit, &prev.aux[j].commit, &c)
                            .map_err(|e| commit_err(slot, round, e))
                    })(),
                );
                for (k, (weights, family)) in [
                    (&bundle.w_value, Family::AuxValue),
                    (&bundle.w_digit, Family::AuxDigit),
                    (&bundle.w_binarity, Family::AuxBinarity),
                ]
                .into_iter()
                .enumerate()
                {
                    record(
                        &mut out,
                        (|| {
                            let beta = weights
                                .beta(round)
                                .map_err(|e| err(family, slot, round, e))?;
                            linear_recursion(
                                &beta,
                                &msg.aux[j].lin[k],
                                &prev.aux[j].lin[k],
                                &c,
                                round,
                            )
                            .map_err(|e| err(family, slot, round, e))
                        })(),
                    );
                }
                record(
                    &mut out,
                    (|| {
                        quad_carry(&msg.aux[j].quad, &prev.aux[j].quad, &c, round)
                            .map_err(|e| err(Family::AuxQuadratic, slot, round, e))
                    })(),
                );
            }
        }
    }

    // --- final round: the base openings, the base pairings, the gates ---
    let c_last = cs[rounds - 1].clone();
    let prev = &proof.rounds[rounds - 1];
    record(
        &mut out,
        (|| {
            main.chain()
                .check_level(0, &proof.tail, &prev.commit, &c_last)
                .map_err(|e| commit_err(Chain::Main, levels, e))
        })(),
    );
    record(
        &mut out,
        (|| {
            linear_base(&proof.tail, main.weights().a0(), &prev.linear, &c_last)
                .map_err(|e| err(Family::Linear, Chain::Main, levels, e))
        })(),
    );
    record(
        &mut out,
        (|| {
            quad_base(&proof.tail, &proof.tail, &prev.quad, &c_last)
                .map_err(|e| err(Family::Quadratic, Chain::Main, levels, e))
        })(),
    );
    record(
        &mut out,
        (|| {
            let tail_sq = square_sum(&proof.tail).map_err(|_| NormError::BadSetup("tail norm"))?;
            // The tail is the *folded* witness, so its admissibility bound is the
            // folding-growth bound `B_tail^2` (Theorem 1), not the statement's
            // `B^2` on the committed vector: `log N - 1` folds by challenges of
            // operator norm `T` multiply the coordinate bound by `(2T)^{log N - 1}`.
            if tail_sq > main.tail_bound_sq() {
                return Err(NormError::NotShort {
                    chain: Chain::Main,
                    norm_sq: tail_sq,
                    bound_sq: main.tail_bound_sq(),
                });
            }
            Ok(())
        })(),
    );
    for (j, bundle) in binary.iter().enumerate() {
        let slot = Chain::Binary(j);
        let tail = &proof.aux_tails[j];
        record(
            &mut out,
            (|| {
                bundle
                    .chain
                    .check_level(0, tail, &prev.aux[j].commit, &c_last)
                    .map_err(|e| commit_err(slot, levels, e))
            })(),
        );
        let tilde = join::<R, D, 2, DIGITS>(tail);
        record(
            &mut out,
            (|| {
                // `lin1`'s witness is the MAIN one (Fig. 3, case 3: `<r_alpha_0,
                // s_log N> = <c, pi^(lin2)>`), so its base pairing reads the main
                // tail against the `r * alpha` weight.
                linear_base(
                    &proof.tail,
                    bundle.w_value.a0(),
                    &prev.aux[j].lin[0],
                    &c_last,
                )
                .map_err(|e| err(Family::AuxValue, slot, levels, e))
            })(),
        );
        record(
            &mut out,
            (|| {
                linear_base(tail, bundle.w_digit.a0(), &prev.aux[j].lin[1], &c_last)
                    .map_err(|e| err(Family::AuxDigit, slot, levels, e))
            })(),
        );
        record(
            &mut out,
            (|| {
                linear_base(
                    &proof.tail,
                    bundle.w_binarity.a0(),
                    &prev.aux[j].lin[2],
                    &c_last,
                )
                .map_err(|e| err(Family::AuxBinarity, slot, levels, e))
            })(),
        );
        record(
            &mut out,
            (|| {
                quad_base(&tilde, &proof.tail, &prev.aux[j].quad, &c_last)
                    .map_err(|e| err(Family::AuxQuadratic, slot, levels, e))
            })(),
        );
        record(
            &mut out,
            (|| {
                let aux_sq = square_sum(tail).map_err(|_| NormError::BadSetup("aux tail norm"))?;
                if aux_sq > bundle.tail_bound_sq {
                    return Err(NormError::NotShort {
                        chain: slot,
                        norm_sq: aux_sq,
                        bound_sq: bundle.tail_bound_sq,
                    });
                }
                Ok(())
            })(),
        );
    }
    out
}

/// Verifier: the first refusal of [`verify_report`], naming the chain, the
/// family and the round.
///
/// # Errors
/// See [`NormError`]. Every rejection is attributable to one named check, so a
/// test can assert *which* forgery was caught *where*; use [`verify_report`] to
/// see all of them at once.
pub fn verify<R, const D: usize, const DIGITS: usize>(
    statement: &Statement<R, D>,
    proof: &NormProof<R, D>,
    main: &MainBundle<R, D, DIGITS>,
    binary: &[BinaryBundle<R, D, DIGITS>],
    w1: u32,
    w2: u32,
) -> Result<(), NormError>
where
    R: CenteredRing,
{
    verify_report(statement, proof, main, binary, w1, w2)
        .into_iter()
        .next()
        .map_or(Ok(()), Err)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shortness::tensor_fold::NormAccounting;
    use algebra::ring::PolynomialQuotientRing;
    use alloc::collections::BTreeSet;
    use alloc::vec;

    type Q5 = Zq<4093>;
    const MOD8: u64 = 4_093;
    const DS: usize = 4;
    const L: usize = 12;
    const N: usize = 8;
    const LOGN: usize = 3;
    const KAPPA: usize = 2;
    const W1: u32 = 1;
    const W2: u32 = 1;
    use algebra::ring::zq::Zq;

    fn e(v: u64) -> Elt<Q5, DS> {
        let mut coeffs = [0u64; DS];
        coeffs[0] = v % MOD8;
        Elt::from_coefficients(coeffs.iter().map(|&c| Q5::from(c)).collect())
    }

    /// The value vector of a repetition: `embed(coef(s) ∘ α)` for a power
    /// weight `α`.
    fn tilde_of(s: &[Elt<Q5, DS>], alpha: u64) -> Vec<Elt<Q5, DS>> {
        let w =
            LinearWeights::<Q5, DS>::geometric(Q5::from(alpha), 1, L, LOGN - 1).expect("weights");
        let full = w.weight(LOGN - 1).expect("full");
        let mut out = Vec::with_capacity(s.len());
        for (p, elt) in s.iter().enumerate() {
            let coeffs: Vec<Q5> = elt
                .coefficients()
                .iter()
                .enumerate()
                .map(|(t, c)| *c * full[p].coefficients()[t])
                .collect();
            out.push(Elt::from_coefficients(coeffs));
        }
        out
    }

    struct Ctx {
        main_chain: LeveledAjtai<Q5, DS, L>,
        aux_chain: LeveledAjtai<Q5, DS, L>,
        weights: LinearWeights<Q5, DS>,
        w_alpha: LinearWeights<Q5, DS>,
        w_r: LinearWeights<Q5, DS>,
        w_rp: LinearWeights<Q5, DS>,
    }

    impl Ctx {
        fn new() -> Self {
            // The binarity weight is `α = 91`; the fingerprint challenge is
            // `r = 41`, so §3.3 item 3's functional on the main witness is the
            // power vector with base `r·α = 3731` and item 4's is the `r`
            // vector pulled back through the digit gadget (base 41, `L` planes
            // absorbed). `2047` is `2⁻¹ mod 4093`, used by the crafted-
            // auxiliary test to solve one linear equation over the digits.
            Self {
                main_chain: LeveledAjtai::setup(b"A", &[1u8; 32], KAPPA, N, L).expect("A"),
                aux_chain: LeveledAjtai::setup(b"B", &[2u8; 32], KAPPA, N, L * L).expect("B"),
                weights: LinearWeights::geometric(Q5::from(123u64), L, L, LOGN - 1).expect("w"),
                w_alpha: LinearWeights::geometric(Q5::from(91u64), 1, L, LOGN - 1).expect("wa"),
                w_r: LinearWeights::geometric(Q5::from(3731u64), 1, L, LOGN - 1).expect("wr"),
                w_rp: LinearWeights::geometric(Q5::from(41u64), L, L * L, LOGN - 1).expect("wrp"),
            }
        }
    }

    fn witness(seed: u64) -> Vec<Elt<Q5, DS>> {
        let values: Vec<Elt<Q5, DS>> = (0..N)
            .map(|m| {
                let coeffs: Vec<Q5> = (0..DS)
                    .map(|t| Q5::from((seed * 7919 + m as u64 * 131 + t as u64 * 17) % MOD8))
                    .collect();
                Elt::from_coefficients(coeffs)
            })
            .collect();
        crate::pcs::gadget::split::<Q5, DS, 2, L>(&values)
    }

    /// Theorem 1's completeness bounds for *this* pool, as
    /// `(main tail, auxiliary tail)`.
    ///
    /// The challenge space `P_{W1,W2}` has `ℓ∞`-operator norm `T = W1 + 2W2`, so
    /// `log N − 1` folds multiply the coordinate bound by `(2T)^{log N − 1}`, and
    /// the revealed tail holds `2·base_len` coordinates. Both chains start from
    /// binary digits (`initial = 1`, the paper's `δ/2` at base `δ = 2`).
    fn tail_bounds() -> (u128, u128) {
        let t_op = u64::from(W1) + 2 * u64::from(W2);
        let of = |base_len: usize| {
            NormAccounting {
                rounds: LOGN - 1,
                t_op,
                initial: 1,
                base_len,
            }
            .bound_sq()
        };
        (of(L * DS), of(L * L * DS))
    }

    /// Every check that rejects this proof, as a set.
    ///
    /// Under Fiat-Shamir one tamper moves every later challenge, so several
    /// checks fail together and only the whole set distinguishes "checked and
    /// failed" from "never reached".
    fn failing(
        statement: &Statement<Q5, DS>,
        proof: &NormProof<Q5, DS>,
        main: &MainBundle<Q5, DS, L>,
        aux: &[BinaryBundle<Q5, DS, L>],
    ) -> BTreeSet<CheckId> {
        verify_report(statement, proof, main, aux, W1, W2)
            .iter()
            .map(|e| e.check_id(LOGN))
            .collect()
    }

    /// The identity of one check, spelled the way the assertions need it.
    fn id(lane: &'static str, chain: Chain, round: usize) -> CheckId {
        CheckId { lane, chain, round }
    }

    fn bundles(
        ctx: &Ctx,
    ) -> (
        Vec<Elt<Q5, DS>>,
        MainBundle<Q5, DS, L>,
        [BinaryBundle<Q5, DS, L>; 1],
    ) {
        let s = witness(3);
        let (main_tail, aux_tail) = tail_bounds();
        let main = MainBundle::new(
            ctx.main_chain.clone(),
            &s,
            ctx.weights.clone(),
            u128::from(N as u64 * L as u64 * DS as u64),
            main_tail,
        )
        .expect("main bundle");
        let tilde = tilde_of(&s, 91);
        let aux = BinaryBundle::new(
            ctx.aux_chain.clone(),
            &tilde,
            ctx.w_r.clone(),
            ctx.w_rp.clone(),
            ctx.w_alpha.clone(),
            aux_tail,
        )
        .expect("aux bundle");
        (s, main, [aux])
    }

    #[test]
    fn honest_execution_verifies() {
        let ctx = Ctx::new();
        let (_s, main, aux) = bundles(&ctx);
        let (statement, proof) = prove(&main, &aux, W1, W2).expect("prove");
        assert_eq!(proof.rounds.len(), LOGN - 1);
        assert_eq!(proof.tail.len(), 2 * L);
        assert_eq!(proof.aux_tails[0].len(), 2 * L * L);
        assert!(proof_size(&proof) > 0);
        verify(&statement, &proof, &main, &aux, W1, W2).expect("honest proof must verify");
    }

    #[test]
    fn the_transcript_has_exactly_the_shape_section_3_6_counts() {
        // §3.6, p. 21: each message round is `(2κι + 6) + t·(2κι + 10)` ring
        // elements — `2 + 4` for `π^(lin), π^(qua)` and `3·2 + 4` for §3.3
        // p. 14's `π^(bin) ∈ R^{2κι+10}` — and the final round `2ℓ + 2tλι`.
        // The count is checked against the *shape*, so a lane that stops
        // emitting one of its three linear openings shows up here rather than
        // as a silent 2-element-per-repetition shrink.
        let ctx = Ctx::new();
        let (_s, main, aux) = bundles(&ctx);
        let reps = aux.len();
        let (_statement, proof) = prove(&main, &aux, W1, W2).expect("prove");
        let per_round = 2 * KAPPA * L + 6 + reps * (2 * KAPPA * L + 10);
        let final_round = 2 * L + 2 * reps * L * L;
        assert_eq!(
            proof.tail.len(),
            2 * L,
            "the revealed main tail is s_log N ∈ R_q^{{2ℓ}}"
        );
        assert_eq!(
            proof.aux_tails[0].len(),
            2 * L * L,
            "the revealed auxiliary tail is ŝ_α,log N ∈ R_q^{{2λι}}"
        );
        assert_eq!(
            proof_size(&proof),
            (LOGN - 1) * per_round + final_round,
            "§3.6's count, per round and in total"
        );
    }

    #[test]
    fn the_norm_claim_is_derived_from_the_witness() {
        let ctx = Ctx::new();
        let (s, main, _aux) = bundles(&ctx);
        let expect: u128 = flatten(&s)
            .iter()
            .map(|c: &Q5| u128::from(c.abs_infinity()) * u128::from(c.abs_infinity()))
            .sum();
        let (statement, _proof) = prove(&main, &[], W1, W2).expect("prove with no repetitions");
        assert_eq!(
            u128::from(statement.b),
            expect,
            "b must be the exact sum of squares"
        );
    }

    #[test]
    fn an_oversized_norm_claim_is_refused_by_the_bound_check() {
        let ctx = Ctx::new();
        let (_s, main, aux) = bundles(&ctx);
        let (mut statement, proof) = prove(&main, &aux, W1, W2).expect("prove");
        // One unit above the honest claim is still inside `B²` — the honest `b`
        // is the count of set bits in a random binary decomposition, well below
        // the `N·L·d` ceiling — so the tamper has to cross the bound itself.
        statement.b = u64::try_from(main.bound_sq() + 1).expect("the fixture's bound fits u64");
        assert_eq!(
            verify(&statement, &proof, &main, &aux, W1, W2),
            Err(NormError::StatementBound {
                claim: u128::from(statement.b),
                max: main.bound_sq(),
            })
        );
    }

    #[test]
    fn each_forgery_is_caught_by_its_own_named_check() {
        let ctx = Ctx::new();
        let (_s, main, aux) = bundles(&ctx);
        let (statement, proof) = prove(&main, &aux, W1, W2).expect("prove");

        // main commitment root
        let mut p = proof.clone();
        p.rounds[0].commit[0] = p.rounds[0].commit[0].clone() + e(1);
        assert_eq!(
            verify(&statement, &p, &main, &aux, W1, W2),
            Err(NormError::Commitment {
                chain: Chain::Main,
                round: 1,
                source: LeveledError::RootMismatch { round: 1 }
            })
        );

        // main linear message
        let mut p = proof.clone();
        p.rounds[0].linear[0] = p.rounds[0].linear[0].clone() + e(1);
        assert!(matches!(
            verify(&statement, &p, &main, &aux, W1, W2),
            Err(NormError::Constraint {
                family: Family::Linear,
                chain: Chain::Main,
                round: 1,
                source: FoldError::ClaimMismatch { .. }
            })
        ));

        // main quadratic message
        let mut p = proof.clone();
        p.rounds[0].quad[3] = p.rounds[0].quad[3].clone() + e(1);
        assert!(matches!(
            verify(&statement, &p, &main, &aux, W1, W2),
            Err(NormError::Constraint {
                family: Family::Quadratic,
                chain: Chain::Main,
                round: 1,
                source: FoldError::NormClaimMismatch { .. }
            })
        ));

        // auxiliary chain root
        let mut p = proof.clone();
        p.rounds[0].aux[0].commit[0] = p.rounds[0].aux[0].commit[0].clone() + e(1);
        assert_eq!(
            verify(&statement, &p, &main, &aux, W1, W2),
            Err(NormError::Commitment {
                chain: Chain::Binary(0),
                round: 1,
                source: LeveledError::RootMismatch { round: 1 }
            })
        );

        // auxiliary digit-side linear message
        let mut p = proof.clone();
        p.rounds[0].aux[0].lin[1][1] = p.rounds[0].aux[0].lin[1][1].clone() + e(1);
        assert!(matches!(
            verify(&statement, &p, &main, &aux, W1, W2),
            Err(NormError::Constraint {
                family: Family::AuxDigit,
                chain: Chain::Binary(0),
                round: 1,
                source: FoldError::ClaimMismatch { .. }
            })
        ));

        // the bilinear message, whose claim is v_alpha
        let mut p = proof.clone();
        p.rounds[0].aux[0].quad[0] = p.rounds[0].aux[0].quad[0].clone() + e(1);
        assert!(matches!(
            verify(&statement, &p, &main, &aux, W1, W2),
            Err(NormError::Constraint {
                family: Family::AuxQuadratic,
                chain: Chain::Binary(0),
                round: 1,
                source: FoldError::NormClaimMismatch { .. }
            })
        ));

        // a revealed tail substituted after the fact is caught by the level-0
        // commitment relation on the tail, which the verifier reads before any
        // of the base pairings — the tail is bound by `cm`, not just by `b`.
        let mut p = proof.clone();
        p.tail[0] = p.tail[0].clone() + e(1);
        assert_eq!(
            verify(&statement, &p, &main, &aux, W1, W2),
            Err(NormError::Commitment {
                chain: Chain::Main,
                round: 3,
                source: LeveledError::LevelMismatch { level: 0 }
            })
        );
    }

    /// Every check Fig. 3's case 3 (`i = log N`) runs, for `reps` repetitions:
    /// the two base openings, the four linear base pairings and the two
    /// quadratic base identities. The norm-admissibility gates are excluded —
    /// they compare a revealed vector against a bound, so an untouched tail
    /// stays admissible however far the challenges moved.
    fn final_round_checks(reps: usize) -> BTreeSet<CheckId> {
        let mut s = BTreeSet::new();
        for lane in ["commitment", "linear", "quadratic"] {
            s.insert(id(lane, Chain::Main, LOGN));
        }
        for j in 0..reps {
            for lane in [
                "commitment",
                Family::AuxValue.name(),
                Family::AuxDigit.name(),
                Family::AuxBinarity.name(),
                Family::AuxQuadratic.name(),
            ] {
                s.insert(id(lane, Chain::Binary(j), LOGN));
            }
        }
        s
    }

    #[test]
    fn a_later_round_forgery_is_caught_by_the_recursion() {
        let ctx = Ctx::new();
        let (_s, main, aux) = bundles(&ctx);
        let (statement, proof) = prove(&main, &aux, W1, W2).expect("prove");
        // A tampered *linear* message at the last message round. Its own round
        // names it, and nothing else upstream moves: round `i` reads `c_{i−1}`,
        // so a tamper inside round `log N − 1` = 2 here leaves `c₁` alone and
        // only displaces the *final* challenge. The whole final round must then
        // be reported, or a single-error verifier hides the aux lanes behind the
        // main one.
        let mut p = proof.clone();
        p.rounds[1].linear[0] = p.rounds[1].linear[0].clone() + e(2);
        let got = verify(&statement, &p, &main, &aux, W1, W2);
        assert!(
            matches!(
                got,
                Err(NormError::Constraint {
                    family: Family::Linear,
                    chain: Chain::Main,
                    round: 2,
                    source: FoldError::RecursionMismatch { round: 2 }
                })
            ),
            "actual: {got:?}"
        );
        let mut expected = final_round_checks(1);
        expected.insert(id(Family::Linear.name(), Chain::Main, 2));
        assert_eq!(
            failing(&statement, &p, &main, &aux),
            expected,
            "a last-round tamper must break its own check and the whole final \
             round, and nothing at round 2 besides it"
        );
        // A tampered *cross term* of the last message round's auxiliary
        // quadratic message. Fig. 3 (p. 17) case 2 constrains only
        // `(1,0,0,1) · πᵢ^(qua,α)` — `L_i + R_i` — at *every* `i ∈ [2 : log N−1]`,
        // the last message round included, so `quad[1]` has no claim of its own
        // to contradict there: it is pinned by case 3's last line
        // `⟨G_{σα,2ℓ} ŝ_α,log N, σ⁻¹(s_log N)⟩ = ⟨c^(qua)_(log N−1), π^(qua,α)_(log N−1)⟩`,
        // whose weight vector `c^(qua)` has all four entries non-zero. Appendix
        // C step II (p. 40) says why there is no per-round claim: the four
        // components are recovered as the coefficients of a degree-2 polynomial
        // in the challenge, so that identity *is* the check.
        //
        // So the exact set here is the final round and nothing else — the same
        // set as the linear tamper above minus the round-2 entry. A per-round
        // `quad[1]` claim would be a check the paper does not specify, and this
        // assertion is what stops this module from inventing one.
        let mut p = proof.clone();
        p.rounds[1].aux[0].quad[1] = p.rounds[1].aux[0].quad[1].clone() + e(2);
        let set = failing(&statement, &p, &main, &aux);
        assert_eq!(
            set,
            final_round_checks(1),
            "the cross terms of the last message round must be caught by the \
             final-round bilinear identity, and must NOT claim a failure at \
             their own round"
        );
        assert!(
            set.contains(&id(Family::AuxQuadratic.name(), Chain::Binary(0), LOGN)),
            "the family must be live here, not dead code: {set:?}"
        );
    }

    #[test]
    fn a_non_binary_witness_with_a_crafted_auxiliary_vector_is_caught_by_r() {
        // The regression for the binding this module exists to provide.
        //
        // Lemma 2 (p. 8) only turns `ct(<s,sigma(s)>) = b` into an `ℓ2` bound
        // given `coef(s) in {0,1}`, and the binarity argument (§3.3) needs the
        // committed auxiliary vector to *be* `s o alpha`. That is forced by
        // item 4's equality, whose two sides live on different witnesses:
        // `v_r = <coef(s), r o alpha>` on the main one and
        // `v_r' = <coef(G s_de), r>` on the committed decomposition.
        //
        // Here the witness has one digit raised to `2` (so it is no longer a
        // decomposition at all), and the auxiliary vector is chosen to defeat
        // the bilinear check: `s~ := s o alpha + beta` with `<beta, s>` equal to
        // the binarity defect, which one free coordinate can always absorb. The
        // `(qua)` exposure then holds by construction, and only the `r`
        // fingerprint refuses.
        let ctx = Ctx::new();
        let s = witness(3);
        let alpha_full = ctx
            .w_alpha
            .weight(LOGN - 1)
            .expect("binarity weights at full nesting");
        // A coordinate that really is `1`, so adding one makes it `2`.
        let hit = s
            .iter()
            .position(|e| e.coefficients()[0] == Q5::ONE)
            .expect("a binary decomposition has a set bit");
        let mut bad = s.clone();
        bad[hit] = bad[hit].clone() + e(1);
        assert_ne!(
            square_sum(&bad).expect("small"),
            square_sum(&s).expect("small"),
            "the tampered witness must actually stop being binary"
        );
        let tilde_honest = tilde_of(&bad, 91);
        let v_alpha = ct(&herm(&bad, &alpha_full));
        let defect = ct(&herm(&tilde_honest, &bad)) - v_alpha;
        // `2^-1 mod 4093 = 2047`, and the touched coordinate of `bad` is `2`.
        let beta = defect * Q5::from(2047u64);
        let mut tilde = tilde_honest.clone();
        tilde[hit] = tilde[hit].clone() - crate::shortness::tensor_fold::constant::<Q5, DS>(beta);
        // With this `tilde` the bilinear check is satisfied:
        // `<tilde, s> = <s o alpha, s> - beta * 2 = <s, alpha>`.
        assert_eq!(
            ct(&herm(&tilde, &bad)),
            v_alpha,
            "the crafted auxiliary vector must defeat (quă)"
        );
        let (main_tail, aux_tail) = tail_bounds();
        let main = MainBundle::new(
            ctx.main_chain.clone(),
            &bad,
            ctx.weights.clone(),
            // Above the honest ceiling `N*ell*d = 384` so the *statement* gate
            // cannot be what refuses, and still under `q`.
            u128::from(400u64),
            main_tail,
        )
        .expect("main bundle");
        let aux = BinaryBundle::new(
            ctx.aux_chain.clone(),
            &tilde,
            ctx.w_r.clone(),
            ctx.w_rp.clone(),
            ctx.w_alpha.clone(),
            aux_tail,
        )
        .expect("aux bundle");
        let (statement, proof) = prove(&main, std::slice::from_ref(&aux), W1, W2).expect("prove");
        let set = failing(&statement, &proof, &main, std::slice::from_ref(&aux));
        assert!(
            set.contains(&id("well-formed", Chain::Binary(0), 0)),
            "the r-fingerprint is the only check that binds the committed \
             auxiliary vector to the main witness; actual: {set:?}"
        );
        assert!(
            !set.contains(&id(Family::AuxQuadratic.name(), Chain::Binary(0), 1)),
            "the crafted vector defeats the bilinear exposure by construction, \
             so reporting it here would be a coincidence, not a check"
        );
    }

    #[test]
    fn a_bound_reaching_the_modulus_voids_the_norm_claim() {
        // Lemma 2's hypothesis, checked rather than assumed: with `B^2 >= q`
        // the residue `b` is also the residue of `b + q`, so the argument
        // certifies nothing and the verifier must refuse on that ground alone.
        let ctx = Ctx::new();
        let s = witness(3);
        let (main_tail, _aux_tail) = tail_bounds();
        assert!(matches!(
            MainBundle::new(
                ctx.main_chain.clone(),
                &s,
                ctx.weights.clone(),
                u128::from(MOD8),
                main_tail,
            ),
            Err(NormError::NotAdmissible {
                limit: _,
                modulus: MOD8
            })
        ));
    }

    #[test]
    fn every_named_check_fires_for_some_forgery() {
        // A check that never appears in any report is dead code, and under
        // Fiat-Shamir a single-error verifier cannot tell it apart from a check
        // that was simply reached last. Enumerate one forgery per lane and
        // assert the union of their reports covers every Fig. 3 identity.
        let ctx = Ctx::new();
        let (_s, main, aux) = bundles(&ctx);
        let (statement, proof) = prove(&main, &aux, W1, W2).expect("prove");
        let mut seen = BTreeSet::new();
        let tamper = |slot: usize, p: &NormProof<Q5, DS>| -> BTreeSet<CheckId> {
            let mut q = p.clone();
            match slot {
                0 => q.rounds[0].commit[0] = q.rounds[0].commit[0].clone() + e(1),
                1 => q.rounds[0].linear[0] = q.rounds[0].linear[0].clone() + e(1),
                2 => q.rounds[0].quad[3] = q.rounds[0].quad[3].clone() + e(1),
                3 => q.rounds[0].aux[0].commit[0] = q.rounds[0].aux[0].commit[0].clone() + e(1),
                4 => q.rounds[0].aux[0].lin[1][1] = q.rounds[0].aux[0].lin[1][1].clone() + e(1),
                5 => q.rounds[0].aux[0].lin[2][0] = q.rounds[0].aux[0].lin[2][0].clone() + e(1),
                6 => q.rounds[0].aux[0].quad[0] = q.rounds[0].aux[0].quad[0].clone() + e(1),
                7 => q.tail[0] = q.tail[0].clone() + e(1),
                8 => q.aux_tails[0][0] = q.aux_tails[0][0].clone() + e(1),
                9 => q.rounds[1].linear[1] = q.rounds[1].linear[1].clone() + e(1),
                10 => q.rounds[1].quad[0] = q.rounds[1].quad[0].clone() + e(1),
                11 => q.rounds[1].aux[0].lin[0][0] = q.rounds[1].aux[0].lin[0][0].clone() + e(1),
                12 => q.rounds[1].aux[0].quad[3] = q.rounds[1].aux[0].quad[3].clone() + e(1),
                _ => panic!("no such slot"),
            }
            let set = failing(&statement, &q, &main, &aux);
            assert!(!set.is_empty(), "tamper {slot} verified: nothing refused");
            set
        };
        for slot in 0..13 {
            seen.extend(tamper(slot, &proof));
        }
        // The statement-level gates, which no message tamper can produce.
        let mut st = statement.clone();
        st.b = u64::try_from(main.bound_sq() + 1).expect("fits");
        seen.extend(failing(&st, &proof, &main, &aux));
        let mut st = statement.clone();
        st.aux[0].claims.v_r_prime = st.aux[0].claims.v_r_prime + Q5::ONE;
        seen.extend(failing(&st, &proof, &main, &aux));
        // The admissibility gate, from the dedicated test above.
        seen.insert(id("wraparound", Chain::Main, 0));
        for lane in [
            "commitment",
            "linear",
            "quadratic",
            "aux-value",
            "aux-digit",
            "aux-binarity",
            "aux-quadratic",
            "statement-bound",
            "well-formed",
            "wraparound",
        ] {
            assert!(
                seen.iter().any(|c| c.lane == lane),
                "{lane} never fired: {seen:?}"
            );
        }
    }

    #[test]
    fn a_decomposition_that_is_not_a_decomposition_is_refused() {
        // The well-formedness gate: substituting the digit-side claim breaks
        // `v_r = v_r'`, which is the statement-level binding of the committed
        // auxiliary decomposition to the main witness's `r o alpha` functional.
        let ctx = Ctx::new();
        let (_s, main, aux) = bundles(&ctx);
        let (mut statement, proof) = prove(&main, &aux, W1, W2).expect("prove");
        statement.aux[0].claims.v_r_prime = statement.aux[0].claims.v_r_prime + Q5::ONE;
        assert!(matches!(
            verify(&statement, &proof, &main, &aux, W1, W2),
            Err(NormError::WellFormed { repetition: 0, .. })
        ));
    }

    #[test]
    fn challenges_depend_on_every_message_they_precede() {
        let ctx = Ctx::new();
        let (_s, main, aux) = bundles(&ctx);
        let (statement, proof) = prove(&main, &aux, W1, W2).expect("prove");
        let mut moved = proof.clone();
        moved.rounds[0].quad[0] = moved.rounds[0].quad[0].clone() + e(5);
        let honest = challenge_at(&statement, &proof.rounds, 1, W1, W2);
        let tampered = challenge_at(&statement, &moved.rounds, 1, W1, W2);
        assert_ne!(
            honest[0], tampered[0],
            "the challenge must bind the message"
        );
        assert_ne!(honest[1], tampered[1]);
    }

    #[test]
    fn an_inconsistent_bundle_is_refused_before_any_crypto_runs() {
        // A weight table sized for another witness must be caught at
        // construction, not silently produce a proof of nothing.
        let ctx = Ctx::new();
        let s = witness(1);
        let short = LinearWeights::<Q5, DS>::geometric(Q5::from(3u64), 1, L, 0).expect("built");
        assert!(matches!(
            MainBundle::new(
                ctx.main_chain.clone(),
                &s,
                short,
                u128::from(u64::MAX),
                // The assertion below is about the weight-table rejection, so the
                // tail bound is irrelevant here; any value works.
                u128::from(u64::MAX),
            ),
            Err(NormError::BadSetup(
                "linear weight length differs from the witness"
            ))
        ));
        let wrong_tilde = vec![e(1); 3];
        assert!(matches!(
            BinaryBundle::new(
                ctx.aux_chain.clone(),
                &wrong_tilde,
                ctx.w_r.clone(),
                ctx.w_rp.clone(),
                ctx.w_alpha.clone(),
                u128::from(u64::MAX),
            ),
            Err(NormError::Length { .. })
        ));
    }

    #[test]
    fn two_repetitions_are_independent() {
        // Fresh alpha per repetition: with the same weights twice the second
        // repetition must still verify, and dropping one must change the proof
        // size exactly by its share.
        let ctx = Ctx::new();
        let (s, main, [aux]) = bundles(&ctx);
        let tilde2 = tilde_of(&s, 91);
        let (_, aux_tail) = tail_bounds();
        let aux2 = BinaryBundle::new(
            LeveledAjtai::setup(b"B2", &[9u8; 32], KAPPA, N, L * L).expect("chain"),
            &tilde2,
            ctx.w_r.clone(),
            ctx.w_rp.clone(),
            ctx.w_alpha.clone(),
            aux_tail,
        )
        .expect("aux2");
        let (statement, proof) =
            prove(&main, &[aux.clone(), aux2.clone()], W1, W2).expect("prove twice");
        assert_eq!(statement.aux.len(), 2);
        verify(&statement, &proof, &main, &[aux.clone(), aux2], W1, W2).expect("both verify");
        let single = prove(&main, &[aux], W1, W2).expect("prove once");
        assert!(proof_size(&single.1) < proof_size(&proof));
    }
}
