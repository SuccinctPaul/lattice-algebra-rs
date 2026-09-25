//! Leveled Ajtai commitment with foldable intermediate states.
//!
//! This is the *binding* layer a self-inner-product norm argument needs:
//! [`crate::shortness::self_ip`] proves that round messages, challenges and a
//! revealed tail are mutually consistent with a claim `b`, but nothing there
//! ties `b` to a vector the prover is committed to. Here the witness is
//! committed by a chain of `log N` gadget-decomposed Ajtai maps, and every
//! level of the chain is exposed as a per-round message that a split-and-fold
//! protocol can check against its predecessor — so an extractor obtains a
//! short kernel vector *against those commitments*.
//!
//! # The chain (Fig. 1)
//!
//! With `N` blocks of `per_block` ring elements, gadget base `2` and
//! `DIGITS = ⌈log₂ q⌉` digit planes, the level maps are
//!
//! ```text
//! c_0      = G⁻¹((I_{N/2}       ⊗ A_0) · s)          A_0 ∈ R_q^{κ × 2·per_block}
//! c_j      = G⁻¹((I_{N/2^{j+1}} ⊗ A_j) · c_{j-1})     A_j ∈ R_q^{κ × 2κ·DIGITS}
//! cm       = A_{log N − 1} · c_{log N − 2}
//! ```
//!
//! so the block count halves per level, every level but the top one
//! decomposes, and `c_j ∈ R^{(N/2^{j+1})·κ·DIGITS}`.
//!
//! # The round checks
//!
//! Round `i` reveals the *folded* state of level `log N − i − 1` split into
//! halves; the verifier checks
//!
//! ```text
//! i = 1:            A_{log N − 1} · m_1                     = cm
//! 2 ≤ i ≤ log N −1: A_{log N − i} · m_i = c_{i−1,0}·G(m_{i−1,L}) + c_{i−1,1}·G(m_{i−1,R})
//! i = log N:        A_0 · s_{log N}      = (same, on m_{log N − 1})
//! ```
//!
//! The right-hand side recombines the previous message with the gadget `G`
//! and folds it with the previous challenge, so the chain and the witness
//! folding stay in lock-step. That works because folding commutes with `G` —
//! [`fold_join_commutes`] checks it against ring arithmetic instead of
//! assuming it, and it is the reason the *same* challenge can drive the
//! witness, the chain and every other sub-proof.
//!
//! [`fold_join_commutes`]: LeveledAjtai::fold_join_commutes
//!
//! # Transcribed from the paper (eprint 2025/1903)
//!
//! §3.2 "Commitment Constraint Proof", p. 10–11, with `n_i = ∏_{j≥i} m_j`,
//! `ι = ⌈log_σ q⌉` and `k = log N` levels:
//!
//! ```text
//! cm_{n_i}  = G⁻¹_{σ,n_{i+1}κ}((I_{n_{i+1}} ⊗ A_i) · G⁻¹_{σ,n_i κ}( … (I_{n_1} ⊗ A_0) s⃗))
//! cm        = A_{log N − 1} · cm_{n_{log N − 2}}                            (Eq. 3, p. 10)
//! cm_{n_{i+1}} = G⁻¹_{σ,n_{i+2}κ}((I_{n_{i+2}} ⊗ A_{i+1}) · cm_{n_i})       (recurrence, p. 10)
//! ```
//!
//! Fig. 3 (p. 17) prints the verifier's *commitment column*, which is what
//! [`LeveledAjtai::check_lane`] implements — one call, three cases:
//!
//! ```text
//! i = 1:                 A_{log N − 1} · π₁ᶜᵐ      =? cm
//! 2 ≤ i ≤ log N − 1:     A_{log N − i} · πᵢᶜᵐ      =? [c_{i−1,0} G_{σ,κ}  c_{i−1,1} G_{σ,κ}] · πᵢ₋₁ᶜ
//! i = log N:             A₀ · s⃗_{log N}            =? [c_{log N −1,0} G_{σ,κ}  c_{log N −1,1} G_{σ,κ}] · π_{log N − 1}ᶜ
//! ```
//!
//! # Why this is the *binding* layer, and what it buys
//!
//! Appendix C step I (p. 37–39) is the reason the column above is more than an
//! algebra check: rewinding the last round with three challenge vectors
//! `c⃗⁽⁰⁾, c⃗⁽¹⁾, c⃗⁽²⁾ ∈ SS(C,2,2)` and dividing by the challenge differences
//! extracts halves with
//!
//! ```text
//! Com(c̄_{log N − 1} · s̄_{log N − 1}) = c̄_{log N − 1} · cm_{n_{log N − 2}}
//! ```
//!
//! and repeating down `log N` levels yields a relaxed opening with
//! `Com(c̄ · s̄) = c̄ · cm` and `‖c̄ s̄‖∞ ≤ 2^{log N − 1} γ_{log N}`. So the
//! extracted witness *opens the commitment*, which is what turns a
//! self-inner-product claim into a statement about the committed vector
//! (Theorem 2's hypothesis, p. 18: M-SIS must be hard for
//! `max(N·√(Nℓ)·γ_{log N}, N·√(Nℓι)·γ_{α,log N})`). §3.2, p. 11 states the
//! precondition outright: "Ajtai commitment is binding under M-SIS, which
//! requires an explicit upper bound on the norm of the committed vector".
//!
//! That is also what this module cannot give on its own: [`check_lane`]
//! authenticates the *tail*; whether the authenticated statement is binding
//! depends on the norm bound and on M-SIS hardness, which the caller supplies
//! (see [`crate::shortness::tensor_fold::NormAccounting::msis_bounds`]).

use crate::pcs::key::{apply_blockwise, RingMatrixKey};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::Ring;
use alloc::vec::Vec;
use core::fmt;

/// Why a leveled-commitment operation refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum LeveledError {
    /// `N` was not a power of two `≥ 2`, so the block axis cannot be halved
    /// down to a single root.
    BadBlockCount {
        /// Block count supplied.
        blocks: usize,
    },
    /// The chain was built with no levels.
    EmptyChain,
    /// A vector had the wrong length for the slot it was used in.
    WrongLength {
        /// Length supplied.
        got: usize,
        /// Length the slot requires.
        expected: usize,
        /// Which slot, so a mis-sized split is diagnosable.
        slot: &'static str,
    },
    /// Fig. 3 step 1: `A_{log N − 1}·m_1 ≠ cm`.
    RootMismatch {
        /// Round index (always `1`).
        round: usize,
    },
    /// Fig. 3 step 2 / final: a level's own message does not reproduce the
    /// gadget-recombination of the previous round's message.
    LevelMismatch {
        /// Level index `log N − i` whose matrix failed.
        level: usize,
    },
}

impl fmt::Display for LeveledError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LeveledError::BadBlockCount { blocks } => {
                write!(f, "block count {blocks} is not a power of two >= 2")
            }
            LeveledError::EmptyChain => write!(f, "a leveled key needs at least one level"),
            LeveledError::WrongLength {
                got,
                expected,
                slot,
            } => {
                write!(f, "{slot}: got {got} ring elements, expected {expected}")
            }
            LeveledError::RootMismatch { round } => {
                write!(
                    f,
                    "round {round}: the top level does not open the commitment"
                )
            }
            LeveledError::LevelMismatch { level } => {
                write!(
                    f,
                    "level {level}: message inconsistent with the folded predecessor"
                )
            }
        }
    }
}

/// One ring element of a chain built over `R_q = Z_q[X]/(X^D + 1)`.
type Elt<R, const D: usize> = PolyRing<R, D>;

/// `c₀·u + c₁·v` entry-wise — the folding step every split-and-fold protocol
/// shares, exposed so the chain and the sub-proofs use *one* implementation.
///
/// # Panics
/// If `u` and `v` differ in length (a structural bug, not a protocol input).
pub fn fold_with<R: Ring, const D: usize>(
    u: &[Elt<R, D>],
    v: &[Elt<R, D>],
    c: &[Elt<R, D>; 2],
) -> Vec<Elt<R, D>> {
    assert_eq!(u.len(), v.len(), "folding needs equal halves");
    u.iter()
        .zip(v.iter())
        .map(|(a, b)| c[0].clone() * a.clone() + c[1].clone() * b.clone())
        .collect()
}

/// The `log N`-level Ajtai chain of Fig. 1.
///
/// `DIGITS` is the gadget digit count (`⌈log₂ q⌉` for base 2, which is what
/// makes the split exact), `KAPPA` the matrix height, and the level matrices
/// expand from one master seed with the level index in the domain-separation
/// label — two levels of equal shape must never share a matrix.
#[derive(Clone)]
pub struct LeveledAjtai<R: Ring, const D: usize, const DIGITS: usize> {
    kappa: usize,
    blocks: usize,
    per_block: usize,
    levels: Vec<RingMatrixKey<R, D>>,
}

impl<R: Ring, const D: usize, const DIGITS: usize> fmt::Debug for LeveledAjtai<R, D, DIGITS> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LeveledAjtai")
            .field("kappa", &self.kappa)
            .field("blocks", &self.blocks)
            .field("per_block", &self.per_block)
            .field("levels", &self.levels.len())
            .finish()
    }
}

impl<R: Ring, const D: usize, const DIGITS: usize> LeveledAjtai<R, D, DIGITS> {
    /// Builds the chain. `blocks` is `N` (a power of two `≥ 2`) and
    /// `per_block` how many ring elements one block holds: `DIGITS` for a
    /// chain that commits to a gadget decomposition, larger when the leaf
    /// block carries an extra decomposition axis.
    ///
    /// # Errors
    /// [`LeveledError::BadBlockCount`] unless `blocks` is a power of two
    /// `≥ 2`, [`LeveledError::EmptyChain`] for `kappa == 0` or
    /// `per_block == 0`.
    pub fn setup(
        label: &[u8],
        seed: &[u8; 32],
        kappa: usize,
        blocks: usize,
        per_block: usize,
    ) -> Result<Self, LeveledError> {
        if blocks < 2 || !blocks.is_power_of_two() {
            return Err(LeveledError::BadBlockCount { blocks });
        }
        if kappa == 0 || per_block == 0 {
            return Err(LeveledError::EmptyChain);
        }
        let levels = blocks.trailing_zeros() as usize;
        Ok(Self {
            kappa,
            blocks,
            per_block,
            levels: (0..levels)
                .map(|j| {
                    // Level 0 consumes pairs of leaf blocks; every upper level
                    // consumes a pair of the previous level's decomposed
                    // outputs, i.e. 2·κ·DIGITS elements.
                    let cols = if j == 0 {
                        2 * per_block
                    } else {
                        2 * kappa * DIGITS
                    };
                    let mut tag = label.to_vec();
                    tag.extend_from_slice(&(j as u64).to_le_bytes());
                    RingMatrixKey::setup(&tag, seed, kappa, cols)
                })
                .collect(),
        })
    }

    /// Matrix height `κ`.
    pub const fn kappa(&self) -> usize {
        self.kappa
    }

    /// Block count `N` — the number of halvings the protocol runs.
    pub const fn blocks(&self) -> usize {
        self.blocks
    }

    /// Ring elements per leaf block.
    pub const fn per_block(&self) -> usize {
        self.per_block
    }

    /// `log N`, the number of levels.
    pub fn levels(&self) -> usize {
        self.levels.len()
    }

    /// Witness length this key accepts.
    pub fn witness_len(&self) -> usize {
        self.blocks * self.per_block
    }

    /// Length of one round message (the folded state, before splitting).
    pub fn message_len(&self) -> usize {
        2 * self.kappa * DIGITS
    }

    /// Level matrix `A_j`, innermost first.
    pub fn matrix(&self, level: usize) -> Option<&RingMatrixKey<R, D>> {
        self.levels.get(level)
    }

    /// Runs the chain bottom-up on an already-decomposed witness `s`
    /// (`G·s` is the committed value), returning `(cm, states)` where
    /// `states[j]` is the decomposed output of level `j` — the prover's
    /// private intermediate commitments.
    ///
    /// # Errors
    /// [`LeveledError::WrongLength`] if `s` is not `N · per_block` long.
    pub fn commit(
        &self,
        s: &[Elt<R, D>],
    ) -> Result<(Vec<Elt<R, D>>, Vec<Vec<Elt<R, D>>>), LeveledError> {
        if s.len() != self.witness_len() {
            return Err(LeveledError::WrongLength {
                got: s.len(),
                expected: self.witness_len(),
                slot: "leveled witness",
            });
        }
        let mut cur = s.to_vec();
        let mut states = Vec::with_capacity(self.levels.len());
        let last = self.levels.len() - 1;
        for (j, key) in self.levels.iter().enumerate() {
            let cols = key.cols();
            if cur.len() % cols != 0 {
                return Err(LeveledError::WrongLength {
                    got: cur.len(),
                    expected: (cur.len() / cols) * cols,
                    slot: "level input",
                });
            }
            let groups: Vec<&[Elt<R, D>]> = cur.chunks(cols).collect();
            if j == last && groups.len() != 1 {
                return Err(LeveledError::WrongLength {
                    got: cur.len(),
                    expected: cols,
                    slot: "root input",
                });
            }
            // `cur.len() % cols == 0` above makes the shape error unreachable.
            let out = apply_blockwise(key, &groups).expect("groups are sized by the chunking");
            if j == last {
                return Ok((out, states));
            }
            cur = crate::pcs::gadget::split::<R, D, 2, DIGITS>(&out);
            states.push(cur.clone());
        }
        unreachable!("the loop returns at the top level")
    }

    /// Fig. 3 step 1: `A_{log N − 1} · m₁ =? cm`.
    ///
    /// # Errors
    /// [`LeveledError::WrongLength`] on a message the top level cannot consume,
    /// [`LeveledError::RootMismatch`] when the top level does not open `cm`.
    pub fn check_root(&self, msg: &[Elt<R, D>], cm: &[Elt<R, D>]) -> Result<(), LeveledError> {
        let top = self.levels.last().expect("non-empty by the constructor");
        let got = top.matvec(msg).map_err(|e| LeveledError::WrongLength {
            got: e.got,
            expected: e.expected,
            slot: "root message",
        })?;
        if got == cm {
            Ok(())
        } else {
            Err(LeveledError::RootMismatch { round: 1 })
        }
    }

    /// Fig. 3 step 2 and the final round together: level `level`'s (possibly
    /// folded) message must equal the gadget recombination of the previous
    /// round's message, folded with challenge `c`.
    ///
    /// At the top of the recursion `msg` is a level state; in the final round
    /// it is the folded witness, which is why `level == 0` is admitted.
    ///
    /// # Errors
    /// [`LeveledError::WrongLength`] for a message or predecessor the level
    /// cannot consume, [`LeveledError::LevelMismatch`] when the recurrence
    /// fails.
    pub fn check_level(
        &self,
        level: usize,
        msg: &[Elt<R, D>],
        prev: &[Elt<R, D>],
        c: &[Elt<R, D>; 2],
    ) -> Result<(), LeveledError> {
        let key = self.levels.get(level).ok_or(LeveledError::WrongLength {
            got: level,
            expected: self.levels.len(),
            slot: "level index",
        })?;
        if prev.len() != self.message_len() {
            return Err(LeveledError::WrongLength {
                got: prev.len(),
                expected: self.message_len(),
                slot: "previous message",
            });
        }
        let half = prev.len() / 2;
        let joined = crate::pcs::gadget::join::<R, D, 2, DIGITS>(prev);
        let (jl, jr) = joined.split_at(half / DIGITS);
        // `G` maps `2κ·DIGITS` digits to `2κ` values; the halves pair up.
        let expect = fold_with(jl, jr, c);
        let got = key.matvec(msg).map_err(|e| LeveledError::WrongLength {
            got: e.got,
            expected: e.expected,
            slot: "level message",
        })?;
        if got == expect {
            Ok(())
        } else {
            Err(LeveledError::LevelMismatch { level })
        }
    }

    /// Folds a level state `folds` times with the round challenges, i.e. the
    /// prover's private view of the message it is about to send.
    pub fn fold_state(&self, state: &[Elt<R, D>], folds: &[[Elt<R, D>; 2]]) -> Vec<Elt<R, D>> {
        let mut cur = state.to_vec();
        for c in folds {
            let half = cur.len() / 2;
            cur = fold_with(&cur[..half], &cur[half..], c);
        }
        cur
    }

    /// The check behind the whole design: folding a digit vector and then
    /// recombining with `G` is the same as recombining first and folding the
    /// values. Verified against ring arithmetic in the tests; the per-round
    /// checks above are only sound because it holds.
    ///
    /// # Errors
    /// [`LeveledError::WrongLength`] unless `x` has this key's witness length
    /// and `c` is a challenge pair.
    pub fn fold_join_commutes(
        &self,
        x: &[Elt<R, D>],
        c: &[Elt<R, D>; 2],
    ) -> Result<bool, LeveledError> {
        if x.len() != self.witness_len() {
            return Err(LeveledError::WrongLength {
                got: x.len(),
                expected: self.witness_len(),
                slot: "fold_join_commutes input",
            });
        }
        let half = x.len() / 2;
        let fold_then_join =
            crate::pcs::gadget::join::<R, D, 2, DIGITS>(&fold_with(&x[..half], &x[half..], c));
        let join_then_fold = fold_with(
            &crate::pcs::gadget::join::<R, D, 2, DIGITS>(&x[..half]),
            &crate::pcs::gadget::join::<R, D, 2, DIGITS>(&x[half..]),
            c,
        );
        Ok(fold_then_join == join_then_fold)
    }

    /// Whether this chain's gadget decomposition is **exact** on `R_q`, i.e.
    /// whether `DIGITS` base-2 planes can represent every residue the chain
    /// will be asked to split.
    ///
    /// The paper fixes `ι = ⌈log_σ q⌉` (§2.1, p. 8) and every level of the
    /// chain re-decomposes, so a chain that is one plane too short does not
    /// merely lose precision: [`crate::pcs::gadget::split`] refuses to run.
    /// Checking here turns that into a parameter-time refusal instead of a
    /// panic inside [`LeveledAjtai::commit`].
    #[must_use]
    pub fn decomposition_is_exact(&self) -> bool {
        crate::pcs::gadget::digit_span::<2, DIGITS>()
            >= crate::pcs::gadget::representative_ceiling_of(2, R::MODULUS)
    }

    /// The prover's side of Fig. 3's commitment column: the message of round
    /// `i` is the level `log N − i − 1` intermediate commitment folded by the
    /// `i − 1` challenges already fixed (§3.2, p. 10: "The prover … folds each
    /// stored intermediate commitment entry-wise in the same manner").
    ///
    /// # Errors
    /// [`LeveledError::WrongLength`] unless `states` holds the `log N − 1`
    /// intermediates of [`commit`](Self::commit) and `challenges` has at least
    /// `log N − 2` pairs.
    pub fn lane_messages(
        &self,
        states: &[Vec<Elt<R, D>>],
        challenges: &[[Elt<R, D>; 2]],
    ) -> Result<Vec<Vec<Elt<R, D>>>, LeveledError> {
        let rounds = self.levels() - 1;
        if states.len() != rounds {
            return Err(LeveledError::WrongLength {
                got: states.len(),
                expected: rounds,
                slot: "chain intermediates",
            });
        }
        if challenges.len() < rounds.saturating_sub(1) {
            return Err(LeveledError::WrongLength {
                got: challenges.len(),
                expected: rounds.saturating_sub(1),
                slot: "chain challenges before the last round",
            });
        }
        Ok((0..rounds)
            .map(|i| self.fold_state(&states[rounds - 1 - i], &challenges[..i]))
            .collect())
    }

    /// Fig. 3's commitment column end to end: root opening, every recursion
    /// step, and the final base opening of the revealed tail.
    ///
    /// This is the *binding* check. Accepting it means the tail is the level-0
    /// opening of `cm` under `challenges`, so a claim verified against that
    /// tail is a claim about the committed vector — see the module doc's
    /// Appendix-C transcription.
    ///
    /// # Errors
    /// [`LeveledError::WrongLength`] for a lane the chain cannot consume,
    /// [`LeveledError::RootMismatch`] for round 1, [`LeveledError::LevelMismatch`]
    /// for a recursion step (level `log N − i`) or for the base opening
    /// (level `0`).
    pub fn check_lane<'a>(
        &self,
        cm: &'a [Elt<R, D>],
        msgs: &[Vec<Elt<R, D>>],
        challenges: &[[Elt<R, D>; 2]],
        tail: &'a [Elt<R, D>],
    ) -> Result<Bound<'a, R, D>, LeveledError> {
        let rounds = self.levels() - 1;
        if msgs.len() != rounds {
            return Err(LeveledError::WrongLength {
                got: msgs.len(),
                expected: rounds,
                slot: "chain messages",
            });
        }
        if challenges.len() != rounds {
            return Err(LeveledError::WrongLength {
                got: challenges.len(),
                expected: rounds,
                slot: "chain challenges",
            });
        }
        self.check_root(&msgs[0], cm)?;
        for i in 1..rounds {
            self.check_level(
                self.levels() - 1 - i,
                &msgs[i],
                &msgs[i - 1],
                &challenges[i - 1],
            )?;
        }
        self.check_level(0, tail, &msgs[rounds - 1], &challenges[rounds - 1])?;
        Ok(Bound {
            root: cm,
            tail,
            levels: self.levels(),
        })
    }
}

/// Proof that a revealed vector is the level-0 opening of a root.
///
/// Returned by [`LeveledAjtai::check_lane`]; it carries no check of its own,
/// because its *existence* is the check having passed. Downstream claims (the
/// self-inner-product of [`crate::shortness::self_ip`], the linear and
/// auxiliary lanes of [`crate::shortness::committed_norm`]) are bound to the
/// commitment exactly to the extent that they are evaluated against
/// [`Bound::tail`] rather than against a vector the prover named.
#[derive(Debug)]
pub struct Bound<'a, R: Ring, const D: usize> {
    root: &'a [Elt<R, D>],
    tail: &'a [Elt<R, D>],
    levels: usize,
}

impl<'a, R: Ring, const D: usize> Bound<'a, R, D> {
    /// The authenticated commitment root.
    pub fn root(&self) -> &'a [Elt<R, D>] {
        self.root
    }

    /// The vector this root commits to, after `log N − 1` folds.
    pub fn tail(&self) -> &'a [Elt<R, D>] {
        self.tail
    }

    /// `log N`, the number of levels the lane ran through.
    pub const fn levels(&self) -> usize {
        self.levels
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::encoding::ring_to_u32;
    use crate::foundation::sampling::from_centered;
    use crate::pcs::{RingElt, Z1Coeff, DIM};
    use algebra::ring::zq::Zq;
    use algebra::ring::PolynomialQuotientRing;
    use alloc::vec;

    /// Serval / CMNW's regime: `q = 4093` is prime and `≡ 5 (mod 8)`, so
    /// `X^D + 1` does **not** split into linears and no NTT exists — yet
    /// Lemma 1's invertibility regime is exactly what the norm argument needs.
    type Q5 = Zq<4093>;
    const MOD8: usize = 4093;
    /// `⌈log₂ 4093⌉ = 12`, and `2¹² = 4096 > q` keeps the base-2 split exact.
    const L: usize = 12;
    const SMALL: usize = 4;

    /// A uniform-ish ring element from a tiny PRNG (tests only).
    fn q5_elt(tag: u64, i: usize) -> Elt<Q5, SMALL> {
        let coeffs = (0..SMALL)
            .map(|t| Q5::from((tag * 7919 + i as u64 * 31 + t as u64 * 17) % MOD8 as u64))
            .collect();
        PolyRing::from_coefficients(coeffs)
    }

    fn digit_vec(tag: u64, len: usize) -> Vec<Elt<Q5, SMALL>> {
        (0..len)
            .map(|i| {
                let v = (tag * 13 + i as u64 * 5) % 2;
                let mut coeffs = [0u32; SMALL];
                coeffs[0] = v as u32;
                coeffs[1] = ((i as u64 + v) % 2) as u32;
                PolyRing::from_coefficients(
                    coeffs.iter().map(|&c| Q5::from(u64::from(c))).collect(),
                )
            })
            .collect()
    }

    fn key(blocks: usize) -> LeveledAjtai<Q5, SMALL, L> {
        LeveledAjtai::setup(b"test-chain", &[0x5au8; 32], 2, blocks, L).expect("key")
    }

    fn elt_q5(v: u64) -> Elt<Q5, SMALL> {
        let mut coeffs = [0u64; SMALL];
        coeffs[0] = v % MOD8 as u64;
        PolyRing::from_coefficients(coeffs.iter().map(|&c| Q5::from(c)).collect())
    }

    #[test]
    fn chain_shapes_follow_fig_1() {
        // N = 8 blocks of ell digits: state j must hold (N/2^{j+1})·κ·DIGITS
        // elements and the root must be κ of them.
        let k = key(8);
        assert_eq!(k.levels(), 3);
        assert_eq!(k.witness_len(), 8 * L);
        assert_eq!(k.message_len(), 2 * 2 * L);
        let (cm, states) = k.commit(&digit_vec(1, k.witness_len())).expect("commit");
        assert_eq!(cm.len(), 2, "the root is κ ring elements");
        assert_eq!(states.len(), 2);
        for (j, st) in states.iter().enumerate() {
            assert_eq!(
                st.len(),
                (8 / 2_usize.pow(j as u32 + 1)) * 2 * L,
                "state {j}"
            );
        }
        assert_eq!(
            k.matrix(0).expect("A_0").cols(),
            2 * L,
            "A_0 takes pairs of leaf blocks"
        );
        assert_eq!(k.matrix(1).expect("A_1").cols(), 2 * 2 * L);
    }

    #[test]
    fn every_round_check_of_fig_3_passes_for_an_honest_chain() {
        // The load-bearing positive test: root, both intermediate steps and the
        // final base opening. A wrong `G` index or a swapped challenge pair
        // breaks one of these, not all of them.
        let k = key(8);
        let s = digit_vec(3, k.witness_len());
        let (cm, states) = k.commit(&s).expect("commit");
        let cs: Vec<[Elt<Q5, SMALL>; 2]> = (0..2)
            .map(|i| [elt_q5(1 + i as u64), elt_q5(3 + i as u64)])
            .collect();
        // round 1: level 2's state unfolded
        k.check_root(&states[1], &cm).expect("fig.3 step 1");
        // round 2: level 1's state, folded once
        let m2 = k.fold_state(&states[0], &cs[..1]);
        k.check_level(1, &m2, &states[1], &cs[0])
            .expect("fig.3 step 2");
        // final round: the folded witness against level 1's message
        let s_folded = k.fold_state(&s, &cs);
        assert_eq!(s_folded.len(), 2 * L);
        k.check_level(0, &s_folded, &m2, &cs[1])
            .expect("fig.3 final base opening");
    }

    #[test]
    fn fold_join_commutes_over_the_block_axis() {
        let k = key(4);
        let c = [elt_q5(2), elt_q5(5)];
        assert!(
            k.fold_join_commutes(&digit_vec(9, k.witness_len()), &c)
                .expect("well-sized"),
            "G(fold(x)) must equal fold(G(x))"
        );
    }

    #[test]
    fn a_tampered_level_message_fails_only_its_own_level() {
        // The error must name the level, so a scheme can prove which check
        // caught which forgery rather than reporting a bare failure.
        let k = key(8);
        let (cm, states) = k.commit(&digit_vec(4, k.witness_len())).expect("commit");
        let c = [elt_q5(1), elt_q5(2)];
        let mut bad = states[1].clone();
        bad[0] = bad[0].clone() + elt_q5(7);
        assert_eq!(
            k.check_root(&bad, &cm),
            Err(LeveledError::RootMismatch { round: 1 })
        );
        let m2 = k.fold_state(&states[0], &[[c[0].clone(), c[1].clone()]]);
        assert_eq!(
            k.check_level(1, &m2, &bad, &c),
            Err(LeveledError::LevelMismatch { level: 1 }),
            "a forged predecessor must be caught at the level that consumes it"
        );
    }

    #[test]
    fn swapping_the_challenge_pair_moves_the_expected_message() {
        // Guards against `fold_with` reading `c` in the wrong order: with a
        // symmetric implementation both orders would verify.
        //
        // The witness must **not** be periodic along the block axis. Every
        // `digit_vec` is (its pattern has period two), so with an even number of
        // digits per leaf block all of `A₀`'s groups coincide, the two halves of
        // the recombined predecessor are equal, and *any* challenge pair folds
        // them the same way — the check would pass vacuously. `q5_elt` varies
        // with the index, which is what makes the refusal below mean something.
        let k = key(8);
        let s: Vec<Elt<Q5, SMALL>> = (0..k.witness_len()).map(|i| q5_elt(6, i)).collect();
        let (_, states) = k.commit(&s).expect("commit");
        let c = [elt_q5(3), elt_q5(11)];
        let flipped = [c[1].clone(), c[0].clone()];
        assert_ne!(
            k.fold_state(&states[0], &[c.clone()]),
            k.fold_state(&states[0], &[flipped.clone()]),
            "the fixture must be one where the challenge order is visible"
        );
        let m2 = k.fold_state(&states[0], &[c.clone()]);
        assert!(k.check_level(1, &m2, &states[1], &c).is_ok());
        assert_eq!(
            k.check_level(1, &m2, &states[1], &flipped),
            Err(LeveledError::LevelMismatch { level: 1 })
        );
    }

    #[test]
    fn root_and_base_openings_reject_a_substituted_commitment() {
        let k = key(4);
        let (mut cm, states) = k.commit(&digit_vec(2, k.witness_len())).expect("commit");
        cm[0] = cm[0].clone() + elt_q5(1);
        assert_eq!(
            k.check_root(&states[0], &cm),
            Err(LeveledError::RootMismatch { round: 1 })
        );
    }

    #[test]
    fn wrong_lengths_are_typed_rejections_not_panics() {
        let k = key(4);
        assert_eq!(
            k.commit(&digit_vec(1, k.witness_len() - 1)),
            Err(LeveledError::WrongLength {
                got: 4 * L - 1,
                expected: 4 * L,
                slot: "leveled witness"
            })
        );
        assert_eq!(
            k.check_root(&digit_vec(1, L), &digit_vec(2, 2)),
            Err(LeveledError::WrongLength {
                got: L,
                expected: 2 * 2 * L,
                slot: "root message"
            })
        );
        assert!(matches!(
            k.fold_join_commutes(&digit_vec(1, 3), &[elt_q5(1), elt_q5(2)]),
            Err(LeveledError::WrongLength { .. })
        ));
    }

    #[test]
    fn block_count_must_be_a_power_of_two_at_least_two() {
        for bad in [0usize, 1, 3, 5, 6] {
            assert_eq!(
                LeveledAjtai::<Q5, SMALL, L>::setup(b"x", &[0u8; 32], 2, bad, L).err(),
                Some(LeveledError::BadBlockCount { blocks: bad }),
                "{bad} blocks cannot be halved to a root"
            );
        }
        assert_eq!(
            LeveledAjtai::<Q5, SMALL, L>::setup(b"x", &[0u8; 32], 0, 4, L).err(),
            Some(LeveledError::EmptyChain)
        );
    }

    #[test]
    fn equal_shape_levels_use_different_matrices() {
        // Without the level index in the label, levels 1 and 2 of an
        // `8`-block chain would share a matrix and the chain would collapse.
        let k = key(8);
        let x = digit_vec(5, k.message_len());
        let a1 = k.matrix(1).expect("A_1").matvec(&x).expect("sized");
        let a2 = k.matrix(2).expect("A_2").matvec(&x).expect("sized");
        assert_ne!(a1, a2, "levels must not share a key");
    }

    #[test]
    fn the_seed_and_label_bind_the_whole_chain() {
        let a = key(4);
        let b =
            LeveledAjtai::<Q5, SMALL, L>::setup(b"test-chain", &[0x5bu8; 32], 2, 4, L).expect("k");
        let c = LeveledAjtai::<Q5, SMALL, L>::setup(b"other", &[0x5au8; 32], 2, 4, L).expect("k");
        let x = digit_vec(1, a.witness_len());
        assert_ne!(a.commit(&x).expect("a").0, b.commit(&x).expect("b").0);
        assert_ne!(a.commit(&x).expect("a").0, c.commit(&x).expect("c").0);
        assert_eq!(a.commit(&x).expect("a").0, a.commit(&x).expect("a2").0);
    }

    #[test]
    fn the_same_code_runs_on_the_crates_z1_instance() {
        // Cross-instance check: `DIGITS = 23`, `d = 256` (the Z1 ring), which is
        // NTT-friendly — the chain must not depend on the q ≡ 5 (mod 8) case.
        const DELTA: usize = 23;
        let k: LeveledAjtai<Z1Coeff, DIM, DELTA> =
            LeveledAjtai::setup(b"z1", &[0x11u8; 32], 2, 4, DELTA).expect("key");
        let s: Vec<RingElt> = (0..k.witness_len())
            .map(|i| {
                let mut coeffs = [0u32; DIM];
                coeffs[0] = (i % 2) as u32;
                crate::foundation::encoding::ring_from_u32::<Z1Coeff, DIM>(&coeffs)
            })
            .collect();
        let (cm, states) = k.commit(&s).expect("commit");
        assert_eq!(cm.len(), 2);
        assert_eq!(states.len(), 1);
        assert_eq!(states[0].len(), k.message_len());
        let c = [
            PolyRing::from_coefficients(vec![Z1Coeff::ONE; DIM]),
            PolyRing::from_coefficients(
                (0..DIM)
                    .map(|j| from_centered::<Z1Coeff>(if j == 0 { -1 } else { 0 }))
                    .collect(),
            ),
        ];
        k.check_root(&states[0], &cm).expect("root opens");
        let folded = k.fold_state(&s, &[c.clone()]);
        assert_eq!(folded.len(), 2 * DELTA);
        k.check_level(0, &folded, &states[0], &c)
            .expect("base opening on the Z1 instance");
        // and the digit content really is binary, so the chain is short-norm
        let max_digit = folded
            .iter()
            .flat_map(ring_to_u32::<Z1Coeff, DIM>)
            .map(u64::from)
            .max()
            .expect("non-empty witness");
        assert!(max_digit <= 1, "a base-2 decomposition is binary");
    }

    #[test]
    fn the_lane_driver_matches_the_per_round_calls() {
        // `lane_messages` + `check_lane` must be exactly the hand-rolled
        // sequence of `check_root`/`check_level` calls, or the one-call form
        // would be a second, drifting implementation of Fig. 3's column.
        let k = key(8);
        let s = digit_vec(11, k.witness_len());
        let (cm, states) = k.commit(&s).expect("commit");
        let cs: Vec<[Elt<Q5, SMALL>; 2]> = (0..2)
            .map(|i| [elt_q5(1 + i as u64), elt_q5(3 + i as u64)])
            .collect();
        let msgs = k.lane_messages(&states, &cs[..1]).expect("lane");
        assert_eq!(msgs.len(), 2);
        assert_eq!(msgs[0], states[1], "round 1 sends the top intermediate");
        assert_eq!(msgs[1], k.fold_state(&states[0], &cs[..1]));
        let tail = k.fold_state(&s, &cs);
        let bound = k
            .check_lane(&cm, &msgs, &cs, &tail)
            .expect("fig. 3 column, all three cases");
        assert_eq!(bound.root(), &cm[..]);
        assert_eq!(bound.tail(), &tail[..]);
        assert_eq!(bound.levels(), 3);
        // and the hand-rolled sequence accepts the same messages
        k.check_root(&msgs[0], &cm).expect("step 1");
        k.check_level(1, &msgs[1], &msgs[0], &cs[0])
            .expect("step 2");
        k.check_level(0, bound.tail(), &msgs[1], &cs[1])
            .expect("step 3");
    }

    #[test]
    fn check_lane_names_the_step_that_failed() {
        let k = key(8);
        let s = digit_vec(12, k.witness_len());
        let (cm, states) = k.commit(&s).expect("commit");
        let cs: Vec<[Elt<Q5, SMALL>; 2]> = (0..2)
            .map(|i| [elt_q5(2 + i as u64), elt_q5(5 + i as u64)])
            .collect();
        let msgs = k.lane_messages(&states, &cs[..1]).expect("lane");
        let tail = k.fold_state(&s, &cs);
        assert!(k.check_lane(&cm, &msgs, &cs, &tail).is_ok());
        // round 1
        let mut bad = msgs.clone();
        bad[0][0] = bad[0][0].clone() + elt_q5(3);
        assert_eq!(
            k.check_lane(&cm, &bad, &cs, &tail).err(),
            Some(LeveledError::RootMismatch { round: 1 })
        );
        // a middle recursion step: level = log N − i
        let mut bad = msgs.clone();
        bad[1][1] = bad[1][1].clone() + elt_q5(3);
        assert_eq!(
            k.check_lane(&cm, &bad, &cs, &tail).err(),
            Some(LeveledError::LevelMismatch { level: 1 })
        );
        // the base opening, which is the step that binds the *tail*
        let mut bad_tail = tail.clone();
        bad_tail[0] = bad_tail[0].clone() + elt_q5(3);
        assert_eq!(
            k.check_lane(&cm, &msgs, &cs, &bad_tail).err(),
            Some(LeveledError::LevelMismatch { level: 0 })
        );
        // a substituted root fails the same way an unrelated commitment does
        let other = key(8);
        let (cm2, _) = other
            .commit(&digit_vec(13, other.witness_len()))
            .expect("commit");
        assert_eq!(
            k.check_lane(&cm2, &msgs, &cs, &tail).err(),
            Some(LeveledError::RootMismatch { round: 1 }),
            "a different chain's root must not open this one"
        );
    }

    #[test]
    fn the_lane_refuses_a_mis_sized_message_sequence() {
        let k = key(8);
        let (cm, states) = k.commit(&digit_vec(14, k.witness_len())).expect("commit");
        let c = [elt_q5(1), elt_q5(2)];
        assert_eq!(
            k.lane_messages(&states[..1], &[c.clone()]),
            Err(LeveledError::WrongLength {
                got: 1,
                expected: 2,
                slot: "chain intermediates"
            })
        );
        assert_eq!(
            k.lane_messages(&states, &[]),
            Err(LeveledError::WrongLength {
                got: 0,
                expected: 1,
                slot: "chain challenges before the last round"
            })
        );
        let msgs = k.lane_messages(&states, &[c.clone()]).expect("lane");
        assert_eq!(
            k.check_lane(&cm, &msgs, &[c.clone()], &msgs[1]).err(),
            Some(LeveledError::WrongLength {
                got: 1,
                expected: 2,
                slot: "chain challenges"
            })
        );
    }

    #[test]
    fn a_chain_too_short_on_digits_says_so_before_it_panics() {
        // `⌈log₂ 4093⌉ = 12`: with 4 planes the level gadget cannot represent a
        // residue, and `commit` would panic inside `gadget::split`.
        let short = LeveledAjtai::<Q5, SMALL, 4>::setup(b"x", &[7u8; 32], 2, 4, 4).expect("key");
        assert!(!short.decomposition_is_exact());
        assert!(key(4).decomposition_is_exact());
    }
}
