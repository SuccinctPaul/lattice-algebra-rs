//! Self-inner-product argument (Z5; the slack-free `ℓ2` line).
//!
//! Serval (eprint 2025/1903 §4) certifies that a vector `s` has small
//! **Euclidean** norm by proving the ring identity
//!
//! ```text
//! ct( ⟨s, σ(s)⟩ ) = b        (an ordinary integer, the sum of squares)
//! ```
//!
//! with `⟨u, v⟩ = Σᵢ uᵢ·σ(vᵢ)`, `σ: X ↦ X⁻¹` the cyclotomic automorphism
//! ([`sigma_automorphism`](crate::pcs::packing::sigma_automorphism), which has
//! order two so `σ⁻¹ = σ`) and `ct` the constant coefficient. Two facts make
//! this a *norm* argument rather than an algebraic game, and both are asserted
//! against ring arithmetic in the tests below:
//!
//! ```text
//! ct(g · σ(h))  =  Σ_t g_t·h_t          (the packing.rs identity)
//! ct(⟨s, σ(s)⟩) =  Σᵢ Σ_t sᵢ[t]²        (an integer sum of squares)
//! ```
//!
//! so `b` is exactly the quantity [`super::exact_l2`] gates, and inherits its
//! wraparound-free requirement: the sum of squares must stay below `q`, else
//! the residue is ambiguous.
//!
//! # Round structure
//!
//! Split `s = (s_L ‖ s_R)`; send the four partial pairings
//!
//! ```text
//! π = (L, M₁, M₂, R) = (⟨s_L,σ s_L⟩, ⟨s_L,σ s_R⟩, ⟨s_R,σ s_L⟩, ⟨s_R,σ s_R⟩)
//! ```
//!
//! The verifier checks `ct(L + R) == carried` (valid because `s = L‖R` gives
//! `⟨s,σs⟩ = ⟨L,σL⟩ + ⟨R,σR⟩`), then carries the claim through the fold
//! `s' = c₀·s_L + c₁·s_R` using bilinearity:
//!
//! ```text
//! ⟨s', σ(s')⟩ = c₀σ(c₀)·L + c₀σ(c₁)·M₁ + c₁σ(c₀)·M₂ + c₁σ(c₁)·R = ⟨w, π⟩
//! ```
//!
//! After `rounds` halvings the remaining vector is revealed and its directly
//! recomputed norm must equal the carried claim — that terminal comparison is
//! where a forged chain dies.
//!
//! # Scope — what this does *not* prove on its own
//!
//! [`prove`]/[`verify`] is the argument over an **explicit witness**, in the
//! same transparent posture as `sumcheck`'s table mode. What it establishes by
//! itself is that the round messages, the challenges and the revealed tail are
//! *mutually consistent* with the claim `b`. It does **not** establish that `b`
//! is the norm of the vector a prover is *bound* to: nothing there ties the
//! witness to a commitment, so a prover is free to run the argument over any
//! vector it likes (and `examples/serval.rs` demonstrates exactly that).
//!
//! [`prove_bound`] / [`verify_bound`] close that gap the way the paper does —
//! by running this column *together with* Serval's leveled commitment column
//! ([`crate::pcs::leveled::LeveledAjtai::check_lane`]) over **one shared
//! challenge sequence**. §3.4, p. 14: "All sub-proofs share the same
//! `log N`-round split-and-fold recursion. In round `i`, the prover folds every
//! active witness (and its commitment state) using the same verifier
//! challenge. This reuse enforces that every sub-proof refers to the same
//! folded main witness `s⃗_{i+1}` … Accordingly, the verifier can maintain one
//! reduced claim per constraint family, and **no additional cross-consistency
//! checks are needed**." The binding is therefore (a) the shared transcript,
//! (b) the base opening `A₀ · s⃗_{log N} = …` that authenticates the tail, and
//! (c) the terminal identity evaluated *on that tail*.
//!
//! # Transcribed from the paper (eprint 2025/1903)
//!
//! Lemma 2 (p. 8, "avoid modular wraparound"):
//!
//! ```text
//! q > 2Nℓd  ⇒  a slack-free ℓ2 bound on f⃗ ∈ R_q^{Nℓ} reduces to
//!   (a) ct(⟨f⃗, σ⁻¹(f⃗)⟩) = b mod q  ∧  0 ≤ b ≤ B², and
//!   (b) coef(f⃗) ∈ {0,1}^{Nℓd}
//! ```
//!
//! The admissibility side of that implication is *not* duplicated here: it is
//! [`crate::shortness::exact_l2::direct_route_admissible`], which states the
//! same window as `S_max < q`.
//!
//! §3.2 "Quadratic Constraint Proof" (p. 12) and Fig. 3 (p. 17):
//!
//! ```text
//! πᵢ = (Lᵢ, M⁽¹⁾ᵢ, M⁽²⁾, Rᵢ) = (⟨s_L,σs_L⟩, ⟨s_L,σs_R⟩, ⟨s_R,σs_L⟩, ⟨s_R,σs_R⟩)
//! i = 1:              ct(⟨(1,0,0,1), π₁⟩) =? b
//! 2 ≤ i ≤ log N − 1:  Lᵢ + Rᵢ =? ⟨c⃗⁽ᵠᵘᵃ⁾₋₁, π₋₁⟩
//! i = log N:          ⟨s⃗_{log N}, σ⁻¹(s⃗_{log N})⟩ =? ⟨c⃗⁽ᵠᵘᵃ⁾_{log N−1}, π_{log N−1}⟩
//! c⃗⁽ᵠᵘ⁾ᵢ = (cᵢ,₀σ(cᵢ,₀), cᵢ,₀σ(cᵢ,₁), cᵢ,₁σ(cᵢ,₀), cᵢ,₁σ(cᵢ,₁))
//! ```
//!
//! **The paper contradicts itself on that weight vector** and Fig. 3 is the
//! correct reading. §3.2's display (p. 12) gives
//! `(c₀σc₀, c₁σc₁, c₀σc₁, c₁σc₀)` paired against `(L, M⁽¹, M⁽²⁾, R)`, which
//! puts `c₁σc₁` on the *cross* term; the expansion two lines earlier
//! (`⟨s₂,σ(s₂)⟩ = c₀σ(c₀)L + c₁σ(c₁)R + c₀σ(c₁)M⁽¹⁾ + c₁σ(c₀)M⁽²⁾`) requires
//! Fig. 3's order. [`weights`] and [`tensor_fold::quad_weights`] both use Fig.
//! 3's, and [`fold_identity_holds_in_the_ring`] checks it against ring
//! arithmetic rather than trusting either display.
//!
//! Note also what the middle rounds do **not** check: only `Lᵢ + R` of the
//! *current* message is constrained at round `i`; the cross terms `M⁽¹⁾ᵢ, M⁽²⁾ᵢ`
//! enter the protocol solely through the *next* round's right-hand side and the
//! final-round identity, because `c⃗⁽ᵠᵘᵃ⁾` has four non-zero entries. Appendix C
//! step II (p. 40) makes that explicit: the four components are pinned by
//! Schwartz–Zippel on the degree-2 polynomial in the challenge, at a cost of
//! `2 log N / |C|` — not by a per-round claim of their own.
//!
//! Theorem 1 (p. 18) supplies the tail bound the argument may gate with:
//! `γ_{log N} = (2T)^{log N − 1}` from `γ₁ = 1` (binary coordinates) and
//! `γ = √(2ℓd)·γ_{log N}`, where `T = ‖c‖_{op,∞} = ‖c‖₁ = w₁ + 2w₂` for the
//! pool of §3.6 (p. 20). [`NormAccounting::bound_sq`] computes it.
//!
//! [`tensor_fold::quad_weights`]: crate::shortness::tensor_fold::quad_weights
//! [`NormAccounting::bound_sq`]: crate::shortness::tensor_fold::NormAccounting::bound_sq

use crate::foundation::encoding::ring_to_u32;
use crate::foundation::fs::absorb_rings;
use crate::foundation::sampling::centered_bounded_poly;
use crate::pcs::leveled::{fold_with, LeveledAjtai, LeveledError};
use crate::pcs::packing::sigma_automorphism;
use crate::pcs::{RingElt, Z1Coeff, DIM};
use crate::shortness::tensor_fold::{pool_challenge, square_sum};
use algebra::crypto::sampling::BitStream;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// One shared domain label: prover and verifier derive challenges through the
/// same function, which is the failure mode that broke `pcs::mle`'s opening.
const FS_DOMAIN: &[u8] = b"lattice-algebra/Z5/self-ip";

/// The label of the *bound* argument's transcript.
///
/// Separate on purpose: a bound proof absorbs the commitment column too, so
/// reusing [`FS_DOMAIN`] would let a proof be replayed against the wrong
/// binding scope.
const FS_DOMAIN_BOUND: &[u8] = b"lattice-algebra/Z5/self-ip-bound";

/// The four partial pairings of one round, in the order the weights use:
/// `(⟨L,σL⟩, ⟨L,σR⟩, ⟨R,σL⟩, ⟨R,σR⟩)`.
pub type RoundMessage = [RingElt; 4];

/// Typed rejection.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SelfIpError {
    /// The vector was too short or not divisible by `2^rounds`.
    BadLength {
        /// Length supplied.
        len: usize,
        /// Smallest length the round count accepts.
        needed: usize,
    },
    /// A round's own top-level norm contradicts the claim carried into it.
    ClaimMismatch {
        /// Round index.
        round: usize,
        /// `ct(L + R)` for this round.
        got: u64,
        /// The carried claim.
        expected: u64,
    },
    /// The revealed tail's directly recomputed norm contradicts the claim.
    TerminalMismatch {
        /// Norm recomputed from the tail.
        got: u64,
        /// Claim carried into the terminal step.
        expected: u64,
    },
    /// The revealed tail is above the bound, so nothing is certified.
    NotShort {
        /// Largest coefficient magnitude in the tail.
        norm: u64,
        /// Bound supplied by the caller.
        bound: u64,
    },
    /// Fig. 3's commitment column refused, so the revealed tail is **not** the
    /// committed vector's folding and the claim says nothing about `cm`.
    Binding(LeveledError),
    /// The two columns of a bound proof disagree about how many rounds ran.
    RoundCountMismatch {
        /// Messages in the commitment column.
        chain: usize,
        /// Messages in the quadratic column.
        quad: usize,
        /// `log N − 1`, what the chain requires.
        expected: usize,
    },
    /// The revealed tail's exact squared `ℓ2` norm is above the Theorem-1
    /// admissibility bound, so the binding argument does not apply to it.
    TailNotAdmissible {
        /// `‖s_{log N}‖²` as an exact integer.
        norm_sq: u128,
        /// `γ² = 2ℓd · γ_{log N}²`.
        bound_sq: u128,
    },
    /// The tail's exact squared norm could not be accumulated, so the
    /// admissibility gate has nothing to compare against.
    TailNormOverflow,
}

impl fmt::Display for SelfIpError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SelfIpError::BadLength { len, needed } => {
                write!(
                    f,
                    "length {len} cannot be halved as requested (needs >= {needed})"
                )
            }
            SelfIpError::ClaimMismatch {
                round,
                got,
                expected,
            } => write!(
                f,
                "round {round}: ct(L+R) = {got} but the claim is {expected}"
            ),
            SelfIpError::TerminalMismatch { got, expected } => {
                write!(f, "tail squares to {got}, carried claim says {expected}")
            }
            SelfIpError::NotShort { norm, bound } => {
                write!(f, "tail norm {norm} exceeds the allowed {bound}")
            }
            SelfIpError::Binding(source) => {
                write!(f, "commitment column: {source}")
            }
            SelfIpError::RoundCountMismatch {
                chain,
                quad,
                expected,
            } => write!(
                f,
                "the two columns disagree: {chain} chain messages, {quad} quadratic \
                 messages, the chain has {expected} rounds"
            ),
            SelfIpError::TailNotAdmissible { norm_sq, bound_sq } => write!(
                f,
                "tail squared norm {norm_sq} exceeds the Theorem-1 bound {bound_sq}"
            ),
            SelfIpError::TailNormOverflow => {
                write!(f, "the tail's squared norm cannot be accumulated")
            }
        }
    }
}

/// The zero ring element.
fn zero_elt() -> RingElt {
    RingElt::from_coefficients(vec![Z1Coeff::ZERO; DIM])
}

/// `⟨u, σ(v)⟩ = Σᵢ uᵢ · σ(vᵢ)`.
///
/// # Panics
/// If the vectors differ in length.
pub fn hermitian(u: &[RingElt], v: &[RingElt]) -> RingElt {
    assert_eq!(u.len(), v.len(), "hermitian pairing needs equal lengths");
    let mut acc = zero_elt();
    for (a, b) in u.iter().zip(v.iter()) {
        acc += a.clone() * sigma_automorphism(b);
    }
    acc
}

/// `⟨s, σ(s)⟩`; its constant term is the integer sum of squares.
pub fn square(s: &[RingElt]) -> RingElt {
    hermitian(s, s)
}

/// The constant coefficient as a plain integer.
pub fn constant_term(x: &RingElt) -> u64 {
    u64::from(ring_to_u32::<Z1Coeff, DIM>(x)[0])
}

/// The fold weights `(c₀σ(c₀), c₀σ(c₁), c₁σ(c₀), c₁σ(c₁))`, ordered to match
/// [`RoundMessage`].
pub fn weights(c0: &RingElt, c1: &RingElt) -> RoundMessage {
    let pair = |a: &RingElt, b: &RingElt| a.clone() * sigma_automorphism(b);
    [pair(c0, c0), pair(c0, c1), pair(c1, c0), pair(c1, c1)]
}

/// `Σⱼ wⱼ · πⱼ`.
fn combine(w: &RoundMessage, pi: &RoundMessage) -> RingElt {
    let mut acc = zero_elt();
    for (a, b) in w.iter().zip(pi.iter()) {
        acc += a.clone() * b.clone();
    }
    acc
}

/// Ternary ring challenges for round `i`, bound to the public claim and to
/// every message sent up to and **including** this round — so the prover
/// cannot see the challenge before committing to `π`.
fn challenges(claim: u64, rounds_through_i: &[RoundMessage]) -> [RingElt; 2] {
    let mut tr = Transcript::<Shake256Xof>::new(FS_DOMAIN);
    tr.absorb(b"claim", &claim.to_le_bytes());
    for (slot, pi) in rounds_through_i.iter().enumerate() {
        for elt in pi.iter() {
            let bytes: Vec<u8> = ring_to_u32::<Z1Coeff, DIM>(elt)
                .into_iter()
                .flat_map(|c| c.to_le_bytes())
                .collect();
            tr.absorb(b"pi", &bytes);
        }
        tr.absorb(b"slot", &(slot as u64).to_le_bytes());
    }
    let seed = tr.challenge_bytes(64);
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(b"C");
    xof.absorb(&seed);
    let mut stream = BitStream::new(&mut xof);
    [
        centered_bounded_poly::<Z1Coeff, Shake256Xof, DIM>(&mut stream, 1),
        centered_bounded_poly::<Z1Coeff, Shake256Xof, DIM>(&mut stream, 1),
    ]
}

/// A completed self-inner-product argument.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SelfIpProof {
    /// One [`RoundMessage`] per halving.
    pub rounds: Vec<RoundMessage>,
    /// The vector revealed at the end (`len = N / 2^rounds`).
    pub tail: Vec<RingElt>,
}

impl SelfIpProof {
    /// Proof size in ring elements.
    pub fn size(&self) -> usize {
        self.rounds.len() * 4 + self.tail.len()
    }
}

/// Splits a vector into contiguous halves.
fn halves(s: &[RingElt]) -> (Vec<RingElt>, Vec<RingElt>) {
    let mid = s.len() / 2;
    (s[..mid].to_vec(), s[mid..].to_vec())
}

/// Proves `ct(⟨s, σ(s)⟩) = b` by halving `s` `rounds` times.
///
/// Returns the honest claim `b` together with the proof — `b` is derived from
/// the witness, never supplied by the caller, so a prover cannot ask to prove
/// a norm it does not have.
///
/// # Errors
/// [`SelfIpError::BadLength`] if `s.len()` is below `2^rounds` or not a
/// multiple of it.
pub fn prove(s: &[RingElt], rounds: usize) -> Result<(u64, SelfIpProof), SelfIpError> {
    let blocks = 1usize << rounds;
    // `rounds` halvings take `N → N/2 → … → N/2^rounds`, so the last split
    // still needs two elements: `N ≥ 2^rounds` and `N` divisible by it.
    if s.len() < blocks || s.len() % blocks != 0 {
        return Err(SelfIpError::BadLength {
            len: s.len(),
            needed: blocks,
        });
    }
    let claim = constant_term(&square(s));
    let mut current = s.to_vec();
    let mut msgs: Vec<RoundMessage> = Vec::with_capacity(rounds);
    for _ in 0..rounds {
        let (left, right) = halves(&current);
        let pi: RoundMessage = [
            square(&left),
            hermitian(&left, &right),
            hermitian(&right, &left),
            square(&right),
        ];
        msgs.push(pi);
        let [c0, c1] = challenges(claim, &msgs);
        current = left
            .iter()
            .zip(right.iter())
            .map(|(l, r)| c0.clone() * l.clone() + c1.clone() * r.clone())
            .collect();
    }
    Ok((
        claim,
        SelfIpProof {
            rounds: msgs,
            tail: current,
        },
    ))
}

/// Fig. 3's quadratic column, given the challenge pair each round used.
///
/// Collects **every** failure instead of stopping at the first one. Under
/// Fiat–Shamir a tampered message moves every later challenge, so a
/// short-circuiting verifier reports whichever check happens to run first and
/// leaves the checks behind it indistinguishable from checks that never run.
///
/// The carry rule needs no claim to survive a failure: round `i`'s carried
/// value is `ct(⟨c̃, π_{i−1}⟩)`, computed from the *messages*, so a broken
/// exposure at round 1 still lets rounds 2… be evaluated and reported.
fn quad_column(b: u64, proof: &SelfIpProof, cs: &[[RingElt; 2]]) -> Vec<SelfIpError> {
    let mut out = Vec::new();
    let mut carried = b;
    for (i, pi) in proof.rounds.iter().enumerate() {
        // `s = L‖R` ⇒ `⟨s,σs⟩ = ⟨L,σL⟩ + ⟨R,σR⟩`, so this round's own L and R
        // must reproduce the claim carried into it.
        let here = (constant_term(&pi[0]) + constant_term(&pi[3])) % Z1Coeff::MODULUS;
        if here != carried {
            out.push(SelfIpError::ClaimMismatch {
                round: i,
                got: here,
                expected: carried,
            });
        }
        let [c0, c1] = &cs[i];
        carried = constant_term(&combine(&weights(c0, c1), pi));
    }
    let tail_norm = constant_term(&square(&proof.tail));
    if tail_norm != carried {
        out.push(SelfIpError::TerminalMismatch {
            got: tail_norm,
            expected: carried,
        });
    }
    out
}

/// The challenge sequence [`verify`] uses: round `i`'s pair is drawn after
/// absorbing every message up to and including `π_i`.
fn ternary_sequence(b: u64, proof: &SelfIpProof) -> Vec<[RingElt; 2]> {
    (0..proof.rounds.len())
        .map(|i| challenges(b, &proof.rounds[..=i]))
        .collect()
}

/// Verifier.
///
/// `tail_bound` must come from the instance's slack accounting: with ternary
/// ring challenges every halving multiplies the tail's norm, so a bound that
/// is too tight rejects honest proofs and one that is too loose certifies
/// nothing. [`super::exact_l2`] is what turns the accepted `b` into a norm
/// statement, and it requires `b < q`.
///
/// Reports the **first** failure of [`quad_column`]; see it for the full set.
///
/// # Errors
/// See [`SelfIpError`].
pub fn verify(b: u64, proof: &SelfIpProof, tail_bound: u64) -> Result<(), SelfIpError> {
    let cs = ternary_sequence(b, proof);
    let mut errors = quad_column(b, proof, &cs);
    let norm = proof
        .tail
        .iter()
        .flat_map(ring_to_u32::<Z1Coeff, DIM>)
        .map(|c| Z1Coeff::from(u64::from(c)).abs_infinity())
        .max()
        .unwrap_or(0);
    if norm > tail_bound {
        errors.push(SelfIpError::NotShort {
            norm,
            bound: tail_bound,
        });
    }
    errors.into_iter().next().map_or(Ok(()), Err)
}

/// Draws the shared challenge pair of a **bound** proof.
///
/// Both columns of round `i` are absorbed before the draw, which is the whole
/// mechanism: §3.4, p. 14 makes the shared challenge the reason "every
/// sub-proof refers to the same folded main witness", and it is why the paper
/// needs no cross-consistency check between the commitment column and the
/// quadratic one. Absorbing only one column would let the two lanes fold
/// *different* vectors and still each satisfy its own equations.
fn bound_challenges(
    root: &[RingElt],
    claim: u64,
    chain_through: &[Vec<RingElt>],
    quad_through: &[RoundMessage],
    w1: u32,
    w2: u32,
) -> [RingElt; 2] {
    let mut tr = Transcript::<Shake256Xof>::new(FS_DOMAIN_BOUND);
    absorb_rings::<Shake256Xof, Z1Coeff, DIM>(&mut tr, b"cm", root);
    tr.absorb(b"claim", &claim.to_le_bytes());
    for (slot, (cm, pi)) in chain_through.iter().zip(quad_through.iter()).enumerate() {
        absorb_rings::<Shake256Xof, Z1Coeff, DIM>(&mut tr, b"chain", cm);
        absorb_rings::<Shake256Xof, Z1Coeff, DIM>(&mut tr, b"quad", pi);
        tr.absorb(b"slot", &(slot as u64).to_le_bytes());
    }
    let seed = tr.challenge_bytes(64);
    let mut xof = crate::foundation::fs::seed_stream::<Shake256Xof>(b"C", &seed);
    let mut stream = BitStream::new(&mut xof);
    let draw = |stream: &mut BitStream<'_, Shake256Xof>| {
        pool_challenge::<Z1Coeff, Shake256Xof, DIM>(stream, w1, w2)
            .expect("the challenge pool must fit the ring degree")
    };
    [draw(&mut stream), draw(&mut stream)]
}

/// A self-inner-product claim **bound to a leveled commitment**: Fig. 3's
/// commitment column and quadratic column, folded by one challenge sequence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BoundProof {
    /// `πᵢᵐ ∈ R^{2κι}` per round: the folded intermediate commitments.
    pub chain: Vec<Vec<RingElt>>,
    /// `πᵢᵠᵘᵃ = (L, M₁, M₂, R)` per round, plus the revealed tail both columns
    /// open against.
    pub ip: SelfIpProof,
}

/// Proves `ct(⟨s, σ(s)⟩) = b` **and** that `s` is the vector `cm` commits to.
///
/// Returns `(b, cm, proof)`: `b` is derived from `s` and `cm` is the chain's
/// root for `s`, so neither is a caller assertion. Runs `log N − 1` rounds,
/// where `log N` is the chain's level count, and reveals the same `2·per_block`
/// tail the chain's level-0 relation consumes.
///
/// `w1`/`w2` size the challenge pool (see
/// [`pool_challenge`](crate::shortness::tensor_fold::pool_challenge)); the
/// pool's operator norm `T = w₁ + 2w₂` is what
/// [`NormAccounting`](crate::shortness::tensor_fold::NormAccounting) turns into
/// the tail bound.
///
/// # Errors
/// [`SelfIpError::BadLength`] if `s` is not the chain's witness length or
/// cannot be halved `log N − 1` times, [`SelfIpError::Binding`] if the chain
/// refuses to build the lane.
pub fn prove_bound<const DIGITS: usize>(
    chain: &LeveledAjtai<Z1Coeff, DIM, DIGITS>,
    s: &[RingElt],
    w1: u32,
    w2: u32,
) -> Result<(u64, Vec<RingElt>, BoundProof), SelfIpError> {
    let rounds = chain.levels() - 1;
    if s.len() != chain.witness_len() {
        return Err(SelfIpError::BadLength {
            len: s.len(),
            needed: chain.witness_len(),
        });
    }
    let (root, states) = chain.commit(s).map_err(SelfIpError::Binding)?;
    let claim = constant_term(&square(s));
    let mut current = s.to_vec();
    let mut chain_msgs: Vec<Vec<RingElt>> = Vec::with_capacity(rounds);
    let mut quad_msgs: Vec<RoundMessage> = Vec::with_capacity(rounds);
    let mut cs: Vec<[RingElt; 2]> = Vec::with_capacity(rounds);
    for i in 0..rounds {
        let (left, right) = halves(&current);
        quad_msgs.push([
            square(&left),
            hermitian(&left, &right),
            hermitian(&right, &left),
            square(&right),
        ]);
        chain_msgs.push(chain.fold_state(&states[rounds - 1 - i], &cs));
        let c = bound_challenges(&root, claim, &chain_msgs, &quad_msgs, w1, w2);
        cs.push(c.clone());
        let half = current.len() / 2;
        current = fold_with(&current[..half], &current[half..], &c);
    }
    Ok((
        claim,
        root,
        BoundProof {
            chain: chain_msgs,
            ip: SelfIpProof {
                rounds: quad_msgs,
                tail: current,
            },
        },
    ))
}

/// Every rejection of a bound proof, as a set rather than the first one.
///
/// Runs Fig. 3's two columns and the tail's admissibility gate:
///
/// ```text
/// commitment column   A_{log N − 1}·π₁ = cm, the recurrences, A₀·s_log N = …
/// quadratic column    ct(L₁+R₁) = b, the carries, ⟨s_log N, σ(s_log N)⟩ = ⟨c̃, π⟩
/// admissibility       ‖s_log N‖² ≤ γ²   (Theorem 1, p. 18)
/// ```
#[must_use]
pub fn bound_report<const DIGITS: usize>(
    chain: &LeveledAjtai<Z1Coeff, DIM, DIGITS>,
    root: &[RingElt],
    b: u64,
    proof: &BoundProof,
    tail_bound_sq: u128,
    w1: u32,
    w2: u32,
) -> Vec<SelfIpError> {
    let rounds = chain.levels() - 1;
    if proof.chain.len() != rounds || proof.ip.rounds.len() != rounds {
        return vec![SelfIpError::RoundCountMismatch {
            chain: proof.chain.len(),
            quad: proof.ip.rounds.len(),
            expected: rounds,
        }];
    }
    let cs: Vec<[RingElt; 2]> = (0..rounds)
        .map(|i| bound_challenges(root, b, &proof.chain[..=i], &proof.ip.rounds[..=i], w1, w2))
        .collect();
    let mut out = Vec::new();
    if let Err(e) = chain.check_lane(root, &proof.chain, &cs, &proof.ip.tail) {
        out.push(SelfIpError::Binding(e));
    }
    out.extend(quad_column(b, &proof.ip, &cs));
    match square_sum(&proof.ip.tail) {
        Ok(norm_sq) => {
            if norm_sq > tail_bound_sq {
                out.push(SelfIpError::TailNotAdmissible {
                    norm_sq,
                    bound_sq: tail_bound_sq,
                });
            }
        }
        // The exact integer norm could not be accumulated, so the gate cannot
        // decide anything and refuses rather than wave the tail through.
        Err(_) => out.push(SelfIpError::TailNormOverflow),
    }
    out
}

/// Verifier for the bound argument: accepts exactly when [`bound_report`] is
/// empty, and reports its first rejection otherwise.
///
/// # Errors
/// See [`SelfIpError`]; the rejection names the column that refused.
pub fn verify_bound<const DIGITS: usize>(
    chain: &LeveledAjtai<Z1Coeff, DIM, DIGITS>,
    root: &[RingElt],
    b: u64,
    proof: &BoundProof,
    tail_bound_sq: u128,
    w1: u32,
    w2: u32,
) -> Result<(), SelfIpError> {
    bound_report(chain, root, b, proof, tail_bound_sq, w1, w2)
        .into_iter()
        .next()
        .map_or(Ok(()), Err)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;

    fn elt(seed: u64, offset: usize) -> RingElt {
        let coeffs: Vec<_> = (0..DIM)
            .map(|j| {
                let v = (seed as i64 * 13 + offset as i64 * 5 + j as i64) % 11;
                from_centered::<Z1Coeff>(v - 5)
            })
            .collect();
        RingElt::from_coefficients(coeffs)
    }

    fn vector(len: usize) -> Vec<RingElt> {
        (0..len).map(|i| elt(3, i)).collect()
    }

    #[test]
    fn constant_term_is_the_integer_sum_of_squares() {
        // The load-bearing semantic claim: ct(⟨s,σ(s)⟩) equals the ordinary
        // integer Σ sᵢ[t]² of the centered coefficients, not a ring value.
        let s = vector(4);
        let expect: i64 = s
            .iter()
            .flat_map(ring_to_u32::<Z1Coeff, DIM>)
            .map(|c| Z1Coeff::from(u64::from(c)).centered())
            .map(|v| v * v)
            .sum();
        let got = constant_term(&square(&s)) as i64;
        assert_eq!(
            got,
            expect.rem_euclid(i64::try_from(Z1Coeff::MODULUS).unwrap()),
            "the constant term must be the integer squared norm"
        );
    }

    #[test]
    fn fold_identity_holds_in_the_ring() {
        // ⟨s', σ(s')⟩ == Σ wⱼπⱼ with s' = c₀s_L + c₁s_R. Checked directly on
        // ring elements: if this fails, the verifier's carry rule is wrong.
        let s = vector(8);
        let (l, r) = halves(&s);
        let c0 = elt(1, 0);
        let c1 = elt(2, 1);
        let folded: Vec<RingElt> = l
            .iter()
            .zip(r.iter())
            .map(|(a, b)| c0.clone() * a.clone() + c1.clone() * b.clone())
            .collect();
        let pi: RoundMessage = [square(&l), hermitian(&l, &r), hermitian(&r, &l), square(&r)];
        assert_eq!(square(&folded), combine(&weights(&c0, &c1), &pi));
    }

    #[test]
    fn honest_proof_verifies_at_several_depths() {
        let s = vector(16);
        for rounds in 1..=4 {
            let (b, proof) = prove(&s, rounds).expect("prove");
            assert_eq!(proof.rounds.len(), rounds);
            assert_eq!(proof.tail.len(), s.len() / (1 << rounds));
            // Generous bound: this test is about the argument, not the growth.
            verify(b, &proof, u64::MAX).expect("honest proof must verify");
        }
    }

    #[test]
    fn the_claim_is_derived_not_declared() {
        // Proving a *smaller* norm than the witness has must fail, and fail on
        // the very first round's check.
        let s = vector(8);
        let (b, proof) = prove(&s, 3).expect("prove");
        assert!(b > 1, "the test vector must have a nontrivial norm");
        let wrong = b - 1;
        assert!(
            matches!(
                verify(wrong, &proof, u64::MAX),
                Err(SelfIpError::ClaimMismatch { round: 0, .. })
            ),
            "a false claim must break at round 0"
        );
    }

    #[test]
    fn a_forged_round_message_is_caught_by_the_next_check() {
        let s = vector(8);
        let (b, mut proof) = prove(&s, 3).expect("prove");
        proof.rounds[1][0] = proof.rounds[1][0].clone() + elt(7, 0);
        assert!(verify(b, &proof, u64::MAX).is_err(), "tampered π rejected");
    }

    #[test]
    fn a_forged_tail_is_caught_by_the_terminal_check() {
        let s = vector(8);
        let (b, mut proof) = prove(&s, 3).expect("prove");
        proof.tail[0] = proof.tail[0].clone() + elt(9, 2);
        assert!(
            matches!(
                verify(b, &proof, u64::MAX),
                Err(SelfIpError::TerminalMismatch { .. })
            ),
            "the tail is recomputed, so substituting it breaks the carry"
        );
    }

    #[test]
    fn challenges_depend_on_the_message_they_follow() {
        let s = vector(8);
        let (b, proof) = prove(&s, 2).expect("prove");
        let mut other = proof.clone();
        other.rounds[0][3] = other.rounds[0][3].clone() + elt(4, 4);
        let c_first = challenges(b, &proof.rounds[..1]);
        let c_moved = challenges(b, &other.rounds[..1]);
        // Compare whole challenges, not one coefficient: a ternary ring
        // element's constant term is 0 with probability ~1/3, which would make
        // this test pass or fail on luck.
        assert_ne!(c_first[0], c_moved[0], "π must be bound before the draw");
        assert_ne!(c_first[1], c_moved[1]);
    }

    #[test]
    fn tail_bound_is_enforced() {
        let s = vector(8);
        let (b, proof) = prove(&s, 3).expect("prove");
        let norm = proof
            .tail
            .iter()
            .flat_map(ring_to_u32::<Z1Coeff, DIM>)
            .map(|c| Z1Coeff::from(u64::from(c)).abs_infinity())
            .max()
            .unwrap();
        assert!(verify(b, &proof, norm).is_ok(), "bound exactly at the norm");
        assert!(
            matches!(
                verify(b, &proof, norm.saturating_sub(1)),
                Err(SelfIpError::NotShort { .. })
            ),
            "one below must refuse"
        );
    }

    #[test]
    fn rejects_vectors_too_short_for_the_requested_depth() {
        assert_eq!(
            prove(&vector(4), 3),
            Err(SelfIpError::BadLength { len: 4, needed: 8 })
        );
    }

    #[test]
    fn proof_size_matches_the_four_elements_per_round_formula() {
        let s = vector(16);
        let (_, proof) = prove(&s, 4).expect("prove");
        assert_eq!(proof.size(), 4 * 4 + 1, "4 ring elements per round + tail");
    }

    /// The crate's Z1 instance, sized so the base-2 chain is exact:
    /// `2²³ = 8388608 > q = 8380417`.
    const DELTA: usize = 23;
    /// Challenge pool `P_{1,1}`, whose operator norm is `T = w₁ + 2w₂ = 3`.
    const POOL: (u32, u32) = (1, 1);

    /// A binary digit vector of the chain's witness length: one set coefficient
    /// per ring element, so `coef(s) ∈ {0,1}` and `‖s‖²` is the number of set
    /// bits.
    fn bound_witness(chain: &LeveledAjtai<Z1Coeff, DIM, DELTA>, shift: usize) -> Vec<RingElt> {
        (0..chain.witness_len())
            .map(|i| {
                let mut coeffs = [0u32; DIM];
                coeffs[0] = u32::from((i + shift) % 3 == 0);
                crate::foundation::encoding::ring_from_u32::<Z1Coeff, DIM>(&coeffs)
            })
            .collect()
    }

    /// A two-block chain: `log N = 2`, so one message round and a revealed tail
    /// of `2·ℓ` ring elements.
    fn bound_chain() -> LeveledAjtai<Z1Coeff, DIM, DELTA> {
        LeveledAjtai::setup(b"self-ip/binding", &[0x42u8; 32], 2, 4, DELTA).expect("chain")
    }

    /// The challenge sequence a bound proof actually used: round `i`'s pair is
    /// drawn after absorbing the statement and both columns up to `πᵢ`, which is
    /// what lets a test ask whether a *single* column is internally consistent
    /// rather than accidentally re-deriving the standalone transcript's.
    fn bound_cs(root: &[RingElt], b: u64, proof: &BoundProof) -> Vec<[RingElt; 2]> {
        (0..proof.chain.len())
            .map(|i| {
                bound_challenges(
                    root,
                    b,
                    &proof.chain[..=i],
                    &proof.ip.rounds[..=i],
                    POOL.0,
                    POOL.1,
                )
            })
            .collect()
    }

    /// Theorem 1's admissibility bound on the revealed tail: `γ_log N = (2T)^{log N−1}`
    /// from `γ₁ = 1`, lifted from `ℓ∞` to `ℓ₂` by the tail's coordinate count.
    fn bound_tail_bound(chain: &LeveledAjtai<Z1Coeff, DIM, DELTA>) -> u128 {
        crate::shortness::tensor_fold::NormAccounting {
            rounds: chain.levels() - 1,
            t_op: u64::from(POOL.0) + 2 * u64::from(POOL.1),
            initial: 1,
            base_len: DELTA * DIM / 2,
        }
        .bound_sq()
    }

    #[test]
    fn a_bound_proof_verifies_and_its_tail_is_the_committed_one() {
        let chain = bound_chain();
        let s = bound_witness(&chain, 0);
        let (b, cm, proof) = prove_bound(&chain, &s, POOL.0, POOL.1).expect("prove_bound");
        assert_eq!(proof.chain.len(), chain.levels() - 1);
        assert_eq!(proof.ip.tail.len(), 2 * DELTA);
        assert_eq!(
            b as u128,
            crate::shortness::tensor_fold::square_sum(&s).expect("norm"),
            "b must be the exact integer squared norm, not a residue"
        );
        verify_bound(
            &chain,
            &cm,
            b,
            &proof,
            bound_tail_bound(&chain),
            POOL.0,
            POOL.1,
        )
        .expect("an honest bound proof must verify");
        // The tail is the committed vector's folding, so opening it against a
        // *different* root is the refusal that `verify` cannot produce.
        let other = bound_witness(&chain, 1);
        let (b2, cm2, _) = prove_bound(&chain, &other, POOL.0, POOL.1).expect("prove s2");
        assert_ne!(cm, cm2, "different witnesses must commit differently");
        let report = bound_report(
            &chain,
            &cm2,
            b,
            &proof,
            bound_tail_bound(&chain),
            POOL.0,
            POOL.1,
        );
        assert!(
            report
                .iter()
                .any(|e| matches!(e, SelfIpError::Binding(LeveledError::RootMismatch { .. }))),
            "a substituted root must break the commitment column: {report:?}"
        );
        let _ = b2;
    }

    #[test]
    fn the_unbound_argument_cannot_tell_which_vector_it_proved() {
        // The gap `prove_bound` closes, stated as a fact about the code: two
        // witnesses that are permutations of each other have the same squared
        // norm, so the bare argument's transcript is valid for both — and it has
        // no way to know which one the prover was bound to.
        let chain = bound_chain();
        let s1 = bound_witness(&chain, 0);
        let mut s2 = s1.clone();
        // Swap two set bits: the multiset of ring elements is preserved.
        let hit = s1
            .iter()
            .position(|e| e.coefficients()[0] == Z1Coeff::ONE)
            .expect("a set bit");
        let miss = s1
            .iter()
            .position(|e| e.coefficients()[0] == Z1Coeff::ZERO)
            .expect("an unset bit");
        s2[hit] = zero_elt();
        s2[miss] = one_at_zero();
        let (b1, p1) = prove(&s1, 1).expect("prove s1");
        let (b2, p2) = prove(&s2, 1).expect("prove s2");
        assert_eq!(b1, b2, "a permutation preserves the squared norm");
        assert_eq!(
            p1.size(),
            p2.size(),
            "the two transcripts have the same shape, so nothing about their \
             size distinguishes the vectors either"
        );
        verify(b1, &p2, u64::MAX).expect("the bare argument accepts the other vector's proof");
        verify(b2, &p1, u64::MAX).expect("and in the other direction");
        let (_, cm1, bound1) = prove_bound(&chain, &s1, POOL.0, POOL.1).expect("bound s1");
        let (_, cm2, bound2) = prove_bound(&chain, &s2, POOL.0, POOL.1).expect("bound s2");
        assert_ne!(cm1, cm2);
        // Each quadratic column satisfies the quadratic checks **under the
        // challenges it was actually folded with** — which is the precise sense
        // in which it is only chain-consistent. (It is not a standalone
        // [`verify`] proof: the bound transcript absorbs the commitment column,
        // so the two derivations differ by construction.)
        assert!(
            quad_column(b1, &bound1.ip, &bound_cs(&cm1, b1, &bound1)).is_empty(),
            "s1's own quadratic column must be clean against its own challenges"
        );
        assert!(
            quad_column(b2, &bound2.ip, &bound_cs(&cm2, b2, &bound2)).is_empty(),
            "and so must s2's"
        );
        // Splicing the honest chain column of s1 with the honest quadratic
        // column of s2 keeps every *per-column* equation true; what refuses is
        // the base opening `A₀ · s_log N = …`, i.e. exactly the step that
        // authenticates the tail the terminal identity is read off.
        //
        // For this fixture that is the *only* refusal, and the reason is worth
        // writing down: `s` is a 0/1 digit vector whose two halves never align
        // (`46 ≡ 1 (mod 3)`), so `M₁ = M₂ = Σᵢ Lᵢσ(Rᵢ) = 0`, and every pool
        // element of `P_{1,1}` has `ct(cσ(c)) = w₁ + 4w₂ = 5`. The carried claim
        // is therefore `5·(L + R) = 5b` for *every* challenge, and so is
        // `ct(⟨s', σ(s')⟩)` — the quadratic column cannot distinguish the two
        // permutations at all. Only the commitment column can.
        let mut mixed = bound1;
        mixed.ip = bound2.ip;
        let report = bound_report(
            &chain,
            &cm1,
            b1,
            &mixed,
            bound_tail_bound(&chain),
            POOL.0,
            POOL.1,
        );
        assert_eq!(
            report,
            vec![SelfIpError::Binding(LeveledError::LevelMismatch {
                level: 0
            })],
            "the spliced proof must die on the base opening and on nothing else: \
             {report:?}"
        );
    }

    #[test]
    fn the_bound_challenge_absorbs_both_columns() {
        // If the draw ignored the commitment column, the two lanes could fold
        // different vectors and each still satisfy its own equations — which is
        // exactly the cross-consistency §3.4, p. 14 claims the shared challenge
        // buys for free.
        let chain = bound_chain();
        let s = bound_witness(&chain, 0);
        let (b, cm, proof) = prove_bound(&chain, &s, POOL.0, POOL.1).expect("prove_bound");
        let honest = bound_challenges(&cm, b, &proof.chain[..1], &proof.ip.rounds[..1], 1, 1);
        let mut moved = proof.chain.clone();
        moved[0][0] = moved[0][0].clone() + one_at_zero();
        let tampered = bound_challenges(&cm, b, &moved, &proof.ip.rounds[..1], 1, 1);
        assert_ne!(
            honest[0], tampered[0],
            "a chain message must be bound before its challenge"
        );
        assert_ne!(honest[1], tampered[1]);
        // and the refusal is attributable to the commitment column
        let report = bound_report(
            &chain,
            &cm,
            b,
            &BoundProof {
                chain: moved,
                ip: proof.ip.clone(),
            },
            bound_tail_bound(&chain),
            POOL.0,
            POOL.1,
        );
        assert!(
            report.iter().any(|e| matches!(e, SelfIpError::Binding(_))),
            "{report:?}"
        );
    }

    #[test]
    fn a_bound_proof_refuses_an_unadmissible_tail() {
        let chain = bound_chain();
        let s = bound_witness(&chain, 0);
        let (b, cm, proof) = prove_bound(&chain, &s, POOL.0, POOL.1).expect("prove_bound");
        let honest = bound_tail_bound(&chain);
        let tail_sq = crate::shortness::tensor_fold::square_sum(&proof.ip.tail).expect("norm");
        assert!(
            tail_sq <= honest,
            "the fixture must sit inside Theorem 1's bound: {tail_sq} vs {honest}"
        );
        let report = bound_report(&chain, &cm, b, &proof, tail_sq - 1, POOL.0, POOL.1);
        assert!(
            report
                .iter()
                .any(|e| matches!(e, SelfIpError::TailNotAdmissible { .. })),
            "one below the tail's own norm must refuse: {report:?}"
        );
        assert!(
            report.iter().all(|e| !matches!(
                e,
                SelfIpError::Binding(_) | SelfIpError::TerminalMismatch { .. }
            )),
            "the gate must be the only thing that fires: {report:?}"
        );
    }

    #[test]
    fn prove_bound_refuses_a_witness_the_chain_cannot_commit() {
        let chain = bound_chain();
        assert_eq!(
            prove_bound(&chain, &vector(8), POOL.0, POOL.1),
            Err(SelfIpError::BadLength {
                len: 8,
                needed: chain.witness_len()
            })
        );
    }

    /// The ring element with `1` in the constant slot.
    fn one_at_zero() -> RingElt {
        let mut coeffs = [0u32; DIM];
        coeffs[0] = 1;
        crate::foundation::encoding::ring_from_u32::<Z1Coeff, DIM>(&coeffs)
    }
}
