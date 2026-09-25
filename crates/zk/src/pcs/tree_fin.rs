//! §5.4's **Greyhound-based finishing protocol** `Π^Fin` (Cheng–Nguyen–Tyagi,
//! eprint 2026/2067, pp. 39–45): the component that takes the claims the folding
//! cycle sets aside and *finishes* them.
//!
//! ```text
//! Π^Fin := GH′ ∘ Π^PE_NC,fin ∘ Π^Reshape                        (p. 39)
//!   Π^Reshape   : TE(1,k,b)^ω × PE(1,k,b)^{ω+1} → PE(2)(b1,b)    (Prot. 6, p. 42)
//!   Π^PE_NC,fin : PE(2)(b1,b2) → OE(2)(b1,b2)                    (p. 44)
//!   GH′         : OE(2)(b1,b2) → (0,1)                           (§5.4.3, p. 45)
//! ```
//!
//! [`crate::pcs::tree_fold`] and [`crate::pcs::tree_eval`] leave each round
//! holding `x̃_top ∈ TE(1,k,b)` and `x̃_subs ∈ PE(1,k,b)`, plus Π^Dec's final
//! base-case `PE` claim — the `TE(1,k,b)^ω × PE(1,k,b)^{ω+1}` of p. 39. Nothing
//! in the cycle binds them: Protocol 4's Eq. (12) *would*, through the factor
//! `êq(0^{ℓ−k}, u_{(:ℓ−k)})·ṽ_top`, but the `TE` point Π^Fold receives in this
//! assembly is the PE→TE bridge `(1 ‖ u)` (p. 25's `TE` relation), so that factor
//! reads coordinate `1` and vanishes — measured 2026-09-24: forging `v_top` left
//! the cycle's whole check list green. §5.4 is where the paper binds them, and
//! this module is that section: [`reshape_prove`]/[`reshape_report`] recommit all
//! `2ω+1` side-claims into Def. 23's two-layer commitment and check Eq. (32)–(36)
//! and the prefix claim, [`finish`]/[`fin_report`] continue through Π^PE_NC,fin's
//! two layer evaluations, and [`gh_prime_report`] checks Eq. (38) row by row — the
//! `GHPrincipal′` system that makes Greyhound fit `OE(2)`.
//!
//! # Where each printed condition lives
//!
//! * **Def. 23 (p. 39–40)** — `GHSetup` ([`FinKey::setup`]), `GHCommit`
//!   ([`gh_commit`]: `s1,i ← G⁻¹_{b1,n}(B2·s2,i)` per block, `t ← B1·s1`) and
//!   `GHOpen` ([`gh_open`], [`gh_open_report`]), whose three displayed conditions
//!   are four gates here: `t = B1·s1` → [`FinError::RootMismatch`],
//!   `G_{b1,n·2^γ}·s1 = (I_{2^γ}⊗B2)·s2` → [`FinError::LinkMismatch`], and
//!   `‖s1‖∞ < b1`, `‖s2‖∞ < b2` → [`FinError::TopNotShort`] /
//!   [`FinError::BottomNotShort`]. This instance sets `b1 = b2 = b` (hence
//!   `α1 = α2 = α`), which [`FinKey::setup`] asserts; the paper allows distinct
//!   `(b1,b2)` and writes Π^Reshape's output as `PE(2)(b1,b)`.
//! * **Protocol 6 (pp. 42–44)** — Step 1(a)'s concatenation
//!   `s_reshape := s_TE,1 ‖ … ‖ s_TE,ω ‖ s_PE,1 ‖ … ‖ s_PE,ω+1 ‖ 0^pad`
//!   ([`reshape_vector]), Eq. (32)'s batched well-formedness
//!   (`v_t + v_G = v_A`, with `q_reshape,A`/`q_reshape,G` of Eq. (33)/(34) in
//!   [`q_reshape_a_vector`]/[`q_reshape_g_vector`]), Step 2(d)/(e)'s evaluation
//!   claims Eq. (35)/(36) (the `PE` ones read through `êq(1 ‖ u_PE,l, ·)`, exactly
//!   as printed), Step 2(f)'s `0^{2nα}` prefix claim, and Step 3's output
//!   `(t*_reshape, r_{(µ'+m)}, y_reshape)`.
//! * **Π^PE_NC,fin (p. 44)** — Step 1's per-layer norm content is Def. 23's
//!   `‖s_i‖∞ < b_i`, which `GHOpen`'s third condition already gates, so it is
//!   *not* checked twice; Step 2's sent evaluations
//!   `a1 := s̃1(r_{[:γ+log(nα1))})` and `a2 := s̃2(r)` (read back through
//!   Lemma 14) are [`FinError::Layer1ClaimMismatch`] /
//!   [`FinError::Layer2ClaimMismatch`], and Step 3's shift claims give `y1, y2` at
//!   a second verifier point `r′`. The paper's `nα1 ≤ 2^β α2` substring
//!   requirement is a `setup` assertion.
//! * **§5.4.3 (pp. 41, 45)** — the *modification*: `OE(2)`'s two multilinear
//!   claims become `GHPrincipal′`'s rows `q⊺·s1 = y1`, with `q` the evaluation-form
//!   tensor of Eq. (37), and `a⊺·s2·b = y2`, with `a, b` the split of Lemma 16; the
//!   reduction's verification equation is then the five-row system Eq. (38).
//!   [`fin_report`] checks the two relation rows *and* that the received `q, a, b`
//!   are those tensors of the received point — without that check `y1, y2` would be
//!   claims about some other evaluation point. [`gh_prime_report`] checks Eq. (38)
//!   itself: `D·ŵ = v`, `b⊺·G_{b1,2^γ}·ŵ = y2`, `c⊺·G_{b1,2^γ}·ŵ = a⊺·z`, the
//!   `η`-row, and the two norm gates Cor. 5 inherits from Greyhound's Thm. 4.1.
//!   The printed system's second row, `B·s1 = u`, *is* Def. 23's root equation, so
//!   it keeps the one name [`FinError::RootMismatch`] rather than getting a second.
//!
//! # What is *not* here
//!
//! * **Greyhound's three-move core, and LaBRADOR.** `GH′` is only a *weak*
//!   interactive reduction (Cor. 5) because Eq. (38)'s matrix is discharged by
//!   LaBRADOR. The crate's [`crate::pcs::greyhound`] implements that core solely
//!   over its own fixed `Z1` instance (`d = 256`, `q = 8380417`, toy
//!   `m·r` columns) and its own √N split, so a Maltese-shaped ring
//!   (`q = 2³²−99`, `d = 64`) cannot call it without editing that module —
//!   reported rather than done. What lands here is everything §5.4 prints around
//!   that core: the recommitment, the reductions' verifier-side equations, and
//!   `GHPrincipal′(b1,b2)`'s rows.
//! * **`BatchSC`/`ShiftSC`** (§4, Protocols 1–2) still do not exist in this crate
//!   (no degree-`e` extension field — see the module doc of
//!   [`crate::pcs::tree_eval`]), so Π^Reshape's five claims are enforced as the
//!   *equations* they summarize, on the openings, exactly as
//!   [`crate::pcs::tree_eval::decompose_report`] does. **Succinctness, stated
//!   plainly:** neither this module nor §2.2 p. 9's direct-opening branch is
//!   succinct as compiled — `Π^Fin` is the paper's *succinct route* (Lem. 35 gives
//!   `O(ω log N)` verifier time and `O(log(N·ω))` proof size for Π^Reshape,
//!   Cor. 4 `O(polylog(2^{µ+k+1}nα))` for `GH′`), while the direct opening is
//!   *never* succinct in any compilation. What this slice buys now is that every
//!   set-aside claim is bound to **one** fresh two-layer commitment (Def. 23's
//!   binding paragraph, p. 39) through named, separately-falsifiable equations.
//! * **`Π^PE_NC,fin`'s Step 1 `Q_N` zero-check**, p. 44: the `ξ`-batched norm
//!   polynomial over **both** layers, proved by a sum-check that ends at the point
//!   `r` Step 2 evaluates at. It is not a round protocol here — its conclusion is
//!   Def. 23's `‖s1‖∞ < b1` and `‖s2‖∞ < b2`, which [`gh_open_report`] already
//!   gates as two named conditions on the opened witness, and this compilation
//!   hands the openings over anyway, so a round would add messages without adding
//!   a check. What that costs is stated in Fig. 6's accounting below: the
//!   `SC(2b)` component of the finish row is the one this module does not send.
//! * **Zero knowledge** — like the rest of the tree line, a proof of knowledge
//!   with no masking.
//!
//! # Layout conventions, which are load-bearing
//!
//! Π^Reshape's input is stated for claims with exactly `k` layers (p. 41), but a
//! real cycle stops lower: Π^Fold's `x̃_top`/`x̃_subs` have exactly `k`, while
//! Π^Dec's base case hands over `PE(1, ℓ̃, b)` with `ℓ̃ ≤ k`. Short blocks are
//! therefore **right-padded to `2^{k+1}·nα` entries** and their points **left-padded
//! with `0^{k−ℓ̃}`**, the one padding that preserves the claim: with
//! `s' = s ‖ 0^{(2^{k+1}−2^{ℓ̃+1})nα}` and `u' = 0^{k−ℓ̃} ‖ u`,
//! `s̃'(u') = Σ_x êq(0^{k−ℓ̃}, x_{[:k−ℓ̃]})·êq(u, x_{tail})·s(x) = s̃(u)` — valid
//! because `bits_of` is MSB-first and layer `i` starts at `2ⁱ·nα`
//! ([`crate::pcs::tree_eval::layer_range`]). [`block_point`] is that map and
//! `padded_short_blocks_preserve_their_claims` pins it against the unpadded
//! reading.
//!
//! The other trap is `a⊺·s2·b` of p. 41: `GHPrincipal′` sizes it
//! `a ∈ R^{2^β·α2}`, `b ∈ R^{2^γ}`, while `(I_{2^γ}⊗B2)·s2` makes the *block*
//! index the leading index bits of `s2`. So `a` is the evaluation-form vector of
//! the **trailing** `β + log α2` coordinates and `b` of the leading `γ` —
//! Greyhound's own convention (`f = Σ_{i<r} X^{im}·fᵢ` with `a(x)ᵀ·F·b(x)` and
//! `a` inside the column), not the reverse. [`bivariate_split`] is that split and
//! `the_lemma_16_split_is_not_transposable` refuses the transposition.

use crate::pcs::dotproduct::{QuadFn, Relation, zero_elt};
use crate::pcs::gadget;
use crate::pcs::key::{apply_blockwise, RingMatrixKey};
use crate::pcs::tree_commit::{self, max_norm, TreeError, TreeKey, TreeOpening};
use crate::pcs::tree_eval::{self, EvalError};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::{CenteredRing, Ring};
use algebra::ring::PolynomialQuotientRing;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Domain-separation label of Def. 23's `B1 ∈ R^{n×2^γ nα1}`.
const B1_LABEL: &[u8] = b"lattice-algebra/Z7/fin-B1";

/// Domain-separation label of Def. 23's `B2 ∈ R^{n×2^β α2}`.
const B2_LABEL: &[u8] = b"lattice-algebra/Z7/fin-B2";

/// Domain-separation label of Eq. (38)'s `D ∈ R^{n×2^γ α1}` — the matrix the
/// Greyhound prover commits `ŵ` with (NS24, Fig. 4). Def. 23's `GHSetup` prints
/// only `{B1,B2}` because it is restating the *commitment scheme*; `GH′` "runs
/// the modified initial three-move protocol" of NS24 §3.1, whose setup also
/// samples the `ŵ`-commitment matrix. It is therefore a third seed-expanded
/// matrix here.
const D_LABEL: &[u8] = b"lattice-algebra/Z7/fin-D";

/// Why a finishing proof was refused. Each variant names the equation of §5.4 it
/// corresponds to, so a tampered component identifies itself rather than
/// diagnosably collapsing into "something was wrong".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum FinError {
    /// A vector had the wrong length for its role (including the case where
    /// `B1`/`B2`'s shape does not cover `|s_reshape|`).
    WrongLength {
        /// Length supplied.
        got: usize,
        /// Length required.
        expected: usize,
    },
    /// A point had a different coordinate count than its vector's variables.
    WrongVariableCount {
        /// Coordinates supplied.
        got: usize,
        /// Coordinates required.
        expected: usize,
    },
    /// The side-claims are not `ω` `TE` claims followed by `ω+1` `PE` claims, so
    /// Eq. (32)'s `ζ` exponents (`ζ^{l−1}` for `TE`, `ζ^{ω−1+l}` for `PE`) name
    /// different blocks than the vectors do.
    ClaimsOutOfOrder {
        /// Position of the misplaced claim.
        position: usize,
    },
    /// Def. 23 `GHOpen`, first condition: `t = B1·s1`.
    RootMismatch {
        /// First row that disagreed.
        at: usize,
    },
    /// Def. 23 `GHOpen`, second condition:
    /// `G_{b1,n·2^γ}·s1 = (I_{2^γ}⊗B2)·s2`.
    LinkMismatch {
        /// First block entry that disagreed.
        at: usize,
    },
    /// Def. 23 `GHOpen`, third condition, first layer: `‖s1‖∞ < b1`.
    TopNotShort {
        /// Observed infinity norm.
        got: u64,
        /// Bound `b1`.
        bound: u64,
    },
    /// Def. 23 `GHOpen`, third condition, second layer: `‖s2‖∞ < b2`. This is the
    /// recommitment a binding break produces: `B2·s2' = B2·s2` with `s2'` longer
    /// than `b` is exactly an `MSIS_{q,n,d,2^β α2,2b2}` collision (p. 39).
    BottomNotShort {
        /// Observed infinity norm.
        got: u64,
        /// Bound `b2`.
        bound: u64,
    },
    /// Protocol 6 Step 1(a): `s*_reshape,2` is not
    /// `s_TE,1 ‖ … ‖ s_PE,ω+1 ‖ 0^pad` for *these* side-claim openings. `Open`
    /// alone is self-consistency, so without this an unrelated well-formed
    /// two-layer commitment satisfies every other equation.
    BlocksMismatch {
        /// First reshaped entry that disagreed.
        at: usize,
    },
    /// Step 2(f) / Eq. (31)'s analogue: a block does not begin with `0^{2nα}`.
    PrefixNotZero {
        /// Block index.
        block: usize,
        /// Index inside the prefix.
        at: usize,
    },
    /// Eq. (33)'s claim: `v_A ≠ ⟨q_reshape,A, p_{η,n} ⊗ s_reshape⟩`.
    AsideMismatch,
    /// Eq. (34)'s claim: `v_G ≠ ⟨q_reshape,G, s_reshape⟩`.
    GsideMismatch,
    /// Eq. (32): `v_t + v_G ≠ v_A`, i.e. the input commitments are not the
    /// commitments of the recommitted openings.
    BatchMismatch,
    /// Eq. (35): a `TE` side-claim value is not its block's evaluation at
    /// `êq(0^{k−ℓ̃} ‖ u_TE,l, ·)`.
    TeClaimMismatch {
        /// Block index.
        block: usize,
    },
    /// Eq. (36): a `PE` side-claim value is not its block's evaluation at
    /// `êq(1 ‖ u_PE,l, ·)`.
    PeClaimMismatch {
        /// Block index.
        block: usize,
    },
    /// Π^PE_NC,fin Step 2: `a1 ≠ s̃1(r_{[:γ+log(nα1))})`.
    Layer1ClaimMismatch,
    /// Π^PE_NC,fin Step 2 / Protocol 6 Step 3: `a2 ≠ s̃2(r)`, i.e. the forwarded
    /// `y_reshape` of `PE(2)`.
    Layer2ClaimMismatch,
    /// §5.4.3: the received `q`, `a`, `b` are not the evaluation-form tensors of
    /// the received points (Eq. (37), Lem. 16), so the two rows below would be
    /// claims about a different point than `OE(2)` carries.
    FormMismatch,
    /// `GHPrincipal′(b1,b2)`, the row `GH′` adds to stock Greyhound (Eq. (38)'s
    /// `+η⃗e1·q⊺` entry): `q⊺·s1 ≠ y1`.
    QFormMismatch,
    /// `GHPrincipal′(b1,b2)`: `a⊺·s2·b ≠ y2`.
    ABFormMismatch,
    /// Eq. (38) row 1: `D·ŵ ≠ v`, i.e. the `ŵ` LaBRADOR is handed is not the one
    /// `GH′` committed to.
    GhCommitmentMismatch {
        /// First row that disagreed.
        at: usize,
    },
    /// Eq. (38) row 3: `b⊺·G_{b1,2^γ}·ŵ ≠ y2`. This is `OE(2)`'s second-layer
    /// claim read through the *digit* witness rather than through `s2`, which is
    /// what makes it a row of the reduction rather than a restatement of
    /// [`FinError::ABFormMismatch`].
    GhEvalRowMismatch,
    /// Eq. (38) row 4: `c⊺·G_{b1,2^γ}·ŵ ≠ a⊺·z`, i.e. the same row combination
    /// `c` applied to `ŵ`'s recomposition and to the folded opening `z` disagree.
    GhFoldRowMismatch,
    /// Eq. (38) row 5: `(c⊺⊗G_{b1,n})·s1 + η⃗e₁·(q⊺s1) ≠ B2·z + η·y₁·⃗e₁`. The
    /// `η` term is `GH′`'s whole modification, so this is the one row a stock
    /// Greyhound cannot produce.
    GhEq38LastRowMismatch {
        /// Row of `R_F^n` that disagreed.
        row: usize,
    },
    /// `GH′`'s first norm gate (Cor. 5, inherited from Greyhound's Thm. 4.1):
    /// `ŵ` is not `b1`-short. Everything Eq. (38) extracts is an argument about
    /// a *short* witness, so an out-of-range `ŵ` makes its rows meaningless
    /// rather than false.
    GhWNotShort {
        /// Observed infinity norm.
        got: u64,
        /// Bound `b1`.
        bound: u64,
    },
    /// `GH′`'s second norm gate: `‖z‖∞` above `d·(Σ_j‖c_j‖∞)·(b2−1)`, the bound
    /// [`folded_norm_bound`] states for `z = Σ_j c_j·s2,j` with `‖s2‖∞ < b2`.
    GhZNotShort {
        /// Observed infinity norm.
        got: u64,
        /// Bound [`folded_norm_bound`] returns for these challenges.
        bound: u64,
    },
    /// A tree commitment carried inside a side-claim failed to open, so the input
    /// is not a member of `TE(1,k,b)^ω × PE(1,k,b)^{ω+1}`.
    Tree(TreeError),
    /// A multilinear evaluation could not be formed at the supplied point.
    Eval(EvalError),
}

impl fmt::Display for FinError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FinError::WrongLength { got, expected } => {
                write!(f, "vector of {got} entries, expected {expected}")
            }
            FinError::WrongVariableCount { got, expected } => {
                write!(f, "point of {got} coordinates, expected {expected}")
            }
            FinError::ClaimsOutOfOrder { position } => write!(
                f,
                "claim {position} breaks the `TE^ω then PE^{{ω+1}}` order Eq. (32)'s ζ exponents assume"
            ),
            FinError::RootMismatch { at } => {
                write!(f, "Def. 23 GHOpen: t = B1·s1 fails at row {at}")
            }
            FinError::LinkMismatch { at } => write!(
                f,
                "Def. 23 GHOpen: G·s1 = (I_2γ ⊗ B2)·s2 fails at entry {at}"
            ),
            FinError::TopNotShort { got, bound } => write!(
                f,
                "Def. 23 GHOpen: ‖s1‖∞ = {got}, the bound demands < {bound}"
            ),
            FinError::BottomNotShort { got, bound } => write!(
                f,
                "Def. 23 GHOpen: ‖s2‖∞ = {got}, the bound demands < {bound}"
            ),
            FinError::BlocksMismatch { at } => write!(
                f,
                "Prot. 6 Step 1(a): s*_reshape,2 is not the concatenation of these openings (entry {at})"
            ),
            FinError::PrefixNotZero { block, at } => write!(
                f,
                "block {block} does not start with 0^2nα (non-zero at {at})"
            ),
            FinError::AsideMismatch => write!(
                f,
                "Eq. 33: the sent v_A differs from ⟨q_reshape,A, p_η ⊗ s_reshape⟩"
            ),
            FinError::GsideMismatch => write!(
                f,
                "Eq. 34: the sent v_G differs from ⟨q_reshape,G, s_reshape⟩"
            ),
            FinError::BatchMismatch => write!(
                f,
                "Eq. 32 fails: v_t + v_G ≠ v_A, so a set-aside commitment is not a commitment to these openings"
            ),
            FinError::TeClaimMismatch { block } => write!(
                f,
                "Eq. 35: TE side-claim {block} is not its block's evaluation at 0^(k−ℓ̃) ‖ u_TE"
            ),
            FinError::PeClaimMismatch { block } => write!(
                f,
                "Eq. 36: PE side-claim {block} is not its block's evaluation at 1 ‖ u_PE"
            ),
            FinError::Layer1ClaimMismatch => {
                write!(f, "Prot. 7 Step 2: a1 ≠ s̃1(r_[:γ+log(nα1)])")
            }
            FinError::Layer2ClaimMismatch => {
                write!(f, "Prot. 6 Step 3 / Prot. 7 Step 2: y_reshape ≠ s̃2(r)")
            }
            FinError::FormMismatch => write!(
                f,
                "§5.4.3: the received q, a, b are not Eq. (37) / Lem. 16's evaluation-form tensors of the received points"
            ),
            FinError::QFormMismatch => write!(f, "GHPrincipal′: q⊺·s1 ≠ y1 (Eq. 38's extra row)"),
            FinError::ABFormMismatch => write!(f, "GHPrincipal′: a⊺·s2·b ≠ y2"),
            FinError::GhCommitmentMismatch { at } => {
                write!(f, "Eq. (38) row 1: (D·ŵ)_{at} ≠ v_{at}")
            }
            FinError::GhEvalRowMismatch => write!(
                f,
                "Eq. (38) row 3: b⊺·G_{{b1,2^γ}}·ŵ ≠ y2, i.e. ŵ does not open to the \
                 column combination whose inner product with b is y2"
            ),
            FinError::GhFoldRowMismatch => write!(
                f,
                "Eq. (38) row 4: c⊺·G_{{b1,2^γ}}·ŵ ≠ a⊺·z, i.e. the row combination c sees \
                 a different ŵ than the folded opening z does"
            ),
            FinError::GhEq38LastRowMismatch { row } => write!(
                f,
                "Eq. (38) row 5: (c⊺⊗G_{{b1,n}})·s1 + η⃗e₁·(q⊺s1) ≠ B2·z + η·y₁·⃗e₁ at row {row}"
            ),
            FinError::GhWNotShort { got, bound } => write!(
                f,
                "GH′: ‖ŵ‖∞ = {got} is not < b1 = {bound}, so Eq. (38) is an equation about \
                 a witness the reduction cannot extract"
            ),
            FinError::GhZNotShort { got, bound } => write!(
                f,
                "GH′: z is not short enough: {got} > d·(Σ of the challenges' norms)·(b2−1) = {bound}"
            ),
            FinError::Tree(err) => write!(f, "a side-claim tree does not open: {err}"),
            FinError::Eval(err) => write!(f, "multilinear evaluation failed: {err}"),
        }
    }
}

/// `GHSetup(1^λ, β, γ) → pp ← {B1, B2}` (Def. 23, p. 39): two independent uniform
/// matrices, `B1 ∈ R^{n×2^γ nα1}` and `B2 ∈ R^{n×2^β α2}` — plus the third one
/// Eq. (38)'s first row needs, `D ∈ R^{n×2^γ α1}`, which Def. 23 does not print
/// because it restates only the *commitment scheme* while `GH′` runs Greyhound's
/// initial three-move protocol, which commits to `ŵ` under a matrix of its own.
///
/// Like [`TreeKey::setup`] there is no trapdoor: all three are seed-expanded
/// uniform matrices, and Def. 23's binding comes from MSIS on the *shortness* of
/// `s1`, `s2`, not from an invertible construction.
///
/// This instance sets `b1 = b2 = b` (`α1 = α2 = α`), i.e. the same base as
/// `TCom`; `BASE`/`ALPHA` are the crate's const generics, so a distinct `b1`
/// would be a second instantiation of this type rather than a runtime choice.
#[derive(Clone)]
pub struct FinKey<R: Ring, const D: usize, const BASE: u64, const ALPHA: usize> {
    seed: [u8; 32],
    rows: usize,
    gamma: usize,
    beta: usize,
    b1: RingMatrixKey<R, D>,
    b2: RingMatrixKey<R, D>,
    d: RingMatrixKey<R, D>,
}

impl<R: Ring, const D: usize, const BASE: u64, const ALPHA: usize> fmt::Debug
    for FinKey<R, D, BASE, ALPHA>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "FinKey<n={}, d={d}, base={BASE}, alpha={ALPHA}, γ={}, β={}>",
            self.rows,
            self.gamma,
            self.beta,
            d = D
        )
    }
}

impl<R: Ring, const D: usize, const BASE: u64, const ALPHA: usize> FinKey<R, D, BASE, ALPHA> {
    /// Samples `B1`, `B2` for `2^γ` outer blocks of `nα1` digits and
    /// `2^β α2`-wide inner keys.
    ///
    /// # Panics
    /// Unless `BASE ≥ 2`, `ALPHA = ⌈log_BASE q⌉` (so `G⁻¹_{b1,n}` is exact),
    /// `nα` is a power of two (`m = log(nα)` must exist), `γ, β ≥ 1`, and
    /// `nα1 ≤ 2^β α2` — Π^PE_NC,fin Step 2's substring
    /// `r_{[:γ+log(nα1)]}` is only well-formed under that inequality (p. 44).
    pub fn setup(seed: &[u8; 32], rows: usize, gamma: usize, beta: usize) -> Self {
        assert!(rows > 0, "the commitment dimension n must be positive");
        assert_eq!(
            tree_commit::digits_for(BASE, R::MODULUS),
            Some(ALPHA),
            "ALPHA must be ⌈log_BASE q⌉ so the gadget split of B2·s2 is exact"
        );
        assert!(
            (rows * ALPHA).is_power_of_two(),
            "nα must be a power of two: m := log(nα) indexes a layer"
        );
        assert!(
            gamma >= 1 && beta >= 1 && gamma + beta < 63,
            "γ and β must both be ≥ 1 and sum below 63"
        );
        assert!(
            rows <= (1usize << beta),
            "Π^PE_NC,fin Step 2 reads s̃1 at r_{{[:γ+log(nα1)]}}, which needs nα1 ≤ 2^β·α2 \
             (p. 44): here that is n ≤ 2^β, so γ would have to cover the layer index twice"
        );
        Self {
            seed: *seed,
            rows,
            gamma,
            beta,
            b1: RingMatrixKey::setup(B1_LABEL, seed, rows, (1usize << gamma) * rows * ALPHA),
            b2: RingMatrixKey::setup(B2_LABEL, seed, rows, (1usize << beta) * ALPHA),
            d: RingMatrixKey::setup(D_LABEL, seed, rows, (1usize << gamma) * ALPHA),
        }
    }

    /// The seed both keys are expanded from.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The lattice dimension `n`.
    pub const fn rows(&self) -> usize {
        self.rows
    }

    /// The outer layer's block count exponent `γ`.
    pub const fn gamma(&self) -> usize {
        self.gamma
    }

    /// The inner key's width exponent `β`.
    pub const fn beta(&self) -> usize {
        self.beta
    }

    /// `2^β·α2`: the width of one `B2` block, i.e. one outer node's digits.
    pub const fn inner_width(&self) -> usize {
        (1usize << self.beta) * ALPHA
    }

    /// `2^γ`: the number of `B2` blocks Def. 23's `GHCommit` splits `s2` into.
    pub const fn nodes(&self) -> usize {
        1usize << self.gamma
    }

    /// `|s2| = 2^{γ+β}·α2`: the vector size this key can commit to.
    pub const fn bottom_len(&self) -> usize {
        self.nodes() * self.inner_width()
    }

    /// `|s1| = 2^γ·n·α1`.
    pub const fn top_len(&self) -> usize {
        self.nodes() * self.rows * ALPHA
    }

    /// `log₂|s1| = γ + log(nα1)`: the coordinate count of a `PE(2)` layer-1 point.
    pub const fn top_variables(&self) -> usize {
        self.gamma + (self.rows * ALPHA).trailing_zeros() as usize
    }

    /// `log₂|s2| = γ + β + log α2`: the coordinate count of a layer-2 point, i.e.
    /// of `r_{(µ'+m)}`.
    pub const fn bottom_variables(&self) -> usize {
        self.gamma + self.beta + ALPHA.trailing_zeros() as usize
    }

    /// `B1`.
    pub fn b1(&self) -> &RingMatrixKey<R, D> {
        &self.b1
    }

    /// `B2`.
    pub fn b2(&self) -> &RingMatrixKey<R, D> {
        &self.b2
    }

    /// `D ∈ R^{n×2^γ α1}`: Eq. (38)'s first row, the commitment to `ŵ`.
    pub fn d(&self) -> &RingMatrixKey<R, D> {
        &self.d
    }

    /// `|ŵ| = 2^γ·α1`: the digit count of the gadget image `G⁻¹_{b1,2^γ}(w)` that
    /// `D` commits to.
    pub const fn w_len(&self) -> usize {
        self.nodes() * ALPHA
    }
}

/// Def. 23's commitment and its full opening `(s1, s2)` — the witness
/// `PE(2)`/`OE(2)` carry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TwoLayerCommitment<R: Ring, const D: usize> {
    /// `t ← B1·s1 ∈ R_F^n`.
    pub t: Vec<PolyRing<R, D>>,
    /// The top layer: `2^γ` gadget images of `B2·s2,i`.
    pub s1: Vec<PolyRing<R, D>>,
    /// The bottom layer, which for Π^Reshape *is* `s_reshape`.
    pub s2: Vec<PolyRing<R, D>>,
}

/// `GHCommit((B1,B2),(b1,b2), s2) → (t, (s1,s2))` (Def. 23, p. 39):
/// `s1,i ← G⁻¹_{b1,n}(B2·s2,i)` for every one of the `2^γ` blocks, then
/// `t ← B1·s1`.
///
/// The input condition `‖s2‖∞ < b2` is *not* enforced here — it is what a
/// cheating prover violates, and [`gh_open_report`] is the gate.
///
/// # Errors
/// [`FinError::WrongLength`] unless `|s2| = 2^{γ+β}·α2`.
pub fn gh_commit<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    s2: &[PolyRing<R, D>],
) -> Result<TwoLayerCommitment<R, D>, FinError>
where
    R: Ring,
{
    if s2.len() != fin.bottom_len() {
        return Err(FinError::WrongLength {
            got: s2.len(),
            expected: fin.bottom_len(),
        });
    }
    let groups: Vec<&[PolyRing<R, D>]> = s2.chunks(fin.inner_width()).collect();
    let values = apply_blockwise(fin.b2(), &groups)
        .map_err(|err| FinError::WrongLength {
            got: err.got,
            expected: err.expected,
        })?;
    let s1 = gadget::split::<R, D, BASE, ALPHA>(&values);
    let t = fin.b1().matvec(&s1).map_err(|err| FinError::WrongLength {
        got: err.got,
        expected: err.expected,
    })?;
    Ok(TwoLayerCommitment {
        t,
        s1,
        s2: s2.to_vec(),
    })
}

/// **Every** condition of Def. 23's `GHOpen`, evaluated rather than taken up to
/// the first failure: an empty vector is an accepted opening.
///
/// `GHOpen` as printed (p. 40) returns 1 iff
/// `t = B1·s1`, `G_{b1,n·2^γ}·s1 = (I_{2^γ}⊗B2)·s2`, `‖s1‖∞ < b1`, `‖s2‖∞ < b2`.
/// The norm line covers two layers, so it is two gates here: a `s1` whose digits
/// are out of range is invisible to the recomposition (`G·s1` can be unchanged
/// while `‖s1‖∞ ≥ b1`, since the digit expansion is not unique once a digit
/// leaves the canonical window), and a `s2` that is not `b2`-short with
/// `(I⊗B2)·s2` unchanged *is* the MSIS collision Def. 23's binding paragraph
/// rules out.
///
/// Shape errors come back as [`FinError::WrongLength`] and stop the report: the
/// equations below index these vectors, and a truncated one would make an inner
/// product agree vacuously.
pub fn gh_open_report<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    commitment: &TwoLayerCommitment<R, D>,
) -> Vec<FinError>
where
    R: Ring + CenteredRing,
{
    let mut bad: Vec<FinError> = Vec::new();
    let mut push = |error: FinError| {
        if !bad.contains(&error) {
            bad.push(error);
        }
    };
    let shapes_ok = commitment.s2.len() == fin.bottom_len()
        && commitment.s1.len() == fin.top_len()
        && commitment.t.len() == fin.rows();
    if !shapes_ok {
        push(FinError::WrongLength {
            got: commitment.s1.len(),
            expected: fin.top_len(),
        });
        return bad;
    }
    // GHOpen line 1: t = B1·s1.
    match fin.b1().matvec(&commitment.s1) {
        Ok(expect) => {
            if let Some(at) = expect
                .iter()
                .zip(commitment.t.iter())
                .position(|(want, got)| want != got)
            {
                push(FinError::RootMismatch { at });
            }
        }
        Err(err) => push(FinError::WrongLength {
            got: err.got,
            expected: err.expected,
        }),
    }
    // GHOpen line 2: G_{b1,n·2^γ}·s1 = (I_{2^γ}⊗B2)·s2.
    let groups: Vec<&[PolyRing<R, D>]> = commitment.s2.chunks(fin.inner_width()).collect();
    match apply_blockwise(fin.b2(), &groups) {
        Ok(values) => {
            let recomposed = gadget::join::<R, D, BASE, ALPHA>(&commitment.s1);
            if let Some(at) = recomposed
                .iter()
                .zip(values.iter())
                .position(|(got, want)| got != want)
            {
                push(FinError::LinkMismatch { at });
            }
        }
        Err(err) => push(FinError::WrongLength {
            got: err.got,
            expected: err.expected,
        }),
    }
    // GHOpen line 3, both layers.
    let top = max_norm(&commitment.s1);
    if top >= BASE {
        push(FinError::TopNotShort { got: top, bound: BASE });
    }
    let bottom = max_norm(&commitment.s2);
    if bottom >= BASE {
        push(FinError::BottomNotShort {
            got: bottom,
            bound: BASE,
        });
    }
    bad
}

/// `GHOpen` as a boolean: [`gh_open_report`] then "take the first".
///
/// # Errors
/// The first entry of [`gh_open_report`].
pub fn gh_open<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    commitment: &TwoLayerCommitment<R, D>,
) -> Result<(), FinError>
where
    R: Ring + CenteredRing,
{
    gh_open_report(fin, commitment)
        .into_iter()
        .next()
        .map_or(Ok(()), Err)
}

/// Which of §5.4's two input relations a set-aside claim lives in. The paper's
/// Protocol 6 reads them differently: Step 2(d) uses the block's own `TE` point,
/// Step 2(e) reads a `PE` claim through the prepended selector `1` — the same
/// bridge [`crate::pcs::tree_eval::concatenated_point`] is for the cycle.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClaimKind {
    /// `TE(1,k,b)`: Π^Fold's `x̃_top = (t, r⃗', y_top)` (Prot. 4 Step 5), whose
    /// value is `s̃_top` over `0^{2nα} ‖ s_1 ‖ … ‖ s_k`.
    Te,
    /// `PE(1,k,b)`: Π^Fold's `x̃_subs` or Π^Dec's base case, whose value is the
    /// bottom layer's evaluation.
    Pe,
}

/// One set-aside claim of `TE(1,k,b)^ω × PE(1,k,b)^{ω+1}` (Prot. 6's `Input`,
/// p. 42): the commitment `t`, the point `u`, the claimed value `v`, and the
/// opening layers the finisher recommits.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SideClaim<R: Ring, const D: usize> {
    /// `TE` or `PE`; decides both the ζ range Eq. (32) puts the block in and
    /// whether `u` carries the layer selector bit.
    pub kind: ClaimKind,
    /// `(t, (s_i)_{i∈[ℓ̃]})`: the claim's own tree. `ℓ̃ ≤ k`, and a shorter tree
    /// is padded by [`reshape_vector`] — see the module doc's layout section.
    pub opening: TreeOpening<R, D>,
    /// `u_TE,l ∈ R_F^{ℓ̃+1+m}` or `u_PE,l ∈ R_F^{ℓ̃+m}` (§5 "Relations").
    pub u: Vec<PolyRing<R, D>>,
    /// `v_l ∈ R_F`.
    pub v: PolyRing<R, D>,
}

impl<R: Ring, const D: usize> SideClaim<R, D> {
    /// The height `ℓ̃` of the claim's own tree.
    pub fn height(&self) -> usize {
        self.opening.layers.len()
    }
}

/// Protocol 6's block geometry (p. 42–43): `µ' = ⌈log(2ω+1)⌉ + k + 1`, every
/// block `2^{k+1}·nα` entries wide, `s_reshape ∈ R_F^{2^µ' nα}`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ReshapeLayout {
    /// `ω`: the number of `TE` side-claims, i.e. the cycle's round count.
    pub omega: usize,
    /// `2ω+1`: the number of claims, and hence of live blocks.
    pub claims: usize,
    /// `⌈log(2ω+1)⌉`: the block-index coordinates Eq. (32)'s `p_{ζ,2ω+1}` has.
    pub log_blocks: usize,
    /// `2^⌈log(2ω+1)⌉`: the *allocated* block count, padding included.
    pub blocks: usize,
    /// The declared arity `k`.
    pub k: usize,
    /// `nα`, one tree node's digit width — the paper's `m = log(nα)` is its log.
    pub slot_len: usize,
    /// `m = log₂(nα)`.
    pub m: usize,
    /// `2^{k+1}·nα`: one block's entry count.
    pub width: usize,
    /// `2^µ'·nα = blocks · width`: `|s_reshape|`.
    pub total: usize,
    /// `µ' = ⌈log(2ω+1)⌉ + k + 1`.
    pub mu: usize,
}

impl ReshapeLayout {
    /// Block `position`'s slice of `s_reshape`.
    pub fn block_range(&self, position: usize) -> core::ops::Range<usize> {
        position * self.width..(position + 1) * self.width
    }
}

/// The shape check Protocol 6's `Input` amounts to: `ω` `TE` claims then `ω+1`
/// `PE` claims, each on a tree of at most `k` layers with a point of the length
/// its relation dictates, over `nα`-wide nodes.
///
/// # Errors
/// [`FinError::WrongLength`] on a claim count that is not `TE^ω × PE^{ω+1}` (or a
/// `slot_len` that is not a power of two), [`FinError::ClaimsOutOfOrder`] when a
/// `TE` claim follows a `PE` one (which would silently move blocks between
/// Eq. (32)'s two ζ ranges), [`FinError::WrongVariableCount`] on a point whose
/// coordinate count does not match its tree.
pub fn reshape_layout<R: Ring, const D: usize>(
    slot_len: usize,
    k: usize,
    claims: &[SideClaim<R, D>],
) -> Result<ReshapeLayout, FinError> {
    if slot_len == 0 || !slot_len.is_power_of_two() {
        return Err(FinError::WrongLength {
            got: slot_len,
            expected: slot_len.next_power_of_two(),
        });
    }
    let m = slot_len.trailing_zeros() as usize;
    let te = claims
        .iter()
        .filter(|claim| claim.kind == ClaimKind::Te)
        .count();
    let pe = claims.len() - te;
    if pe != te + 1 {
        return Err(FinError::WrongLength {
            got: claims.len(),
            expected: 2 * te + 1,
        });
    }
    if let Some(extra) = claims
        .iter()
        .skip(te)
        .position(|claim| claim.kind == ClaimKind::Te)
    {
        return Err(FinError::ClaimsOutOfOrder {
            position: te + extra,
        });
    }
    let width = (1usize << (k + 1))
        .checked_mul(slot_len)
        .ok_or(FinError::WrongLength {
            got: usize::MAX,
            expected: 0,
        })?;
    for claim in claims {
        let height = claim.height();
        if height > k {
            return Err(FinError::WrongLength {
                got: height,
                expected: k,
            });
        }
        let want = match claim.kind {
            ClaimKind::Te => height + 1 + m,
            ClaimKind::Pe => height + m,
        };
        if claim.u.len() != want {
            return Err(FinError::WrongVariableCount {
                got: claim.u.len(),
                expected: want,
            });
        }
        let expect = tree_eval::concatenation_height(
            &tree_eval::concatenated(slot_len, &claim.opening.layers),
            slot_len,
        )
        .map_err(FinError::Eval)?;
        if expect != height {
            return Err(FinError::WrongLength {
                got: expect,
                expected: height,
            });
        }
    }
    let log_blocks = (2 * te + 1).next_power_of_two().trailing_zeros() as usize;
    let blocks = 1usize << log_blocks;
    let total = blocks
        .checked_mul(width)
        .ok_or(FinError::WrongLength {
            got: usize::MAX,
            expected: 0,
        })?;
    Ok(ReshapeLayout {
        omega: te,
        claims: claims.len(),
        log_blocks,
        blocks,
        k,
        slot_len,
        m,
        width,
        total,
        mu: log_blocks + k + 1,
    })
}

/// Step 1(a): `s_reshape := s_TE,1 ‖ … ‖ s_TE,ω ‖ s_PE,1 ‖ … ‖ s_PE,ω+1 ‖ 0^pad`,
/// every `s` a block's `0^{2nα} ‖ s_1 ‖ … ‖ s_ℓ̃` and `pad` the zeros that take
/// the block count up to `2^⌈log(2ω+1)⌉`.
///
/// Both the prover and the verifier build it from this one function, so a claim
/// re-read against `s*_reshape,2` cannot be re-read against a different vector
/// than the one committed.
///
/// # Errors
/// Propagates [`reshape_layout`].
pub fn reshape_vector<R: Ring, const D: usize>(
    slot_len: usize,
    k: usize,
    claims: &[SideClaim<R, D>],
) -> Result<Vec<PolyRing<R, D>>, FinError> {
    let layout = reshape_layout(slot_len, k, claims)?;
    let mut out = vec![tree_eval::zero_ring::<R, D>(); layout.total];
    for (position, claim) in claims.iter().enumerate() {
        let block = tree_eval::concatenated(slot_len, &claim.opening.layers);
        let range = layout.block_range(position);
        for (slot, value) in out[range].iter_mut().zip(block.iter()) {
            *slot = value.clone();
        }
    }
    Ok(out)
}

/// The point Eq. (35)/(36) evaluates block `position` at: `0^{k−ℓ̃} ‖ u_TE,l` and
/// `0^{k−ℓ̃} ‖ 1 ‖ u_PE,l`, i.e. the padding of the module doc's layout section
/// plus Step 2(e)'s prepended layer selector.
///
/// # Errors
/// Propagates [`reshape_layout`]'s gates for this claim.
pub fn block_point<R: Ring, const D: usize>(
    slot_len: usize,
    k: usize,
    claim: &SideClaim<R, D>,
) -> Result<Vec<PolyRing<R, D>>, FinError> {
    let m = slot_len.trailing_zeros() as usize;
    let height = claim.height();
    let want = match claim.kind {
        ClaimKind::Te => height + 1 + m,
        ClaimKind::Pe => height + m,
    };
    if claim.u.len() != want || height > k {
        return Err(FinError::WrongVariableCount {
            got: claim.u.len(),
            expected: want,
        });
    }
    let local: Vec<PolyRing<R, D>> = match claim.kind {
        ClaimKind::Te => claim.u.clone(),
        ClaimKind::Pe => tree_eval::pe_to_te_point(&claim.u),
    };
    let mut point = vec![tree_eval::zero_ring::<R, D>(); k - height];
    point.extend_from_slice(&local);
    debug_assert_eq!(point.len(), k + 1 + m, "every block has the same variables");
    Ok(point)
}

/// `q_reshape,A` of Eq. (33): `⊗_{r∈[n]} (p_{ζ,2^⌈log(2ω+1)⌉} ⊗ p_{ξ,2^k} ⊗ a_r)`.
///
/// Built block by block at each block's *own* height, then zero-padded to the
/// `k`-height stride: `a` is `A`'s row `r` (from [`TreeKey::matrix`]), and a short
/// tree contributes no `A`-side constraints past its own layers.
///
/// # Errors
/// Propagates [`reshape_layout`].
pub fn q_reshape_a_vector<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    tree: &TreeKey<R, D, BASE, ALPHA>,
    slot_len: usize,
    k: usize,
    claims: &[SideClaim<R, D>],
    zeta: R,
    xi: R,
) -> Result<Vec<PolyRing<R, D>>, FinError>
where
    R: Ring + CenteredRing,
{
    let layout = reshape_layout(slot_len, k, claims)?;
    let mut out = vec![tree_eval::zero_ring::<R, D>(); tree.rows() * layout.total];
    for (position, claim) in claims.iter().enumerate() {
        let powers: Vec<PolyRing<R, D>> = tree_eval::powers_vector(
            xi,
            1usize << claim.height(),
        )
        .iter()
        .map(|power| tree_eval::embed::<R, D>(*power))
        .collect();
        let zeta_power = zeta.pow(position as u64);
        for row in 0..tree.rows() {
            let weights = tree_eval::tensor_ring(&powers, tree.matrix().row(row));
            let start = row * layout.total + layout.block_range(position).start;
            for (offset, weight) in weights.iter().enumerate() {
                out[start + offset] = weight.clone() * tree_eval::embed::<R, D>(zeta_power);
            }
        }
    }
    Ok(out)
}

/// `q_reshape,G` of Eq. (34):
/// `p_{ζ,2ω+1} ⊗ ((p_{ξ,2^k} ⊗ p_{η,n}) ⊗ p_{b,α} ‖ 0^{2^k nα})`.
///
/// The `‖ 0^{…}` suffix is what keeps each block's *leaf* layer off the gadget
/// side, exactly as in Π^Dec's Eq. (28) — the reason `Open`'s last link is bound
/// by the `A` side alone.
///
/// # Errors
/// Propagates [`reshape_layout`].
#[allow(clippy::too_many_arguments)]
pub fn q_reshape_g_vector<R, const D: usize>(
    slot_len: usize,
    rows: usize,
    k: usize,
    claims: &[SideClaim<R, D>],
    zeta: R,
    xi: R,
    eta: R,
    base: u64,
    alpha: usize,
) -> Result<Vec<R>, FinError>
where
    R: Ring,
{
    let layout = reshape_layout(slot_len, k, claims)?;
    let mut out = vec![R::ZERO; layout.total];
    for (position, claim) in claims.iter().enumerate() {
        let weights = tree_eval::q_g_vector(
            slot_len,
            rows,
            claim.height(),
            base,
            alpha,
            xi,
            eta,
        );
        let zeta_power = zeta.pow(position as u64);
        let start = layout.block_range(position).start;
        for (offset, weight) in weights.iter().enumerate() {
            out[start + offset] = *weight * zeta_power;
        }
    }
    Ok(out)
}

/// The `v_t` Eq. (32) computes *on the verifier's side*: the ζ-batched
/// `Σ_l ζ^{l−1}·ξ·⟨p_{η,n}, t_TE,l⟩ + Σ_l ζ^{ω−1+l}·ξ·⟨p_{η,n}, t_PE,l⟩` over the
/// received set-aside commitments.
///
/// # Errors
/// Propagates [`reshape_layout`].
pub fn batched_commit_claim<R, const D: usize>(
    slot_len: usize,
    k: usize,
    claims: &[SideClaim<R, D>],
    zeta: R,
    xi: R,
    eta: R,
) -> Result<PolyRing<R, D>, FinError>
where
    R: Ring,
{
    // The claim set's shape is part of the statement: Eq. (32)'s ζ exponents
    // only name the blocks Protocol 6 orders them into.
    reshape_layout(slot_len, k, claims)?;
    let rows = claims
        .first()
        .map(|claim| claim.opening.root.len())
        .unwrap_or(0);
    let weights = tree_eval::powers_vector(eta, 1usize.max(rows));
    let mut acc = tree_eval::zero_ring::<R, D>();
    for (position, claim) in claims.iter().enumerate() {
        if claim.opening.root.len() != rows {
            return Err(FinError::WrongLength {
                got: claim.opening.root.len(),
                expected: rows,
            });
        }
        let inner = tree_eval::scalar_inner_product(&weights, &claim.opening.root);
        let zeta_power = zeta.pow(position as u64);
        acc += tree_eval::scale_by_scalar(&inner, zeta_power * xi);
    }
    Ok(acc)
}

/// `p_{η,n} ⊗ s_reshape`, the `A` side's partner in Eq. (33).
///
/// `η^r` is a *constant* polynomial, so this is the scalar lift of `tensor_ring`
/// over [`crate::pcs::tree_eval`]’s powers embedding — `d` times cheaper per
/// entry and equal to it, which `lifting_p_eta_matches_the_tensor_form` pins.
pub fn lift_by_eta<R: Ring, const D: usize>(
    s: &[PolyRing<R, D>],
    eta: R,
    rows: usize,
) -> Vec<PolyRing<R, D>> {
    let powers = tree_eval::powers_vector(eta, 1usize.max(rows));
    let mut out = Vec::with_capacity(powers.len() * s.len());
    for power in &powers {
        for value in s {
            out.push(tree_eval::scale_by_scalar(value, *power));
        }
    }
    out
}

/// Eq. (33)'s right-hand side, evaluated blockwise rather than as one
/// `n·|s_reshape|`-wide tensor: `Σ_{r} η^r Σ_{block} ζ^{block} Σ_{j} ξ^j ⟨a_r,
/// s[j·2nα …]⟩`. Same arithmetic as [`q_reshape_a_vector`] paired with
/// `lift_by_eta` (the test says so), `Θ(1)` memory instead of `n·|s_reshape|`.
///
/// # Errors
/// Propagates [`reshape_layout`] and reports [`FinError::WrongLength`] when a
/// block is not the stride its weights assume.
#[allow(clippy::too_many_arguments)]
pub fn reshape_a_side<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    tree: &TreeKey<R, D, BASE, ALPHA>,
    s: &[PolyRing<R, D>],
    slot_len: usize,
    k: usize,
    claims: &[SideClaim<R, D>],
    zeta: R,
    xi: R,
    eta: R,
) -> Result<PolyRing<R, D>, FinError>
where
    R: Ring + CenteredRing,
{
    let layout = reshape_layout(slot_len, k, claims)?;
    if s.len() != layout.total {
        return Err(FinError::WrongLength {
            got: s.len(),
            expected: layout.total,
        });
    }
    let block_width = 2 * slot_len;
    let mut acc = tree_eval::zero_ring::<R, D>();
    for row in 0..tree.rows() {
        let a_row = tree.matrix().row(row);
        let mut inner = tree_eval::zero_ring::<R, D>();
        for (position, claim) in claims.iter().enumerate() {
            let zeta_power = zeta.pow(position as u64);
            let range = layout.block_range(position);
            let blocks = 1usize << claim.height();
            for (index, chunk) in s[range].chunks(block_width).take(blocks).enumerate() {
                let weight = zeta_power * xi.pow(index as u64);
                let dot = tree_eval::inner_product(a_row, chunk);
                inner += tree_eval::scale_by_scalar(&dot, weight);
            }
        }
        let eta_power = eta.pow(row as u64);
        acc += tree_eval::scale_by_scalar(&inner, eta_power);
    }
    Ok(acc)
}

/// Eq. (34)'s right-hand side `⟨q_reshape,G, s_reshape⟩`; the weights are field
/// elements, so this is `d` times cheaper than the `A` side.
///
/// # Errors
/// Propagates [`reshape_layout`].
#[allow(clippy::too_many_arguments)]
pub fn reshape_g_side<R, const D: usize>(
    s: &[PolyRing<R, D>],
    slot_len: usize,
    rows: usize,
    k: usize,
    claims: &[SideClaim<R, D>],
    zeta: R,
    xi: R,
    eta: R,
    base: u64,
    alpha: usize,
) -> Result<PolyRing<R, D>, FinError>
where
    R: Ring,
{
    let layout = reshape_layout(slot_len, k, claims)?;
    if s.len() != layout.total {
        return Err(FinError::WrongLength {
            got: s.len(),
            expected: layout.total,
        });
    }
    let weights = q_reshape_g_vector(slot_len, rows, k, claims, zeta, xi, eta, base, alpha)?;
    Ok(tree_eval::scalar_inner_product(&weights, s))
}

/// What Π^Reshape sends and forwards (Protocol 6 Steps 1–2): the two-layer
/// commitment, its opening `(s1, s2 = s_reshape)`, and the two batched constraint
/// claims Eq. (33)/(34).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReshapeProof<R: Ring, const D: usize> {
    /// `(t*_reshape, s*_reshape,1, s*_reshape,2)` from `GHCommit` (Step 1).
    pub commitment: TwoLayerCommitment<R, D>,
    /// `v_A` of Step 2(b)ii.
    pub v_a: PolyRing<R, D>,
    /// `v_G` of Step 2(a)ii.
    pub v_g: PolyRing<R, D>,
}

/// Π^Reshape prover (Protocol 6 Steps 1–2): recommit all `2ω+1` side-claims with
/// Def. 23's `GHCommit`, then form `v_A`, `v_G` against the verifier's
/// `ζ, ξ, η`. Runs [`reshape_report`] on its own output before returning, so a
/// proof this module would refuse never reaches a caller.
///
/// `γ` (Step 2(a)i's zero-prefix challenge) needs no argument: with the openings
/// in hand the prefix is decidable entry by entry, exactly as
/// [`crate::pcs::tree_eval::decompose_report`] decides Eq. (31).
///
/// # Errors
/// Whatever [`reshape_report`] reports for the proof just built.
#[allow(clippy::too_many_arguments)]
pub fn reshape_prove<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    tree: &TreeKey<R, D, BASE, ALPHA>,
    fin: &FinKey<R, D, BASE, ALPHA>,
    claims: &[SideClaim<R, D>],
    k: usize,
    zeta: R,
    xi: R,
    eta: R,
) -> Result<ReshapeProof<R, D>, FinError>
where
    R: Ring + CenteredRing,
{
    let slot_len = tree.slot_len();
    let s = reshape_vector(slot_len, k, claims)?;
    let commitment = gh_commit(fin, &s)?;
    let v_a = reshape_a_side(tree, &s, slot_len, k, claims, zeta, xi, eta)?;
    let v_g = reshape_g_side(
        &s,
        slot_len,
        tree.rows(),
        k,
        claims,
        zeta,
        xi,
        eta,
        BASE,
        ALPHA,
    )?;
    let proof = ReshapeProof {
        commitment,
        v_a,
        v_g,
    };
    if let Some(error) = reshape_report(tree, fin, &proof, claims, k, zeta, xi, eta)
        .into_iter()
        .next()
    {
        return Err(error);
    }
    Ok(proof)
}

/// **Every** Π^Reshape condition the paper prints, evaluated rather than taken up
/// to the first failure; an empty vector accepts. In protocol order:
///
/// 1. shapes: the claim set's order and point lengths, and that `B1`/`B2` cover
///    `|s_reshape| = 2^µ' nα` (Prot. 6's remark under Step 1, p. 43);
/// 2. Step 1(a): `s*_reshape,2` **is** the reshaped concatenation;
/// 3. Def. 23 `GHOpen`'s four gates ([`gh_open_report`]);
/// 4. Step 2(f): every block starts with `0^{2nα}`;
/// 5. the input relation's own premise: each set-aside tree opens at `b`
///    (Def. 19, and what `TE`/`PE` membership means);
/// 6. Eq. (33)/(34): the sent `v_A`, `v_G` re-read against `s_reshape`;
/// 7. Eq. (32): `v_t + v_G = v_A`;
/// 8. Eq. (35)/(36): each side-claim value re-read at its block point.
///
/// # Errors
/// See [`FinError`]; every variant but [`FinError::Tree`] / [`FinError::Eval`]
/// names one printed condition.
#[allow(clippy::too_many_arguments)]
pub fn reshape_report<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    tree: &TreeKey<R, D, BASE, ALPHA>,
    fin: &FinKey<R, D, BASE, ALPHA>,
    proof: &ReshapeProof<R, D>,
    claims: &[SideClaim<R, D>],
    k: usize,
    zeta: R,
    xi: R,
    eta: R,
) -> Vec<FinError>
where
    R: Ring + CenteredRing,
{
    let mut bad: Vec<FinError> = Vec::new();
    let mut push = |error: FinError| {
        if !bad.contains(&error) {
            bad.push(error);
        }
    };
    let slot_len = tree.slot_len();
    // 1. shapes, incl. the key/instance agreement Prot. 6's remark requires.
    let layout = match reshape_layout(slot_len, k, claims) {
        Ok(layout) => layout,
        Err(error) => {
            push(error);
            return bad;
        }
    };
    if fin.bottom_len() != layout.total {
        push(FinError::WrongLength {
            got: fin.bottom_len(),
            expected: layout.total,
        });
        return bad;
    }
    // 2. Step 1(a).
    let expect = match reshape_vector(slot_len, k, claims) {
        Ok(vector) => vector,
        Err(error) => {
            push(error);
            return bad;
        }
    };
    if proof.commitment.s2.len() != expect.len() {
        push(FinError::WrongLength {
            got: proof.commitment.s2.len(),
            expected: expect.len(),
        });
        return bad;
    }
    if let Some(at) = expect
        .iter()
        .zip(proof.commitment.s2.iter())
        .position(|(want, got)| want != got)
    {
        push(FinError::BlocksMismatch { at });
    }
    // 3. Def. 23.
    for error in gh_open_report(fin, &proof.commitment) {
        push(error);
    }
    // 4. Step 2(f).
    for position in 0..claims.len() {
        let range = layout.block_range(position);
        let block = &proof.commitment.s2[range];
        for (at, value) in block.iter().take(2 * slot_len).enumerate() {
            if value.coefficients().into_iter().any(|c| c != R::ZERO) {
                push(FinError::PrefixNotZero {
                    block: position,
                    at,
                });
            }
        }
    }
    // 5. the input relation's membership premise.
    for claim in claims {
        if let Err(err) = tree.open(&claim.opening, BASE) {
            push(FinError::Tree(err));
        }
    }
    // 6. Eq. (33)/(34).
    match reshape_a_side(
        tree,
        &proof.commitment.s2,
        slot_len,
        k,
        claims,
        zeta,
        xi,
        eta,
    ) {
        Ok(want) => {
            if want != proof.v_a {
                push(FinError::AsideMismatch);
            }
        }
        Err(error) => push(error),
    }
    match reshape_g_side(
        &proof.commitment.s2,
        slot_len,
        tree.rows(),
        k,
        claims,
        zeta,
        xi,
        eta,
        BASE,
        ALPHA,
    ) {
        Ok(want) => {
            if want != proof.v_g {
                push(FinError::GsideMismatch);
            }
        }
        Err(error) => push(error),
    }
    // 7. Eq. (32).
    match batched_commit_claim(slot_len, k, claims, zeta, xi, eta) {
        Ok(v_t) => {
            if v_t + proof.v_g.clone() != proof.v_a {
                push(FinError::BatchMismatch);
            }
        }
        Err(error) => push(error),
    }
    // 8. Eq. (35)/(36).
    for (position, claim) in claims.iter().enumerate() {
        let point = match block_point(slot_len, k, claim) {
            Ok(point) => point,
            Err(error) => {
                push(error);
                continue;
            }
        };
        let range = layout.block_range(position);
        let value = tree_eval::mle_at_ring(&proof.commitment.s2[range], &point);
        match value {
            Ok(reclaim) => {
                let mismatch = match claim.kind {
                    ClaimKind::Te => FinError::TeClaimMismatch { block: position },
                    ClaimKind::Pe => FinError::PeClaimMismatch { block: position },
                };
                if reclaim != claim.v {
                    push(mismatch);
                }
            }
            Err(error) => push(FinError::Eval(error)),
        }
    }
    bad
}

/// Π^Reshape verifier: [`reshape_report`] then "take the first", and on success
/// Protocol 6 Step 3's output claim `(t*_reshape, r_{(µ'+m)}, y_reshape)` — the
/// evaluation of `s_reshape` at the transcript point `r`, which is what
/// Π^PE_NC,fin and `GH′` then continue on.
///
/// # Errors
/// The first entry of [`reshape_report`], plus [`FinError::WrongVariableCount`]
/// when `r` does not index `s_reshape`.
#[allow(clippy::too_many_arguments)]
pub fn reshape_verify<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    tree: &TreeKey<R, D, BASE, ALPHA>,
    fin: &FinKey<R, D, BASE, ALPHA>,
    proof: &ReshapeProof<R, D>,
    claims: &[SideClaim<R, D>],
    k: usize,
    zeta: R,
    xi: R,
    eta: R,
    r: &[PolyRing<R, D>],
) -> Result<(Vec<PolyRing<R, D>>, PolyRing<R, D>), FinError>
where
    R: Ring + CenteredRing,
{
    if let Some(error) =
        reshape_report(tree, fin, proof, claims, k, zeta, xi, eta)
            .into_iter()
            .next()
    {
        return Err(error);
    }
    let y = tree_eval::mle_at_ring(&proof.commitment.s2, r).map_err(FinError::Eval)?;
    Ok((r.to_vec(), y))
}

/// What `Π^Fin` sends after Π^Reshape: Π^PE_NC,fin Step 2's two layer
/// evaluations, Step 3's two reduced claims at `r′`, and `GHPrincipal′`'s public
/// linear forms.
///
/// `q`, `a`, `b` are *received* rather than recomputed on purpose:
/// `GHPrincipal′(b1,b2)` lists them among its public inputs `x` (p. 41), and the
/// check that they are the evaluation-form tensors of the claimed points is what
/// stops `y1, y2` from being claims about a point the reduction never chose.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FinProof<R: Ring, const D: usize> {
    /// Π^Reshape's messages.
    pub reshape: ReshapeProof<R, D>,
    /// `r_{(µ'+m)}`: Prot. 6 Step 3's point, and Prot. 7 Step 2's `a2` point.
    pub r: Vec<PolyRing<R, D>>,
    /// `a1 := s̃1(r_{[:γ+log(nα1))})` (Prot. 7 Step 2).
    pub a1: PolyRing<R, D>,
    /// `a2 := s̃2(r)` (Prot. 7 Step 2) — `PE(2)`'s forwarded `y_reshape`.
    pub a2: PolyRing<R, D>,
    /// `r′`: Prot. 7 Step 3's shift-sum-check point, i.e. `OE(2)`'s `u1, u2`.
    pub r_prime: Vec<PolyRing<R, D>>,
    /// `OE(2)`'s layer-1 claim `ỹ1(u1) = y1`.
    pub y1: PolyRing<R, D>,
    /// `OE(2)`'s layer-2 claim `ỹ2(u2) = y2`.
    pub y2: PolyRing<R, D>,
    /// Eq. (37)'s `q ∈ R_F^{2^γ nα1}`.
    pub q: Vec<PolyRing<R, D>>,
    /// Lem. 16's `a`, the evaluation form of `u2`'s trailing `β + log α2` bits.
    pub a: Vec<PolyRing<R, D>>,
    /// Lem. 16's `b`, the evaluation form of `u2`'s leading `γ` bits.
    pub b: Vec<PolyRing<R, D>>,
}

/// The evaluation-form tensor `⊗_j (1 − u_j, u_j)` of §5.4.3 — Eq. (37)'s `q` and
/// Lemma 16's `a`, `b` are all this map at different points, and it is the same
/// table [`crate::pcs::tree_eval::eq_ring_table`] builds for a multilinear
/// extension, so the reduction's "rewrite the claim as an inner product" step
/// cannot drift from the claim it rewrites.
///
/// # Errors
/// [`FinError::WrongVariableCount`] unless `2^|u| = len`.
pub fn eval_form_vector<R: Ring, const D: usize>(
    u: &[PolyRing<R, D>],
    len: usize,
) -> Result<Vec<PolyRing<R, D>>, FinError> {
    tree_eval::eq_ring_table(u, len).map_err(FinError::Eval)
}

/// Lemma 16's split of `ũ(r ‖ u)` into `a ⊗ b`: `b` is the evaluation form of the
/// **leading** `split_at` coordinates and `a` of the trailing ones, because
/// `GHPrincipal′` sizes `a ∈ R^{2^β·α2}` and `b ∈ R^{2^γ}` while `(I_{2^γ}⊗B2)·s2`
/// makes the block index the leading bits of `s2` (module doc, "the other trap").
///
/// # Errors
/// [`FinError::WrongVariableCount`] if `split_at` is outside `u`'s coordinates.
pub fn bivariate_split<R: Ring, const D: usize>(
    u: &[PolyRing<R, D>],
    split_at: usize,
) -> Result<(Vec<PolyRing<R, D>>, Vec<PolyRing<R, D>>), FinError> {
    if split_at > u.len() {
        return Err(FinError::WrongVariableCount {
            got: split_at,
            expected: u.len(),
        });
    }
    let b = eval_form_vector(&u[..split_at], 1usize << split_at)?;
    let tail = &u[split_at..];
    let a = eval_form_vector(tail, 1usize << tail.len())?;
    Ok((a, b))
}

/// `GH′`'s and Π^PE_NC,fin's messages: Step 2's `a1, a2` and Step 3's reduced
/// claims `y1, y2` with their forms, on top of Π^Reshape's.
///
/// The two layers are the two openings of `OE(2)`'s Def. 23 commitment, so the
/// only new material is five ring elements and three derived vectors.
#[allow(clippy::too_many_arguments)]
pub fn fin_prove<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    tree: &TreeKey<R, D, BASE, ALPHA>,
    fin: &FinKey<R, D, BASE, ALPHA>,
    claims: &[SideClaim<R, D>],
    k: usize,
    zeta: R,
    xi: R,
    eta: R,
    r: Vec<PolyRing<R, D>>,
    r_prime: Vec<PolyRing<R, D>>,
) -> Result<FinProof<R, D>, FinError>
where
    R: Ring + CenteredRing,
{
    let reshape = reshape_prove(tree, fin, claims, k, zeta, xi, eta)?;
    let proof = finish(fin, &reshape, r, r_prime)?;
    if let Some(error) = fin_report(tree, fin, &proof, claims, k, zeta, xi, eta)
        .into_iter()
        .next()
    {
        return Err(error);
    }
    Ok(proof)
}

/// Π^PE_NC,fin Steps 2–3 plus §5.4.3's form construction, given a *verified-shape*
/// Π^Reshape proof: `a1 := s̃1(r_{[:γ+log(nα1))})`, `a2 := s̃2(r)`, and
/// `y1 := q⊺·s1`, `y2 := a⊺·s2·b` at the shift point `r′`.
///
/// Step 1's norm content is deliberately absent: it is Def. 23's
/// `‖s1‖∞ < b1, ‖s2‖∞ < b2`, which [`gh_open_report`] gates as two separate
/// named conditions, so running the `ξ`-batched `Q_N` of p. 44 here would be one
/// fact under two names.
///
/// # Errors
/// [`FinError::WrongVariableCount`] / [`FinError::WrongLength`] when `r` or
/// `r′` does not index the two layers.
pub fn finish<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    reshape: &ReshapeProof<R, D>,
    r: Vec<PolyRing<R, D>>,
    r_prime: Vec<PolyRing<R, D>>,
) -> Result<FinProof<R, D>, FinError>
where
    R: Ring + CenteredRing,
{
    let commitment = &reshape.commitment;
    let bottom = layer_variables(commitment.s2.len());
    if r.len() != bottom || r_prime.len() != bottom {
        return Err(FinError::WrongVariableCount {
            got: r.len().max(r_prime.len()),
            expected: bottom,
        });
    }
    let layer1 = &r[..fin.top_variables()];
    let a1 = tree_eval::mle_at_ring(&commitment.s1, layer1).map_err(FinError::Eval)?;
    let a2 = tree_eval::mle_at_ring(&commitment.s2, &r).map_err(FinError::Eval)?;
    let (q, a, b) = gh_forms(fin, commitment, &r_prime)?;
    let y1 = tree_eval::inner_product(&q, &commitment.s1);
    let y2 = split_form(&a, &b, &commitment.s2);
    Ok(FinProof {
        reshape: reshape.clone(),
        r,
        a1,
        a2,
        r_prime,
        y1,
        y2,
        q,
        a,
        b,
    })
}

/// `log₂` of a layer's entry count: `γ + log(nα1)` for `s1`, `γ+β+log α2` for
/// `s2` (the two point lengths `OE(2)` prints, p. 40).
///
/// # Panics
/// If `len` is not a power of two — neither layer can be, since both are
/// `2^{…}·α` digit vectors.
fn layer_variables(len: usize) -> usize {
    assert!(len.is_power_of_two(), "a Greyhound layer is 2^ν entries");
    len.trailing_zeros() as usize
}

/// The `GHPrincipal′` forms of §5.4.3 at the shift point `r′`: Eq. (37)'s `q` and
/// Lemma 16's `a, b`.
///
/// # Errors
/// [`FinError::WrongVariableCount`] if `r′` is not `log₂|s2|` long, or if the key
/// is not sized for these layers.
#[allow(clippy::type_complexity)]
pub fn gh_forms<R: Ring, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    commitment: &TwoLayerCommitment<R, D>,
    r_prime: &[PolyRing<R, D>],
) -> Result<(Vec<PolyRing<R, D>>, Vec<PolyRing<R, D>>, Vec<PolyRing<R, D>>), FinError> {
    let bottom = layer_variables(commitment.s2.len());
    if r_prime.len() != bottom || fin.bottom_variables() != bottom {
        return Err(FinError::WrongVariableCount {
            got: r_prime.len(),
            expected: bottom,
        });
    }
    if commitment.s1.len() != 1usize << fin.top_variables() {
        return Err(FinError::WrongLength {
            got: commitment.s1.len(),
            expected: 1usize << fin.top_variables(),
        });
    }
    let q = eval_form_vector(&r_prime[..fin.top_variables()], commitment.s1.len())?;
    // `b` carries the leading `γ` coordinates (the `(I_{2^γ}⊗B2)` block index),
    // `a` the trailing `β + log α2` — see the module doc's second layout note.
    let (a, b) = bivariate_split(r_prime, fin.gamma())?;
    Ok((q, a, b))
}

/// Lemma 16's `a⊺·s2·b`, evaluated as the *nested* sum
/// `Σ_i b_i · (Σ_j a_j · s2[i·|a| + j])` rather than as one flat `êq` table, which
/// is what makes it a second reading of `ỹ2(u2) = y2` instead of a restatement of
/// the first.
///
/// # Panics
/// If `|a|·|b| ≠ |s2|` — the tensor shape is part of the claim, and a truncated
/// inner product would pass vacuously.
pub fn split_form<R: Ring, const D: usize>(
    a: &[PolyRing<R, D>],
    b: &[PolyRing<R, D>],
    s2: &[PolyRing<R, D>],
) -> PolyRing<R, D> {
    assert_eq!(
        a.len() * b.len(),
        s2.len(),
        "a ⊗ b must span s2 exactly"
    );
    let mut acc = tree_eval::zero_ring::<R, D>();
    for (weight, row) in b.iter().zip(s2.chunks(a.len())) {
        acc += weight.clone() * tree_eval::inner_product(a, row);
    }
    acc
}

/// **Every** condition Π^PE_NC,fin and `GH′` print, on top of
/// [`reshape_report`]'s, evaluated without short-circuiting:
///
/// 1. everything Π^Reshape owes ([`reshape_report`]), including that `r` has
///    `µ'+m = log₂|s2|` coordinates (`a2` is the forwarded claim);
/// 2. Prot. 7 Step 2's `a1 = s̃1(r_{[:γ+log(nα1))})`, read back through Lemma 14's
///    multilinear extension;
/// 3. Prot. 7 Step 2's `a2 = s̃2(r)`;
/// 4. §5.4.3: the received `q, a, b` are Eq. (37)'s and Lem. 16's tensors of the
///    received `r′`;
/// 5. `GHPrincipal′`'s extra row `q⊺·s1 = y1` — the one `GH′` adds to stock
///    Greyhound, and the equation that binds a `TE` side-claim's value to the
///    recommitted layers;
/// 6. `GHPrincipal′`'s row `a⊺·s2·b = y2`.
#[allow(clippy::too_many_arguments)]
pub fn fin_report<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    tree: &TreeKey<R, D, BASE, ALPHA>,
    fin: &FinKey<R, D, BASE, ALPHA>,
    proof: &FinProof<R, D>,
    claims: &[SideClaim<R, D>],
    k: usize,
    zeta: R,
    xi: R,
    eta: R,
) -> Vec<FinError>
where
    R: Ring + CenteredRing,
{
    let mut bad = reshape_report(
        tree,
        fin,
        &proof.reshape,
        claims,
        k,
        zeta,
        xi,
        eta,
    );
    let mut push = |error: FinError| {
        if !bad.contains(&error) {
            bad.push(error);
        }
    };
    let commitment = &proof.reshape.commitment;
    // 1. the two points have the variables their layers need.
    let bottom = layer_variables(commitment.s2.len());
    if proof.r.len() != bottom || proof.r_prime.len() != bottom {
        push(FinError::WrongVariableCount {
            got: proof.r.len().max(proof.r_prime.len()),
            expected: bottom,
        });
        return bad;
    }
    // 2./3. Prot. 7 Step 2's sent evaluations.
    let layer1 = &proof.r[..fin.top_variables()];
    match tree_eval::mle_at_ring(&commitment.s1, layer1) {
        Ok(want) => {
            if want != proof.a1 {
                push(FinError::Layer1ClaimMismatch);
            }
        }
        Err(err) => push(FinError::Eval(err)),
    }
    match tree_eval::mle_at_ring(&commitment.s2, &proof.r) {
        Ok(want) => {
            if want != proof.a2 {
                push(FinError::Layer2ClaimMismatch);
            }
        }
        Err(err) => push(FinError::Eval(err)),
    }
    // 4. §5.4.3's forms: the received q, a, b must be the tensors of the received
    //    r′, or y1 and y2 are claims about a point the reduction never chose.
    match gh_forms(fin, commitment, &proof.r_prime) {
        Ok((q, a, b)) => {
            if q != proof.q || a != proof.a || b != proof.b {
                push(FinError::FormMismatch);
            }
        }
        Err(error) => push(error),
    }
    // 5. GHPrincipal′'s `q⊺·s1 = y1`. The length gate is not decoration:
    //    `inner_product` panics on a mismatch rather than truncating.
    if proof.q.len() != commitment.s1.len() {
        push(FinError::WrongLength {
            got: proof.q.len(),
            expected: commitment.s1.len(),
        });
    } else if tree_eval::inner_product(&proof.q, &commitment.s1) != proof.y1 {
        push(FinError::QFormMismatch);
    }
    // 6. GHPrincipal′'s `a⊺·s2·b = y2`.
    if proof.a.len() * proof.b.len() != commitment.s2.len() {
        push(FinError::WrongLength {
            got: proof.a.len() * proof.b.len(),
            expected: commitment.s2.len(),
        });
    } else if split_form(&proof.a, &proof.b, &commitment.s2) != proof.y2 {
        push(FinError::ABFormMismatch);
    }
    bad
}

/// The verifier: [`fin_report`] followed by "take the first", which is
/// `Π^Fin → (0,1)`'s verdict (p. 39): `Ok(())` is the accepting branch.
///
/// # Errors
/// The first entry of [`fin_report`].
#[allow(clippy::too_many_arguments)]
pub fn fin_verify<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    tree: &TreeKey<R, D, BASE, ALPHA>,
    fin: &FinKey<R, D, BASE, ALPHA>,
    proof: &FinProof<R, D>,
    claims: &[SideClaim<R, D>],
    k: usize,
    zeta: R,
    xi: R,
    eta: R,
) -> Result<(), FinError>
where
    R: Ring + CenteredRing,
{
    fin_report(tree, fin, proof, claims, k, zeta, xi, eta)
        .into_iter()
        .next()
        .map_or(Ok(()), Err)
}

/// Ring elements `Π^Fin` puts on the wire: `t*_reshape` (`n`), the two batched
/// claims `v_A`, `v_G`, Step 2's `a1`, `a2`, and Step 3's `y1`, `y2`. The points
/// `r`, `r′` are transcript-derived, and `q`, `a`, `b` are computed by the
/// verifier from `r′`, so none of them is sent.
///
/// This is Fig. 6's (p. 47) "1 commitment + 2 RF + 2 RF" part of the finish row;
/// [`FinishAccounting`] computes the whole row and names what this compilation
/// does not send.
pub fn wire_rings<R: Ring, const D: usize>(proof: &FinProof<R, D>) -> usize {
    proof.reshape.commitment.t.len() + 6
}

/// The entries `Π^Fin`'s `s_reshape` holds — the witness size, which this
/// compilation makes the verifier *read* (no `BatchSC`) and the paper's never
/// sends. Kept separate from [`wire_rings`] so the two are never conflated.
pub fn witness_entries<R: Ring, const D: usize>(proof: &FinProof<R, D>) -> usize {
    proof.reshape.commitment.s1.len() + proof.reshape.commitment.s2.len()
}

/// What `GH′` commits to *before* the verifier sends `η` (p. 45: "η would need to
/// be sent by the verifier after the commitments to `ŵ, s1, z` are sent"): the
/// three witnesses Eq. (38)'s `z` column vector holds. `s1` is already in
/// [`TwoLayerCommitment`], so only the other two legs are new messages.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GhPrimeProof<R: Ring, const D: usize> {
    /// `ŵ ← G⁻¹_{b1,2^γ}(s2·a)`: the gadget image of Lemma 16's column
    /// combination, `2^γ·α1` entries.
    pub w_hat: Vec<PolyRing<R, D>>,
    /// `v = D·ŵ ∈ R_F^n`: Eq. (38) row 1's left-hand commitment.
    pub v: Vec<PolyRing<R, D>>,
    /// `z = Σ_j c_j·s2,j ∈ R^{2^β α2}`: the folded second-layer opening, i.e.
    /// Greyhound's `z` leg.
    pub z: Vec<PolyRing<R, D>>,
}

/// `d·(Σ_j norm(c_j))·(b2−1)`, the bound on `‖z‖∞` for `z = Σ_j c_j·s2,j` with
/// `s2` `b2`-short: negacyclic multiplication is a `d`-term convolution, so
/// `‖x·y‖∞ ≤ d·‖x‖∞·‖y‖∞`. At `r` ternary challenges and `b2 = 2` it reads
/// `d·r`, which is exactly the crate's ternary [`crate::pcs::B_Z`]; `GH′`'s Cor. 5
/// inherits Greyhound's norm gates for an arbitrary challenge set, and without this
/// bound the row-5 equation would be checkable by an arbitrarily long `z`.
///
/// Saturating on the products, and *not* floored at one: with all-zero challenges
/// the bound genuinely is `0`, and a gate that rounded it up would accept a `z` the
/// fold cannot produce. `d ≥ 1` and `b2 − 1 ≥ 1` for any legal base, so `0` is the
/// only degenerate value it can take.
pub fn folded_norm_bound<R: Ring + CenteredRing, const D: usize>(
    challenges: &[PolyRing<R, D>],
    base2: u64,
) -> u64 {
    let sum: u64 = challenges
        .iter()
        .map(|c| max_norm(core::slice::from_ref(c)))
        .fold(0, u64::saturating_add);
    (D as u64)
        .saturating_mul(sum)
        .saturating_mul(base2.saturating_sub(1))
}

/// `s2·a`: the column combination of the `2^γ × 2^β α2` matrix `s2` by Lemma
/// 16's `a` — the vector `w` whose digit expansion is `ŵ` and whose inner product
/// with `b` is `y2`.
fn column_combination<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    s2: &[PolyRing<R, D>],
    a: &[PolyRing<R, D>],
) -> Vec<PolyRing<R, D>>
where
    R: Ring,
{
    s2.chunks(fin.inner_width())
        .map(|row| tree_eval::inner_product(a, row))
        .collect()
}

/// `GH′`'s prover: `w = s2·a`, `ŵ = G⁻¹_{b1,2^γ}(w)`, `v = D·ŵ`, and
/// `z = Σ_j c_j·s2,j`.
///
/// `claim` is the `OE(2)` instance being reduced — its `a` (Lemma 16) fixes the
/// column combination, and its `y1, y2, b` are what the rows below re-read.
///
/// # Errors
/// [`FinError::WrongLength`] unless `|a| = 2^β α2`, `|s2| = 2^{γ+β}α2` and there
/// is one challenge per `2^γ` block.
pub fn gh_prime_prove<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    claim: &FinProof<R, D>,
    challenges: &[PolyRing<R, D>],
) -> Result<GhPrimeProof<R, D>, FinError>
where
    R: Ring + CenteredRing,
{
    let s2 = &claim.reshape.commitment.s2;
    if claim.a.len() != fin.inner_width()
        || s2.len() != fin.bottom_len()
        || challenges.len() != fin.nodes()
    {
        return Err(FinError::WrongLength {
            got: challenges.len(),
            expected: fin.nodes(),
        });
    }
    let w = column_combination(fin, s2, &claim.a);
    let w_hat = gadget::split::<R, D, BASE, ALPHA>(&w);
    let v = fin.d().matvec(&w_hat).map_err(|err| FinError::WrongLength {
        got: err.got,
        expected: err.expected,
    })?;
    let mut z = vec![tree_eval::zero_ring::<R, D>(); fin.inner_width()];
    for (c, block) in challenges.iter().zip(s2.chunks(fin.inner_width())) {
        for (acc, value) in z.iter_mut().zip(block) {
            *acc += c.clone() * value;
        }
    }
    Ok(GhPrimeProof { w_hat, v, z })
}

/// **Every** condition of Eq. (38) plus the two norm gates Cor. 5 inherits from
/// Greyhound's Thm. 4.1, evaluated rather than short-circuiting.
///
/// Eq. (38) is the five-row system `P·(ŵ, s1, z)⊺ = h` printed on p. 45. Row by
/// row here:
///
/// 1. `D·ŵ = v` → [`FinError::GhCommitmentMismatch`];
/// 2. `B·s1 = u` *is* Def. 23's root equation, so it keeps the one name
///    [`gh_open_report`] gives it ([`FinError::RootMismatch`]) rather than
///    getting a second;
/// 3. `b⊺·G_{b1,2^γ}·ŵ = y2` → [`FinError::GhEvalRowMismatch`];
/// 4. `c⊺·G_{b1,2^γ}·ŵ − a⊺·z = 0` → [`FinError::GhFoldRowMismatch`];
/// 5. `(c⊺⊗G_{b1,n})·s1 + η·ẽ₁·(q⊺s1) − B2·z = η·y₁·ẽ₁` →
///    [`FinError::GhEq38LastRowMismatch`].
///
/// Row 5 is the whole modification: the `+η·ẽ₁·q⊺` entry in that row's `s1`
/// column is what carries the *first* layer's Eq. (37) claim into the linear
/// relation LaBRADOR proves, and `ẽ₁` is the first standard basis vector of
/// `R_F^n`, so of the `n` rows only row 0 carries the new term — which is why
/// moving `q⊺·s1` leaves every row but `row = 0` of the last equation alone.
///
/// The `q`, `a`, `b` used here are the ones the `OE(2)` instance carries, exactly
/// as `GHPrincipal′(b1,b2)` lists them among its public inputs; that they are the
/// tensors of the forwarded point is [`fin_report`]'s [`FinError::FormMismatch`]
/// gate, and Eq. (37) itself is re-checked here as its own row
/// ([`FinError::QFormMismatch`]) because row 5's `η` term is stated in terms of
/// `q⊺·s1`, not in terms of `y1`.
///
/// A shape mismatch is reported as [`FinError::WrongLength`] and returned alone:
/// the rows above index these vectors, and a truncated one would make an inner
/// product agree vacuously.
pub fn gh_prime_report<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    claim: &FinProof<R, D>,
    proof: &GhPrimeProof<R, D>,
    challenges: &[PolyRing<R, D>],
    eta: &PolyRing<R, D>,
) -> Vec<FinError>
where
    R: Ring + CenteredRing,
{
    let mut bad: Vec<FinError> = Vec::new();
    let mut push = |error: FinError| {
        if !bad.contains(&error) {
            bad.push(error);
        }
    };
    let commitment = &claim.reshape.commitment;
    if proof.w_hat.len() != fin.w_len()
        || proof.v.len() != fin.rows()
        || proof.z.len() != fin.inner_width()
        || challenges.len() != fin.nodes()
        || commitment.s1.len() != fin.top_len()
        || commitment.s2.len() != fin.bottom_len()
        || claim.a.len() != fin.inner_width()
        || claim.b.len() != fin.nodes()
    {
        push(FinError::WrongLength {
            got: proof.w_hat.len(),
            expected: fin.w_len(),
        });
        return bad;
    }
    // The norm gates first: everything below is an extraction argument about a
    // *short* witness, so an out-of-range ŵ or z makes the rows meaningless
    // rather than false.
    let got = max_norm(&proof.w_hat);
    if got >= BASE {
        push(FinError::GhWNotShort { got, bound: BASE });
    }
    let bound = folded_norm_bound(challenges, BASE);
    let got = max_norm(&proof.z);
    if got > bound {
        push(FinError::GhZNotShort { got, bound });
    }
    // Row 1: D·ŵ = v.
    match fin.d().matvec(&proof.w_hat) {
        Ok(expect) => {
            if let Some(at) = expect
                .iter()
                .zip(proof.v.iter())
                .position(|(want, got)| got != want)
            {
                push(FinError::GhCommitmentMismatch { at });
            }
        }
        Err(err) => push(FinError::WrongLength {
            got: err.got,
            expected: err.expected,
        }),
    }
    // Rows 3 and 4 open the same row combination G_{b1,2^γ}·ŵ.
    let w = gadget::join::<R, D, BASE, ALPHA>(&proof.w_hat);
    if tree_eval::inner_product(&claim.b, &w) != claim.y2 {
        push(FinError::GhEvalRowMismatch);
    }
    if tree_eval::inner_product(challenges, &w) != tree_eval::inner_product(&claim.a, &proof.z) {
        push(FinError::GhFoldRowMismatch);
    }
    // Eq. (37) on its own — the claim row 5 batches in.
    let side = tree_eval::inner_product(&claim.q, &commitment.s1);
    if side != claim.y1 {
        push(FinError::QFormMismatch);
    }
    // Row 5: (c⊺G_{b1,n})·s1 + η·ẽ₁·(q⊺s1) = B2·z + η·y₁·ẽ₁.
    let recomposed = gadget::join::<R, D, BASE, ALPHA>(&commitment.s1);
    let folded = match fin.b2().matvec(&proof.z) {
        Ok(values) => values,
        Err(err) => {
            push(FinError::WrongLength {
                got: err.got,
                expected: err.expected,
            });
            return bad;
        }
    };
    for row in 0..fin.rows() {
        let mut combined = tree_eval::zero_ring::<R, D>();
        for (c, block) in challenges.iter().zip(recomposed.chunks(fin.rows())) {
            combined += c.clone() * &block[row];
        }
        let mut lhs = combined - &folded[row];
        let mut expect = tree_eval::zero_ring::<R, D>();
        if row == 0 {
            lhs += eta.clone() * &side;
            expect = eta.clone() * &claim.y1;
        }
        if lhs != expect {
            push(FinError::GhEq38LastRowMismatch { row });
            break;
        }
    }
    bad
}

/// Eq. (38) as **LaBRADOR's principal relation** — §5.4.3's last step, which is
/// where the paper says the matrix equation is "proven by using LaBRADOR as a
/// sub-protocol".
///
/// Every row of Eq. (38) is *linear* in the stacked witness `(ŵ, s1, z)`, so each
/// row coordinate becomes one [`QuadFn`] with `a = 0`, `φ` the matrix row and `b`
/// the claimed entry: `Σᵢ ⟨φᵢ, xᵢ⟩ = b`. `Relation::rank` is one number, so the
/// three parts are padded to the widest (`|s1|`); a padded slot carries zero
/// coefficient and zero witness, which neither weakens the statement nor inflates
/// `β`.
///
/// Row 2 (`B·s1 = u`) is included even though Def. 23 already gates it: LaBRADOR
/// proves the *system*, and dropping a row would make the statement proved weaker
/// than the one [`gh_prime_report`] accepts.
///
/// The norm budget is derived, not asserted: `ŵ` and `s1` are gadget images, so
/// every entry has magnitude `≤ b−1`, and `z = Σⱼ cⱼ·s2,j` is bounded by
/// [`folded_norm_bound`]. That is the number LaBRADOR's slack condition
/// (`β ≤ √(30/128)·q/125`) has to fit, and it is why the budget is computed here
/// rather than passed in.
///
/// # Errors
/// [`FinError::WrongLength`] when the shapes do not describe this key.
pub fn eq38_relation<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    claim: &FinProof<R, D>,
    gh: &GhPrimeProof<R, D>,
    challenges: &[PolyRing<R, D>],
    eta: &PolyRing<R, D>,
) -> Result<Relation<R, D>, FinError>
where
    R: Ring + CenteredRing,
{
    let commitment = &claim.reshape.commitment;
    let (nodes, width, rows, alpha) = (fin.nodes(), fin.inner_width(), fin.rows(), ALPHA);
    let (w_len, s1_len) = (fin.w_len(), fin.top_len());
    if gh.w_hat.len() != w_len
        || gh.z.len() != width
        || gh.v.len() != rows
        || commitment.s1.len() != s1_len
        || commitment.s2.len() != fin.bottom_len()
        || commitment.t.len() != rows
        || challenges.len() != nodes
        || claim.b.len() != nodes
        || claim.a.len() != width
        || claim.q.len() != s1_len
    {
        return Err(FinError::WrongLength {
            got: gh.w_hat.len(),
            expected: w_len,
        });
    }
    // The three witness parts share `Relation::rank`; `s1` is the widest.
    let rank = w_len.max(s1_len).max(width);
    let mut phi_w = vec![zero_elt::<R, D>(); rank];
    let mut phi_s = vec![zero_elt::<R, D>(); rank];
    let mut phi_z = vec![zero_elt::<R, D>(); rank];
    let mut full: Vec<QuadFn<R, D>> = Vec::new();
    let mut push = |phi_w: &mut Vec<PolyRing<R, D>>,
                    phi_s: &mut Vec<PolyRing<R, D>>,
                    phi_z: &mut Vec<PolyRing<R, D>>,
                    b: PolyRing<R, D>| {
        full.push(QuadFn {
            a: vec![vec![zero_elt::<R, D>(); 3]; 3],
            phi: vec![phi_w.clone(), phi_s.clone(), phi_z.clone()],
            b,
        });
        phi_w.iter_mut().for_each(|c| *c = zero_elt::<R, D>());
        phi_s.iter_mut().for_each(|c| *c = zero_elt::<R, D>());
        phi_z.iter_mut().for_each(|c| *c = zero_elt::<R, D>());
    };

    // Row 1: D·ŵ = v, one function per row of D.
    for rho in 0..rows {
        let row = fin.d().row(rho);
        phi_w[..w_len].clone_from_slice(row);
        push(&mut phi_w, &mut phi_s, &mut phi_z, gh.v[rho].clone());
    }
    // Row 2: B1·s1 = t — Def. 23's root equation, part of the system.
    for rho in 0..rows {
        let row = fin.b1().row(rho);
        phi_s[..s1_len].clone_from_slice(row);
        push(&mut phi_w, &mut phi_s, &mut phi_z, commitment.t[rho].clone());
    }
    // Row 3: b⊺·G_{b1,2^γ}·ŵ = y2. `G` recomposes `Σ_k BASE^k·ŵ[i·α + k]`, so the
    // coefficient of `ŵ[i·α + k]` is `b[i]·BASE^k`.
    let powers: Vec<PolyRing<R, D>> = (0..alpha)
        .scan(tree_eval::embed::<R, D>(R::ONE), |acc, _| {
            let out = acc.clone();
            *acc = acc.clone() * &tree_eval::embed::<R, D>(R::from(BASE));
            Some(out)
        })
        .collect();
    for i in 0..nodes {
        for k in 0..alpha {
            phi_w[i * alpha + k] = claim.b[i].clone() * &powers[k];
        }
    }
    push(&mut phi_w, &mut phi_s, &mut phi_z, claim.y2.clone());
    // Row 4: c⊺·G_{b1,2^γ}·ŵ − a⊺·z = 0.
    for i in 0..nodes {
        for k in 0..alpha {
            phi_w[i * alpha + k] = challenges[i].clone() * &powers[k];
        }
    }
    for j in 0..width {
        phi_z[j] = tree_eval::zero_ring::<R, D>() - claim.a[j].clone();
    }
    push(&mut phi_w, &mut phi_s, &mut phi_z, tree_eval::zero_ring::<R, D>());
    // Row 5: (c⊺G_{b1,n})·s1 + η·ẽ₁·(q⊺s1) − B2·z = η·y₁·ẽ₁, one function per
    // coordinate of R_F^n. Only row 0 carries the `η` terms — `ẽ₁` is the first
    // standard basis vector, and that single entry is §5.4.3's whole modification.
    for rho in 0..rows {
        for j in 0..nodes {
            for k in 0..alpha {
                phi_s[(j * rows + rho) * alpha + k] = challenges[j].clone() * &powers[k];
            }
        }
        if rho == 0 {
            for slot in phi_s[..s1_len].iter_mut().zip(claim.q.iter()) {
                *slot.0 += eta.clone() * slot.1;
            }
        }
        let row = fin.b2().row(rho);
        phi_z[..width].clone_from_slice(row);
        phi_z[..width].iter_mut().for_each(|c| *c = tree_eval::zero_ring::<R, D>() - c.clone());
        let b = if rho == 0 {
            eta.clone() * &claim.y1
        } else {
            tree_eval::zero_ring::<R, D>()
        };
        push(&mut phi_w, &mut phi_s, &mut phi_z, b);
    }

    // The derived budget: binary digits, and `z` bounded by the convolution.
    let digit = (BASE - 1) as u128;
    let z_bound = folded_norm_bound(challenges, BASE) as u128;
    let norm_bound_sq = (D as u128)
        * (digit * digit * (w_len + s1_len) as u128 + (width as u128) * z_bound * z_bound);
    Ok(Relation {
        rank,
        multiplicity: 3,
        full,
        ct_only: Vec::new(),
        norm_bound_sq,
    })
}

/// `GH′`'s verifier: [`gh_prime_report`] then "take the first". `GH′` is a *weak*
/// interactive reduction (Cor. 5), so its acceptance is the bit `(0,1)` — the
/// whole output of `Π^Fin`.
///
/// # Errors
/// The first entry of [`gh_prime_report`].
pub fn gh_prime_verify<R, const D: usize, const BASE: u64, const ALPHA: usize>(
    fin: &FinKey<R, D, BASE, ALPHA>,
    claim: &FinProof<R, D>,
    proof: &GhPrimeProof<R, D>,
    challenges: &[PolyRing<R, D>],
    eta: &PolyRing<R, D>,
) -> Result<(), FinError>
where
    R: Ring + CenteredRing,
{
    gh_prime_report(fin, claim, proof, challenges, eta)
        .into_iter()
        .next()
        .map_or(Ok(()), Err)
}

/// Ring elements `GH′` puts on the wire *in addition to* [`wire_rings`]: `ŵ`
/// (`2^γ·α1`), `v` (`n`) and `z` (`2^β α2`). Kept separate because these three
/// are the messages of the LaBRADOR-backed inner protocol, not of `Π^Reshape`,
/// and Fig. 6 accounts for them under `Greyhound(2^{µ+k+1}nαd)`.
pub fn gh_prime_wire_elements<R: Ring, const D: usize>(proof: &GhPrimeProof<R, D>) -> usize {
    proof.w_hat.len() + proof.v.len() + proof.z.len()
}

/// One row of Fig. 6 (p. 47)'s proof-size breakdown, computed from the parameter
/// rather than read off the printed table.
///
/// The `finish` row is
/// `SC(2b) + ShiftSC(2,1) + 2 R_K + BatchSC(2,1) + 2 R_F + 1 commitment`,
/// `+ Greyhound(2^{µ+k+1}nαd)`, where `µ := ⌈log₂(2ω+1)⌉` and every sum-check
/// message is a `K`-valued field element (`e` coefficients of `F_q` each, since
/// §4's ring sum-checks run over the degree-`e` extension). The last term is the
/// one this crate cannot compute: its size *is* the LaBRADOR recursion (module
/// doc, "What is *not* here"), which is why [`Self::greyhound_allowance`] reports
/// it as a difference rather than as a formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FinishAccounting {
    /// `SC(2b)`: `2b+1` elements per round, `µ′+m` rounds.
    pub norm_sumcheck: usize,
    /// `ShiftSC(2,1)`: `3` elements per round.
    pub shift_sc: usize,
    /// `BatchSC(2,1)`: `3` elements per round.
    pub batch_sc: usize,
    /// The two `R_K` claims `a1, a2` (Prot. 7 Step 2).
    pub packed_claims: usize,
    /// The two `R_F` claims `y1, y2` (Prot. 7 Step 3).
    pub eval_claims: usize,
    /// The one `R_F^n` commitment `t*_reshape` (Prot. 6 Step 3).
    pub commitment: usize,
    /// `2^{µ+k+1}·n·α·d`, the field-element input size `Greyhound(·)` is stated
    /// at — a size, not a byte count, because its proof is the unlanded term.
    pub greyhound_input: usize,
    /// `µ′+m`, the variables each of the three sum-checks runs over.
    pub rounds: usize,
}

impl FinishAccounting {
    /// The row's components for one parameterisation.
    ///
    /// `field_bytes` is `⌈log₂ q / 8⌉` and `e` the extension degree that makes a
    /// `K`-valued message cost `e·log₂ q` bits — Protocols 1–2 state their
    /// sum-checks over `K`, so a caller accounting for `F` alone passes `e = 1`.
    ///
    /// # Panics
    /// If `n·α` is not a power of two (`m := log₂(nα)` must exist) or `base < 2`.
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        field_bytes: usize,
        e: usize,
        d: usize,
        n: usize,
        alpha: usize,
        k: usize,
        omega: usize,
        base: usize,
    ) -> Self {
        let slot = n * alpha;
        assert!(
            slot.is_power_of_two(),
            "m := log₂(nα) must exist: nα = {slot} is not a power of two"
        );
        assert!(base >= 2, "a digit base below 2 has no expansion");
        let mu = (2 * omega + 1).next_power_of_two().trailing_zeros() as usize;
        let rounds = mu + k + 1 + slot.trailing_zeros() as usize;
        let ring_bytes = field_bytes * d;
        Self {
            norm_sumcheck: (2 * base + 1) * rounds * e * field_bytes,
            shift_sc: 3 * rounds * e * field_bytes,
            batch_sc: 3 * rounds * e * field_bytes,
            packed_claims: 2 * ring_bytes * e,
            eval_claims: 2 * ring_bytes,
            commitment: n * ring_bytes,
            greyhound_input: (1usize << (mu + k + 1)) * slot * d,
            rounds,
        }
    }

    /// The components this module's `Π^Fin` actually sends, in bytes.
    pub const fn implemented_bytes(&self) -> usize {
        self.norm_sumcheck
            + self.shift_sc
            + self.batch_sc
            + self.packed_claims
            + self.eval_claims
            + self.commitment
    }

    /// The printed row's total, less what [`Self::implemented_bytes`] accounts
    /// for: that difference *is* the `Greyhound(2^{µ+k+1}nαd)` term, so this is
    /// the size of the hole rather than a measurement of it.
    pub const fn greyhound_allowance(&self, paper_total_kb: usize) -> usize {
        (paper_total_kb * 1024).saturating_sub(self.implemented_bytes())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    /// `q = 2³² − 99`: prime, `≡ 5 (mod 8)`, Maltese P3's field size.
    type F = Zq<4294967197>;
    /// A degree that keeps the toy instance interactive; P3's `d = 64` is the
    /// example's job.
    const D: usize = 8;
    /// P3's gadget base.
    const BASE: u64 = 2;
    /// `α = ⌈log₂ q⌉ = 32`.
    const ALPHA: usize = 32;
    /// `nα`, one tree node's digits, at `n = 2`.
    const SLOT: usize = 64;
    /// `m = log₂(nα)`.
    const M: usize = 6;
    /// The folding arity the side-claims carry.
    const K: usize = 2;
    /// Def. 23's `γ`: `s1` is `2^γ` blocks of `nα1`.
    const GAMMA: usize = 3;
    /// Def. 23's `β`: `B2 ∈ R^{n×2^β α2}`.
    const BETA: usize = 3;
    /// `µ' + m`, the coordinate count of `r` and `r′`: `⌈log(2ω+1)⌉+k+1+m`.
    const NV: usize = 11;

    type Key = TreeKey<F, D, BASE, ALPHA>;
    type Fin = FinKey<F, D, BASE, ALPHA>;
    type Elt = PolyRing<F, D>;

    fn monomial(c: u64) -> Elt {
        let mut coefficients = vec![F::ZERO; D];
        coefficients[0] = F::from(c);
        PolyRing::from_coefficients(coefficients)
    }

    fn ring_point(coordinates: usize, tag: u64) -> Vec<Elt> {
        (0..coordinates)
            .map(|i| {
                PolyRing::from_coefficients(
                    (0..D)
                        .map(|j| F::from(((i as u64 * 7_919 + j as u64 * 13 + tag) % 251) as u64))
                        .collect(),
                )
            })
            .collect()
    }

    fn scalar_vector(len: usize, value: u64) -> Vec<Elt> {
        vec![monomial(value); len]
    }

    fn message(len: usize) -> Vec<Elt> {
        (0..len)
            .map(|i| {
                PolyRing::from_coefficients(
                    (0..D)
                        .map(|j| F::from(((i as u64 * 1_000_003 + j as u64 * 40_503 + 7) % 97) as u64))
                        .collect(),
                )
            })
            .collect()
    }

    fn key() -> Key {
        Key::setup(&[0x4du8; 32], 2)
    }

    fn fin_key() -> Fin {
        Fin::setup(&[0x5fu8; 32], 2, GAMMA, BETA)
    }

    /// A height-`height` tree commitment, i.e. a `TE(1,·,b)`/`PE(1,·,b)` witness.
    fn tree_of(k: &Key, height: usize) -> TreeOpening<F, D> {
        k.commit(&message((1usize << height) * k.rows()))
            .expect("a legal leaf length")
    }

    /// A `TE(1,ℓ,b)` claim: the value is the concatenated opening's own MLE, so
    /// the honest case is true by construction (Prot. 6's `Input`).
    fn te_claim(k: &Key, height: usize, tag: u64) -> SideClaim<F, D> {
        let opening = tree_of(k, height);
        let u = ring_point(height + 1 + M, tag);
        let s = tree_eval::concatenated(SLOT, &opening.layers);
        let v = tree_eval::mle_at_ring(&s, &u).expect("a TE point");
        SideClaim {
            kind: ClaimKind::Te,
            opening,
            u,
            v,
        }
    }

    /// A `PE(1,ℓ,b)` claim: the value is the *bottom layer's* MLE (Eq. 10), read
    /// through the same `concatenated` vector Π^Reshape will recommit.
    fn pe_claim(k: &Key, height: usize, tag: u64) -> SideClaim<F, D> {
        let opening = tree_of(k, height);
        let u = ring_point(height + M, tag);
        let s = tree_eval::concatenated(SLOT, &opening.layers);
        let v = tree_eval::layer_value(&s, SLOT, height, &u).expect("a PE point");
        SideClaim {
            kind: ClaimKind::Pe,
            opening,
            u,
            v,
        }
    }

    /// `TE(1,k,b)^1 × PE(1,k,b)^2` — one `ω`-round cycle's worth of set-aside
    /// claims, with the base case deliberately shorter than `k` so the padding
    /// rule of the module doc is exercised rather than assumed.
    fn claims(k: &Key) -> Vec<SideClaim<F, D>> {
        vec![te_claim(k, K, 11), pe_claim(k, K, 23), pe_claim(k, K - 1, 37)]
    }

    /// One finished instance: the reshaping challenges, the two transcript points,
    /// and the prover's full message set.
    struct Setup {
        tree: Key,
        fin: Fin,
        claims: Vec<SideClaim<F, D>>,
        zeta: F,
        xi: F,
        eta: F,
        proof: FinProof<F, D>,
    }

    impl Setup {
        fn new() -> Self {
            let tree = key();
            let fin = fin_key();
            let claims = claims(&tree);
            let openings: Vec<&TreeOpening<F, D>> =
                claims.iter().map(|claim| &claim.opening).collect();
            let values: Vec<Elt> = claims.iter().map(|claim| claim.v.clone()).collect();
            let points: Vec<&[Elt]> = claims.iter().map(|claim| claim.u.as_slice()).collect();
            let binding =
                tree_eval::statement_bytes(tree.seed(), &openings, &values, &points);
            let drawn = tree_eval::challenges::<F>(b"tree-fin-tests", &binding, 3);
            let (zeta, xi, eta) = (drawn[0], drawn[1], drawn[2]);
            let r = tree_eval::ring_challenges::<F, D>(b"tree-fin-r", &binding, NV);
            let r_prime = tree_eval::ring_challenges::<F, D>(b"tree-fin-r-prime", &binding, NV);
            let proof = fin_prove(
                &tree, &fin, &claims, K, zeta, xi, eta, r, r_prime,
            )
            .expect("Π^Fin is complete on a fresh cycle shape");
            Self {
                tree,
                fin,
                claims,
                zeta,
                xi,
                eta,
                proof,
            }
        }

        fn report(&self) -> Vec<FinError> {
            fin_report(
                &self.tree,
                &self.fin,
                &self.proof,
                &self.claims,
                K,
                self.zeta,
                self.xi,
                self.eta,
            )
        }
    }

    #[test]
    fn the_honest_finish_is_accepted() {
        let sc = Setup::new();
        assert!(
            sc.report().is_empty(),
            "the honest proof was refused by {:?}",
            sc.report()
        );
        fin_verify(
            &sc.tree, &sc.fin, &sc.proof, &sc.claims, K, sc.zeta, sc.xi, sc.eta,
        )
        .expect("Π^Fin accepts");
        // Def. 23's shape facts, on the instance the doc's arithmetic predicts.
        assert_eq!(sc.fin.bottom_len(), 1 << NV);
        assert_eq!(sc.fin.top_len(), 1 << sc.fin.top_variables());
        assert_eq!(
            sc.proof.reshape.commitment.s2.len(),
            4 * (1usize << (K + 1)) * SLOT,
            "2^⌈log(2ω+1)⌉ blocks of 2^(k+1)·nα"
        );
        // GHCommit's own shortness: `s1` is a gadget image, so the top layer can
        // never violate `‖s1‖∞ < b1` — which is why the *bottom* norm gate is the
        // one an attacker has to break.
        assert!(max_norm(&sc.proof.reshape.commitment.s1) < BASE);
    }

    #[test]
    fn each_def_23_gate_fails_alone() {
        let sc = Setup::new();
        let honest = sc.proof.reshape.commitment.clone();
        let expect = |cm: &TwoLayerCommitment<F, D>, want: Vec<FinError>, label: &str| {
            let got = gh_open_report(&sc.fin, cm);
            assert_eq!(got, want, "{label}: got {got:?}");
        };
        expect(&honest, vec![], "honest");

        // GHOpen line 1 only: `t = B1·s1` is the equation a forged root breaks.
        let mut bad = honest.clone();
        bad.t[0] = bad.t[0].clone() + monomial(1);
        expect(&bad, vec![FinError::RootMismatch { at: 0 }], "forged t");

        // GHOpen line 2 only: an `s2` edit that leaves `s1` (hence `t`) alone.
        let mut bad = honest.clone();
        bad.s2[0] = monomial(1);
        expect(&bad, vec![FinError::LinkMismatch { at: 0 }], "forged s2");

        // GHOpen line 3, top layer: digits `(2, −1)` in place of `(0, 0)` keep
        // `G·s1` bit-for-bit identical (`2·2^k − 1·2^{k+1} = 0`), so only
        // `‖s1‖∞ < b1` can speak once `t` is recomputed for the moved `s1`. This
        // is the non-canonical expansion Π^PE_NC,fin's Step 1 exists to refuse.
        let mut bad = honest.clone();
        let zero = monomial(0);
        let at = honest
            .s1
            .windows(2)
            .enumerate()
            .find(|(index, pair)| {
                index % ALPHA + 1 < ALPHA && pair[0] == zero && pair[1] == zero
            })
            .expect("a gadget image has adjacent zero digits inside one block")
            .0;
        bad.s1[at] = monomial(2);
        bad.s1[at + 1] = monomial(0) - monomial(1);
        assert_eq!(
            gadget::join::<F, D, BASE, ALPHA>(&honest.s1),
            gadget::join::<F, D, BASE, ALPHA>(&bad.s1),
            "the pair move must preserve G·s1"
        );
        bad.t = sc
            .fin
            .b1()
            .matvec(&bad.s1)
            .expect("the same shape the honest commitment had");
        expect(
            &bad,
            vec![FinError::TopNotShort {
                got: 2,
                bound: BASE,
            }],
            "a non-canonical but recomposing s1",
        );

        // GHOpen line 3, bottom layer: re-commit *from* a long `s2`, so `t` and
        // the link are the honest ones for that `s2` and only shortness fails.
        // That is exactly a binding break: `B2·s2' = B2·s2''` with `‖s2''‖∞ ≥ b`.
        let mut long_s2 = sc.proof.reshape.commitment.s2.clone();
        long_s2[3] = monomial(7);
        let forged = gh_commit(&sc.fin, &long_s2).expect("GHCommit takes any s2");
        let got = gh_open_report(&sc.fin, &forged);
        assert_eq!(
            got,
            vec![FinError::BottomNotShort {
                got: 7,
                bound: BASE
            }],
            "a long but consistent recommitment must fail only the b2 gate"
        );
    }

    #[test]
    fn a_forged_te_side_claim_is_caught_by_eq_35_alone() {
        // The point of landing §5.4: Protocol 4 has no equation that reads
        // `v_top` in this shape (its Eq. (12) factor is `êq(0^{ℓ−k}, 1‖…) = 0`),
        // and Eq. (35) is the one the paper binds it with.
        let mut sc = Setup::new();
        assert_eq!(sc.claims[0].kind, ClaimKind::Te);
        sc.claims[0].v = sc.claims[0].v.clone() + monomial(1);
        assert_eq!(
            sc.report(),
            vec![FinError::TeClaimMismatch { block: 0 }],
            "the TE value enters no other Π^Fin equation"
        );
    }

    #[test]
    fn a_forged_pe_side_claim_is_caught_by_eq_36_alone() {
        let mut sc = Setup::new();
        sc.claims[2].v = sc.claims[2].v.clone() + monomial(1);
        assert_eq!(
            sc.report(),
            vec![FinError::PeClaimMismatch { block: 2 }],
            "Step 2(e)'s êq(1 ‖ u_PE, ·) reading is the only equation that sees it"
        );
    }

    #[test]
    fn padded_short_blocks_keep_their_claims_and_wrong_padding_does_not() {
        let sc = Setup::new();
        let claim = &sc.claims[2];
        assert_eq!(claim.height(), K - 1, "the base case is one layer short of k");
        let point = block_point(SLOT, K, claim).expect("a padded block point");
        assert_eq!(point.len(), K + 1 + M);
        let block = tree_eval::concatenated(SLOT, &claim.opening.layers);
        let width = (1usize << (K + 1)) * SLOT;
        // Right-padding the vector and left-padding the point with zeros is the
        // combination Protocol 6's `2^{k+1}nα`-wide blocks assume…
        let mut padded = block.clone();
        padded.resize(width, monomial(0));
        assert_eq!(
            tree_eval::mle_at_ring(&padded, &point).expect("a padded block MLE"),
            claim.v,
            "Prot. 6's blocks are 2^(k+1)nα wide, so a short block must read the same"
        );
        // …and the *only* one that does: left-padding the vector moves the leaf
        // layer out from under Step 2(e)'s `1 ‖ u_PE` selector, which is exactly
        // how a wrong convention would go silently wrong.
        let mut misplaced = vec![monomial(0); width];
        for (slot, value) in misplaced
            .iter_mut()
            .rev()
            .zip(block.iter().rev())
        {
            *slot = value.clone();
        }
        assert_ne!(
            tree_eval::mle_at_ring(&misplaced, &point).expect("the shape is right"),
            claim.v,
            "left-padding the vector would silently re-point every side claim"
        );
        // The unpadded reading agrees, too: `1 ‖ u_PE` is the Eq. (10) selector.
        assert_eq!(
            tree_eval::layer_value(&block, SLOT, claim.height(), &claim.u).expect("layer"),
            claim.v
        );
    }

    #[test]
    fn the_batched_and_side_claims_fail_where_the_paper_prints_them() {
        let mut sc = Setup::new();
        // Eq. (33)'s claim alone is impossible: `v_A` is Eq. (32)'s right-hand
        // side too, so forging it breaks the batch gate with it (p. 43 Step 2(c)).
        sc.proof.reshape.v_a = sc.proof.reshape.v_a.clone() + monomial(1);
        assert_eq!(
            sc.report(),
            vec![FinError::AsideMismatch, FinError::BatchMismatch],
            "one object, two printed equations"
        );

        let mut sc = Setup::new();
        sc.proof.reshape.v_g = sc.proof.reshape.v_g.clone() + monomial(1);
        assert_eq!(
            sc.report(),
            vec![FinError::GsideMismatch, FinError::BatchMismatch]
        );

        // A set-aside *commitment* forgery: Eq. (32) is the equation that reads
        // `t`, and the input relation's own `Open` premise sees it too.
        let mut sc = Setup::new();
        sc.claims[1].opening.root[0] = sc.claims[1].opening.root[0].clone() + monomial(1);
        let got = sc.report();
        assert!(
            got.contains(&FinError::BatchMismatch),
            "Eq. (32) must refuse a `t` that is not a commitment to these digits: {got:?}"
        );
        assert!(
            got.iter().any(|e| matches!(e, FinError::Tree(_))),
            "the input is then not a member of TE × PE either: {got:?}"
        );

        // Step 1(a)'s binding: a two-layer commitment to *something else* that
        // opens perfectly satisfies every one of Def. 23's gates (measured 2026-09-26
        // by this test), which is the Π^Dec `t*_dec` attack re-found one layer up.
        let mut sc = Setup::new();
        let other = scalar_vector(sc.proof.reshape.commitment.s2.len(), 0);
        sc.proof.reshape.commitment =
            gh_commit(&sc.fin, &other).expect("a well-formed commitment");
        let got = sc.report();
        assert!(
            got
                .iter()
                .any(|error| matches!(error, FinError::BlocksMismatch { .. })),
            "an unrelated recommitted vector must be refused: {got:?}"
        );
    }

    #[test]
    fn the_greyhound_prime_rows_each_fail_alone() {
        // Eq. (38)'s extra row `q⊺·s1 = y1` — the §5.4.3 modification — and
        // Lem. 16's `a⊺·s2·b = y2`, each alone.
        let mut sc = Setup::new();
        sc.proof.y1 = sc.proof.y1.clone() + monomial(1);
        assert_eq!(sc.report(), vec![FinError::QFormMismatch]);

        let mut sc = Setup::new();
        sc.proof.y2 = sc.proof.y2.clone() + monomial(1);
        assert_eq!(sc.report(), vec![FinError::ABFormMismatch]);

        // Step 2's two sent evaluations (Prot. 7, p. 44).
        let mut sc = Setup::new();
        sc.proof.a1 = sc.proof.a1.clone() + monomial(1);
        assert_eq!(sc.report(), vec![FinError::Layer1ClaimMismatch]);

        let mut sc = Setup::new();
        sc.proof.a2 = sc.proof.a2.clone() + monomial(1);
        assert_eq!(sc.report(), vec![FinError::Layer2ClaimMismatch]);

        // A prover that sends a `q` for a *different* point and recomputes `y1`
        // to match: every row still balances, and only the form check refuses it.
        let mut sc = Setup::new();
        let mut shifted = sc.proof.r_prime.clone();
        shifted[sc.fin.top_variables() - 1] = shifted[sc.fin.top_variables() - 1].clone()
            + monomial(1);
        sc.proof.q = eval_form_vector(&shifted[..sc.fin.top_variables()], sc.proof.q.len())
            .expect("same coordinate count");
        sc.proof.y1 = tree_eval::inner_product(&sc.proof.q, &sc.proof.reshape.commitment.s1);
        assert_eq!(sc.report(), vec![FinError::FormMismatch]);
    }

    #[test]
    fn the_lemma_16_split_is_not_transposable() {
        let sc = Setup::new();
        let s2 = &sc.proof.reshape.commitment.s2;
        assert_eq!(sc.proof.b.len(), 1usize << GAMMA, "b spans the block index");
        assert_eq!(sc.proof.a.len(), 1usize << (BETA + 5), "a spans one node");
        // Lemma 16's own content: the split form *is* the multilinear extension.
        assert_eq!(
            split_form(&sc.proof.a, &sc.proof.b, s2),
            tree_eval::mle_at_ring(s2, &sc.proof.r_prime).expect("a full point"),
            "a⊺·s2·b = s̃2(r′) must hold by the same code path the claim uses"
        );
        // And the transposition is a different number, so the direction is live.
        assert_ne!(
            split_form(&sc.proof.b, &sc.proof.a, s2),
            split_form(&sc.proof.a, &sc.proof.b, s2),
            "a ∈ R^(2^β α2) / b ∈ R^(2^γ) is a real convention, not a symmetry"
        );
    }

    #[test]
    fn the_streamed_sides_equal_the_printed_tensor_forms() {
        // The report evaluates Eq. (33)/(34) blockwise to avoid materialising an
        // `n·|s_reshape|`-wide tensor; that is only the same claim if it agrees
        // with the vectors this module publishes as the paper's `q_reshape,A` and
        // `q_reshape,G`, paired with `lift_by_eta` and `s_reshape` respectively.
        let sc = Setup::new();
        let s = &sc.proof.reshape.commitment.s2;
        let q_a = q_reshape_a_vector(&sc.tree, SLOT, K, &sc.claims, sc.zeta, sc.xi)
            .expect("Eq. 33's vector");
        let lifted = lift_by_eta(s, sc.eta, sc.tree.rows());
        assert_eq!(q_a.len(), lifted.len(), "both span n·|s_reshape|");
        assert_eq!(
            tree_eval::inner_product(&lifted, &q_a),
            reshape_a_side(&sc.tree, s, SLOT, K, &sc.claims, sc.zeta, sc.xi, sc.eta)
                .expect("the blockwise read-out"),
            "the streamed A side must be Eq. (33)'s inner product"
        );
        let q_g = q_reshape_g_vector(
            SLOT,
            sc.tree.rows(),
            K,
            &sc.claims,
            sc.zeta,
            sc.xi,
            sc.eta,
            BASE,
            ALPHA,
        )
        .expect("Eq. 34's vector");
        assert_eq!(
            tree_eval::scalar_inner_product(&q_g, s),
            reshape_g_side(
                s,
                SLOT,
                sc.tree.rows(),
                K,
                &sc.claims,
                sc.zeta,
                sc.xi,
                sc.eta,
                BASE,
                ALPHA,
            )
            .expect("the weighted read-out"),
            "the G side must be Eq. (34)'s inner product"
        );
    }

    #[test]
    fn a_live_prefix_is_caught_even_when_the_prover_rebinds_its_claims() {
        // Step 2(f)'s `Cpre` is the one Π^Reshape claim a prover can attack by
        // reshaping a vector that is *not* a concatenation of tree openings: here
        // it re-derives `v_A`, `v_G` from the edited `s_reshape`, so the
        // Eq. (33)/(34) re-reads go quiet and the prefix claim is what speaks.
        let mut sc = Setup::new();
        let mut reshaped = sc.proof.reshape.commitment.s2.clone();
        reshaped[1] = monomial(1);
        let commitment = gh_commit(&sc.fin, &reshaped).expect("GHCommit takes any s2");
        let v_a =
            reshape_a_side(&sc.tree, &reshaped, SLOT, K, &sc.claims, sc.zeta, sc.xi, sc.eta)
                .expect("the A side of the edited vector");
        let v_g = reshape_g_side(
            &reshaped,
            SLOT,
            sc.tree.rows(),
            K,
            &sc.claims,
            sc.zeta,
            sc.xi,
            sc.eta,
            BASE,
            ALPHA,
        )
        .expect("the G side of the edited vector");
        sc.proof.reshape = ReshapeProof {
            commitment,
            v_a,
            v_g,
        };
        let got = sc.report();
        assert!(
            got.contains(&FinError::PrefixNotZero { block: 0, at: 1 }),
            "the live prefix must be named: {got:?}"
        );
        assert!(
            got.iter()
                .any(|error| matches!(error, FinError::BlocksMismatch { .. })),
            "Step 1(a)'s binding reads the same coordinate: {got:?}"
        );
        assert!(
            !got.contains(&FinError::AsideMismatch) && !got.contains(&FinError::GsideMismatch),
            "the re-derived claims must satisfy Eq. (33)/(34): {got:?}"
        );
    }

    #[test]
    fn a_padding_block_is_pinned_by_step_1a_alone() {
        // Π^Reshape pads `s_reshape` to `2^⌈log(2ω+1)⌉` blocks, so the last block
        // carries no claim: Step 2(f)'s prefix gate walks the *declared* blocks and
        // never looks at it, and a prover that re-derives Eq. (33)/(34)'s claims
        // *and* the `OE(2)` leg from the edited vector leaves every other check
        // quiet. What still refuses it is Step 1(a)'s binding — the padding is part
        // of Prot. 6's input, not an implementation detail.
        let mut sc = Setup::new();
        let block_width = (1usize << (K + 1)) * SLOT;
        let padding = sc.claims.len();
        assert!(
            (padding + 1) * block_width <= sc.proof.reshape.commitment.s2.len(),
            "this instance must actually have a padding block"
        );
        let at = padding * block_width + 1;
        let mut reshaped = sc.proof.reshape.commitment.s2.clone();
        reshaped[at] = monomial(1);
        let commitment = gh_commit(&sc.fin, &reshaped).expect("GHCommit takes any s2");
        let v_a =
            reshape_a_side(&sc.tree, &reshaped, SLOT, K, &sc.claims, sc.zeta, sc.xi, sc.eta)
                .expect("the A side of the edited vector");
        let v_g = reshape_g_side(
            &reshaped,
            SLOT,
            sc.tree.rows(),
            K,
            &sc.claims,
            sc.zeta,
            sc.xi,
            sc.eta,
            BASE,
            ALPHA,
        )
        .expect("the G side of the edited vector");
        let reshape = ReshapeProof {
            commitment,
            v_a,
            v_g,
        };
        let r = sc.proof.r.clone();
        let r_prime = sc.proof.r_prime.clone();
        sc.proof = finish(&sc.fin, &reshape, r, r_prime).expect("the OE(2) leg re-derives");
        assert_eq!(sc.report(), vec![FinError::BlocksMismatch { at }]);
    }

    #[test]
    fn lifting_p_eta_matches_the_tensor_form() {
        // Eq. (33) pairs `q_reshape,A` with `p_{η,n} ⊗ s`; the report takes the
        // cheap scalar lift, so pin it against `tensor_ring` on a small case.
        let s: Vec<Elt> = (0..2 * ALPHA).map(|i| monomial(i as u64 + 1)).collect();
        let eta = F::from(31u64);
        let lifted = lift_by_eta(&s, eta, 2);
        let powers: Vec<Elt> = tree_eval::powers_vector(eta, 2)
            .iter()
            .map(|p| tree_eval::embed::<F, D>(*p))
            .collect();
        assert_eq!(lifted, tree_eval::tensor_ring(&powers, &s));
    }

    #[test]
    fn reshape_shapes_that_cannot_be_stated_cannot_be_proved() {
        let k = key();
        let claims = claims(&k);
        let drawn = tree_eval::challenges::<F>(b"tree-fin-shapes", b"", 3);
        let (zeta, xi, eta) = (drawn[0], drawn[1], drawn[2]);

        // `TE^ω × PE^{ω+1}` is part of Π^Reshape's input type.
        let mut short = claims.clone();
        short.pop();
        assert_eq!(
            reshape_layout(SLOT, K, &short),
            Err(FinError::WrongLength {
                got: 2,
                expected: 3
            })
        );
        // A `TE` claim after a `PE` one would silently move blocks between
        // Eq. (32)'s two ζ ranges.
        let mut shuffled = claims.clone();
        shuffled.swap(0, 2);
        assert_eq!(
            reshape_layout(SLOT, K, &shuffled),
            Err(FinError::ClaimsOutOfOrder { position: 2 })
        );
        // A claim taller than the declared arity has no block that holds it.
        let mut tall = claims.clone();
        tall[0] = te_claim(&k, K + 1, 11);
        assert_eq!(
            reshape_layout(SLOT, K, &tall),
            Err(FinError::WrongLength {
                got: K + 1,
                expected: K
            })
        );
        // A point one coordinate too long is a `TE` point on a `PE` claim.
        let mut wrong_point = claims.clone();
        wrong_point[1].u.push(monomial(1));
        assert_eq!(
            reshape_layout(SLOT, K, &wrong_point),
            Err(FinError::WrongVariableCount {
                got: K + 1 + M,
                expected: K + M
            })
        );
        // Π^Reshape's remark under Step 1 (p. 43): `2^{γ+β}α2 = 2^µ' nα`.
        let narrow = Fin::setup(&[0x5fu8; 32], 2, GAMMA, BETA - 1);
        let error = reshape_report(&k, &narrow, &ReshapeProof {
            commitment: gh_commit(&narrow, &scalar_vector(narrow.bottom_len(), 0)).unwrap(),
            v_a: monomial(0),
            v_g: monomial(0),
        }, &claims, K, zeta, xi, eta);
        assert_eq!(
            error,
            vec![FinError::WrongLength {
                got: narrow.bottom_len(),
                expected: 1usize << NV
            }],
            "a key too small for the claim set must be a shape refusal, not an empty proof"
        );
        // A `PE` claim read at a `TE` point: `block_point` refuses before any
        // inner product can silently truncate.
        let mut mismatched = claims[1].clone();
        mismatched.u.pop();
        assert_eq!(
            block_point(SLOT, K, &mismatched),
            Err(FinError::WrongVariableCount {
                got: K - 1 + M,
                expected: K - 1 + M + 1
            })
        );
    }

    #[test]
    fn the_wire_and_the_witness_are_counted_separately() {
        let sc = Setup::new();
        assert_eq!(
            wire_rings(&sc.proof),
            sc.fin.rows() + 6,
            "t*_reshape + v_A + v_G + a1 + a2 + y1 + y2"
        );
        assert_eq!(
            witness_entries(&sc.proof),
            sc.fin.top_len() + sc.fin.bottom_len(),
            "the openings §5.4's BatchSC would hide"
        );
        assert!(witness_entries(&sc.proof) > wire_rings(&sc.proof) * 100);
    }

    /// `GH′`'s folding challenges `c` — one ring element per `2^γ` block of `s2`
    /// — and `η`, which p. 45 draws *after* the commitments to `ŵ, s1, z`.
    fn gh_challenges(sc: &Setup) -> Vec<Elt> {
        tree_eval::ring_challenges::<F, D>(b"gh-prime-c", b"tree-fin-gh-prime", sc.fin.nodes())
    }

    fn gh_eta() -> Elt {
        ring_point(1, 91)[0].clone()
    }

    #[test]
    fn eq_38_verifies_and_its_rows_are_named_separately() {
        let sc = Setup::new();
        let c = gh_challenges(&sc);
        let eta = gh_eta();
        let gh = gh_prime_prove(&sc.fin, &sc.proof, &c).expect("GH′ proves its own rows");
        assert_eq!(gh.w_hat.len(), sc.fin.w_len(), "ŵ is 2^γ·α1 digits");
        assert_eq!(gh.v.len(), sc.fin.rows(), "v = D·ŵ ∈ R_F^n");
        assert_eq!(gh.z.len(), sc.fin.inner_width(), "z is 2^β·α2 long");
        assert!(
            gh_prime_report(&sc.fin, &sc.proof, &gh, &c, &eta).is_empty(),
            "the honest GH′ proof was refused by {:?}",
            gh_prime_report(&sc.fin, &sc.proof, &gh, &c, &eta)
        );
        gh_prime_verify(&sc.fin, &sc.proof, &gh, &c, &eta).expect("GH′ accepts");
        assert_eq!(
            gh_prime_wire_elements(&gh),
            sc.fin.w_len() + sc.fin.rows() + sc.fin.inner_width()
        );

        // Row 1 alone: the commitment to `ŵ`, with `ŵ` itself untouched.
        let mut bad = gh.clone();
        bad.v[0] = bad.v[0].clone() + monomial(1);
        assert_eq!(
            gh_prime_report(&sc.fin, &sc.proof, &bad, &c, &eta),
            vec![FinError::GhCommitmentMismatch { at: 0 }],
            "D·ŵ ≠ v enters no other row"
        );

        // Row 3 alone: `y2` is what `b⊺·G_{b1,2^γ}·ŵ` reads, and GH′ is the only
        // reader — `a⊺·s2·b = y2` is the same claim through `s2`, and `fin_report`
        // owns that name.
        let mut claim = sc.proof.clone();
        claim.y2 = claim.y2.clone() + monomial(1);
        assert_eq!(
            gh_prime_report(&sc.fin, &claim, &gh, &c, &eta),
            vec![FinError::GhEvalRowMismatch]
        );

        // Row 4 alone: `a` enters GH′ only as `a⊺·z`.
        let mut claim = sc.proof.clone();
        claim.a[0] = claim.a[0].clone() + monomial(1);
        assert_eq!(
            gh_prime_report(&sc.fin, &claim, &gh, &c, &eta),
            vec![FinError::GhFoldRowMismatch]
        );
    }

    #[test]
    fn the_eta_entry_is_what_carries_eq_37_into_eq_38() {
        // §5.4.3's whole modification is the `+η·ẽ₁·q⊺` entry of Eq. (38)'s last
        // row, so the control is to run the same forgery with and without it: a
        // stock Greyhound row cannot see the first layer's claim at all.
        let sc = Setup::new();
        let c = gh_challenges(&sc);
        let eta = gh_eta();
        let gh = gh_prime_prove(&sc.fin, &sc.proof, &c).expect("GH′ proves its own rows");
        let mut claim = sc.proof.clone();
        claim.y1 = claim.y1.clone() + monomial(1);
        let zero = monomial(0);
        assert_eq!(
            gh_prime_report(&sc.fin, &claim, &gh, &c, &zero),
            vec![FinError::QFormMismatch],
            "η = 0 leaves Eq. (37) outside the last equation"
        );
        assert_eq!(
            gh_prime_report(&sc.fin, &claim, &gh, &c, &eta),
            vec![
                FinError::QFormMismatch,
                FinError::GhEq38LastRowMismatch { row: 0 }
            ],
            "with η ≠ 0 the same forgery breaks the last equation — at row 0 only, \
             because ẽ₁ has a single nonzero coordinate"
        );
    }

    #[test]
    fn a_noncanonical_w_hat_trips_only_the_gh_norm_gate() {
        // The pair move `each_def_23_gate_fails_alone` uses, applied to `ŵ`:
        // `(0,0) → (2,−1)` preserves `G_{b1,2^γ}·ŵ`, hence rows 3 and 4, and the
        // prover rebinds `v`, hence row 1 — so only `‖ŵ∞ < b1` can speak. This is
        // the gate that stops a prover from satisfying Eq. (38) with a witness no
        // LaBRADOR extractor could return.
        let sc = Setup::new();
        let c = gh_challenges(&sc);
        let eta = gh_eta();
        let gh = gh_prime_prove(&sc.fin, &sc.proof, &c).expect("GH′ proves its own rows");
        let zero = monomial(0);
        let at = gh
            .w_hat
            .windows(2)
            .enumerate()
            .find(|(index, pair)| index % ALPHA + 1 < ALPHA && pair[0] == zero && pair[1] == zero)
            .expect("a gadget image has adjacent zero digits inside one block")
            .0;
        let mut bad = gh.clone();
        bad.w_hat[at] = monomial(2);
        bad.w_hat[at + 1] = monomial(0) - monomial(1);
        assert_eq!(
            gadget::join::<F, D, BASE, ALPHA>(&gh.w_hat),
            gadget::join::<F, D, BASE, ALPHA>(&bad.w_hat),
            "the pair move must preserve G·ŵ"
        );
        bad.v = sc
            .fin
            .d()
            .matvec(&bad.w_hat)
            .expect("the same shape the honest commitment had");
        assert_eq!(
            gh_prime_report(&sc.fin, &sc.proof, &bad, &c, &eta),
            vec![FinError::GhWNotShort {
                got: 2,
                bound: BASE
            }]
        );
    }

    #[test]
    fn folded_norm_bound_tracks_the_challenges_and_bites() {
        let sc = Setup::new();
        let eta = gh_eta();
        // Ternary challenges, so the bound is a real number rather than something
        // no `z` could reach: `d·(Σ_j‖c_j‖∞)·(b2−1) = 8·8·1`.
        let c: Vec<Elt> = (0..sc.fin.nodes())
            .map(|j| {
                if j % 2 == 0 {
                    monomial(1)
                } else {
                    monomial(0) - monomial(1)
                }
            })
            .collect();
        let bound = folded_norm_bound(&c, BASE);
        assert_eq!(bound, (D * sc.fin.nodes() * (BASE as usize - 1)) as u64);
        assert_eq!(bound, 64);
        // And the bound is not floored at one: all-zero challenges genuinely give
        // `0`, so a gate that rounded up would accept a `z` of norm 1 the fold
        // cannot produce.
        let zeros = vec![monomial(0); sc.fin.nodes()];
        assert_eq!(folded_norm_bound(&zeros, BASE), 0);
        let gh = gh_prime_prove(&sc.fin, &sc.proof, &c).expect("ternary challenges fold");
        assert!(
            max_norm(&gh.z) <= bound,
            "the honest fold is inside the bound the negacyclic convolution gives: \
             {} > {bound}",
            max_norm(&gh.z)
        );
        // A `z` longer than the bound is refused *as a length*: rows 4 and 5 read
        // `z` too, so they co-fail, and the report says so in that order.
        let mut bad = gh.clone();
        bad.z[0] = monomial(bound + 1);
        assert_eq!(
            gh_prime_report(&sc.fin, &sc.proof, &bad, &c, &eta),
            vec![
                FinError::GhZNotShort {
                    got: bound + 1,
                    bound
                },
                FinError::GhFoldRowMismatch,
                FinError::GhEq38LastRowMismatch { row: 0 },
            ]
        );
    }

    #[test]
    fn finish_accounting_decomposes_fig_6_s_p3_row() {
        // Fig. 5 (p. 45)'s P3 column: `log₂q = 32`, `d = 64`, `e = 8`, `n = 32`,
        // `b = 2`, `k = 7`; Fig. 6 (p. 47) gives `ω = 6` cycles, a `single cycle
        // total` of 43.8 KB, a `finish` row of ∼72 KB, and Fig. 5's total of
        // 335 KB.
        let p3 = FinishAccounting::new(4, 8, 64, 32, 32, 7, 6, 2);
        assert_eq!(
            p3.rounds, 22,
            "µ′+m = (⌈log₂(2ω+1)⌉+k+1)+log₂(nα) = (4+7+1)+10"
        );
        assert_eq!(p3.norm_sumcheck, 5 * 22 * 8 * 4, "SC(2b)");
        assert_eq!(p3.shift_sc, 3 * 22 * 8 * 4, "ShiftSC(2,1)");
        assert_eq!(p3.batch_sc, 3 * 22 * 8 * 4, "BatchSC(2,1)");
        assert_eq!(p3.packed_claims, 2 * 4 * 64 * 8, "2 R_K");
        assert_eq!(p3.eval_claims, 2 * 4 * 64, "2 R_F");
        assert_eq!(p3.commitment, 32 * 4 * 64, "1 commitment");
        assert_eq!(p3.greyhound_input, (1usize << 12) * 1024 * 64);
        // What this compilation sends is a fifth of the printed row, and the
        // unlanded `Greyhound(2^{µ+k+1}nαd)` term is the rest — bigger than every
        // component above. That difference is the size of the hole, stated as one.
        assert_eq!(p3.implemented_bytes(), 20_544);
        let allowance = p3.greyhound_allowance(72);
        assert_eq!(allowance, 72 * 1024 - 20_544);
        assert!(
            allowance > p3.implemented_bytes(),
            "the hole should dominate: {allowance} vs {}",
            p3.implemented_bytes()
        );
        // The ∼72 KB row is *inside* Fig. 5's 335 KB total (43.8·6 + 72 = 334.8),
        // which is what makes the allowance above a statement about Greyhound
        // rather than about a proof the paper never counted.
        assert_eq!(
            438 * 6 + 720,
            3_348,
            "Fig. 6's own arithmetic, in tenths of KB"
        );
    }

    #[test]
    #[should_panic(expected = "not a power of two")]
    fn finish_accounting_refuses_a_shape_with_no_m() {
        // `m := log₂(nα)` indexes the sum-check's variables; without it the row
        // cannot be stated, and a silent rounding would print a confident number.
        let _ = FinishAccounting::new(4, 8, 64, 3, 32, 7, 6, 2);
    }
}
