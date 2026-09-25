//! Maltese — Cheng–Nguyen–Tyagi, *Maltese: Succinct Polynomial Commitment from
//! Lattices*, ASIACRYPT 2026, eprint 2026/2067: a **multilinear** polynomial
//! commitment whose witness is an Ajtai *hash tree* rather than a Merkle tree,
//! opened by a folding cycle that spends norm and then buys it back.
//!
//! This file is a **scheme assembly**: it contains no cryptographic logic. Every
//! step is a call into a `src` capability —
//!
//! | paper step | capability |
//! |---|---|
//! | Def. 18 gadget `G`, `G⁻¹`, `g_b^⊺` | [`zk::pcs::gadget`] |
//! | Def. 19 `TCom` Setup / Commit / Open / Open_F | [`pcs::tree_commit`] |
//! | §5 relations `PE`/`TE`, Eq. (7)–(10) + Lemma 14, Protocol 3 Π^PE_NC, Protocol 5 Π^Dec | [`pcs::tree_eval`] |
//! | §2.2.2 + Protocol 4 Π^Fold, Def. 11/14 challenge sets, Thm. 2/3/4 | [`pcs::tree_fold`] |
//! | §5.4 `Π^Fin` = `GH′ ∘ Π^PE_NC,fin ∘ Π^Reshape`, Def. 23, Prot. 6, Eq. (32)–(37) | [`pcs::tree_fin`] |
//! | Def. 9's degree-`d` sum-check | [`zk::sumcheck::circuit`] (`Δ = 2b` in Π^PE_NC, `Δ = 2` in Π^Fold) |
//!
//! and the trace below is ordered by the paper's own step numbering.
//!
//! # The cycle, as the paper states it
//!
//! Lemma 13 (p. 26) is the shape of one round, and Fig. 2 (p. 8) the shape of the
//! scheme:
//!
//! ```text
//! B := 2^k·T·b     h := log_b B
//! Π^Dec ∘ Π^Fold ∘ Π^PE_NC : PE(1,ℓ,b) → TE(1,k,b) ⊕ PE(1, ℓ−k+1+log h, b) ⊕ PE(1,k,b)
//! ```
//!
//! so the recursion continues on the *bottom* claim, which leaves the tree at
//! height `ℓ − k + 1 + ⌈log₂ h⌉` ([`CycleShape::next_height`]), and the cycle only
//! shrinks the claim while `k > log h + 1` (§2.2, p. 8).
//!
//! The three reductions do **not** agree about the length of the evaluation
//! point, and that is the one thing easy to get silently wrong:
//!
//! * `PE(L,ℓ,b⃗)` (§5 "Relations", p. 25) carries `u ∈ R_F^{ℓ+m}` and claims on the
//!   **bottom layer alone**: `s̃_{ℓ,l}(u) = v_l`.
//! * `TE(L,ℓ,b⃗)` carries `u ∈ R_F^{ℓ+1+m}` and claims on the **concatenation**
//!   `s_l := 0^{2nα} ‖ s_{1,l} ‖ … ‖ s_{ℓ,l} ∈ R_F^{2^{ℓ+1}nα}`.
//!
//! [`tree_eval::concatenated_point`] is the one-coordinate bridge between them,
//! and it is *checked* rather than assumed, because the two readings of the claim
//! agree only for the correct selector bit: layer `ℓ` starts at
//! `2nα + Σ_{i<ℓ}2ⁱnα = 2^ℓ nα`, exactly the concatenation's midpoint, so
//! `s̃_ℓ(u) = s̃(1‖u)` — which is Protocol 3's Eq. (10) (p. 27),
//! `v_l = Σ_X êq(X₁,1)·êq(u, X_{[2:]})·s̃_l(X)`, read as a point instead of as a
//! sum. Π^Fold's `Input` is a `TE` claim and Π^Dec's `Output` is a `PE` claim, so
//! the assembly crosses that bridge once per cycle, and the point the cycle
//! carries forward is Protocol 5 Step 3's `r_{[:ℓ̃+m]}` — nothing "resizes" a
//! point, because no such step exists in the paper.
//!
//! # What is *not* here, and why
//!
//! * **No TrapGen, no SamplePre, no trusted setup.** Def. 19's `Setup` samples
//!   `A ←$ R^{n×2nα}` and returns `pp ← {A}`; the paper's 90 pages contain no
//!   trapdoor sampler, and the string "trapdoor" appears only in reference
//!   titles. [`TreeKey::setup`] is a seed-expanded uniform matrix.
//! * **No authentication path.** `TCom.Open` reveals the *whole layer vector*
//!   `(s_i)_{i∈[ℓ]}`, never sibling digests, which is what lets Π^Fold linearly
//!   combine layers. The opening is large; the *proof* is small because the
//!   folding cycle only ever sends claims and commitments.
//! * **No NTT.** P3 needs `q = 2³²−99 ≡ 5 (mod 8)`, whose 2-adicity is 2, so `X⁶⁴+1`
//!   does not split into linear factors and `RingMatrixKey`'s schoolbook path is
//!   the only one available.
//! * **No `BatchSC`/`ShiftSC` rounds** (§4, Protocols 1–2): those need the
//!   degree-`e` extension field `K` (`R_F ≅ K^{d/e}`, `R_K ≅ R_F^e`), which this
//!   crate does not model as a `Ring`. So `K = F` here: each reduction's
//!   sum-check runs for real over `F` — as [`zk::sumcheck::circuit`]'s degree-`Δ`
//!   protocol, because Def. 9's `SC(v, ℓ, G)` is *not* the multilinear table
//!   sum-check and the two end at different claims off the hypercube — and Π^Dec's
//!   claims are checked as the verifier equations they are (Eq. (25), (26), (28),
//!   (30), (31)) rather than as rounds. See each function's doc for which
//!   equation it enforces.
//! * **`Π^Fin` is landed, and it is not yet succinct.** §5.4's finisher
//!   (`zk::pcs::tree_fin`) recommits the `TE(1,k,b)^ω × PE(1,k,b)^{ω+1}`
//!   side-claims into Def. 23's two-layer Greyhound commitment, checks Eq. (32)–(36)
//!   and Prot. 6 Step 2(f)'s prefix claim, continues through Π^PE_NC,fin's two
//!   layer evaluations, and runs `GH′`'s added row `q⊺·s1 = y1` (§5.4.3, Eq. (37)).
//!   The cycle's set-aside claims therefore now end up somewhere: the `TE`
//!   value `v_top` is bound by Eq. (35) *through that fresh commitment*, which is
//!   the paper's route. What is *not* landed is Greyhound's three-move core and
//!   LaBRADOR (the crate's `pcs::greyhound` is welded to its own `Z1` instance, so
//!   a `q = 2³²−99`, `d = 64` ring cannot call it) and §4's `BatchSC`/`ShiftSC`, so
//!   Π^Reshape's claims are enforced as verifier equations on the openings, exactly
//!   as Π^Dec's already are here. **Which check is succinct, stated plainly:** the
//!   paper's `Π^Fin` is the succinct branch (Lem. 35 gives `O(ω log N)` verifier
//!   time and `O(log(N·ω))` proof size, Cor. 4 `O(polylog)` for `GH′`), while
//!   `forward.top_tree_claim` — §2.2 p. 9's "open the tree and check the
//!   evaluation" branch — is *never* succinct in any compilation. Both are kept:
//!   the finisher binds the claim the paper's way, the direct opening stays as the
//!   cross-check that says so if the two ever disagree.
//!   The residual gap is the reason the cycle still runs the direct branch's
//!   checks: without the LaBRADOR core, `Π^Fin`'s `GH′` step verifies
//!   `GHPrincipal′(b1,b2)`'s rows rather than proving them.
//!   Historical note, now superseded: on 2026-09-24 forging `v_top` produced an
//!   *empty* failing set, which is what made `forward.top_tree_claim` necessary;
//!   that forgery is now refused by `fin.eval_te` as well.
//!
//! * **A smaller instance than P3.** P3 is `log q = 32, d = 64, e = 8, n = 32,
//!   b = 2, k = 7, C = C_sp(32,8), ω = 6` for `N = 2³⁰` (Fig. 5, p. 46). This
//!   instance keeps `log q = 32`, `d = 64`, `b = 2`, `α = 32`, `k = 7` and the
//!   same challenge set — the parameters that decide the protocol's *shape* — and
//!   shrinks `n` and `ℓ` so the cycle runs in seconds. §6.2's accounting for real
//!   P3 is printed alongside, from Fig. 6's own numbers (p. 47).
//!
//! Run with: `cargo run --release -p lattice-zk --example maltese`. The shape above
//! is why this one example needs `--release`: `b = 2` only shrinks the cycle for
//! `k ≥ 7` (here `B = 2^k·T·b = 12 288`, `⌈log₂ B⌉ = 14 < 2k`), so `ℓ = 8` is
//! forced, so every verifier pass touches a `2^{ℓ+1+m} = 2^15`-entry `êq` table
//! `2^k = 128` times over. Measured 2026-09-24: cycle assembly 10.0 s release vs
//! 84.3 s debug, and the tamper battery scales with it (≈2 min vs ≈40 min).

use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::Ring;
use algebra::ring::PolynomialQuotientRing;
use std::collections::BTreeSet;
use std::time::Instant;
use zk::pcs::tree_commit::{self, TreeKey, TreeOpening};
use zk::pcs::tree_eval::{self, DecompositionProof, EvalError, NormCheckProof};
use zk::pcs::tree_fin::{self, ClaimKind, SideClaim};
use zk::pcs::tree_fold::{self, ChallengeSet, CycleShape, FoldError, FoldProof, TreeClaim};

/// The finisher's key type at this instance's shape parameters.
type FinKey = tree_fin::FinKey<F, D, BASE, ALPHA>;

/// The scalar field: `q = 2³² − 99`, prime and `≡ 5 (mod 8)` — P3's `log q = 32`.
type F = algebra::ring::zq::Zq<4294967197>;

/// P3's cyclotomic degree, `R_F = F[X]/(X⁶⁴ + 1)`.
const D: usize = 64;

/// P3's gadget base `b = 2`, so the tree's digits are binary.
const BASE: u64 = 2;

/// `α = ⌈log_b q⌉ = 32` — Def. 18's digit count (p. 20). The inequality that
/// makes the split exact is `b^α ≥ q`, not `> q`.
const ALPHA: usize = 32;

/// The lattice dimension `n`. P3 uses `n = 32`; a full P3 tree over `N = 2³⁰`
/// scalars is out of reach for a debug-mode example, so this is one of the two
/// shrunk shape parameters.
const N: usize = 2;

/// P3's folding arity: one round opens `k = 7` layers and folds `2⁷` subtrees.
const K: usize = 7;

/// Initial tree height `ℓ`. With `ℓ = 8`, `k = 7` and `h = 14` (padded to `16`)
/// one cycle lands the tree at height `ℓ − k + 1 + ⌈log₂ h⌉ = 6 ≤ k`, so the
/// cycle runs exactly once and the base case is discharged directly.
const HEIGHT: usize = 8;

/// `m := log(nα)` — §5 "Relations" (p. 25) adds exactly this many coordinates to
/// a layer index. `nα = 2·32 = 64`, so `m = 6`.
const M: usize = 6;

/// Def. 23's `GHSetup` draws `B1, B2` independently of `TCom`'s `A` (p. 39), so
/// the finisher's key gets its own seed.
const FIN_SEED: [u8; 32] = [0x27u8; 32];

/// Variables of the norm-check sum-check: Eq. (8) is over `{0,1}^{ℓ+1+m}`.
const NV_NORM: usize = HEIGHT + 1 + M;

/// Variables of the folding sum-check: Eq. (15) is over `{0,1}^{ℓ−k+1+m}`.
const NV_FOLD: usize = HEIGHT - K + 1 + M;

/// Round-message width of Protocol 3's sum-check: Def. 9's `SC` runs on a
/// polynomial of per-variable degree `Δ`, and Step 1(c)'s `êq(X,r)·Q_N(X)` has
/// `Δ = 1 + (2b − 1) = 2b` (Eq. 7), so the message carries `2b + 1` elements.
/// The crate's multilinear sum-check (`Δ = 1`) cannot express this claim at all:
/// see `zk::sumcheck::circuit`.
const NC_NORM: usize = (2 * BASE + 1) as usize;

/// The ring element with constant coefficient `c`.
fn monomial(c: u64) -> PolyRing<F, D> {
    let mut coefficients = vec![F::ZERO; D];
    coefficients[0] = F::from(c);
    PolyRing::from_coefficients(coefficients)
}

/// The committed multilinear polynomial: `f ∈ R_F^{2^ℓ·n}` (Def. 19), i.e.
/// `2^ℓ·n·d` field coefficients — the `N = 2³⁰`-scalar shape of §6.2 at the scale
/// a debug run can afford.
fn message() -> Vec<PolyRing<F, D>> {
    (0..(1usize << HEIGHT) * N)
        .map(|i| {
            PolyRing::from_coefficients(
                (0..D)
                    .map(|j| F::from(((i * 1_000_003 + j * 40_503 + 7) % 97) as u64))
                    .collect(),
            )
        })
        .collect()
}

/// A ring point in `R_F^{coordinates}` — an evaluation point of a `TE`/`PE` claim.
fn point(coordinates: usize, tag: u64) -> Vec<PolyRing<F, D>> {
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

/// P3's challenge set, `C_sp(32,8)` (Def. 14, p. 18; Fig. 5, p. 46).
fn p3_set() -> ChallengeSet {
    ChallengeSet::Sparse { tau1: 32, tau2: 8 }
}

type Key = TreeKey<F, D, BASE, ALPHA>;
type Elt = PolyRing<F, D>;
type Proof = FoldProof<F, D, NV_FOLD, { tree_fold::FOLD_NC }>;

/// Π^Fold's `x̃_top` (§5.2.2 p. 34), i.e. the `TE(1,ℓ̃,b)` side-claim Π^Fin later
/// recommits: the round's own commitment, the `k` top layers, and Eq. (12)'s
/// suffix point.
fn te_side_claim(
    t: &[Elt],
    layers: &[Vec<Elt>],
    u: &[Elt],
    v: &Elt,
) -> SideClaim<F, D> {
    SideClaim {
        kind: ClaimKind::Te,
        opening: TreeOpening {
            root: t.to_vec(),
            layers: layers.to_vec(),
        },
        u: u.to_vec(),
        v: v.clone(),
    }
}

/// A `PE(1,ℓ̃,b)` side-claim: Π^Fold's `x̃_subs` (on `t_subs`) or Π^Dec's base case.
///
/// Protocol 4's Step 4(e) hands the paper a `PE` claim *reduced* to `BatchSC`'s
/// point; `BatchSC` is not compiled in this crate (`K = F`, see the header), so
/// the claim is taken at a transcript point instead. That is not a weakening: the
/// value is still a claim on the very `t_subs` Eq. (16)/(17) already bound, and
/// Π^Fin's Eq. (36) re-reads it against the fresh two-layer commitment, which is
/// the binding that matters here.
fn pe_side_claim(
    t: &[Elt],
    layers: &[Vec<Elt>],
    u: &[Elt],
    v: &Elt,
) -> SideClaim<F, D> {
    SideClaim {
        kind: ClaimKind::Pe,
        opening: TreeOpening {
            root: t.to_vec(),
            layers: layers.to_vec(),
        },
        u: u.to_vec(),
        v: v.clone(),
    }
}

/// §5.4's transcript material for a whole set-aside list: the binding, the
/// reshaping challenges `ζ, ξ, η` (Prot. 6 Step 2(a)i), and the two points `r`
/// (Prot. 6 Step 3's `r_{(µ'+m)}`) and `r′` (Prot. 7 Step 3's shift point).
#[derive(Clone)]
struct Finishing {
    key: FinKey,
    zeta: F,
    xi: F,
    eta: F,
    r: Vec<Elt>,
    r_prime: Vec<Elt>,
}

impl Finishing {
    fn new(tree: &Key, seed: &[u8; 32], claims: &[SideClaim<F, D>]) -> Self {
        let slot = tree.slot_len();
        // Π^Reshape's blocks are `2^{k+1}nα` wide and there are
        // `2^⌈log(2ω+1)⌉` of them, so Def. 23 needs `2^{γ+β}α2 = 2^µ' nα`. The
        // split is Greyhound's own: `γ ≈ β`, i.e. the √N choice.
        let omega = claims
            .iter()
            .filter(|claim| claim.kind == ClaimKind::Te)
            .count();
        let total = (2 * omega + 1)
            .next_power_of_two()
            .checked_mul(1usize << (K + 1))
            .expect("block count times block width")
            * slot;
        let layers = (total / ALPHA).trailing_zeros() as usize;
        let key = FinKey::setup(seed, tree.rows(), layers / 2, layers - layers / 2);
        let openings: Vec<&TreeOpening<F, D>> = claims
            .iter()
            .map(|claim| &claim.opening)
            .collect();
        let values: Vec<Elt> = claims.iter().map(|claim| claim.v.clone()).collect();
        let points: Vec<&[Elt]> = claims.iter().map(|claim| claim.u.as_slice()).collect();
        let binding = tree_eval::statement_bytes(tree.seed(), &openings, &values, &points);
        let drawn = tree_eval::challenges::<F>(b"maltese-fin", &binding, 3);
        let variables = key.bottom_variables();
        Self {
            key,
            zeta: drawn[0],
            xi: drawn[1],
            eta: drawn[2],
            r: tree_eval::ring_challenges::<F, D>(b"maltese-fin-r", &binding, variables),
            r_prime: tree_eval::ring_challenges::<F, D>(
                b"maltese-fin-r-prime",
                &binding,
                variables,
            ),
        }
    }

    fn prove(&self, tree: &Key, claims: &[SideClaim<F, D>]) -> tree_fin::FinProof<F, D> {
        tree_fin::fin_prove(
            tree,
            &self.key,
            claims,
            K,
            self.zeta,
            self.xi,
            self.eta,
            self.r.clone(),
            self.r_prime.clone(),
        )
        .expect("Π^Fin prover")
    }

    fn report(
        &self,
        tree: &Key,
        claims: &[SideClaim<F, D>],
        proof: &tree_fin::FinProof<F, D>,
    ) -> Vec<tree_fin::FinError> {
        tree_fin::fin_report(
            tree,
            &self.key,
            proof,
            claims,
            K,
            self.zeta,
            self.xi,
            self.eta,
        )
    }
}

fn main() {
    // ── the instance, and the shape facts it has to satisfy ─────────────────
    assert_eq!(
        M,
        (N * ALPHA).trailing_zeros() as usize,
        "m = log₂(nα), and nα must be a power of two"
    );
    assert_eq!(tree_commit::digits_for(BASE, F::MODULUS), Some(ALPHA));
    assert_eq!(F::MODULUS % 8, 5, "P3 needs the non-NTT congruence");
    assert_eq!((F::MODULUS - 1).trailing_zeros(), 2, "…2-adicity 2…");
    assert!(!PolyRing::<F, D>::is_ntt_available(), "…so no NTT exists");

    // ── §3.5 Def. 19 `Setup(1^λ) → pp = {A}` ────────────────────────────────
    let seed = [0x4du8; 32];
    let key = Key::setup(&seed, N);
    println!(
        "P3-shaped instance: log q = 32 (q = {}), d = {D}, b = {BASE}, α = {ALPHA}, n = {N}, ℓ = {HEIGHT}, k = {K}, m = {M}",
        F::MODULUS
    );
    println!(
        "  A ∈ R^(n × 2nα) = R^({} × {}) — uniform from the public seed, no trapdoor",
        key.rows(),
        2 * key.rows() * ALPHA
    );

    // ── Def. 19 `Commit(A, f) → (t, (s_i)_{i∈[ℓ]})` ─────────────────────────
    let f = message();
    let opening = key.commit(&f).expect("a legal leaf length");
    println!(
        "  commit: t ∈ R^{}/{}, layers {:?} (bottom = G⁻¹(f), ‖·‖∞ = {} < b = {BASE})",
        opening.root.len(),
        key.rows(),
        opening.layers.iter().map(|l| l.len()).collect::<Vec<_>>(),
        tree_commit::max_norm(&opening.layers[HEIGHT - 1])
    );
    key.open_with_message(&opening, key.base(), &f)
        .expect("Lemma 10: perfect completeness for b ≥ b");
    println!("  Open + Open_F accept: t = A·s₁, G·sᵢ = (I⊗A)·s_{{i+1}}, ‖sᵢ‖∞ < b");

    // ── §5 `PE(1, ℓ, b)`: the claim `ṽ(u) = v` on the leaf layer ────────────
    let slot = key.slot_len();
    let u = point(HEIGHT + M, 0xA5);
    let s = tree_eval::concatenated(slot, &opening.layers);
    let v = tree_eval::layer_value(&s, slot, HEIGHT, &u).expect("leaf MLE");
    tree_eval::layer_claim(&s, slot, HEIGHT, &u, &v).expect("Eq. 10");
    println!(
        "  claim: ṽ = s̃_ℓ(u), u ∈ R^{} = ℓ+m coordinates, i.e. PE(1,{HEIGHT},b)",
        u.len()
    );

    // ── §2.2 the folding cycle Π^Dec ∘ Π^Fold ∘ Π^PE_NC ─────────────────────
    let set = p3_set();
    let expansion = set.expansion_factor(D);
    let shape = CycleShape::new(K, expansion, BASE);
    println!(
        "Π^Fold: C = C_sp(32,8), T_C ≤ {expansion} (Thm. 4), B = 2^k·T·b = {}, h = log_b B = {} (padded to {}) → each cycle maps ℓ ↦ {}",
        shape.bound,
        shape.planes,
        shape.padded_planes,
        shape.next_height(HEIGHT)
    );
    println!(
        "  Thm. 2 at e = 8 decides invertibility deterministically: {} → Fig. 5's P3 column says \"no (Thm. 2)\" (no heuristic)",
        set.deterministically_invertible(F::MODULUS, D, 8)
    );
    assert!(shape.progresses(), "P3's k = 7 is the smallest progressing k");
    println!(
        "  |C_sp(32,8)| = 2^{} log₂, matching Fig. 5's P1/P3/P7 row",
        set.log2_size(D)
    );

    let mut claim = TreeClaim {
        t: opening.root.clone(),
        u,
        v,
    };
    let mut layers = opening.layers.clone();
    let mut cycles = 0usize;
    let mut proof_bytes = 0usize;
    // §5.4 p. 39: what the main cycle leaves behind, claim by claim.
    let mut side_claims: Vec<SideClaim<F, D>> = Vec::new();
    let started = Instant::now();

    while layers.len() > K {
        let height = layers.len();
        let s = tree_eval::concatenated(slot, &layers);
        assert_eq!(s.len(), (2usize << height) * slot, "s ∈ R^(2^(ℓ+1)·nα)");
        assert_eq!(height - K + 1 + M, NV_FOLD, "Eq. (15)'s variable count");
        // Protocol 3's Input is a PE claim; Protocol 4's Input is a TE claim: one
        // coordinate apart, and Eq. (10)'s selector bit is the bridge.
        let te_point =
            tree_eval::concatenated_point(&claim.u, &s, slot).expect("PE point → TE point");
        assert_eq!(te_point.len(), height + 1 + M);
        let binding = tree_eval::statement_bytes(key.seed(), &[], &[], &[&te_point, &layers[0]]);

        // Protocol 3 (Π^PE_NC): norm-check the concatenated openings, then pack
        // the d field claims into one ring claim (Lemma 14).
        let drawn = tree_eval::challenges::<F>(b"maltese-norm", &binding, 1 + NV_NORM);
        let xi = drawn[0];
        let r = drawn[1..].to_vec();
        let norm = tree_eval::norm_check_prove::<F, D, NV_NORM, NC_NORM>(
            &s, &r, xi, BASE, &binding, slot, &claim.u, &claim.v,
        )
        .expect("Protocol 3 prover");
        tree_eval::norm_check_verify::<F, D, NV_NORM, NC_NORM>(
            &norm, &s, &r, xi, BASE, &binding, slot, &claim.u, &claim.v,
        )
        .expect("Protocol 3 verifier");
        println!(
          "cycle {cycles} ℓ = {height}: Π^PE_NC — SC(0, ℓ+1+m, êq(X,r)·Q_N) over {NV_NORM} variables, deg N_b = {}, Lemma 14 packing; a = s̃(r_N) has ‖a‖∞ = {}",
          2 * BASE - 1,
          tree_commit::max_norm(core::slice::from_ref(&norm.packed))
        );
        proof_bytes += NC_NORM * norm.sumcheck.rounds.len() * 4 * D
            + norm.sumcheck.point.len() * 4 * D
            + D * 4;

        // Protocol 4 (Π^Fold): open k layers, fold 2^k subtrees, pay norm.
        let challenges: Vec<Elt> = (0..1usize << K)
            .map(|j| set.sample(&seed, j as u64))
            .collect();
        let te_claim = TreeClaim {
            t: claim.t.clone(),
            u: te_point.clone(),
            v: claim.v.clone(),
        };
        let (fold, top, bottom) = tree_fold::fold_prove::<F, D, BASE, ALPHA, NV_FOLD>(
            &key, &te_claim, &layers, K, &challenges, &shape, &binding,
        )
        .expect("Protocol 4 prover");
        let rho = tree_eval::challenges::<F>(b"maltese-fold-batch", &binding, 1)[0];
        tree_fold::fold_verify::<F, D, BASE, ALPHA, NV_FOLD>(
            &key, &te_claim, &layers, &fold, K, &challenges, &binding, &shape, rho,
        )
        .expect("Protocol 4 verifier: Eq. 11/12/14/15/16/17/18/19 all hold");
        let folded_norm = fold
            .folded_layers
            .iter()
            .map(|layer| tree_commit::max_norm(layer))
            .max()
            .unwrap_or(0);
        println!(
            "  Π^Fold — t* = Σⱼ cⱼ·G·s_(k,j), r ∈ R^{} (Eq. 15's point), ‖s*‖∞ = {folded_norm} ≤ B = {}; side-claims TE(1,{K},b) and PE(1,{K},b) set aside for Π^Fin",
            fold.sumcheck.point.len(),
            shape.bound
        );
        assert_eq!(top.u.len(), K + 1 + M, "x̃_top is a TE(1,k,b) claim");
        proof_bytes += tree_fold::wire_size(&fold) * D * 4;
        // §5.2.2 Step 5: the two claims this round sets aside, in the order
        // Prot. 6 expects them — all `TE` blocks first, then the `PE` ones.
        side_claims.push(te_side_claim(&top.t, &layers[..K], &top.u, &top.v));
        let subs_point =
            tree_eval::ring_challenges::<F, D>(b"maltese-subs-claim", &binding, K + M);
        let subs_s = tree_eval::concatenated(slot, &fold.subs.layers);
        let subs_value = tree_eval::layer_value(&subs_s, slot, K, &subs_point)
            .expect("t_subs opens a k-layer tree, so its layer point has k+m coords");
        side_claims.push(pe_side_claim(
            &fold.subs.root,
            &fold.subs.layers,
            &subs_point,
            &subs_value,
        ));

        // Protocol 5 (Π^Dec): reset the norm by re-committing the digit planes in
        // a fresh low-norm tree, checked through Eq. (25)/(30)/(31).
        let planes = shape.padded_planes;
        let new_height = shape.next_height(height);
        let bottom_opening = TreeOpening {
            root: bottom.t.clone(),
            layers: fold.folded_layers.clone(),
        };
        let dec_drawn = tree_eval::challenges::<F>(b"maltese-dec", &binding, 2);
        let (xi_dec, eta_dec) = (dec_drawn[0], dec_drawn[1]);
        let r_new =
            tree_eval::ring_challenges::<F, D>(b"maltese-dec-point", &binding, new_height + M);
        let decomposition = tree_eval::decompose_prove::<F, D, BASE, ALPHA>(
            &key, &bottom_opening, planes, xi_dec, eta_dec,
        )
        .expect("Protocol 5 prover");
        let (next_point, next_value) = tree_eval::decompose_verify::<F, D, BASE, ALPHA>(
            &key,
            &decomposition,
            &bottom.u,
            &bottom.v,
            &bottom_opening,
            planes,
            xi_dec,
            eta_dec,
            &r_new,
        )
        .expect("Protocol 5 verifier: Eq. 21/25/26/28/30/31 all hold");
        println!(
            "  Π^Dec — s = Σ_(j∈[{planes}]) b^(j−1)·s_(dec,j) re-committed as a height-{new_height} tree (ℓ̃ = ℓ−k+1+log₂ h), ‖s_dec‖∞ = {} < b; forwarded PE point r_{{[:ℓ̃+m]}} has {} coords",
            decomposition
                .planes
                .iter()
                .map(|plane| tree_commit::max_norm(plane))
                .max()
                .unwrap_or(0),
            next_point.len()
        );
        proof_bytes += (decomposition.commitment.root.len() + 2 * D) * 4;

        layers = decomposition.commitment.layers.clone();
        claim = TreeClaim {
            t: decomposition.commitment.root.clone(),
            u: next_point,
            v: next_value,
        };
        cycles += 1;
        assert_eq!(
            layers.len(),
            new_height,
            "Lemma 13: the cycle maps ℓ → ℓ − k + 1 + log h"
        );
    }

    // ── §2.2 p. 9 / §5.4: the base case, checked directly ───────────────────
    let base = TreeOpening {
        root: claim.t.clone(),
        layers: layers.clone(),
    };
    key.open(&base, BASE).expect("the base tree opens");
    let height = layers.len();
    let s = tree_eval::concatenated(slot, &layers);
    assert_eq!(
        claim.u.len(),
        height + M,
        "Π^Dec forwarded a PE point: ℓ+m coordinates"
    );
    // What is checked here is the claim the cycle *carried*, not one re-read off
    // the witness — re-reading it would make this assertion vacuous.
    tree_eval::layer_claim(&s, slot, height, &claim.u, &claim.v)
        .expect("the base evaluation claim holds");
    println!(
        "base case after {cycles} cycle(s): height {height} ≤ k, opened directly ({} layer elements, ‖·‖∞ ≤ {BASE})",
        layers.iter().map(|l| l.len()).sum::<usize>()
    );
    println!("  honest cycle verified end to end in {:?} (debug)", started.elapsed());

    // ── §5.4 `Π^Fin = GH′ ∘ Π^PE_NC,fin ∘ Π^Reshape` ────────────────────────
    // The base case is the `(ω+1)`st PE claim, so the cycle's whole set-aside list
    // is now Π^Reshape's input (Prot. 6, p. 42).
    side_claims.push(pe_side_claim(&claim.t, &layers, &claim.u, &claim.v));
    let finishing = Finishing::new(&key, &FIN_SEED, &side_claims);
    let finish = finishing.prove(&key, &side_claims);
    tree_fin::fin_verify(
        &key,
        &finishing.key,
        &finish,
        &side_claims,
        K,
        finishing.zeta,
        finishing.xi,
        finishing.eta,
    )
    .expect("Π^Fin verifier: Def. 23, Eq. (32)–(36) and GH′'s rows all hold");
    println!(
        "Π^Fin: {} side-claims (TE(1,{K},b)^{cycles} × PE(1,{K},b)^{}) recommitted into one Def. 23 pair — t* ∈ R^{},{}, |s1| = {}, |s_reshape| = {} (µ' = {}, γ = {}, β = {}); Eq. 35 binds x̃_top's value, Eq. 36 the two PE claims, GH′'s q⊺s1 = y1 the layer-1 claim",
        side_claims.len(),
        cycles + 1,
        finishing.key.rows(),
        finishing.key.rows(),
        finishing.key.top_len(),
        finishing.key.bottom_len(),
        (finishing.key.bottom_len() / slot).trailing_zeros() as usize,
        finishing.key.gamma(),
        finishing.key.beta(),
    );
    let finish_rings = tree_fin::wire_rings(&finish);
    let finish_bytes = finish_rings * D * 4;
    proof_bytes += finish_bytes;
    println!(
        "  finish wire: {finish_rings} ring elements = {finish_bytes} bytes; §5.4's BatchSC would hide the {} entries of s1‖s_reshape this compilation reads",
        tree_fin::witness_entries(&finish)
    );

    // ── §6.1/§6.2: the real P3 numbers (Fig. 5 p. 46, Fig. 6 p. 47) ─────────
    println!(
        "this run's proof: {proof_bytes} bytes for N = {} field coefficients",
        (1usize << HEIGHT) * N * D
    );
    println!(
        "P3 (Fig. 6): one cycle 43.8 KB × ω = 6, plus a ≈72 KB finish = {} KB ≈ the paper's 335 KB at N = 2^30",
        6 * 43 + 72
    );
    let p3_finish_kb = (32 * 64 * 4 + 6 * 64 * 4) / 1024;
    println!(
        "  of that finish row, the landed slice is {} KB at P3's n = 32, d = 64, log q = 32 (the one commitment + 6 ring claims just measured); the other ≈{} KB is Fig. 6's SC(2b)+ShiftSC(2,1)+2 RK + BatchSC(2,1)+2 RF messages and Greyhound(2^µ+k+1 nαd), i.e. §5.4.3's LaBRADOR core, still open",
        p3_finish_kb,
        72 - p3_finish_kb
    );
    println!(
        "  (MSIS targets: Lemma 11 wants b' ≥ 2B = {} for the folded claim's binding; Lemma 12's relaxed binding wants 2·T_(C−C,k)·B = {})",
        tree_commit::binding_norm(shape.bound),
        tree_commit::relaxed_binding_norm(2 * expansion, shape.bound)
    );

    // ── every tampered component is refused by its own named check ──────────
    let checks = tamper(&key, &f, &seed);
    println!(
        "every tamper refused, and all {} named checks were tripped by some one of them",
        checks.len()
    );
}

/// One assembled cycle, with every message and challenge the checks consume.
///
/// Cloning is the tamper mechanism: a case mutates exactly one component and the
/// whole battery re-runs against it.
#[derive(Clone)]
struct Scenario {
    key: Key,
    f: Vec<Elt>,
    slot: usize,
    k: usize,
    planes: usize,
    /// The height-`ℓ` tree the cycle starts from, and its `PE(1,ℓ,b)` claim.
    opening: TreeOpening<F, D>,
    layers: Vec<Vec<Elt>>,
    s: Vec<Elt>,
    claim: TreeClaim<F, D>,
    /// The same claim read as `TE(1,ℓ,b)`, which is what Π^Fold consumes.
    te_point: Vec<Elt>,
    te_claim: TreeClaim<F, D>,
    binding: Vec<u8>,
    /// Protocol 3 Step 1(a)'s `ξ` and `r`.
    xi: F,
    r: Vec<F>,
    norm: NormCheckProof<F, D, NV_NORM, NC_NORM>,
    /// Protocol 4 Step 3(a)'s `c₁…c_{2^k}` and Step 4(c)(i)'s row challenge.
    challenges: Vec<Elt>,
    rho: F,
    fold: Proof,
    /// Π^Fold's `x̃_bot`, and the tree it is a claim on.
    bottom: TreeClaim<F, D>,
    bottom_opening: TreeOpening<F, D>,
    /// Protocol 5 Step 2(a)(i)'s batching challenges. Step 3's output point is
    /// not a message — it is squeezed from the transcript — so the battery
    /// carries the *claims* it produces (`next_point`, `next_value`) instead.
    xi_dec: F,
    eta_dec: F,
    dec: DecompositionProof<F, D>,
    next_point: Vec<Elt>,
    next_value: Elt,
    shape: CycleShape,
    /// §5.4: `TE(1,k,b)^ω × PE(1,k,b)^{ω+1}` as Π^Reshape receives it, its
    /// transcript material, and the finished proof.
    side_claims: Vec<SideClaim<F, D>>,
    finishing: Finishing,
    finish: tree_fin::FinProof<F, D>,
}

impl Scenario {
    fn build(key: &Key, f: &[Elt], seed: &[u8; 32]) -> Self {
        let slot = key.slot_len();
        let opening = key.commit(f).expect("commit");
        let layers = opening.layers.clone();
        let s = tree_eval::concatenated(slot, &layers);
        let u = point(HEIGHT + M, 0xA5);
        let v = tree_eval::layer_value(&s, slot, HEIGHT, &u).expect("leaf MLE");
        let te_point = tree_eval::concatenated_point(&u, &s, slot).expect("PE→TE bridge");
        let claim = TreeClaim {
            t: opening.root.clone(),
            u,
            v,
        };
        let te_claim = TreeClaim {
            t: claim.t.clone(),
            u: te_point.clone(),
            v: claim.v.clone(),
        };
        let binding = tree_eval::statement_bytes(seed, &[], &[], &[&te_point, &layers[0]]);
        let shape = CycleShape::new(K, p3_set().expansion_factor(D), BASE);

        let drawn = tree_eval::challenges::<F>(b"maltese-norm", &binding, 1 + NV_NORM);
        let (xi, r) = (drawn[0], drawn[1..].to_vec());
        let norm = tree_eval::norm_check_prove::<F, D, NV_NORM, NC_NORM>(
            &s,
            &r,
            xi,
            BASE,
            &binding,
            slot,
            &claim.u,
            &claim.v,
        )
        .expect("norm check");

        let challenges: Vec<Elt> = (0..1usize << K)
            .map(|j| p3_set().sample(seed, j as u64))
            .collect();
        let (fold, top, bottom) = tree_fold::fold_prove::<F, D, BASE, ALPHA, NV_FOLD>(
            key,
            &te_claim,
            &layers,
            K,
            &challenges,
            &shape,
            &binding,
        )
        .expect("fold");
        let rho = tree_eval::challenges::<F>(b"maltese-fold-batch", &binding, 1)[0];
        let bottom_opening = TreeOpening {
            root: bottom.t.clone(),
            layers: fold.folded_layers.clone(),
        };
        // Π^Fold's two set-aside claims (§5.2.2 Step 5), in Prot. 6's order.
        let mut side_claims =
            vec![te_side_claim(&top.t, &layers[..K], &top.u, &top.v)];
        let subs_point =
            tree_eval::ring_challenges::<F, D>(b"maltese-subs-claim", &binding, K + M);
        let subs_value = tree_eval::layer_value(
            &tree_eval::concatenated(slot, &fold.subs.layers),
            slot,
            K,
            &subs_point,
        )
        .expect("t_subs opens a k-layer tree");
        side_claims.push(pe_side_claim(
            &fold.subs.root,
            &fold.subs.layers,
            &subs_point,
            &subs_value,
        ));

        let planes = shape.padded_planes;
        let dec_drawn = tree_eval::challenges::<F>(b"maltese-dec", &binding, 2);
        let (xi_dec, eta_dec) = (dec_drawn[0], dec_drawn[1]);
        let r_new = tree_eval::ring_challenges::<F, D>(
            b"maltese-dec-point",
            &binding,
            shape.next_height(HEIGHT) + M,
        );
        let dec = tree_eval::decompose_prove::<F, D, BASE, ALPHA>(
            key,
            &bottom_opening,
            planes,
            xi_dec,
            eta_dec,
        )
        .expect("decompose");
        let (next_point, next_value) = tree_eval::decompose_verify::<F, D, BASE, ALPHA>(
            key,
            &dec,
            &bottom.u,
            &bottom.v,
            &bottom_opening,
            planes,
            xi_dec,
            eta_dec,
            &r_new,
        )
        .expect("Π^Dec is complete");

        // Π^Dec Step 3's output is the `(ω+1)`st `PE(1,·,b)` claim (Prot. 6, p. 42);
        // here `ℓ̃ = 6 < k = 7`, so it also exercises Π^Reshape's short-block padding.
        side_claims.push(pe_side_claim(
            &dec.commitment.root,
            &dec.commitment.layers,
            &next_point,
            &next_value,
        ));
        let finishing = Finishing::new(key, &FIN_SEED, &side_claims);
        let finish = finishing.prove(key, &side_claims);

        Self {
            key: key.clone(),
            f: f.to_vec(),
            slot,
            k: K,
            planes,
            opening,
            layers,
            s,
            claim,
            te_point,
            te_claim,
            binding,
            xi,
            r,
            norm,
            challenges,
            rho,
            fold,
            bottom,
            bottom_opening,
            xi_dec,
            eta_dec,
            dec,
            next_point,
            next_value,
            shape,
            side_claims,
            finishing,
            finish,
        }
    }
}

/// Every check the assembled scheme owes the reader, run **without
/// short-circuiting**, returned as the set of names that *rejected*.
///
/// Fiat–Shamir absorbs each message before the next challenge, so one tamper
/// usually cascades and `is_err()` from a bundled verifier says little. Each
/// name below is therefore one equation of one protocol, and each protocol is
/// dispatched through its `*_report` entry point — the capability that evaluates
/// *every* equation and returns *all* the rejections it owns
/// ([`tree_eval::norm_check_report`], [`tree_fold::fold_report`],
/// [`tree_eval::decompose_report`], on the model of
/// [`zk::pcs::dotproduct::verify_core_report`]). A verifier that returned only
/// the first error could not show that a check is live, because a check that is
/// only ever reached second is indistinguishable from one that never runs.
fn failing(sc: &Scenario) -> BTreeSet<&'static str> {
    let mut bad = BTreeSet::new();
    let mut record = |name: &'static str, tripped: bool| {
        if tripped {
            bad.insert(name);
        }
    };

    // ── Def. 19's four equations ────────────────────────────────────────────
    record(
        "open.rejects",
        sc.key.open(&sc.opening, BASE).is_err(),
    );
    record(
        "open.rejects_with_message",
        sc.key.open_with_message(&sc.opening, BASE, &sc.f).is_err(),
    );
    record(
        "open.norm_gate",
        sc.key.check_norms(&sc.opening, BASE).is_err(),
    );

    // ── Protocol 3 (Π^PE_NC): Eq. (10), Step 1(c), Eq. (8), Step 2(b), Lem. 14 ─
    for error in tree_eval::norm_check_report(
        &sc.norm,
        &sc.s,
        &sc.r,
        sc.xi,
        BASE,
        &sc.binding,
        sc.slot,
        &sc.claim.u,
        &sc.claim.v,
    ) {
        record(
            match error {
                EvalError::SumcheckRejected => "pe_nc.sumcheck",
                EvalError::PackedNormMismatch => "pe_nc.packed_norm",
                EvalError::PackingMismatch { .. } => "pe_nc.packing",
                EvalError::LayerClaimMismatch { .. } => "pe_nc.input_claim",
                EvalError::WrongVariableCount { .. }
                | EvalError::WrongLength { .. }
                | EvalError::DegreeUnderstated { .. } => "pe_nc.wrong_shape",
                _ => panic!("norm_check_report returned an unmapped {error:?}"),
            },
            true,
        );
    }

    // ── Protocol 4 (Π^Fold): Eq. (11)–(19) ──────────────────────────────────
    record(
        "fold.split_eq12",
        tree_fold::check_split(&sc.te_claim, &sc.layers, sc.k, &sc.fold.v_top, &sc.fold.v_subs)
            .is_err(),
    );
    for error in tree_fold::fold_report(
        &sc.key,
        &sc.te_claim,
        &sc.layers,
        &sc.fold,
        sc.k,
        &sc.challenges,
        &sc.binding,
        &sc.shape,
        sc.rho,
    ) {
        record(
            match error {
                FoldError::SplitClaimMismatch => "fold.split_eq12",
                FoldError::SubtreeWeightsMismatch => "fold.subtree_weights_eq14",
                FoldError::SumcheckRejected => "fold.sumcheck",
                FoldError::SubtreeEvaluationMismatch => "fold.subtree_eval_eq17",
                FoldError::SubtreeCommitmentMismatch { .. } => "fold.subtree_commit_eq16",
                FoldError::FoldedCommitmentMismatch => "fold.root_eq11",
                FoldError::FoldedCommitmentBatchMismatch => "fold.root_batch_eq19",
                FoldError::FoldedLayerMismatch { .. } => "fold.layers_eq11",
                FoldError::NormGrowth { .. } => "fold.norm_growth",
                FoldError::FoldedEvaluationMismatch => "fold.bot_eval_eq18",
                FoldError::WrongLength { .. }
                | FoldError::HeightTooSmall { .. }
                | FoldError::DegreeUnderstated { .. }
                | FoldError::Eval(_) => "fold.wrong_shape",
                FoldError::Tree(_) => "fold.input_tree_opens",
                FoldError::SubtreeCommitInvalid(_) => "fold.subs_tree_opens",
                _ => panic!("fold_report returned an unmapped {error:?}"),
            },
            true,
        );
    }

    // ── Protocol 5 (Π^Dec): Eq. (21)–(31) ───────────────────────────────────
    for error in tree_eval::decompose_report(
        &sc.key,
        &sc.dec,
        &sc.bottom.u,
        &sc.bottom.v,
        &sc.bottom_opening,
        sc.planes,
        sc.xi_dec,
        sc.eta_dec,
    ) {
        record(
            match error {
                EvalError::PlaneNotShort { .. } => "dec.plane_short_eq21",
                EvalError::DecompositionMismatch { .. } => "dec.recompose_eq21",
                EvalError::PrefixNotZero { .. } => "dec.prefix_eq31",
                EvalError::ConstraintBatchMismatch => "dec.batch_eq25",
                EvalError::DecompositionSideMismatch => "dec.sides_eq26_28",
                EvalError::LayerClaimMismatch { .. } => "dec.eval_eq30",
                EvalError::DecomposedCommitmentMismatch { .. } => "dec.commitment_eq21a",
                EvalError::Tree(_) => "dec.new_tree_opens",
                EvalError::WrongLength { .. }
                | EvalError::WrongVariableCount { .. }
                | EvalError::DigitOverflow { .. }
                | EvalError::DegreeUnderstated { .. } => "dec.wrong_shape",
                _ => panic!("decompose_report returned an unmapped {error:?}"),
            },
            true,
        );
    }

    // ── §5.4 (Π^Fin): Def. 23, Eq. (32)–(36), Π^PE_NC,fin, GH′ ───────────────
    for error in sc.finishing.report(&sc.key, &sc.side_claims, &sc.finish) {
        record(
            match error {
                tree_fin::FinError::RootMismatch { .. } => "fin.gh_root",
                tree_fin::FinError::LinkMismatch { .. } => "fin.gh_link",
                tree_fin::FinError::TopNotShort { .. } => "fin.gh_norm_top",
                tree_fin::FinError::BottomNotShort { .. } => "fin.gh_norm_bot",
                tree_fin::FinError::BlocksMismatch { .. } => "fin.blocks",
                tree_fin::FinError::PrefixNotZero { .. } => "fin.prefix",
                tree_fin::FinError::AsideMismatch => "fin.a_side",
                tree_fin::FinError::GsideMismatch => "fin.g_side",
                tree_fin::FinError::BatchMismatch => "fin.batch_eq32",
                tree_fin::FinError::TeClaimMismatch { .. } => "fin.eval_te",
                tree_fin::FinError::PeClaimMismatch { .. } => "fin.eval_pe",
                tree_fin::FinError::Layer1ClaimMismatch => "fin.a1_claim",
                tree_fin::FinError::Layer2ClaimMismatch => "fin.a2_claim",
                tree_fin::FinError::FormMismatch => "fin.form_vectors",
                tree_fin::FinError::QFormMismatch => "fin.q_claim",
                tree_fin::FinError::ABFormMismatch => "fin.ab_claim",
                tree_fin::FinError::Tree(_) => "fin.blocks_open",
                tree_fin::FinError::WrongLength { .. }
                | tree_fin::FinError::WrongVariableCount { .. }
                | tree_fin::FinError::ClaimsOutOfOrder { .. }
                | tree_fin::FinError::Eval(_) => "fin.wrong_shape",
                _ => panic!("fin_report returned an unmapped {error:?}"),
            },
            true,
        );
    }

    // ── the two claim-level facts the cycle forwards ────────────────────────
    // The TE claim Π^Fold was given must be the *bridge* applied to the PE claim
    // Π^PE_NC was given, evaluated on the very vector the norm check ran on; if
    // the two diverge the round is proving a claim about some other table.
    let bridge = tree_eval::concatenated_point(&sc.claim.u, &sc.s, sc.slot);
    record(
        "forward.te_bridge",
        bridge.as_ref() != Ok(&sc.te_point),
    );
    let new_layers = &sc.dec.commitment.layers;
    record(
        "forward.base_layer_claim",
        tree_eval::layer_claim(
            &tree_eval::concatenated(sc.slot, new_layers),
            sc.slot,
            new_layers.len(),
            &sc.next_point,
            &sc.next_value,
        )
        .is_err(),
    );
    // Π^Fold's **set-aside top claim**, which Eq. (12) cannot bind in this shape.
    // The `TE` point Π^Fold is handed is the bridge `(1 ‖ u_PE)` (the check just
    // above), so Eq. (12)'s factor `êq(0^{ℓ−k}, u_{(:ℓ−k)})` reads coordinate 1 and
    // is identically zero: `v = 0·v_top + v_subs`, and a forged `v_top` slips past
    // every equation of Protocol 4 — measured, not argued (it was the one tamper
    // this file's battery could not land on 2026-09-24). §5.4's `Π^Fin`, run above,
    // is the paper's answer: Eq. (35) re-reads this very value against the fresh
    // two-layer commitment, and `fin.eval_te` now refuses the same forgery. What
    // remains here is §2.2 p. 9's *direct* branch kept as a **cross-check** — the
    // branch that opens the `k` top layers and evaluates `s̃_top` at Eq. (12)'s own
    // point `u_{(ℓ−k+1:)}`. It is the non-succinct one of the two; `Π^Fin` is the
    // route whose succinctness the paper claims (Lem. 35, Cor. 4), and the two
    // agreeing is itself the evidence that the recommitment did not move the claim.
    let u_tail = &sc.te_claim.u[sc.te_claim.u.len() - (sc.k + 1 + M)..];
    let s_top = tree_eval::concatenated(sc.slot, &sc.layers[..sc.k]);
    let top_forged = match tree_eval::mle_at_ring(&s_top, u_tail) {
        Ok(value) => value != sc.fold.v_top,
        Err(_) => true,
    };
    record("forward.top_tree_claim", top_forged);
    bad
}

/// The check list, as the coverage audit asserts it.
const ALL_CHECKS: &[&str] = &[
    "open.rejects",
    "open.rejects_with_message",
    "open.norm_gate",
    "pe_nc.sumcheck",
    "pe_nc.packed_norm",
    "pe_nc.packing",
    "pe_nc.input_claim",
    "pe_nc.wrong_shape",
    "fold.split_eq12",
    "fold.subtree_weights_eq14",
    "fold.subtree_commit_eq16",
    "fold.subtree_eval_eq17",
    "fold.root_eq11",
    "fold.root_batch_eq19",
    "fold.layers_eq11",
    "fold.norm_growth",
    "fold.bot_eval_eq18",
    "fold.sumcheck",
    "fold.wrong_shape",
    "fold.input_tree_opens",
    "fold.subs_tree_opens",
    "dec.plane_short_eq21",
    "dec.recompose_eq21",
    "dec.prefix_eq31",
    "dec.batch_eq25",
    "dec.sides_eq26_28",
    "dec.eval_eq30",
    "dec.new_tree_opens",
    "dec.commitment_eq21a",
    "dec.wrong_shape",
    "forward.te_bridge",
    "forward.base_layer_claim",
    "forward.top_tree_claim",
    "fin.gh_root",
    "fin.gh_link",
    "fin.gh_norm_top",
    "fin.gh_norm_bot",
    "fin.blocks",
    "fin.blocks_open",
    "fin.prefix",
    "fin.a_side",
    "fin.g_side",
    "fin.batch_eq32",
    "fin.eval_te",
    "fin.eval_pe",
    "fin.a1_claim",
    "fin.a2_claim",
    "fin.form_vectors",
    "fin.q_claim",
    "fin.ab_claim",
    "fin.wrong_shape",
];

/// Every rejection the scheme owes the reader, one named tamper per line.
///
/// Each case asserts the *whole* set of checks that rejected it — not merely
/// `is_err()` — because Fiat–Shamir makes an early edit re-derive every later
/// challenge, so a single forged commitment legitimately trips most of the
/// battery at once. The last block asserts every name in [`ALL_CHECKS`] appears
/// in some case's set: a check no tamper can trip is dead code.
fn tamper(key: &Key, f: &[Elt], seed: &[u8; 32]) -> BTreeSet<&'static str> {
    let started = Instant::now();
    let sc = Scenario::build(key, f, seed);
    println!("tamper battery: cycle assembled in {:?}", started.elapsed());

    let honest = failing(&sc);
    assert!(
        honest.is_empty(),
        "the honest proof was rejected by {honest:?}"
    );
    println!("  honest proof: 0 of {} checks reject", ALL_CHECKS.len());

    let mut covered: BTreeSet<&'static str> = BTreeSet::new();
    let mut drift: Vec<String> = Vec::new();
    let mut cases = 0usize;
    let mut case = |label: &str, state: &Scenario, expected: &[&'static str]| {
        cases += 1;
        let bad = failing(state);
        assert!(!bad.is_empty(), "{label}: the tamper was accepted");
        if bad != expected.iter().copied().collect::<BTreeSet<_>>() {
            drift.push(format!("{label}\n      want {expected:?}\n      got  {bad:?}"));
        }
        covered.extend(bad.iter().copied());
        println!("  {label}: {}", bad.len());
    };

    // ── Def. 19: `Open`'s and `Open_F`'s equations, one tamper each ─────────
    let mut s = sc.clone();
    s.opening.root[0] = s.opening.root[0].clone() + monomial(1);
    s.te_claim.t[0] = s.te_claim.t[0].clone() + monomial(1);
    s.claim.t[0] = s.claim.t[0].clone() + monomial(1);
    // Adjudicated: expectation under-predicted. `claim.t` *is* the received root
    // Π^Fold opens in its Step-1 well-formedness check, so one shared object
    // trips Def. 19's two opening gates and Protocol 4's `Open` at once.
    case(
        "root t = A·s₁ forged (Def. 19 root equation)",
        &s,
        &[
            "open.rejects",
            "open.rejects_with_message",
            "fold.input_tree_opens",
        ],
    );

    let mut s = sc.clone();
    s.opening.layers[HEIGHT - 1][0] = s.opening.layers[HEIGHT - 1][0].clone() + monomial(1);
    // Adjudicated: expectation under-predicted. Layer ℓ is `G⁻¹(f)`, so its digits
    // are binary and `+1` puts one at exactly `b` — Def. 19's `‖sᵢ‖∞ < b` gate,
    // which `Open` enforces alongside the link equations.
    case(
        "leaf layer edited inside the opening (Def. 19 link)",
        &s,
        &[
            "open.norm_gate",
            "open.rejects",
            "open.rejects_with_message",
        ],
    );

    let mut s = sc.clone();
    s.f[3] = s.f[3].clone() + monomial(1);
    case(
        "committed value f forged (Def. 19 Open_F leaf equation)",
        &s,
        &["open.rejects_with_message"],
    );

    let mut s = sc.clone();
    s.opening.layers[0][0] = monomial(9);
    case(
        "a digit at or above b (Def. 19 norm gate)",
        &s,
        &["open.rejects", "open.rejects_with_message", "open.norm_gate"],
    );

    // ── Protocol 3: the norm-check reduction ────────────────────────────────
    let mut s = sc.clone();
    s.norm.packed = monomial(9);
    case(
        "packed a outside N_b's root set (Prot. 3 Step 2(b))",
        &s,
        &["pe_nc.packed_norm", "pe_nc.packing"],
    );

    let mut s = sc.clone();
    s.norm.sumcheck.rounds[0][1] += F::ONE;
    case(
        "norm sum-check round forged (Prot. 3 Step 1(c))",
        &s,
        &["pe_nc.sumcheck"],
    );

    let mut s = sc.clone();
    s.r.truncate(NV_NORM - 1);
    case(
        "norm-check point r truncated (Eq. 8's variable count)",
        &s,
        &["pe_nc.sumcheck", "pe_nc.wrong_shape"],
    );

    let mut s = sc.clone();
    s.claim.v = s.claim.v + monomial(1);
    s.te_claim.v = s.te_claim.v + monomial(1);
    case(
        "input PE claim v forged (Eq. 10)",
        &s,
        &["pe_nc.input_claim", "fold.split_eq12"],
    );

    // ── Protocol 4: the folding reduction ───────────────────────────────────
    let mut s = sc.clone();
    s.fold.v_bot = s.fold.v_bot + monomial(1);
    case(
        "folded evaluation v_bot forged (Eq. 18)",
        &s,
        &["fold.bot_eval_eq18"],
    );

    let mut s = sc.clone();
    s.fold.v_top = s.fold.v_top + monomial(1);
    // Not `fold.split_eq12`: in this shape Eq. (12)'s top factor is zero (see
    // `forward.top_tree_claim`), so Protocol 4 has no equation that reads
    // `v_top`. The direct base-case check is what lands this tamper.
    case(
        "top-tree claim v_top forged (Eq. (12)'s factor is 0 here)",
        &s,
        &["forward.top_tree_claim"],
    );

    let mut s = sc.clone();
    s.fold.v_subs = s.fold.v_subs + monomial(1);
    // Adjudicated: expectation mis-read the equations. `v_subs` is Eq. (12)'s
    // second summand *and* Eq. (15)'s claimed sum, so the weights' inner product
    // (Eq. 14) and the sum-check's own opening check both reject; Eq. (17) is
    // about `y_subs`, which this tamper never touches.
    case(
        "bottom-subtrees claim v_subs forged (Eq. 12/15)",
        &s,
        &[
            "fold.split_eq12",
            "fold.subtree_weights_eq14",
            "fold.sumcheck",
        ],
    );

    let mut s = sc.clone();
    s.fold.folded_root[0] = s.fold.folded_root[0].clone() + monomial(1);
    // Adjudicated: expectation under-predicted. Eq. (19) is Eq. (11) applied to
    // the *same received* `t*`, so a forged `t*` trips the batched restatement by
    // construction — the two names are one object, not a cascade.
    case(
        "folded commitment t* forged (Eq. 11)",
        &s,
        &["fold.root_batch_eq19", "fold.root_eq11"],
    );

    let mut s = sc.clone();
    s.challenges[0] = s.challenges[0].clone() + monomial(1);
    // Adjudicated: expectation over-predicted. `c` is read by exactly Eq. (11)'s
    // two halves and Eq. (19); `t_subs`/`y_subs` are committed before `c` is
    // sampled (p. 33 Steps 2(c) then 3(a)), and Π^Dec replays the *stored*
    // forwarded objects, which a verifier-side `c` forgery does not alter.
    // (Eq. (18) as coded reads `s*`, not `c` — see `fold_report` step 10 — so
    // `bot_eval_eq18` stays silent; the round is still refused by Eq. (11).)
    case(
        "a folding challenge cⱼ forged (Eq. 11/19, and the sum-check binding)",
        &s,
        &["fold.layers_eq11", "fold.root_batch_eq19", "fold.root_eq11"],
    );

    let mut s = sc.clone();
    s.fold.folded_layers[0][0] = s.fold.folded_layers[0][0].clone() + monomial(1);
    s.bottom_opening.layers[0][0] = s.bottom_opening.layers[0][0].clone() + monomial(1);
    // Adjudicated: expectation named the wrong Protocol 5 equation. Eq. (25)
    // reads only `t`, `v_A`, `v_G` — never `s` — so it cannot see `s*`; the
    // equation that does is Eq. (26)/(28), whose *value* side is the inner
    // product against the received openings `s`.
    case(
        "folded openings s* forged (Eq. 11's second half)",
        &s,
        &[
            "dec.recompose_eq21",
            "dec.sides_eq26_28",
            "fold.bot_eval_eq18",
            "fold.layers_eq11",
        ],
    );

    let mut s = sc.clone();
    s.fold.subs.layers[0][0] = s.fold.subs.layers[0][0].clone() + monomial(1);
    // Adjudicated: expectation over-predicted twice over. Eq. (16)'s
    // well-formedness *is* `Open(t_subs)` → `fold.subs_tree_opens`; the slot
    // read-out reads `s_{subs,k}` (the bottom layer) alone, so layer 1 is
    // invisible to it, and Π^Dec never receives `t_subs`, so `dec.new_tree_opens`
    // could never have fired. The two named equations get their own cases below.
    case(
        "subtree-evaluation commitment t_subs forged (Eq. 16/17)",
        &s,
        &["fold.subs_tree_opens"],
    );

    let mut s = sc.clone();
    let bottom_slot = s.k - 1;
    s.fold.subs.layers[bottom_slot][0] = s.fold.subs.layers[bottom_slot][0].clone() + monomial(1);
    // The tamper that Eq. (16)/(17)'s read-out *is* reachable by: subtree `j`'s
    // evaluation must equal the `j`th slot of `s_{subs,k}`.
    case(
        "a subtree slot of t_subs forged (Eq. 16/17's read-out)",
        &s,
        &["fold.subtree_commit_eq16", "fold.subs_tree_opens"],
    );

    let mut s = sc.clone();
    s.fold.y_subs = s.fold.y_subs + monomial(1);
    // Eq. (17)'s claimed sum, against both the sum-check's own final evaluation
    // and the value re-read through `t_subs`'s slots.
    case(
        "subtree evaluation claim y_subs forged (Eq. 17)",
        &s,
        &["fold.subtree_eval_eq17"],
    );

    let mut s = sc.clone();
    s.k = K - 1;
    // Adjudicated: expectation assumed Eq. (12) has a `k` to disagree about. Its
    // only `k` is the factor `êq(0^{ℓ−k}, u_{(:ℓ−k)})`, identically 0 for every
    // `k < ℓ` because `u₁ = 1` is the PE→TE bridge, so a wrong arity cannot trip
    // `split_eq12`; `fold_report`'s arity gate returns before its other
    // equations. `forward.top_tree_claim` does fire, and correctly: it keys on
    // the *declared* `k` for both its `(k+1+m)`-coordinate tail and the `k`
    // layers it reads, so a re-declared arity re-derives some other `ṽ_top`.
    case(
        "a different declared arity than the fold used (Protocol 4's shape)",
        &s,
        &["fold.wrong_shape", "forward.top_tree_claim"],
    );

    let mut s = sc.clone();
    s.shape = CycleShape::new(1, 1, BASE);
    case(
        "a smaller declared B than the fold spent (§2.2 norm gate)",
        &s,
        &["fold.norm_growth"],
    );

    // ── Protocol 5: the norm-decomposition reduction ────────────────────────
    let mut s = sc.clone();
    s.dec.v_a = s.dec.v_a + monomial(1);
    // Adjudicated: expectation under-predicted. Eq. (25) is `ξ·⟨p_η,n, t⟩ + v_G
    // = v_A` on the *received* `v_A`, so forging it breaks the batch gate with
    // the Eq. (26)/(27) side check — one object, two equations (p. 38 Step 2(c)).
    case(
        "batched constraint claim v_A forged (Eq. 26/27)",
        &s,
        &["dec.batch_eq25", "dec.sides_eq26_28"],
    );

    let mut s = sc.clone();
    s.dec.v_g = s.dec.v_g + monomial(1);
    // Adjudicated: same mechanism as `v_A` — `v_G` is Eq. (25)'s other summand.
    case(
        "batched constraint claim v_G forged (Eq. 28/29)",
        &s,
        &["dec.batch_eq25", "dec.sides_eq26_28"],
    );

    let mut s = sc.clone();
    // Index `2·slot` is layer 1's first digit, i.e. the first entry *past* the
    // `0^{2nα}` prefix Eq. (31) guards, so a digit at 2 names Eq. (21)'s
    // shortness gate rather than the prefix one.
    s.dec.planes[0][2 * s.slot] = monomial(2);
    // Adjudicated: expectation under-predicted. The planes are the shared object
    // of Protocol 5: they enter Eq. (21)'s sum, Eq. (26)/(28)'s digit side and
    // Eq. (30)'s `v = Σ_j b^{j−1}·s̃_{dec,j}(u)` re-read, all three of which move
    // with a single digit. (Eq. (25) reads only `t, v_A, v_G` and stays silent.)
    case(
        "a decomposition plane pushed past the gadget base (Eq. 21)",
        &s,
        &[
            "dec.commitment_eq21a",
            "dec.eval_eq30",
            "dec.plane_short_eq21",
            "dec.recompose_eq21",
            "dec.sides_eq26_28",
        ],
    );

    let mut s = sc.clone();
    // Eq. (31): the recomposed `s` must begin with `0^{2nα}`. A single digit in
    // plane 0's prefix is still `b`-short, so shortness and the digit width stay
    // clean and only the prefix gate speaks.
    s.dec.planes[0][0] = monomial(1);
    // Adjudicated: expectation under-predicted — the same shared-object argument:
    // the prefix entry is a coordinate of `s_dec`, so Eq. (21)'s sum, the digit
    // side of Eq. (26)/(28) and Eq. (30)'s re-read all disagree with the input.
    case(
        "a decomposition plane whose 0^{2nα} prefix is live (Eq. 31)",
        &s,
        &[
            "dec.commitment_eq21a",
            "dec.eval_eq30",
            "dec.prefix_eq31",
            "dec.recompose_eq21",
            "dec.sides_eq26_28",
        ],
    );

    let mut s = sc.clone();
    // A move that keeps every digit inside `{−1,0,1}` and so stays short: this is
    // Eq. (21)'s *sum*, and only it, that fails.
    s.dec.planes[0][2 * s.slot] = s.dec.planes[0][2 * s.slot].clone() - monomial(1);
    // Adjudicated: expectation under-predicted. Only Eq. (21)'s sum was the
    // intended victim, but `decompose_report` re-reads the *same* planes through
    // Eq. (26)/(28)'s digit side and Eq. (30), so shortness is the one gate that
    // stays clean here.
    case(
        "a short plane that is not a decomposition of s (Eq. 21's sum)",
        &s,
        &[
            "dec.commitment_eq21a",
            "dec.eval_eq30",
            "dec.recompose_eq21",
            "dec.sides_eq26_28",
        ],
    );

    let mut s = sc.clone();
    s.planes += 1;
    case(
        "a plane count that is not the h the cycle declared (Eq. 21's shape)",
        &s,
        &["dec.wrong_shape"],
    );

    let mut s = sc.clone();
    s.bottom.v = s.bottom.v + monomial(1);
    case(
        "Π^Fold's output claim v_bot forged against Π^Dec (Eq. 30)",
        &s,
        &["dec.eval_eq30"],
    );

    let mut s = sc.clone();
    s.dec.commitment.layers[0][0] = s.dec.commitment.layers[0][0].clone() + monomial(1);
    // Adjudicated: expectation over-predicted. `forward.base_layer_claim` is a
    // `PE` claim, i.e. one read off the new tree's *bottom* layer alone (§5
    // "Relations"), and this edit is in layer 1; Eq. (21)–(31) are all stated
    // against the *input* openings, which are untouched.
    case(
        "the recommitted tree does not open (Protocol 5 Step 1)",
        &s,
        &["dec.new_tree_opens"],
    );

    // Step 1(a) *also* says the prover commits to `s_dec`, so the tree it hands over
    // must be a commitment to **these** planes. Swapping `t*_dec` for another
    // well-formed low-norm tree of the same shape used to be accepted by every
    // equation Π^Dec runs — Eq. (21)'s sum and (25)/(26)/(28)/(30) all read the
    // planes and the *input* tree, and `Open` checks the new tree only against
    // itself. That attack is what found the missing check (2026-09-24).
    let mut s = sc.clone();
    let mut other = tree_eval::decomposed_leaves(&sc.dec.planes);
    for digit in other.iter_mut() {
        *digit = monomial(0);
    }
    other[0] = monomial(1);
    other[1] = monomial(1);
    s.dec.commitment = key
        .commit_digits(&other)
        .expect("another well-formed tree of the same shape");
    // Honest scoping: the assembly already noticed, but only through
    // `forward.base_layer_claim` — the `PE` claim this file re-reads off the new
    // tree's bottom layer, which lives *outside* Π^Dec. Every equation the protocol
    // itself prints was satisfied by the swapped tree, which is the src gap.
    case(
        "t*_dec is a valid tree but not a commitment to these planes (Prot. 5 Step 1(a))",
        &s,
        &["dec.commitment_eq21a", "forward.base_layer_claim"],
    );

    let mut s = sc.clone();
    s.next_value = s.next_value + monomial(1);
    case(
        "the forwarded claim y_dec forged (Protocol 5 Step 3)",
        &s,
        &["forward.base_layer_claim"],
    );

    let mut s = sc.clone();
    s.s.pop();
    case(
        "the concatenated opening the norm check ran on is truncated",
        &s,
        &["pe_nc.wrong_shape", "forward.te_bridge"],
    );

    // ── §5.4 `Π^Fin`: one named tamper per printed condition ────────────────
    // Where an edit cannot be isolated, it is because two conditions the paper
    // prints separately read the *same object*; the case says which, and the
    // alone-version of that condition is a `zk::pcs::tree_fin` unit test.
    let mut s = sc.clone();
    s.finish.reshape.commitment.t[0] = s.finish.reshape.commitment.t[0].clone() + monomial(1);
    case(
        "finish: t* is not B1·s1 (Def. 23 GHOpen, line 1)",
        &s,
        &["fin.gh_root"],
    );

    let mut s = sc.clone();
    // A digit of `s1` raised from 0 to 1 still satisfies `‖s1‖∞ < b1`, so with
    // `t`, `a1` and `y1` re-derived the only equation left disagreeing is the
    // recomposition `G·s1 = (I⊗B2)·s2`.
    let index = s
        .finish
        .reshape
        .commitment
        .s1
        .iter()
        .position(|digit| *digit == monomial(0))
        .expect("a binary digit plane has zeros");
    s.finish.reshape.commitment.s1[index] = monomial(1);
    let moved = s.finish.reshape.commitment.clone();
    s.finish.reshape.commitment.t = s
        .finishing
        .key
        .b1()
        .matvec(&moved.s1)
        .expect("the top layer's shape is unchanged");
    let derived = tree_fin::finish(
        &s.finishing.key,
        &s.finish.reshape,
        s.finish.r.clone(),
        s.finish.r_prime.clone(),
    )
    .expect("re-derive Step 2/3's claims from the moved layer");
    s.finish.a1 = derived.a1;
    s.finish.y1 = derived.y1;
    case(
        "finish: the recomposition G·s1 = (I⊗B2)·s2 broken (Def. 23, line 2)",
        &s,
        &["fin.gh_link"],
    );

    let mut s = sc.clone();
    // Digits `(2, −1)` in place of `(0, 0)` inside one `α`-block: `2·2^k − 2^{k+1}
    // = 0`, so `G·s1` is bit-for-bit the honest one and only the norm gate sees
    // the non-canonical expansion Π^PE_NC,fin's Step 1 exists to refuse.
    let zero = monomial(0);
    let pair = s
        .finish
        .reshape
        .commitment
        .s1
        .windows(2)
        .enumerate()
        .find(|(at, digits)| at % ALPHA + 1 < ALPHA && digits[0] == zero && digits[1] == zero)
        .expect("two adjacent zero digits inside one block")
        .0;
    s.finish.reshape.commitment.s1[pair] = monomial(2);
    s.finish.reshape.commitment.s1[pair + 1] = monomial(0) - monomial(1);
    let moved = s.finish.reshape.commitment.clone();
    s.finish.reshape.commitment.t = s
        .finishing
        .key
        .b1()
        .matvec(&moved.s1)
        .expect("the top layer's shape is unchanged");
    let derived = tree_fin::finish(
        &s.finishing.key,
        &s.finish.reshape,
        s.finish.r.clone(),
        s.finish.r_prime.clone(),
    )
    .expect("re-derive Step 2/3's claims");
    s.finish.a1 = derived.a1;
    s.finish.y1 = derived.y1;
    case(
        "finish: s1 recomposes correctly but is not b1-short (Def. 23, line 3)",
        &s,
        &["fin.gh_norm_top"],
    );

    let mut s = sc.clone();
    // A `s2` that is not `b2`-short with `(I⊗B2)·s2` re-derived from it is exactly
    // the binding break Def. 23's MSIS paragraph rules out; Step 1(a)'s binding is
    // the other equation that reads the same vector, so the pair is minimal here.
    let pad = 3 * (1usize << (K + 1)) * sc.slot;
    let mut long = s.finish.reshape.commitment.s2.clone();
    long[pad] = monomial(5);
    s.finish.reshape.commitment =
        tree_fin::gh_commit(&s.finishing.key, &long).expect("GHCommit takes any s2");
    s.finish = tree_fin::finish(
        &s.finishing.key,
        &s.finish.reshape,
        s.finish.r.clone(),
        s.finish.r_prime.clone(),
    )
    .expect("re-derive the layer claims");
    case(
        "finish: a b2-long s2, committed consistently (Def. 23, line 3 + Prot. 6 Step 1)",
        &s,
        &["fin.gh_norm_bot", "fin.blocks"],
    );

    let mut s = sc.clone();
    // The pad block is outside every claim's re-read and every weight's span, so
    // this isolates Step 1(a)'s binding: `s*_reshape,2` must be *these* openings.
    let mut other = s.finish.reshape.commitment.s2.clone();
    other[3 * (1usize << (K + 1)) * sc.slot] = monomial(1);
    s.finish.reshape.commitment =
        tree_fin::gh_commit(&s.finishing.key, &other).expect("a well-formed commitment");
    s.finish = tree_fin::finish(
        &s.finishing.key,
        &s.finish.reshape,
        s.finish.r.clone(),
        s.finish.r_prime.clone(),
    )
    .expect("re-derive the layer claims");
    case(
        "finish: t* commits to another vector than the side-claims (Prot. 6 Step 1(a))",
        &s,
        &["fin.blocks"],
    );

    let mut s = sc.clone();
    // A live `0^{2nα}` prefix, with the recomputed `v_A`/`v_G` left at their honest
    // values: Step 2(f)'s claim fires together with every equation that reads the
    // edited coordinate. The paper *needs* `Cpre` because its verifier never sees
    // `s_reshape`; here Step 1(a)'s binding is what makes it decidable at all.
    let mut prefix = s.finish.reshape.commitment.s2.clone();
    prefix[1] = monomial(1);
    s.finish.reshape.commitment =
        tree_fin::gh_commit(&s.finishing.key, &prefix).expect("GHCommit takes any s2");
    s.finish = tree_fin::finish(
        &s.finishing.key,
        &s.finish.reshape,
        s.finish.r.clone(),
        s.finish.r_prime.clone(),
    )
    .expect("re-derive the layer claims");
    case(
        "finish: a recommitted opening with a live 0^{2nα} prefix (Prot. 6 Step 2(f))",
        &s,
        &[
            "fin.prefix",
            "fin.blocks",
            "fin.a_side",
            "fin.g_side",
            "fin.eval_te",
        ],
    );

    let mut s = sc.clone();
    s.side_claims[1].opening.root[0] = s.side_claims[1].opening.root[0].clone() + monomial(1);
    // The two equations that read a set-aside `t`: Eq. (32)'s `v_t` term, and the
    // input's own `Open` premise. Nothing else in §5.4 touches a root alone.
    case(
        "finish: a set-aside commitment forged (Eq. 32 + the TE/PE input premise)",
        &s,
        &["fin.batch_eq32", "fin.blocks_open"],
    );

    let mut s = sc.clone();
    s.finish.reshape.v_a = s.finish.reshape.v_a.clone() + monomial(1);
    case(
        "finish: the batched A-side claim v_A forged (Eq. 33, and Eq. 32 reads it too)",
        &s,
        &["fin.a_side", "fin.batch_eq32"],
    );

    let mut s = sc.clone();
    s.finish.reshape.v_g = s.finish.reshape.v_g.clone() + monomial(1);
    case(
        "finish: the batched G-side claim v_G forged (Eq. 34, and Eq. 32 reads it too)",
        &s,
        &["fin.g_side", "fin.batch_eq32"],
    );

    let mut s = sc.clone();
    s.side_claims[0].v = s.side_claims[0].v.clone() + monomial(1);
    // The headline: this is Protocol 4's `x̃_top` value — the `v_top` Eq. (12)
    // cannot bind — refused by Eq. (35) *alone*. `forward.top_tree_claim` stays
    // silent, and correctly so: it reads `fold.v_top`, and the forged claim is a
    // separate copy. The direct check's own case is the `v_top` tamper above.
    case(
        "finish: Π^Fold's top-tree claim value forged (Eq. 35)",
        &s,
        &["fin.eval_te"],
    );

    let mut s = sc.clone();
    s.side_claims[2].v = s.side_claims[2].v.clone() + monomial(1);
    case(
        "finish: the base-case PE claim value forged (Eq. 36)",
        &s,
        &["fin.eval_pe"],
    );

    let mut s = sc.clone();
    s.finish.a1 = s.finish.a1 + monomial(1);
    case(
        "finish: Π^PE_NC,fin Step 2's a1 forged",
        &s,
        &["fin.a1_claim"],
    );

    let mut s = sc.clone();
    s.finish.a2 = s.finish.a2 + monomial(1);
    case(
        "finish: the forwarded PE(2) claim y_reshape (= Step 2's a2) forged",
        &s,
        &["fin.a2_claim"],
    );

    let mut s = sc.clone();
    s.finish.y1 = s.finish.y1 + monomial(1);
    case(
        "finish: GHPrincipal′'s extra row q⊺·s1 = y1 forged (§5.4.3)",
        &s,
        &["fin.q_claim"],
    );

    let mut s = sc.clone();
    s.finish.y2 = s.finish.y2 + monomial(1);
    case(
        "finish: GHPrincipal′'s row a⊺·s2·b = y2 forged (§5.4.3)",
        &s,
        &["fin.ab_claim"],
    );

    let mut s = sc.clone();
    // A prover that sends a `q` for a *different* point and re-balances `y1`: the
    // row still adds up, and only the §5.4.3 form check refuses it.
    s.finish.q[0] = s.finish.q[0].clone() + monomial(1);
    s.finish.y1 = tree_eval::inner_product(
        &s.finish.q,
        &s.finish.reshape.commitment.s1,
    );
    case(
        "finish: q is not the evaluation-form tensor of r′ (Eq. 37 / Lem. 16)",
        &s,
        &["fin.form_vectors"],
    );

    let mut s = sc.clone();
    let swapped = s.finish.b.clone();
    s.finish.b = std::mem::replace(&mut s.finish.a, swapped);
    // Transposing Lem. 16's split keeps `|a|·|b| = |s2|`, so the nested sum still
    // spans the vector — and reads it in the wrong order. The form check fires
    // because the received tensors are no longer those of `r′`.
    case(
        "finish: Lemma 16's split transposed (a ↔ b)",
        &s,
        &["fin.form_vectors", "fin.ab_claim"],
    );

    let mut s = sc.clone();
    s.finish.r.truncate(3);
    case(
        "finish: r_{(µ'+m)} too short to index s_reshape (Prot. 6 Step 3's shape)",
        &s,
        &["fin.wrong_shape"],
    );

    // ── no check is dead code ────────────────────────────────────────────────
    if !drift.is_empty() {
        panic!(
            "{} tamper case(s) rejected a different set than documented:\n\n{}\n",
            drift.len(),
            drift.join("\n")
        );
    }
    let dead: Vec<&str> = ALL_CHECKS
        .iter()
        .copied()
        .filter(|c| !covered.contains(c))
        .collect();
    assert!(
        dead.is_empty(),
        "never tripped by any tamper, so dead code: {dead:?}"
    );
    assert_eq!(
        covered.len(),
        ALL_CHECKS.len(),
        "the audit and the check list disagree"
    );
    println!(
        "  {cases} tampers tripped all {} named checks in {:?}",
        ALL_CHECKS.len(),
        started.elapsed()
    );
    covered
}
