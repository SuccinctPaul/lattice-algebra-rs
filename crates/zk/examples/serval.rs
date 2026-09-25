//! Serval's polynomial commitment scheme — Zhang–Chow–Gao–Xiao, eprint
//! 2025/1903, *"Serval: Slack-Free ℓ2-Sound Polynomial Commitments from
//! Lattices"* — assembled as a scheme, from `src` capabilities only.
//!
//! Nothing in this file is cryptographic logic. The leveled Ajtai chain is
//! [`zk::pcs::leveled::LeveledAjtai`], the base-2 gadget is [`zk::pcs::gadget`],
//! the tensor-structured weights and the four check columns are
//! [`zk::shortness::tensor_fold`], the composed `R_main` argument is
//! [`zk::shortness::committed_norm`], the self-inner-product core is
//! [`zk::shortness::self_ip`], and the wraparound gate is
//! [`zk::shortness::exact_l2`]. What lives here is the instance, Fig. 4's
//! `Setup`/`Commit`/`Eval` order, and the Fiat–Shamir schedule of §5.1.
//!
//! # What the scheme proves
//!
//! `R_main` (Eq. 2, p. 9): knowledge of a short binary `s⃗ ∈ R_q^{Nℓ}` with
//!
//! ```text
//! Com(s⃗)                        = cm      the leveled Ajtai chain (§3.2 p. 10, Fig. 1 p. 6)
//! <coef(s⃗), ⊗_{i<log N} a⃗_i>   = v       the evaluation claim, a⃗_i from the point u
//! ct(<s⃗, σ¹(s⃗)>) mod q = b ≤ β²         the exact ℓ2 norm (§3.2 p. 12)
//! coef(s⃗) ∈ {0,1}^{Nℓd}                 the binary validation (§3.3 p. 13)
//! ```
//!
//! all folded by **one** challenge sequence, so every column talks about the
//! same surviving witness (§3.4, p. 14). `ℓ = ⌈log q⌉` is the base-2 digit count
//! of the *coefficients* (Fig. 4, p. 24: "Employ unsigned base-2 on f to get
//! s⃗ ∈ R_q^{N·⌈log q}"), and `ι = ⌈log_σ q⌉` the chain's own gadget depth; this
//! instance takes `σ = 2`, so `ι = ℓ`.
//!
//! # Why "slack-free", concretely
//!
//! Lemma 2 (p. 8) is the whole point and it is a *numerical* condition:
//!
//! ```text
//! q > 2Nℓd  ⇒  the centered representative of ct(<s⃗,σ⁻¹(s⃗)>) is the integer
//!               ‖s⃗‖² itself, so b ≤ B² really bounds the norm — no wraparound
//! ```
//!
//! which is the same window as
//! [`zk::shortness::exact_l2::direct_route_admissible`]. A scheme that ignores
//! it proves an `ℓ2` bound only up to "some integer congruent to `b` mod `q`",
//! silently regressing to the slack Serval exists to remove.
//! [`check_lemma_2_window`] asserts the instance satisfies it, and
//! `committed_norm::verify_report` refuses a statement whose bound does not.
//!
//! # The second half of the picture: what the binding buys
//!
//! [`binding_lane`] runs the same claim twice, with and without the leveled
//! commitment. Without it, `self_ip::verify` accepts a proof built over a
//! *different* vector than the one committed — the argument is only
//! chain-consistent. With it, `self_ip::verify_bound` refuses, because the
//! revealed tail must open `cm` at level 0 (Fig. 3, p. 17) and the terminal
//! identity is then evaluated on *that* tail.
//!
//! # Instance, and where it departs from the paper
//!
//! `q = 4093` (prime, `≡ 5 (mod 8)`, so `X^d + 1` does not split into linears
//! and Lemma 1's invertibility regime is the live one), `d = 4`, `N = 8` blocks,
//! `ℓ = ι = 12`, `κ = 2`, challenge pool `P_{1,1}` (`T = w₁ + 2w₂ = 3`), and `t`
//! binary repetitions derived from [`NormAccounting::repetitions`] rather than
//! chosen.
//!
//! Three honest deviations, all of scale rather than structure:
//!
//! * `log q = 12` where Table 4 (p. 28) needs `log q = 88…128` at
//!   `L = 2^15…2^20` — and beyond that lies this crate's `q ≤ 2³²` encoding
//!   ceiling (gap **G7** in `docs/open-milestones.md`). So what runs here is the
//!   protocol, not a security level: Eq. (4)'s `β_M-SIS` is printed next to `q`
//!   so the gap is visible rather than hidden.
//! * Fig. 4 covers univariate **and** multilinear evaluation; only the
//!   univariate line (§4, p. 23) is assembled here. The multilinear weight
//!   vector would come from `LinearWeights::multilinear`, whose digit axis must
//!   be `1` — i.e. the MLE axis folded *before* the digit decomposition, which
//!   the current builder cannot express for a `ℓ`-plane witness.
//! * No LaBRADOR proof-of-proof compaction (§5.1), so the proof is the raw
//!   `log N`-round transcript. The paper's own "Opt." column is analytic
//!   (p. 27: "not included in the measured microbenchmarks"), so sizes here are
//!   compared against the *Raw* formula of §3.6, p. 21 only.
//!
//! Run with: `cargo run -p lattice-zk --example serval`

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::zq::Zq;
use algebra::ring::{PolynomialQuotientRing, Ring};
use std::collections::BTreeSet;
use std::process;
use zk::foundation::fs::absorb_rings;
use zk::pcs::gadget::split;
use zk::pcs::leveled::LeveledAjtai;
use zk::shortness::committed_norm::{
    self, BinaryBundle, Chain, CheckId, MainBundle, NormProof, Statement,
};
use zk::shortness::exact_l2::direct_route_admissible;
use zk::shortness::self_ip;
use zk::shortness::tensor_fold::{
    ct, hadamard, herm, pack, square_sum, Elt, LinearWeights, NormAccounting,
};

/// Prime, `≡ 5 (mod 8)`: Lemma 1's (p. 8) regime, and no NTT-backed key exists.
type Q = Zq<4093>;
const MODULUS: u64 = 4_093;
/// Ring degree `d` of the toy instance.
const D: usize = 4;
/// `ℓ = ι = ⌈log₂ q⌉ = 12`; `2¹² = 4096 > q`, so the base-2 split is exact.
const ELL: usize = 12;
/// Block count `N`, so the polynomial has `L = N·d = 32` coefficients.
const N: usize = 8;
/// `log N`.
const LOG_N: usize = 3;
/// Rounds that send a message: `log N − 1` (Fig. 3, p. 17).
const ROUNDS: usize = LOG_N - 1;
/// Matrix height `κ` (Table 4 uses 13).
const KAPPA: usize = 2;
/// Challenge pool `P_{w₁,w₂}` (§3.6, p. 20).
const W1: u32 = 1;
const W2: u32 = 1;
/// `T = ‖c‖_{op,∞} ≤ ‖c‖₁ = w₁ + 2w₂`, the number Theorem 1's growth uses.
const T_OP: u64 = W1 as u64 + 2 * W2 as u64;
/// The security target behind the repetition count (the paper's `λ`).
const LAMBDA: u64 = 8;
/// `B² = Nℓd`, the largest squared norm the statement may claim (Lemma 2).
const B_SQ: u128 = (N * ELL * D) as u128;

/// `pp` from Fig. 4: the main chain `A_•` and one auxiliary chain `B_•` per
/// binary repetition.
struct Params {
    main: LeveledAjtai<Q, D, ELL>,
    aux: Vec<LeveledAjtai<Q, D, ELL>>,
    /// The evaluation weights `⊗ a⃗_i` at `u`, with the base-2 digit weights
    /// absorbed into `a⃗_0` (§4, p. 23).
    w_eval: LinearWeights<Q, D>,
    u: Q,
    reps: usize,
}

/// The transcript-derived scalars and the weight tables they induce, in the
/// paper's commitment order (§3.3, p. 13): `α` first, then `cm_α`, then `r`.
struct Sealed {
    alpha: Q,
    r: Q,
    /// The `cm_α` actually absorbed before `r` was drawn. [`scheme_lane`] checks
    /// these against the statement's roots, so the ordering above is a fact
    /// about the bytes the challenges came from rather than a comment.
    aux_roots: Vec<Vec<Elt<Q, D>>>,
    w_alpha: LinearWeights<Q, D>,
    w_r_alpha: LinearWeights<Q, D>,
    w_r_digit: LinearWeights<Q, D>,
}

/// A committed polynomial plus the witness the chain binds.
struct Committed {
    s: Vec<Elt<Q, D>>,
    cm: Vec<Elt<Q, D>>,
}

/// Lemma 1's regime and the gadget's exactness, checked rather than assumed.
fn check_instance() {
    assert_eq!(MODULUS % 8, 5, "Lemma 1's regime needs q ≡ 5 (mod 8)");
    assert!(
        (1u128 << ELL) > u128::from(MODULUS),
        "a base-2 gadget with {ELL} planes must cover q"
    );
}

/// Lemma 2's window: `2·N·ℓ·d < q`, i.e. a binary witness' squared norm cannot
/// wrap, so `ct(⟨s,σ(s)⟩) = b` is a statement about an integer.
fn check_lemma_2_window() {
    let twice = 2 * B_SQ;
    assert!(
        twice < u128::from(MODULUS),
        "2Nℓd = {twice} must stay under q = {MODULUS}"
    );
    assert!(
        direct_route_admissible::<Q>(B_SQ),
        "exact_l2 must agree that B² is admissible"
    );
    println!(
        "  Lemma 2 window: 2·N·ℓ·d = {twice} < q = {MODULUS} ✓  \
         (B² = {B_SQ}, exact_l2::direct_route_admissible = true)"
    );
}

/// Theorem 1's (p. 18) admissibility bounds, as squared `ℓ2` bounds on the two
/// revealed tails: `γ_log N = (2T)^{log N − 1}` from `γ₁ = 1`, then
/// `γ² · (coordinate count)`.
fn tail_bounds() -> (u128, u128) {
    let of = |base_len: usize| {
        NormAccounting {
            rounds: ROUNDS,
            t_op: T_OP,
            initial: 1,
            base_len,
        }
        .bound_sq()
    };
    (of(ELL * D), of(ELL * ELL * D))
}

/// `t`, the number of independent binary repetitions (§3.3, p. 14).
fn repetitions() -> usize {
    NormAccounting::repetitions(2 * (N * ELL * D) as u64, MODULUS, LAMBDA)
        .map(|(reps, bits)| {
            assert!(
                bits >= LAMBDA,
                "the repetition count must meet {LAMBDA} bits"
            );
            reps as usize
        })
        .expect("q > 2Nℓd, so one repetition already has an advantage")
}

/// A polynomial of `N·d` coefficients, deterministic and non-degenerate.
fn polynomial() -> Vec<Q> {
    (0..N * D)
        .map(|i| Q::from((i as u64 * 977 + 131) % MODULUS))
        .collect()
}

/// `f(u)`, computed the way a verifier would check it by hand.
fn evaluate(f: &[Q], u: Q) -> Q {
    f.iter().rev().fold(Q::ZERO, |acc, c| acc * u + *c)
}

/// A ring scalar as the little-endian word the transcript absorbs.
fn word(c: Q) -> [u8; 8] {
    u64::try_from(c.to_u128())
        .expect("q fits u64")
        .to_le_bytes()
}

/// Draws a scalar from the transcript, kept in `[1, q)` so the induced power
/// vector has distinct entries.
fn scalar(tr: &mut Transcript<Shake256Xof>) -> Q {
    let bytes = tr.challenge_bytes(8);
    let mut raw = [0u8; 8];
    raw.copy_from_slice(&bytes);
    Q::from(u64::from_le_bytes(raw) % (MODULUS - 1) + 1)
}

/// `Setup(1^λ)`: the chains of Fig. 4's `pp`, and nothing else.
fn setup(u: Q) -> Params {
    let reps = repetitions();
    Params {
        main: LeveledAjtai::setup(b"serval/A", &[0xa1u8; 32], KAPPA, N, ELL).expect("A chain"),
        aux: (0..reps)
            .map(|j| {
                let mut seed = [0xb2u8; 32];
                seed[0] = j as u8;
                LeveledAjtai::setup(b"serval/B", &seed, KAPPA, N, ELL * ELL).expect("B chain")
            })
            .collect(),
        w_eval: LinearWeights::geometric(u, ELL, ELL, ROUNDS).expect("evaluation weights"),
        u,
        reps,
    }
}

/// `Commit(pp, f)` (Fig. 4, p. 24): pack every `d` coefficients into one ring
/// element, take the unsigned base-2 decomposition, run the chain.
fn commit(pp: &Params, f: &[Q]) -> Committed {
    let s = split::<Q, D, 2, ELL>(&pack(f));
    let (cm, _) = pp.main.commit(&s).expect("commit");
    assert!(
        pp.main.decomposition_is_exact(),
        "the chain's gadget is exact"
    );
    Committed { s, cm }
}

/// The `α → cm_α → r` ordering of §3.3 ("Commitment order", p. 13).
///
/// `r` must be drawn *after* the auxiliary commitment is fixed: knowing
/// `(α, r)` beforehand would let the prover pick an `s̃_α` that matches the
/// required inner products at the single point `r` while differing elsewhere.
///
/// This is also where §5.1, p. 25 fixes the interactive schedule: "We apply
/// Fiat–Shamir to the recursive phase **after the prover sends
/// (v_r, v_rα)**", with round challenge `cᵢ` a function of
/// `Com(tr_{i−1}) = Com(pp, cm, (cm_α^(j))_{j∈[t]}, π₁, …, π_{i−1})` — so
/// `cm`, every `cm_α` and every earlier round message precede the challenge
/// that folds them. `scheme_lane` then checks that the roots absorbed here are
/// the ones the statement carries, and the round challenges themselves are
/// derived inside `committed_norm`, which absorbs the prefix and the round index
/// (`challenge_at`) before each draw.
fn seal(pp: &Params, c: &Committed) -> Sealed {
    let b = square_sum(&c.s).expect("small") as u64;
    let v = ct(&herm(
        &c.s,
        &pp.w_eval.weight(ROUNDS).expect("full weights"),
    ));
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/serval/eval");
    absorb_rings::<Shake256Xof, Q, D>(&mut tr, b"cm", &c.cm);
    tr.absorb(b"u", &word(pp.u));
    tr.absorb(b"v", &word(v));
    tr.absorb(b"b", &b.to_le_bytes());
    let alpha = scalar(&mut tr);

    // The prover forms s̃_α = s ∘ α and commits its decomposition, per
    // repetition; those roots are what `r` is then bound to.
    let tilde = hadamard(
        &c.s,
        &pp_alpha(alpha).weight(ROUNDS).expect("alpha weights"),
    );
    let mut aux_roots = Vec::with_capacity(pp.aux.len());
    for chain in &pp.aux {
        let digits = split::<Q, D, 2, ELL>(&tilde);
        let (root, _) = chain.commit(&digits).expect("aux commit");
        absorb_rings::<Shake256Xof, Q, D>(&mut tr, b"cm-alpha", &root);
        aux_roots.push(root);
    }
    let r = scalar(&mut tr);
    Sealed {
        alpha,
        r,
        aux_roots,
        w_alpha: pp_alpha(alpha),
        w_r_alpha: LinearWeights::geometric(r * alpha, 1, ELL, ROUNDS).expect("r*alpha weights"),
        w_r_digit: LinearWeights::geometric(r, ELL, ELL * ELL, ROUNDS).expect("r digit weights"),
    }
}

/// `α⃗ = (1, α, …, α^{Nℓd−1})` as a tensor-structured weight (§3.3, p. 13).
fn pp_alpha(alpha: Q) -> LinearWeights<Q, D> {
    LinearWeights::geometric(alpha, 1, ELL, ROUNDS).expect("alpha weights")
}

/// Builds both bundles from a witness and the sealed weights.
fn bundles(
    pp: &Params,
    sealed: &Sealed,
    s: &[Elt<Q, D>],
) -> (MainBundle<Q, D, ELL>, Vec<BinaryBundle<Q, D, ELL>>) {
    let (main_tail, aux_tail) = tail_bounds();
    let tilde = hadamard(s, &sealed.w_alpha.weight(ROUNDS).expect("alpha weights"));
    let main = MainBundle::new(pp.main.clone(), s, pp.w_eval.clone(), B_SQ, main_tail)
        .expect("main bundle");
    let aux = pp
        .aux
        .iter()
        .map(|chain| {
            BinaryBundle::new(
                chain.clone(),
                &tilde,
                sealed.w_r_alpha.clone(),
                sealed.w_r_digit.clone(),
                sealed.w_alpha.clone(),
                aux_tail,
            )
            .expect("aux bundle")
        })
        .collect();
    (main, aux)
}

/// Every check that rejects this proof, as a set.
///
/// Under Fiat–Shamir each message is absorbed before the next challenge, so one
/// tamper cascades: a single-error verifier reports whichever check runs first
/// and leaves the rest indistinguishable from checks that never ran. Every
/// assertion below is therefore on the whole set.
fn failing(
    statement: &Statement<Q, D>,
    proof: &NormProof<Q, D>,
    main: &MainBundle<Q, D, ELL>,
    aux: &[BinaryBundle<Q, D, ELL>],
) -> BTreeSet<CheckId> {
    committed_norm::verify_report(statement, proof, main, aux, W1, W2)
        .iter()
        .map(|e| e.check_id(LOG_N))
        .collect()
}

/// Fig. 3's three main-column lanes, in the order the paper prints them.
const MAIN_LANES: [&str; 3] = ["commitment", "linear", "quadratic"];
/// Fig. 3's five lanes for one binary repetition: `π^(cm,α)`, the three linear
/// openings and the bilinear one (§3.3, p. 14; Fig. 3, p. 17 case 1).
const AUX_LANES: [&str; 5] = [
    "commitment",
    "aux-value",
    "aux-digit",
    "aux-binarity",
    "aux-quadratic",
];

/// Every check a message round runs.
fn round_checks(reps: usize, round: usize, into: &mut BTreeSet<CheckId>) {
    for lane in MAIN_LANES {
        into.insert(id(lane, Chain::Main, round));
    }
    for j in 0..reps {
        for lane in AUX_LANES {
            into.insert(id(lane, Chain::Binary(j), round));
        }
    }
}

/// The final round's transcript-reading checks: the two base openings, the base
/// pairings and the two quadratic base identities (Fig. 3, p. 17 case 3).
///
/// The norm-admissibility gates of case 3 are deliberately **not** here: they
/// compare a revealed vector against `γ`/`γ_α`, so an untouched tail stays
/// admissible however far the challenges moved. That distinction is the reason
/// `tail-short` needs its own tamper below rather than riding along with one.
fn final_checks(reps: usize, into: &mut BTreeSet<CheckId>) {
    for lane in MAIN_LANES {
        into.insert(id(lane, Chain::Main, LOG_N));
    }
    for j in 0..reps {
        for lane in AUX_LANES {
            into.insert(id(lane, Chain::Binary(j), LOG_N));
        }
    }
}

/// Everything Fiat–Shamir cascades a change made at (or before) message round
/// `through`: every later round's checks, because round `i` reads challenge
/// `c_{i−1}` and `c_{through}` moved, plus the final round's.
///
/// Round 1 is excluded by construction — it is the only round whose checks
/// read no challenge at all, so a statement-level tamper cannot hide behind it.
fn downstream(reps: usize, through: usize) -> BTreeSet<CheckId> {
    let mut set = BTreeSet::new();
    for round in (through + 1).max(2)..=ROUNDS {
        round_checks(reps, round, &mut set);
    }
    final_checks(reps, &mut set);
    set
}

/// One Fig. 3 check identity.
fn id(lane: &'static str, chain: Chain, round: usize) -> CheckId {
    CheckId { lane, chain, round }
}

/// §3.6, p. 21's component list, each part named and counted on its own, so a
/// discrepancy says *which* component is off and not only the total.
///
/// ```text
/// π_i , i ∈ [1 : log N − 1]   2κι     π^(cm)
///                            + 2      π^(lin)  = (v_L, v_R)
///                            + 4      π^(qua)  = (L, M₁, M₂, R)
///                            + t · (  2κι      π^(cm,α)
///                                   + 2        π^(lin1,α)
///                                   + 2        π^(lin2,α)
///                                   + 2        π^(lin3,α)
///                                   + 4        π^(qua,α) )
/// π_log N                       2ℓ    s⃗_log N ∈ R_q^{2ℓ}
///                            + 2tλι_α ŝ^(j)_α,log N ∈ R_q^{2λι}
/// ```
///
/// The `+10` per repetition is §3.3, p. 14's `π_i^(bin) ∈ R_q^{2κι+10}`, read
/// off the message it lists; dropping any one of the three linear openings
/// breaks both that sentence and the total below.
fn check_sizes(proof: &NormProof<Q, D>, reps: usize) {
    // `2κι`, one column's intermediate commitment (`B_i ∈ R_q^{κ×2κι}`, §3.3
    // p. 13, so the auxiliary column has the same width as the main one).
    let ki = 2 * KAPPA * ELL;
    assert_eq!(
        proof.rounds.len(),
        ROUNDS,
        "log N − 1 message rounds (Fig. 2)"
    );
    for (i, msg) in proof.rounds.iter().enumerate() {
        let round = i + 1;
        assert_eq!(
            msg.commit.len(),
            ki,
            "round {round}: π^(cm) is 2κι elements"
        );
        assert_eq!(msg.linear.len(), 2, "round {round}: π^(lin) = (v_L, v_R)");
        assert_eq!(msg.quad.len(), 4, "round {round}: π^(qua) = (L, M₁, M₂, R)");
        assert_eq!(msg.aux.len(), reps, "round {round}: t binary repetitions");
        for (j, a) in msg.aux.iter().enumerate() {
            assert_eq!(a.commit.len(), ki, "round {round} rep {j}: π^(cm,α)");
            assert_eq!(
                a.lin.len(),
                3,
                "round {round} rep {j}: π^(bin) carries lin1, lin2 and lin3"
            );
            assert!(
                a.lin.iter().all(|pair| pair.len() == 2),
                "round {round} rep {j}: each linear opening is (v_L, v_R)"
            );
            assert_eq!(a.quad.len(), 4, "round {round} rep {j}: π^(qua,α)");
        }
    }
    assert_eq!(proof.tail.len(), 2 * ELL, "π_logN: s⃗_log N ∈ R_q^{{2ℓ}}");
    assert_eq!(
        proof.aux_tails.len(),
        reps,
        "one auxiliary tail per repetition"
    );
    for (j, tail) in proof.aux_tails.iter().enumerate() {
        assert_eq!(
            tail.len(),
            2 * ELL * ELL,
            "π_logN: ŝ^({j})_α,log N ∈ R_q^{{2λι}}"
        );
    }
    let per_round = ki + 2 + 4 + reps * (ki + 2 * 3 + 4);
    let final_round = 2 * ELL + 2 * reps * ELL * ELL;
    let formula = ROUNDS * per_round + final_round;
    let actual = committed_norm::proof_size(proof);
    assert_eq!(
        actual, formula,
        "the transcript must be exactly the shape §3.6 counts"
    );
    println!(
        "  size: {actual} ring elements = (log N−1)·[(2κι={ki})+2+4+t·((2κι={ki})+3·2+4)] \
         + (2ℓ={}) + 2tℓι={} — every component above counted separately, \
         {} bits at d·log q = {} per element",
        2 * ELL,
        2 * reps * ELL * ELL,
        actual * D * 12,
        D * 12,
    );
}

/// The whole scheme: honest proof, then one named tamper per Fig. 3 column.
fn scheme_lane() -> Result<(), String> {
    println!(
        "Serval evaluation proof (Fig. 2/3/4): q = {MODULUS}, d = {D}, N = {N}, \
         ℓ = ι = {ELL}, κ = {KAPPA}, pool P_{{{W1},{W2}}}"
    );
    check_instance();
    check_lemma_2_window();
    let f = polynomial();
    let u = Q::from(123u64);
    let pp = setup(u);
    let c = commit(&pp, &f);
    let sealed = seal(&pp, &c);
    let (main, aux) = bundles(&pp, &sealed, &c.s);
    let (statement, proof) = committed_norm::prove(&main, &aux, W1, W2).expect("prove");
    // Fiat–Shamir ordering, checked against the objects rather than asserted in
    // prose: the commitments every challenge was drawn from are exactly the ones
    // the statement carries, so no second copy can be substituted after the draw.
    assert_eq!(
        statement.cm, c.cm,
        "cm must be what α was absorbed-and-drawn from"
    );
    assert_eq!(
        statement
            .aux
            .iter()
            .map(|a| a.root.clone())
            .collect::<Vec<_>>(),
        sealed.aux_roots,
        "cm_α must be what r was absorbed-and-drawn from"
    );
    let claimed = evaluate(&f, u);
    assert_eq!(
        statement.v, claimed,
        "the linear claim must be the evaluation f(u)"
    );
    assert_eq!(
        u128::from(statement.b),
        square_sum(&c.s).expect("norm"),
        "b must be the exact integer squared norm of the committed witness"
    );
    committed_norm::verify(&statement, &proof, &main, &aux, W1, W2)
        .map_err(|e| format!("honest proof rejected: {e}"))?;
    println!(
        "  honest proof verifies: {} message rounds, t = {} repetitions, \
         b = {}, v = f(u) = {}, α = {}, r = {}",
        proof.rounds.len(),
        pp.reps,
        statement.b,
        claimed.to_u128(),
        sealed.alpha.to_u128(),
        sealed.r.to_u128(),
    );
    check_sizes(&proof, pp.reps);
    let growth = NormAccounting {
        rounds: ROUNDS,
        t_op: T_OP,
        initial: 1,
        base_len: ELL * D,
    };
    let (beta_main, beta_aux) = growth.msis_bounds(N, ELL, ELL);
    println!(
        "  Theorem 1: γ_log N = {}, γ² on the revealed tail = {} ; \
         Eq. (4) needs β_M-SIS ≥ max({beta_main}, {beta_aux}) against q = {MODULUS} \
         → this instance demonstrates the protocol, not a security level",
        growth.coord_bound(),
        growth.bound_sq(),
    );
    tampers(&statement, &proof, &main, &aux, pp.reps)
}

/// The lanes [`committed_norm::verify_report`] can name, in Fig. 3's order, for
/// a compact rendering of a failing set.
const LANE_ORDER: [&str; 13] = [
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
    "tail-short",
    "shape",
    "setup",
];

/// A failing set as `lane@{rounds} (entries)`, one group per lane.
fn summarise(set: &BTreeSet<CheckId>) -> String {
    let mut out = Vec::new();
    for lane in LANE_ORDER {
        let rounds: BTreeSet<usize> = set
            .iter()
            .filter(|c| c.lane == lane)
            .map(|c| c.round)
            .collect();
        if !rounds.is_empty() {
            out.push(format!(
                "{lane}@{rounds:?} ({})",
                set.iter().filter(|c| c.lane == lane).count()
            ));
        }
    }
    out.join(" ")
}

/// One tamper: what it edits, and the **whole** set of Fig. 3 checks it must
/// break. The set is derived from the paper's check schedule, not snapshotted
/// from output — see [`downstream`].
type Case = (
    &'static str,
    fn(&mut Statement<Q, D>, &mut NormProof<Q, D>),
    BTreeSet<CheckId>,
);

/// One tamper per component Fig. 3 checks, each asserted against its exact
/// failing set, plus the coverage argument that no column is dead code.
fn tampers(
    statement: &Statement<Q, D>,
    proof: &NormProof<Q, D>,
    main: &MainBundle<Q, D, ELL>,
    aux: &[BinaryBundle<Q, D, ELL>],
    reps: usize,
) -> Result<(), String> {
    // Every final-round check that reads the *main* revealed tail: its own base
    // opening and pairings, and the auxiliary lanes whose Fig. 3 case-3
    // identity has `s_log N` in one of its two slots.
    let main_tail_reads = {
        let mut s: BTreeSet<CheckId> = BTreeSet::new();
        for lane in MAIN_LANES {
            s.insert(id(lane, Chain::Main, LOG_N));
        }
        for j in 0..reps {
            for lane in ["aux-value", "aux-binarity", "aux-quadratic"] {
                s.insert(id(lane, Chain::Binary(j), LOG_N));
            }
        }
        s
    };
    // …and the ones that read repetition 0's auxiliary tail.
    let aux_tail_reads = {
        let mut s: BTreeSet<CheckId> = BTreeSet::new();
        for lane in ["commitment", "aux-digit", "aux-quadratic"] {
            s.insert(id(lane, Chain::Binary(0), LOG_N));
        }
        s
    };
    // A tamper inside message round 1 moves `c₁`, hence every check from round 2
    // on; the entry it edits fails at round 1 only if round 1 actually reads it.
    type Edit = fn(&mut Statement<Q, D>, &mut NormProof<Q, D>);
    let at_round_1 = |name: &'static str, edit: Edit, direct: CheckId| -> Case {
        let mut set = downstream(reps, 1);
        set.insert(direct);
        (name, edit, set)
    };
    let cases: Vec<Case> = vec![
        at_round_1(
            "round-1 main commitment",
            |_, p| p.rounds[0].commit[0] = p.rounds[0].commit[0].clone() + one(),
            id("commitment", Chain::Main, 1),
        ),
        at_round_1(
            "round-1 linear message",
            |_, p| p.rounds[0].linear[0] = p.rounds[0].linear[0].clone() + one(),
            id("linear", Chain::Main, 1),
        ),
        at_round_1(
            "round-1 quadratic message (R)",
            |_, p| p.rounds[0].quad[3] = p.rounds[0].quad[3].clone() + one(),
            id("quadratic", Chain::Main, 1),
        ),
        // A cross term `M₁` of the *first* round: Fig. 3 case 1 constrains only
        // `ct(L₁ + R₁) = b`, so nothing at round 1 reads it and its own round
        // must NOT appear in the set — the cascade from `c₁` is the only thing
        // that can see it, and it sees all of it.
        (
            "round-1 quadratic cross term (M₁)",
            |_, p| p.rounds[0].quad[1] = p.rounds[0].quad[1].clone() + one(),
            downstream(reps, 1),
        ),
        at_round_1(
            "round-1 aux commitment",
            |_, p| p.rounds[0].aux[0].commit[0] = p.rounds[0].aux[0].commit[0].clone() + one(),
            id("commitment", Chain::Binary(0), 1),
        ),
        at_round_1(
            "round-1 aux digit lane (lin2)",
            |_, p| p.rounds[0].aux[0].lin[1][1] = p.rounds[0].aux[0].lin[1][1].clone() + one(),
            id("aux-digit", Chain::Binary(0), 1),
        ),
        at_round_1(
            "round-1 aux binarity lane (lin3)",
            |_, p| p.rounds[0].aux[0].lin[2][0] = p.rounds[0].aux[0].lin[2][0].clone() + one(),
            id("aux-binarity", Chain::Binary(0), 1),
        ),
        at_round_1(
            "round-1 aux value lane (lin1)",
            |_, p| p.rounds[0].aux[0].lin[0][0] = p.rounds[0].aux[0].lin[0][0].clone() + one(),
            id("aux-value", Chain::Binary(0), 1),
        ),
        at_round_1(
            "round-1 aux bilinear message (L)",
            |_, p| p.rounds[0].aux[0].quad[0] = p.rounds[0].aux[0].quad[0].clone() + one(),
            id("aux-quadratic", Chain::Binary(0), 1),
        ),
        // The last message round's cross terms: no check of their own anywhere,
        // because case 3's bilinear identities — whose weight vector
        // `c^(qua) = (c₀σ(c₀), c₀σ(c₁), c₁σ(c₀), c₁σ(c₁))` has all four entries
        // non-zero — are what pin them. So the exact set is the final round and
        // nothing else.
        (
            "last-round quadratic cross term",
            |_, p| p.rounds[ROUNDS - 1].quad[1] = p.rounds[ROUNDS - 1].quad[1].clone() + one(),
            downstream(reps, ROUNDS),
        ),
        (
            "last-round aux bilinear cross term",
            |_, p| {
                p.rounds[ROUNDS - 1].aux[0].quad[1] =
                    p.rounds[ROUNDS - 1].aux[0].quad[1].clone() + one()
            },
            downstream(reps, ROUNDS),
        ),
        // The revealed tails are not absorbed into any challenge, so they move
        // nothing upstream: only the final round can see them.
        (
            "revealed main tail",
            |_, p| p.tail[0] = p.tail[0].clone() + one(),
            main_tail_reads.clone(),
        ),
        (
            "revealed aux tail",
            |_, p| p.aux_tails[0][0] = p.aux_tails[0][0].clone() + one(),
            aux_tail_reads.clone(),
        ),
        // Fig. 3 case 3's first line, `‖s_log N‖ ≤ γ ∧ ‖ŝ_α,log N‖ ≤ γ_α`, gates
        // on a *value*, not on a challenge, so it needs a tail that is actually
        // too long. Without these two cases the gate is untested code.
        (
            "revealed main tail above γ",
            |_, p| p.tail = p.tail.iter().map(|_| huge()).collect(),
            {
                let mut s = main_tail_reads.clone();
                s.insert(id("tail-short", Chain::Main, LOG_N));
                s
            },
        ),
        (
            "revealed aux tail above γ_α",
            |_, p| p.aux_tails[0] = p.aux_tails[0].iter().map(|_| huge()).collect(),
            {
                let mut s = aux_tail_reads.clone();
                s.insert(id("tail-short", Chain::Binary(0), LOG_N));
                s
            },
        ),
        // Statement-level forgeries move the challenge too — `challenge_at`
        // absorbs `b` and all three auxiliary claims before any message — so
        // their sets are the round-2-onward cascade plus the round-1 check that
        // reads the tampered claim.
        (
            "oversized norm claim (b > B²)",
            |s, _| s.b = u64::try_from(B_SQ + 1).expect("fits"),
            {
                let mut set = downstream(reps, 0);
                set.insert(id("statement-bound", Chain::Main, 0));
                set.insert(id("quadratic", Chain::Main, 1));
                set
            },
        ),
        (
            "digit-side claim (v_r' ≠ v_r)",
            |s, _| s.aux[0].claims.v_r_prime += Q::ONE,
            {
                let mut set = downstream(reps, 0);
                set.insert(id("well-formed", Chain::Binary(0), 0));
                set.insert(id("aux-digit", Chain::Binary(0), 1));
                set
            },
        ),
    ];
    let mut seen: BTreeSet<CheckId> = BTreeSet::new();
    for (name, edit, expected) in cases {
        let mut st = statement.clone();
        let mut p = proof.clone();
        edit(&mut st, &mut p);
        let set = failing(&st, &p, main, aux);
        if set != expected {
            let missing: Vec<String> = expected.difference(&set).map(|c| c.to_string()).collect();
            let extra: Vec<String> = set.difference(&expected).map(|c| c.to_string()).collect();
            return Err(format!(
                "tamper `{name}`: expected {} checks, got {}.\n    not fired: {missing:?}\n    unexpected: {extra:?}",
                expected.len(),
                set.len()
            ));
        }
        println!("  tamper {:38} → {}", name, summarise(&set));
        seen.extend(set);
    }
    // Every Fig. 3 column must appear in some report, or it is dead code. The
    // three lanes of [`LANE_ORDER`] *not* listed here are deliberate:
    // `wraparound` needs `B² ≥ q`, which [`check_lemma_2_window`] asserts this
    // instance does not have, and `shape`/`setup` need malformed inputs rather
    // than forgeries — all three are exercised in `shortness::committed_norm`'s
    // own tests (`a_bound_reaching_the_modulus_voids_the_norm_claim`,
    // `an_inconsistent_bundle_is_refused_before_any_crypto_runs`).
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
        "tail-short",
    ] {
        if !seen.iter().any(|c| c.lane == lane) {
            return Err(format!("{lane} never fired in any tamper: {seen:?}"));
        }
    }
    println!("  every Fig. 3 column fired for some tamper (10 lanes)");
    Ok(())
}

/// `1` as a ring element, for the tampers.
fn one() -> Elt<Q, D> {
    Elt::from_coefficients(vec![Q::ONE, Q::ZERO, Q::ZERO, Q::ZERO])
}

/// The largest-magnitude ring element, every coefficient at `⌊q/2⌋`: one of
/// these already exceeds Theorem 1's squared tail bound, which is what the
/// `tail-short` gate needs.
fn huge() -> Elt<Q, D> {
    Elt::from_coefficients(vec![Q::from((MODULUS - 1) / 2); D])
}

/// The gap the leveled commitment closes.
///
/// This runs on the crate's canonical ring instance (`d = 256`, `ℓ = 23`)
/// because that is the instance [`zk::shortness::self_ip`] is written against —
/// its generic twin is `tensor_fold::herm`, and `committed_norm` uses that. The
/// scheme above is generic over `(R, d)` and uses the small prime so the
/// auxiliary `ℓ·ι`-plane chain stays interactive.
fn binding_lane() -> Result<(), String> {
    use zk::foundation::encoding::ring_from_u32;
    use zk::pcs::{RingElt, Z1Coeff, DELTA, DIM};
    println!(
        "\nBinding: the same norm claim with and without the leveled chain \
         (d = {DIM}, q = {}, ℓ = {DELTA})",
        Z1Coeff::MODULUS
    );
    let chain: LeveledAjtai<Z1Coeff, DIM, DELTA> =
        LeveledAjtai::setup(b"serval/binding", &[0x37u8; 32], 2, 4, DELTA).expect("chain");
    let rounds = chain.levels() - 1;
    let digit = |bit: u32| -> RingElt {
        let mut coeffs = [0u32; DIM];
        coeffs[0] = bit;
        ring_from_u32::<Z1Coeff, DIM>(&coeffs)
    };
    // Two witnesses that are permutations of each other: identical squared norm
    // `b`, different committed vectors.
    let base: Vec<RingElt> = (0..chain.witness_len())
        .map(|i| digit(u32::from(i % 3 == 0)))
        .collect();
    let mut s1 = base.clone();
    let mut s2 = base;
    s1[0] = digit(1);
    s1[1] = digit(0);
    s2[0] = digit(0);
    s2[1] = digit(1);
    let (b1, _proof1) = self_ip::prove(&s1, rounds).expect("prove s1");
    let (b2, proof2) = self_ip::prove(&s2, rounds).expect("prove s2");
    assert_eq!(b1, b2, "permutations must have the same squared norm");
    self_ip::verify(b1, &proof2, u64::MAX)
        .map_err(|e| format!("the unbound argument refused a permutation: {e}"))?;
    println!(
        "  unbound self_ip accepts s2's proof under the claim b = {b1} \
         that was derived from s1 — it proves consistency, not binding"
    );
    let (b1, cm1, bound1) = self_ip::prove_bound(&chain, &s1, W1, W2).expect("prove_bound s1");
    let (b2, cm2, bound2) = self_ip::prove_bound(&chain, &s2, W1, W2).expect("prove_bound s2");
    assert_ne!(cm1, cm2, "the two witnesses must commit differently");
    // Theorem 1's bound for this pool: γ_log N = (2T)^{log N − 1}, and the
    // revealed tail holds 2·ℓ ring elements of degree d.
    let growth = NormAccounting {
        rounds,
        t_op: T_OP,
        initial: 1,
        base_len: DELTA * DIM / 2,
    };
    let tail_bound = growth.bound_sq();
    self_ip::verify_bound(&chain, &cm1, b1, &bound1, tail_bound, W1, W2)
        .map_err(|e| format!("honest bound proof rejected: {e}"))?;
    println!("  bound proof verifies against its own root (γ² = {tail_bound})");
    let report = self_ip::bound_report(&chain, &cm1, b2, &bound2, tail_bound, W1, W2);
    assert_eq!(
        report,
        vec![self_ip::SelfIpError::Binding(
            zk::pcs::leveled::LeveledError::RootMismatch { round: 1 },
        )],
        "s2's bound proof under s1's root must be refused by the root opening \
         and by nothing else; got {report:?}"
    );
    println!(
        "  s2's bound proof under s1's root → {}",
        report
            .iter()
            .map(|e| format!("{e}"))
            .collect::<Vec<_>>()
            .join(" | ")
    );
    // The informative forgery: an honest chain column for s1 spliced with an
    // honest quadratic column for s2. Each column satisfies its own equations,
    // so a verifier that runs only the quadratic column has nothing to refuse —
    // for *this* witness class that is not a coincidence but arithmetic: the
    // digits are 0/1 in the constant slot and the two halves never align
    // (`46 ≡ 1 (mod 3)`), so `M₁ = M₂ = 0`, and every element of the pool
    // `P_{1,1}` has `ct(cσ(c)) = w₁ + 4w₂ = 5`, so the carried claim is
    // `5·(L + R) = 5b` for **every** challenge. The one check that can see the
    // swap is the base opening `A₀ · s_log N = …`, which is exactly the step
    // that authenticates the tail the terminal identity is read off (Fig. 3,
    // p. 17, case 3, and Appendix C step I, p. 37–39).
    let mut mixed = bound1;
    mixed.ip = bound2.ip;
    let report = self_ip::bound_report(&chain, &cm1, b1, &mixed, tail_bound, W1, W2);
    assert_eq!(
        report,
        vec![self_ip::SelfIpError::Binding(
            zk::pcs::leveled::LeveledError::LevelMismatch { level: 0 },
        )],
        "a proof whose two columns fold different vectors must die on the base \
         opening; got {report:?}"
    );
    let names: BTreeSet<String> = report.iter().map(|e| format!("{e}")).collect();
    println!("  spliced columns (chain of s1, quadratic of s2) → {names:?}");
    Ok(())
}

fn main() {
    if let Err(e) = scheme_lane() {
        eprintln!("serval: scheme lane failed: {e}");
        process::exit(1);
    }
    if let Err(e) = binding_lane() {
        eprintln!("serval: binding lane failed: {e}");
        process::exit(1);
    }
    println!("\nserval: every lane completed");
}
