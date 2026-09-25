//! SLAP — Albrecht–Fenzi–Lapiha–Nguyen, *SLAP: Succinct Lattice-Based
//! Polynomial Commitments from Standard Assumptions*, eprint 2023/1469 — as a
//! scheme assembly: **Fig. 4** (the Merkle-PRISIS commitment, p. 29) plus
//! **Fig. 5** (the recursive split-and-fold evaluation protocol, p. 35), made
//! non-interactive with Fiat–Shamir as §5.3's Theorem 5.10 prescribes.
//!
//! Like [`cmnw`](cmnw) and [`hachi`](hachi), this file holds no cryptographic
//! logic. `TrapGen`/`SamplePre` come from [`zk::pcs::trapdoor`]; the per-level
//! basis `B_j = [[A_j,0,−G],[0,w_j A_j,−G]]`, the tree commitment and Fig. 4's
//! `Open` from [`zk::pcs::prisis`]; and the decommitment layout, the round
//! algebra and the base-case relation `R^{(r)}_{l,β}` from
//! [`zk::pcs::slap_tree`]. What lives here is the instance, the message order,
//! the transcript and the tampers.
//!
//! # What the scheme is, read off the paper
//!
//! * **Commitment** (Fig. 4). `Setup` runs, for `j = h … 1`,
//!   `(A, R) ← TrapGen(n, m)`, `w ← R_q^×`, `R_i := R·G⁻¹(w⁻ⁱG)`,
//!   `R̃ = [R₀; R₁; 0]` with `B_j·R̃ = G_{2n}`, then
//!   `T_j ← SamplePre(B_j, R̃_j, G_{2n}, σ₀)`. `Commit` sets the leaves
//!   `t_b := f_b·e₁` and, for `j = h … 1` and every node `b ∈ Z₂^{j−1}`, samples
//!   `(s_{(b,0)}, s_{(b,1)}, t̂_b) ← SamplePre(B_j, (−t_{(b,0)}, −t_{(b,1)}), T_j, σ₁)`
//!   and **defines the parent as `t_b := G·t̂_b`**. The root is the commitment.
//! * **Opening is additive, not a sibling path.** Fig. 4's `Open` accepts iff
//!   for the leaf `b`: `Σ_{j=1}^{h} w_j^{b_j}·A_j·s_{b:j} + f_b·e₁ = t`. Each
//!   `G·t̂` appears with a `+` in one child's equation and is the shared value of
//!   the other, so the chain telescopes and **no digest of any sibling is ever
//!   sent**. Checked here twice over: per node
//!   ([`zk::pcs::prisis::PrisisTree::failing_levels`]) and per leaf as one sum
//!   ([`zk::pcs::prisis::PrisisTree::failing`]), and again on the *folded*
//!   instance by [`zk::pcs::slap_tree::FoldInstance::verify_final`].
//! * **Split-and-fold** (Fig. 2 p. 10, Fig. 5 p. 35). A round of factor `k`
//!   splits by the low `k` index bits (`f(X) = Σ_{i<2^k} X^i f̄_i(X^{2^k})`,
//!   §5.1 p. 32's `int((i,j)) = int(i) + 2^k int(j)`), sends the `2^k` partial
//!   evaluations plus the openings of the `k` topmost levels, and then folds
//!   *everything* — coefficients, level blocks, commitment, claim — under
//!   monomial challenges `α ← (X^r)^{r2^k}`. The successor is the same relation
//!   with `h − k` levels and slack `(r2^k)β`. No new preimage is sampled: §5.1's
//!   Eq. (7) *is* the statement that the fold of the openings opens the fold of
//!   the commitment. This differs from LatticeFold's fold, which folds a
//!   sumcheck claim and re-commits: here the commitment itself is the folded
//!   object, and the tree's level matrices are *consumed*, `k` per round.
//! * **Cost** (Lemma 5.9 p. 42; Table 4 p. 53). Verifier
//!   `O(ℓ·2^k n(km + r²) + r·2^{h−kℓ})` ring operations; the paper's own row for
//!   `d = 2²⁰, λ = 128` is `n = 162, m = 2329, N = 64, δ = 22, log q = 276,
//!   β = 258` at **36.5 MB**, and `d = 2³⁰` is 767 MB. The paper states its own
//!   verdict: "the resulting parameters are rather large, and thus we cannot
//!   claim that our scheme achieves concrete efficiency" (p. 53).
//!
//! # Instance — a structural demonstration, not a security level
//!
//! SLAP needs `log₂ q ≈ 276` because the extracted norm `β` is large, and this
//! crate's [`zk::foundation::encoding`] is `u32`-bounded, so such a modulus
//! cannot even be absorbed into a transcript. Following
//! [`cmnw`](cmnw)/[`hachi`](hachi)/[`labrador`](labrador), the assembly runs on
//! `q = 2³² − 99`: prime, `≡ 5 (mod 8)`, 2-adicity 2, so by
//! `algebra::ring::number_theory::x_pow_d_plus_1_splitting` `X^64 + 1` does
//! **not** split into linear factors and no NTT-backed key exists — which is
//! fine, because SLAP's `A_j` is a `TrapGen` output and
//! [`zk::pcs::key::RingMatrixKey`] multiplies schoolbook anyway. With
//! `d = 64, n = 1, m = 36, h = 4, k = 1, ℓ = 2, r = 1` the example stays
//! interactive. `log q = 32` here vs 276 there: **this demonstrates the
//! protocol, not a security parameter.**
//!
//! Three deliberate deviations, each structural rather than numerical:
//!
//! 1. **The gadget is the binary one**, `G = Iₙ ⊗ [1, 2, …, 2³¹]`, exactly
//!    SLAP's Fig. 1 and FMN's Fig. 4 `G := G_n`, at the cost of `t = 32n`
//!    columns instead of the papers' `δ̃ = ⌊log_δ q⌋ + 1` for their own base
//!    `δ`. A wider base is *available* here ([`zk::pcs::gadget::split`] is
//!    generic in `(BASE, DIGITS)`), but no even base with few enough planes is
//!    exact at this modulus: `digit_planes`' rounding yields digits in
//!    `[[−(BASE/2−1), BASE/2]]`, so e.g. `base 256, 4 planes` reaches
//!    `−2.139·10⁹` and cannot reach `−(q−1)/2 = −2.147·10⁹`, while its reported
//!    `digit_span` says `2.156·10⁹` — see the note in this task's report. Base 2
//!    has digit set `{0, 1}` over the canonical representative and is exact.
//! 2. **`SamplePre` is the deterministic `p = 0` form** of
//!    [`zk::pcs::trapdoor`], licensed by §6's "Deterministic preimage sampling"
//!    (p. 52–53): `v := T·G⁻¹(t)`. The CRS trapdoor must still be *randomised*
//!    (the nonzero perturbation below), because `R̃`'s closing block is zero and
//!    with `T = R̃` every parent commitment collapses to `0`.
//! 3. **`w_j` is a scalar unit** (`W = w·Iₙ`, PRISIS's own shape: 2023/846 §3
//!    p. 30, "PRISIS is the instance where each `W_i := w^{i−1} I_{n+1}`"),
//!    drawn through [`zk::pcs::trapdoor::UnitMatrix::scalar_units`] — a
//!    subfamily of `GL(n, R_q)`, not a uniform draw, because the crate has no
//!    linear solver over `R_q`.
//!
//! Also *not* assembled: §3's re-randomisation (the h-PRISIS → Module-SIS
//! reduction), §5.4's zero-knowledge simulation (it needs MP12's Gaussian
//! `SampleD`), and §6's `d/N` scalar-coefficient lift (Lemma 5.16). None of them
//! changes an equation this proof checks.
//!
//! Run with: `cargo run -p lattice-zk --example slap`

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::Ring;
use std::collections::BTreeSet;
use zk::foundation::fs::{absorb_rings, seed_stream};
use zk::pcs::key::RingMatrixKey;
use zk::pcs::prisis::{poly_eval, PrisisTree};
use zk::pcs::slap_tree::{
    leaves_in_tree_order, path_bits, tree_keys, Alpha, FinalMessage, FoldInstance, RoundMessage,
    TreeOpenings,
};
use zk::pcs::trapdoor::{scalar_elt, vector_infinity_norm};

/// `2³² − 99`: prime, `≡ 5 (mod 8)`, `u32`-encodable, and without an NTT.
type Q = Zq<4294967197>;
/// Ring degree `d`.
const D: usize = 64;
type Elt_ = PolyRing<Q, D>;

/// Gadget: the **binary** one, `G = Iₙ ⊗ [1, 2, …, 2³¹]` — MP12's and both
/// papers' `g`, digits `{0,1}` over the canonical representative, exact since
/// `2³² > q` (see the deviation note in the header for why no wider base with
/// fewer planes is safe here).
const BASE: u64 = 2;
const DIGITS: usize = 32;
/// Module rank `n`: rows of every `A_j`, and the height of `G = G_n`.
const N: usize = 1;
/// Columns of `A_j`'s uniform half; `m = mbar + n·DIGITS`.
const MBAR: usize = 4;
/// Tree height `h`: the polynomial has `2^h` coefficients.
const H: usize = 4;
/// Folding factor `k`, its `kk = 2^k`, and the round count `ℓ`.
const K: usize = 1;
const KK: usize = 1 << K;
const ROUNDS: usize = 2;
/// Amortisation parameter `r` of `R^{(r)}_{h,β}`. Theorem 5.10's `Eval` runs the
/// protocol with `f_{0,1} = … = f_{0,r}` (footnote 11, p. 43), so `r = 1` *is*
/// the single-evaluation polynomial commitment.
const CLAIMS: usize = 1;
/// `X^r`: exponents are multiples of `CLAIMS`. `CLAIMS ≥ 1` by construction.
const ALPHA_POWER: usize = CLAIMS;
/// Perturbation of the CRS trapdoor randomisation (deviation 2).
const CRS_PERTURBATION: u32 = 1;
/// Levels surviving the `ROUNDS` rounds, and the folded degree bound.
const LEVELS_LEFT: usize = H - ROUNDS * K;
const FINAL_COEFFS: usize = 1 << LEVELS_LEFT;

/// The public statement: the level keys, the commitment, the point, the claim,
/// and the starting slack.
#[derive(Clone)]
struct Instance {
    a: Vec<RingMatrixKey<Q, D>>,
    w: Vec<RingMatrixKey<Q, D>>,
    root: Vec<Elt_>,
    u: Elt_,
    z: Elt_,
    beta: u64,
}

/// Fig. 4's CRS `(A_j, w_j, T_j)_{j∈[h]}`. `T_j` stays inside the tree object,
/// where only `Commit` can reach it (see [`zk::pcs::prisis::PrisisLevel::pair`]).
struct Crs {
    tree: PrisisTree<Q, D, BASE, DIGITS>,
}

/// The evaluation proof: one Fig. 5 item 2(d) message per round, then item 3's.
#[derive(Clone)]
struct Proof {
    rounds: Vec<RoundMessage<Q, D>>,
    last: FinalMessage<Q, D>,
}

/// Fig. 4 `Setup(1^λ)`.
fn setup(seed: &[u8; 32]) -> Crs {
    Crs {
        tree: PrisisTree::setup(seed, N, MBAR, H, CRS_PERTURBATION),
    }
}

/// The Fiat–Shamir chain: prover and verifier walk the **same** functions in the
/// same order, absorbing each message before squeezing the challenge that
/// follows it.
struct Fs {
    tr: Transcript<Shake256Xof>,
}

impl Fs {
    fn new(inst: &Instance, crs: &Crs) -> Self {
        let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/slap");
        for j in 1..=H {
            let level = crs.tree.level(j).expect("levels are 1-based");
            for i in 0..level.pair().a().rows() {
                absorb_rings(&mut tr, b"crs-a", level.pair().a().row(i));
            }
            for i in 0..inst.a[j - 1].rows() {
                absorb_rings(&mut tr, b"crs-w", inst.w[j - 1].row(i));
            }
        }
        absorb_rings(&mut tr, b"t", &inst.root);
        absorb_rings(&mut tr, b"u", &[inst.u.clone()]);
        absorb_rings(&mut tr, b"z", &[inst.z.clone()]);
        Self { tr }
    }

    /// Fig. 5 item 2(d) → 2(e): absorb the round's message, then `α ← (X^r)^{r2^k}`.
    fn alpha(&mut self, msg: &RoundMessage<Q, D>, round: usize) -> Alpha<Q, D> {
        for zi in &msg.z {
            absorb_rings(&mut self.tr, b"z-partial", zi);
        }
        for levels in &msg.blocks {
            for array in levels {
                for block in array {
                    absorb_rings(&mut self.tr, b"s-block", block);
                }
            }
        }
        self.tr
            .absorb(b"round", &(round as u64).to_le_bytes());
        let seed: [u8; 32] = {
            let mut out = [0u8; 32];
            out.copy_from_slice(&self.tr.challenge_bytes(32));
            out
        };
        let mut xof = seed_stream::<Shake256Xof>(b"slap-alpha", &seed);
        Alpha::sample(CLAIMS, KK, ALPHA_POWER, &mut xof)
    }
}

/// The root commitment of `coeffs` (SLAP's index convention: bit `0` of the
/// coefficient index is `b₁`, the parity split that Fig. 2 makes first).
fn commit(crs: &Crs, coeffs: &[Elt_]) -> (Vec<Elt_>, TreeOpenings<Q, D>) {
    let proof = crs.tree.commit(&leaves_in_tree_order(coeffs));
    let openings = TreeOpenings::from_proof(&crs.tree, &proof).expect("layout");
    (proof.root, openings)
}

/// The public statement of `f(u) = z` over that commitment.
fn statement(crs: &Crs, root: &[Elt_], u: &Elt_, z: &Elt_) -> Instance {
    let (a, w) = tree_keys(&crs.tree);
    Instance {
        a,
        w,
        root: root.to_vec(),
        u: u.clone(),
        z: z.clone(),
        beta: crs.tree.certified_bound(),
    }
}

/// Fig. 4 `Commit` + Fig. 5 `Eval`.
fn prove(crs: &Crs, inst: &Instance, coeffs: &[Elt_], openings: &TreeOpenings<Q, D>) -> Proof {
    let mut cur = FoldInstance::new(
        0,
        &inst.a,
        &inst.w,
        &inst.u,
        inst.beta,
        &[inst.root.clone()],
        &[inst.z.clone()],
        &[coeffs.to_vec()],
        Some(vec![openings.clone()]),
    )
    .expect("shapes");
    let mut fs = Fs::new(inst, crs);
    let mut rounds = Vec::with_capacity(ROUNDS);
    for _ in 0..ROUNDS {
        let msg = cur.prover_round(KK).expect("prover message");
        let alpha = fs.alpha(&msg, cur.round());
        cur = cur.fold_round(&msg, &alpha).expect("round").next;
        rounds.push(msg);
    }
    Proof {
        rounds,
        last: cur.final_message().expect("final message"),
    }
}

/// Every check the verifier runs, **without short-circuiting**, as the names
/// that did not hold.
///
/// The verifier holds only `(A_j, w_j)` and the public `(t, u, z)`: it rebuilds
/// each round's `α` from the messages it actually received, so one tamper on an
/// absorbed message re-derives every later challenge and cascades. Reporting the
/// whole set is what lets [`main`] attribute each tamper to the equations it
/// really violates — the pattern [`zk::pcs::dotproduct::verify_core_report`]
/// established.
fn failing(crs: &Crs, inst: &Instance, proof: &Proof) -> Vec<String> {
    let mut cur =
        FoldInstance::statement(
            0,
            &inst.a,
            &inst.w,
            &inst.u,
            inst.beta,
            &[inst.root.clone()],
            &[inst.z.clone()],
        )
        .expect("public statement");
    let mut fs = Fs::new(inst, crs);
    let mut bad = Vec::new();
    for msg in &proof.rounds {
        let alpha = fs.alpha(msg, cur.round());
        let out = cur.fold_round(msg, &alpha).expect("well-shaped message");
        bad.extend(out.failing);
        cur = out.next;
    }
    bad.extend(
        cur.verify_final(&proof.last)
            .expect("well-shaped final message"),
    );
    bad
}

/// The verifier: accept only when every check holds.
fn verify(crs: &Crs, inst: &Instance, proof: &Proof) -> Result<(), String> {
    let bad = failing(crs, inst, proof);
    if bad.is_empty() {
        Ok(())
    } else {
        Err(bad[0].clone())
    }
}

/// Proof size in bytes, for `docs/survey-lattice-pcs.md`'s comparison column.
fn proof_bytes(proof: &Proof) -> usize {
    let mut elts = 0;
    for msg in &proof.rounds {
        for zi in &msg.z {
            elts += zi.len();
        }
        for levels in &msg.blocks {
            for array in levels {
                for block in array {
                    elts += block.len();
                }
            }
        }
    }
    for c in &proof.last.coeffs {
        elts += c.len();
    }
    for op in &proof.last.openings {
        for t in 0..op.height() {
            for block in op.level(t) {
                elts += block.len();
            }
        }
    }
    elts * D * 4
}

/// The largest opening norm the honest proof actually carries.
fn max_opening_norm(proof: &Proof) -> u64 {
    let mut best = 0;
    for msg in &proof.rounds {
        for levels in &msg.blocks {
            for array in levels {
                for block in array {
                    best = best.max(vector_infinity_norm(block));
                }
            }
        }
    }
    for op in &proof.last.openings {
        for t in 0..op.height() {
            for block in op.level(t) {
                best = best.max(vector_infinity_norm(block));
            }
        }
    }
    best
}

/// A copy of a level array with one block **shifted** by `delta`: an additive
/// tamper can never be a no-op, whatever the block already held.
fn shift_block(
    op: &TreeOpenings<Q, D>,
    level: usize,
    path: usize,
    delta: u64,
) -> TreeOpenings<Q, D> {
    let mut levels: Vec<Vec<Vec<Elt_>>> = (0..op.height()).map(|t| op.level(t).to_vec()).collect();
    let d = scalar_elt::<Q, D>(Q::from(delta));
    levels[level][path][0] = levels[level][path][0].clone() + d;
    TreeOpenings::from_levels(levels).expect("same shape")
}

/// A copy of a level array with one block's first coefficient **set** to
/// `value`, which is how a norm gate is tripped honestly: incrementing can wrap
/// a negative coefficient (stored as `q − x`) back inside the bound, so an
/// additive tamper proves nothing about a gate.
fn fatten_block(op: &TreeOpenings<Q, D>, level: usize, path: usize, value: u64) -> TreeOpenings<Q, D> {
    let mut levels: Vec<Vec<Vec<Elt_>>> = (0..op.height()).map(|t| op.level(t).to_vec()).collect();
    levels[level][path][0] = scalar_elt::<Q, D>(Q::from(value));
    TreeOpenings::from_levels(levels).expect("same shape")
}

/// Assert a tamper is rejected by **exactly** `expected`, and nothing else.
fn expect_reject(
    label: &str,
    crs: &Crs,
    inst: &Instance,
    proof: &Proof,
    expected: &[&str],
) -> Vec<String> {
    let bad = failing(crs, inst, proof);
    assert!(!bad.is_empty(), "{label}: the tamper was accepted");
    let got: BTreeSet<&str> = bad.iter().map(String::as_str).collect();
    let want: BTreeSet<&str> = expected.iter().copied().collect();
    assert_eq!(got, want, "{label}: unexpected failing set {bad:?}");
    match verify(crs, inst, proof) {
        Err(first) => assert_eq!(first, bad[0], "{label}: attribution"),
        Ok(()) => panic!("{label}: the tamper verified"),
    }
    println!("  {label}\n      rejected by {bad:?}");
    bad
}

/// The check families of Figs. 4/5 as this assembly names them.
const FAMILIES: [&str; 5] = ["z-decompose", "norm", "eval", "root", "final-norm"];

fn family(name: &str) -> &'static str {
    for f in FAMILIES {
        if name.starts_with(f) {
            return match f {
                "z-decompose" => "z-decompose",
                "norm" => "norm",
                "eval" => "eval",
                "root" => "root",
                _ => "final-norm",
            };
        }
    }
    "other"
}

fn main() {
    let seed = [0x51u8; 32];
    let crs = setup(&seed);
    let coeffs: Vec<Elt_> = (0..1usize << H)
        .map(|i| scalar_elt::<Q, D>(Q::from(3 + 7 * i as u64)))
        .collect();
    let u = scalar_elt::<Q, D>(Q::from(17u64));
    let (root, openings) = commit(&crs, &coeffs);
    let z = poly_eval(&coeffs, &u);
    let inst = statement(&crs, &root, &u, &z);
    let beta = inst.beta;
    assert!(
        beta.saturating_mul(4) < (Q::MODULUS - 1) / 2,
        "the gate must sit inside the centered representative range to be testable: β = {beta}"
    );

    println!(
        "SLAP (eprint 2023/1469) Fig.4 + Fig.5 — q = 2^32-99, d = {D}, n = {N}, m = {}, h = {H}, k = {K}, l = {ROUNDS}, r = {CLAIMS}",
        MBAR + N * DIGITS
    );
    println!(
        "  structural demonstration only: Table 4 needs log q ≈ 276 (this instance has 32)"
    );
    println!("  certified opening slack β = {beta}, taken from the actual keys");

    // ---- Fig. 4: the commitment, and the additive opening it licenses --------
    let tree_proof = crs.tree.commit(&leaves_in_tree_order(&coeffs));
    for i in 0..coeffs.len() {
        let path = path_bits(i, H);
        let blocks = crs.tree.path_openings(&tree_proof, &path);
        assert!(
            crs.tree
                .failing(&root, &path, &coeffs[i], &blocks)
                .expect("shapes")
                .is_empty(),
            "Fig. 4's Open must accept leaf {i}"
        );
    }
    assert!(crs
        .tree
        .failing_levels(&tree_proof, &leaves_in_tree_order(&coeffs))
        .expect("shapes")
        .is_empty());
    println!(
        "  Fig. 4: {} node relations hold; the root opens additively at all {} leaves, no sibling path",
        tree_proof.nodes.len(),
        coeffs.len()
    );
    // One leaf, spelled out: Σ_j w_j^{b_j} A_j s_{b:j} + f_b e₁ = t.
    let path = path_bits(11, H);
    let blocks = crs.tree.path_openings(&tree_proof, &path);
    let bad = crs
        .tree
        .failing(&root, &path, &coeffs[11], &blocks)
        .expect("shapes");
    assert!(bad.is_empty());
    let broken = {
        let mut b = blocks.clone();
        b[2] = b[2]
            .iter()
            .enumerate()
            .map(|(k, v)| {
                if k == 0 {
                    v.clone() + scalar_elt::<Q, D>(Q::ONE)
                } else {
                    v.clone()
                }
            })
            .collect();
        b
    };
    assert_eq!(
        crs.tree.failing(&root, &path, &coeffs[11], &broken).expect("shapes"),
        vec!["root: sum_j w_j^b_j A_j s_b:j + f_b e1 = t".to_string()],
        "dropping one level out of the sum must break the accumulation"
    );
    println!("  Fig. 4 Open: withholding one level of leaf 11's path trips the accumulation");

    // ---- Fig. 5: the evaluation proof ---------------------------------------
    let proof = prove(&crs, &inst, &coeffs, &openings);
    let honest_bad = failing(&crs, &inst, &proof);
    assert!(honest_bad.is_empty(), "the honest proof must verify: {honest_bad:?}");
    println!(
        "  Fig. 5: {} rounds of kk = {KK} fold h = {H} levels down to {LEVELS_LEFT}, proof = {} bytes, honest opening norm ≤ {} ≤ β",
        ROUNDS,
        proof_bytes(&proof),
        max_opening_norm(&proof)
    );

    let mut tripped: Vec<&str> = Vec::new();
    let mut note = |bad: Vec<String>| {
        for name in bad {
            let f = family(&name);
            if !tripped.contains(&f) {
                tripped.push(f);
            }
        }
    };

    // A false claim `z`: absorbed before every challenge, so round 1's
    // recombination fails at once and every later α differs from the prover's.
    let wrong_claim = Instance {
        z: inst.z.clone() + scalar_elt::<Q, D>(Q::ONE),
        ..inst.clone()
    };
    note(expect_reject(
        "false claim z",
        &crs,
        &wrong_claim,
        &proof,
        &[
            "z-decompose(round 1,claim 0)",
            "z-decompose(round 2,claim 0)",
            "eval(claim 0)",
            "root(claim 0, leaf 0)",
            "root(claim 0, leaf 1)",
            "root(claim 0, leaf 2)",
            "root(claim 0, leaf 3)",
        ],
    ));

    // A false partial evaluation in round 1: the same cascade, because the
    // tamper is absorbed before the α that folds the tree.
    let mut lied_z = proof.clone();
    lied_z.rounds[0].z[0][0] =
        lied_z.rounds[0].z[0][0].clone() + scalar_elt::<Q, D>(Q::ONE);
    note(expect_reject(
        "false partial evaluation z_(round 1, i = 0)",
        &crs,
        &inst,
        &lied_z,
        &[
            "z-decompose(round 1,claim 0)",
            "z-decompose(round 2,claim 0)",
            "eval(claim 0)",
            "root(claim 0, leaf 0)",
            "root(claim 0, leaf 1)",
            "root(claim 0, leaf 2)",
            "root(claim 0, leaf 3)",
        ],
    ));

    // A false partial evaluation in the *last* round: its own recombination
    // fires, and since that round's α is squeezed after the message, the folded
    // commitment no longer matches the prover's surviving blocks either.
    let mut lied_last = proof.clone();
    lied_last.rounds[ROUNDS - 1].z[0][1] =
        lied_last.rounds[ROUNDS - 1].z[0][1].clone() + scalar_elt::<Q, D>(Q::ONE);
    note(expect_reject(
        "false partial evaluation in the last round",
        &crs,
        &inst,
        &lied_last,
        &[
            "z-decompose(round 2,claim 0)",
            "eval(claim 0)",
            "root(claim 0, leaf 0)",
            "root(claim 0, leaf 1)",
            "root(claim 0, leaf 2)",
            "root(claim 0, leaf 3)",
        ],
    ));

    // An oversized opening in round 1: the gate fires on the block itself, and
    // because the block is absorbed before that round's α, everything folded
    // from it onwards is out of step with the prover's surviving arrays.
    let mut swollen = proof.clone();
    swollen.rounds[0].blocks[0][0][1][0] = scalar_elt::<Q, D>(Q::from(beta + 7));
    let gate = format!("norm(round 1,claim 0,level 1,path 1) <= {beta}");
    note(expect_reject(
        "oversized opening block in round 1",
        &crs,
        &inst,
        &swollen,
        &[
            gate.as_str(),
            "z-decompose(round 2,claim 0)",
            "eval(claim 0)",
            "root(claim 0, leaf 0)",
            "root(claim 0, leaf 1)",
            "root(claim 0, leaf 2)",
            "root(claim 0, leaf 3)",
        ],
    ));

    // A stale commitment: a root from a different polynomial. The recombination
    // checks survive (they never mention `t`), the accumulation does not.
    let other = {
        let mut c = coeffs.clone();
        c[0] = c[0].clone() + scalar_elt::<Q, D>(Q::ONE);
        c
    };
    let (other_root, _) = commit(&crs, &other);
    let stale = Instance {
        root: other_root,
        ..inst.clone()
    };
    note(expect_reject(
        "root commitment of a different polynomial",
        &crs,
        &stale,
        &proof,
        &[
            "z-decompose(round 2,claim 0)",
            "eval(claim 0)",
            "root(claim 0, leaf 0)",
            "root(claim 0, leaf 1)",
            "root(claim 0, leaf 2)",
            "root(claim 0, leaf 3)",
        ],
    ));

    // ---- the final message: sent after the last challenge, so nothing ------
    // ---- cascades and each tamper isolates its own equations ----------------
    let leaf_of = |level: usize, path: usize| -> Vec<usize> {
        (0..FINAL_COEFFS)
            .filter(|b| (b & ((1 << (level + 1)) - 1)) == path)
            .collect()
    };
    let names = |leaves: &[usize]| -> Vec<String> {
        leaves.iter().map(|b| format!("root(claim 0, leaf {b})")).collect()
    };
    /// Borrow a built name list as the `&[&str]` set `expect_reject` pins.
    fn as_strs(v: &[String]) -> Vec<&str> {
        v.iter().map(String::as_str).collect()
    }

    // The deepest surviving block, read by exactly one leaf.
    let mut one_block = proof.clone();
    one_block.last.openings[0] = shift_block(&one_block.last.openings[0], LEVELS_LEFT - 1, 2, 3);
    let want = names(&leaf_of(LEVELS_LEFT - 1, 2));
    note(expect_reject(
        "tampered surviving block (deepest level, path 2)",
        &crs,
        &inst,
        &one_block,
        &as_strs(&want),
    ));

    // The shallowest surviving block, read by half the leaves.
    let mut half_block = proof.clone();
    half_block.last.openings[0] = shift_block(&half_block.last.openings[0], 0, 1, 3);
    let want = names(&leaf_of(0, 1));
    note(expect_reject(
        "tampered surviving block (first surviving level, path 1)",
        &crs,
        &inst,
        &half_block,
        &as_strs(&want),
    ));

    // An oversized surviving block: the base case's own norm gate, plus the
    // leaves that read it. Fig. 5 item 2(g) grows the slack by `r·2^k` per
    // round, so the gate standing at the base case is `(r 2^k)^ℓ β`.
    let final_beta = (0..ROUNDS).fold(beta, |acc, _| acc * (CLAIMS * KK) as u64);
    assert_eq!(final_beta, beta * 4, "this instance folds r·2^k = 2 twice");
    let mut fat_block = proof.clone();
    fat_block.last.openings[0] = fatten_block(&fat_block.last.openings[0], 0, 0, final_beta + 7);
    let gate = format!("final-norm(claim 0, level 1, path 0) <= {final_beta}");
    let fat_leaves = names(&leaf_of(0, 0));
    let fat_leaf_names = as_strs(&fat_leaves);
    let mut fat_expected = vec![gate.as_str()];
    fat_expected.extend(fat_leaf_names.iter().copied());
    note(expect_reject(
        "oversized surviving block",
        &crs,
        &inst,
        &fat_block,
        &fat_expected,
    ));

    // A false coefficient of the folded polynomial: its own leaf equation and
    // the final claim — and nothing else, because it is sent after the last
    // challenge.
    let mut false_coeff = proof.clone();
    false_coeff.last.coeffs[0][2] =
        false_coeff.last.coeffs[0][2].clone() + scalar_elt::<Q, D>(Q::ONE);
    note(expect_reject(
        "false coefficient of the folded polynomial",
        &crs,
        &inst,
        &false_coeff,
        &["eval(claim 0)", "root(claim 0, leaf 2)"],
    ));

    // Every family of checks must be the thing some tamper is caught by.
    for name in FAMILIES {
        assert!(
            tripped.contains(&name),
            "no tamper is caught by {name} — it is not being tested"
        );
    }
    println!("  all five check families are tripped by some tamper, and each tamper is attributed");
}
