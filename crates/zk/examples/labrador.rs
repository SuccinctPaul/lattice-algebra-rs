//! LaBRADOR: a compact argument for R1CS from Module-SIS.
//!
//! Beullens–Seiler, CRYPTO 2023, eprint 2022/1341. Headline result: 58 KB to
//! prove knowledge of a short solution of 2²⁰ R1CS constraints.
//!
//! This file is a **scheme assembly**: it holds no cryptographic logic. Every
//! step below is a call into `zk::pcs::binary_r1cs` and `zk::pcs::dotproduct`,
//! which carry the paper's Figure 4 R1CS reduction, its Section 5.1 relation,
//! Section 5.2 protocol and Figure 3 verification algorithm.
//!
//! # What is covered
//!
//! Covered, in the paper's own order:
//!
//! * §6 / Figure 4 — the binary R1CS and its reduction to the principal
//!   relation `R` (`binary_r1cs::reduce`), with Theorem 6.2's guards;
//! * §5.1 — the relation `R`: families `F` (vanishing in `R_q`) and `F′`
//!   (vanishing constant term) plus one global `l2` budget;
//! * §5.2 / Figure 2 — commit (`tᵢ = A·sᵢ`, outer `u₁`), project (the
//!   Johnson–Lindenstrauss `Π`, the response `p`, and its `F′` form), aggregate
//!   (twice: `ψ, ω` into `F′′`, then `α, β` into the single `F`), amortize
//!   (`cᵢ`, `z`, `u₂`);
//! * §5.2 — the shortness proof: `‖p‖₂ ≤ √128·β`, the `√(128/30)` extraction gap
//!   of Lemmas 4.1 and 4.2, and Figure 3 line 14's consolidated budget (5);
//! * §5.4 — the norm bounds and decomposition parameters `b, t₁, t₂, γ, γ₁, γ₂`;
//! * §5.7 — the proof-size formula;
//! * Figure 3, lines 3–20 — every verification equation, each with its own
//!   named rejection, exercised by the tamper walk-through below;
//! * **§5.3 / Lemma 3.7 — one recursion level**: the verifier's recomputation
//!   (`derive_view`), §5.3's reblocking `s′ = (z⁽⁰⁾, z⁽¹⁾, v)` with `v = t‖g‖h`
//!   cut into `r′ = 2ν+μ` vectors of rank `n′`, the `κ+κ₁+κ₂+3` equations of
//!   eq. (6), and the check that Figure 3's last message *is* a witness for that
//!   target relation — which is what lets the protocol be composed with itself.
//!
//! # What the recursion costs, and whether it pays here
//!
//! The recursion is the mechanism, and `RecursionPlan` (§5.7's own arithmetic) is
//! the decision: a level pays when `core(target) + last(target) < last(this)`.
//! At this example's shape it does **not** pay — the numbers are printed in the
//! run below, together with the rank at which the decision flips — because a
//! level's target witness is `2n + m` ring elements with
//! `m = r·t₁·κ + (t₁+t₂)(r²+r)/2`, and `m` does not shrink with `n`: with
//! `n = 3`, `r = 8`, `κ = 4`, `t₁ = t₂ = 4` it is 416 elements against a source
//! witness of 24. The paper's Table 3 (p.28) starts its recursion at `n = 37450`,
//! `r = 112`. So one level is wired and checked end-to-end here, and the size win
//! is reported as arithmetic rather than claimed.
//!
//! Run with: `cargo run -p lattice-zk --example labrador`

use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::{shortcuts::h256, Shake256Xof, Xof};
use algebra::ring::traits::CenteredRing;
use algebra::ring::PolynomialQuotientRing;
use zk::pcs::binary_r1cs::{
    lift_witness, reduce, sample_combos, sample_satisfiable, sample_theta, R1csGuards, MULTIPLICITY,
};
use zk::pcs::dotproduct::{
    self, const_elt, derive_view, operator_norm_bound, prove_composed, recursion_msis_norm_sq,
    target_instance, verify_composed, verify_composed_report, ChallengeSpace, CoreError,
    CoreMessage, CoreParams, CoreSetup, Decomposition, Elt, NormBounds, QuadFn, RecursionPlan,
    Relation, RelationError, SizeModel, TargetEquation, TargetShape,
};
use zk::pcs::{aggregation_count, prove_core, verify_core, verify_core_report, RingMatrixKey};

/// Ring degree `d`: the paper's instantiation is `R = Z_q[X]/(X⁶⁴ + 1)`.
const D: usize = 64;
/// LaBRADOR's modulus shape: prime, `q ≈ 2³²`, `q ≡ 5 (mod 8)`, so `X⁶⁴ + 1`
/// splits into two degree-32 factors (the §2 hypothesis) and no NTT exists.
const Q: u64 = 4_294_967_197; // 2³² − 99
type Scalar = algebra::ring::zq::Zq<Q>;
type Ring = Elt<Scalar, D>;

/// Constraints and variables of the toy binary R1CS. Both are multiples of
/// `d`, which is the padding §6 asks for, and `k = n` makes the reduction's
/// four vectors the same length.
const K: usize = 192;
/// Rows of the Figure 4 commitment matrix `𝒜` (the paper's `m/d`).
const K_PRIME: usize = 2;
/// Inner commitment rank `κ` (rows of `A`) and the outer ranks `κ₁ = κ₂`.
const KAPPA: usize = 4;
const KAPPA1: usize = 4;
const KAPPA2: usize = 4;
/// Random `F₂`-combinations of the `3k` linear relations: soundness `2⁻ˡ`.
const L: usize = 128;

fn bytes_of(elts: &[Ring]) -> usize {
    elts.len() * D * 4
}

fn centered(x: &Ring) -> Vec<i64> {
    x.coefficients().iter().map(|c| c.centered()).collect()
}

/// The ring element `1` (constant term one, rest zero).
fn one() -> Ring {
    const_elt::<Scalar, D>(1)
}

/// Integer square root, ceiling — the bounds print as integers, never floats.
fn isqrt(v: u128) -> u128 {
    if v < 2 {
        return v;
    }
    let mut x = v;
    let mut y = (x + 1) / 2;
    while y < x {
        x = y;
        y = (x + v / x) / 2;
    }
    if x * x < v {
        x + 1
    } else {
        x
    }
}

/// `⌈log₂ v⌉`, at least 1.
fn log2_ceil(v: u128) -> u128 {
    let mut bits = 1u128;
    while (1u128 << bits) < v.max(2) {
        bits += 1;
    }
    bits
}

/// `⌈log₂ q⌉`, the encoding width §5.7 charges per ring coefficient.
fn bit_width(v: u64) -> u128 {
    log2_ceil(u128::from(v))
}

/// Runs one *real* composed level: Lemma 3.7 with the target relation proved by
/// a second execution instead of its witness being sent.
///
/// The statement is the shape §6's reduction produces — `r = MULTIPLICITY` parts,
/// one `F` function per row of `𝒜`, `4 + 4 + 1 + ℓ` functions in `F′` — at a rank
/// `parts_per_ring` bigger than the toy instance's, because §5.7's own arithmetic
/// says a level only pays past one: `m = r·t₁·κ + (t₁+t₂)(r²+r)/2`, the plane
/// width of `v = t‖g‖h`, does not shrink with `n`, so `2n + m` only beats the
/// source once `n` is past `m`'s shadow. Both the predicted and the *measured*
/// last-message sizes are printed, and the prediction is read off
/// `RecursionPlan::of`, i.e. the same code the verifier runs, never restated here.
fn composed_level(rank: usize) {
    println!("\nLemma 3.7 executed — one composed level, instance of R at rank {rank}:");
    let beta_sq = u128::from(Q);
    let space = ChallengeSpace::PAPER;
    // The Figure 4 shape: `|F| = m′` full functions and `4 σ-image + 4 binarity +
    // 1 product + ℓ combinations` partial ones. `sample_instance` is asked for
    // that shape rather than run through the reduction, whose `O(ℓ·k²)` bit-matrix
    // products are the cost of a *large R1CS* and not of the recursion.
    let (relation, witness) = dotproduct::sample_instance::<Scalar, D>(
        &h256(b"labrador-composed-level"),
        MULTIPLICITY,
        rank,
        K_PRIME,
        4 + 4 + 1 + L,
        beta_sq,
    );
    relation
        .check(&witness)
        .expect("the scenario's statement must be satisfiable");
    assert_eq!(relation.multiplicity, MULTIPLICITY);
    let bounds = NormBounds::derive(
        beta_sq,
        Q,
        relation.multiplicity,
        relation.rank,
        KAPPA,
        D,
        space.tau(),
    );
    let decomp1 = Decomposition::new(bounds.base, bounds.t1);
    let decomp2 = Decomposition::new(bounds.base, bounds.t2);
    decomp1
        .validate::<Scalar>()
        .expect("b₁^t₁ must exceed q for the split to be exact");
    let triangle = (relation.multiplicity * relation.multiplicity + relation.multiplicity) / 2;
    let setup = CoreSetup {
        params: CoreParams {
            inner_key: RingMatrixKey::<Scalar, D>::setup(
                b"l2-inner-A",
                &[0x1Au8; 32],
                KAPPA,
                relation.rank,
            ),
            key_b: RingMatrixKey::<Scalar, D>::setup(
                b"l2-outer-B",
                &[0x1Bu8; 32],
                KAPPA1,
                relation.multiplicity * bounds.t1 * KAPPA,
            ),
            key_c: RingMatrixKey::<Scalar, D>::setup(
                b"l2-outer-C",
                &[0x1Cu8; 32],
                KAPPA1,
                bounds.t2 * triangle,
            ),
            key_d: RingMatrixKey::<Scalar, D>::setup(
                b"l2-outer-D",
                &[0x1Du8; 32],
                KAPPA2,
                bounds.t1 * triangle,
            ),
            decomp1,
            decomp2,
            bounds,
            aggregation_count: aggregation_count(Q),
        },
        space,
    };
    let key_seed = [0x2Eu8; 32];

    // The plan the verifier will re-derive, before either side runs anything.
    let plan = RecursionPlan::of(&setup, &relation);
    let model = SizeModel::of(&setup);
    let direct_here = model.size(relation.multiplicity, relation.rank, beta_sq);
    assert!(
        plan.compacts(),
        "this scenario exists to be run where §5.7 says a level pays"
    );
    println!(
        "  statement: r = {}, n = {}, β = {}, |F| = {}, |F′| = {}",
        relation.multiplicity,
        relation.rank,
        isqrt(beta_sq),
        relation.full.len(),
        relation.ct_only.len()
    );
    println!(
        "  §5.4 for this rank: b = {}, t₁ = {}, t₂ = {} → m = r·t₁·κ + (t₁+t₂)(r²+r)/2 = {} planes",
        bounds.base,
        bounds.t1,
        bounds.t2,
        plan.shape.v_width
    );
    println!(
        "  §5.3 reblocking: ν = {}, μ = {} → r′ = {}, n′ = {}; (β′)² = {} against β² = {beta_sq}",
        plan.shape.nu,
        plan.shape.mu,
        plan.shape.multiplicity(),
        plan.shape.rank,
        bounds.beta_prime_sq,
    );
    println!(
        "  §5.7 predicts: terminate {} KB, recurse {} KB → this step {} {} KB",
        direct_here.last_message_bits / 8 / 1024,
        plan.recursed.total_bits() / 8 / 1024,
        if plan.compacts() { "saves" } else { "costs" },
        (plan.saving_bits() / 8 / 1024).abs()
    );

    // (1) The direct argument, so the two accounts are measured on the same run.
    // `prove_core` checks its own proof before returning it (Figure 3 run by the
    // prover), which is why this does not call `verify_core` a second time: the
    // assembly is paying for one honest execution, not two.
    let message = prove_core(&setup, &relation, &key_seed, &witness)
        .expect("the honest core argument must go through at this size too");

    // (2) The composed argument: Figure 2 run again on this level's target.
    let proof = prove_composed(&setup, &relation, &key_seed, &witness)
        .expect("one composed level must instantiate and prove");
    let report = verify_composed_report(&setup, &relation, &key_seed, &proof);
    assert!(report.is_empty(), "the composed argument must verify: {report:?}");

    // What each account puts in the last message. `last_message_planes` is the
    // honest payload: `z, t, g, h` are recomputable from their digit planes
    // (Figure 3 lines 10–13), so the planes are what is transmitted.
    let direct_planes = message.last_message_planes();
    let composed_planes = proof.last_message_planes();
    println!(
        "  MEASURED last message, raw 4 B/coefficient: direct {} KB → composed {} KB ({} {} KB)",
        direct_planes * D * 4 / 1024,
        composed_planes * D * 4 / 1024,
        if composed_planes < direct_planes { "saves" } else { "costs" },
        ((direct_planes as i128 - composed_planes as i128) * (D * 4) as i128 / 1024).abs()
    );
    println!(
        "    element counts: direct 2n+m = {} planes of level 0 (never sent by the composed prover); \
         composed 2n′+m′ = {} planes of level 1",
        direct_planes, composed_planes
    );
    println!(
        "    heads, unchanged by recursion: head₀ {} B + head₁ {} B; §5.7's own widths say {} KB → {} KB",
        message.head_elements() * D * 4,
        proof.next.head_elements() * D * 4,
        direct_here.last_message_bits / 8 / 1024,
        plan.recursed.last_message_bits / 8 / 1024,
    );
    assert!(
        proof.head.u1 == message.u1 && proof.head.p == message.p && proof.head.u2 == message.u2,
        "the composed prover sends the same head the direct one does"
    );
    // (3) The composed chain's named checks, each tripped. The claims that used to
    // be re-sent are now *proved*, so the interesting forgeries are edits of the
    // head the target is derived from and of level 1's message. `src`'s own tests
    // walk every variant at a shape cheap enough to enumerate; here the two
    // guards that exist *only* in the composed protocol are shown together with
    // one forgery per level.
    println!("  composed tamper walk-through (whole report, named at its head):");
    let mut cases: Vec<(&str, dotproduct::ComposedProof<Scalar, D>, bool)> = Vec::new();
    let mut p = proof.clone();
    p.reroll = dotproduct::MAX_PROJECTION_REROLLS;
    cases.push(("reroll out of range  ", p, false));
    let mut p = proof.clone();
    p.shape.nu += 1;
    cases.push(("prover-chosen shape  ", p, true));
    let mut p = proof.clone();
    p.head.b_double[0] = &p.head.b_double[0] + &one();
    cases.push(("b″(0) constant term  ", p, false));
    let mut p = proof.clone();
    p.next.u1[0] = &p.next.u1[0] + &one();
    cases.push(("level 1's u₁         ", p, false));
    let mut seen: Vec<&'static str> = Vec::new();
    for (label, tampered, cheap) in cases {
        let report = verify_composed_report(&setup, &relation, &key_seed, &tampered);
        assert!(
            !report.is_empty(),
            "{label}: a tampered composed proof was ACCEPTED"
        );
        let head = report[0].to_string();
        for e in &report {
            let kind = match e {
                dotproduct::RecursionError::Reroll { .. } => "reroll",
                dotproduct::RecursionError::Shape { .. } => "shape",
                // The declared budget (5) disagreeing with this level's own
                // `(β′)² = 2γ²/b² + γ₁² + γ₂²` is its own condition — §5.4's
                // budget, not a reroll or a shape — and `verify_composed_report`
                // reports it alone.
                dotproduct::RecursionError::Budget { .. } => "budget",
                dotproduct::RecursionError::Head(_) => "head",
                dotproduct::RecursionError::NextSetup(_) => "next-setup",
                dotproduct::RecursionError::NextLevel(_) => "next-level",
            };
            if !seen.contains(&kind) {
                seen.push(kind);
            }
        }
        println!(
            "    {label} → {head}{}",
            if report.len() > 1 {
                format!(" (+{} more)", report.len() - 1)
            } else {
                String::new()
            }
        );
        if cheap {
            // `verify_composed` is the report's head by construction; checking it
            // once here costs one early-return, where the other cases would each
            // pay for a second full replay of both levels.
            assert_eq!(
                verify_composed(&setup, &relation, &key_seed, &tampered),
                Err(report[0]),
                "{label}: verify_composed must agree with the head of the report"
            );
        }
    }
    for kind in ["reroll", "shape", "head", "next-level"] {
        assert!(
            seen.contains(&kind),
            "no tamper ever produces a {kind} rejection, so that check could be dead code"
        );
    }
    println!(
        "  the composed verifier read {} elements in its last message and {}.{} KB of head — \
         level 0's z,t,g,h were never on the wire.",
        composed_planes,
        (message.head_elements() + proof.next.head_elements()) * D * 4 / 1024,
        (message.head_elements() + proof.next.head_elements()) * D * 4 % 1024 / 10
    );
}

fn main() {
    println!("LaBRADOR (2022/1341) — core argument for binary R1CS");
    println!("ring: Z_{Q}[X]/(X^{D}+1), d = {D}, q ≡ {} (mod 8)", Q % 8);
    let splitting = algebra::ring::number_theory::x_pow_d_plus_1_splitting(Q, D as u64)
        .expect("q an odd prime, d a power of two");
    println!(
        "§2 hypothesis: X^{D}+1 → {} factors of degree {} — {}",
        splitting.factor_count,
        splitting.factor_degree,
        if splitting.is_two_half_degrees(D as u64) {
            "the two-prime-ideal regime the paper states, so no NTT exists"
        } else {
            "NOT the paper's regime"
        }
    );
    assert!(splitting.is_two_half_degrees(D as u64));

    // ── §6 / Figure 4: the R1CS and its reduction to the relation R ─────────
    let instance = sample_satisfiable(&h256(b"labrador-instance"), K, K, 3);
    assert!(
        instance.r1cs.is_satisfied(&instance.witness),
        "the toy instance must really be satisfiable"
    );
    let guards = R1csGuards::check(K, K, Q);
    println!(
        "\nFigure 4: binary R1CS, k = {K} constraints, n = {K} variables, 3 non-zeros per row"
    );
    println!(
        "  Theorem 6.2 guards: n+3k < q {}, 6k < q {}, composition n+3k < 15q/128 {}",
        guards.no_overflow, guards.product_guard, guards.composition
    );
    assert!(guards.all(), "Theorem 6.2 needs all three");

    let combos = sample_combos(&h256(b"labrador-combos"), L, K);
    let lifted = lift_witness::<Scalar, D>(&instance, &combos);
    assert!(
        lifted.combinations_are_even(),
        "a satisfying witness makes every claimed combination value even"
    );
    let fig4_key =
        RingMatrixKey::<Scalar, D>::setup(b"fig4-commitment", &[0xF4u8; 32], K_PRIME, 4 * (K / D));
    // Figure 4 states the relation bound as β = √q.
    let beta_sq = u128::from(Q);
    let theta = sample_theta::<Scalar, D>(&h256(b"labrador-theta"), K / D, 4);
    let relation = reduce::<Scalar, D>(&instance, &fig4_key, &lifted, &theta, &combos, beta_sq)
        .expect("a reduced instance");
    println!(
        "  relation R: rank n = {}, r = {}, |F| = {} (one per 𝒜 row), |F'| = {} (4 σ-image + 4 binarity + 1 product + {L} combinations)",
        relation.rank,
        relation.multiplicity,
        relation.full.len(),
        relation.ct_only.len()
    );
    assert_eq!(relation.multiplicity, MULTIPLICITY);
    relation
        .check(&lifted.s)
        .expect("the honest witness satisfies the reduced relation");
    println!(
        "  Σᵢ‖sᵢ‖₂² = {} against β² = {beta_sq} (the paper's 2(3k+n) = {})",
        dotproduct::witness_norm_sq(&lifted.s),
        2 * (3 * K + K)
    );

    // ── §2: the challenge space ─────────────────────────────────────────────
    let space = ChallengeSpace::PAPER;
    let mut probe = Shake256Xof::new(&[]);
    probe.absorb(b"labrador-challenge-probe");
    let mut stream = BitStream::new(&mut probe);
    let sample: Ring = space.sample(&mut stream).expect("the filter accepts");
    let (zeros, ones, twos) = centered(&sample).iter().fold((0, 0, 0), |mut a, &c| {
        match c.abs() {
            0 => a.0 += 1,
            1 => a.1 += 1,
            2 => a.2 += 1,
            _ => {}
        }
        a
    });
    println!(
        "\n§2 challenge space C: {zeros} zeros, {ones} ±1, {twos} ±2; τ = ‖c‖₂² = {}, T ≤ {} (measured bound {})",
        space.tau(),
        space.operator_norm,
        operator_norm_bound(&sample)
    );
    assert_eq!((zeros, ones, twos), (space.zeros, space.ones, space.twos));

    // ── §5.4: norm bounds and decomposition parameters ──────────────────────
    let triangle = (MULTIPLICITY * MULTIPLICITY + MULTIPLICITY) / 2;
    let bounds = NormBounds::derive(
        beta_sq,
        Q,
        relation.multiplicity,
        relation.rank,
        KAPPA,
        D,
        space.tau(),
    );
    let decomp1 = Decomposition::new(bounds.base, bounds.t1);
    let decomp2 = Decomposition::new(bounds.base, bounds.t2);
    decomp1
        .validate::<Scalar>()
        .expect("b₁^t₁ must exceed q for the split to be exact");
    decomp2
        .validate::<Scalar>()
        .expect("b₂^t₂ must exceed q for the split to be exact");
    println!(
        "\n§5.4: b = {} (from (12·s²·r·τ)^{{1/4}}), t₁ = {} with b^t₁ = {} > q, t₂ = {}",
        bounds.base,
        bounds.t1,
        decomp1.capacity(),
        bounds.t2
    );
    println!(
        "  γ² = β²τ = {}, γ₁² = {}, γ₂² = {}, (β')² = {}",
        bounds.gamma_sq, bounds.gamma1_sq, bounds.gamma2_sq, bounds.beta_prime_sq
    );
    let [msis_outer, msis_inner] = bounds.msis_norm_sq(beta_sq, space.operator_norm);
    println!(
        "  Theorem 5.1 Module-SIS (squared norms): rank κ₁=κ₂ needs {msis_outer}, rank κ needs {msis_inner}"
    );
    assert!(
        NormBounds::slack_condition(beta_sq, Q),
        "Theorem 5.1's precondition β ≤ √(30/128)·q/125"
    );
    println!(
        "  slack: β = {} ≤ √(30/128)·q/125 = {}",
        isqrt(beta_sq),
        isqrt(30 * u128::from(Q) * u128::from(Q) / (128 * 125 * 125))
    );

    let setup = CoreSetup {
        params: CoreParams {
            inner_key: RingMatrixKey::<Scalar, D>::setup(
                b"inner-A",
                &[0xAu8; 32],
                KAPPA,
                relation.rank,
            ),
            key_b: RingMatrixKey::<Scalar, D>::setup(
                b"outer-B",
                &[0xBu8; 32],
                KAPPA1,
                relation.multiplicity * bounds.t1 * KAPPA,
            ),
            key_c: RingMatrixKey::<Scalar, D>::setup(
                b"outer-C",
                &[0xCu8; 32],
                KAPPA1,
                bounds.t2 * triangle,
            ),
            key_d: RingMatrixKey::<Scalar, D>::setup(
                b"outer-D",
                &[0xFDu8; 32],
                KAPPA2,
                bounds.t1 * triangle,
            ),
            decomp1,
            decomp2,
            bounds,
            aggregation_count: aggregation_count(Q),
        },
        space,
    };
    let params = &setup.params;

    // ── §5.2 / Figure 2: prove; Figure 3: verify ─────────────────────────────
    let key_seed = [0x1Du8; 32];
    let message = prove_core(&setup, &relation, &key_seed, &lifted.s)
        .expect("the honest core argument must go through");
    verify_core(&setup, &relation, &key_seed, &message).expect("the proof verifies");
    println!(
        "\nFigure 2/3: honest core argument verified — {} aggregated functions, {} projection rows",
        params.aggregation_count,
        message.p.len()
    );
    println!(
        "  ‖p‖₂² = {} against 128·β² = {}",
        message
            .p
            .iter()
            .map(|v| u128::from(v.unsigned_abs()) * u128::from(v.unsigned_abs()))
            .sum::<u128>(),
        128 * beta_sq
    );
    let revealed = params.decomp1.norm_sq(&message.z_digits)
        + params.decomp1.norm_sq(&message.t_digits)
        + params.decomp2.norm_sq(&message.g_digits)
        + params.decomp1.norm_sq(&message.h_digits);
    println!(
        "  line 14 (equation 5): Σ revealed digit-plane squares = {} ≤ (β')² = {}",
        revealed, bounds.beta_prime_sq
    );

    // ── §5.7: proof size ────────────────────────────────────────────────────
    let q_width = bit_width(Q);
    let proof_bits = ((KAPPA1 + KAPPA2) as u128) * (D as u128) * q_width
        + 256 * log2_ceil(12 * isqrt(beta_sq) / 2 + 1)
        + (params.aggregation_count as u128) * (D as u128) * q_width
        + 4 * 128;
    println!(
        "\n§5.7 size of THIS core execution: {} bits ≈ {} KB  (u₁+u₂ {} B, p {} B, b'' {} B)",
        proof_bits,
        proof_bits / 8 / 1024,
        bytes_of(&message.u1) + bytes_of(&message.u2),
        message.p.len() * 8,
        bytes_of(&message.b_double)
    );
    let last_message =
        bytes_of(&message.z) + bytes_of(&message.t) + bytes_of(&message.g) + bytes_of(&message.h);
    println!(
        "  last prover message (the recursion is what removes it): z {} B + t {} B + g {} B + h {} B = {} KB",
        bytes_of(&message.z),
        bytes_of(&message.t),
        bytes_of(&message.g),
        bytes_of(&message.h),
        last_message / 1024
    );

    // ── §5.3 / Lemma 3.7: one recursion level ────────────────────────────────
    //
    // Figure 3's caption is the specification: *"the algorithm checks that the
    // last prover message is a witness for the target relation, which is an
    // instance of the principal relation"*. So a level is a proof-of-knowledge
    // reduction (Def. 3.5) whose statement the verifier computes, and Lemma 3.7
    // composes it with another execution, adding soundness errors. Nothing below
    // is new cryptography — it is §5.3's bookkeeping, driven through `src`.
    println!("\n§5.3 recursion — Figure 3's last message turned into R′:");

    // (1) Recompute, never receive: Π, ψ, ω, a″, φ″, α, β and the r challenges.
    let view = derive_view(&setup, &relation, &key_seed, &message)
        .expect("the honest transcript replays");
    assert_eq!(view.c.len(), relation.multiplicity, "one cᵢ per sᵢ");
    assert_eq!(view.claims.len(), params.aggregation_count);

    // (2) §5.3's reblocking, with (ν, μ) chosen by §5.7's size rule.
    let model = SizeModel {
        modulus: Q,
        degree: D,
        tau: space.tau(),
        kappa: KAPPA,
        kappa1: KAPPA1,
        kappa2: KAPPA2,
        aggregation_count: params.aggregation_count,
        projection_rows: dotproduct::PROJECTION_ROWS,
    };
    let plan = RecursionPlan::derive(&model, relation.multiplicity, relation.rank, beta_sq);
    let shape = plan.shape;
    assert!(
        shape.fits(),
        "ν·n′ must cover n and μ·n′ must cover m, or the padding drops witness"
    );
    assert_eq!(
        shape.v_width,
        TargetShape::width_v(relation.multiplicity, bounds.t1, bounds.t2, KAPPA)
    );
    println!(
        "  v = t‖g‖h is m = r·t₁·κ + (t₁+t₂)(r²+r)/2 = {} planes; z contributes 2n = {} → target witness {} elements",
        shape.v_width,
        2 * relation.rank,
        2 * relation.rank + shape.v_width
    );
    println!(
        "  ν = {}, μ = {} → r′ = 2ν+μ = {}, n′ = {} ({} slots, {} of them padding)",
        shape.nu,
        shape.mu,
        shape.multiplicity(),
        shape.rank,
        shape.target_width(),
        shape.target_width() - 2 * relation.rank - shape.v_width
    );

    let target = target_instance(
        &relation,
        &view,
        params,
        &shape,
        &message.u1,
        &message.u2,
        &message.z,
        &message.t_digits,
        &message.g_digits,
        &message.h_digits,
    )
    .expect("the target instance builds");
    assert_eq!(
        target.relation.full.len(),
        TargetShape::equation_count(KAPPA, KAPPA1, KAPPA2),
        "eq. (6): κ+κ₁+κ₂+3 equations"
    );
    assert!(
        target.relation.ct_only.is_empty(),
        "§5.3: the target is ((G, {{}}, β′), s′), so F′ is empty"
    );
    assert_eq!(target.relation.norm_bound_sq, bounds.beta_prime_sq);
    target
        .check_honest()
        .expect("Definition 3.5's factoring: the last message is a witness for R′");
    println!(
        "  R′ = (G, ∅, β′): Σ‖s′‖² = {} ≤ (β′)² = {}, and all {} equations of (6) vanish",
        dotproduct::witness_norm_sq(&target.witness),
        bounds.beta_prime_sq,
        target.relation.full.len()
    );
    println!(
        "  (β′)² ≤ β² here: {} ≤ {} — eq. (5) divides ‖z‖² by b² = {} before adding the plane norms γ₁²+γ₂² = {}",
        bounds.beta_prime_sq,
        beta_sq,
        bounds.base * bounds.base,
        bounds.gamma1_sq + bounds.gamma2_sq
    );
    assert!(bounds.beta_prime_sq <= beta_sq, "at this shape the budget shrinks");

    // The hardness bound is what the recursion pays with (Remark 5.2, p.20): the
    // norm the commitments must be binding for grows by √(128/30) for every level
    // whose norm the verifier only receives *proof* of. `κ` must grow to keep
    // Module-SIS hard, which is why §6.1 recomputes the ranks per level; this
    // crate's toy κ is fixed, so the growth is reported, not absorbed.
    let [outer0, inner0] = bounds.msis_norm_sq(beta_sq, space.operator_norm);
    let [outer1, inner1] = recursion_msis_norm_sq(&bounds, beta_sq, space.operator_norm, 1);
    println!(
        "  Remark 5.2 after one composed level: MSIS² {}→{outer1} (rank κ₁=κ₂), {}→{inner1} (rank κ)",
        outer0, inner0
    );
    assert!(outer1 > outer0 && inner1 > inner0, "the bound must grow");

    // (3) Every family of target equations must be *owned* by some tamper: a
    // level whose target relation accepted a bad last message would let the whole
    // chain prove nothing. `derive_view` is re-run on the tampered transcript,
    // because under Fiat–Shamir the target statement moves with the message.
    let edits: Vec<(&str, fn(&mut CoreMessage<Scalar, D>))> = vec![
        ("u₁  ", |m| m.u1[0] = &m.u1[0] + &one()),
        ("u₂  ", |m| m.u2[0] = &m.u2[0] + &one()),
        ("z   ", |m| m.z[0] = &m.z[0] + &one()),
        ("t⁽ᵏ⁾", |m| m.t_digits[0] = &m.t_digits[0] + &one()),
        ("g⁽ᵏ⁾", |m| m.g_digits[0] = &m.g_digits[0] + &one()),
        ("h⁽ᵏ⁾", |m| m.h_digits[0] = &m.h_digits[0] + &one()),
    ];
    fn family_of(e: TargetEquation) -> &'static str {
        match e {
            TargetEquation::InnerLink { .. } => "line15",
            TargetEquation::OuterCommitment1 { .. } => "line19",
            TargetEquation::OuterCommitment2 { .. } => "line20",
            TargetEquation::SelfInnerProduct => "line16",
            TargetEquation::LinearClaim => "line17",
            TargetEquation::Relation => "line18",
        }
    }
    let mut tripped: Vec<&'static str> = Vec::new();
    for (label, edit) in edits {
        let mut m = message.clone();
        edit(&mut m);
        let tampered_view = derive_view(&setup, &relation, &key_seed, &m)
            .expect("a tampered transcript still replays; that is the point");
        let built = target_instance(
            &relation,
            &tampered_view,
            params,
            &shape,
            &m.u1,
            &m.u2,
            &m.z,
            &m.t_digits,
            &m.g_digits,
            &m.h_digits,
        )
        .expect("the target builds");
        let fails: Vec<usize> = (0..built.relation.full.len())
            .filter(|i| !built.relation.full[*i].value(&built.witness).is_zero())
            .collect();
        assert!(
            !fails.is_empty(),
            "{label}: a tampered level left R′ satisfied — Def. 3.5's factoring would be false"
        );
        let names: Vec<String> = fails
            .iter()
            .map(|i| {
                let e = built
                    .equation(*i)
                    .unwrap_or_else(|| panic!("equation {i} of (6) maps to no line"));
                if !tripped.contains(&family_of(e)) {
                    tripped.push(family_of(e));
                }
                e.name().to_string()
            })
            .collect();
        println!("  {label} → {}", names.join("\n           "));
    }
    for family in ["line15", "line16", "line17", "line18", "line19", "line20"] {
        assert!(
            tripped.contains(&family),
            "target equation {family} is never tripped by any tamper, so it could be \
             dead code and the recursion would not be attributable"
        );
    }
    println!("  all six equation families of (6) tripped, each by its own edit");

    // The norm clause (5) is the one part of R′ that is not an equation, so it has
    // to fail alone: tighten only the budget and every equation keeps holding.
    let honest_target_norm = dotproduct::witness_norm_sq(&target.witness);
    let mut tight = target.relation.clone();
    tight.norm_bound_sq = honest_target_norm - 1;
    assert_eq!(
        tight.check(&target.witness),
        Err(RelationError::NormExceeded {
            norm_sq: honest_target_norm,
            bound_sq: honest_target_norm - 1
        }),
        "the recursion's norm gate must reject on its own"
    );
    assert!(
        (0..target.relation.full.len())
            .filter(|i| !target.relation.full[*i].value(&target.witness).is_zero())
            .count()
            == 0,
        "and it must be the only thing that rejects"
    );
    println!(
        "  budget (5) alone: (β′)² = {} − 1 already rejects, with all {} equations still satisfied",
        honest_target_norm,
        target.relation.full.len()
    );

    // ── §5.7 / §6.1: whether this step pays ──────────────────────────────────
    //
    // Terminating a level costs its last message (= the target witness); recursing
    // costs one more core message plus *that* level's last message. The comparison
    // is §5.7's own formula, evaluated in `src`, never a float.
    let here = model.size(relation.multiplicity, relation.rank, beta_sq);
    let recursed_total = plan.recursed.total_bits() / 8;
    let terminate_total = here.last_message_bits / 8;
    println!(
        "\n§5.7 decision for THIS level (r = {}, n = {}):",
        relation.multiplicity, relation.rank
    );
    println!(
        "  terminate now : reveal the target witness = {:>9} B",
        terminate_total
    );
    println!(
        "  recurse once  : core {} B + its last {} B = {} B",
        plan.recursed.core_bits / 8,
        plan.recursed.last_message_bits / 8,
        recursed_total
    );
    println!(
        "  → this level's step {} {} B  (compacts: {})",
        if plan.compacts() { "saves" } else { "costs" },
        (plan.saving_bits() / 8).abs(),
        plan.compacts()
    );
    // The mechanism is wired and checked above; the *shrink* is a property of the
    // shape, and this example's shape is too small for it. `m` — the digit planes
    // of t, g and h — is independent of n, so `2n + m` only beats `rn` once n is
    // past r's own overhead. Recorded as arithmetic, not tuned away.
    println!(
        "  → at THIS shape (n = {}, m = {}) one level is a {} of {} B, not a saving: \
         the target witness 2n+m = {} beats the source rn = {} only past the rank below.",
        relation.rank,
        shape.v_width,
        if plan.compacts() { "gain" } else { "cost" },
        (plan.saving_bits() / 8).abs(),
        2 * relation.rank + shape.v_width,
        relation.multiplicity * relation.rank,
    );
    let mut flip: Option<usize> = None;
    let mut ladder: Vec<(usize, i128)> = Vec::new();
    for n in 1..=600usize {
        let p = RecursionPlan::derive(&model, MULTIPLICITY, n, beta_sq);
        if p.compacts() && flip.is_none() {
            flip = Some(n);
        }
        if [3usize, 16, 32, 64, 96, 128, 192, 256, 384, 600].contains(&n) {
            ladder.push((n, p.saving_bits() / 8));
        }
    }
    println!(
        "  recursion's saving (bytes, r = {MULTIPLICITY}, κ = {KAPPA}, t₁ = {}, b = {} at n = 3):",
        bounds.t1, bounds.base
    );
    for (n, saving) in &ladder {
        println!(
            "    n = {n:>4}: {saving:+8} B {}",
            if *saving > 0 { "← compacts" } else { "" }
        );
    }
    let flip = flip.expect("the sweep must find a rank where the step pays");
    assert!(
        flip > relation.rank,
        "the flip ({flip}) must be above this example's rank ({})",
        relation.rank
    );
    println!(
        "  first rank that compacts: n = {flip} (k = {} binary constraints at this reduction's shape), \
         i.e. {}× this example's rank",
        flip * D,
        flip / relation.rank
    );
    // The flip is a knife edge — a few hundred predicted bytes — so the *measured*
    // run below uses the smallest rank whose predicted saving clears 2 % of this
    // level's own last message. The rule is stated here, before the answer: an
    // effect that small is the smallest one a byte count can show honestly.
    let gain = (1..=600usize)
        .find(|n| {
            let p = RecursionPlan::derive(&model, MULTIPLICITY, *n, beta_sq);
            p.compacts() && 100 * p.saving_bits() > 2 * p.terminate_bits as i128
        })
        .expect("the saving grows with the rank, so a 2 % rank exists");
    println!(
        "  smallest rank whose predicted saving clears 2 % of this level's last message: n = {gain}"
    );
    // The paper's own first level (Table 3, p.28: binary R1CS with k = 2²⁵
    // constraints, reblocked to r = 112, n = 37450) is deep in the compacting
    // regime, which is what its 7-level, 53.84 KB schedule is built from.
    let paper = RecursionPlan::derive(&model, 112, 37450, beta_sq);
    println!(
        "  the paper's level-1 shape (r = 112, n = 37450): last = {} KB → recursed = {} KB, saving {} KB ({})",
        paper.terminate_bits / 8 / 1024,
        paper.recursed.total_bits() / 8 / 1024,
        paper.saving_bits() / 8 / 1024,
        if paper.compacts() { "compacts" } else { "costs" }
    );
    assert!(paper.compacts(), "Table 3's own shape must be in the compacting regime");

    // ── every tampered component must die by its own named check ────────────
    //
    // Figure 3's checks are chained, and the verifier recomputes the projection
    // matrix and every challenge from the transcript, so one edit usually trips
    // several equations at once. The walk-through therefore prints
    // `verify_core_report` — the whole set — and asserts on its head: with a
    // single-error verifier, a check that is only ever reached second is
    // indistinguishable from a check that never runs.
    //
    // Two kinds of edit are listed: the bare edit, which names the check that
    // fires first, and a self-consistent edit that keeps the digit
    // decompositions valid so the relation equations are among what fails. The
    // latter is the interesting forgery: an opening of a *different* witness.
    println!("\nFigure 3 tamper walk-through (each rejected by its own named check):");
    let mut cases: Vec<(&str, CoreMessage<Scalar, D>, CoreError)> = Vec::new();

    // u₁ is recommitted from the revealed digit planes, so an edit that does
    // not move them is caught by line 19 directly.
    let mut m = message.clone();
    m.u1[0] = &m.u1[0] + &one();
    cases.push(("u₁ (binds Π)     ", m, CoreError::OuterCommitment1));
    // The same for u₂ and line 20.
    let mut m = message.clone();
    m.u2[0] = &m.u2[0] + &one();
    cases.push(("u₂ (binds cᵢ)     ", m, CoreError::OuterCommitment2));

    let mut m = message.clone();
    m.p[0] += 1;
    cases.push((
        "p                ",
        m,
        CoreError::AggregationConstantTerm { index: 0 },
    ));

    let mut m = message.clone();
    m.b_double[1] = &m.b_double[1] + &one();
    cases.push((
        "b''(1)           ",
        m,
        CoreError::AggregationConstantTerm { index: 1 },
    ));

    let mut m = message.clone();
    m.g[1] = &m.g[1] + &one();
    cases.push(("g off-diagonal   ", m, CoreError::AsymmetricGarbage));

    let mut m = message.clone();
    m.h[1] = &m.h[1] + &one();
    cases.push(("h off-diagonal   ", m, CoreError::AsymmetricGarbage));

    let mut m = message.clone();
    m.z[0] = &m.z[0] + &one();
    cases.push(("z alone          ", m, CoreError::DigitRecombination));

    let mut m = message.clone();
    m.t[0] = &m.t[0] + &one();
    cases.push(("t alone          ", m, CoreError::DigitRecombination));

    let mut m = message.clone();
    m.g[0] = &m.g[0] + &one();
    cases.push(("g diagonal alone ", m, CoreError::DigitRecombination));

    // Self-consistent edits: value and planes move together, so lines 10–13
    // stay satisfied. Moving the planes also moves the outer commitment, so
    // lines 16 and 17 show up in the *tail* of the report rather than at its
    // head — which is exactly what the report is for.
    let mut m = message.clone();
    m.z[0] = &m.z[0] + &one();
    m.z_digits[0] = &m.z_digits[0] + &one();
    cases.push(("z + its digits   ", m, CoreError::InnerLink));

    let mut m = message.clone();
    m.t[0] = &m.t[0] + &one();
    m.t_digits[0] = &m.t_digits[0] + &one();
    cases.push(("t + its digits   ", m, CoreError::OuterCommitment1));

    let mut m = message.clone();
    m.g[0] = &m.g[0] + &one();
    m.g_digits[0] = &m.g_digits[0] + &one();
    cases.push(("g + its digits   ", m, CoreError::OuterCommitment1));

    let mut m = message.clone();
    m.h[0] = &m.h[0] + &one();
    m.h_digits[0] = &m.h_digits[0] + &one();
    cases.push(("h + its digits   ", m, CoreError::OuterCommitment2));

    // A digit plane pushed past the centered half-width with the next plane
    // compensating, so the value still recombines: only line 13's bound sees
    // it, which is what keeps line 14's budget meaningful.
    let mut m = message.clone();
    m.t_digits[0] = &m.t_digits[0] + &const_elt::<Scalar, D>(bounds.base as i64);
    m.t_digits[1] = &m.t_digits[1] - &one();
    cases.push(("wide digit plane ", m, CoreError::DigitBound));

    for (label, tampered, expected) in cases {
        // The check that fires first must own this component: an unrelated
        // earlier guard would mean the real check is unreachable, which is
        // exactly how a faked step hides.
        let report = verify_core_report(&setup, &relation, &key_seed, &tampered);
        assert!(!report.is_empty(), "{label}: a tampered proof was ACCEPTED");
        assert_eq!(report[0], expected, "{label}: wrong check fired");
        let rest = if report.len() > 1 {
            format!(" (+{} more)", report.len() - 1)
        } else {
            String::new()
        };
        println!("  {label} → {expected}{rest}");
        assert_eq!(
            verify_core(&setup, &relation, &key_seed, &tampered),
            Err(expected),
            "{label}: verify_core must agree with the head of the report"
        );
    }

    // Lines 16 and 17 are the amortization's soundness. No *head* position can
    // reach them (moving `g` or `h` moves their planes, hence the outer
    // commitment, which is checked first), so the assembly asserts they appear
    // in the report at all: that is what distinguishes them from dead code.
    let mut g_edit = message.clone();
    g_edit.g[0] = &g_edit.g[0] + &one();
    g_edit.g_digits[0] = &g_edit.g_digits[0] + &one();
    assert!(
        verify_core_report(&setup, &relation, &key_seed, &g_edit)
            .contains(&CoreError::SelfInnerProduct),
        "⟨z,z⟩ = Σ g_ij cᵢc_j (line 16) never fired"
    );
    let mut h_edit = message.clone();
    h_edit.h[0] = &h_edit.h[0] + &one();
    h_edit.h_digits[0] = &h_edit.h_digits[0] + &one();
    assert!(
        verify_core_report(&setup, &relation, &key_seed, &h_edit).contains(&CoreError::LinearClaim),
        "Σ⟨φᵢ,z⟩cᵢ = Σ h_ij cᵢc_j (line 17) never fired"
    );

    // A false statement must not be provable either: same keys, one unit off.
    let broken = Relation {
        full: relation
            .full
            .iter()
            .enumerate()
            .map(|(i, f)| QuadFn {
                a: f.a.clone(),
                phi: f.phi.clone(),
                b: if i == 0 { &f.b + &one() } else { f.b.clone() },
            })
            .collect(),
        ct_only: relation.ct_only.clone(),
        rank: relation.rank,
        multiplicity: relation.multiplicity,
        norm_bound_sq: relation.norm_bound_sq,
    };
    assert_eq!(
        broken.check(&lifted.s),
        Err(RelationError::FullConstraintNonZero { index: 0 }),
        "the tampered statement must be unsatisfiable for this witness"
    );
    match prove_core(&setup, &broken, &key_seed, &lifted.s) {
        Err(err) => println!("\nfalse statement refused at the prover: {err}"),
        Ok(_) => panic!("a false statement was proved"),
    }
    // …and the verifier reaches the same verdict on an honest-looking proof of
    // a claim nobody can satisfy.
    assert_eq!(
        verify_core(&setup, &broken, &key_seed, &message),
        Err(CoreError::AggregationConstantTerm { index: 0 }),
        "the claim is absorbed into the transcript, so every later challenge
         moves with it and the head of the report is the first one to break"
    );
    let report = verify_core_report(&setup, &broken, &key_seed, &message);
    assert!(
        report.contains(&CoreError::Relation),
        "line 18 must be among the rejections; the report was {report:?}"
    );
    println!(
        "verifier rejects it too: line 18 appears among {} cascade rejections",
        report.len()
    );

    println!("\nWhat the recursion does and does not buy here:");
    println!("  §5.3's target step is wired and checked: the last message is a witness for");
    println!("  R′ = (G, ∅, β′), all {} of eq. (6)'s equations vanish, budget (5) holds,",
        target.relation.full.len());
    println!("  and each of the six equation families rejects by its own name. Lemma 3.7 then");
    println!("  allows this protocol to be run on R′, which is what shrinks O(√N) to polylog.");
    println!("  The size win needs 2n + m < rn, and m = {} here against r·n = {}: this example",
        shape.v_width,
        relation.multiplicity * relation.rank);
    println!("  proves a 192-constraint R1CS, so one level costs {} B rather than saving any.",
        (plan.saving_bits() / 8).abs());
    println!("  It flips at n = {flip} (≈ {} constraints at this reduction's shape), and the",
        flip * D);
    println!("  paper's own level 1 (r = 112, n = 37450, Table 3 p.28) saves {} KB in one step.",
        paper.saving_bits() / 8 / 1024);

    // The flip is a prediction, so it gets tested against a measurement: run the
    // *second* execution on the *first* one's target, at the smallest rank the
    // model says pays, and count the bytes that actually move.
    composed_level(flip);

    println!(
        "\nThe crate's own d = 256 Greyhound constants are deliberately unused: LaBRADOR's\n  d = 64 instance runs on the shape-generic keys of `pcs::key` instead."
    );
    println!("every step above is checked; one recursion level is executed, and its size is measured.");
}
