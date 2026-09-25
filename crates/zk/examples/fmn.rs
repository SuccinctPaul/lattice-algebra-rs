//! Fenzi–Moghaddas–Nguyen, *Lattice-Based Polynomial Commitments: Towards
//! Asymptotic and Concrete Efficiency*, eprint 2023/846 (Journal of Cryptology
//! 2025) — as a scheme assembly: **Fig. 4** (the PowerBASIS commitment, p. 37)
//! plus **Fig. 6** (the recursive `Eval[d, k, h, C, β]`, p. 45), non-interactive
//! by Fiat–Shamir as §5.4/Theorem 5.12 prescribes.
//!
//! Every capability comes from `src`: `TrapGen`/`SamplePre` from
//! [`zk::pcs::trapdoor`], the `(d+1)`-slot basis `B`, its trapdoor `R̃`, the
//! commitment and Eq. (14) from [`zk::pcs::prisis::BasisPair`], the strided
//! folds from [`zk::pcs::prisis`] ([`fold_openings`](zk::pcs::prisis::fold_openings),
//! [`fold_commitment`](zk::pcs::prisis::fold_commitment),
//! [`split_by_stride`](zk::pcs::prisis::split_by_stride)) and
//! [`zk::pcs::slap_tree`] ([`partial_evaluations`], [`fold_coeffs`],
//! [`Alpha`]). This file is the instance, the message order, the transcript and
//! the tampers — nothing else.
//!
//! # Read off the paper
//!
//! * **The commitment is FLAT, not a tree** (Fig. 4). One
//!   `B = [W⁰A −G; …; W^d A −G] ∈ R^{n(d+1) × (m(d+1)+t)}` with one trapdoor
//!   `R̃ = [R₀; …; R_d; 0]`, `B·R̃ = G_{n(d+1)}`, and the CRS is `(A, W, T)`.
//!   A message is the *whole* coefficient vector `(f₀, …, f_d)`, and opening it
//!   means Eq. (14): `A sᵢ + fᵢ e₁ = W⁻ⁱ t` for every slot `i`. So there is
//!   exactly one `A`, one `W`, no levels and no per-node sampling.
//!   **`docs/survey-lattice-pcs.md` §1 lists this scheme's commitment structure
//!   as "tree-based"; the paper contradicts that.** FMN's own §1.7 (p. 18) says
//!   of SLAP: "the authors construct a new commitment scheme that combines *our
//!   PowerBASIS construction together with the Merkle tree paradigm*", i.e. the
//!   tree is SLAP's contribution to the line, and FMN §4 has none. The cost of
//!   that difference is visible in the sizes below: the CRS here is quadratic in
//!   `d` (`T` alone is `(m(d+1)+t) × n(d+1)δ`), which is precisely what
//!   SLAP's abstract complains of ("a CRS and committing time that are
//!   undesirably large, as they are quadratic in the degree").
//! * **Assumption**: ring-BASIS/PRISIS — §3 p. 30: "PRISIS is the instance
//!   where each `W_i := w^{i−1} I_{n+1}`", which is what
//!   [`BasisPair::new`](zk::pcs::prisis::BasisPair::new) builds — reduced to
//!   Module-SIS by **Lemma 3.6** through the *statistical* NTRU trapdoor
//!   generator of Lemma 2.11 (`q ≡ 5 (mod 8)`, `‖T̃_NTRU‖ ≤ Ns`), i.e. Game 2
//!   replaces the aux `w` by `(w, T_NTRU) ← NTRU.TrapGen(q, N, s)` (p. 34).
//!   That reduction is not implemented here; the assumption name is cited so
//!   the assembly's place in it is explicit.
//! * **Fold** (Fig. 5 p. 43, Fig. 6 p. 45). `f(X) = Σ_{t∈[k]} X^{t−1} g_t(X^k)`,
//!   `z_t = g_t(u^k)`, check `z = Σ_t u^{t−1} z_t` (Eq. 17); the verifier sends
//!   `α ← C ⊆ R_q^k`; then `g = Σ α_t g_t`, openings `ẑ_i = Σ_t α_t s_{ki+t−1}`,
//!   and — the trick Lemma 5.1 proves in three lines —
//!   `t' = (Σ_t α_t W^{−(t−1)})·t` with the *same* `A` and the re-powered
//!   `W' = W^k` satisfy `A ẑ_i + g_i e₁ = (W^k)^{−i} t'`, so the instance
//!   shrinks to `R_{d', wβ}` with `d' = (d+1)/k − 1` and **no new sampling**.
//! * **Monomial instantiation** (§5.2 p. 45): `k = 2`, `C = {1} × {Xⁱ}`. Fixing
//!   the first component to `1` is what makes `α₂ − α₂′` a unit in the
//!   2-special-soundness extraction, and it sets the norm multiplier
//!   `w = max_{α∈C} ‖α‖₁ = 2`, which is why `β` doubles per round rather than
//!   growing with `k`.
//! * **Cost** (Lemma 5.5 p. 44, Table 5 p. 47): proof
//!   `h(kN⌈log q⌉ + ⌈log|C|⌉) + (d+1)/k^h (N⌈log q⌉ + mN⌈log(2^h β)⌉)`, prover
//!   `O(md)`, verifier `O((n+m)²(hk + d/k^h))`. Because the *last* term is
//!   linear in `d/k^h`, `h` can be at most `O(log log d)` before the extracted
//!   norm forces `log q ≥ poly(d)` — the paper's own reason for
//!   quasi-polylogarithmic rather than polylogarithmic proofs (p. 47). Its
//!   Marlin instantiation (Table 9, p. 68) is the **17 MB @ 2²⁰ R1CS** figure
//!   quoted in the survey, over 19 polynomial commitments at `log q = 343`.
//!
//! # Instance — a structural demonstration, not a security level
//!
//! Same disclaimer as [`slap`](slap) and [`cmnw`](cmnw): FMN's Table 5 needs
//! `log q ≈ 343` (`q ≡ 5 (mod 8)`, `N = 64`), which this crate cannot encode,
//! so the assembly runs at `q = 2³² − 99` — prime and `≡ 5 (mod 8)`, the
//! congruence FMN's own `q ≡ 5 (mod 8)` hypotheses (Lemma 2.11, §5.4) require,
//! and of 2-adicity 2, so there is no NTT here and every key is the schoolbook
//! [`zk::pcs::key::RingMatrixKey`] the `TrapGen` construction needs anyway.
//! `d = 7` (`d + 1 = 8` slots), `k = 2`, `h = 2` rounds, `n = 1`, `m = 12`,
//! `δ = 256` with 4 planes. **No security level is claimed.**
//!
//! Deviations, all structural: the gadget base is 256 rather than the papers'
//! `δ` (generic in [`zk::pcs::gadget::split`]); `W` is a scalar-unit
//! [`UnitMatrix`](zk::pcs::trapdoor::UnitMatrix) rather than a uniform
//! `GL(n, R_q)` draw (deviation 3 of [`slap`](slap), same reason); the CRS
//! trapdoor is randomised with a bounded perturbation instead of `σ₀`
//! ([`zk::pcs::trapdoor`]'s "What is not claimed"); and the relaxation factors
//! `c ∈ S` of Fig. 4's `Open` are taken to be `1`, the global choice of
//! Def. 2.19's completeness.
//!
//! Not assembled: §5.4's multi-evaluation amortisation (Table 6), §6's
//! field-of-coefficients variant, §7's statistical NTRU reduction, and the
//! Marlin compilation itself.
//!
//! Run with: `cargo run -p lattice-zk --example fmn`

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::Ring;
use std::collections::BTreeSet;
use zk::foundation::fs::{absorb_rings, seed_stream};
use zk::pcs::prisis::{
    fold_commitment, fold_openings, failing_basis_relation, poly_eval, BasisPair,
};
use zk::pcs::slap_tree::{fold_coeffs, partial_evaluations, Alpha};
use zk::pcs::trapdoor::{scalar_elt, scale_vec, vector_infinity_norm, TrapdoorKey, UnitMatrix};

/// `2³² − 99`: prime, `≡ 5 (mod 8)`, `u32`-encodable, no NTT.
type Q = Zq<4294967197>;
/// Ring degree `N` in the papers' notation.
const D: usize = 64;
type Elt_ = PolyRing<Q, D>;

/// Gadget: base 8 with 11 planes — a wide base is the paper's own choice (its
/// Table 9 uses `δ = 28`), and the exactness requirement is
/// `(BASE/2 − 1)·(BASE^DIGITS − 1)/(BASE − 1) ≥ (q−1)/2` on the **negative**
/// side, because `digit_planes`' rounding gives digits in
/// `[[−(BASE/2−1), BASE/2]]`, not `[[−BASE/2, BASE/2]]`: here that is
/// `3·(8¹¹−1)/7 = 3.68·10⁹ ≥ 2.147·10⁹` ✓, whereas `base 256, 4 planes` reaches
/// only `−2.139·10⁹` while its reported `digit_span` claims `2.156·10⁹`.
const BASE: u64 = 8;
const DIGITS: usize = 11;
/// Height `n` of `A`.
const N: usize = 1;
/// Columns of `A`'s uniform half; `m = mbar + n·DIGITS`.
const MBAR: usize = 4;
/// Message slots `d + 1`. FMN commits the whole coefficient vector at once —
/// and its CRS trapdoor `T` is `(m(d+1)+t) × n(d+1)δ` ring elements, i.e.
/// quadratic in the message, which is the cost SLAP's tree removes. At `d+1 = 8`
/// randomising `T` already costs ~10⁶ ring multiplications.
const SLOTS: usize = 8;
/// Folding factor `k`, fixed at 2 by §5.2's monomial instantiation.
const K: usize = 2;
/// Interaction rounds `h` of Fig. 6: `d_r = (d_{r−1}+1)/k − 1`.
const ROUNDS: usize = 2;
/// `w := max_{α ∈ C} ‖α‖₁` for `C = {1} × {Xⁱ}` (§5.2), i.e. `1 + 1`.
const W_CHALLENGE: u64 = 2;
/// Perturbation randomising the CRS trapdoor `T`.
const CRS_PERTURBATION: u32 = 1;

/// Slots left after `ROUNDS` folds: `(d+1)/k^h`.
const FINAL_SLOTS: usize = SLOTS / (1 << ROUNDS);

/// The public statement `(A, W)` plus the claim.
#[derive(Clone)]
struct Instance {
    a: zk::pcs::key::RingMatrixKey<Q, D>,
    w: UnitMatrix<Q, D>,
    t: Vec<Elt_>,
    u: Elt_,
    z: Elt_,
    beta: u64,
}

/// Fig. 6's transcript: `h` rounds of `k` partial evaluations, then
/// `(f_h, (s_{h,i}))`.
#[derive(Clone)]
struct Proof {
    zs: Vec<Vec<Elt_>>,
    final_coeffs: Vec<Elt_>,
    final_openings: Vec<Vec<Elt_>>,
}

/// Fig. 4 `Setup`: `TrapGen`, the unit `W`, the `(d+1)`-slot basis, and the
/// re-randomised trapdoor `T`. `A` and `W` are public; `T` is the trapdoor the
/// printed `crs := (A, W, T)` bundles in, and only `Commit` reads it.
fn setup(
    seed: &[u8; 32],
) -> (
    BasisPair<Q, D, BASE, DIGITS>,
    zk::pcs::key::RingMatrixKey<Q, D>,
    UnitMatrix<Q, D>,
) {
    let td = TrapdoorKey::<Q, D, BASE, DIGITS>::generate(b"fmn-powerbasis", seed, N, MBAR);
    let unit = UnitMatrix::scalar_units(&[scalar_unit(b"fmn-w", seed)])
        .expect("nonzero scalar of a field ring is a unit");
    let pair = BasisPair::new(&td, &unit, SLOTS).expect("shapes are consistent by construction");
    let mut tseed = *seed;
    for (k, b) in tseed.iter_mut().enumerate() {
        *b = seed[k] ^ 0x9e;
    }
    let trap = pair
        .randomise_trapdoor(&tseed, CRS_PERTURBATION)
        .expect("the CRS preimage is well-shaped");
    (pair, trap, unit)
}

/// A nonzero scalar of `R_q`, i.e. a unit: `w ← R_q^×` of Fig. 1 / Fig. 4
/// item 2, drawn deterministically.
fn scalar_unit(domain: &[u8], seed: &[u8; 32]) -> Q {
    use algebra::crypto::xof::{Shake256Xof as X, Xof};
    let mut xof = X::new(&[]);
    xof.absorb(domain);
    xof.absorb(seed);
    let mut buf = [0u8; 8];
    xof.squeeze(&mut buf);
    let raw = u64::from_le_bytes(buf);
    Q::from(raw % (Q::MODULUS - 1) + 1)
}

/// Fig. 4 `Commit`: the preimage under `B` of `(−fᵢ Wⁱ e₁)ᵢ`, split into
/// `(s₀, …, s_d, t̂)`, with commitment `t = G·t̂`.
fn commit(
    pair: &BasisPair<Q, D, BASE, DIGITS>,
    trap: &zk::pcs::key::RingMatrixKey<Q, D>,
    coeffs: &[Elt_],
) -> (Vec<Elt_>, Vec<Vec<Elt_>>) {
    let c = pair.commit(trap, coeffs).expect("one slot per coefficient");
    (c.t, c.opening.s)
}

/// The public statement of `f(u) = z`.
fn statement(
    pair: &BasisPair<Q, D, BASE, DIGITS>,
    w: &UnitMatrix<Q, D>,
    t: &[Elt_],
    u: &Elt_,
    coeffs: &[Elt_],
    beta: u64,
) -> Instance {
    Instance {
        a: pair.a().clone(),
        w: w.clone(),
        t: t.to_vec(),
        u: u.clone(),
        z: poly_eval(coeffs, u),
        beta,
    }
}

/// Fig. 6 `Eval`: `ROUNDS` folds, each absorbing its `k` partial evaluations
/// before squeezing the next `α`.
fn prove(inst: &Instance, coeffs: &[Elt_], openings: &[Vec<Elt_>]) -> Proof {
    let mut fs = Fs::new(inst);
    let mut coeffs = coeffs.to_vec();
    let mut s = openings.to_vec();
    let mut t = inst.t.clone();
    let mut u = inst.u.clone();
    let mut z = inst.z.clone();
    let mut w = inst.w.clone();
    let mut zs = Vec::with_capacity(ROUNDS);
    for r in 0..ROUNDS {
        let u_next = pow_u(&u, K);
        let partial = partial_evaluations(&coeffs, &u_next, K).expect("strided");
        let alpha = fs.alpha(&partial, r);
        zs.push(partial);
        let col: Vec<Elt_> = alpha.values[0].iter().map(|slot| slot[0].clone()).collect();
        coeffs = fold_coeffs(&coeffs, &col).expect("strided");
        s = fold_openings(&s, &col).expect("strided");
        t = fold_commitment(&w_inv_powers(&w, K), &col, &t).expect("well-shaped");
        z = fold_claim(zs.last().expect("pushed"), &col);
        w = w.powered(K).expect("a power of a unit is a unit");
        u = u_next;
    }
    let _ = z;
    Proof {
        zs,
        final_coeffs: coeffs,
        final_openings: s,
    }
}

/// `z_r = Σ_t α_t z_{r,t}` — Fig. 6 item 2(h).
fn fold_claim(partial: &[Elt_], alpha: &[Elt_]) -> Elt_ {
    let mut acc = scalar_elt::<Q, D>(Q::ZERO);
    for (t, a) in alpha.iter().enumerate() {
        acc = acc + scale_vec(a, &[partial[t].clone()])[0].clone();
    }
    acc
}

/// `(I, W⁻¹, …, W^{-(k−1)})`, the multiplier list `fold_commitment` consumes.
fn w_inv_powers(w: &UnitMatrix<Q, D>, count: usize) -> Vec<zk::pcs::key::RingMatrixKey<Q, D>> {
    w.powers(count).1
}

/// `x^e` for a ring element and a small exponent.
fn pow_u(x: &Elt_, e: usize) -> Elt_ {
    let mut acc = scalar_elt::<Q, D>(Q::ONE);
    for _ in 0..e {
        acc = acc * x.clone();
    }
    acc
}

/// The Fiat–Shamir chain of Fig. 6, walked identically by both sides.
struct Fs {
    tr: Transcript<Shake256Xof>,
}

impl Fs {
    fn new(inst: &Instance) -> Self {
        let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/fmn");
        for i in 0..inst.a.rows() {
            absorb_rings(&mut tr, b"crs-a", inst.a.row(i));
        }
        for i in 0..inst.w.value().rows() {
            absorb_rings(&mut tr, b"crs-w", inst.w.value().row(i));
        }
        absorb_rings(&mut tr, b"t", &inst.t);
        absorb_rings(&mut tr, b"u", &[inst.u.clone()]);
        absorb_rings(&mut tr, b"z", &[inst.z.clone()]);
        Self { tr }
    }

    /// §5.2's `C = {1} × {Xⁱ}`: the first component is fixed, the second is a
    /// monomial drawn after absorbing this round's message.
    fn alpha(&mut self, partial: &[Elt_], round: usize) -> Alpha<Q, D> {
        absorb_rings(&mut self.tr, b"z-partial", partial);
        self.tr.absorb(b"round", &(round as u64).to_le_bytes());
        let seed: [u8; 32] = {
            let mut out = [0u8; 32];
            out.copy_from_slice(&self.tr.challenge_bytes(32));
            out
        };
        let mut xof = seed_stream::<Shake256Xof>(b"fmn-alpha", &seed);
        let mut a = Alpha::sample(1, K, 1, &mut xof);
        a.values[0][0][0] = scalar_elt::<Q, D>(Q::ONE);
        a
    }
}

/// Fig. 6 item 2(b): `z_{r−1} = Σ_{t∈[k]} u_{r−1}^{t−1} z_{r−1,t}`, the only
/// check an intermediate round carries (the openings stay with the prover until
/// step 3, which is what makes the last term of the proof dominate its size).
fn check_round(r: usize, z: &Elt_, partial: &[Elt_], u: &Elt_) -> Option<String> {
    if poly_eval(partial, u) == *z {
        None
    } else {
        Some(format!("z-decompose(round {})", r + 1))
    }
}

/// Every check of Fig. 6, named, without short-circuiting: the verifier
/// rebuilds each `α` from the messages it received (so a tamper on an absorbed
/// message cascades), and then runs item 4 — the claim, Eq. (14) at the folded
/// multiplier `W_h`, and the `β_h` gate — on the received final message.
fn failing(inst: &Instance, proof: &Proof) -> Vec<String> {
    let mut bad = Vec::new();
    let mut t = inst.t.clone();
    let mut u = inst.u.clone();
    let mut z = inst.z.clone();
    let mut w = inst.w.clone();
    let mut beta = inst.beta;
    let mut fs = Fs::new(inst);
    for (r, partial) in proof.zs.iter().enumerate() {
        if let Some(name) = check_round(r, &z, partial, &u) {
            bad.push(name);
        }
        let alpha = fs.alpha(partial, r);
        let col: Vec<Elt_> = alpha.values[0].iter().map(|slot| slot[0].clone()).collect();
        t = fold_commitment(&w_inv_powers(&w, K), &col, &t).expect("well-shaped");
        z = fold_claim(partial, &col);
        w = w.powered(K).expect("a power of a unit is a unit");
        u = pow_u(&u, K);
        beta *= W_CHALLENGE;
    }
    // Fig. 6 item 4.
    if poly_eval(&proof.final_coeffs, &u) != z {
        bad.push("eval(final claim)".to_string());
    }
    let coeffs = &proof.final_coeffs;
    let s = &proof.final_openings;
    if s.len() != coeffs.len() {
        bad.push(format!(
            "shape: {} openings for {} coefficients",
            s.len(),
            coeffs.len()
        ));
        return bad;
    }
    for (i, v) in s.iter().enumerate() {
        if v.len() != inst.a.cols() {
            bad.push(format!("shape: opening {i} is {} wide", v.len()));
        }
        if vector_infinity_norm(v) > beta {
            bad.push(format!("final-norm(slot {i}) <= {beta}"));
        }
    }
    bad.extend(
        failing_basis_relation(&inst.a, &w.powers(coeffs.len()).1, &t, coeffs, s)
            .expect("well-shaped openings"),
    );
    bad
}

/// The verifier: accept only when every check holds.
fn verify(inst: &Instance, proof: &Proof) -> Result<(), String> {
    let bad = failing(inst, proof);
    if bad.is_empty() {
        Ok(())
    } else {
        Err(bad[0].clone())
    }
}

fn expect_reject(label: &str, inst: &Instance, proof: &Proof, expected: &[&str]) -> Vec<String> {
    let bad = failing(inst, proof);
    // The tamper must fail *exactly* the equations it violates: no check may
    // pass that the paper's verifier would reject, and none may fail for a
    // reason the case does not account for.
    assert!(
        !bad.is_empty(),
        "{label}: the tamper was accepted: {bad:?}"
    );
    let got: BTreeSet<&str> = bad.iter().map(String::as_str).collect();
    let want: BTreeSet<&str> = expected.iter().copied().collect();
    assert_eq!(
        got, want,
        "{label}: unexpected failing set {bad:?}"
    );
    match verify(inst, proof) {
        Err(first) => assert_eq!(first, bad[0], "{label}: attribution"),
        Ok(()) => panic!("{label}: the tamper verified"),
    }
    println!("  {label}\n      rejected by {bad:?}");
    bad
}

fn main() {
    let seed = [0xf7u8; 32];
    let (pair, trap, w) = setup(&seed);
    let coeffs: Vec<Elt_> = (0..SLOTS)
        .map(|i| scalar_elt::<Q, D>(Q::from(5 + 11 * i as u64)))
        .collect();
    let u = scalar_elt::<Q, D>(Q::from(23u64));
    let (t, s) = commit(&pair, &trap, &coeffs);
    let beta = pair.certified_bound(&trap);
    assert!(
        beta.saturating_mul(W_CHALLENGE.pow(ROUNDS as u32) * 4) < (Q::MODULUS - 1) / 2,
        "the gate must sit inside the centered range to be testable: β = {beta}"
    );
    let inst = statement(&pair, &w, &t, &u, &coeffs, beta);

    println!(
        "FMN (eprint 2023/846) Fig.4 + Fig.6 — q = 2^32-99, N = {D}, n = {N}, m = {}, d = {}, k = {K}, h = {ROUNDS}",
        MBAR + N * DIGITS,
        SLOTS - 1
    );
    println!("  structural demonstration only: Table 9 needs log q ≈ 343 (this instance has 32)");
    println!("  FLAT PowerBASIS: one A, one W, {} slots, no Merkle levels (cf. examples/slap.rs)", SLOTS);
    println!("  certified opening slack β = {beta}");

    // Fig. 4's Open over the whole message: Eq. (14) for every slot, at once.
    let commit_obj = pair.commit(&trap, &coeffs).expect("commit");
    assert!(
        pair.failing(&commit_obj, &coeffs).expect("shapes").is_empty(),
        "Eq. (14) must hold on every slot of an honest commitment"
    );
    println!(
        "  Fig. 4: commitment t is {} ring elements, opening is {} × {} — Eq. (14) holds on all {} slots",
        commit_obj.t.len(),
        s.len(),
        s[0].len(),
        SLOTS
    );
    let mut bad_slot = commit_obj.clone();
    bad_slot.opening.s[3][0] = scalar_elt::<Q, D>(Q::from(beta + 7));
    let one = pair.failing(&bad_slot, &coeffs).expect("shapes");
    assert_eq!(one.len(), 1, "one slot's equation breaks alone: {one:?}");
    println!("  Eq. (14) is per-slot: corrupting s₃ trips only slot 3: {one:?}");
    let ones = vec![scalar_elt::<Q, D>(Q::ONE); SLOTS];
    assert!(
        pair.failing_norms(&bad_slot, &ones, beta)
            .expect("shapes")
            .iter()
            .any(|n| n.contains("s[3]")),
        "the relaxation gate must see the same slot"
    );

    let proof = prove(&inst, &coeffs, &s);
    let bad = failing(&inst, &proof);
    assert!(bad.is_empty(), "the honest proof must verify: {bad:?}");
    let bytes = (proof.zs.len() * K + proof.final_coeffs.len()) * D * 4
        + proof.final_openings.iter().map(|v| v.len()).sum::<usize>() * D * 4;
    println!(
        "  Fig. 6: {} rounds fold d = {} down to {}, proof = {} bytes, claim f(u) = z verified",
        ROUNDS,
        SLOTS - 1,
        FINAL_SLOTS - 1,
        bytes
    );

    let mut tripped: Vec<&str> = Vec::new();
    let mut note = |bad: Vec<String>| {
        for name in bad {
            let f: &'static str = if name.starts_with("z-decompose") {
                "z-decompose"
            } else if name.starts_with("final-norm") {
                "final-norm"
            } else if name.starts_with("eval") {
                "eval"
            } else if name.starts_with("eq14") {
                "eq14"
            } else {
                "other"
            };
            if !tripped.contains(&f) {
                tripped.push(f);
            }
        }
    };

    // A false claim z: absorbed before every α, so each round's recombination
    // fires and the folded commitment no longer matches the received openings.
    // Fig. 6 item 4 (`P̂(u) = z`) fires too — with `z` moved out from under an
    // honest `P̂`, that equation is simply false, and the neighbouring tamper
    // cases below already list `eval(final claim)` on the same grounds.
    let wrong_claim = Instance {
        z: inst.z.clone() + scalar_elt::<Q, D>(Q::ONE),
        ..inst.clone()
    };
    note(expect_reject(
        "false claim z",
        &wrong_claim,
        &proof,
        &[
            "z-decompose(round 1)",
            "z-decompose(round 2)",
            "eval(final claim)",
            "eq14[slot 0]",
            "eq14[slot 1]",
        ],
    ));

    // A false partial evaluation in the first round: it is absorbed before α₁,
    // so α₁ changes, and *both* quantities the verifier derives from it change —
    // the folded commitment (hence Eq. 14 at every slot) and the round-1 claim
    // `z₁ = Σ_t α_t z_{1,t}` it compares round 2's recombination against. So
    // round 2's own `z-decompose` fires as a cascade, not as an independent
    // equation: the received `zs[1]` is honest but the `z₁` rebuilt from the
    // tampered α₁ no longer equals it.
    let mut lied = proof.clone();
    lied.zs[0][0] = lied.zs[0][0].clone() + scalar_elt::<Q, D>(Q::ONE);
    note(expect_reject(
        "false partial evaluation in round 1",
        &inst,
        &lied,
        &[
            "z-decompose(round 1)",
            "z-decompose(round 2)",
            "eval(final claim)",
            "eq14[slot 0]",
            "eq14[slot 1]",
        ],
    ));

    // A false partial evaluation in the LAST round: α₂ changes, so t₂ changes
    // and Eq. (14) breaks, but the recombination of round 1 is untouched.
    let mut lied_last = proof.clone();
    lied_last.zs[ROUNDS - 1][1] =
        lied_last.zs[ROUNDS - 1][1].clone() + scalar_elt::<Q, D>(Q::ONE);
    note(expect_reject(
        "false partial evaluation in the last round",
        &inst,
        &lied_last,
        &[
            "z-decompose(round 2)",
            "eval(final claim)",
            "eq14[slot 0]",
            "eq14[slot 1]",
        ],
    ));

    // A stale commitment. `t` is absorbed before the first α (Fig. 6 binds the
    // transcript to the statement), so swapping it re-derives α₁ and α₂: Eq. (14)
    // breaks at both slots, and so does round 2's recombination because the
    // verifier's `z₁` is folded with the tampered α₁. Only round 1's own
    // `z-decompose` survives — it reads `z`, `u` and the received partial, none
    // of which moved.
    let other_coeffs: Vec<Elt_> = (0..SLOTS)
        .map(|i| scalar_elt::<Q, D>(Q::from(9 + 13 * i as u64)))
        .collect();
    let (other_t, _) = commit(&pair, &trap, &other_coeffs);
    let stale = Instance {
        t: other_t,
        ..inst.clone()
    };
    note(expect_reject(
        "commitment of a different polynomial",
        &stale,
        &proof,
        &[
            "z-decompose(round 2)",
            "eval(final claim)",
            "eq14[slot 0]",
            "eq14[slot 1]",
        ],
    ));

    // The final message is sent after the last challenge: each tamper there
    // isolates its own equation. A false coefficient breaks the claim and
    // *only* its own slot — `eq14[slot i]` is `A sᵢ + fᵢ e₁ = W⁻ⁱ t`, which reads
    // `fᵢ` and `sᵢ` alone (t is shared but unchanged here), so `slot 0` staying
    // green is what makes Eq. (14) a per-slot family rather than one equation.
    let mut false_coeff = proof.clone();
    false_coeff.final_coeffs[1] =
        false_coeff.final_coeffs[1].clone() + scalar_elt::<Q, D>(Q::ONE);
    note(expect_reject(
        "false coefficient of the folded polynomial",
        &inst,
        &false_coeff,
        &["eval(final claim)", "eq14[slot 1]"],
    ));

    let mut false_opening = proof.clone();
    false_opening.final_openings[0][0] =
        false_opening.final_openings[0][0].clone() + scalar_elt::<Q, D>(Q::ONE);
    note(expect_reject(
        "false folded opening (slot 0)",
        &inst,
        &false_opening,
        &["eq14[slot 0]"],
    ));

    let final_beta = (0..ROUNDS).fold(beta, |acc, _| acc * W_CHALLENGE);
    let mut fat_opening = proof.clone();
    fat_opening.final_openings[1][0] = scalar_elt::<Q, D>(Q::from(final_beta + 7));
    note(expect_reject(
        "oversized folded opening (slot 1)",
        &inst,
        &fat_opening,
        &[&format!("final-norm(slot 1) <= {final_beta}"), "eq14[slot 1]"]
            .into_iter()
            .collect::<Vec<&str>>()
            .as_slice(),
    ));

    // Fig. 4's two conditions have to be *independent*, not one check with two
    // names. Every case above violates the equation and `final-norm` only ever
    // rode along with it, so it proves nothing on its own. Here is the other
    // direction. `R_q` is commutative, so
    //     v = (a₀₁, −a₀₀, 0, …, 0)   satisfies   (A v)₀ = a₀₀a₀₁ − a₀₁a₀₀ = 0.
    // Adding that kernel element to slot 0's opening leaves Eq. (14) exactly
    // true — `s₀ + v` is a genuine *alternative preimage* of the same commitment
    // — and only the norm gate refuses it. Delete the `β` comparison from
    // `failing` and this proof would verify, which is exactly why Theorem 5.12's
    // extraction needs the bound: shortness, not the equation, is what binds.
    let zero = scalar_elt::<Q, D>(Q::ZERO);
    let kernel: Vec<Elt_> = (0..inst.a.cols())
        .map(|j| match j {
            0 => inst.a.get(0, 1).expect("A has ≥ 2 columns").clone(),
            1 => -inst.a.get(0, 0).expect("A has a column 0").clone(),
            _ => zero.clone(),
        })
        .collect();
    assert!(
        kernel.iter().any(|e| e != &zero),
        "the two columns of A must be distinct for v to be nonzero"
    );
    assert_eq!(
        inst.a.matvec(&kernel).expect("well-shaped"),
        vec![zero.clone(); N],
        "v must lie in the kernel of A"
    );
    let mut alt_opening = proof.clone();
    alt_opening.final_openings[0] = proof.final_openings[0]
        .iter()
        .zip(kernel.iter())
        .map(|(s, k)| s.clone() + k.clone())
        .collect();
    assert!(
        vector_infinity_norm(&alt_opening.final_openings[0]) > final_beta,
        "the alternative opening must overflow the bound for this case to bite"
    );
    note(expect_reject(
        "alternative preimage: Eq. (14) holds, only the norm gate refuses",
        &inst,
        &alt_opening,
        &[&format!("final-norm(slot 0) <= {final_beta}")],
    ));

    for name in ["z-decompose", "eval", "eq14", "final-norm"] {
        assert!(
            tripped.contains(&name),
            "no tamper is caught by {name} — it is not being tested"
        );
    }
    println!("  every tamper is rejected by the equations it actually violates");
}
