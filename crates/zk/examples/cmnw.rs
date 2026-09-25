//! CMNW's concretely efficient univariate PCS argument — Cini–Malavolta–
//! Nguyen–Wee, eprint 2024/281, **Appendix A, Figure 7** — as a scheme
//! assembly.
//!
//! Like [`greyhound_pcs`](greyhound_pcs), this file holds no cryptographic
//! logic. The nested Ajtai keys come from [`zk::pcs::key`], the base-2 gadget
//! `G`/`G⁻¹` from [`zk::pcs::gadget`], every tensor contraction from
//! [`zk::pcs::mixed`], the σ-automorphism from [`zk::pcs::packing`], and the
//! coefficient-level projection line — the paper's approximate range proof —
//! from [`zk::pcs::projection`]. What lives here is the instance, the message
//! order, and the seven equations Fig. 7 prints.
//!
//! # What the argument proves
//!
//! The relation (paper Eq. 18) is a nested-gadget opening: binary digit
//! vectors `s₁`, `s₂` with
//!
//! ```text
//! G_{r₀r₁n}·s₁ = (I_{r₀r₁} ⊗ A₂)·s₂                        layers agree
//! t            = (I_{r₀} ⊗ A₁)·s₁                          the commitment
//! u            = x₀ᵀ·(I_{r₀}⊗x₁ᵀ)·(I_{r₀r₁}⊗x₂ᵀ)·G·s₂     the claim
//! ```
//!
//! so `u` is the committed polynomial evaluated at the point encoded by
//! `(x₀, x₁, x₂)`. Shortness is *not* proved by a gadget recursion: the
//! verifier sends a random `{−1,0,1}` matrix `P` over the **coefficient
//! field**, then a random `B`, and the prover's `γ` ties the two views
//! together (Eq. 21–22). That crossing between the coefficient and ring views
//! is why [`zk::pcs::projection`] is its own capability.
//!
//! # Instance
//!
//! `q = 2³² − 99` is prime and `≡ 5 (mod 8)`, the congruence the paper's
//! Lyubashevsky–Seiler short-inverse step needs — and the reason this
//! instance has no NTT, so every step runs in the coefficient domain. Toy
//! dimensions (`d = 64`, `α = 32` digits, `r₀ = r₁ = r₂ = 2`, `n = 1`) keep the
//! example interactive; the three gates are Lemma 5's formulas, not tuned
//! constants.
//!
//! Two deliberate deviations from the paper's *concrete* parameters, both
//! structural rather than numerical: the gadget here is the binary one
//! (`BASE = 2`, `α = ⌈log₂ q⌉` digits) where App. A takes `δ = q^{1/α}` with
//! `α` digits — [`zk::pcs::gadget::split`] is generic in the base, so the
//! δ-gadget is a parameter change, not a new capability; and `log q = 32` is
//! far below the ≈2⁶⁰ the paper's size table assumes, so this demonstrates
//! the protocol, not a security level.
//!
//! Run with: `cargo run -p lattice-zk --example cmnw`

use algebra::crypto::sampling::BitStream;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::{PolynomialQuotientRing, Ring};
use zk::foundation::encoding::u32s_to_le_bytes;
use zk::foundation::fs::{absorb_rings, seed_stream};
use zk::foundation::sampling::{centered_bounded_poly, from_centered, uniform_vec_from_seed};
use zk::pcs::gadget::{join, split};
use zk::pcs::key::{apply_blockwise, RingMatrixKey};
use zk::pcs::mixed::{dot, BlockMat};
use zk::pcs::projection::{
    const_term, dot as field_dot, from_coeffs, gamma_stack, sigma_matrix, to_coeffs, FieldMat,
};
use zk::shortness::exact_l2::max_magnitude;

/// `2³² − 99`: prime, `≡ 5 (mod 8)`, and small enough for the `u32` encoding
/// the transcript uses.
type Q = Zq<4294967197>;
/// Ring degree `d`.
const D: usize = 64;
type Elt = PolyRing<Q, D>;

/// Gadget digits per ring element, `⌈log₂ q⌉`, so `2^α > q` and the split is
/// exact.
const ALPHA: usize = 32;
/// Ajtai rows per level, the paper's `n`.
const N: usize = 1;
/// The three block counts of the √-style split.
const R0: usize = 2;
const R1: usize = 2;
const R2: usize = 2;
/// Projection rows λ.
const LAM: usize = 8;
/// `l = ⌈λ / log q⌉` (App. A, under Eq. 20): rows of `B`, the soundness boost.
const LROWS: usize = 1;
/// Per-coefficient bound κ of the challenge ring elements — they are ternary.
const KAPPA: usize = 1;

/// Ring elements per `e`-block: `r₂nα`.
const EBLK: usize = R2 * N * ALPHA;
/// Columns of `P`: the coefficient length of one `e`-block.
const P_COLS: usize = EBLK * D;

/// Lemma 5: `β₁ ≥ r₀κd`.
const BETA1: u64 = (R0 * KAPPA * D) as u64;
/// Lemma 5: `β_p ≥ β₁·r₂nαd`.
const BETA_P: u64 = BETA1 * P_COLS as u64;
/// Lemma 5: `β₂ ≥ β₁·r₁κd`.
const BETA2: u64 = BETA1 * (R1 * KAPPA * D) as u64;

/// Fig. 7's equations and Lemma 5's gates, named once so the prover, the
/// verifier and the demo agree on what each one is.
const C1: &str = "1: x₀ᵀ·v₀ = u";
const C2: &str = "2: x₁ᵀ·v₁ = c₁ᵀ·v₀";
const C3: &str = "3: x₂ᵀ·G·y₂ = c₂ᵀ·v₁";
const C4: &str = "4: const γᵢⱼ = ⟨bᵢ, p⟩";
const C5: &str = "5: A₁·y₁ = (c₁ᵀ⊗I)·t";
const C6: &str = "6: A₂·y₂ = (c₂ᵀ⊗Iₙ)·G·y₁";
const C7: &str = "7: N·y₂ = (c₂ᵀ⊗I_l)·γ";
const G1: &str = "g1: ‖y₁ ≤ β₁";
const G2: &str = "g2: ‖p⃗‖ ≤ β_p";
const G3: &str = "g3: ‖y₂‖ ≤ β₂";

/// Why the proof was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
enum CmnwError {
    /// The first Fig. 7 equation or Lemma 5 gate that failed.
    Rejected(&'static str),
    /// A proof component did not have the shape the instance fixes.
    Malformed(&'static str),
}

impl core::fmt::Display for CmnwError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Rejected(what) => write!(f, "rejected: {what}"),
            Self::Malformed(what) => write!(f, "malformed proof: {what}"),
        }
    }
}

/// Public parameters: the two nested Ajtai keys, the evaluation point, the
/// commitment `t` and the claimed evaluation `u`.
#[derive(Clone)]
struct Instance {
    a1: RingMatrixKey<Q, D>,
    a2: RingMatrixKey<Q, D>,
    x0: Vec<Elt>,
    x1: Vec<Elt>,
    x2: Vec<Elt>,
    t: Vec<Elt>,
    u: Elt,
}

/// The secret half of the relation.
struct Witness {
    s1: Vec<Elt>,
    s2: Vec<Elt>,
}

/// The prover's messages, in Fig. 7's order. `e` is never sent — that is the
/// point of the projection.
#[derive(Clone)]
struct Proof {
    v0: Vec<Elt>,
    y1: Vec<Elt>,
    v1: Vec<Elt>,
    p: Vec<Q>,
    gamma: Vec<Elt>,
    y2: Vec<Elt>,
}

/// The ring element `1`.
fn one() -> Elt {
    Elt::from_coefficients(vec![Q::ONE])
}

/// The ring element `X^k` — a bump that leaves the constant term alone.
fn monomial(k: usize) -> Elt {
    let mut coeffs = vec![Q::ZERO; D];
    coeffs[k] = Q::ONE;
    Elt::from_coefficients(coeffs)
}

/// `(I_{r₀r₁} ⊗ x₂ᵀ) · (I_{r₀} ⊗ x₁ᵀ)`-style fold of a gadget-recombined
/// vector down to `r₀n` elements: Fig. 7's `v₀` and `v₁`.
fn fold_down(recombined: &[Elt], outer: usize, inner_blocks: usize, x: &[Elt]) -> Vec<Elt> {
    BlockMat::new(outer, inner_blocks, recombined.to_vec())
        .expect("instance-sized")
        .contract_cols(x)
        .expect("point of the right width")
}

/// The committed polynomial of the demo instance: `r₀r₁r₂n` small ring
/// elements. Nothing about it is public except through `t` and `u`.
fn committed() -> Vec<Elt> {
    (0..R0 * R1 * R2 * N)
        .map(|i| {
            Elt::from_coefficients(
                (0..D)
                    .map(|k| from_centered::<Q>(((i * 7 + k * 3) % 9) as i64 - 4))
                    .collect(),
            )
        })
        .collect()
}

/// Build the instance and a witness by running the nested-gadget chain
/// backwards: `f → s₂ → (I⊗A₂)s₂ → s₁ → t`, then evaluate `f` at the point.
fn setup(seed: &[u8; 32]) -> (Instance, Witness) {
    let a1 = RingMatrixKey::setup(b"cmnw-a1", seed, N, R1 * N * ALPHA);
    let a2 = RingMatrixKey::setup(b"cmnw-a2", seed, N, R2 * N * ALPHA);
    let x0 = uniform_vec_from_seed::<Q, D>(b"cmnw-x0", seed, R0);
    let x1 = uniform_vec_from_seed::<Q, D>(b"cmnw-x1", seed, R1);
    let x2 = uniform_vec_from_seed::<Q, D>(b"cmnw-x2", seed, R2);

    let f = committed();
    let s2 = split::<Q, D, 2, ALPHA>(&f);
    let layer2 = apply_blockwise(&a2, &s2.chunks(EBLK).collect::<Vec<_>>()).expect("aligned");
    let s1 = split::<Q, D, 2, ALPHA>(&layer2);
    let t = apply_blockwise(&a1, &s1.chunks(R1 * N * ALPHA).collect::<Vec<_>>()).expect("aligned");

    // The digit vectors are binary by construction, which is what makes
    // Lemma 5's bounds the right ones.
    assert_eq!(max_magnitude(&to_coeffs(&s1)), 1);
    assert_eq!(max_magnitude(&to_coeffs(&s2)), 1);
    // And the two layers do agree, i.e. the witness is in the relation.
    assert_eq!(join::<Q, D, 2, ALPHA>(&s1), layer2);

    let v0 = fold_down(&fold_down(&f, R0 * R1, R2, &x2), R0, R1, &x1);
    let u = dot(&x0, &v0);
    (
        Instance {
            a1,
            a2,
            x0,
            x1,
            x2,
            t,
            u,
        },
        Witness { s1, s2 },
    )
}

/// The Fiat–Shamir chain. Prover and verifier walk **the same** functions in
/// the same order, so the two sides cannot derive different challenges — the
/// failure mode that once made [`zk::pcs::mle`] reject honest proofs.
struct Fs {
    tr: Transcript<Shake256Xof>,
}

impl Fs {
    fn new(inst: &Instance) -> Self {
        let mut tr = Transcript::new(b"lattice-algebra/Z7/cmnw");
        for i in 0..inst.a1.rows() {
            absorb_rings(&mut tr, b"a1", inst.a1.row(i));
        }
        for i in 0..inst.a2.rows() {
            absorb_rings(&mut tr, b"a2", inst.a2.row(i));
        }
        absorb_rings(&mut tr, b"x0", &inst.x0);
        absorb_rings(&mut tr, b"x1", &inst.x1);
        absorb_rings(&mut tr, b"x2", &inst.x2);
        absorb_rings(&mut tr, b"t", &inst.t);
        absorb_rings(&mut tr, b"u", &[inst.u.clone()]);
        Self { tr }
    }

    fn seed(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out.copy_from_slice(&self.tr.challenge_bytes(32));
        out
    }

    /// `c ← C^len`: ternary challenges, so κ = 1 and Lemma 5's bounds apply.
    fn challenges(&mut self, label: &[u8], len: usize) -> Vec<Elt> {
        let seed = self.seed();
        let mut xof = seed_stream::<Shake256Xof>(label, &seed);
        let mut stream = BitStream::new(&mut xof);
        (0..len)
            .map(|_| centered_bounded_poly::<Q, _, D>(&mut stream, KAPPA as u32))
            .collect()
    }

    fn c1(&mut self, v0: &[Elt]) -> Vec<Elt> {
        absorb_rings(&mut self.tr, b"v0", v0);
        self.challenges(b"cmnw-c1", R0)
    }

    fn p(&mut self, y1: &[Elt], v1: &[Elt]) -> FieldMat<Q> {
        absorb_rings(&mut self.tr, b"y1", y1);
        absorb_rings(&mut self.tr, b"v1", v1);
        FieldMat::ternary(b"cmnw-P", &self.seed(), LAM, P_COLS)
    }

    fn b(&mut self, p: &[Q]) -> FieldMat<Q> {
        let bytes: Vec<u8> = p
            .iter()
            .flat_map(|c| u32s_to_le_bytes(&[c.to_u128() as u32]))
            .collect();
        self.tr.absorb(b"p", &bytes);
        FieldMat::uniform(b"cmnw-B", &self.seed(), LROWS, LAM)
    }

    fn c2(&mut self, gamma: &[Elt]) -> Vec<Elt> {
        absorb_rings(&mut self.tr, b"gamma", gamma);
        self.challenges(b"cmnw-c2", R1)
    }
}

/// Rows `nᵢ` of `B·P`, each grouped back into ring elements: the prover's view
/// of the projection triangle, and the verifier's once it re-derives `B`.
fn sigma_rows(b: &FieldMat<Q>, p: &FieldMat<Q>) -> Vec<Vec<Elt>> {
    let bp = b.matmul(p).expect("instance-sized");
    (0..bp.rows())
        .map(|i| from_coeffs::<Q, D>(bp.row(i)))
        .collect()
}

/// The prover: Fig. 7's left column, top to bottom.
fn prove(inst: &Instance, w: &Witness) -> Proof {
    let mut fs = Fs::new(inst);
    let f = join::<Q, D, 2, ALPHA>(&w.s2);
    let v0 = fold_down(&fold_down(&f, R0 * R1, R2, &inst.x2), R0, R1, &inst.x1);
    let c1 = fs.c1(&v0);

    let y1 = BlockMat::new(R0, R1 * N * ALPHA, w.s1.clone())
        .expect("aligned")
        .contract_rows(&c1)
        .expect("challenge of the right width");
    let e = BlockMat::new(R0, R1 * R2 * N * ALPHA, w.s2.clone())
        .expect("aligned")
        .contract_rows(&c1)
        .expect("challenge of the right width");
    let v1 = fold_down(&join::<Q, D, 2, ALPHA>(&e), R1, R2 * N, &inst.x2);

    let p_mat = fs.p(&y1, &v1);
    let p = p_mat.project_blocks(&to_coeffs(&e), R1).expect("aligned");
    let b_mat = fs.b(&p);
    let n_rows = sigma_rows(&b_mat, &p_mat);
    let n_refs: Vec<&[Elt]> = n_rows.iter().map(|r| r.as_slice()).collect();
    let e_blocks: Vec<&[Elt]> = e.chunks(EBLK).collect();
    let gamma = gamma_stack(&n_refs, &e_blocks);

    let c2 = fs.c2(&gamma);
    let y2 = BlockMat::new(R1, EBLK, e)
        .expect("aligned")
        .contract_rows(&c2)
        .expect("challenge of the right width");
    Proof {
        v0,
        y1,
        v1,
        p,
        gamma,
        y2,
    }
}

/// Every Fig. 7 equation and Lemma 5 gate, evaluated without short-circuiting,
/// as the names that did **not** hold. One source of truth for the checks is
/// what lets the demo attribute each tamper to the equations it really trips.
fn failing(inst: &Instance, pr: &Proof) -> Result<Vec<&'static str>, CmnwError> {
    let shapes = [
        (pr.v0.len(), R0 * N),
        (pr.y1.len(), R1 * N * ALPHA),
        (pr.v1.len(), R1 * N),
        (pr.p.len(), R1 * LAM),
        (pr.gamma.len(), R1 * LROWS),
        (pr.y2.len(), EBLK),
    ];
    if let Some(&(got, expected)) = shapes.iter().find(|(got, expected)| got != expected) {
        return Err(CmnwError::Malformed(if got > expected {
            "component too long"
        } else {
            "component too short"
        }));
    }

    let mut fs = Fs::new(inst);
    let c1 = fs.c1(&pr.v0);
    let p_mat = fs.p(&pr.y1, &pr.v1);
    let b_mat = fs.b(&pr.p);
    let c2 = fs.c2(&pr.gamma);
    let n_rows = sigma_rows(&b_mat, &p_mat);
    let n_refs: Vec<&[Elt]> = n_rows.iter().map(|r| r.as_slice()).collect();

    let mut bad: Vec<&'static str> = Vec::new();
    let mut check = |holds: bool, name: &'static str| {
        if !holds {
            bad.push(name);
        }
    };

    // 1, 2, 3: the fold reaches the claim.
    check(dot(&inst.x0, &pr.v0) == inst.u, C1);
    check(dot(&inst.x1, &pr.v1) == dot(&c1, &pr.v0), C2);
    check(
        dot(&inst.x2, &join::<Q, D, 2, ALPHA>(&pr.y2)) == dot(&c2, &pr.v1),
        C3,
    );

    // 4: the projection triangle, App. A's sentence under Eq. (21) — the
    //    constant term of the ring quantity is the field inner product.
    let triangle = (0..LROWS).all(|i| {
        (0..R1).all(|j| {
            const_term(&pr.gamma[j * LROWS + i])
                == field_dot(b_mat.row(i), &pr.p[j * LAM..(j + 1) * LAM])
        })
    });
    check(triangle, C4);

    // 5 and 6: the two Ajtai layers open against `t` and against each other.
    let a1y1 = inst.a1.matvec(&pr.y1).map_err(|_| CmnwError::Malformed("A₁·y₁"))?;
    let c1t = BlockMat::new(R0, N, inst.t.clone())
        .expect("instance-sized")
        .contract_rows(&c1)
        .expect("challenge of the right width");
    check(a1y1[0] == c1t[0], C5);

    let a2y2 = inst.a2.matvec(&pr.y2).map_err(|_| CmnwError::Malformed("A₂·y₂"))?;
    let c2g1 = BlockMat::new(R1, N, join::<Q, D, 2, ALPHA>(&pr.y1))
        .expect("instance-sized")
        .contract_rows(&c2)
        .expect("challenge of the right width");
    check(a2y2[0] == c2g1[0], C6);

    // 7: γ is pinned to y₂ through the σ-matrix N (Eq. 22).
    let n_mat = BlockMat::new(LROWS, EBLK, sigma_matrix(&n_refs)).expect("instance-sized");
    let lhs7 = n_mat.contract_cols(&pr.y2).expect("instance-sized");
    let rhs7 = BlockMat::new(R1, LROWS, pr.gamma.clone())
        .expect("instance-sized")
        .contract_rows(&c2)
        .expect("challenge of the right width");
    check(lhs7 == rhs7, C7);

    // Lemma 5's three gates.
    check(max_magnitude(&to_coeffs(&pr.y1)) <= BETA1, G1);
    check(max_magnitude(&pr.p) <= BETA_P, G2);
    check(max_magnitude(&to_coeffs(&pr.y2)) <= BETA2, G3);
    Ok(bad)
}

/// The verifier: accept only when every equation and gate holds.
fn verify(inst: &Instance, pr: &Proof) -> Result<(), CmnwError> {
    match failing(inst, pr)? {
        empty if empty.is_empty() => Ok(()),
        bad => Err(CmnwError::Rejected(bad[0])),
    }
}

/// Proof size in bytes, for the survey's comparison column.
fn proof_bytes(pr: &Proof) -> usize {
    (pr.v0.len() + pr.y1.len() + pr.v1.len() + pr.gamma.len() + pr.y2.len()) * D * 4
        + pr.p.len() * 4
}

/// Assert a tamper is rejected and that every check in `expected` really is in
/// the failing set, then return that set.
///
/// The set is what is asserted, not a single "first failure": under
/// Fiat–Shamir every message is absorbed before the next challenge, so binding
/// a public value or an early message re-derives `c₁`, `P`, `B`, `c₂` and
/// cascades into most equations at once. A bare `is_err()` would hide that, and
/// so would pinning one name per tamper; `main` additionally asserts that every
/// check appears in *some* tamper's set, which is what proves none of them is
/// dead code.
fn expect_reject(label: &str, inst: &Instance, pr: &Proof, expected: &[&str]) -> Vec<&'static str> {
    let bad = failing(inst, pr).unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(!bad.is_empty(), "{label}: the tamper was accepted");
    for name in expected {
        assert!(bad.contains(name), "{label}: {name} should have fired, got {bad:?}");
    }
    match verify(inst, pr) {
        Err(CmnwError::Rejected(name)) => assert_eq!(name, bad[0], "{label}: attribution"),
        other => panic!("{label}: expected a rejection, got {other:?}"),
    }
    println!("  {label}: rejected by {bad:?}");
    bad
}

fn main() {
    let seed = [0x2cu8; 32];
    let (inst, w) = setup(&seed);

    // Completeness (Lemma 5): the honest proof passes every equation, and the
    // paper's bounds are the ones it passes under.
    let proof = prove(&inst, &w);
    verify(&inst, &proof).expect("honest proof rejected");
    println!(
        "CMNW 2024/281 App. A — q = 2³²−99 (≡5 mod 8, no NTT), d = {D}, α = {ALPHA}, r = ({R0},{R1},{R2}), n = {N}, λ = {LAM}, l = {LROWS}"
    );
    println!(
        "  honest proof verifies: {} bytes; bounds β₁ = {BETA1}, β_p = {BETA_P}, β₂ = {BETA2}",
        proof_bytes(&proof)
    );

    let mut tripped: Vec<&'static str> = Vec::new();

    // A false claim: `u` appears only in equation (1), but it is absorbed
    // before `c₁`, so the cascade reaches (2) and (5) too.
    let false_u = inst.u.clone() + one();
    let wrong_claim = Instance {
        u: false_u,
        ..inst.clone()
    };
    tripped.extend(expect_reject(
        "false claim",
        &wrong_claim,
        &proof,
        &[C1, C2, C5],
    ));

    // A false commitment: `t` appears only in equation (5).
    let mut t = inst.t.clone();
    t[0] = t[0].clone() + one();
    let wrong_t = Instance { t, ..inst.clone() };
    tripped.extend(expect_reject(
        "false commitment",
        &wrong_t,
        &proof,
        &[C5],
    ));

    let bump_v0 = {
        let mut p = proof.clone();
        p.v0[0] = p.v0[0].clone() + one();
        p
    };
    tripped.extend(expect_reject(
        "tampered v₀",
        &inst,
        &bump_v0,
        &[C1, C2, C5],
    ));

    let bump_v1 = {
        let mut p = proof.clone();
        p.v1[0] = p.v1[0].clone() + one();
        p
    };
    tripped.extend(expect_reject(
        "tampered v₁",
        &inst,
        &bump_v1,
        &[C2, C3, C4, C6, C7],
    ));

    let bump_y1 = {
        let mut p = proof.clone();
        p.y1[0] = p.y1[0].clone() + one();
        p
    };
    tripped.extend(expect_reject(
        "tampered y₁",
        &inst,
        &bump_y1,
        &[C3, C4, C5, C6, C7],
    ));

    let bump_y2 = {
        let mut p = proof.clone();
        p.y2[0] = p.y2[0].clone() + one();
        p
    };
    tripped.extend(expect_reject(
        "tampered y₂",
        &inst,
        &bump_y2,
        &[C3, C6, C7],
    ));

    let bump_p = {
        let mut p = proof.clone();
        p.p[0] = p.p[0] + Q::ONE;
        p
    };
    tripped.extend(expect_reject("tampered p⃗", &inst, &bump_p, &[C4, C7]));

    let bump_gamma = {
        let mut p = proof.clone();
        p.gamma[0] = p.gamma[0].clone() + one();
        p
    };
    tripped.extend(expect_reject(
        "tampered γ",
        &inst,
        &bump_gamma,
        &[C3, C4, C6, C7],
    ));

    // Equation (7) is not redundant: a γ entry with the *correct* constant
    // term — so the projection triangle still holds — is caught only through
    // the σ-matrix product.
    let bump_gamma_high = {
        let mut p = proof.clone();
        p.gamma[0] = p.gamma[0].clone() + monomial(1);
        p
    };
    tripped.extend(expect_reject(
        "γ with a wrong non-constant coefficient",
        &inst,
        &bump_gamma_high,
        &[C3, C6, C7],
    ));

    // Equation (6) is what binds the two gadget layers. A prover that cheats
    // *there* — committing to a different `s₁` while keeping `s₂`, and using
    // the matching `t` — passes every fold equation, the projection triangle
    // and all three gates, and is caught by (6) alone.
    let mut forged_s1 = w.s1.clone();
    forged_s1[0] = forged_s1[0].clone() + one();
    let forged_t =
        apply_blockwise(&inst.a1, &forged_s1.chunks(R1 * N * ALPHA).collect::<Vec<_>>())
            .expect("aligned");
    let forged_inst = Instance {
        t: forged_t,
        ..inst.clone()
    };
    let forged = prove(
        &forged_inst,
        &Witness {
            s1: forged_s1,
            s2: w.s2.clone(),
        },
    );
    tripped.extend(expect_reject(
        "layers that do not agree",
        &forged_inst,
        &forged,
        &[C6],
    ));

    // Lemma 5's three gates, each tripped by an oversized response. The value
    // is *set*, not incremented: adding past the bound can wrap mod q back
    // inside it, since a negative coefficient is stored as `q − x`.
    let oversized_y1 = {
        let mut p = proof.clone();
        p.y1[0] = Elt::from_coefficients(vec![Q::from(BETA1 + 7)]);
        p
    };
    tripped.extend(expect_reject("oversized y₁", &inst, &oversized_y1, &[G1]));
    let oversized_p = {
        let mut p = proof.clone();
        p.p[0] = Q::from(BETA_P + 7);
        p
    };
    tripped.extend(expect_reject("oversized p⃗", &inst, &oversized_p, &[G2]));
    let oversized_y2 = {
        let mut p = proof.clone();
        p.y2[0] = Elt::from_coefficients(vec![Q::from(BETA2 + 7)]);
        p
    };
    tripped.extend(expect_reject("oversized y₂", &inst, &oversized_y2, &[G3]));

    // Every equation and gate must be the thing some tamper is caught by.
    for name in [C1, C2, C3, C4, C5, C6, C7, G1, G2, G3] {
        assert!(
            tripped.contains(&name),
            "no tamper is caught by {name} — it is not being tested"
        );
    }
    println!("  every tamper is rejected by the equations it actually violates");
}
