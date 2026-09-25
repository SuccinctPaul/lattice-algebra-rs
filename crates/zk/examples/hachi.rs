//! Hachi's ring-switching step — Nguyen–O'Rourke–Zhang, eprint 2026/156 — as a
//! scheme assembly.
//!
//! This file holds no cryptographic logic: the coefficient-level Ajtai
//! commitment is [`zk::pcs::projection::FieldMat`], the residual is
//! [`zk::pcs::switching`], the extension field is
//! [`algebra::ring::extension::ExtField`], the norm gate is
//! [`zk::shortness::exact_l2::max_magnitude`], and the deterministic challenges
//! come from [`algebra::crypto::transcript::Transcript`].
//!
//! # Which step of Hachi this is
//!
//! §1.3, "Ring switching and sumcheck over extension fields" (p. 7). Hachi's
//! divergence from Greyhound/LaBRADOR is in one place: instead of running
//! LaBRADOR on the relation
//!
//! ```text
//! M z = w  over R_q,  z short                            (paper Eq. 6)
//! ```
//!
//! it *lifts* the relation to `Z_q[X]` without reducing, so the negacyclic fold
//! error becomes an explicit polynomial `ρ`:
//!
//! ```text
//! Σⱼ mⱼ(X)·ẑⱼ(X) = ω̂(X) + (X^d + 1)·ρ̂(X),   deg ρ ≤ d − 2
//! ```
//!
//! commits to the `Z_q`-coefficient vectors `z_ν`, `r_ν` of `z`, `ρ`, and then
//! substitutes `X = ζ ∈ F_{q^k}` — turning the ring relation into a **field
//! inner-product claim**, i.e. something a sumcheck proves with `Õ(k)` base
//! operations per round instead of a full ring multiplication. That is where
//! Hachi's `Õ(√(2^ℓ·λ))` verifier comes from.
//!
//! Assembled below: the lift, the commitment to `(z_ν, r_ν)`, the substitution
//! at a transcript-derived `ζ`, and the three obligations a verifier must then
//! believe. Not here, and recorded in `crates/zk/docs/open-milestones.md` under
//! "Hachi": the sumcheck that *proves* the substituted claim (the claim is
//! checked here, not proved); Lemma 1 / Theorem 1's trace-map identification of
//! `F_{q^k}` with the fixed subring `R_q^H`; and the paper's own `‖ρ‖`
//! bookkeeping, which needs its modulus-separation argument — so the norm gate
//! below bounds the **witness** `z`, which is what Eq. 6 requires.
//!
//! # Instance
//!
//! `q = 2³² − 99` is prime and `≡ 5 (mod 8)`, the congruence Lemma 1 needs, and
//! `F_{q^4} = F_q[Z]/(Z^4 − 2)` — the shape of Hachi's own `ℓ = 30` row
//! (`q = 2³² − 99, d = 2¹⁰, k = 4`). Dimensions are toy.
//!
//! Run with: `cargo run -p lattice-zk --example hachi`

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::extension::ExtField;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::{PolynomialQuotientRing, Ring};
use zk::pcs::projection::{to_coeffs, FieldMat};
use zk::pcs::switching::{evaluate_at_base, relation_residual};
use zk::shortness::exact_l2::max_magnitude;

/// `2³² − 99`: prime, `≡ 5 (mod 8)`, and no NTT of degree ≥ 4 exists.
type Q = Zq<4294967197>;
/// Ring degree `d`.
const D: usize = 8;
/// Extension degree `k`.
const K: usize = 4;
/// Extension relation `Z^K = A`.
const A: u64 = 2;
/// Number of products `mⱼ·zⱼ` in the relation — one matrix row of `T` entries.
const T: usize = 6;
/// Rows of the Ajtai commitment matrix.
const CROWS: usize = 4;
/// Committed coefficient count: the `d` coefficients of each `zⱼ`, then the
/// `d − 1` of `ρ`.
const VLEN: usize = T * D + (D - 1);
/// The witness is binary, which is what the gadget decomposition buys.
const Z_BOUND: u64 = 1;
/// Seed for the public commitment matrix.
const KEY_SEED: [u8; 32] = [0x48u8; 32];

type Elt = PolyRing<Q, D>;
type Ext = ExtField<Q, K, A>;

/// Which verifier obligation failed.
#[derive(Debug, PartialEq, Eq)]
enum HachiError {
    /// `A·v = c`: the claimed coefficients do not open the commitment.
    Commitment,
    /// `Σⱼ m̂ⱼ(ζ)·ẑⱼ(ζ) = ω̂(ζ) + (ζ^d + 1)·ρ̂(ζ)` did not hold at the challenge.
    Substitution,
    /// The lifted witness is not short.
    NotShort {
        /// Measured `ℓ` norm of the `z` part.
        got: u64,
        /// Admitted bound.
        bound: u64,
    },
    /// `w` is not the relation's value, so no residual exists.
    NotARelation,
}

/// The public relation: one matrix row and the claimed value.
struct Relation {
    ms: Vec<Elt>,
    w: Elt,
}

/// The prover's lifted witness.
#[derive(Clone)]
struct Lifted {
    zs: Vec<Elt>,
    rho: Vec<Q>,
}

/// The ring element `Σⱼ coeffsⱼ X^j` from a domain-separated stream.
fn ring_from(label: &[u8], salt: &[u8; 32], i: usize) -> Elt {
    let mut tr = Transcript::<Shake256Xof>::new(label);
    tr.absorb(b"index", &(i as u32).to_le_bytes());
    tr.absorb(b"salt", salt);
    Elt::from_coefficients(
        tr.challenge_bytes(D * 4)
            .chunks_exact(4)
            .map(|c| Q::from(u32::from_le_bytes(c.try_into().expect("4 bytes")) as u64))
            .collect(),
    )
}

/// A `{0,1}`-coefficient ring element: the short witness.
fn short_from(label: &[u8], salt: &[u8; 32], i: usize) -> Elt {
    let mut tr = Transcript::<Shake256Xof>::new(label);
    tr.absorb(b"index", &(i as u32).to_le_bytes());
    tr.absorb(b"salt", salt);
    Elt::from_coefficients(
        tr.challenge_bytes(D)
            .iter()
            .map(|b| Q::from((b & 1) as u64))
            .collect(),
    )
}

/// `Σⱼ mⱼ·zⱼ` in the ring — the value the relation claims.
fn fold(ms: &[Elt], zs: &[Elt]) -> Elt {
    let mut acc = Elt::from_coefficients(vec![Q::ZERO; D]);
    for (m, z) in ms.iter().zip(zs.iter()) {
        acc = acc + m.clone() * z.clone();
    }
    acc
}

/// A relation and a binary witness satisfying it.
fn sample(salt: &[u8; 32]) -> (Relation, Lifted) {
    let ms: Vec<Elt> = (0..T).map(|j| ring_from(b"hachi-m", salt, j)).collect();
    let zs: Vec<Elt> = (0..T)
        .map(|j| short_from(b"hachi-z", salt, j))
        .collect();
    let w = fold(&ms, &zs);
    (Relation { ms, w }, Lifted { zs, rho: Vec::new() })
}

/// The prover's lift: `ρ` of `Σ mⱼ·zⱼ = w + (X^d+1)·ρ`.
///
/// [`relation_residual`] re-derives `Σ mⱼ·zⱼ` and refuses an unrelated `w`, so
/// a prover cannot hand-check a `ρ` for a relation it does not satisfy.
fn lift(rel: &Relation, lifted: &mut Lifted) -> Result<(), HachiError> {
    lifted.rho = relation_residual(&rel.ms, &lifted.zs, &rel.w).map_err(|_| HachiError::NotARelation)?;
    Ok(())
}

/// The committed vector: the coefficients of each `zⱼ`, then those of `ρ`.
fn coefficients(lifted: &Lifted) -> Vec<Q> {
    let mut v = to_coeffs(&lifted.zs);
    v.extend_from_slice(&lifted.rho);
    v
}

fn bytes_of(values: &[Q]) -> Vec<u8> {
    values
        .iter()
        .flat_map(|v| (v.to_u128() as u32).to_le_bytes())
        .collect()
}

/// The challenge point `ζ = Σⱼ c·Z^j ∈ F_{q^k}`, bound to everything public.
fn challenge(rel: &Relation, com: &[Q]) -> Ext {
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/hachi");
    for m in &rel.ms {
        tr.absorb(b"m", &bytes_of(&to_coeffs(&[m.clone()])));
    }
    tr.absorb(b"w", &bytes_of(&to_coeffs(&[rel.w.clone()])));
    tr.absorb(b"c", &bytes_of(com));
    tr.absorb(b"key", &KEY_SEED);
    let mut zeta = Ext::zero();
    let mut basis = Ext::one();
    for c in tr.challenge_bytes(K * 4).chunks_exact(4) {
        let v = Q::from(u32::from_le_bytes(c.try_into().expect("4 bytes")) as u64);
        zeta = zeta + basis.clone() * Ext::from_base(v);
        basis = basis * Ext::z_generator();
    }
    zeta
}

/// The verifier: the commitment opens, the witness is short, and the lifted
/// identity survives substitution at `ζ`.
fn verify(rel: &Relation, key: &FieldMat<Q>, com: &[Q], lifted: &Lifted) -> Result<(), HachiError> {
    let v = coefficients(lifted);
    if key.apply(&v).map_err(|_| HachiError::Commitment)? != com {
        return Err(HachiError::Commitment);
    }
    let got = max_magnitude(&to_coeffs(&lifted.zs));
    if got > Z_BOUND {
        return Err(HachiError::NotShort { got, bound: Z_BOUND });
    }
    let zeta = challenge(rel, com);
    let mut lhs = Ext::zero();
    for j in 0..T {
        lhs = lhs
            + evaluate_at_base(&to_coeffs(&[rel.ms[j].clone()]), &zeta)
            * evaluate_at_base(&to_coeffs(&[lifted.zs[j].clone()]), &zeta);
    }
    let rhs = evaluate_at_base(&to_coeffs(&[rel.w.clone()]), &zeta)
        + (zeta.pow(D as u64) + Ext::one()) * evaluate_at_base(&lifted.rho, &zeta);
    if lhs != rhs {
        return Err(HachiError::Substitution);
    }
    Ok(())
}

/// Re-derive the whole statement around a (possibly cheating) witness, so that
/// only the obligation under test can fail.
fn recommit(rel: &mut Relation, key: &FieldMat<Q>, lifted: &mut Lifted) -> Vec<Q> {
    rel.w = fold(&rel.ms, &lifted.zs);
    lift(rel, lifted).expect("rebuilt from the same witness");
    key.apply(&coefficients(lifted)).expect("instance-sized")
}

fn main() {
    let salt = [0x11u8; 32];
    let (rel, mut lifted) = sample(&salt);
    lift(&rel, &mut lifted).expect("the honest witness satisfies the relation");
    assert_eq!(lifted.rho.len(), D - 1, "deg ρ ≤ d − 2");

    let key = FieldMat::<Q>::uniform(b"hachi-ajtai", &KEY_SEED, CROWS, VLEN);
    let com = key.apply(&coefficients(&lifted)).expect("instance-sized");
    verify(&rel, &key, &com, &lifted).expect("honest lift verifies");

    println!(
        "Hachi 2026/156 §1.3 ring switching — q = 2³²−99 (≡5 mod 8), d = {D}, k = {K}, Z^{K} = {A}, T = {T}"
    );
    println!("  Σⱼ mⱼ(X)·ⱼ(X) = ω̂(X) + (X^{D}+1)·ρ̂(X) over Z_q[X], deg ρ = {}", D - 2);
    println!(
        "  committed {} coefficients ({} zⱼ + ), opens and holds at ζ, ‖z‖∞ ≤ {Z_BOUND}",
        VLEN,
        T
    );

    // The residual is load-bearing: with ρ := 0 the same z, re-committed so the
    // opening still holds, fails the substituted claim — because `ζ^d + 1 ≠ 0`
    // for a challenge drawn in the extension field.
    let mut no_rho = lifted.clone();
    no_rho.rho = vec![Q::ZERO; D - 1];
    let mut rel2 = Relation {
        ms: rel.ms.clone(),
        w: rel.w.clone(),
    };
    let bare_com = key.apply(&coefficients(&no_rho)).expect("sized");
    assert_eq!(
        verify(&rel2, &key, &bare_com, &no_rho),
        Err(HachiError::Substitution),
        "the claim must need the residual, not merely the ring product"
    );
    println!("  ρ := 0 (re-committed, opening intact) breaks the substituted claim");
    rel2.w = rel.w.clone();

    // A value that is not the relation's value has no residual at all.
    let bogus = Relation {
        ms: rel.ms.clone(),
        w: rel.w.clone() + Elt::from_coefficients(vec![Q::ONE]),
    };
    let mut untouched = lifted.clone();
    assert_eq!(
        lift(&bogus, &mut untouched),
        Err(HachiError::NotARelation),
        "a false claim must be refused before any ρ is produced"
    );
    println!("  a false claim is refused outright — no residual is produced for it");

    // A non-binary witness passes the opening and the substitution and is
    // caught by the norm gate alone. The bump must exceed `Z_BOUND`, not just
    // perturb: adding `1` to a `{0,1}` coefficient can still leave it ≤ 1.
    let mut heavy = lifted.clone();
    heavy.zs[0] = heavy.zs[0].clone() + Elt::from_coefficients(vec![Q::from(Z_BOUND + 8)]);
    let mut heavy_rel = Relation {
        ms: rel.ms.clone(),
        w: Elt::from_coefficients(vec![Q::ZERO; D]),
    };
    let heavy_com = recommit(&mut heavy_rel, &key, &mut heavy);
    let got = max_magnitude(&to_coeffs(&heavy.zs));
    assert_eq!(
        verify(&heavy_rel, &key, &heavy_com, &heavy),
        Err(HachiError::NotShort { got, bound: Z_BOUND }),
        "the norm gate must be the only thing that fires"
    );
    println!("  a witness with ‖z‖∞ = {got} passes both equations and trips the norm gate");

    // A stale commitment is caught before anything else.
    let mut shifted = com.clone();
    shifted[0] = shifted[0] + Q::ONE;
    assert_eq!(
        verify(&rel, &key, &shifted, &lifted),
        Err(HachiError::Commitment)
    );
    println!("  every rejection is attributed to the obligation it violates");
}
