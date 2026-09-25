//! Orbweaver: a succinct **linear functional commitment** from a *trusted
//! structured* reference string — Fisch–Liu–Vesely, CRYPTO 2023 (rev.
//! 2024-12), eprint 2024/2026, §4 with the §4.1/§4.2/§4.3/§5.1 extensions.
//!
//! # This scheme needs a trusted setup, and says so
//!
//! `Setup` runs `TrapGen`, which produces a **trapdoor** alongside the public
//! R-SIS vectors. The SRS is the list of short preimages of the powers of one
//! invertible ring element `v`:
//!
//! ```text
//! ⟨a₀, u_{0,i}⟩ ≡ vⁱ mod q   (i ∈ Z(W) \ {0})      ⟨a₁, u_{1,i}⟩ ≡ vⁱ·t mod q   (i ∈ [W])
//! ```
//!
//! Whoever keeps the trapdoor can sample a short preimage of *any* target, so
//! they can open one committed vector to two different values, or open a
//! commitment they never saw. Nothing in the verification equations detects a
//! forged opening — the last block of this run demonstrates that by forging one
//! with the setup trapdoor and watching it verify. The SRS is therefore
//! **universal but trusted**: soundness is only claimed for a `Setup` whose
//! trapdoor was destroyed, exactly as the paper states ("we require a trusted
//! setup to generate a universal structured reference string", abstract; §4's
//! `Setup` box).
//!
//! # Where the logic lives
//!
//! Every cryptographic step is a capability call. [`zk::pcs::powers_srs`] holds
//! `TrapGen`/`SampPre` (the sampling algorithms of §2.3, instantiated with the
//! [MP12] gadget form §5.1 names), the power-window SRS,
//! `Com`/`Open`/`PreVerify`/`Verify` with Table 1's derived gates, the §4.1
//! aggregation and inner-product argument, the §4.2 integer shim and §4.3's
//! `O(log w)` functional keys. What is left here is the instance, the paper's
//! step order, and the trace.
//!
//! # Why a *structured* SRS is the point
//!
//! An Ajtai key ([`zk::pcs::key`]) is random, so it commits to exactly the
//! coordinates it indexes. Here the targets are `vⁱ`, so the commitment to *any*
//! linear functional `f` is `Σᵢ fᵢv⁻ⁱ`, which the verifier computes itself — in
//! `w` ring multiplications, or `log w` for the power and `eq`-tensor tables
//! (§4.3). That is the polylog verifier, and one `Setup` covers every `w ≤ W`
//! (§4.1, "Universal SRS").
//!
//! # Assumptions and instance
//!
//! Security is **k-P-R-ISIS** (plain, for evaluation binding) and **knowledge
//! k-P-R-ISIS** (for extractability), §2.4.1–§2.4.2: the lattice analogue of
//! k-SDH over the admissible monomial family `G₀ = [Xⁱ]_{i∈Z(w)\{0}}` with
//! target `g*(X) = 1`.
//!
//! `q = 8380417` is prime and `≡ 1 (mod 2d)` for `d = 8`, so `X^8 + 1` splits
//! completely: `R_q ≅ Z_q^8`, a uniform `v` is a unit, and the set `T` of
//! Definition 2.15 — "all the elements `t` such that exactly half of the
//! elements in the NTT representation of `t` are zero" — exists. That is why this
//! instance is *not* the `q ≡ 5 (mod 8)` ring the CMNW/Hachi lanes use: on such a
//! ring `T` is unavailable (the paper: "this is only defined when `⟨q⟩` is not a
//! prime ideal in `R`") and only the binding half of the scheme is expressible —
//! which the capability module still supports, and its
//! `non_ntt_ring_binding_half_round_trips` test exercises.
//!
//! Toy dimensions (`d = 8`, `W = 4`, `ℓ = 2·⌈log₂ q⌉ = 46`) keep the run
//! interactive; the gates come from Table 1 rather than from tuning, so this
//! demonstrates the protocol, not a security level.
//!
//! Run with: `cargo run -p lattice-zk --example orbweaver`

use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::zq::Zq;
use algebra::ring::{PolynomialQuotientRing, Ring};
use zk::foundation::sampling::from_centered;
use zk::pcs::mixed::dot as ring_dot;
use zk::pcs::powers_srs::{
    aggregate, check_alphabet, commit, commit_dual, eq_tensor, failing, failing_aggregated,
    failing_combined, failing_inner_product, functional_key, integer_claim, laurent_product,
    max_norm, multilinear_functional_key, open, pack_integer_functional, pack_integer_witness,
    pairing, power_functional_key, pre_verify, sample_unit, setup, vanishing_element, Claim,
    Commitment, Condition, CrsParts, NormBounds, Opening, PowersSrs, SetupTrapdoor, SrsError,
    Trapdoor,
};

/// Splitting-friendly prime: `q ≡ 1 (mod 2d)` for every `d ≤ 2¹²`.
type Q = Zq<8_380_417>;
/// Ring degree `d` (the paper's `n`).
const D: usize = 8;
type Elt = PolyRing<Q, D>;
/// The `q ≡ 5 (mod 8)` instance the CMNW/Hachi lanes use: prime, 2-adicity 2, so
/// `X^64 + 1` has two degree-32 factors and no NTT exists.
type Q5 = Zq<4_294_967_197>;
const D5: usize = 64;
type Elt5 = PolyRing<Q5, D5>;
/// Digits for `q ≈ 2³²`: `2³² > 2³² − 99`, so the gadget split stays exact.
const DIGITS5: usize = 32;
/// Gadget base and digit count: `2²³ = 8388608 > q`, so the split is exact.
const BASE: u64 = 2;
const DIGITS: usize = 23;
/// `ℓ = 2·DIGITS` ring elements per SRS vector and per proof.
const ELL: usize = 2 * DIGITS;
/// The universal SRS covers every dimension `w ≤ W`.
const W: usize = 4;
/// Trapdoor (and preimage-randomizer) coefficient bound `ρ`.
const RHO: u32 = 1;
/// Declared alphabet bound on the witness: `X = {x ∈ R : ‖x‖ ≤ α}`.
const ALPHA_X: u64 = 2;
/// `α` for the functionals. The power table `(1, z, z², z³)` at `z = 2` has norm
/// `8`, which is §4.3's `‖f‖ ≤ α^{log w + 1}` blow-up at this dimension.
const ALPHA_F: u64 = 8;
/// `γ_R ≤ d` for power-of-two cyclotomics (Theorem 2.2).
const GAMMA_R: u64 = D as u64;

type Srs = PowersSrs<Q, D, BASE, DIGITS>;

/// §4's `Verify` box lines, §4.1's two extension equations, `Setup`'s invariant
/// and `PreVerify`'s abort — named once so the prover, the verifier and the
/// tamper table agree on what each one is.
const S0: &str = "S0: ⟨a₀,u₀ᵢ⟩ = vⁱ ∧ ⟨a₁,u₁ᵢ⟩ = vⁱ·t";
const E1: &str = "E1: ⟨a₁,π₁⟩ = c·t";
const E2: &str = "E2: ⟨a₀,π₀⟩ = vk_f·c − y";
const E3: &str = "E3: ⟨a₀,Σhᵢπ₀ᵢ⟩ = Σhᵢ(vkᵢc − yᵢ)";
const E4: &str = "E4: ⟨a₀,π₀⟩ = c'·c − y";
const E5: &str = "E5: ⟨a,vk_f·π₁ − t·π₀⟩ = y·t";
const N1: &str = "N1: ‖y‖ ≤ δ_M";
const N2: &str = "N2: ‖π₁‖ ≤ δ₁";
const N3: &str = "N3: ‖π₀‖ ≤ δ₀";
const N4: &str = "N4: ‖f‖ ≤ α (PreVerify aborts)";

/// The name of a failed condition. Exhaustive on purpose: a new condition in
/// `src` has to be named here or the build fails.
fn name(condition: Condition) -> &'static str {
    match condition {
        Condition::ValueNorm => N1,
        Condition::KnowledgeNorm => N2,
        Condition::OpeningNorm => N3,
        Condition::KnowledgeEquation => E1,
        Condition::OpeningEquation => E2,
        Condition::SrsPreimages => S0,
        Condition::AggregatedOpeningEquation => E3,
        Condition::InnerProductEquation => E4,
        Condition::CombinedEquation => E5,
    }
}

fn names(conditions: Vec<Condition>) -> Vec<&'static str> {
    conditions.iter().map(|&c| name(c)).collect()
}

/// The constant ring element.
fn konst(v: u64) -> Elt {
    PolyRing::from_coefficients(vec![Q::from(v)])
}

/// The ring element `X^k`.
fn monomial(k: usize) -> Elt {
    let mut coeffs = vec![Q::ZERO; D];
    coeffs[k % D] = if (k / D) % 2 == 0 { Q::ONE } else { -Q::ONE };
    PolyRing::from_coefficients(coeffs)
}

/// `base^k` by repeated ring multiplication (`PolyRing` carries no `pow`).
fn ring_pow<R: Ring, const N: usize>(base: &PolyRing<R, N>, k: u64) -> PolyRing<R, N> {
    let mut acc = PolyRing::from_coefficients({
        let mut c = vec![R::ZERO; N];
        c[0] = R::ONE;
        c
    });
    for _ in 0..k {
        acc *= base.clone();
    }
    acc
}

/// The additive identity of the non-NTT ring.
fn zero5() -> Elt5 {
    PolyRing::from_coefficients(vec![Q5::ZERO; D5])
}

/// A small-coefficient vector over the non-NTT ring.
fn q5_vector(tag: usize, w: usize) -> Vec<Elt5> {
    (0..w)
        .map(|i| {
            PolyRing::from_coefficients(
                (0..D5)
                    .map(|k| from_centered::<Q5>((((i + tag) * 5 + k) % 5) as i64 - 2))
                    .collect(),
            )
        })
        .collect()
}

/// A committed vector with coefficients in `[-bound, bound]`: nothing about it
/// is public except through `c`.
fn vector(tag: u64, w: usize, bound: i64) -> Vec<Elt> {
    (0..w)
        .map(|i| {
            PolyRing::from_coefficients(
                (0..D)
                    .map(|k| {
                        from_centered::<Q>(
                            ((tag as i64 * 7 + i as i64 * 3 + k as i64) % (2 * bound + 1)) - bound,
                        )
                    })
                    .collect(),
            )
        })
        .collect()
}

/// Table 1 / Theorem 4.1's gates for one `(w, α_f)` claim at `α_x = ALPHA_X`.
fn gates(srs: &Srs, w: usize, alpha_f: u64) -> NormBounds {
    NormBounds::derive(
        w as u64,
        ALPHA_X,
        alpha_f,
        srs.opening_norm_bound(),
        srs.knowledge_norm_bound(),
        GAMMA_R,
    )
    .expect("derived gates must fit u128")
}

/// Asserts that a rejection names exactly `want`, and prints it.
fn expect_reject(label: &str, got: Vec<&'static str>, want: &[&'static str]) {
    assert!(!got.is_empty(), "{label}: the tamper was ACCEPTED");
    let mut sorted = got.clone();
    sorted.sort_unstable();
    sorted.dedup();
    let mut want_sorted = want.to_vec();
    want_sorted.sort_unstable();
    assert_eq!(
        sorted, want_sorted,
        "{label}: rejected by {got:?}, expected exactly {want:?}"
    );
    println!("  {label}: rejected by {got:?}");
}

/// Asserts full acceptance and prints the trace line.
fn expect_accept(label: &str, got: Vec<&'static str>) {
    assert!(got.is_empty(), "{label}: honest proof rejected by {got:?}");
    println!("  {label}: verifies");
}

/// §4's linear functional commitment driven through
/// [`zk::pcs::api::WeightPcs`].
///
/// This is the seam's second implementor, and its purpose is to be *structurally
/// unlike* Greyhound: a trusted power-window SRS rather than a transparent
/// two-layer Ajtai key, a `PreVerify` step keyed by the functional itself, and a
/// response *pair* `(π₁, π₀)` rather than gadget digits. It deliberately does
/// **not** implement `WeightPcsExt`: `Open(ck, f, x)` blinds nothing, so there is
/// no mask seed to pass, and `value_of(com, f)` would have to recover `x` from
/// `c = ⟨a₀, x⟩` under a short key — impossible without `pcs::mle`'s tall key.
/// Those two are the capabilities the base trait used to conflate.
struct Lfc<'a> {
    srs: &'a Srs,
    bounds: &'a NormBounds,
}

/// Why the dispatch refused: a malformed object, or the named checks that failed.
#[derive(Debug)]
enum Dispatch {
    Malformed(SrsError),
    Failed(Vec<&'static str>),
}

impl zk::pcs::api::WeightPcs for Lfc<'_> {
    type Coeff = Elt;
    type Weight = Elt;
    type Value = Elt;
    type Commitment = Commitment<Q, D>;
    type Proof = Opening<Q, D>;
    type Error = Dispatch;

    fn commit(&self, x: &[Elt]) -> Result<Self::Commitment, Dispatch> {
        commit(self.srs, x).map_err(Dispatch::Malformed)
    }

    fn open(&self, x: &[Elt], f: &[Elt]) -> Result<(Elt, Opening<Q, D>), Dispatch> {
        let proof = open(self.srs, f, x).map_err(Dispatch::Malformed)?;
        Ok((ring_dot(f, x), proof))
    }

    fn verify(
        &self,
        com: &Self::Commitment,
        f: &[Elt],
        y: &Elt,
        proof: &Opening<Q, D>,
    ) -> Result<(), Dispatch> {
        let vk_f = pre_verify(self.srs, f, ALPHA_F).map_err(Dispatch::Malformed)?;
        let checks = failing(self.srs, self.bounds, &vk_f, com, y, proof);
        if checks.is_empty() {
            Ok(())
        } else {
            Err(Dispatch::Failed(
                checks.into_iter().map(name).collect::<Vec<_>>(),
            ))
        }
    }
}

fn main() {
    let seed = [0x0bu8; 32];

    // ---- §4 Setup(1^λ, 1^W): the trusted structured universal SRS ----------
    let (srs, waste): (Srs, SetupTrapdoor<Q, D, BASE, DIGITS>) =
        setup::<Q, D, BASE, DIGITS>(&seed, W, RHO, true).expect("the ring splits");
    println!(
        "Orbweaver (2024/2026 §4) — TRUSTED SETUP · q = {}, d = {D}, ℓ = {ELL}, W = {W}, ρ = {RHO}, β₀ = {}",
        Q::MODULUS,
        srs.opening_norm_bound()
    );
    println!(
        "  CRS: {} ring elements = {} KiB ({} window preimages + 2 keys, each ℓ = {ELL}; §5.2.1's 3w·ℓ·n·log β)",
        srs.crs_ring_elements(),
        srs.crs_ring_elements() * D * 4 / 1024,
        srs.exponents().len() + W,
    );
    expect_accept("S0 (SRS well-formed)", names(srs.failing_setup_invariant()));
    println!("  window P = Z({W}) \\ {{0}} = {:?}", srs.exponents());

    // ---- §4 Com / PreVerify / Open / Verify --------------------------------
    let x = vector(3, W, 2);
    let f = vector(4, W, 2);
    check_alphabet(&x, ALPHA_X, false).expect("x ∈ X^w");
    let com = commit(&srs, &x).expect("Com");
    let vk_f = pre_verify(&srs, &f, ALPHA_F).expect("PreVerify");
    let y = ring_dot(&f, &x);
    let lp = laurent_product(&x, &f).expect("Open's coefficient table");
    assert_eq!(lp.constant_term(), y, "a₀ is the claim");
    let opening = open(&srs, &f, &x).expect("Open");
    let bounds = gates(&srs, W, ALPHA_F);
    println!(
        "  gates (Table 1): δ_M = {}, δ₁ = {}, δ₀ = {}, β*₀ = {}; all < q/2 = {}",
        bounds.delta_m,
        bounds.delta_1,
        bounds.delta_0,
        bounds.beta_star_0,
        bounds.gates_below_half_modulus(Q::MODULUS)
    );
    assert!(bounds.gates_below_half_modulus(Q::MODULUS));
    expect_accept(
        "§4 Verify(vk_f, c, π₁, y, π₀)",
        names(failing(&srs, &bounds, &vk_f, &com, &y, &opening)),
    );
    println!(
        "  sizes: |c| = {} B, |π₁| = {} B, |π₀| = {} B, ‖π₀‖ = {} ≤ δ₀",
        D * 4,
        com.pi1.len() * D * 4,
        opening.pi0.len() * D * 4,
        max_norm(&opening.pi0)
    );

    // ---- tampers: every component is caught by its own condition -----------
    let one = konst(1);
    expect_reject(
        "false value y+1",
        names(failing(
            &srs,
            &bounds,
            &vk_f,
            &com,
            &(y.clone() + one.clone()),
            &opening,
        )),
        &[E2],
    );
    let mut tampered_pi0 = opening.clone();
    tampered_pi0.pi0[0] = tampered_pi0.pi0[0].clone() + one.clone();
    expect_reject(
        "tampered π₀",
        names(failing(&srs, &bounds, &vk_f, &com, &y, &tampered_pi0)),
        &[E2],
    );
    let mut tampered_pi1 = com.clone();
    tampered_pi1.pi1[0] = tampered_pi1.pi1[0].clone() + one.clone();
    expect_reject(
        "tampered π₁",
        names(failing(&srs, &bounds, &vk_f, &tampered_pi1, &y, &opening)),
        &[E1],
    );
    // `c` is read by both equations, so it is attributed to both.
    let tampered_c = Commitment {
        c: com.c.clone() + one.clone(),
        ..com.clone()
    };
    expect_reject(
        "tampered c",
        names(failing(&srs, &bounds, &vk_f, &tampered_c, &y, &opening)),
        &[E1, E2],
    );
    expect_reject(
        "tampered vk_f",
        names(failing(
            &srs,
            &bounds,
            &(vk_f.clone() + one.clone()),
            &com,
            &y,
            &opening,
        )),
        &[E2],
    );
    let oversized = y.clone() + konst(1 << 21);
    expect_reject(
        "value outside δ_M",
        names(failing(&srs, &bounds, &vk_f, &com, &oversized, &opening)),
        &[N1, E2],
    );
    // The gates are live: tighten one below the honest proof and only it fires.
    let tight = NormBounds {
        delta_0: u128::from(max_norm(&opening.pi0)) - 1,
        ..bounds
    };
    expect_reject(
        "δ₀ one below the honest π₀",
        names(failing(&srs, &tight, &vk_f, &com, &y, &opening)),
        &[N3],
    );
    let tight1 = NormBounds {
        delta_1: u128::from(max_norm(&com.pi1)) - 1,
        ..bounds
    };
    expect_reject(
        "δ₁ one below the honest π₁",
        names(failing(&srs, &tight1, &vk_f, &com, &y, &opening)),
        &[N2],
    );
    // PreVerify's own abort line.
    let mut long_f = f.clone();
    // Push one coefficient to 4α so the gate fires whatever the honest draw was.
    long_f[0] = long_f[0].clone() + monomial(2) * konst(4 * ALPHA_F);
    assert!(max_norm(&long_f) > ALPHA_F, "the tamper must leave X");
    println!(
        "  {N4}: {}",
        pre_verify(&srs, &long_f, ALPHA_F).unwrap_err()
    );

    // A corrupted CRS: the SRS is public data, so this is the cheapest
    // setup-adversary move, and only S0 sees it.
    let mut parts: CrsParts<Q, D> = srs.to_parts();
    parts.openings.swap(0, 1);
    let corrupted: Srs = PowersSrs::from_parts(parts).expect("same shape");
    expect_reject(
        "SRS window entries swapped in transit",
        names(corrupted.failing_setup_invariant()),
        &[S0],
    );

    // ---- §4.1 universal SRS: the same ck, a smaller dimension --------------
    let w2 = 2;
    let x2 = vector(9, w2, 2);
    let f2 = vector(10, w2, 2);
    let com2 = commit(&srs, &x2).expect("Com");
    let vk2 = pre_verify(&srs, &f2, ALPHA_F).expect("PreVerify");
    let y2 = ring_dot(&f2, &x2);
    let open2 = open(&srs, &f2, &x2).expect("Open");
    expect_accept(
        "§4.1 universal SRS at w = 2, no re-setup",
        names(failing(
            &srs,
            &gates(&srs, w2, ALPHA_F),
            &vk2,
            &com2,
            &y2,
            &open2,
        )),
    );

    // ---- the binding half on a ring with no NTT (Def 2.15's restriction) ---
    // `q = 2³² − 99 ≡ 5 (mod 8)` has 2-adicity 2, so no NTT of degree ≥ 4 exists
    // and `T` — "only defined when ⟨q⟩ is not a prime ideal in R" — is
    // unavailable: the knowledge half carries no extractability claim here. The
    // k-P-R-ISIS half (evaluation *binding*) is ring-generic, and this is it on
    // that ring: trapdoor, power window, `Open`, `PreVerify`, opening equation.
    assert_eq!(
        (Q5::MODULUS - 1).trailing_zeros(),
        2,
        "2-adicity 2 ⇒ no NTT"
    );
    println!(
        "  T over q = {}: {}",
        Q5::MODULUS,
        vanishing_element::<Q5, D5>(&seed).unwrap_err()
    );
    let td5 = Trapdoor::<Q5, D5, BASE, DIGITS5>::trap_gen(&seed, b"orbweaver-a0", RHO);
    let (v5, v_inv5) = sample_unit::<Q5, D5>(&seed, b"v", 8).expect("a unit exists");
    let beta5 = td5.preimage_norm_bound(D5 as u64);
    let w5: i32 = 3;
    let mut window5 = Vec::new();
    for exponent in -(w5 - 1)..=w5 - 1 {
        if exponent == 0 {
            continue;
        }
        let base = if exponent > 0 {
            v5.clone()
        } else {
            v_inv5.clone()
        };
        let target = ring_pow(&base, u64::from(exponent.unsigned_abs()));
        let u = td5.samp_pre(&target, &seed, (exponent + 8) as u64);
        assert!(max_norm(&u) <= beta5, "the preimage must stay short");
        assert_eq!(
            pairing(td5.public_vector(), &u).expect("shaped"),
            target,
            "S0 must hold on a ring with no NTT"
        );
        window5.push((exponent, u));
    }
    let x5 = q5_vector(5, w5 as usize);
    let f5 = q5_vector(3, w5 as usize);
    let lp5 = laurent_product(&x5, &f5).expect("Open's table");
    let y5 = lp5.constant_term();
    assert_eq!(y5, ring_dot(&f5, &x5), "a₀ = ⟨f, x⟩");
    let mut c5 = zero5();
    let mut vk5 = zero5();
    let mut pi05 = vec![zero5(); td5.ell()];
    for (i, xi) in x5.iter().enumerate() {
        c5 += xi.clone() * ring_pow(&v5, (i + 1) as u64);
        vk5 += f5[i].clone() * ring_pow(&v_inv5, (i + 1) as u64);
    }
    for (exponent, u) in &window5 {
        let a = lp5.coefficient(*exponent).expect("in the window");
        for (acc, uk) in pi05.iter_mut().zip(u.iter()) {
            *acc += a.clone() * uk.clone();
        }
    }
    assert_eq!(
        pairing(td5.public_vector(), &pi05).expect("shaped"),
        vk5 * c5 - y5,
        "E2 must hold on a ring with no NTT"
    );
    let b5 = NormBounds::derive(
        w5 as u64,
        max_norm(&x5),
        max_norm(&f5),
        beta5,
        beta5,
        D5 as u64,
    )
    .expect("derived gates fit u128");
    assert!(
        b5.gates_below_half_modulus(Q5::MODULUS),
        "Table 1's gates must still constrain at q = 2³²−99"
    );
    assert!(
        max_norm(&pi05) <= u64::try_from(b5.delta_0).expect("fits u64"),
        "‖π₀ ≤ δ₀ (Theorem 4.1) on the non-NTT ring"
    );
    println!(
        "  E2 over q = 2³²−99, d = {D5}: ⟨a₀,π₀⟩ = vk_f·c − y, ‖π₀‖ = {} ≤ δ₀ = {} < q/2",
        max_norm(&pi05),
        b5.delta_0
    );

    // ---- §4.3 univariate PCS: the power table, formed in log w -------------
    let z = konst(2);
    let power_table: Vec<Elt> = (0..W).map(|i| ring_pow(&z, i as u64)).collect();
    let log_key = power_functional_key(&srs, &z, W).expect("log-time power key");
    assert_eq!(
        log_key,
        functional_key(&srs, &power_table).expect("direct key"),
        "v^(-w)·Π(z^(2^j) + v^(2^j)) must equal Σ z^(i-1)·v^(-i)"
    );
    let coeffs = vector(11, W, 2);
    let p_com = commit(&srs, &coeffs).expect("Com");
    let p_y = ring_dot(&power_table, &coeffs);
    let p_open = open(&srs, &power_table, &coeffs).expect("Open");
    expect_accept(
        "§4.3 univariate P(z), key from the point alone",
        names(failing(
            &srs,
            &gates(&srs, W, ALPHA_F),
            &log_key,
            &p_com,
            &p_y,
            &p_open,
        )),
    );
    println!(
        "  degree-{} polynomial evaluated at z = 2: key in {} ring multiplications (log w), not {}",
        W - 1,
        W.trailing_zeros(),
        W
    );

    // ---- §4.3 multilinear PCS: the eq tensor, formed in log w --------------
    let point = [konst(2), konst(3)];
    let weights = eq_tensor::<Q, D>(&point, W).expect("eq tensor fits W");
    let ml_key = multilinear_functional_key(&srs, &point).expect("log-time ml key");
    assert_eq!(
        ml_key,
        functional_key(&srs, &weights).expect("direct eq sum"),
        "v⁻¹·Π((1−z_j) + z_j·v^(-2^j)) must equal Σ eq(z,i−1)·v^(-i)"
    );
    let m_y = ring_dot(&weights, &coeffs);
    let m_open = open(&srs, &weights, &coeffs).expect("Open");
    let alpha_eq = max_norm(&weights);
    expect_accept(
        "§4.3 multilinear g(z₀,z₁), key from the point alone",
        names(failing(
            &srs,
            &gates(&srs, W, alpha_eq),
            &ml_key,
            &p_com,
            &m_y,
            &m_open,
        )),
    );
    println!(
        "  ‖eq(z,·)‖ = {alpha_eq} ≤ α = {ALPHA_F}: PreVerify's gate is what bounds the point set"
    );

    // ---- §4.1 public proof aggregation ------------------------------------
    let ax = 1u64;
    let claims_x = [vector(21, W, 1), vector(22, W, 1), vector(23, W, 1)];
    let claims_f = [vector(31, W, 1), vector(32, W, 1), vector(33, W, 1)];
    let mut coms: Vec<Commitment<Q, D>> = Vec::new();
    let mut vks = Vec::new();
    let mut ys = Vec::new();
    let mut opens = Vec::new();
    for (cx, cf) in claims_x.iter().zip(claims_f.iter()) {
        coms.push(commit(&srs, cx).expect("Com"));
        vks.push(pre_verify(&srs, cf, ax).expect("PreVerify"));
        ys.push(ring_dot(cf, cx));
        opens.push(open(&srs, cf, cx).expect("Open"));
    }
    // Sparse ternary challenges: §2.1's set H with c = 2 non-zero ±1
    // coefficients, whose operator norm is c = 2 (Lemma 2.5).
    let hs = [
        monomial(0) + monomial(3),
        -monomial(1),
        monomial(2) - monomial(5),
    ];
    let claim_refs: Vec<Claim<'_, Q, D>> = (0..3)
        .map(|i| Claim {
            commitment: &coms[i].c,
            functional_key: &vks[i],
            value: &ys[i],
            opening: &opens[i].pi0,
        })
        .collect();
    let agg_bounds = gates(&srs, W, ax);
    let agg_gate = agg_bounds
        .aggregated_opening_bound(claim_refs.len(), 2)
        .expect("aggregate gate fits");
    let (residual, pi0) = aggregate(&srs, &claim_refs, &hs).expect("aggregate");
    expect_accept(
        "§4.1 aggregation: 3 openings → one π₀",
        names(failing_aggregated(&srs, &residual, &pi0, agg_gate).expect("shaped")),
    );
    let mut wrong_residual = residual.clone();
    wrong_residual += hs[2].clone();
    expect_reject(
        "aggregate with one yᵢ altered",
        names(failing_aggregated(&srs, &wrong_residual, &pi0, agg_gate).expect("shaped")),
        &[E3],
    );
    println!(
        "  aggregate π₀ = {} B, gate {} < q/2 = {}",
        pi0.len() * D * 4,
        agg_gate,
        agg_gate < u128::from(Q::MODULUS / 2)
    );

    // ---- §4.1 inner-product argument --------------------------------------
    // The paper's two IPA equations together require preimages of v^{-i}·t,
    // which §4's Setup box never samples, so the setup extends the window.
    let xp = vector(41, W, 2);
    let mut ipa_srs = srs.clone();
    waste
        .extend_for_inner_product(&mut ipa_srs, &seed)
        .expect("§4.1 window");
    expect_accept(
        "S0 after the §4.1 extension",
        names(ipa_srs.failing_setup_invariant()),
    );
    println!(
        "  extended CRS: {} ring elements ({} window preimages + 2 keys)",
        ipa_srs.crs_ring_elements(),
        ipa_srs.exponents().len() + 2 * W
    );
    let com_xp = commit_dual(&ipa_srs, &xp).expect("dual Com, at v^{-i}");
    let ip_y = ring_dot(&xp, &x);
    let ip_open = open(&srs, &xp, &x).expect("Open with the committed functional x'");
    let ip_bounds = gates(&srs, W, ALPHA_X);
    expect_accept(
        "§4.1 inner product ⟨x,x'⟩ between two commitments",
        names(
            failing_inner_product(&srs, &ip_bounds, &com, &com_xp, &ip_y, &ip_open)
                .expect("shaped"),
        ),
    );
    expect_reject(
        "false inner product",
        names(
            failing_inner_product(
                &srs,
                &ip_bounds,
                &com,
                &com_xp,
                &(ip_y.clone() + one.clone()),
                &ip_open,
            )
            .expect("shaped"),
        ),
        &[E4],
    );
    // π₁' feeds only the knowledge equation — E4 reads `c'`, not `π₁'`, which is
    // exactly why the dual commitment needs a knowledge proof of its own.
    let mut bad_dual_pi1 = com_xp.clone();
    bad_dual_pi1.pi1[0] = bad_dual_pi1.pi1[0].clone() + one.clone();
    expect_reject(
        "dual knowledge proof tampered",
        names(
            failing_inner_product(&srs, &ip_bounds, &com, &bad_dual_pi1, &ip_y, &ip_open)
                .expect("shaped"),
        ),
        &[E1],
    );
    assert_eq!(
        commit_dual(&srs, &x),
        Err(SrsError::MissingDualWindow),
        "the plain §4 SRS has no v^(-i)·t window, so it cannot serve the IPA"
    );
    let stretched = ip_bounds
        .inner_product_variant()
        .expect("stretched bounds fit");
    println!(
        "  β*₀ the IPA needs (α* = δ₁): {} vs {} for the plain linear map",
        stretched.beta_star_0, ip_bounds.beta_star_0
    );

    // ---- §4.2 linear functional commitments for integers ------------------
    let n_scalar = W * D;
    let x_hat: Vec<Q> = (0..n_scalar)
        .map(|i| from_centered::<Q>(((i as i64 * 7) % 5) - 2))
        .collect();
    let f_hat: Vec<Q> = (0..n_scalar)
        .map(|i| from_centered::<Q>(((i as i64 * 11 + 3) % 5) - 2))
        .collect();
    let x_ring = pack_integer_witness::<Q, D>(&x_hat).expect("N = w·d");
    let f_ring = pack_integer_functional::<Q, D>(&f_hat).expect("N = w·d");
    let z_com = commit(&srs, &x_ring).expect("Com");
    let z_vk = functional_key(&srs, &f_ring).expect("w ≤ W");
    let z_y = ring_dot(&f_ring, &x_ring);
    let z_open = open(&srs, &f_ring, &x_ring).expect("Open");
    expect_accept(
        "§4.2 integer linear map, read out of ct(y)",
        names(failing(
            &srs,
            &gates(&srs, W, max_norm(&f_ring)),
            &z_vk,
            &z_com,
            &z_y,
            &z_open,
        )),
    );
    let mut expect_scalar = Q::ZERO;
    for (a, b) in x_hat.iter().zip(f_hat.iter()) {
        expect_scalar += *a * *b;
    }
    assert_eq!(
        integer_claim(&z_y),
        expect_scalar,
        "ct(⟨f, x⟩) must be the scalar inner product ⟨f̂, x̂⟩"
    );
    println!(
        "  ⟨f̂,x̂⟩ over Z^{n_scalar} = ct(y) = {}; the other {} coefficients of y are proof, not instance",
        integer_claim(&z_y).centered(),
        D - 1
    );

    // ---- §5.1 the halved verifier for the shared-a instantiation ----------
    assert!(srs.shares_a(), "Setup was run with a₁ = a₀");
    expect_accept(
        "§5.1 combined check (one pairing instead of two)",
        names(failing_combined(&srs, &bounds, &vk_f, &com, &y, &opening).expect("shared a")),
    );
    expect_reject(
        "combined check against a false value",
        names(
            failing_combined(
                &srs,
                &bounds,
                &vk_f,
                &com,
                &(y.clone() + one.clone()),
                &opening,
            )
            .expect("shared a"),
        ),
        &[E2, E5],
    );

    // ---- the trusted-setup caveat, demonstrated ---------------------------
    // The setup trapdoor samples a preimage of any target, so a false claim
    // opens and verifies. Destroying `waste` is what makes the CRS usable.
    let forged_target = vk_f.clone() * com.c.clone() - (y.clone() + one.clone());
    let forged = waste.open_trapdoor().samp_pre(&forged_target, &seed, 0);
    let forged_opening = Opening { pi0: forged };
    let forged_conditions = names(failing(
        &srs,
        &bounds,
        &vk_f,
        &com,
        &(y.clone() + one.clone()),
        &forged_opening,
    ));
    assert!(
        forged_conditions.is_empty(),
        "the trapdoor must be able to forge, or the equations are not the scheme's"
    );
    println!(
        "  TOXIC WASTE: a trapdoor-forged opening of a false y verifies (all conditions hold)"
    );
    drop(waste);

    // E2 restated directly, so the trace's last line is the scheme's own equation.
    assert_eq!(
        pairing(srs.a0(), &opening.pi0).expect("shaped"),
        vk_f * com.c - y,
        "E2 restated"
    );
    // ---- the same scheme, driven through `pcs::api::WeightPcs` -------------
    // The point is not ceremony: this is the seam's second implementor, and it
    // only fits because `value_of` and the mask seed now live on
    // `WeightPcsExt`. A short-key LFC can neither recover its witness from `c`
    // nor blind an opening it does not have.
    {
        use zk::pcs::api::WeightPcs as _;
        let lfc = Lfc {
            srs: &srs,
            bounds: &bounds,
        };
        let com_t = lfc.commit(&x).expect("trait commit");
        assert_eq!(
            com_t,
            commit(&srs, &x).expect("free-function Com"),
            "the trait commits exactly as §4's Com does"
        );
        let (y_t, proof_t) = lfc.open(&x, &f).expect("trait open");
        assert_eq!(
            y_t,
            ring_dot(&f, &x),
            "the trait must report the same claim as Open(ck,f,x)"
        );
        lfc.verify(&com_t, &f, &y_t, &proof_t)
            .expect("honest proof verifies through the trait");
        // ... and still refuses a false claim, naming what failed.
        match lfc.verify(&com_t, &f, &(y_t + one), &proof_t) {
            Err(Dispatch::Failed(checks)) => assert!(
                checks.contains(&E2),
                "a false y must be caught by E2, got {checks:?}"
            ),
            other => panic!("expected a named E2 refusal, got {other:?}"),
        }
        println!(
            "  WeightPcs dispatch: trusted power-window SRS + PreVerify + (π₁, π₀) \
             fit commit/open/verify; the tall-key extras stay on WeightPcsExt"
        );
    }
    println!("  every step above is a call into zk::pcs::powers_srs");
}
