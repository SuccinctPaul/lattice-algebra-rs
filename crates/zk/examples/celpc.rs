//! CELPC — *Concretely Efficient Lattice-based Polynomial Commitment* —
//! Hwang, Seo and Song, CRYPTO 2024, eprint 2024/306, assembled from `src`
//! only: the **univariate lattice PCS** of §4.1 (`PC.Setup`, `PC.Com`,
//! `PC.Open`, `PC.Eval`, `PC.Verify`) over the modified Ajtai commitment of
//! §3.3, with the batched proof of opening knowledge of Fig. 1 attached for
//! extractability and made non-interactive by Fiat–Shamir (§5: "convert the
//! interactive protocol into a non-interactive one using the Fiat–Shamir
//! transform").
//!
//! Like [`greyhound_pcs`](greyhound_pcs) and [`cmnw`](cmnw), this file holds no
//! cryptographic logic. The large-field → small-ring-coefficient encoding
//! `Ecd`/`Dcd` (Lemma 9 + Alg. 1, §3.1) is [`zk::pcs::digit_pack`]; the monomial
//! challenge set `C = {1, X, …, X^{2d−1}}` and the batched `Σ`-protocol of
//! Fig. 1 are [`zk::pcs::monomial_pok`]; the Ajtai key is
//! [`zk::pcs::key::RingMatrixKey`]; each `Σᵢ cᵢ·⃗vᵢ` fold goes through
//! [`fold_rows`] (a [`zk::pcs::mixed::BlockMat`] row contraction); the norm
//! gates are [`zk::shortness::exact_l2`]. What lives here is the instance, the
//! message order, and the eight equations §4.1 and Fig. 1 print.
//!
//! # The scheme in one paragraph
//!
//! `N = n·m` field coefficients split into `m` blocks of `n`, each block packed
//! by `Ecd` into `ℓ = rn/d` ring elements and committed on its own
//! (`mᵢ = A₀·hhᵢ`). An opening at `x` is *one* ring vector
//! `e = Σᵢ Ecd(xⁿⁱ)·hhᵢ` — `O(ℓ)` ring elements, i.e. `Õ(√N)`, which is the
//! square-root proof size. It verifies because
//! `Dcd(Ecd(s)·u) = s·Dcd(u)` ([`zk::pcs::digit_pack`]'s pinning identity), so
//! `Dcd(e)` *is* the folded block `Σᵢ xⁿⁱ⃗hᵢ`, and
//! `y = ⟨Dcd(e), (1,x,…,xⁿ⁻¹)⟩` is `h(x)` while the verifier touches only `n`
//! field elements. Binding is `MSIS` *conditional on the responses being short*,
//! which is what `β_Eval`/`β_Open` gate, and Fig. 1 turns "these `mᵢ` really do
//! have openings" into an argument of knowledge.
//!
//! # Scope: the non-hiding ("w/o ZK") variant
//!
//! §5.3 benchmarks `Ours` and `Ours w/o ZK` separately, and the footnote there
//! says the non-zero-knowledge version "excludes all random sampling
//! procedures". That is the variant assembled here, and it is the reachable
//! one: the only part of the construction that needs discrete Gaussian sampling
//! over a coset is the randomized encoding `R.Ecd` of §3.2 —
//!
//! > "Given an element `⃗a ∈ Z_p^{d/r}` and a positive real `s > 0`, output a
//! > ring element `aaa ← D_{Ecd(⃗a)+P Z^d, sP}` where `P ∈ Z^{d×d}` is the
//! > negacyclic matrix of `X^{d/r} − b`" (§3.2, `R.Ecd`)
//!
//! — and this repo has no such sampler. `algebra::crypto::sampling` exposes
//! `DiscreteGaussian` ("Truncated discrete Gaussian `D_{Z,σ}`", spherical over
//! `Z` by CDT inversion) and nothing else Gaussian; searching `foundation` and
//! `algebra::crypto` for `coset`, `Peikert`, `convolution sampler` and a
//! negacyclic-matrix covariance turns up no capability to call. Concretely, the
//! *hiding* variant would additionally need:
//!
//! 1. a coset sampler for `D_{Ecd(⃗a)+P Z^d, sP}` (the paper uses
//!    Micciancio–Walter's convolution sampler over `P^{-1}Ecd(⃗a) + Z^d`), which
//!    `R.Ecd` wraps — every masked object downstream (`hhᵢ`, the Fig. 1 masks
//!    `ggⱼ`, the blinder blocks) is sampled through it;
//! 2. `PC.Com` step 2's blinders `b₁,…,b_{n−1} ← U(Z_p)` and the two extra
//!    blocks `⃗h_m = (b₁,…,b_{n−1},0)`, `⃗h_{m+1} = (0,−b₁,…,−b_{n−1})`, whose
//!    `⟨x·⃗h_m + ⃗h_{m+1}, ⃗x⟩ = 0` is what hides the coefficients;
//! 3. the `A₁ = [A₁′|I_µ]` half of the key and `ηᵢ ← D_{Z^d,σ₁}^{µ+ν}`, so a
//!    commitment is `mᵢ = A₀·hhᵢ + A₁·ηᵢ`, the `τ_j` responses come back, and
//!    `PC.Open`'s gate becomes the doubled `‖(2hhᵢ ‖ 2ηᵢ)‖₂ ≤ 2d·β`;
//! 4. `β_Open`, `β_Eval` and `β_PC` from Thm. 7's *Gaussian* widths instead of
//!    Alg. 1's deterministic digit bound, plus the Hint-MLWE hypotheses of
//!    Thm. 4/6/9 that make the transcripts simulable.
//!
//! Items 2–4 are arithmetic this repo can already do; item 1 is the blocker,
//! and it is a sampling capability, not a change to any scheme step.
//!
//! # Toy vs paper (Table 1, Table 2, §5.1)
//!
//! | | paper (§5.1) | here | why |
//! |---|---|---|---|
//! | `p` | `bʳ+1` with `b = 63388`, `r = 16`, 255 bits | `b = 210`, `r = 4`, `p = 1944810001` (31 bits) | a 255-bit field needs big-integer arithmetic (gap G7); `p = bʳ+1` prime, `r ∣ d` and `d/r` lanes are all kept |
//! | `log q` | ≈ 112, split RNS over two 56-bit primes | `q = 2³²−99`, one prime | [`zk::foundation::encoding::ring_to_u32`] asserts `q ≤ 2³²`, so a 112-bit coefficient cannot even be absorbed into the transcript |
//! | `d` | 2048 | 64 | keeps the toy interactive; `d` only ever enters as the ring degree |
//! | `µ`, `ν` | 1, 2 | 2, absent | 2 rows keep the Ajtai key non-degenerate at toy size; `ν` counts the `A₁·η` columns, which the non-hiding variant does not have |
//! | `ℓ`, `m`, `N` | `2⁵–2⁸`, `2⁷–2^{10}`, `2^{19}–2^{25}` | 2, 4, 128 | `N = n·m` with `n = d·ℓ/r` is the structural requirement, and it holds exactly: `32 = 64·2/4` |
//! | `κ` | `⌈λ/log₂(2d)⌉`, `λ = 128` | same formula ⇒ 19 | [`rounds_for`] |
//! | widths `s₁,s₂,s₃,σ₁,σ₂,σ₃` | Gaussian, sized against `η_ε` | unused | deterministic `Ecd` needs no width and no `η` is sampled |
//! | commitment compression, `D = 24` bits (§5.2) | applied | not applied | a wire-format optimization, orthogonal to the protocol |
//!
//! The *protocol* and every *identity* it rests on are the paper's; the *sizes*
//! are a structurally faithful toy, and no security level is claimed (the
//! paper's own target is root Hermite factor `δ ≈ 1.005` at `λ = 128`).
//!
//! Run with: `cargo run -p lattice-zk --example celpc`

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::{CenteredRing, PolynomialQuotientRing, Ring};
use zk::foundation::fs::absorb_rings;
use zk::pcs::digit_pack::LanePacking;
use zk::pcs::key::RingMatrixKey;
use zk::pcs::monomial_pok::{
    challenges, commit_masks, fold_rows, norm_sq, open_violations, prove_open, rounds_for, scale,
    OpenProof, OpenViolation,
};
use zk::pcs::projection::to_coeffs;
use zk::shortness::exact_l2::max_magnitude;

/// The commitment modulus: `2³² − 99`, prime, `≡ 5 (mod 8)`, so this instance
/// has **no NTT** and every ring product is schoolbook (CELPC's own `q` is a
/// 112-bit RNS modulus, unrepresentable here — see the table above).
type Q = Zq<4294967197>;
/// Ring degree `d`.
const D: usize = 64;
type Elt = PolyRing<Q, D>;

/// Encoding base `b`.
const BASE: u64 = 210;
/// Encoding digit count `r`, with `p = bʳ + 1` prime and `r ∣ d`.
const DIGITS: usize = 4;
/// Ajtai rows `µ` (the paper's 1, widened to 2 to keep the key non-degenerate).
const MU: usize = 2;
/// Ring elements per block `ℓ`, so `n = d·ℓ/r` field elements ride each one.
const ELL: usize = 2;
/// Number of blocks `m`: the `√` side of the split.
const BLOCKS: usize = 4;
/// Security parameter `λ`, which enters only through `κ`.
const LAMBDA: usize = 128;

/// Field elements per block: `n = d·ℓ/r`.
const N_BLOCK: usize = D / DIGITS * ELL;
/// Committed polynomial length in field elements: `N = n·m`.
const N_DEG: usize = N_BLOCK * BLOCKS;

// ---- the checks, named by the §4.1 / Fig. 1 step they implement -------------

/// `PC.Open` step 1: `‖2·hhᵢ‖₂ ≤ 2d·β_PC.Open`.
const OPEN1: &str = "O1: ||2*hh_i|| <= 2d*beta_Open";
/// `PC.Open` step 3: each commitment really is the Ajtai image of its witness.
/// Step 2 — the blinder block `hh_{m+1}`'s own gate — is hiding-only and has no
/// counterpart here.
const OPEN3: &str = "O3: m_i = A0*hh_i";
/// `PC.Open` step 4: `h(X) = Σᵢ X^{ni}·⟨⃗hᵢ, ⃗X⟩` from the decoded witness.
const OPEN4: &str = "O4: h = sum X^ni <h_i,X>";
/// `PC.Verify`, first clause: `‖e‖₂ ≤ β_PC.Eval` (Thm. 7's bound, `η`-free).
const V1: &str = "V1: ||e|| <= beta_Eval";
/// `PC.Verify`, second clause: `y = ⟨Dcd(e), (1,x,…,x^{n−1})⟩ mod p`.
const V2: &str = "V2: y = <Dcd(e),(1,x,..)>";
/// `PC.Verify`, third clause: `A₀·e = Σᵢ Ecd(x^{ni})·mᵢ` — the non-hiding
/// truncation of §4.1's `+ Ecd(x)·m_m + m_{m+1}`.
const V3: &str = "V3: A0*e = sum Ecd(x^ni)*m_i";
/// Fig. 1 step 11: `‖t_j‖₂ ≤ β_Open`, per round.
const POK11: &str = "P11: ||t_j|| <= beta_Open";
/// Fig. 1 step 12: `A₀·t_j = gg_j + Σᵢ c_{j,i}·mᵢ`, per round.
const POK12: &str = "P12: A0*t_j = gg_j + sum c_ji*m_i";

/// `PC.Setup`: the commitment key is `A₀` alone (`A₁` exists only to carry the
/// `η` randomness that the non-hiding variant does not sample).
fn keygen(seed: &[u8; 32]) -> RingMatrixKey<Q, D> {
    RingMatrixKey::<Q, D>::setup(b"celpc-a0", seed, MU, ELL)
}

/// `PC.Com` steps 1 and 3: block the coefficients, encode, commit. Step 2 (the
/// blinders) is hiding-only and absent here.
#[derive(Clone)]
struct Opening {
    /// `hhᵢ = Ecd(⃗hᵢ)`, one `ℓ`-vector per block.
    witnesses: Vec<Vec<Elt>>,
    /// `mᵢ = A₀·hhᵢ`.
    commitments: Vec<Vec<Elt>>,
}

fn commit(key: &RingMatrixKey<Q, D>, pack: &LanePacking, h: &[u64]) -> Opening {
    let blocks = pack.blocks(h, BLOCKS).expect("N = n*m");
    let witnesses: Vec<Vec<Elt>> = blocks
        .iter()
        .map(|b| pack.encode::<Q, D>(b).expect("coefficients in Z_p"))
        .collect();
    let commitments = witnesses
        .iter()
        .map(|w| key.matvec(w).expect("ell columns"))
        .collect();
    Opening {
        witnesses,
        commitments,
    }
}

/// The `PC.Open` clauses of §4.1, evaluated without short-circuiting: the
/// names that did **not** hold.
fn open_failing(
    key: &RingMatrixKey<Q, D>,
    pack: &LanePacking,
    claimed: &[u64],
    op: &Opening,
    doubled_limit: u128,
) -> Vec<&'static str> {
    assert_eq!(op.witnesses.len(), BLOCKS, "one witness per block");
    assert_eq!(op.witnesses.len(), op.commitments.len(), "paired");
    let mut bad: Vec<&'static str> = Vec::new();
    let mut decodes: Vec<Vec<u64>> = Vec::new();
    for (i, w) in op.witnesses.iter().enumerate() {
        // Step 1: the doubled norm gate. Reported as one name, since §4.1
        // numbers it per commitment but a scheme-level tamper moves them all.
        if norm_sq(&scale(w, Q::ONE + Q::ONE)).expect("within u128") > doubled_limit {
            bad.push(OPEN1);
        }
        // Step 3: the commitment equation.
        if key.matvec(w).expect("shape") != op.commitments[i] {
            bad.push(OPEN3);
        }
        decodes.push(pack.decode(w).expect("encode is total"));
    }
    // Step 4: the polynomial the witness decodes to must be the claimed one.
    let refs: Vec<&[u64]> = decodes.iter().map(|v| v.as_slice()).collect();
    if pack.recombine(&refs, N_BLOCK).expect("uniform blocks") != claimed {
        bad.push(OPEN4);
    }
    bad.sort_unstable();
    bad.dedup();
    bad
}

/// `PC.Eval` step 1: the weights `Ecd(xⁿⁱ)` and `e = Σᵢ Ecd(xⁿⁱ)·hhᵢ`.
fn eval_witness(pack: &LanePacking, witnesses: &[Vec<Elt>], x: u64) -> (Vec<Elt>, Vec<u64>) {
    let weights = pack.block_weights(x, N_BLOCK, BLOCKS);
    let alpha: Vec<Elt> = weights
        .iter()
        .map(|w| pack.encode_scalar::<Q, D>(*w).expect("in Z_p"))
        .collect();
    let refs: Vec<&[Elt]> = witnesses.iter().map(|v| v.as_slice()).collect();
    (
        fold_rows(&alpha, &refs).expect("one row per block"),
        weights,
    )
}

/// `PC.Eval` step 2: `y = ⟨Dcd(e), (1,x,…,x^{n−1})⟩ mod p`.
fn eval_value(pack: &LanePacking, e: &[Elt], x: u64) -> u64 {
    pack.eval_fold(&pack.decode(e).expect("decode"), x)
}

/// The three `PC.Verify` clauses of §4.1, without short-circuiting.
fn verify_failing(
    key: &RingMatrixKey<Q, D>,
    pack: &LanePacking,
    commitments: &[Vec<Elt>],
    x: u64,
    y: u64,
    e: &[Elt],
    beta_eval_sq: u128,
) -> Vec<&'static str> {
    let mut bad: Vec<&'static str> = Vec::new();
    if norm_sq(e).expect("within u128") > beta_eval_sq {
        bad.push(V1);
    }
    if eval_value(pack, e, x) != y {
        bad.push(V2);
    }
    let (recombined, _) = eval_witness(pack, commitments, x);
    if key.matvec(e).expect("shape") != recombined {
        bad.push(V3);
    }
    bad
}

/// Fig. 1's challenge table, Fiat–Shamir-compiled. Prover and verifier walk
/// **this one function**, so the two sides cannot derive different challenges —
/// the failure mode that once made [`zk::pcs::mle`] reject honest proofs.
fn pok_challenges(
    key: &RingMatrixKey<Q, D>,
    commitments: &[Vec<Elt>],
    mask_commitments: &[Vec<Elt>],
) -> Vec<Vec<Elt>> {
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/celpc-pok");
    for i in 0..key.rows() {
        absorb_rings(&mut tr, b"a0", key.row(i));
    }
    for c in commitments {
        absorb_rings(&mut tr, b"m", c);
    }
    for g in mask_commitments {
        absorb_rings(&mut tr, b"gg", g);
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&tr.challenge_bytes(32));
    challenges::<Q, D>(b"celpc-c", &seed, mask_commitments.len(), BLOCKS)
}

/// Fig. 1 steps 5–9 from a given set of masks: the commitments to them, the
/// challenges they force, and the responses.
fn pok_round(
    key: &RingMatrixKey<Q, D>,
    op: &Opening,
    masks: &[Vec<Elt>],
) -> (OpenProof<Q, D>, Vec<Vec<Elt>>) {
    let mrefs: Vec<&[Elt]> = masks.iter().map(|v| v.as_slice()).collect();
    let mask_commitments = commit_masks(key, &mrefs).expect("ell-wide masks");
    let table = pok_challenges(key, &op.commitments, &mask_commitments);
    let wrefs: Vec<&[Elt]> = op.witnesses.iter().map(|v| v.as_slice()).collect();
    (
        prove_open(key, &mrefs, &wrefs, &table).expect("shapes"),
        table,
    )
}

/// Fig. 1 steps 2–3 on the prover's side: `⃗gⱼ ← U(Z_pⁿ)`, then `Ecd`.
fn pok_masks(pack: &LanePacking, seed: &[u8; 32], kappa: usize) -> Vec<Vec<Elt>> {
    let flat = pack.uniform_preimages(b"celpc-mask", seed, kappa * N_BLOCK);
    flat.chunks(N_BLOCK)
        .map(|g| pack.encode::<Q, D>(g).expect("in Z_p"))
        .collect()
}

/// Fig. 1 steps 11–12, mapped onto this scheme's check names.
fn pok_failing(
    key: &RingMatrixKey<Q, D>,
    op: &Opening,
    proof: &OpenProof<Q, D>,
    table: &[Vec<Elt>],
    beta_open_sq: u128,
) -> Vec<&'static str> {
    let refs: Vec<&[Elt]> = op.commitments.iter().map(|v| v.as_slice()).collect();
    match open_violations(key, &refs, proof, table, beta_open_sq) {
        Ok(viol) => {
            let mut bad: Vec<&'static str> = viol
                .iter()
                .map(|v| match v {
                    OpenViolation::Linear { .. } => POK12,
                    OpenViolation::TooLong { .. } => POK11,
                })
                .collect();
            bad.sort_unstable();
            bad.dedup();
            bad
        }
        // A malformed proof is a harness bug, never a "rejection": naming it
        // would let a shape error masquerade as a caught tamper.
        Err(err) => panic!("malformed opening proof: {err}"),
    }
}

/// The committed polynomial of the demo: `N` field elements across the range.
fn committed(pack: &LanePacking) -> Vec<u64> {
    (0..N_DEG)
        .map(|i| {
            let mut x = (i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15);
            x ^= x >> 30;
            x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
            x ^= x >> 27;
            x = x.wrapping_mul(0x94D0_49BB_1331_11EB);
            x ^ (x >> 31)
        })
        .map(|x| x % pack.modulus())
        .collect()
}

fn one() -> Elt {
    Elt::from_coefficients(vec![Q::ONE])
}

/// Proof + commitment size in bytes, for the survey's comparison column.
fn size_bytes(op: &Opening, e: &[Elt], proof: &OpenProof<Q, D>) -> usize {
    let rings = op.commitments.len() * MU
        + e.len()
        + proof.responses.len() * ELL
        + proof.mask_commitments.len() * MU;
    rings * D * 4
}

/// Assert the named checks are exactly `expected` (empty means "must verify").
fn expect(label: &str, got: &[&'static str], expected: &[&'static str]) {
    let mut g = got.to_vec();
    g.sort_unstable();
    g.dedup();
    let mut w = expected.to_vec();
    w.sort_unstable();
    w.dedup();
    if w.is_empty() {
        assert!(g.is_empty(), "{label}: rejected by {g:?}");
        println!("  {label}: verifies");
        return;
    }
    assert!(!g.is_empty(), "{label}: the tamper was accepted");
    assert_eq!(g, w, "{label}: failing set");
    println!("  {label}: rejected by {g:?}");
}

fn main() {
    let seed = [0xceu8; 32];
    let pack = LanePacking::new(BASE, DIGITS, D).expect("p = 210^4+1 is prime");
    let key = keygen(&seed);
    assert_eq!(pack.lanes() * DIGITS, D, "r must split d into lanes");
    assert_eq!(N_BLOCK, D * ELL / DIGITS, "the paper's n = d*ell/r");
    assert_eq!(pack.modulus(), BASE.pow(DIGITS as u32) + 1);
    let kappa = rounds_for(D, LAMBDA);

    // Thm. 7's bounds under the deterministic encoding: `‖Ecd(⃗a)‖∞ ≤ (b+2)/2`
    // per coefficient and `‖Ecd(a)‖₁ ≤ (b+2)r/2` per scalar weight, over `ℓ·d`
    // coefficients per ring vector. No `σ`/`s` width enters, because nothing is
    // sampled.
    let coef = u128::from(pack.coefficient_bound());
    let l1 = u128::from(pack.scalar_l1_bound());
    let area = u128::from((ELL * D) as u64);
    let beta_open_sq = area * (coef * (BLOCKS as u128 + 1)).pow(2);
    let beta_eval_sq = area * (coef * l1 * BLOCKS as u128).pow(2);
    // `PC.Open` step 1 squares `2d·β_PC.Open`, hence the `4d²`.
    let doubled_limit = 4 * u128::from((D * D) as u64) * beta_open_sq;

    let h = committed(&pack);
    let x = 123_456_789 % pack.modulus();

    // ---- PC.Com, PC.Open ---------------------------------------------------
    let op = commit(&key, &pack, &h);
    assert!(
        op.witnesses.iter().all(|w| {
            let c = to_coeffs::<Q, D>(w);
            c.iter()
                .all(|k| k.abs_infinity() <= pack.coefficient_bound())
        }),
        "Alg. 1's digit bound must hold on an honest encoding"
    );
    expect(
        "PC.Open on the honest witness",
        &open_failing(&key, &pack, &h, &op, doubled_limit),
        &[],
    );

    // ---- PC.Eval, PC.Verify ------------------------------------------------
    let (e, weights) = eval_witness(&pack, &op.witnesses, x);
    let y = eval_value(&pack, &e, x);
    assert_eq!(
        y,
        pack.eval_at(&h, x),
        "the fold of Dcd(e) must equal the direct h(x)"
    );
    expect(
        "PC.Verify on the honest evaluation",
        &verify_failing(&key, &pack, &op.commitments, x, y, &e, beta_eval_sq),
        &[],
    );

    // ---- Π_PC.Open (Fig. 1, Fiat–Shamir) ----------------------------------
    let masks = pok_masks(&pack, &[0xf1u8; 32], kappa);
    let (proof, table) = pok_round(&key, &op, &masks);
    expect(
        "Fig. 1 over the batched openings",
        &pok_failing(&key, &op, &proof, &table, beta_open_sq),
        &[],
    );

    println!("CELPC 2024/306 §4.1, non-hiding variant — q = 2³²−99 (≡5 mod 8, no NTT), d = {D}");
    println!(
        "  b = {BASE}, r = {DIGITS}, p = {} (31-bit toy vs the paper's 255-bit), ell = {ELL}, n = {N_BLOCK}, m = {BLOCKS}, N = {N_DEG}, mu = {MU}, nu = absent, kappa = {kappa}",
        pack.modulus()
    );
    println!(
        "  honest: PC.Open ok, y = h(x) = {y}, PC.Verify ok, Fig. 1 ok over {kappa} rounds; {} bytes for commitments + opening + POK",
        size_bytes(&op, &e, &proof)
    );
    println!(
        "  beta_Open^2 = {beta_open_sq} vs ||t_j||^2 = {}, beta_Eval^2 = {beta_eval_sq} vs ||e||^2 = {}",
        norm_sq(&proof.responses[0]).expect("ok"),
        norm_sq(&e).expect("ok"),
    );
    println!(
        "  sqrt size: {BLOCKS} commitments of {ELL} ring elements each, one opening of {} ring elements; block weights x^(n*i) = {:?}",
        e.len(),
        weights
    );

    // ---- tampers: each trips the check it actually breaks ------------------
    // A false claim enters through `y` alone.
    let lie = pack.add(y, 1);
    expect(
        "false claim y+1",
        &verify_failing(&key, &pack, &op.commitments, x, lie, &e, beta_eval_sq),
        &[V2],
    );

    // A bumped evaluation witness: what it decodes to moves (V2) and the Ajtai
    // relation breaks (V3), while its length stays inside `β_Eval` — so V1 is
    // demonstrably not the check doing the work here.
    let mut bumped = e.clone();
    bumped[0] = bumped[0].clone() + one();
    expect(
        "tampered evaluation witness e",
        &verify_failing(&key, &pack, &op.commitments, x, y, &bumped, beta_eval_sq),
        &[V2, V3],
    );

    // A tampered commitment: the opening equation (V3) and both knowledge
    // halves (O3, P12) see it. The claim (V2) is about `e` alone and survives.
    let mut coms = op.commitments.clone();
    coms[1][0] = coms[1][0].clone() + one();
    let tampered = Opening {
        witnesses: op.witnesses.clone(),
        commitments: coms.clone(),
    };
    expect(
        "tampered commitment m_1 (PC.Verify)",
        &verify_failing(&key, &pack, &coms, x, y, &e, beta_eval_sq),
        &[V3],
    );
    expect(
        "tampered commitment m_1 (PC.Open)",
        &open_failing(&key, &pack, &h, &tampered, doubled_limit),
        &[OPEN3],
    );
    expect(
        "tampered commitment m_1 (Fig. 1)",
        &pok_failing(&key, &tampered, &proof, &table, beta_open_sq),
        &[POK12],
    );

    // A witness that decodes to a different polynomial: `PC.Open` step 4 only.
    let mut other = h.clone();
    other[5] = pack.add(other[5], 1);
    expect(
        "wrong polynomial h'",
        &open_failing(&key, &pack, &other, &op, doubled_limit),
        &[OPEN4],
    );

    // A tampered Fig. 1 response: exactly the relation of that round.
    let mut bad_proof = proof.clone();
    bad_proof.responses[3][0] = bad_proof.responses[3][0].clone() + one();
    expect(
        "tampered response t_3",
        &pok_failing(&key, &op, &bad_proof, &table, beta_open_sq),
        &[POK12],
    );

    // A response scaled up by 5: too long *and* no longer satisfies the
    // relation, which is what shows P11 and P12 are separate gates.
    let mut grown = proof.clone();
    grown.responses = grown
        .responses
        .iter()
        .map(|t| scale(t, Q::from(5)))
        .collect();
    expect(
        "rescaled responses 5*t_j",
        &pok_failing(&key, &op, &grown, &table, beta_open_sq),
        &[POK12, POK11],
    );

    // Oversized masks: the relation still holds (the mask commitments are
    // honestly derived from them), so only the length gate fires.
    let fat: Vec<Vec<Elt>> = masks.iter().map(|g| scale(g, Q::from(4_000))).collect();
    let (fat_proof, fat_table) = pok_round(&key, &op, &fat);
    expect(
        "oversized masks (relation holds, bound does not)",
        &pok_failing(&key, &op, &fat_proof, &fat_table, beta_open_sq),
        &[POK11],
    );

    // The norm gates carry real weight on the PCS itself: scaling *every*
    // witness by `B` gives a rival that satisfies O3, O4, V2 and V3 exactly as
    // well as the honest one — the scheme is linear — and is rejected only by
    // the length gates. That is the lattice multiple-preimage problem `β` exists
    // to rule out, and the reason binding is stated "for short responses".
    let big = 10_000u64;
    let rival_w: Vec<Vec<Elt>> = op
        .witnesses
        .iter()
        .map(|w| scale(w, Q::from(big)))
        .collect();
    let rival_c: Vec<Vec<Elt>> = rival_w
        .iter()
        .map(|w| key.matvec(w).expect("shape"))
        .collect();
    let rival = Opening {
        witnesses: rival_w,
        commitments: rival_c,
    };
    let decoded: Vec<Vec<u64>> = rival
        .witnesses
        .iter()
        .map(|w| pack.decode(w).expect("decode"))
        .collect();
    let drefs: Vec<&[u64]> = decoded.iter().map(|v| v.as_slice()).collect();
    let rival_h = pack.recombine(&drefs, N_BLOCK).expect("uniform blocks");
    let (rival_e, _) = eval_witness(&pack, &rival.witnesses, x);
    let rival_y = eval_value(&pack, &rival_e, x);
    assert!(
        rival_h != h && rival_y != y,
        "the rival must open to a different polynomial"
    );
    assert_eq!(rival_y, pack.mul(y, big), "linearity: the rival claims B*y");
    expect(
        "long rival opening (B·hh, B·m)",
        &open_failing(&key, &pack, &rival_h, &rival, doubled_limit),
        &[OPEN1],
    );
    expect(
        "long rival evaluation (B·e)",
        &verify_failing(
            &key,
            &pack,
            &rival.commitments,
            x,
            rival_y,
            &rival_e,
            beta_eval_sq,
        ),
        &[V1],
    );
    println!(
        "  the length gates are the only thing separating two consistent openings (||B·e||_inf = {})",
        max_magnitude(&to_coeffs(&rival_e)),
    );
    println!("  every tamper is rejected by the check it actually violates");
}
