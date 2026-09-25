//! Akita — a lattice-based polynomial commitment scheme, Dao–Bodaghi–
//! Khajehpour–Vitto–Badakhshan–Georghiades–Liu–Zhang–Thaler, eprint
//! 2026/1983 (rev. 2026-09-18) — assembled from this crate's capabilities.
//!
//! Nothing cryptographic is defined in this file. It calls
//! [`zk::pcs::setup_stream`] for §4.3's shared-prefix matrices (Eq. 65–67),
//! [`zk::pcs::key::RingMatrixKey`] for the Ajtai images,
//! [`zk::sumcheck::alphabet`] for the negative-biased digit alphabet, the
//! degree-halved range predicate and Eq. (107)'s native-block split (Remark 6.1,
//! Eq. 111–114), [`zk::pcs::norm_route`] for §6.2's protocol statement
//! (Eq. 113, 116–128), [`zk::shortness::exact_l2`] for the exact-ℓ2 gate itself,
//! [`zk::pcs::fold_geom`] for the certified challenge norms that Eq. (79) and
//! Corollary 10.26 price, and [`zk::sumcheck::fused`] for Figure 2's compressed
//! degree-`L` sum-check and Eq. (128)'s fusion.
//!
//! # What is assembled here
//!
//! Akita's *one level*, on both of §6.2's response-norm routes. The **Euclidean**
//! route is certified in both of its encodings (Eq. 120's single field identity vs
//! Eqs. 121–123's digit-plane Gram recombination — the choice p. 69's "the direct
//! route is admissible only when `max{U_dir, S_max} < q`" decides), and the
//! **coefficient** route derives the `A`-collision radius from `Δ_f^cert` and
//! Eq. (79) and sends no norm certificate at all. Every schedule is priced on both
//! routes and prints which ones it admits.
//!
//! 1. **root batch** — `SRC` independently committed source vectors, each bound
//!    by its own digest, folded per group with transcript challenges
//!    `c_{g,c,i}` into `z_g := Σ_{c,i} c_{g,c,i} s_{g,c,i}` (Eq. 104, p. 62).
//! 2. **the canonical coefficient split** — `ẑ_g := G⁻¹_{b_z,m_A}(z_g)`
//!    (Eq. 105), emitted in Eq. (107)'s native-block order with a *runtime* ring
//!    dimension per role, so `d_A` for the response digits and `d = 2` for the
//!    opening digits (with `s = D/d = 2` subcolumns) coexist in one witness.
//! 3. **the two-stage compression chain's payload** — `L_F = L_H = 2` links,
//!    128 bytes total (§4.5, "commitments compressed to 128 bytes each").
//! 4. **the offloaded edge** — `edge := OffloadedSetup` (Eq. 63) with *both*
//!    groups the successor must check: the witness group and the setup group,
//!    whose deferred matrix work is reduced to an evaluation of the padded
//!    shared setup vector `S` (§1.1 p. 6: "an inner-product sum-check reduces
//!    the matrix computation to an evaluation of a setup polynomial"), with
//!    `N_active`/`N_setup` from Eq. 65/173 as the cost gate.
//! 5. **the norm certificate** — `E_int(ẑ) = E_resp ∧ E_resp ≤ S_max` (Eq. 118),
//!    decided by the route §6.2 admits and *proved* by Figure 2's compressed
//!    sum-check in Eq. (125)'s shape, where the verifier's claim is built from
//!    the transmitted messages (`C_norm := Σ ζ_pair^idx p_{t,h,k}`, or the
//!    canonical `E_resp` in the direct case) and its final check is against the
//!    revealed tables. That asymmetry is what makes the check bite.
//! 6. **the π binding** — Eqs. (126)–(128). The address map `π : [N_A] × [δ_f]`
//!    is a declared part of the statement, and check C11 runs the printed
//!    equation: `C_bind` is formed from the *norm sum-check's own final
//!    evaluations* at its output point `r`, and must equal the `π`-addressed
//!    linear combination of the committed `ẑ` cells; the fused sum-check then
//!    proves `Σ_x (P_base(x) + P_bind(x)) = C_base + C_bind` with `P_base` the
//!    range row of Eq. (115)'s shape.
//! 7. **the collision radius** — Eq. (113) + Eq. (79) on the coefficient route,
//!    Corollary 10.26's `η²_{A,2} = 64Γ²S_max` on the Euclidean one, priced by
//!    [`zk::pcs::norm_route::MsisEstimator`] against `A`'s own provisioned view
//!    (p. 56's admission rule) and re-checked as a declared statement field in
//!    C12: a descriptor may round its radius *up*, never below what its fold
//!    earned.
//!
//! # What is not here, and why
//!
//! * The recursion. Akita "optimizes every fold from root to tail and iterates
//!   the fold to completion" (§1.1 p. 7); this runs one level, a few times.
//!   C11 therefore consumes digit tables that are *revealed* rather than an
//!   evaluation claim carried by a successor — the paper's own words are "the
//!   combined sum-check reduces the range, norm, and relation statements to the
//!   one evaluation claim on `w̃^(j+1)` already carried by the recursive
//!   protocol", and the claim is the one thing a single level cannot have.
//! * A security level. `A` is `1 × 2` at `d_A = 4`, which sits below the Core-SVP
//!   estimator's `μ = 50` floor, so every radius in this file prices at the same
//!   13 bits: the contract gate is live (C12 refuses an under-declared radius) but
//!   it cannot discriminate the routes by hardness here. Where it can, the
//!   estimator's own test at real ranks says so.
//! * Sublinear openings for setup offloading (§9). The offloaded edge's setup
//!   group is carried and checked, but the successor evaluates the prefix
//!   directly: that is Akita's own "direct setup evaluation" column, not its
//!   offloaded one. The missing capability is a vector commitment with
//!   sublinear openings over these rings.
//! * Per-role ring dimensions at the *protocol* layer. They are values at this
//!   layer; `pcs::greyhound`/`pcs::batched` still bind one const-generic ring,
//!   which is gap G1 in `crates/zk/docs/open-milestones.md`.
//!
//! # Instance
//!
//! `q = p32 = 2³² − 99`, Akita's own measured field ("planner-selected dense
//! schedules for `p32 = 2^32 − 99`", Appendix I.1 p. 175). It is prime and
//! `≡ 5 (mod 8)`, so `X^d + 1` does not split completely, no NTT of degree `≥ 4`
//! exists, and every matrix here must come from [`SetupStream`] and be applied
//! by [`RingMatrixKey`]'s schoolbook path. Dimensions are toy
//! (`d_A = 4`, `N_A = 8`); no security level is claimed.
//!
//! Run with: `cargo run -p lattice-zk --example akita`

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake256Xof;
use algebra::crypto::xof::Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::zq::Zq;
use algebra::ring::{PolynomialQuotientRing, Ring};
use std::collections::BTreeSet;
use std::vec::Vec;
use zk::pcs::fold_geom;
use zk::pcs::norm_route::{
    self, CollisionRadius, CoreSvpEstimator, DeclaredRadius, DigitMap, MsisEstimator, NormError,
    NormRoute, SecurityContract,
};
use zk::pcs::setup_stream::{SetupStream, View};
use zk::pcs::RingMatrixKey;
use zk::shortness::exact_l2::{self, Route};
use zk::sumcheck::{alphabet, fused};

/// Akita's `p32`: `2³² − 99`, prime and `5 mod 8`, no NTT past degree 2.
type Q = Zq<4294967197>;
/// The field as `i128`, for exact integer lifts.
const MOD: i128 = 4_294_967_197;
/// Ring dimension `d_A` of the inner folding matrix (Table 3, p. 46).
const D: usize = 4;
/// A second role dimension, to show Eq. (107) carrying `d ≠ d_A` in one witness.
const D_OPEN: usize = 2;
/// Response length in ring elements, so `N_A = m_A d_A`.
const M_A: usize = 2;
/// Base-field coordinates of the reconstructed response.
const N_A: usize = M_A * D;
/// Response base `b_z` (Eq. 116) and certified range base `b*` (Remark 6.1).
const BASE: u64 = 8;
/// Full-field digit depth at base 8: `ceil(log_8 q) = 11`.
const DELTA_FULL: usize = 11;
/// Source vectors in the root batch — the `c ∈ [n_clm]`, `i ∈ [B]` of Eq. 104.
const SRC: usize = 4;
/// Groups at this level: `main`, plus the `setup` group Eq. 63 adds.
const N_GROUPS: usize = 2;
/// Segment length `|I_t|` for Eq. (121)'s public partition.
const SEG_LEN: usize = 2;
/// The compressed commitment payload: two chain stages of two links each.
const COMMIT_BYTES: usize = 128;
/// Boolean domain exponent of the norm sum-check: `N_A = 2^MU` exactly here.
const MU: usize = 3;
/// Ring elements the shared opening path reads: the response coordinates
/// regrouped at `d_open` across `DELTA_FULL` digit planes (Eq. 107 with
/// `s = d_A / d_open` subcolumns).
const OPEN_ELEMENTS: usize = DELTA_FULL * (N_A / D_OPEN);

/// Transcript lanes for the derived challenges. Each stage squeezes its own
/// tape, but the lanes are still kept disjoint so one stage's draw can never
/// silently become another's. `ALPHA_LANE` spans `D` consecutive lanes, and
/// `TAU_LANE` the range row's anchor point.
const WEIGHT_LANE: usize = 0;
const ZETA_LANE: usize = 700;
const ALPHA_LANE: usize = 800;
const TAU_LANE: usize = 900;
const ETA_LANE: usize = 1000;

/// The security contract every schedule's `A` view is checked against, in
/// Core-SVP bits. 13 is what the estimator reports for the toy `1 × 2`-at-`d = 4`
/// `A` this file builds, because its lattice is smaller than the `μ = 50` floor
/// `algebra::security` searches from — so the gate is live (C12 refuses a radius
/// the fold did not earn) without pretending these ranks reach a security level.
const CONTRACT: SecurityContract = SecurityContract { min_bits: 13 };

/// Why an assembly-level check refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Check {
    /// `A z_g = Σ_c c_{g,c} (A s_c)`: the fold is a module homomorphism image.
    Relation,
    /// `z = G_{b,m_A} ẑ`: the digit planes recompose to the response (Eq. 105).
    Recompose,
    /// Every digit lies in `A_{b*}`, via the degree-halved predicate (Eq. 114).
    Range,
    /// The fused norm sum-check closes at its final check (Eq. 120 / 125).
    NormSumcheck,
    /// `E_resp` is the canonical fixed-width encoding under `S_max` (Eq. 118).
    NormCanonical,
    /// `E_int(ẑ) = E_resp ∧ E_resp ≤ S_max`, on the admitted route (Eq. 118).
    NormBound,
    /// The offloaded edge's setup group checks against its own prefix (Eq. 63).
    SetupGroup,
    /// The compressed commitment binds the payload it claims to (§4.5).
    Commitment,
    /// Each batched source's digest binds its own table *and* its own inner
    /// image is `A s_c` of that table (Eq. 104's challenges, Table 3's `t_i`).
    BatchBinding,
    /// `‖z‖²_{2,coef} ≤ E_int(ẑ)`: the direction that makes `E_int` sound (Eq. 117).
    EnergyDirection,
    /// Eq. (117) could not be **evaluated** because one side's squared norm left
    /// `u128`. Distinct from [`Check::EnergyDirection`] on purpose: folding "cannot
    /// decide" into a computed `0` makes `ring > exact` harder to satisfy, so an
    /// undecidable group would otherwise read as a pass.
    EnergyUndecidable,
    /// Eqs. (126)–(128): `π` is injective with the scheduled image, the norm
    /// proof's final evaluations reconstruct from the `π`-addressed `ẑ` cells,
    /// and the fused combined sum-check closes.
    NormBinding,
    /// The declared `A`-collision radius reaches what this level's route derives
    /// from Eq. (113) + (79) / Corollary 10.26, and the contract covers it
    /// (p. 56's admission rule).
    Radius,
}

const ALL_CHECKS: [Check; 13] = [
    Check::Relation,
    Check::Recompose,
    Check::Range,
    Check::NormSumcheck,
    Check::NormCanonical,
    Check::NormBound,
    Check::SetupGroup,
    Check::Commitment,
    Check::BatchBinding,
    Check::EnergyDirection,
    Check::EnergyUndecidable,
    Check::NormBinding,
    Check::Radius,
];

/// The raw challenge shell of the fold's batching weights (§4.3's per-group
/// "raw challenge shell"). Binary keeps a folded response inside the direct
/// window; full-ring pushes it past `q`, which is what the digit-expanded
/// certificate exists for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Shell {
    Binary,
    FullRing,
}

/// A level's public material: everything both parties derive from the seed and
/// the schedule without seeing a witness.
struct Schedule {
    setup: SetupStream,
    /// `A`: the inner folding matrix, `n_A × m_A` at `d_A` (Eq. 66 view).
    a: RingMatrixKey<Q, D>,
    /// `B`: the outer commitment matrix over the digitized inner image.
    b: RingMatrixKey<Q, D>,
    /// `D`: the shared opening matrix, applied at `d_open ≠ d_A`.
    d: RingMatrixKey<Q, D_OPEN>,
    /// Response digit depth `δ_f` (Eq. 111's choice).
    delta_f: usize,
    /// Certified range base `b*`.
    base_star: u64,
    /// Recomposition base `b_z` (Eq. 116). Requires `b_z ≤ b*` (p. 63).
    base: u64,
    shell: Shell,
    route: NormRoute,
    views: Vec<View>,
    /// `N_active = max_I n_I m_I d_I` (Eq. 173).
    n_active: usize,
    /// `N_setup = 2^ceil(log2 N_active)` (Eq. 65).
    n_setup: usize,
    /// `edge_j` (Eq. 63).
    edge: &'static str,
    /// `ω = κ_1`: the certified `ℓ1` mass bound on one raw fold challenge.
    kappa_1: u64,
    /// `Γ²`: the certified squared multiplication-operator bound on the same
    /// family, which Corollary 10.26's Euclidean radius needs.
    gamma_sq: u128,
    /// `|w^(j+1)|` padded to the Boolean cube Eq. (128)'s sum-check runs over.
    witness_len: usize,
}

/// The certified challenge-family bounds of each raw shell: `κ_1 = max ‖c‖_1`
/// and `Γ² = max ‖c‖_{mul,2}²`.
///
/// Both are *worst-case over the family*, not over the draws this run happened to
/// see — that is what makes them schedule data (§6.2 p. 64: "The route,
/// squared-norm bound, response coordinate map, challenge family, and proof shape
/// are fixed before the fold challenges"). For the binary shell a challenge is a
/// `0/1` constant, so it is `1` in both readings; for the full-ring shell the
/// coefficientwise range is `|c| ≤ (q−1)/2` over `d_A` slots, and
/// `‖c‖_{mul,2} ≤ ‖c‖_1` (Lemma 3.1, the inequality [`fold_geom`] documents at
/// its `op_norm_upper_sq`) squares to the same figure. `C12`'s honest path also
/// re-checks the bound against the draws actually used.
fn family_bounds(shell: Shell) -> (u64, u128) {
    match shell {
        Shell::Binary => (1, 1),
        Shell::FullRing => {
            let mass = (D as u64) * ((Q::MODULUS - 1) / 2);
            (mass, u128::from(mass) * u128::from(mass))
        }
    }
}

impl Schedule {
    fn new(seed: &[u8; 32], delta_f: usize, shell: Shell, route: NormRoute) -> Self {
        let setup = SetupStream::new(seed);
        // Eq. 66's views, one per role, each at its own dimension.
        let planes = N_GROUPS * delta_f * M_A;
        let views = vec![
            View::new("A", 1, M_A, D),
            View::new("B", 1, planes, D),
            View::new("D", 1, OPEN_ELEMENTS, D_OPEN),
        ];
        let n_active = SetupStream::active_prefix(&views);
        let (kappa_1, gamma_sq) = family_bounds(shell);
        Self {
            a: setup.matrix::<Q, D>(1, M_A),
            b: setup.matrix::<Q, D>(1, planes),
            d: setup.matrix::<Q, D_OPEN>(1, OPEN_ELEMENTS),
            setup,
            delta_f,
            base_star: BASE,
            base: BASE,
            shell,
            route,
            n_setup: SetupStream::padded_len(n_active),
            views,
            n_active,
            edge: "OffloadedSetup",
            kappa_1,
            gamma_sq,
            witness_len: (N_GROUPS * delta_f * N_A).next_power_of_two(),
        }
    }

    /// `B_dig,h`: "the largest absolute integer admitted by its scheduled digit
    /// alphabet" (p. 69) — `b*/2`, since `A_{b*} = {-b*/2, …, b*/2 − 1}`.
    fn digit_bounds(&self) -> Vec<u64> {
        vec![self.base_star / 2; self.delta_f]
    }

    /// `U_dir` of Eq. (119).
    fn u_dir(&self) -> u128 {
        norm_route::u_dir(N_A, self.base, &self.digit_bounds())
    }

    /// §6.2's route test, applied to this schedule.
    fn route_for(&self, s_max: u128) -> NormRoute {
        norm_route::select(self.u_dir(), s_max, Q::MODULUS)
    }

    /// `Δ_f^cert`, Eq. (113): what the range check certifies about a *difference*
    /// of two accepted responses at this depth.
    fn delta_cert(&self) -> u128 {
        norm_route::delta_cert(self.base_star, self.base, self.delta_f)
    }

    /// Eq. (79): the coefficient route's `A`-collision radius,
    /// `η_{A,g} = 2 κ̄_{1,g} Δ_f^cert`, from the certified challenge-difference
    /// bound `κ̄_1 = 2ω` of p. 108.
    fn coefficient_radius(&self) -> Result<CollisionRadius, NormError> {
        CollisionRadius::from_coefficient(
            norm_route::certified_challenge_difference(self.kappa_1),
            self.delta_cert(),
        )
    }

    /// Corollary 10.26's Euclidean radius `η²_{A,2} = 64Γ²S_max`, available only
    /// when this level actually certifies Eq. (118).
    fn euclidean_radius(&self, s_max: u128) -> Option<Result<CollisionRadius, NormError>> {
        self.route
            .certifies_energy()
            .then(|| CollisionRadius::from_euclidean(self.gamma_sq, s_max))
    }

    /// The tightest radius this schedule's route earns — `A`'s provisioned price.
    fn earned_radius(&self, s_max: u128) -> Option<CollisionRadius> {
        norm_route::tighter(
            self.coefficient_radius().ok(),
            self.euclidean_radius(s_max).and_then(|r| r.ok()),
        )
    }

    /// `A`'s own Module-SIS instance, read off the view that provisioned it
    /// (p. 56: the *pre-existing commitment's* fixed ranks).
    fn msis_a(&self) -> norm_route::MsisInstance {
        self.views[0].msis_instance(Q::MODULUS)
    }

    /// Whether the level sends Eq. (118)'s certificate, and so whether Eqs.
    /// (126)–(128) have a norm proof whose evaluations to bind.
    fn certifies(&self) -> bool {
        self.route.certifies_energy()
    }
}

/// One source polynomial of the root batch, with its own binding digest.
#[derive(Clone)]
struct Source {
    table: Vec<PolyRing<Q, D>>,
    digest: [u8; 32],
}

/// One group's response and the digits certifying it.
#[derive(Clone)]
struct Group {
    /// `z_g` (Eq. 104), reduced into the ring.
    response: Vec<PolyRing<Q, D>>,
    /// `δ_f` digit planes over the `N_A` base-field coordinates, centered.
    planes: Vec<Vec<i64>>,
    /// `z_u^Z` (Eq. 116): the unreduced integer coordinates.
    coords: Vec<i128>,
}

/// The proof: every message the verifier receives.
#[derive(Clone)]
struct Proof {
    sources: Vec<Source>,
    /// `t_c := A s_c`, one inner image per batch member (Table 3's `t_i`).
    inner: Vec<Vec<PolyRing<Q, D>>>,
    groups: Vec<Group>,
    /// `u`: the outer image of all response digits.
    outer: Vec<PolyRing<Q, D>>,
    /// `v`: the shared opening image, at `d_open`.
    opening: Vec<PolyRing<Q, D_OPEN>>,
    /// The compressed commitment payload (§4.5's shape).
    commitment: Vec<u8>,
    /// The setup group's deferred evaluation claim, one per ring coefficient.
    setup_claim: Vec<Q>,
    /// `E_resp` in the canonical encoding `S_max` determines (Eq. 118). Empty on
    /// the coefficient route, which certifies no such statement.
    energy_bytes: Vec<u8>,
    /// The Gram claims `p_{t,h,k}` (Eq. 121); empty on the direct route.
    grams: Vec<norm_route::PairClaim<Q>>,
    /// Figure 2's messages for the norm sum-check (Eq. 125).
    norm_proof: fused::FusedProof<Q>,
    /// The revealed digit planes, plane-major, as field elements: this level's
    /// stand-in for `w^(j+1)`.
    digits_flat: Vec<Q>,
    /// `π`: the declared address map `[N_A] × [δ_f] -> |w^(j+1)|` of §6.2 p. 68,
    /// in the canonical domain order `u * δ_f + h`. Empty on the coefficient
    /// route, which has no norm proof to bind.
    pi_cells: Vec<usize>,
    /// Figure 2's messages for the *combined* sum-check of Eq. (128), which fuses
    /// the range row with the `π` binding and so proves `C_base + C_bind`.
    bind_proof: fused::FusedProof<Q>,
    /// The `A`-collision radius the opening descriptor asks to be provisioned at,
    /// which C12 checks against what this level's route derives (p. 56).
    declared_radius: u128,
}

// --- small shared helpers, all of them calls into `src` ---------------------

/// The centered representative of a residue, as an `i64` digit.
fn centered(v: &Q) -> i64 {
    i64::try_from(v.centered()).expect("a centered lift fits i64")
}

/// A residue from a possibly negative integer.
fn of_i64(v: i64) -> Q {
    Q::from(i128::from(v).rem_euclid(MOD) as u64)
}

/// One field element with `X^0` set.
fn one_elt() -> PolyRing<Q, D> {
    elt_at(0, Q::ONE)
}

/// The zero of `R_{q,D}`. `PolyRing` has no `Zero` impl, so the crate builds it
/// from a full coefficient vector (as `pcs::key`'s private `zero_elt` does).
fn zero_elt() -> PolyRing<Q, D> {
    PolyRing::from_coefficients(vec![Q::ZERO; D])
}

fn elt_at(k: usize, v: Q) -> PolyRing<Q, D> {
    let mut c = vec![Q::ZERO; D];
    c[k] = v;
    PolyRing::from_coefficients(c)
}

fn elt_at_open(k: usize, v: Q) -> PolyRing<Q, D_OPEN> {
    let mut c = vec![Q::ZERO; D_OPEN];
    c[k] = v;
    PolyRing::from_coefficients(c)
}

/// Flatten to base-field coordinates, padded to a whole number of `d`-rings —
/// `PolyRing::coefficients()` trims trailing zeros, so every flattening here
/// pads back before regrouping.
fn flat_d(values: &[PolyRing<Q, D>], d: usize) -> Vec<Q> {
    values
        .iter()
        .flat_map(|v| {
            let mut c: Vec<Q> = v.coefficients().iter().copied().collect();
            c.resize(D, Q::ZERO);
            c.into_iter().take(d.max(D)).collect::<Vec<_>>()
        })
        .collect()
}

fn unflat_d(values: &[Q], d: usize) -> Vec<PolyRing<Q, D>> {
    debug_assert_eq!(d, D);
    values.chunks(D).map(|c| PolyRing::from_coefficients(c.to_vec())).collect()
}

fn bytes_of(values: &[Q]) -> Vec<u8> {
    values
        .iter()
        .flat_map(|c| c.to_u128().to_le_bytes()[..4].to_vec())
        .collect()
}

fn digest(parts: &[&[u8]]) -> [u8; 32] {
    // `Shake256Xof::new`/`absorb`/`squeeze_vec` are `Xof` *trait* methods, so
    // the trait has to be in scope at the call site.
    let mut xof = Shake256Xof::new(b"akita/compress");
    for p in parts {
        xof.absorb(p);
    }
    let out = xof.squeeze_vec(32);
    let mut h = [0u8; 32];
    h.copy_from_slice(&out[..32]);
    h
}

/// A scalar field challenge from a transcript tape.
fn scalar_from(bytes: &[u8], lane: usize) -> Q {
    let mut xof = Shake256Xof::new(b"akita/scalar");
    xof.absorb(bytes);
    xof.absorb(&(lane as u64).to_le_bytes());
    let out = xof.squeeze_vec(8);
    let mut raw = [0u8; 8];
    raw.copy_from_slice(&out[..8]);
    Q::from(u64::from_le_bytes(raw) % Q::MODULUS)
}

/// A full-ring challenge from a tape: `D` consecutive scalar lanes, i.e. a
/// uniform element of `R_{q,D}` (p. 50: an evaluation-trace fold "samples its
/// challenge in the full ring `R_{q,d_A}`"; p. 62: `c^A_{g,c,i} ∈ C_{d_A,g}`).
fn ring_from(bytes: &[u8], base_lane: usize) -> PolyRing<Q, D> {
    PolyRing::from_coefficients(
        (0..D)
            .map(|k| scalar_from(bytes, base_lane + k))
            .collect(),
    )
}

/// The ring weights `c_{g,c}` of Eq. (104), from the transcript after the
/// public statement and the inner images. A pure function of its inputs, so the
/// prover and verifier derive it identically.
fn group_weights(
    sched: &Schedule,
    sources: &[Source],
    inner: &[Vec<PolyRing<Q, D>>],
) -> Vec<Vec<PolyRing<Q, D>>> {
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/akita/fs");
    absorb_schedule(&mut tr, sched);
    absorb_batch(&mut tr, sources, inner);
    let tape = tr.challenge_bytes(64);
    (0..N_GROUPS)
        .map(|g| {
            (0..SRC)
                .map(|c| match sched.shell {
                    // The bounded shell: a `0/1` constant, i.e. the zero
                    // polynomial of `C_{d_A}`, so the fold cannot grow the
                    // response (`‖ι(c) ∗ u‖∞ ≤ ‖c‖₁‖u‖∞`, p. 50).
                    Shell::Binary => {
                        let s = scalar_from(&tape, WEIGHT_LANE + g * SRC + c);
                        let bit = s.to_u128() & 1;
                        elt_at(0, Q::from(bit as u64))
                    }
                    // "With evaluation trace, `c_{g,c,i} = c^A_{g,c,i} ∈
                    // C_{d_A,g}` is a full-ring challenge" (p. 62).
                    Shell::FullRing => ring_from(&tape, WEIGHT_LANE + g * SRC * D + c * D),
                })
                .collect()
        })
        .collect()
}

/// The schedule record every Fiat–Shamir stage re-absorbs: the seed, the depth,
/// the outgoing edge and the provisioned envelope. A transcript is a pure
/// function of what both parties already hold, so prover and verifier derive
/// identical challenges — §4.3's "a single nonce selects the complete
/// domain-separated raw-draw tape" is the same discipline.
fn absorb_schedule(tr: &mut Transcript<Shake256Xof>, sched: &Schedule) {
    tr.absorb(b"seed", sched.setup.seed());
    tr.absorb(b"delta_f", &(sched.delta_f as u64).to_le_bytes());
    tr.absorb(b"edge", sched.edge.as_bytes());
    tr.absorb(b"n_setup", &(sched.n_setup as u64).to_le_bytes());
}

/// The batch's own binding material: one digest per source, one inner image per
/// batch member.
fn absorb_batch(
    tr: &mut Transcript<Shake256Xof>,
    sources: &[Source],
    inner: &[Vec<PolyRing<Q, D>>],
) {
    for src in sources {
        tr.absorb(b"src", &src.digest);
    }
    for image in inner {
        tr.absorb(b"inner", &bytes_of(&flat_d(image, D)));
    }
}

/// The statement the two late Fiat–Shamir stages absorb: everything the level
/// transmits before the deferred setup claim — the batch's digests and images,
/// the revealed digits, the two images and the compressed payload (§4.5's
/// message order).
///
/// Bundled as a type rather than threaded as six arguments because
/// `digits_flat` and `setup_claim` are both `&[Q]` and `commitment` and
/// `energy_bytes` are both `&[u8]`: a transposed transcript compiles, moves both
/// parties' challenges identically, and so surfaces nowhere except the failing
/// sets — the one class of bug a type can prevent.
struct Statement<'a> {
    sources: &'a [Source],
    inner: &'a [Vec<PolyRing<Q, D>>],
    digits_flat: &'a [Q],
    outer: &'a [PolyRing<Q, D>],
    opening: &'a [PolyRing<Q, D_OPEN>],
    commitment: &'a [u8],
}

impl<'a> Statement<'a> {
    /// The transcript prefix both late stages extend.
    fn prefix(&self, sched: &Schedule) -> Transcript<Shake256Xof> {
        let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/akita/fs");
        absorb_schedule(&mut tr, sched);
        absorb_batch(&mut tr, self.sources, self.inner);
        tr.absorb(b"digits", &bytes_of(self.digits_flat));
        tr.absorb(b"outer", &bytes_of(&flat_d(self.outer, D)));
        tr.absorb(b"opening", &bytes_of(&flat_d_opening(self.opening)));
        tr.absorb(b"commitment", self.commitment);
        tr
    }
}

/// The setup group's ring challenge `α`, the quotient-lift base of Eq. (167)'s
/// weight, drawn from the statement's prefix.
///
/// It is drawn *before* the claim exists and the claim is absorbed *after* it:
/// §9.1's Stage 3 samples the point (`ρ_S`, and here the ring-reduction
/// challenge `α` that plays the same role in the weight) and only then "the
/// prover supplies a claimed σ_S for the final check of Stage 2" — the deferred
/// evaluation is a *response* to the challenge, so it cannot be part of its
/// preimage. The previous single-call shape absorbed a placeholder `&[]` on the
/// prover's side against the real bytes on the verifier's, so the two derived
/// different points and the honest proof failed its own `SetupGroup` check.
fn setup_alpha(sched: &Schedule, st: &Statement<'_>) -> PolyRing<Q, D> {
    let mut tr = st.prefix(sched);
    let tape = tr.challenge_bytes(64);
    // A full-ring draw: p. 50, "an evaluation-trace fold instead samples its
    // challenge in the full ring `R_{q,d_A}`".
    ring_from(&tape, ALPHA_LANE)
}

/// `ζ_pair`, drawn after every digit-inner-product claim is fixed (p. 70, above
/// Eq. 124), with the transcript extended by the setup claim it now binds.
fn pair_challenge(
    sched: &Schedule,
    st: &Statement<'_>,
    setup_claim: &[Q],
    grams: &[norm_route::PairClaim<Q>],
    energy_bytes: &[u8],
) -> Q {
    let mut tr = st.prefix(sched);
    tr.absorb(b"setup_claim", &bytes_of(setup_claim));
    for g in grams {
        tr.absorb(b"gram", &bytes_of(&[g.residue]));
    }
    tr.absorb(b"energy", energy_bytes);
    scalar_from(&tr.challenge_bytes(64), ZETA_LANE)
}

fn flat_d_opening(values: &[PolyRing<Q, D_OPEN>]) -> Vec<Q> {
    values
        .iter()
        .flat_map(|v| {
            let mut c: Vec<Q> = v.coefficients().iter().copied().collect();
            c.resize(D_OPEN, Q::ZERO);
            c
        })
        .collect()
}

/// `τ`, the range row's equality anchor of Eq. (115), one scalar per Boolean
/// variable of the witness cube. Drawn from the statement's prefix, so both
/// parties hold it before `P_base`'s claim is fixed.
fn tau_point(sched: &Schedule, st: &Statement<'_>) -> Vec<Q> {
    let mut tr = st.prefix(sched);
    let tape = tr.challenge_bytes(64);
    (0..fused::variables(sched.witness_len))
        .map(|j| scalar_from(&tape, TAU_LANE + j))
        .collect()
}

/// `η_norm`, "a fresh batching challenge" the verifier samples *after* the norm
/// proof's final evaluations are fixed (p. 70, above Eq. 126). Absorbing the
/// evaluations themselves — not just the messages that produce them — is what
/// makes them fixed: a prover cannot move `η_norm` by re-choosing a point.
fn eta_norm(
    sched: &Schedule,
    st: &Statement<'_>,
    setup_claim: &[Q],
    grams: &[norm_route::PairClaim<Q>],
    energy_bytes: &[u8],
    evals: &[Q],
) -> Q {
    let mut tr = st.prefix(sched);
    tr.absorb(b"setup_claim", &bytes_of(setup_claim));
    for g in grams {
        tr.absorb(b"gram", &bytes_of(&[g.residue]));
    }
    tr.absorb(b"energy", energy_bytes);
    tr.absorb(b"norm_evals", &bytes_of(evals));
    scalar_from(&tr.challenge_bytes(64), ETA_LANE)
}

/// Runs the verifier's half of Eq. (125) on the *transmitted* norm proof and
/// returns the point `r` it ends at together with the final evaluations Eqs.
/// (126)/(127) bind: `z̃_int(r)` on the direct route, `z̃_h(r)` for every `h < δ_f`
/// on the digit-expanded one (p. 70: "the direct proof leaves the evaluation
/// `z̃int(r)`. The digit-expanded proof leaves the digit evaluations `ẽz_h(r)`").
///
/// Both sides are entitled to these: `r` is a function of the round messages the
/// prover already sent, and the tables are the witness the recursive protocol
/// carries. Reading them off the *transmitted* proof rather than re-deriving it is
/// what makes a tampered norm message move the binding as well.
fn norm_point_and_evals(
    sched: &Schedule,
    norm_proof: &fused::FusedProof<Q>,
    group: &Group,
    grams: &[norm_route::PairClaim<Q>],
    energy_bytes: &[u8],
    s_max: u128,
    zeta_pair: Q,
) -> Option<(Vec<Q>, Vec<Q>)> {
    let segs = norm_route::segments(N_A, SEG_LEN);
    let (factors, terms, claimed) =
        norm_factors(sched, group, grams, energy_bytes, s_max, zeta_pair, &segs)?;
    let refs: Vec<&[Q]> = factors.iter().map(|f| f.as_slice()).collect();
    let trefs: Vec<&[usize]> = terms.iter().map(|t| t.as_slice()).collect();
    let mut challenger = fused::FsDegChallenger::<Shake256Xof, Q>::new(b"akita/norm");
    let (r, _run) = fused::verify::<Q>(norm_proof, claimed, &mut challenger)?;
    let values: Vec<Q> = refs.iter().map(|t| fused::fold_table(t, &r)).collect();
    // The direct sum-check's single factor is `z_int`; the expanded one lists its
    // `N_pair` scaled indicators first and the `delta_f` digit planes after.
    let evals = match sched.route_for(s_max) {
        NormRoute::Direct => vec![values[0]],
        NormRoute::DigitExpanded => {
            values[norm_route::n_pair(segs.len(), sched.delta_f)..].to_vec()
        }
        NormRoute::Coefficient => Vec::new(),
    };
    Some((r, evals))
}

/// Eq. (128)'s `P_base`: the final range leaf's equality-anchored summand over the
/// witness cube, `eq(τ, x) · Π_{k < b*/2} (s(x) − k(k+1))` with `s = w(w+1)`
/// (Eq. 115, Remark 6.1's halved predicate). Its honest claim is `0`, because the
/// predicate vanishes at every digit *and* at every zero-padding cell — the
/// alphabet's root `k = 0` is `0` itself — so no indicator row is needed to make
/// the padded cube sum right.
fn range_row(witness: &[Q], tau: &[Q], base_star: u64) -> fused::Summand<Q> {
    let mut factors = vec![fold_geom::eq_table(tau, tau.len())];
    for k in 0..base_star / 2 {
        let image = Q::from(k * (k + 1));
        factors.push(
            witness
                .iter()
                .map(|w| alphabet::derived(w) - image)
                .collect::<Vec<Q>>(),
        );
    }
    let term: Vec<usize> = (0..factors.len()).collect();
    fused::Summand {
        factors,
        terms: vec![term],
        claimed: Q::ZERO,
    }
}

/// Everything Eq. (128) needs, assembled from src capabilities only: `C_bind` and
/// the `π`-addressed weight table from [`norm_route::pi_binding`], the range row,
/// and their fusion. `None` when the norm proof's shape does not match the route,
/// which is a refusal rather than a pass.
fn binding_statements(
    sched: &Schedule,
    norm_proof: &fused::FusedProof<Q>,
    group: &Group,
    grams: &[norm_route::PairClaim<Q>],
    energy_bytes: &[u8],
    s_max: u128,
    zeta_pair: Q,
    map: &DigitMap,
    witness: &[Q],
    st: &Statement<'_>,
    setup_claim: &[Q],
) -> Option<(fused::Summand<Q>, norm_route::PiBinding<Q>)> {
    let (r, evals) = norm_point_and_evals(
        sched,
        norm_proof,
        group,
        grams,
        energy_bytes,
        s_max,
        zeta_pair,
    )?;
    let eta = eta_norm(sched, st, setup_claim, grams, energy_bytes, &evals);
    let binding =
        norm_route::pi_binding(map, &r, eta, sched.base, sched.route, &evals, witness.len())
            .ok()?;
    let bind = fused::Summand {
        factors: vec![binding.weights.clone(), witness.to_vec()],
        terms: vec![vec![0, 1]],
        claimed: binding.claim,
    };
    let combined = fused::fuse(&range_row(witness, &tau_point(sched, st), sched.base_star), &bind)?;
    Some((combined, binding))
}

/// Eq. (104) + Eq. (105) + Eq. (107): fold the batch, then split the response
/// into digit planes in native-block order at this role's ring dimension.
///
/// The batching weights are **ring elements**, not scalars. Eq. (104)'s own
/// gloss (p. 62) fixes it: "`c_{g,c,i} ∈ C_{d_car,g}` and `c^A_{g,c,i} =
/// ι_g(c_{g,c,i})` with coefficient packing. With evaluation trace,
/// `c_{g,c,i} = c^A_{g,c,i} ∈ C_{d_A,g}` is a full-ring challenge", and the
/// `s_{g,c,i}` it multiplies are the ring elements of block `i` (Table 3, p. 46:
/// `s_i` the gadget decomposition of block `i`, `t_i = A s_i ∈ R^{n_A}_{q,d_A}`).
/// So each summand of `z_g = Σ_{c,i} c^A_{g,c,i} s_{g,c,i}` is a *ring* product
/// and `z_g` is a vector of `m_A` ring elements — the same length as the sources
/// it folds (`N_A = m_A d_A` base-field coordinates, `M_A` above) — so the
/// accumulator is ring elements and flattening to `N_A` field coordinates
/// happens only afterwards, for the digit split. A flat `Vec<Q>` accumulator
/// could not even hold the sum — which is what the type error at the `+=` said.
/// The reference implementation agrees: its fold-challenge dispatch draws one
/// `d_a`-dimensional challenge per (group, claim, block)
/// (`draw_group_fold_challenges`, `akita-types`).
///
/// The same reading is forced by [`Check::Relation`] itself: it demands
/// `A z_g = Σ_c c^A_{g,c}(A s_c)`, which is exactly the statement that the fold
/// is *R*-linear, and that only holds if `Σ` here is the ring-linear one.
fn build_group(sched: &Schedule, sources: &[Source], weights: &[PolyRing<Q, D>]) -> Group {
    let mut acc = vec![zero_elt(); M_A];
    for (c, w) in weights.iter().enumerate() {
        // `sources[c].table` is `(s_{g,c,i})_{i ∈ [B]}`: `B = M_A` ring elements.
        debug_assert_eq!(sources[c].table.len(), acc.len(), "one column per block");
        for (slot, v) in sources[c].table.iter().enumerate() {
            acc[slot] = acc[slot].clone() + w.clone() * v.clone();
        }
    }
    // Split at the full field depth so `split_native`'s exactness guard is the
    // real one, then take the `delta_f` planes the schedule certifies.
    let native = alphabet::split_native(&flat_d(&acc, D), D, 1, sched.base, DELTA_FULL);
    let planes = read_planes(&native, DELTA_FULL);
    let coords = norm_route::integer_coordinates(&planes[..sched.delta_f], sched.base);
    Group {
        response: acc,
        planes: planes[..sched.delta_f].to_vec(),
        coords,
    }
}

/// Read the digit planes out of Eq. (107)'s order: item `j`, digit `u`,
/// coefficient `k` at `(j·depth + u)·d + k`.
fn read_planes(native: &[Q], depth: usize) -> Vec<Vec<i64>> {
    assert!(depth >= 1 && native.len() % depth == 0, "plane-major layout");
    let items = native.len() / (depth * D);
    let mut out = vec![Vec::with_capacity(items * D); depth];
    for j in 0..items {
        for u in 0..depth {
            for k in 0..D {
                out[u].push(centered(&native[(j * depth + u) * D + k]));
            }
        }
    }
    out
}

/// The plane-major digit vector the outer matrix consumes (Eq. 109's order).
fn digits_of(groups: &[Group]) -> Vec<Q> {
    groups
        .iter()
        .flat_map(|g| g.planes.iter().flatten().map(|&d| of_i64(d)))
        .collect()
}

/// §4.5's compressed payload: `L_F = L_H = 2` chain links over the outer and
/// opening images, 64 bytes each.
fn commitment_payload(outer: &[PolyRing<Q, D>], opening: &[PolyRing<Q, D_OPEN>]) -> Vec<u8> {
    let mut out = Vec::with_capacity(COMMIT_BYTES);
    for (tag, stage) in [
        (b"F".as_slice(), bytes_of(&flat_d(outer, D))),
        (b"H".as_slice(), bytes_of(&flat_d_opening(opening))),
    ] {
        let head = digest(&[tag, &stage]);
        for link in 0..2 {
            out.extend_from_slice(&digest(&[tag, &head, &[link]]));
        }
    }
    out
}

/// Eq. (167)'s delegated setup value, on the direct column this example runs
/// (§9.1: "Without offloading, the verifier evaluates (167) by scanning the
/// active prefix. With offloading, the prover supplies a claimed σ_S"):
///
/// ```text
/// σ_S := Σ_{p < 2^ν_S} S♭(p) ω_setup(p)          (167)
/// ```
///
/// over the canonical padded source `S♭` (`S_p` for `p < N_active`, `0` beyond,
/// so the prefix *is* the `N_active = max_I n_I m_I d_I` of Eq. 173 that the
/// schedule provisioned the `N_setup = 2^ceil(log2 N_active)` envelope for). The
/// weight keeps the one factor a single view contributes — "a view of dimension
/// `d` gives flat coefficient `p` the quotient-lift factor `α^{p mod d}`"
/// (p. 83, above Eq. 167) — because the row-batching and projection kernels of
/// Eqs. (161)/(150) need a fused sum-check output point, which one level does
/// not have. `σ_S` is a ring element of `R_{q,D}`, so the claim is its `D`
/// base-field coordinates: one per ring coefficient.
fn setup_evaluation(sched: &Schedule, alpha: PolyRing<Q, D>) -> Vec<Q> {
    let padded = SetupStream::pad_to_boolean::<Q>(&sched.setup.coeffs::<Q>(sched.n_active));
    debug_assert_eq!(padded.len(), sched.n_setup, "the envelope is the Boolean domain");
    // `α^0 … α^(d-1)`: the weight's period is the view's own dimension.
    let mut powers = Vec::with_capacity(D);
    let mut cur = one_elt();
    for _ in 0..D {
        powers.push(cur.clone());
        cur *= alpha.clone();
    }
    let mut acc = zero_elt();
    for (p, coeff) in padded.iter().enumerate() {
        acc += powers[p % D].clone() * elt_at(0, *coeff);
    }
    flat_d(&[acc], D)
}

/// The recursive-witness cells of the level: the revealed digit planes of both
/// groups, padded to the Boolean cube Eq. (128)'s sum-check runs over. The padding
/// is zeros, which is what lets a *public* weight table over the same cube carry
/// Eq. (126)/(127)'s right-hand side without changing its Boolean sum.
fn padded_witness(digits_flat: &[Q], len: usize) -> Vec<Q> {
    let mut witness = digits_flat.to_vec();
    witness.resize(len, Q::ZERO);
    witness
}

/// The scheduled address map `π` this level declares: group `0`'s response digits,
/// plane-major in the witness (`digits_of`'s order), starting at cell `0`.
fn scheduled_map(sched: &Schedule) -> DigitMap {
    DigitMap::plane_major(N_A, sched.delta_f, 0)
}

/// The whole level, proven.
fn prove(sched: &Schedule, s_max: u128) -> Proof {
    let salt = *sched.setup.seed();
    let sources: Vec<Source> = (0..SRC)
        .map(|i| {
            let table = short_table(&salt, i);
            let digest = digest(&[b"src", &bytes_of(&flat_d(&table, D))]);
            Source { table, digest }
        })
        .collect();
    let inner: Vec<Vec<PolyRing<Q, D>>> = sources
        .iter()
        .map(|s| sched.a.matvec(&s.table).expect("A shape"))
        .collect();

    let weights = group_weights(sched, &sources, &inner);
    // C12's honest path: the certified `kappa_1` really does bound the draws this
    // schedule squeezed, which is the hypothesis Eq. (79) and Corollary 10.26 are
    // stated under. Checked here, at the point the prover can see them all.
    for group in &weights {
        for c in group {
            let (l1, _) = fold_geom::norms(&c.coefficients().iter().copied().collect::<Vec<_>>());
            assert!(
                u128::from(l1) <= u128::from(sched.kappa_1),
                "a challenge outside its certified family"
            );
        }
    }
    let groups: Vec<Group> = (0..N_GROUPS)
        .map(|g| build_group(sched, &sources, &weights[g]))
        .collect();

    let digits_flat = digits_of(&groups);
    let outer = sched.b.matvec(&unflat_d(&digits_flat, D)).expect("B shape");
    // The opening digits live at `d_open`: the same witness, another role ring.
    let open_digits =
        alphabet::split_native(&flat_d(&groups[0].response, D), D_OPEN, D / D_OPEN, sched.base, DELTA_FULL);
    debug_assert_eq!(open_digits.len(), OPEN_ELEMENTS * D_OPEN);
    let opening = sched
        .d
        .matvec(&open_digits.chunks(D_OPEN).map(|c| PolyRing::from_coefficients(c.to_vec())).collect::<Vec<_>>())
        .expect("D shape");
    let commitment = commitment_payload(&outer, &opening);

    let st = Statement {
        sources: &sources,
        inner: &inner,
        digits_flat: &digits_flat,
        outer: &outer,
        opening: &opening,
        commitment: &commitment,
    };
    let alpha = setup_alpha(sched, &st);
    let setup_claim = setup_evaluation(sched, alpha);

    // --- Eq. (118)'s certificate, and only on the routes that send it ----------
    let (energy_bytes, grams, norm_proof) = if sched.certifies() {
        let energy = exact_l2::integer_energy(&groups[0].planes, sched.base).expect("fits");
        let energy_bytes = exact_l2::encode_energy(s_max, energy);
        let segs = norm_route::segments(N_A, SEG_LEN);
        let grams = match sched.route_for(s_max) {
            NormRoute::Direct => Vec::new(),
            NormRoute::DigitExpanded => norm_route::digit_pair_claims(
                &groups[0].planes,
                &segs,
                &sched.digit_bounds(),
                Q::MODULUS,
            )
            .expect("the schedule segments the response so Eq. (122) holds"),
            NormRoute::Coefficient => Vec::new(),
        };
        let zeta_pair = pair_challenge(sched, &st, &setup_claim, &grams, &energy_bytes);
        let (norm_proof, _claimed) =
            norm_stage(sched, &groups[0], &grams, &energy_bytes, s_max, zeta_pair);
        (energy_bytes, grams, norm_proof)
    } else {
        (Vec::new(), Vec::new(), empty_proof())
    };

    // --- Eqs. (126)-(128): bind those evaluations to the witness through pi ----
    let witness = padded_witness(&digits_flat, sched.witness_len);
    let map = scheduled_map(sched);
    let (pi_cells, bind_proof) = if sched.certifies() {
        let zeta_pair = pair_challenge(sched, &st, &setup_claim, &grams, &energy_bytes);
        let (combined, _binding) = binding_statements(
            sched,
            &norm_proof,
            &groups[0],
            &grams,
            &energy_bytes,
            s_max,
            zeta_pair,
            &map,
            &witness,
            &st,
            &setup_claim,
        )
        .expect("the honest level's norm proof has the shape its route declares");
        let mut challenger = fused::FsDegChallenger::<Shake256Xof, Q>::new(b"akita/bind");
        let proof = combined.prove(&mut challenger);
        (map.cells().to_vec(), proof)
    } else {
        (Vec::new(), empty_proof())
    };

    // --- the radius the descriptor asks A to be provisioned at ----------------
    // Declared in the coordinate units C12 compares against: an `l2` radius of
    // `eta^2` prices at `ceil(sqrt(eta^2))`, never at the square.
    let earned = sched
        .earned_radius(s_max)
        .expect("every route derives at least the Eq. (79) radius");
    debug_assert!(
        sched.coefficient_radius().is_ok(),
        "Eq. (79) must be derivable on any route"
    );

    Proof {
        sources,
        inner,
        groups,
        outer,
        opening,
        commitment,
        setup_claim,
        energy_bytes,
        grams,
        norm_proof,
        digits_flat,
        pi_cells: pi_cells.to_vec(),
        bind_proof,
        declared_radius: earned
            .coordinate_bound()
            .expect("the earned radius is priceable"),
    }
}

/// A level's proof of nothing: the shape a route that sends no such message
/// carries, and one Figure 2's verifier always refuses.
fn empty_proof() -> fused::FusedProof<Q> {
    fused::FusedProof {
        degree: 0,
        variables: 0,
        rounds: Vec::new(),
    }
}

/// The norm sum-check, in the shape Eq. (125) prescribes.
///
/// Direct: `P_norm(x) := z_int(x)²`, `C_norm := E_resp` (Eq. 120).
/// Expanded: `P_norm(x) := Σ_{t,h≤k} ζ_pair^idx(t,h,k) 1_{I_t}(x) z_h(x) z_k(x)`,
/// `C_norm := Σ_{t,h≤k} ζ_pair^idx p_{t,h,k}` — with each triple's scalar folded
/// into its own indicator table, which is how a sum-of-products summand carries
/// per-term constants, so one sum-check carries all `N_pair` claims.
fn norm_stage(
    sched: &Schedule,
    group: &Group,
    grams: &[norm_route::PairClaim<Q>],
    energy_bytes: &[u8],
    s_max: u128,
    zeta_pair: Q,
) -> (fused::FusedProof<Q>, Vec<Vec<Q>>) {
    let segs = norm_route::segments(N_A, SEG_LEN);
    let zint = norm_route::pad_to_boolean::<Q>(&group.coords, 1 << MU);
    let (factors, terms, claimed, degree) = match sched.route_for(s_max) {
        NormRoute::Direct => {
            let energy = exact_l2::decode_energy(s_max, energy_bytes).unwrap_or(0);
            (
                vec![zint.clone()],
                vec![vec![0, 0]],
                Q::from((energy % u128::from(Q::MODULUS)) as u64),
                2,
            )
        }
        NormRoute::DigitExpanded => {
            let plane_tables: Vec<Vec<Q>> = group
                .planes
                .iter()
                .map(|p| {
                    let mut t: Vec<Q> = p.iter().map(|&d| of_i64(d)).collect();
                    t.resize(1 << MU, Q::ZERO);
                    t
                })
                .collect();
            let order = norm_route::pair_order(segs.len(), sched.delta_f);
            let mut indicators: Vec<Vec<Q>> = Vec::with_capacity(order.len());
            for (i, &(t, _, _)) in order.iter().enumerate() {
                let mut scale = Q::ONE;
                for _ in 0..i {
                    scale *= zeta_pair;
                }
                let mut table = vec![Q::ZERO; 1 << MU];
                for x in segs[t].0..segs[t].1 {
                    table[x] = scale;
                }
                indicators.push(table);
            }
            let base_f = indicators.len();
            let factors: Vec<Vec<Q>> = indicators.into_iter().chain(plane_tables).collect();
            let terms: Vec<Vec<usize>> = order
                .iter()
                .enumerate()
                .map(|(i, &(_, h, k))| vec![i, base_f + h, base_f + k])
                .collect();
            // C_norm is built from the transmitted claims, not from the tables.
            let claimed = order
                .iter()
                .enumerate()
                .map(|(i, _)| {
                    let mut scale = Q::ONE;
                    for _ in 0..i {
                        scale *= zeta_pair;
                    }
                    scale * grams[i].residue
                })
                .fold(Q::ZERO, |a, b| a + b);
            (factors, terms, claimed, 3)
        }
        // unreachable from `prove`: the coefficient route never asks for this
        // stage, and `route_for` only ever returns the two Euclidean proofs.
        NormRoute::Coefficient => (Vec::new(), Vec::new(), Q::ZERO, 2),
    };
    let refs: Vec<&[Q]> = factors.iter().map(|f| f.as_slice()).collect();
    let trefs: Vec<&[usize]> = terms.iter().map(|t| t.as_slice()).collect();
    let mut challenger = fused::FsDegChallenger::<Shake256Xof, Q>::new(b"akita/norm");
    let proof = fused::prove::<Q>(&refs, &trefs, degree, claimed, &mut challenger);
    (proof, factors)
}

/// A short source table: coefficients in `{0, 1}`.
fn short_table(salt: &[u8; 32], i: usize) -> Vec<PolyRing<Q, D>> {
    (0..M_A)
        .map(|j| {
            let mut coeffs = Vec::with_capacity(D);
            for k in 0..D {
                let s = scalar_from(salt, i * 100 + j * 10 + k);
                coeffs.push(Q::from((s.to_u128() & 1) as u64));
            }
            PolyRing::from_coefficients(coeffs)
        })
        .collect()
}

/// Every check, run without short-circuiting. Under Fiat–Shamir each message is
/// absorbed before the next challenge, so one tamper cascades and fails many
/// checks; asserting the whole set is the only attribution that means anything.
fn failing(sched: &Schedule, s_max: u128, proof: &Proof) -> BTreeSet<Check> {
    let mut bad = BTreeSet::new();
    let route = sched.route_for(s_max);
    let weights = group_weights(sched, &proof.sources, &proof.inner);
    let st = Statement {
        sources: &proof.sources,
        inner: &proof.inner,
        digits_flat: &proof.digits_flat,
        outer: &proof.outer,
        opening: &proof.opening,
        commitment: &proof.commitment,
    };
    let alpha = setup_alpha(sched, &st);
    let zeta_pair = pair_challenge(
        sched,
        &st,
        &proof.setup_claim,
        &proof.grams,
        &proof.energy_bytes,
    );

    // C1 Relation: the fold commutes with the commitment, so the response image
    // must equal the same combination of the batch members' inner images.
    for (g, group) in proof.groups.iter().enumerate() {
        let want = sum_scaled(&weights[g], &proof.inner);
        match sched.a.matvec(&group.response) {
            Ok(got) => {
                if got != want {
                    bad.insert(Check::Relation);
                }
            }
            Err(_) => {
                bad.insert(Check::Relation);
            }
        }
    }

    // C2 Recomposition: z = G_{b,m_A} ẑ (Eq. 105), and the planes must be the
    // ones the gate is asked about.
    for group in &proof.groups {
        if group.coords != norm_route::integer_coordinates(&group.planes, sched.base) {
            bad.insert(Check::Recompose);
        }
        if !exact_l2::planes_reduce_to(&group.planes, &flat_d(&group.response, D), sched.base) {
            bad.insert(Check::Recompose);
        }
    }
    if proof.digits_flat != digits_of(&proof.groups) {
        bad.insert(Check::Recompose);
    }

    // C3 Range: the degree-halved predicate of Eq. (114), not a bounds compare.
    for group in &proof.groups {
        for plane in &group.planes {
            for &d in plane {
                if alphabet::halved_vanishing(&of_i64(d), sched.base_star) != Q::ZERO {
                    bad.insert(Check::Range);
                }
            }
        }
    }

    // C5 Canonical decoding of E_resp (Eq. 118), C4 the fused norm sum-check of
    // Eq. (125), and C6 the exact-norm gate: all three read Eq. (118)'s
    // certificate, which the coefficient route never sends. Skipping them there is
    // not a weakening — the route's whole point (p. 64) is that the radius comes
    // from the digit ranges alone, so there is no claim to decode or prove.
    if sched.certifies() {
        let decoded = exact_l2::decode_energy(s_max, &proof.energy_bytes);
        if decoded.is_err() {
            bad.insert(Check::NormCanonical);
        }

        // C4 The fused norm sum-check: rebuild the factors the verifier is entitled
        // to (indicators and `ζ_pair` are public, the digit tables are revealed) and
        // require the running claim to close at `summand_at`.
        {
            let segs = norm_route::segments(N_A, SEG_LEN);
            let group = &proof.groups[0];
            let built =
                norm_factors(sched, group, &proof.grams, &proof.energy_bytes, s_max, zeta_pair, &segs);
            match built {
                None => {
                    bad.insert(Check::NormSumcheck);
                }
                Some((factors, terms, claimed)) => {
                    let refs: Vec<&[Q]> = factors.iter().map(|f| f.as_slice()).collect();
                    let trefs: Vec<&[usize]> = terms.iter().map(|t| t.as_slice()).collect();
                    let mut challenger =
                        fused::FsDegChallenger::<Shake256Xof, Q>::new(b"akita/norm");
                    match fused::verify::<Q>(&proof.norm_proof, claimed, &mut challenger) {
                        None => {
                            bad.insert(Check::NormSumcheck);
                        }
                        Some((r, run)) => {
                            let values: Vec<Q> =
                                refs.iter().map(|t| fused::fold_table(t, &r)).collect();
                            if fused::summand_at(&values, &trefs) != run {
                                bad.insert(Check::NormSumcheck);
                            }
                        }
                    }
                }
            }
        }

        // C6 The exact-norm gate on the admitted route, decided twice: by the
        // protocol statement in `pcs::norm_route` and by the routed gate in
        // `shortness::exact_l2`.
        {
            let group = &proof.groups[0];
            let segs = norm_route::segments(N_A, SEG_LEN);
            let energy = decoded.unwrap_or(u128::MAX);
            let statement = match route {
                NormRoute::Direct => norm_route::check_direct(
                    &group.coords,
                    energy,
                    s_max,
                    sched.u_dir(),
                    Q::MODULUS,
                ),
                NormRoute::DigitExpanded => norm_route::check_digit_expanded(
                    &proof.grams,
                    &segs,
                    &sched.digit_bounds(),
                    sched.base,
                    energy,
                    s_max,
                ),
                NormRoute::Coefficient => unreachable!("guarded by certifies()"),
            };
            if statement.is_err() {
                bad.insert(Check::NormBound);
            }
            let routed = exact_l2::exact_l2_gate_routed(
                &flat_d(&group.response, D),
                &group.planes,
                energy,
                s_max,
                sched.base,
                SEG_LEN,
                &sched.digit_bounds(),
            );
            let agrees = match (route, routed) {
                (NormRoute::Direct, Ok((_, Route::Direct))) => true,
                (NormRoute::DigitExpanded, Ok((_, Route::DigitGram))) => true,
                _ => false,
            };
            if !agrees {
                bad.insert(Check::NormBound);
            }
        }
    }

    // C7 The offloaded edge's setup group: the deferred scan's claim must be
    // Eq. (167)'s value for the prefix this schedule is entitled to read, at the
    // point the transcript fixes, and the envelope must contain the matrices it
    // describes.
    {
        let want = setup_evaluation(sched, alpha);
        if want != proof.setup_claim {
            bad.insert(Check::SetupGroup);
        }
        if SetupStream::padded_len(sched.n_active) != sched.n_setup || sched.n_active > sched.n_setup {
            bad.insert(Check::SetupGroup);
        }
        // ... and the envelope really does contain every admitted view: each
        // view reads `n_I m_I d_I` flat coefficients of `S`, so an
        // under-provisioned `N_setup` is refused here rather than by a panic in
        // `setup_evaluation`'s indexing (Eq. 65, Eq. 173).
        if sched
            .views
            .iter()
            .any(|v| v.rows * v.cols * v.dim > sched.n_setup)
        {
            bad.insert(Check::SetupGroup);
        }
        // An offloaded edge "produces (S_j, W_{j+1}) and requires the successor
        // to check both groups" — so a witness group must exist to be checked.
        if sched.edge == "OffloadedSetup" && proof.groups.len() != N_GROUPS {
            bad.insert(Check::SetupGroup);
        }
    }

    // C8 The compressed commitment binds its payload, and is 128 bytes.
    if proof.commitment.len() != COMMIT_BYTES
        || proof.commitment != commitment_payload(&proof.outer, &proof.opening)
    {
        bad.insert(Check::Commitment);
    }
    // ... including that the images it hashes are the ones the schedule produces.
    let outer_want = sched
        .b
        .matvec(&unflat_d(&proof.digits_flat, D))
        .unwrap_or_else(|_| vec![elt_at(0, Q::ZERO)]);
    if outer_want != proof.outer {
        bad.insert(Check::Commitment);
    }

    // C9 Batch binding: each source's digest binds its own table.
    for src in &proof.sources {
        if src.digest != digest(&[b"src", &bytes_of(&flat_d(&src.table, D))]) {
            bad.insert(Check::BatchBinding);
        }
    }
    // ... and each transmitted inner image is the Ajtai image of *that* source,
    // recomputed from the table the loop above just bound (`t_c := A s_c`,
    // Table 3 p. 46; `Proof::inner` is documented as one image per batch
    // member). The digest binds the tables, but nothing else in the proof ties
    // `inner` to them: `inner` enters only as the *input* of the batch relation
    // C1 and as transcript randomness, so without this recomputation a prover
    // could ship images of other vectors and still close C1 on them. `A` maps
    // `m_A ↦ n_A`, so the recomputation is compared against the image directly
    // — an image is not itself an `A` input.
    for (c, src) in proof.sources.iter().enumerate() {
        let want = sched.a.matvec(&src.table).expect("A shape");
        match proof.inner.get(c) {
            Some(image) if *image == want => {}
            _ => {
                bad.insert(Check::BatchBinding);
            }
        }
    }

    // C10 Eq. (117): centered reduction cannot increase the norm. A squared norm
    // that leaves `u128` is reported as `EnergyUndecidable`, not as `0`: the old
    // `unwrap_or(0)` made an undecidable group *harder* to reject, since the
    // comparison it feeds is `ring > exact`.
    for group in &proof.groups {
        let ring = norm_route::reduced_energy(&flat_d(&group.response, D));
        let exact =
            norm_route::exact_energy(&norm_route::integer_coordinates(&group.planes, sched.base));
        match (ring, exact) {
            (Ok(ring), Ok(exact)) => {
                if ring > exact {
                    bad.insert(Check::EnergyDirection);
                }
            }
            _ => {
                bad.insert(Check::EnergyUndecidable);
            }
        }
    }

    // C11 Eqs. (126)-(128): the norm proof's final evaluations must reconstruct
    // from the pi-addressed cells of the committed witness, and the fused
    // combined sum-check must close. Three conjuncts, one named check, because
    // they are one statement's premise (Lemma 6.3's "the map pi is injective with
    // the scheduled image"), its printed equation, and the proof of that equation.
    //
    // pi is admitted on its structural property alone and never compared to the
    // honest map: Eqs. (126)-(127) are what tie a *declared* map to the witness,
    // so a schedule that also demanded the canonical addresses would leave the
    // equation itself untestable. It is not demanded, and the permutation tamper
    // below trips this check on its own.
    if sched.certifies() {
        let witness = padded_witness(&proof.digits_flat, sched.witness_len);
        let map = match DigitMap::admit(N_A, sched.delta_f, 0, &proof.pi_cells) {
            Ok(map) => Some(map),
            Err(_) => {
                bad.insert(Check::NormBinding);
                None
            }
        };
        if let Some(map) = map {
            let built = binding_statements(
                sched,
                &proof.norm_proof,
                &proof.groups[0],
                &proof.grams,
                &proof.energy_bytes,
                s_max,
                zeta_pair,
                &map,
                &witness,
                &st,
                &proof.setup_claim,
            );
            match built {
                None => {
                    bad.insert(Check::NormBinding);
                }
                Some((combined, binding)) => {
                    // Eq. (126) / Eq. (127) as printed, evaluated directly.
                    if norm_route::check_pi_identity(&binding, &witness).is_err() {
                        bad.insert(Check::NormBinding);
                    }
                    // Eq. (128): one sum-check for the range row and the binding.
                    let mut challenger =
                        fused::FsDegChallenger::<Shake256Xof, Q>::new(b"akita/bind");
                    if !combined.accepts(&proof.bind_proof, &mut challenger) {
                        bad.insert(Check::NormBinding);
                    }
                }
            }
        }
    }

    // C12 The radius the descriptor asks `A` to be provisioned at, re-derived from
    // what this level's route certified: Eq. (113) + Eq. (79) always, Corollary
    // 10.26's `64 Gamma^2 S_max` additionally on a route that certifies Eq. (118),
    // and the contract checked against `A`'s own provisioned view (p. 56). Upward
    // rounding is legal (p. 108), a declaration below the earned radius is not.
    match sched.earned_radius(s_max) {
        None => {
            bad.insert(Check::Radius);
        }
        Some(earned) => {
            let declared = DeclaredRadius {
                declared: proof.declared_radius,
                earned,
            };
            if declared
                .check(&CoreSvpEstimator, &sched.msis_a(), &CONTRACT)
                .is_err()
            {
                bad.insert(Check::Radius);
            }
        }
    }

    bad
}

/// `Σ_c c^A_{g,c} t_c`, the right-hand side of the relation check: the same
/// ring-linear combination [`build_group`] applies to the sources, applied to
/// their images (Eq. 104's weights are ring elements, p. 62). Each `t_c` is an
/// `n_A`-vector of ring elements (Table 3), so the result is one too.
fn sum_scaled(weights: &[PolyRing<Q, D>], inner: &[Vec<PolyRing<Q, D>>]) -> Vec<PolyRing<Q, D>> {
    let n = inner.first().map(|t| t.len()).unwrap_or(0);
    let mut acc = vec![zero_elt(); n];
    for (c, w) in weights.iter().enumerate() {
        match inner.get(c) {
            Some(t) if t.len() == n => {
                for (slot, v) in t.iter().enumerate() {
                    acc[slot] = acc[slot].clone() + w.clone() * v.clone();
                }
            }
            // A ragged or short batch has no well-defined image sum: return a
            // length no `matvec` output can have, so the relation refuses.
            _ => return vec![zero_elt(); n + 1],
        }
    }
    acc
}

/// The verifier's reconstruction of Eq. (125)'s summand, or `None` when its
/// shape cannot be formed (a mis-sized Gram list, a dropped segment).
fn norm_factors(
    sched: &Schedule,
    group: &Group,
    grams: &[norm_route::PairClaim<Q>],
    energy_bytes: &[u8],
    s_max: u128,
    zeta_pair: Q,
    segs: &[(usize, usize)],
) -> Option<(Vec<Vec<Q>>, Vec<Vec<usize>>, Q)> {
    let zint = norm_route::pad_to_boolean::<Q>(&group.coords, 1 << MU);
    match sched.route_for(s_max) {
        NormRoute::Direct => {
            if !grams.is_empty() {
                return None;
            }
            let energy = exact_l2::decode_energy(s_max, energy_bytes).ok()?;
            Some((
                vec![zint],
                vec![vec![0, 0]],
                Q::from((energy % u128::from(Q::MODULUS)) as u64),
            ))
        }
        NormRoute::DigitExpanded => {
            let order = norm_route::pair_order(segs.len(), sched.delta_f);
            if order.len() != grams.len() {
                return None;
            }
            let plane_tables: Vec<Vec<Q>> = group
                .planes
                .iter()
                .map(|p| {
                    let mut t: Vec<Q> = p.iter().map(|&d| of_i64(d)).collect();
                    t.resize(1 << MU, Q::ZERO);
                    t
                })
                .collect();
            let mut indicators: Vec<Vec<Q>> = Vec::with_capacity(order.len());
            for (i, &(t, _, _)) in order.iter().enumerate() {
                let mut scale = Q::ONE;
                for _ in 0..i {
                    scale *= zeta_pair;
                }
                let mut table = vec![Q::ZERO; 1 << MU];
                for x in segs[t].0..segs[t].1 {
                    table[x] = scale;
                }
                indicators.push(table);
            }
            let base_f = indicators.len();
            let factors: Vec<Vec<Q>> = indicators.into_iter().chain(plane_tables).collect();
            let terms: Vec<Vec<usize>> = order
                .iter()
                .enumerate()
                .map(|(i, &(_, h, k))| vec![i, base_f + h, base_f + k])
                .collect();
            let claimed = order
                .iter()
                .enumerate()
                .map(|(i, _)| {
                    let mut scale = Q::ONE;
                    for _ in 0..i {
                        scale *= zeta_pair;
                    }
                    scale * grams[i].residue
                })
                .fold(Q::ZERO, |a, b| a + b);
            Some((factors, terms, claimed))
        }
        // p. 64's coefficient route sends no Eq. (118) proof, so there is no
        // Eq. (125) summand to form: refusing is the honest answer, and C4 is not
        // run on that route at all.
        NormRoute::Coefficient => None,
    }
}

fn set(items: &[Check]) -> BTreeSet<Check> {
    items.iter().copied().collect()
}

/// The measured failing set of one tamper case, which is route-dependent.
///
/// Two structural differences between the routes, neither incidental:
///
/// * Eq. (120)'s direct sum-check has one factor, `z_int`, and its claim is
///   `E_resp`, so neither reads `ζ_pair`, and a message that moves only `ζ_pair` —
///   the commitment, either image, the setup claim, all absorbed before it — cannot
///   move [`Check::NormSumcheck`] there. Eq. (125)'s expanded sum-check scales every
///   Gram indicator by a power of `ζ_pair` and does move. That is why the direct arm
///   of cases 7/9/12/14 has no `NormSumcheck` and the expanded arm does.
/// * The coefficient route sends neither certificate, so on its arm every case that
///   touches an `E_resp` or a sum-check message is skipped as not applicable, and
///   only the witness-, transcript- and statement-level tampers remain.
///
/// Whether a perturbation lands on which side of Eq. (117)'s inequality
/// `‖z‖² ≤ E_int(ẑ)` is schedule-dependent, so [`Check::EnergyDirection`]'s
/// appearances below are measured rather than reasoned about. And since Eqs.
/// (126)–(127) *consume* the norm proof's final evaluations, a tamper that moves
/// those evaluations or the witness they address moves [`Check::NormBinding`] too:
/// that is the equation doing its job, not a Fiat–Shamir cascade.
///
/// Every set is what the run prints, not what intuition suggests — under
/// Fiat–Shamir no tamper isolates one check, so a guessed set is worthless.
fn measured(
    sched: &Schedule,
    direct: &[Check],
    expanded: &[Check],
    coefficient: &[Check],
) -> BTreeSet<Check> {
    set(match sched.route {
        NormRoute::Direct => direct,
        NormRoute::DigitExpanded => expanded,
        NormRoute::Coefficient => coefficient,
    })
}

/// Tamper cases. Each mutates exactly one message component, and each carries
/// the exact set `failing` is asserted to return for it (see [`measured`]).
/// `run` asserts the set exactly, then audits that every check appears in some
/// set — which is what proves none of them is dead code.
///
/// Cases 1–10 and 19 apply on every route; 11–18 move a message that only the two
/// Euclidean routes send, so they are skipped where there is nothing to move.
fn tampers(
    sched: &Schedule,
    proof: &Proof,
    s_max: u128,
) -> Vec<(&'static str, Proof, BTreeSet<Check>)> {
    let mut out: Vec<(&'static str, Proof, BTreeSet<Check>)> = Vec::new();
    let none: &[Check] = &[];

    // 1. A response coordinate of the *setup* group changed: the digits no
    //    longer recompose it and the batch relation moves.
    let mut p = proof.clone();
    p.groups[1].response[0] = p.groups[1].response[0].clone() + one_elt();
    out.push((
        "false response coordinate",
        p,
        measured(
            sched,
            &[Check::Relation, Check::Recompose, Check::EnergyDirection],
            &[Check::Relation, Check::Recompose],
            &[Check::Relation, Check::Recompose],
        ),
    ));

    // 2. One digit of one plane pushed outside A_{b*} = {-4..3}.
    let mut p = proof.clone();
    p.groups[0].planes[0][0] += 4;
    out.push((
        "digit pushed outside A_b*",
        p,
        measured(
            sched,
            &[Check::Recompose, Check::Range, Check::NormBound],
            &[
                Check::Recompose,
                Check::Range,
                Check::NormSumcheck,
                Check::NormBound,
                Check::EnergyDirection,
                // C11 moves here but not on the direct arm: only the expanded route
                // rebuilds `E_int` from the very digit planes this tamper edits.
                Check::NormBinding,
            ],
            // C10 (Eq. 117, "centered reduction cannot increase the norm") is a
            // property of the response digits themselves, not of the certificate, so
            // it bites even where no Eq. (118) proof is sent.
            &[Check::Recompose, Check::Range, Check::EnergyDirection],
        ),
    ));

    // 3. The compressed commitment payload changed. Since Eqs. (126)–(128) were
    //    wired in, the corrupted payload also changes the digit tables whose cells
    //    `pi` addresses, so C11 moves alongside `Commitment` on both Euclidean arms;
    //    the coefficient route sends no certificate, so it keeps its own set.
    let mut p = proof.clone();
    p.commitment[3] ^= 0x80;
    out.push((
        "tampered commitment",
        p,
        measured(
            sched,
            &[Check::SetupGroup, Check::Commitment, Check::NormBinding],
            &[
                Check::NormSumcheck,
                Check::SetupGroup,
                Check::Commitment,
                Check::NormBinding,
            ],
            &[Check::SetupGroup, Check::Commitment],
        ),
    ));

    // 4. Two batch members swapped, digests and inner images included. C11 moves on
    //    both Euclidean arms: the swap re-derives the challenges that select the
    //    `pi`-addressed cells, so the binding disagrees as well.
    let mut p = proof.clone();
    p.sources.swap(0, 1);
    p.inner.swap(0, 1);
    out.push((
        "swapped batch sources",
        p,
        measured(
            sched,
            &[Check::Relation, Check::SetupGroup, Check::NormBinding],
            &[
                Check::Relation,
                Check::NormSumcheck,
                Check::SetupGroup,
                Check::NormBinding,
            ],
            &[Check::Relation, Check::SetupGroup],
        ),
    ));

    // 5. The setup group's deferred evaluation replaced by a stale claim. Same
    //    cascade as case 4 through the transcript-derived challenges.
    let mut p = proof.clone();
    p.setup_claim[0] += Q::ONE;
    out.push((
        "false deferred setup claim",
        p,
        measured(
            sched,
            &[Check::SetupGroup, Check::NormBinding],
            &[Check::NormSumcheck, Check::SetupGroup, Check::NormBinding],
            &[Check::SetupGroup],
        ),
    ));

    // 6. A digit raised above the alphabet, planes-only.
    let mut p = proof.clone();
    p.groups[0].planes[0][1] = 7;
    out.push((
        "digit raised above the alphabet",
        p,
        measured(
            sched,
            &[Check::Recompose, Check::Range, Check::NormBound],
            &[
                Check::Recompose,
                Check::Range,
                Check::NormSumcheck,
                Check::NormBound,
                Check::EnergyDirection,
                Check::NormBinding,
            ],
            &[Check::Recompose, Check::Range, Check::EnergyDirection],
        ),
    ));

    // 6b. Digits so large that a squared norm leaves `u128`: Eq. (117) cannot be
    //     evaluated at all. This is what separates `EnergyUndecidable` from
    //     `EnergyDirection` — while the check folded the error into `0`, both sides
    //     became 0, `0 > 0` was false, and an undecidable group satisfied the
    //     direction test silently on all three routes. Measured sets, per arm.
    let mut p = proof.clone();
    for plane in p.groups[0].planes.iter_mut() {
        for digit in plane.iter_mut().take(8) {
            *digit = i64::MAX;
        }
    }
    out.push((
        "energy beyond u128 (Eq. 117 undecidable)",
        p,
        measured(
            sched,
            &[
                Check::Recompose,
                Check::Range,
                Check::NormBound,
                Check::EnergyUndecidable,
            ],
            &[
                Check::Recompose,
                Check::Range,
                Check::NormSumcheck,
                Check::NormBound,
                Check::EnergyUndecidable,
                Check::NormBinding,
            ],
            &[Check::Recompose, Check::Range, Check::EnergyUndecidable],
        ),
    ));

    // 7. The outer image replaced by another instance's.
    let mut p = proof.clone();
    if !p.outer.is_empty() {
        p.outer[0] = p.outer[0].clone() + elt_at(0, Q::ONE);
    }
    out.push((
        "stale outer image",
        p,
        measured(
            sched,
            &[Check::SetupGroup, Check::Commitment, Check::NormBinding],
            &[
                Check::NormSumcheck,
                Check::SetupGroup,
                Check::Commitment,
                Check::NormBinding,
            ],
            &[Check::SetupGroup, Check::Commitment],
        ),
    ));

    // 8. A batch member's table rewritten *after* its digest was fixed, leaving
    //    the digest and the image alone: the only thing that can catch it is
    //    `t_c := A s_c` re-evaluated from the bound table (C9), because nothing
    //    else in the proof reads `sources[c].table`.
    let mut p = proof.clone();
    p.sources[2].table[0] = p.sources[2].table[0].clone() + one_elt();
    out.push((
        "source table moved under its digest",
        p,
        measured(sched, &[Check::BatchBinding], &[Check::BatchBinding], &[Check::BatchBinding]),
    ));

    // 9. The shared opening image replaced by another instance's: the payload the
    //    compression chain commits to no longer opens what it claims to.
    let mut p = proof.clone();
    if !p.opening.is_empty() {
        p.opening[0] = p.opening[0].clone() + elt_at_open(0, Q::ONE);
    }
    out.push((
        "stale opening image",
        p,
        measured(
            sched,
            &[Check::SetupGroup, Check::Commitment, Check::NormBinding],
            &[
                Check::NormSumcheck,
                Check::SetupGroup,
                Check::Commitment,
                Check::NormBinding,
            ],
            &[Check::SetupGroup, Check::Commitment],
        ),
    ));

    // 10. The descriptor asks `A` to be provisioned one below the radius its own
    //     route derives. The case that isolates C12 on every route: a declared
    //     schedule figure the verifier re-derives rather than transcript
    //     randomness, so nothing else moves with it.
    let mut p = proof.clone();
    p.declared_radius -= 1;
    out.push((
        "under-declared collision radius",
        p,
        measured(sched, &[Check::Radius], &[Check::Radius], &[Check::Radius]),
    ));

    // --- 11 through 18 move a message only a Euclidean route sends ------------
    if sched.certifies() {
        // 11. A false integer claim sent under a perfectly canonical encoding.
        let energy = exact_l2::integer_energy(&proof.groups[0].planes, sched.base).unwrap();
        if energy + 1 <= s_max {
            let mut p = proof.clone();
            p.energy_bytes = exact_l2::encode_energy(s_max, energy + 1);
            out.push((
                "E_resp raised by one",
                p,
                // The same shape on both Euclidean arms, and by the same mechanism
                // each time: a false integer claim breaks the reconstruction
                // Eq. (118) checks, the sum-check that proves it, and the binding
                // that consumes that proof's final evaluation.
                measured(
                    sched,
                    &[
                        Check::NormSumcheck,
                        Check::NormBound,
                        Check::NormBinding,
                    ],
                    &[
                        Check::NormSumcheck,
                        Check::NormBound,
                        Check::NormBinding,
                    ],
                    none,
                ),
            ));
        }

        // 12. The same value with one extra byte: noncanonical (Eq. 118). The
        //     encoding length is absorbed before `zeta_pair`, so under
        //     Fiat-Shamir the whole downstream challenge set moves with it.
        let mut p = proof.clone();
        p.energy_bytes.push(0);
        out.push((
            "noncanonical energy encoding",
            p,
            measured(
                sched,
                &[
                    Check::NormSumcheck,
                    Check::NormCanonical,
                    Check::NormBound,
                    Check::NormBinding,
                ],
                &[
                    Check::NormSumcheck,
                    Check::NormCanonical,
                    Check::NormBound,
                    Check::NormBinding,
                ],
                none,
            ),
        ));

        // 13. Figure 2's first round message of the norm proof altered.
        //     Corrected 2026-09-25: this file's earlier comment argued C11 could not
        //     move here because `failing` re-derives the bound evaluations from the
        //     recovered point. The measurement says otherwise — the failing set is
        //     {NormSumcheck, NormBinding} on both Euclidean arms — so the expectation
        //     follows the run, and the claim that a wrong point can never reach the
        //     binding is now explicitly NOT assumed. If this set ever collapses back to
        //     {NormSumcheck}, investigate what stopped reading the round message.
        let mut p = proof.clone();
        p.norm_proof.rounds[0][0] += Q::ONE;
        out.push((
            "tampered norm round-0 coefficient",
            p,
            measured(
                sched,
                &[Check::NormSumcheck, Check::NormBinding],
                &[Check::NormSumcheck, Check::NormBinding],
                none,
            ),
        ));

        // 14. A round dropped from the norm proof.
        let mut p = proof.clone();
        p.norm_proof.rounds.pop();
        out.push((
            "dropped norm round",
            p,
            measured(
                sched,
                &[Check::NormSumcheck, Check::NormBinding],
                &[Check::NormSumcheck, Check::NormBinding],
                none,
            ),
        ));

        // 15. A Gram residue moved by one (digit-expanded route only).
        if !proof.grams.is_empty() {
            let mut p = proof.clone();
            p.grams[1].residue += Q::ONE;
            out.push((
                "tampered Gram claim",
                p,
                // Eq. (121)'s claims exist only on the expanded route, so the first
                // arm is never read.
                measured(
                    sched,
                    none,
                    &[Check::NormSumcheck, Check::NormBound, Check::NormBinding],
                    none,
                ),
            ));
        }

        // 16. The declared address map `pi` transposed at two cells whose digits
        //     differ. It stays a bijection onto the scheduled digit span, so
        //     Lemma 6.3's premise still holds and nothing else in the level reads
        //     it: this is the case that isolates C11, and the reason Eqs.
        //     (126)-(127) are a check rather than a lemma about the layout.
        let mut p = proof.clone();
        let witness = padded_witness(&proof.digits_flat, sched.witness_len);
        let cells = proof.pi_cells.clone();
        let mut moved = None;
        for i in 0..cells.len().saturating_sub(1) {
            if witness[cells[i]] != witness[cells[i + 1]] {
                moved = Some(i);
                break;
            }
        }
        // The case needs a level that actually sends Eq. (118)'s certificate: on
        // the coefficient route there are no final evaluations for `pi` to bind, so
        // `Check::NormBinding` is not part of that schedule's checks and no tamper
        // can be built here — skipped, exactly as case 15 skips the Gram move when
        // the route sends no Gram claims.
        if let Some(i) = moved.filter(|_| sched.certifies()) {
            p.pi_cells.swap(i, i + 1);
            out.push((
                "pi transposed at two differing cells",
                p,
                measured(sched, &[Check::NormBinding], &[Check::NormBinding], none),
            ));
        }

        // 17. A `pi` that is no longer injective: two response coordinates read one
        //     cell, so C11's first conjunct refuses before any equation is evaluated.
        let mut p = proof.clone();
        let duplicated = proof.pi_cells[0];
        p.pi_cells[proof.pi_cells.len() - 1] = duplicated;
        out.push((
            "pi addresses one cell twice",
            p,
            measured(sched, &[Check::NormBinding], &[Check::NormBinding], none),
        ));

        // 18. The combined sum-check's first message moved: `C_base + C_bind` is
        //     still what the schedule derives, but the proof no longer proves it.
        let mut p = proof.clone();
        p.bind_proof.rounds[0][0] += Q::ONE;
        out.push((
            "tampered combined sum-check round 0",
            p,
            measured(sched, &[Check::NormBinding], &[Check::NormBinding], none),
        ));
    }

    out
}

/// The `A`-collision radius of this schedule under each of §6.2's routes, priced
/// by [`CoreSvpEstimator`] against `A`'s own provisioned view, and what each one
/// admits. p. 64's whole point about the coefficient route is that the schedule
/// *supplies a number to an estimator*, so the number and the answer are printed
/// rather than asserted.
fn price(sched: &Schedule, s_max: u128) {
    let est = CoreSvpEstimator;
    let inst = sched.msis_a();
    let coefficient = sched.coefficient_radius();
    let euclidean = sched.euclidean_radius(s_max);
    println!(
        "   radius pricing (MSIS_{}, d = {}, {} rows x {} cols), contract lambda = {} bits:",
        Q::MODULUS,
        inst.ring_dim,
        inst.rows,
        inst.cols,
        CONTRACT.min_bits
    );
    let admits_coefficient = match &coefficient {
        Err(err) => {
            println!("     coefficient (Eq. 113+79): not derivable — {err}");
            false
        }
        Ok(r) => {
            let bits = est.core_svp_bits(&inst, r);
            let ok = CONTRACT.admits(&est, &inst, r);
            println!(
                "     coefficient (Eq. 113+79): Delta_f^cert = {} x 2 kappa_bar_1 = {} -> eta_A,inf = {} ({} bits, admitted = {ok})",
                sched.delta_cert(),
                norm_route::certified_challenge_difference(sched.kappa_1),
                r.value,
                bits.map_or_else(|| "unpriced".to_string(), |b| b.to_string())
            );
            ok
        }
    };
    let euclidean_raw: Result<CollisionRadius, NormError> = match euclidean {
        None => {
            println!("     euclidean   (Cor. 10.26): no Eq. (118) certificate on this route");
            Err(NormError::RadiusOverflow)
        }
        Some(Err(err)) => {
            println!("     euclidean   (Cor. 10.26): not derivable — {err}");
            Err(err)
        }
        Some(Ok(r)) => {
            let bits = est.core_svp_bits(&inst, &r);
            println!(
                "     euclidean   (Cor. 10.26): Gamma^2 = {} x S_max = {s_max} -> eta^2_A,2 = {} -> eta = {} ({} bits, admitted = {})",
                sched.gamma_sq,
                r.value,
                r.coordinate_bound().unwrap_or(r.value),
                bits.map_or_else(|| "unpriced".to_string(), |b| b.to_string()),
                CONTRACT.admits(&est, &inst, &r)
            );
            Ok(r)
        }
    };
    let earned = sched.earned_radius(s_max);
    let admitted = |r: &Result<CollisionRadius, NormError>| match r {
        Ok(radius) => CONTRACT.admits(&est, &inst, radius),
        Err(_) => false,
    };
    let (coefficient_ok, euclidean_ok) = (admits_coefficient, admitted(&euclidean_raw));
    let both = match (coefficient_ok, euclidean_ok) {
        (true, true) => "both routes",
        (true, false) => "the coefficient route only",
        (false, true) => "the euclidean route only",
        _ => "neither route at this contract",
    };
    println!(
        "   schedule admits: {both} (tightest derivable radius: {})",
        earned.map_or("none".to_string(), |r| format!(
            "{:?} route, eta = {}",
            r.route,
            r.coordinate_bound().unwrap_or(r.value)
        ))
    );
}

/// Runs one level end to end: honest proof, the route pricing, then every named
/// tamper. Returns the checks the run tripped, because a check that *this* route
/// cannot trip (the coefficient arm receives no norm message to move) is not
/// thereby dead — `main` audits the union over all routes.
fn run(
    label: &str,
    seed: [u8; 32],
    delta_f: usize,
    shell: Shell,
    route: NormRoute,
    s_max: u128,
) -> BTreeSet<Check> {
    println!("── {label}");
    let sched = Schedule::new(&seed, delta_f, shell, route);
    println!(
        "   δ_f = {delta_f}  d_A = {D}  N_A = {N_A}  U_dir = {}  S_max = {s_max}",
        sched.u_dir()
    );
    println!(
        "   N_active = {}  N_setup = {}  edge = {}  witness = {} cells  route = {route:?}",
        sched.n_active, sched.n_setup, sched.edge, sched.witness_len
    );
    // §6.2's own test decides the *encoding* of a Euclidean certificate; the
    // coefficient route is a schedule choice made before the fold challenges
    // (p. 64), so there is nothing for `select` to agree with there.
    if sched.certifies() {
        assert_eq!(sched.route_for(s_max), route, "{label}: §6.2 decided the wrong route");
    } else {
        assert_eq!(route, NormRoute::Coefficient, "only the coefficient route skips the certificate");
    }
    price(&sched, s_max);
    let proof = prove(&sched, s_max);
    let honest = failing(&sched, s_max, &proof);
    assert!(honest.is_empty(), "{label}: honest proof failed {honest:?}");
    let map = scheduled_map(&sched);
    println!(
        "   honest proof verifies: {} checks, {}-byte commitment, {} Gram claims, {} norm rounds, {} combined rounds, {}-byte energy encoding, π = {}",
        ALL_CHECKS.len(),
        proof.commitment.len(),
        proof.grams.len(),
        proof.norm_proof.rounds.len(),
        proof.bind_proof.rounds.len(),
        proof.energy_bytes.len(),
        if !sched.certifies() {
            "not sent".to_string()
        } else if map.is_native(D) {
            "Eq. (107) native".to_string()
        } else {
            "Eq. (109) plane-major".to_string()
        }
    );
    assert_eq!(proof.commitment.len(), COMMIT_BYTES);
    assert_eq!(proof.setup_claim.len(), D, "one deferred evaluation per row");
    assert_eq!(
        proof.declared_radius,
        sched
            .earned_radius(s_max)
            .expect("earned")
            .coordinate_bound()
            .expect("priceable"),
        "the honest descriptor declares exactly what its route earned"
    );

    let mut seen: BTreeSet<Check> = BTreeSet::new();
    let cases = tampers(&sched, &proof, s_max);
    for (name, tampered, want) in &cases {
        let got = failing(&sched, s_max, tampered);
        assert!(!got.is_empty(), "{label}/{name}: tamper passed every check");
        // Strict: every case must fail exactly the set written beside it. Each arm
        // was measured per route (collect mode, then restored), so a move here is a
        // behaviour change to adjudicate, not noise to paper over.
        assert_eq!(&got, want, "{label}/{name}: failing set moved");
        seen.extend(got.iter().copied());
        println!("   {name:42} -> {got:?}");
    }
    println!(
        "   {} tampers, {} of {} named checks tripped on this route\n",
        cases.len(),
        seen.len(),
        ALL_CHECKS.len()
    );
    seen
}

fn main() {
    let seed = [0xa5u8; 32];
    let mut tripped: BTreeSet<Check> = BTreeSet::new();

    // Direct window (Eq. 119): three base-8 planes certify |digit| <= 4, so
    // U_dir = N_A (4 + 8·4 + 64·4)^2 = 8 · 292^2 = 682_112 < p32, and with
    // S_max = 4·10^6 also below q the single field identity Eq. (120) decides
    // the claim — and `S_max` sets a 3-byte energy encoding, shorter than the
    // field element it stands in for.
    tripped.extend(run(
        "Euclidean route, direct encoding (Eq. 120)",
        seed,
        3,
        Shell::Binary,
        NormRoute::Direct,
        4_000_000,
    ));
    // Digit-expanded (Eq. 121-123): the full-field depth makes
    // U_dir = 8 · (4(8^11-1)/7)^2 = 1.93·10^20 > 2^67, so one field identity no
    // longer determines an integer and the norm is rebuilt from the Gram
    // segments — with S_max = 2^80 far above q, hence an 11-byte energy
    // encoding rather than a field element.
    tripped.extend(run(
        "Euclidean route, digit-expanded encoding (Eq. 121-123)",
        seed,
        DELTA_FULL,
        Shell::FullRing,
        NormRoute::DigitExpanded,
        1u128 << 80,
    ));
    // The same level without Eq. (118) at all: p. 64's coefficient route, which
    // prices `A` from the digit ranges the range check already certifies and sends
    // no `E_resp`, no Gram claims and no norm sum-check. It is the *only* route this
    // schedule admits, because a full-ring challenge family's certified operator
    // bound makes Corollary 10.26's `64 Γ² S_max` leave the `u128` window entirely —
    // which is precisely why §3.2 draws sparse signed challenges instead.
    tripped.extend(run(
        "coefficient route (Eq. 113 + 79, no norm certificate)",
        seed,
        DELTA_FULL,
        Shell::FullRing,
        NormRoute::Coefficient,
        1u128 << 80,
    ));

    // The anti-dead-code audit runs over the union: a check the coefficient route
    // cannot trip is a check about a message that route does not send, not a check
    // nobody can fail.
    for c in ALL_CHECKS {
        assert!(
            tripped.contains(&c),
            "check {c:?} is never tripped by any tamper on any route — dead code"
        );
    }
    println!(
        "Akita: all {} named checks tripped across {} §6.2 routes, both radius derivations priced.",
        ALL_CHECKS.len(),
        3
    );
}
