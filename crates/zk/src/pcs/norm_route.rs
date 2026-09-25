//! Certifying the exact `l2` response norm (eprint 2026/1983 §6.2).
//!
//! [`crate::shortness::exact_l2`] is the *gate*: it compares an integer squared
//! norm against a claim. This module is the *protocol statement* that gate is
//! meant to discharge, and the arithmetic Akita needs to build the claim at all:
//!
//! * **the reconstructed integer response.** A digit in plane `h` contributes
//!   `b^h` times its value, so the squares must be taken *after* adding the
//!   planes: Eq. (116) rebuilds each response coordinate `z_u^Z` as an integer
//!   and Eq. (117) states `||z||^2 <= E_int(z_hat)` — the direction that makes
//!   `E_int` a sound substitute for the ring norm, and the one a scheme cannot
//!   get by squaring digit planes separately.
//! * **the direct route and its window.** A sum-check proves an equality in
//!   `F_q`; it decides an *integer* equality only while both sides stay below
//!   `q`. §6.2's precondition is therefore `max{U_dir, S_max} < q` with `U_dir`
//!   of Eq. (119) — the largest squared norm the certified digit ranges can
//!   produce. [`select`] applies that test instead of assuming the direct route
//!   is universal, and refuses it otherwise.
//! * **the digit-expanded route.** When `U_dir` can exceed `q`, the norm is
//!   rebuilt from digit-plane Gram segments `p_{t,h,k}` (Eq. 121) whose integer
//!   values are individually recoverable — Eq. (122)'s `|I_t| B_h B_k < q/2` is
//!   what makes the centered lift unique (Lemma 6.4) — and recombined with the
//!   `b^{h+k}` cross weights of Eq. (123) (Proposition 6.5).
//!
//! Both Euclidean routes end at the same statement `E_int = E_resp <= S_max`
//! (Eq. 118), which is the premise Corollary 10.26 turns into the route-specific
//! `A` collision radius; the tighter radius is the whole reason to pay for the
//! proof.
//!
//! # The coefficient route (§5.4 p. 56, §6.2 p. 64, Corollary 10.26 p. 108)
//!
//! The third variant of [`NormRoute`] prices the same inner commitment *without*
//! any norm certificate. p. 64 states the derivation in one sentence: "on the
//! coefficient route, the schedule combines `Delta_f^cert` (Eq. 113) with the
//! certified challenge-difference bound to derive the A-collision radius in
//! (79), which it supplies to the Module-SIS estimator". Concretely,
//!
//! ```text
//! Delta_f^cert = (b* - 1) (b^delta_f - 1)/(b - 1)                    (113)
//! eta_{A,g}    = 2 kappa_bar_{1,g} Delta_f^cert                        (79)
//! kappa_bar_{1,j} <= 2 omega_j,  so  eta_{A,j} = 4 omega_j Delta_f^cert (p. 108)
//! ```
//!
//! which [`a_collision_radius`] and [`delta_cert`] compute, and
//! [`CollisionRadius::from_coefficient`] packages for [`MsisEstimator`]. Because
//! it reads only the *digit ranges* the range check already enforces, this route
//! is available on every schedule — what it costs is the radius, and what
//! justifies the Euclidean certificate's extra proof is exactly [`tighter`]
//! preferring the smaller number. Corollary 10.26's Euclidean price,
//! `eta^2_{A,2} = 64 Gamma^2 S_max`, is [`CollisionRadius::from_euclidean`], and
//! §4.5's admission rule ("The verifier admits the descriptor only when the
//! fixed ranks and security contract of the pre-existing commitment cover these
//! exact bounds", p. 56) is [`SecurityContract::admits`].
//!
//! # Layering
//!
//! The Gram arithmetic is **not** reimplemented here. [`crate::shortness::
//! exact_l2`] owns the single canonical copy of Eqs. (116) and (119)–(123) —
//! `integer_coordinates`, `u_dir`, `segments`, `segment_admissible`,
//! `n_pair`, `pair_order`, `gram_claims`, `reconstruct_energy`,
//! `exact_l2_gate_gram` — and this module's same-named entry points are thin
//! delegations that re-label its errors as [`NormError`] and re-export its
//! [`crate::shortness::exact_l2::GramClaim`] as [`PairClaim`]. What stays here
//! is only what is specific to the *protocol statement*: the reduced ring
//! energy of Eq. (117)'s left side, the coordinate reduction, the Boolean
//! padding that Eq. (120)'s sum-check runs on, the verifier's canonical decoding
//! on the direct route, the coefficient route's Eq. (113)+(79) radius derivation
//! (whose `Delta_f^cert` is a delegation to [`crate::sumcheck::alphabet`], whose
//! `kappa_bar_1` and `Gamma` come from [`crate::pcs::fold_geom`]), and the
//! address map `pi` of Eqs. (126)-(127).
//!
//! # Binding the norm values to the committed witness (pp. 70–71)
//!
//! ```text
//! pi : [N_A] x [delta_f] -> [|w^(j+1)|], image = the scheduled zhat digit cells
//! eta_norm zint^(r)       = eta_norm  sum_u eeq(r,u) sum_h b^h w^(j+1)(pi(u,h))   (126)
//! sum_h eta_norm^(h+1) zh^(r) = sum_u sum_h eta_norm^(h+1) eeq(r,u) w^(j+1)(pi(u,h)) (127)
//! sum_x (P_base(x) + P_bind(x)) = C_base + C_bind                                  (128)
//! ```
//!
//! [`DigitMap`] is `pi` and its admission test (injective, with exactly the
//! scheduled image — Lemma 6.3's premise, which the paper lists alongside the
//! range check and the window). [`pi_binding`] forms *both* printed sides: its
//! `claim` is `C_bind`, the left-hand side read off the norm proof's final
//! evaluations at `r`, and its `weights` are the public coefficients of the
//! right-hand side over the witness cells, which is the shape Eq. (128)'s
//! `P_bind` needs. The equation itself — "Both right-hand sides are public
//! linear functions of the same witness used by the relation check" — is
//! [`check_pi_identity`], and [`crate::sumcheck::fused::fuse`] is Eq. (128)'s
//! additive fusion. Why fusion is the point, p. 71: "The ordinary relation is
//! independent of `eta_norm`, while every norm-check residual has positive
//! degree in `eta_norm`. Thus a false norm-check identity cannot cancel a false
//! ordinary relation identically in the batching challenge."
//!
//! # Verbatim from §6.2 (pp. 68–70)
//!
//! ```text
//! z_u^Z  := Σ_{h<δ_f} b^h w^(j+1)(π(u,h))                          (116)
//! E_int(ẑ) := Σ_{u<N_A} (z_u^Z)^2,   ‖z‖²_{2,coef} ≤ E_int(ẑ)      (117)
//! E_int(ẑ) = E_resp  ∧  E_resp ≤ S_max                             (118)
//! U_dir  := N_A (Σ_{h<δ_f} b^h B_dig,h)²                           (119)
//! Σ_{x∈{0,1}^{µ'}} z_int(x)² = E_resp                              (120)
//! p_{t,h,k} := Σ_{u∈I_t} z_h(u) z_k(u) ∈ F_q                       (121)
//! |I_t| B_dig,h B_dig,k < q/2                                      (122)
//! E_resp = Σ_t (Σ_h b^{2h} p̄_{t,h,h} + 2 Σ_{h<k} b^{h+k} p̄_{t,h,k})  (123)
//! N_pair = |{I_t}| δ_f(δ_f + 1)/2                                  (124)
//! Σ_x (P_rng(x) + ζ_norm P_norm(x)) = C_rng + ζ_norm C_norm        (125)
//! ```
//!
//! with the paper's own precondition, "The direct route is admissible only when
//! `max{U_dir, S_max} < q`" (p. 69), and Lemma 6.4 (p. 70) licensing the
//! centered lift `p̄ ∈ (-q/2, q/2)` that [`reconstruct_from_pairs`] performs.
//! The scheme plumbing around these statements — which tables the prover holds,
//! what order the transcript absorbs them in, and how the fused sum-check is
//! anchored — is example work, per this crate's layering rule; the equations
//! themselves, including Eqs. (126)–(128), are here.

use crate::pcs::fold_geom::{ceil_sqrt, eq_weight};
use crate::shortness::exact_l2::{self, GramClaim};
use crate::sumcheck::alphabet;
use algebra::ring::traits::CenteredRing;
use algebra::ring::Ring;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// The crate's canonical Gram claim, re-exported under the name this module's
/// protocol statement uses (`PairClaim` in Eq. 121's prose).
pub type PairClaim<R> = GramClaim<R>;

/// Lifts the gate's refusal into this module's protocol-level error type, so
/// the two never disagree about *why* something was refused.
fn lifted(err: exact_l2::ExactL2Error) -> NormError {
    match err {
        exact_l2::ExactL2Error::NotAdmissible { limit, modulus } => {
            NormError::NotAdmissible { limit, modulus }
        }
        exact_l2::ExactL2Error::Overflow => NormError::Overflow,
        exact_l2::ExactL2Error::Mismatch { actual, claimed } => NormError::Mismatch { actual, claimed },
        exact_l2::ExactL2Error::BoundExceeded { norm_sq, max } => {
            NormError::BoundExceeded { norm_sq, max }
        }
        exact_l2::ExactL2Error::NonCanonical { decoded, max } => {
            NormError::NonCanonical { decoded, max }
        }
        exact_l2::ExactL2Error::SegmentTooWide {
            len,
            magnitude,
            half_modulus,
        } => NormError::SegmentTooWide {
            len,
            magnitude,
            half_modulus,
        },
    }
}

/// Why a norm statement was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormError {
    /// The squared bound reaches the modulus, so the field equality no longer
    /// determines an integer (§6.2's direct-route precondition).
    NotAdmissible {
        /// `max{U_dir, S_max}` as supplied.
        limit: u128,
        /// The modulus it must stay under.
        modulus: u64,
    },
    /// The claimed norm is not the canonical unsigned encoding the transcript
    /// fixes (Eq. 118's "rejects any noncanonical encoding").
    NonCanonical {
        /// What was decoded.
        decoded: u128,
        /// The public ceiling the encoding must fit under.
        max: u128,
    },
    /// The reconstruction differs from the transmitted claim.
    Mismatch {
        /// What the witness actually squares to.
        actual: u128,
        /// What was claimed.
        claimed: u128,
    },
    /// The exact norm is correct arithmetic but exceeds the schedule bound.
    BoundExceeded {
        /// The computed squared norm.
        norm_sq: u128,
        /// The permitted squared bound `S_max`.
        max: u128,
    },
    /// A Gram segment is too long to lift uniquely (Eq. 122 violated, so
    /// Lemma 6.4's hypothesis fails and the residue is ambiguous).
    SegmentTooWide {
        /// Segment length.
        len: usize,
        /// `|I_t| B_{dig,h} B_{dig,k}`, the integer the residue must represent.
        magnitude: u128,
        /// `q/2`, the ceiling it must stay under.
        half_modulus: u128,
    },
    /// A squared-norm accumulation left the `u128` window. Never wraps.
    Overflow,
    /// Eq. (79) / Corollary 10.26's radius product left the `u128` window. The
    /// route is not derivable at this scale rather than silently saturated —
    /// an estimator handed a clamped radius would over-report hardness.
    RadiusOverflow,
    /// `pi` names some witness cell twice, so two response coordinates read the
    /// same digit and Lemma 6.3's premise ("the map `pi` is injective with the
    /// scheduled image") fails.
    NotInjective {
        /// The domain pair `(u, h)` that repeats an earlier address.
        pair: (usize, usize),
        /// The repeated address.
        cell: usize,
    },
    /// `pi` addresses a cell outside the scheduled `zhat` digit span. Together
    /// with [`NormError::NotInjective`] and the domain/span size equality this is
    /// exactly the paper's premise: an injective map from a `delta_f * N_A`
    /// domain into a span of `delta_f * N_A` cells *is* a bijection onto the
    /// scheduled image, so no separate surjectivity scan is needed.
    AddressOutsideSpan {
        /// The domain pair `(u, h)` whose address is bad.
        pair: (usize, usize),
        /// The address `pi(u, h)` declared.
        cell: usize,
    },
    /// The declared `pi` has the wrong domain size, or a witness is shorter than
    /// the weight table Eqs. (126)/(127) were formed over.
    ImageMismatch {
        /// Domain length the schedule fixes.
        want: usize,
        /// Length supplied.
        got: usize,
    },
    /// Eqs. (126)/(127)'s two sides disagree: the norm proof's final evaluations
    /// do not reconstruct from the `pi`-addressed witness cells.
    BindingMismatch {
        /// `C_bind`, the left-hand side.
        claim: u128,
        /// The `pi`-addressed right-hand side.
        reconstructed: u128,
    },
    /// The last range-tree point does not index the response domain: `eq(r, .)`
    /// runs over `2^|r|` coordinates and `pi`'s domain has `N_A` of them, and the
    /// two must agree or the weights are formed over a different cube than the
    /// evaluations were left on.
    DomainMismatch {
        /// `N_A`.
        cells: usize,
        /// `|r|`, so the point indexes `2^point_bits` cells.
        point_bits: usize,
    },
    /// The norm proof left a different number of final evaluations than the route
    /// has digits to bind: one for Eq. (126)'s `zint`, `delta_f` for Eq. (127)'s
    /// planes. A malformed proof rather than a false statement.
    MalformedEvaluations {
        /// How many evaluations arrived.
        left: usize,
        /// How many the route owes.
        expected: usize,
    },
    /// The descriptor asks to be provisioned at a radius *below* the one its own
    /// fold certified, which would price Module-SIS against collisions the
    /// schedule never excluded (p. 56's admission rule).
    RadiusUnderDeclared {
        /// What was declared.
        declared: u128,
        /// The least radius the route derives.
        earned: u128,
    },
    /// The declared radius meets the derivation but the estimator reports fewer
    /// Core-SVP bits than the security contract requires.
    ContractNotMet {
        /// What the estimator reported.
        bits: u32,
        /// What the contract requires.
        min_bits: u32,
    },
    /// The estimator could not price the query at all, which is *not* a hardness
    /// of zero and never an admission.
    NotPriced,
}

impl fmt::Display for NormError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NormError::NotAdmissible { limit, modulus } => write!(
                f,
                "direct route needs max(U_dir, S_max) < q, got {limit} against q = {modulus}"
            ),
            NormError::NonCanonical { decoded, max } => {
                write!(f, "decoded norm {decoded} is outside [0, {max}]")
            }
            NormError::Mismatch { actual, claimed } => {
                write!(f, "claimed E_resp {claimed}, reconstruction gives {actual}")
            }
            NormError::BoundExceeded { norm_sq, max } => {
                write!(f, "exact norm {norm_sq} exceeds the bound {max}")
            }
            NormError::SegmentTooWide {
                len,
                magnitude,
                half_modulus,
            } => write!(
                f,
                "segment of {len} cells spans {magnitude} >= q/2 = {half_modulus}, \
                 so its residue is not uniquely liftable"
            ),
            NormError::Overflow => f.write_str("squared-norm accumulation overflowed u128"),
            NormError::RadiusOverflow => {
                f.write_str("the collision radius product left u128, so the route is not derivable")
            }
            NormError::NotInjective { pair, cell } => write!(
                f,
                "pi({},{}) = {cell} repeats an address, so pi is not injective",
                pair.0, pair.1
            ),
            NormError::AddressOutsideSpan { pair, cell } => write!(
                f,
                "pi({},{}) = {cell} lies outside the scheduled zhat digit span",
                pair.0, pair.1
            ),
            NormError::ImageMismatch { want, got } => write!(
                f,
                "the schedule fixes a domain of {want} cells, {got} were declared"
            ),
            NormError::BindingMismatch {
                claim,
                reconstructed,
            } => write!(
                f,
                "the norm proof's final evaluations give {claim}, the pi-addressed witness cells {reconstructed}"
            ),
            NormError::DomainMismatch { cells, point_bits } => write!(
                f,
                "pi addresses {cells} response coordinates, the point indexes 2^{point_bits}"
            ),
            NormError::MalformedEvaluations { left, expected } => write!(
                f,
                "the norm proof left {left} final evaluations, the route owes {expected}"
            ),
            NormError::RadiusUnderDeclared { declared, earned } => write!(
                f,
                "descriptor declares radius {declared}, its fold earned {earned}"
            ),
            NormError::ContractNotMet { bits, min_bits } => write!(
                f,
                "radius prices {bits} Core-SVP bits, the contract requires {min_bits}"
            ),
            NormError::NotPriced => f.write_str("the Module-SIS estimator cannot price this query"),
        }
    }
}

/// Which certificate a level's schedule sends, and hence which radius it may
/// price its inner `A` with (§6.2, pp. 64 and 68–70).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum NormRoute {
    /// Euclidean, one field identity `sum_x zint(x)^2 = E_resp` (Eq. 120), exact
    /// only under [`NormError::NotAdmissible`]'s precondition.
    Direct,
    /// Euclidean, digit-plane Gram segments lifted to integers and recombined
    /// (Eq. 123).
    DigitExpanded,
    /// Coefficient: no norm certificate at all. The digit ranges the range check
    /// already enforces give `Delta_f^cert` (Eq. 113), and Eq. (79) turns that
    /// plus the certified challenge-difference bound into the `A`-collision
    /// radius, which the schedule supplies to the Module-SIS estimator (p. 64).
    /// p. 64's "on the Euclidean route, the same digit ranges remain in force and
    /// the next level *additionally* certifies `Eint(zhat) <= Smax`" is what this
    /// variant omits.
    Coefficient,
}

impl NormRoute {
    /// Whether this route sends the exact statement Eq. (118) — i.e. whether the
    /// level's proof carries `E_resp` and a norm sum-check, and hence whether
    /// Eqs. (126)-(128) have any final evaluations to bind.
    pub const fn certifies_energy(self) -> bool {
        !matches!(self, NormRoute::Coefficient)
    }
}

/// The reconstructed integer response coordinates of Eq. (116):
/// `z_u^Z = sum_{h < delta_f} b^h * digit[h][u]`, over the integers (no
/// reduction), from `delta_f` digit planes of `n_a` cells each.
///
/// Delegates to [`crate::shortness::exact_l2::integer_coordinates`], the
/// canonical copy.
///
/// # Panics
/// If the planes have unequal lengths, or `base^h` would overflow.
pub fn integer_coordinates(planes: &[Vec<i64>], base: u64) -> Vec<i128> {
    exact_l2::integer_coordinates(planes, base)
}

/// `E_int(z_hat) = sum_u (z_u^Z)^2` — the exact integer quantity of Eq. (116),
/// which bounds the ring norm from above (Eq. 117).
///
/// # Errors
/// [`NormError::Overflow`] if the sum leaves the `u128` window.
pub fn exact_energy(coords: &[i128]) -> Result<u128, NormError> {
    let mut acc: u128 = 0;
    for &z in coords {
        let square = u128::try_from(z.checked_mul(z).ok_or(NormError::Overflow)?)
            .map_err(|_| NormError::Overflow)?;
        acc = acc.checked_add(square).ok_or(NormError::Overflow)?;
    }
    Ok(acc)
}

/// The squared ring norm of the *reduced* coordinates, `||z||^2_{2,coef}`, which
/// Eq. (117) puts below [`exact_energy`].
pub fn reduced_energy<R: CenteredRing>(coords: &[R]) -> Result<u128, NormError> {
    let mut acc: u128 = 0;
    for c in coords {
        let v = i128::from(c.centered());
        acc = acc
            .checked_add(u128::try_from(v * v).map_err(|_| NormError::Overflow)?)
            .ok_or(NormError::Overflow)?;
    }
    Ok(acc)
}
/// The reduction `Z -> F_q` of integer response coordinates, so a caller can
/// form the ring vector `z = G_{b,m_A} z_hat` Eq. (117) compares against.
pub fn reduce_coords<R: Ring>(coords: &[i128]) -> Vec<R> {
    let modulus = i128::from(R::MODULUS);
    coords
        .iter()
        .map(|&z| R::from(z.rem_euclid(modulus) as u64))
        .collect()
}

/// `U_dir` of Eq. (119): the largest squared norm the *certified digit ranges*
/// can produce, `N_A * (sum_h b^h B_{dig,h})^2`. The direct route may only be
/// used when this and `S_max` both stay under `q`. Delegates to
/// [`crate::shortness::exact_l2::u_dir`].
///
/// # Panics
/// If the bounds are inconsistent or the weight overflows.
pub fn u_dir(n_a: usize, base: u64, digit_bounds: &[u64]) -> u128 {
    exact_l2::u_dir(n_a, base, digit_bounds)
}

/// Which of §6.2's two *Euclidean* proofs a level takes: direct iff
/// `max{U_dir, S_max} < q`, otherwise the digit-expanded reconstruction (the gate
/// "refuses rather than approximating", which is also
/// [`crate::shortness::exact_l2::direct_route_admissible`]'s test, applied here
/// to a raw modulus because the caller holds `q`, not a value).
///
/// This never returns [`NormRoute::Coefficient`]: that route is not a proof of
/// Eq. (118) and so is not decided by Eq. (119)'s window. It is a *schedule*
/// choice — p. 64, "The route, squared-norm bound, response coordinate map,
/// challenge family, and proof shape are fixed before the fold challenges" — and
/// [`CollisionRadius::from_coefficient`] is what it costs to take.
///
/// The decision itself is [`crate::shortness::exact_l2::select_route`]'s; this
/// only re-labels it in the protocol's vocabulary.
pub fn select(u_dir: u128, s_max: u128, modulus: u64) -> NormRoute {
    match exact_l2::select_route(u_dir, s_max, modulus) {
        exact_l2::Route::Direct => NormRoute::Direct,
        exact_l2::Route::DigitGram => NormRoute::DigitExpanded,
    }
}

/// The verifier's side of the direct route (Lemma 6.3): canonical decoding into
/// `[0, S_max]`, the admissibility window `max{U_dir, S_max} < q`, and the
/// equality of the reconstruction with the transmitted claim.
///
/// # Errors
/// [`NormError::NotAdmissible`], [`NormError::NonCanonical`],
/// [`NormError::Mismatch`] or [`NormError::BoundExceeded`].
pub fn check_direct(
    coords: &[i128],
    claimed: u128,
    s_max: u128,
    u_dir: u128,
    modulus: u64,
) -> Result<u128, NormError> {
    let limit = u_dir.max(s_max);
    if limit >= u128::from(modulus) {
        return Err(NormError::NotAdmissible { limit, modulus });
    }
    if claimed > s_max {
        return Err(NormError::NonCanonical {
            decoded: claimed,
            max: s_max,
        });
    }
    let actual = exact_energy(coords)?;
    if actual != claimed {
        return Err(NormError::Mismatch { actual, claimed });
    }
    if actual > s_max {
        return Err(NormError::BoundExceeded {
            norm_sq: actual,
            max: s_max,
        });
    }
    Ok(actual)
}

/// Public consecutive segments of `[0, n_a)`, the `I_t` of Eq. (121). Delegates
/// to [`crate::shortness::exact_l2::segments`].
///
/// # Panics
/// If `seg_len == 0` or `n_a == 0`.
pub fn segments(n_a: usize, seg_len: usize) -> Vec<(usize, usize)> {
    exact_l2::segments(n_a, seg_len)
}

/// Eq. (122): a segment may only be used if the largest integer its Gram sum can
/// reach stays inside the unique centered-lift window. Canonical copy:
/// [`crate::shortness::exact_l2::segment_admissible`].
pub fn segment_admissible(len: usize, b_dig_h: u64, b_dig_k: u64, modulus: u64) -> bool {
    exact_l2::segment_admissible(len, b_dig_h, b_dig_k, modulus)
}

/// `N_pair = |{I_t}| * delta_f (delta_f + 1) / 2` (Eq. 124): how many Gram
/// claims the digit-expanded route transmits, which is the proof-size price of
/// leaving the direct window.
pub const fn n_pair(segments: usize, delta_f: usize) -> usize {
    exact_l2::n_pair(segments, delta_f)
}

/// The canonical ordering of `(t, h, k)` triples the verifier indexes its
/// batching powers by (Eq. 125's "public canonical ordering of triples").
pub fn pair_order(segments: usize, delta_f: usize) -> Vec<(usize, usize, usize)> {
    exact_l2::pair_order(segments, delta_f)
}

/// Forms every `p_{t,h,k}` from the digit planes, checking Eq. (122) as it goes:
/// a segment that cannot be lifted uniquely is refused rather than silently
/// wrapped. The arithmetic is [`crate::shortness::exact_l2::gram_claims`].
///
/// # Errors
/// [`NormError::SegmentTooWide`] for the first inadmissible `(t, h, k)`.
pub fn digit_pair_claims<R: Ring>(
    planes: &[Vec<i64>],
    segs: &[(usize, usize)],
    digit_bounds: &[u64],
    modulus: u64,
) -> Result<Vec<PairClaim<R>>, NormError> {
    exact_l2::gram_claims(planes, segs, digit_bounds, modulus).map_err(lifted)
}

/// Reconstructs the integer squared norm from the Gram claims (Eq. 123), lifting
/// each residue to its unique representative in `(-q/2, q/2)` (Lemma 6.4) and
/// weighting by `b^{2h}` on the diagonal and `2 b^{h+k}` off it (Proposition 6.5).
/// The arithmetic is [`crate::shortness::exact_l2::reconstruct_energy`].
///
/// # Errors
/// [`NormError::SegmentTooWide`] if a claim's integer magnitude cannot be
/// uniquely lifted, [`NormError::Overflow`] beyond `u128` or for the negative
/// reconstruction p. 69 tells the verifier to reject.
pub fn reconstruct_from_pairs<R: Ring>(
    claims: &[PairClaim<R>],
    segs: &[(usize, usize)],
    digit_bounds: &[u64],
    base: u64,
) -> Result<u128, NormError> {
    exact_l2::reconstruct_energy(claims, segs, digit_bounds, base).map_err(lifted)
}

/// The full digit-expanded gate: reconstruct, compare with the transmitted
/// integer claim, and enforce `<= S_max` (Eq. 118 with Eq. 123's reconstruction).
/// The gate itself is [`crate::shortness::exact_l2::exact_l2_gate_gram`].
///
/// # Errors
/// As [`reconstruct_from_pairs`], plus [`NormError::Mismatch`] and
/// [`NormError::BoundExceeded`].
pub fn check_digit_expanded<R: Ring>(
    claims: &[PairClaim<R>],
    segs: &[(usize, usize)],
    digit_bounds: &[u64],
    base: u64,
    claimed: u128,
    s_max: u128,
) -> Result<u128, NormError> {
    exact_l2::exact_l2_gate_gram(claims, segs, digit_bounds, base, claimed, s_max).map_err(lifted)
}

/// The extension of the reconstructed response to the Boolean domain: the
/// `n_a` coordinates in their scheduled order, zero-padded to `2^bits` (§6.2's
/// `zint(x)`, the table the direct norm sum-check runs on).
///
/// # Panics
/// If `coords` does not fit the declared padding length.
pub fn pad_to_boolean<R: Ring>(coords: &[i128], domain: usize) -> Vec<R> {
    assert!(
        coords.len() <= domain,
        "the response must fit its padded domain"
    );
    let mut out = reduce_coords::<R>(coords);
    out.resize(domain, R::ZERO);
    out
}

// --- the coefficient route: Eq. (113) + Eq. (79) -> the Module-SIS estimator ---

/// `Delta_f^cert`, Eq. (113): the certified *difference* envelope of a
/// `delta_f`-deep base-`base` response whose digits were range-checked against
/// the balanced alphabet `A_{b*}`. "Two digits in `{-b*/2, ..., b*/2 - 1}` differ
/// by at most `b* - 1`" (p. 64), and digit position `h` contributes `b^h`.
///
/// Delegates to [`crate::sumcheck::alphabet::cert_difference`], the canonical
/// copy — and the *wider* of §5.4's two envelopes, which is the point: p. 63,
/// "this second bound applies to every accepted response and determines the
/// Module-SIS collision radius".
///
/// # Panics
/// As [`crate::sumcheck::alphabet::cert_difference`]: a non-power-of-two base, or
/// a width that leaves `u128`.
pub fn delta_cert(base_star: u64, base: u64, delta_f: usize) -> u128 {
    alphabet::cert_difference(base_star, base, delta_f)
}

/// `Z_infinity`, Eq. (112)'s `beta_fold^cert`: the certified coefficient envelope
/// of a *single* accepted response, i.e. the `Z_infty` Corollary 10.26 quantifies
/// over ("every accepted response on the coefficient route satisfies
/// `||z||_{inf,coef} <= Z_infty`"). Delegates to
/// [`crate::sumcheck::alphabet::cert_envelope`].
///
/// # Panics
/// As [`crate::sumcheck::alphabet::cert_envelope`].
pub fn coefficient_envelope(base_star: u64, base: u64, delta_f: usize) -> u128 {
    alphabet::cert_envelope(base_star, base, delta_f)
}

/// `kappa_bar_{1,j} <= 2 omega_j`, p. 108: the certified challenge-difference
/// `l1` bound of a family drawn from an `l1`-ball of mass `omega_j`, since two
/// members differ by at most `2 omega_j`. Substituting it into Eq. (79) is the
/// paper's own next sentence — "its coefficient-norm inner commitment is
/// therefore queried at `eta_{A,j} = 4 omega_j Delta_f^cert`".
///
/// `omega` is a challenge mass, so `2 omega` always fits `u128`; nothing saturates.
pub fn certified_challenge_difference(omega: u64) -> u128 {
    2 * u128::from(omega)
}

/// Eq. (79) as a free entry point: `eta_{A,g} = 2 kappa_bar_{1,g} Delta_f^cert`,
/// the number p. 64 says the schedule "supplies to the Module-SIS estimator".
/// Delegates to [`CollisionRadius::from_coefficient`], which carries the route tag
/// and norm index along with the figure so a schedule cannot hand the estimator an
/// `l2` radius labelled as an `l_inf` one.
///
/// # Errors
/// [`NormError::RadiusOverflow`] beyond `u128`.
pub fn a_collision_radius(kappa_bar_1: u128, delta_cert: u128) -> Result<u128, NormError> {
    CollisionRadius::from_coefficient(kappa_bar_1, delta_cert).map(|r| r.value)
}

/// Which norm an `A`-collision radius is stated in — Corollary 10.26's `p_A`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CollisionNorm {
    /// `p_A = infinity`: a coefficientwise bound, Eq. (205)'s line.
    Sup,
    /// `p_A = 2`: a bound on the squared `l2` norm, Eq. (206)'s line.
    Two,
}

/// An `A`-collision radius as a schedule derives it, tagged with the route that
/// earned it: the quantity p. 64 says the schedule "supplies to the Module-SIS
/// estimator", and the `eta_I` of Theorem 10.33's
/// `Adv^{MSIS}_{q,d_I}(n_I, m_I, eta_I)` sum.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CollisionRadius {
    /// The route that derived it.
    pub route: NormRoute,
    /// Which norm it is stated in.
    pub norm: CollisionNorm,
    /// `eta_{A,inf}` for [`CollisionNorm::Sup`]; `eta_{A,2}^2` — the *square*, as
    /// Corollary 10.26 prints it — for [`CollisionNorm::Two`].
    pub value: u128,
}

impl CollisionRadius {
    /// Eq. (79): `eta_{A,g} = 2 kappa_bar_{1,g} Delta_f^cert`, p. 64's coefficient
    /// route. Eq. (205) is the same product read as
    /// `||z_A||_{inf,coef} <= 2 kappa_bar_1 beta_bar_inf` with the certified
    /// *difference* envelope `beta_bar_inf := Delta_f^cert` standing in for a
    /// response-specific bound, which is why this radius needs no norm
    /// certificate: the range check already fixed `Delta_f^cert`.
    ///
    /// # Errors
    /// [`NormError::RadiusOverflow`] beyond `u128`.
    pub fn from_coefficient(kappa_bar_1: u128, delta_cert: u128) -> Result<Self, NormError> {
        let value = kappa_bar_1
            .checked_mul(delta_cert)
            .and_then(|v| v.checked_mul(2))
            .ok_or(NormError::RadiusOverflow)?;
        Ok(Self {
            route: NormRoute::Coefficient,
            norm: CollisionNorm::Sup,
            value,
        })
    }

    /// Corollary 10.26's own spelling of the coefficient radius,
    /// `eta_{A,inf} = 8 kappa_1 Z_infty`, with `Z_infty` of Eq. (112) and
    /// `kappa_1` a bound on each *raw* challenge's `l1` norm — so two accepted
    /// openings double it, and two accepted responses double it again.
    ///
    /// This is never tighter than [`CollisionRadius::from_coefficient`] at the same
    /// family, because `b* - 1 <= b*` is exactly the difference between Eq. (113)'s
    /// difference envelope and twice Eq. (112)'s single-response envelope. A
    /// schedule reaching for the looser form would over-price its own collisions,
    /// so the tests pin the inequality rather than leaving it to prose.
    ///
    /// # Errors
    /// [`NormError::RadiusOverflow`] beyond `u128`.
    pub fn coefficient_corollary(kappa_1: u128, z_infinity: u128) -> Result<Self, NormError> {
        let value = kappa_1
            .checked_mul(z_infinity)
            .and_then(|v| v.checked_mul(8))
            .ok_or(NormError::RadiusOverflow)?;
        Ok(Self {
            route: NormRoute::Coefficient,
            norm: CollisionNorm::Sup,
            value,
        })
    }

    /// Corollary 10.26's Euclidean radius, `eta_{A,2}^2 = 64 Gamma^2 S_max`: the
    /// certified challenge *multiplication-operator* bound `Gamma` squared, times
    /// the schedule's certified energy bound. `gamma_sq` rather than `gamma` keeps
    /// the arithmetic exact — [`crate::pcs::fold_geom::op_norm_upper_sq`] already
    /// returns a squared integer, and p. 108's "if the schedule certifies an exact
    /// operator bound on challenge differences, it may replace `2 Gamma`" is the
    /// licence to use it here instead of the two-raw-challenge form.
    ///
    /// # Errors
    /// [`NormError::RadiusOverflow`] beyond `u128`.
    pub fn from_euclidean(gamma_sq: u128, s_max: u128) -> Result<Self, NormError> {
        let value = gamma_sq
            .checked_mul(s_max)
            .and_then(|v| v.checked_mul(64))
            .ok_or(NormError::RadiusOverflow)?;
        Ok(Self {
            route: NormRoute::Direct,
            norm: CollisionNorm::Two,
            value,
        })
    }

    /// This radius as a coordinatewise `l_inf` bound, the units
    /// [`algebra::security::SisInstance`] consumes. `||v||_{inf} <= ||v||_2`, so the
    /// square root of an `l2` radius is a valid — if conservative — coordinate
    /// bound, and [`crate::pcs::fold_geom::ceil_sqrt`] rounds *up*, so the
    /// conversion never claims more hardness than the radius carries.
    ///
    /// # Errors
    /// Never today; kept fallible so a future wider radius cannot silently clamp.
    pub fn coordinate_bound(&self) -> Result<u128, NormError> {
        match self.norm {
            CollisionNorm::Sup => Ok(self.value),
            CollisionNorm::Two => Ok(ceil_sqrt(self.value)),
        }
    }
}

/// The tighter of two admissible radii, compared in the coordinate units the
/// estimator prices (so a `p_A = 2` and a `p_A = infinity` radius are
/// commensurable). An unpriceable candidate never wins: it is dropped rather than
/// treated as infinitely loose.
#[must_use]
pub fn tighter(a: Option<CollisionRadius>, b: Option<CollisionRadius>) -> Option<CollisionRadius> {
    let rank = |r: &CollisionRadius| r.coordinate_bound().ok();
    match (a, b) {
        (Some(x), Some(y)) => match (rank(&x), rank(&y)) {
            (rx, Some(ry)) if ry < rx.unwrap_or(u128::MAX) => Some(y),
            _ => Some(x),
        },
        (x, y) => x.or(y),
    }
}

/// One Module-SIS instance in the schedule's inventory: Theorem 10.33's `I(sch)`
/// entry `(n_I, m_I, d_I, q)`, of which the extracted collision of radius
/// [`CollisionRadius`] is a nonzero solution.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MsisInstance {
    /// Which map this instance is, for the schedule record.
    pub role: &'static str,
    /// Modulus `q`.
    pub modulus: u64,
    /// Ring dimension `d_I`.
    pub ring_dim: usize,
    /// Module rank `n_I`.
    pub rows: usize,
    /// Column count `m_I`.
    pub cols: usize,
}

impl MsisInstance {
    /// The instance as a base-field lattice, rows: `n_I d_I`.
    pub const fn flat_rows(&self) -> usize {
        self.rows * self.ring_dim
    }

    /// The instance as a base-field lattice, columns: `m_I d_I`.
    pub const fn flat_cols(&self) -> usize {
        self.cols * self.ring_dim
    }
}

/// The Module-SIS estimator p. 64 hands the coefficient radius to.
///
/// An implementation reports the Core-SVP cost of finding a nonzero solution to
/// `A y = 0 (mod q)` for `A` drawn from the instance with `y` bounded by the
/// radius. `None` means it cannot price the query at all, and
/// [`SecurityContract::admits`] treats that as *not* admitted rather than as zero.
pub trait MsisEstimator {
    /// Estimated attack cost in bits.
    fn core_svp_bits(&self, instance: &MsisInstance, radius: &CollisionRadius) -> Option<u32>;

    /// The radius as an `l_inf` coordinate bound, in the estimator's `f64` units.
    fn bound(&self, radius: &CollisionRadius) -> Option<f64> {
        radius.coordinate_bound().map(|b| to_f64(b)).ok()
    }
}

/// The crate's [`algebra::security`] Core-SVP estimator behind Akita's interface:
/// Lyubashevsky's BKZ-on-the-kernel rule, which
/// [`algebra::security::sis_block_size`] inverts and
/// [`algebra::security::sis_security`] prices at `0.265 mu` quantum / `0.292 mu`
/// classical sieve cost.
///
/// It flattens the module — a Module-SIS solution *is* an SIS solution of the same
/// coordinate bound on the `n d x m d` lattice, so this reads the module instance
/// from below and never over-reports hardness. The quantum figure is the one
/// returned, since that is the weaker of the two.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct CoreSvpEstimator;

impl MsisEstimator for CoreSvpEstimator {
    fn core_svp_bits(&self, instance: &MsisInstance, radius: &CollisionRadius) -> Option<u32> {
        let bound = self.bound(radius)?;
        let inst = algebra::security::SisInstance {
            n_rows: instance.flat_rows(),
            n_cols: instance.flat_cols(),
            q: instance.modulus,
            bound_inf: bound,
        };
        // The quantum figure, because it is the cheaper of the two and therefore
        // the honest one to plan against. `as u32` truncates toward zero, which is
        // the floor for a non-negative cost and needs no `libm` on a `no_std` path.
        algebra::security::sis_security(&inst).map(|cost| cost.quantum as u32)
    }
}

/// `2^32` as an `f64`, exactly representable.
const TWO_32: f64 = 4_294_967_296.0;

/// One unit in the last place at `1.0`, as a multiplier.
const ONE_ULP_UP: f64 = 1.000_000_000_000_000_2;

/// `u128 -> f64` with no `libm` and no `u128` float libcall: four `u32` limbs
/// recombined by Horner. Exact below `2^53` — every radius a real schedule prices
/// — and rounded *up* beyond that on purpose: a bound read one ulp too small makes
/// the instance look *harder* than it is, and over-claiming hardness is the one
/// direction this module never allows.
fn to_f64(n: u128) -> f64 {
    let mut acc = 0f64;
    for limb in [
        (n >> 96) as u32,
        (n >> 64) as u32,
        (n >> 32) as u32,
        n as u32,
    ] {
        acc = acc * TWO_32 + f64::from(limb);
    }
    acc * ONE_ULP_UP
}

/// The schedule's security contract: what the pre-existing commitments' fixed
/// ranks and geometry are provisioned to survive (p. 56's "the fixed ranks and
/// security contract of the pre-existing commitment").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SecurityContract {
    /// Minimum Core-SVP bits every inventory entry must reach.
    pub min_bits: u32,
}

impl SecurityContract {
    /// Is `instance` at `radius` covered by the contract?
    pub fn admits<E: MsisEstimator>(
        &self,
        estimator: &E,
        instance: &MsisInstance,
        radius: &CollisionRadius,
    ) -> bool {
        estimator
            .core_svp_bits(instance, radius)
            .is_some_and(|bits| bits >= self.min_bits)
    }
}

/// A descriptor's declared `A`-collision radius, checked against what the fold
/// actually certified (p. 56: "The verifier admits the descriptor only when the
/// fixed ranks and security contract of the pre-existing commitment cover these
/// exact bounds"; p. 64: "a different response certificate changes the collision
/// bound that the incoming `A` map must support").
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeclaredRadius {
    /// What the descriptor asks to be provisioned at. Upward rounding is legal —
    /// "the schedule may use either exact radius or an upward-rounded radius in
    /// its Module-SIS inventory" (p. 108) — downward is not.
    pub declared: u128,
    /// The tightest radius the route this level took derives.
    pub earned: CollisionRadius,
}

impl DeclaredRadius {
    /// Checks the declaration against the earned radius and the contract, and
    /// returns the hardness of what was declared.
    ///
    /// # Errors
    /// [`NormError::RadiusUnderDeclared`], [`NormError::NotPriced`] or
    /// [`NormError::ContractNotMet`].
    pub fn check<E: MsisEstimator>(
        &self,
        estimator: &E,
        instance: &MsisInstance,
        contract: &SecurityContract,
    ) -> Result<u32, NormError> {
        let earned = self.earned.coordinate_bound()?;
        if self.declared < earned {
            return Err(NormError::RadiusUnderDeclared {
                declared: self.declared,
                earned,
            });
        }
        let priced = CollisionRadius {
            route: self.earned.route,
            norm: self.earned.norm,
            value: self.declared,
        };
        let bits = estimator
            .core_svp_bits(instance, &priced)
            .ok_or(NormError::NotPriced)?;
        if bits < contract.min_bits {
            return Err(NormError::ContractNotMet {
                bits,
                min_bits: contract.min_bits,
            });
        }
        Ok(bits)
    }
}

// --- Eqs. (126)-(128): binding the norm proof's final evaluations to ẑ ---------

/// §6.2's injective address map
/// `pi : [N_A] x [delta_f] -> [|w^(j+1)|]` "whose image is exactly the scheduled
/// `zhat` digit cells" (p. 68), held as `pi(u, h)` for the canonical domain order
/// `u * delta_f + h`.
///
/// p. 69 pins what the map is *not*: "The map `pi` is defined after
/// extension-field packing, so no further packing factor is applied to this
/// norm." The honest map is therefore Eq. (107)'s native-block address read at
/// the response's own dimension — [`crate::pcs::fold_geom::address`] with
/// `s = 1`, digit slot `h` and coefficient slot `k`, i.e. `pi(u, h)` = plane `h`'s
/// `u`-th cell — and [`DigitMap::native`] builds exactly that, delegating the
/// arithmetic rather than restating it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DigitMap {
    /// Base-field response coordinates `N_A`.
    n_a: usize,
    /// Response digit depth `delta_f`.
    delta_f: usize,
    /// First cell of the scheduled span inside the recursive witness.
    span_start: usize,
    /// `pi(u, h)` at `u * delta_f + h`.
    cells: Vec<usize>,
}

impl DigitMap {
    /// How many cells the scheduled `zhat` digit span occupies: `N_A delta_f`.
    pub const fn span_len(n_a: usize, delta_f: usize) -> usize {
        n_a * delta_f
    }

    /// The honest map, from Eq. (107)'s address arithmetic: response coordinate
    /// `u = j d_A + k` of digit plane `h` lives at
    /// `span_start + pos(j, 0, h, k, 1, delta_f, d_a)`.
    ///
    /// Note what that order *is*: "the coefficient coordinate changes first, then
    /// the digit, then the native block" (p. 63), so a coordinate's `delta_f`
    /// digits are `d_A` apart and the item index `j` is outermost. A schedule whose
    /// witness concatenates whole planes instead — Eq. (109)'s order — must declare
    /// [`DigitMap::plane_major`], and `pi` is precisely where that choice lives.
    ///
    /// # Panics
    /// If `d_a` does not divide `n_a`, which would make `N_A = m_A d_A` untrue.
    pub fn native(n_a: usize, d_a: usize, delta_f: usize, span_start: usize) -> Self {
        assert!(
            d_a >= 1 && n_a % d_a == 0,
            "N_A = m_A d_A is a whole number of ring elements"
        );
        let cells = (0..n_a)
            .flat_map(|u| {
                let (j, k) = (u / d_a, u % d_a);
                (0..delta_f).map(move |h| {
                    span_start + crate::pcs::fold_geom::address(j, 0, h, k, 1, delta_f, d_a)
                })
            })
            .collect();
        Self {
            n_a,
            delta_f,
            span_start,
            cells,
        }
    }

    /// The plane-major reading of `pi`: `pi(u, h) = span_start + h N_A + u`, the
    /// address map of a witness that stores one whole digit plane after another
    /// (Eq. 109's concatenation order) rather than Eq. (107)'s interleaved one.
    ///
    /// This is a *declared* map like any other: [`DigitMap::admit`] is what decides
    /// whether it is legal, and [`DigitMap::is_native`] reports whether it agrees
    /// with the native-block order. Both orders address exactly the scheduled span,
    /// and Eqs. (126)-(127) hold for whichever one the committed witness uses —
    /// which is the point of the map being part of the statement.
    pub fn plane_major(n_a: usize, delta_f: usize, span_start: usize) -> Self {
        let cells = (0..n_a)
            .flat_map(|u| (0..delta_f).map(move |h| span_start + h * n_a + u))
            .collect();
        Self {
            n_a,
            delta_f,
            span_start,
            cells,
        }
    }

    /// Admits a *declared* map, enforcing Lemma 6.3's premise. The domain size is
    /// fixed by the schedule, so injectivity plus "every address inside a span of
    /// that many cells" already forces the image to be exactly the scheduled
    /// `zhat` cells.
    ///
    /// # Errors
    /// [`NormError::ImageMismatch`] on a wrong domain length,
    /// [`NormError::AddressOutsideSpan`] on an address outside the span,
    /// [`NormError::NotInjective`] on a repeated address.
    pub fn admit(
        n_a: usize,
        delta_f: usize,
        span_start: usize,
        cells: &[usize],
    ) -> Result<Self, NormError> {
        let want = Self::span_len(n_a, delta_f);
        if cells.len() != want {
            return Err(NormError::ImageMismatch { want, got: cells.len() });
        }
        let mut seen = vec![false; want];
        for (index, &cell) in cells.iter().enumerate() {
            let pair = (index / delta_f, index % delta_f);
            let Some(offset) = cell.checked_sub(span_start) else {
                return Err(NormError::AddressOutsideSpan { pair, cell });
            };
            if offset >= want {
                return Err(NormError::AddressOutsideSpan { pair, cell });
            }
            if seen[offset] {
                return Err(NormError::NotInjective { pair, cell });
            }
            seen[offset] = true;
        }
        Ok(Self {
            n_a,
            delta_f,
            span_start,
            cells: cells.to_vec(),
        })
    }

    /// `pi(u, h)`.
    ///
    /// # Panics
    /// If `u >= n_a` or `h >= delta_f`.
    pub fn address(&self, u: usize, h: usize) -> usize {
        assert!(u < self.n_a && h < self.delta_f, "pi domain index");
        self.cells[u * self.delta_f + h]
    }

    /// The scheduled span's first cell and length.
    pub const fn span(&self) -> (usize, usize) {
        (self.span_start, self.n_a * self.delta_f)
    }

    /// `N_A`.
    pub const fn n_a(&self) -> usize {
        self.n_a
    }

    /// `delta_f`.
    pub const fn delta_f(&self) -> usize {
        self.delta_f
    }

    /// The declared addresses, in domain order.
    pub fn cells(&self) -> &[usize] {
        &self.cells
    }

    /// Whether this is Eq. (107)'s honest plane-major map, which the schedule
    /// requires of a level whose witness really was split natively.
    pub fn is_native(&self, d_a: usize) -> bool {
        *self == Self::native(self.n_a, d_a, self.delta_f, self.span_start)
    }
}

/// Both sides of Eqs. (126)/(127), as the verifier forms them.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PiBinding<R> {
    /// `C_bind`: the equation's left-hand side, read off the norm proof's final
    /// evaluations at the last range-tree point `r`.
    pub claim: R,
    /// The public coefficients of the right-hand side over the recursive witness,
    /// one entry per witness cell and zero outside the scheduled span — i.e.
    /// exactly `P_bind`'s first factor, ready for [`crate::sumcheck::fused::fuse`].
    pub weights: Vec<R>,
    /// The route's exponent form, for the schedule record.
    pub route: NormRoute,
}

/// Forms Eqs. (126)/(127) as printed.
///
/// * [`NormRoute::Direct`], Eq. (126): `eta_norm zint^(r) =
///   eta_norm sum_u eq(r,u) sum_{h<delta_f} b^h w^(j+1)(pi(u,h))`, so
///   `plane_evals = [zint^(r)]` and cell `pi(u,h)` carries `eta_norm b^h eq(r,u)`.
/// * [`NormRoute::DigitExpanded`], Eq. (127): `sum_h eta_norm^{h+1} zh^(r) =
///   sum_u sum_h eta_norm^{h+1} eq(r,u) w^(j+1)(pi(u,h))`, so `plane_evals` holds
///   all `delta_f` digit evaluations and cell `pi(u,h)` carries
///   `eta_norm^{h+1} eq(r,u)` — **no** `b^h`, because the base weighting already
///   entered through Eq. (123) and the planes are bound raw.
/// * [`NormRoute::Coefficient`]: there is no norm proof, so nothing to bind;
///   refused as a malformed request rather than silently yielding zeros.
///
/// `eta_norm` is the fresh batching challenge the verifier samples *after* these
/// evaluations are fixed (p. 70), and `r` the last range-tree point, so
/// `eq(r, .)` is over `log2(n_a)` coordinates.
///
/// # Errors
/// [`NormError::MalformedEvaluations`] if the route and the evaluation count
/// disagree, or [`NormError::DomainMismatch`] if `r` does not index `n_a` cells.
///
/// # Panics
/// If `witness_len` is below the end of the scheduled span: the map would address
/// cells that do not exist, which no equation can paper over.
pub fn pi_binding<R: Ring>(
    map: &DigitMap,
    r: &[R],
    eta_norm: R,
    base: u64,
    route: NormRoute,
    plane_evals: &[R],
    witness_len: usize,
) -> Result<PiBinding<R>, NormError> {
    let expected = match route {
        NormRoute::Direct => 1,
        NormRoute::DigitExpanded => map.delta_f,
        NormRoute::Coefficient => {
            return Err(NormError::MalformedEvaluations {
                left: plane_evals.len(),
                expected: 0,
            })
        }
    };
    if plane_evals.len() != expected {
        return Err(NormError::MalformedEvaluations {
            left: plane_evals.len(),
            expected,
        });
    }
    let bits = r.len();
    if bits >= 64 || (1usize << bits) != map.n_a {
        return Err(NormError::DomainMismatch {
            cells: map.n_a,
            point_bits: bits,
        });
    }
    let (_span_start, span_len) = map.span();
    if witness_len < span_len + map.span_start {
        panic!("the recursive witness must contain the scheduled zhat digit span");
    }
    let mut weights = vec![R::ZERO; witness_len];
    let mut claim = R::ZERO;
    match route {
        NormRoute::Direct => {
            // `eta_norm b^h`, Eq. (126)'s inner coefficient: the batching
            // challenge times the digit's place value in the response base.
            let mut place = eta_norm;
            for h in 0..map.delta_f {
                for u in 0..map.n_a {
                    let weight = place * eq_weight(r, u, bits);
                    let cell = map.address(u, h);
                    weights[cell] += weight;
                }
                place *= R::from(base);
            }
            claim = eta_norm * plane_evals[0];
        }
        NormRoute::DigitExpanded => {
            // `eta_norm^{h+1}`: positive degree in the batching challenge, which
            // is exactly what Eq. (128)'s non-cancellation argument reads.
            let mut eta_power = eta_norm;
            for h in 0..map.delta_f {
                for u in 0..map.n_a {
                    let weight = eta_power * eq_weight(r, u, bits);
                    let cell = map.address(u, h);
                    weights[cell] += weight;
                }
                claim += eta_power * plane_evals[h];
                eta_power *= eta_norm;
            }
        }
        NormRoute::Coefficient => unreachable!("rejected above"),
    }
    Ok(PiBinding {
        claim,
        weights,
        route,
    })
}

/// Eqs. (126)/(127) as an executable statement: the binding's left-hand side must
/// equal the `pi`-addressed linear combination of the committed witness cells.
///
/// This is *not* re-computing `P_bind`'s Boolean sum — that is what the fused
/// sum-check proves. It is the verifier's own read of the printed equation, and
/// the reason [`crate::sumcheck::fused::fuse`] gets an `eta_norm`-weighted
/// residual: "Both right-hand sides are public linear functions of the same
/// witness used by the relation check" (p. 71).
///
/// # Errors
/// [`NormError::BindingMismatch`] when the two sides differ, or
/// [`NormError::ImageMismatch`] when the witness is shorter than the weight table.
///
/// # Panics
/// Never: a mis-shaped witness is refused.
pub fn check_pi_identity<R: Ring>(binding: &PiBinding<R>, witness: &[R]) -> Result<(), NormError> {
    if witness.len() != binding.weights.len() {
        return Err(NormError::ImageMismatch {
            want: binding.weights.len(),
            got: witness.len(),
        });
    }
    let rhs = binding
        .weights
        .iter()
        .zip(witness)
        .fold(R::ZERO, |acc, (w, x)| acc + *w * *x);
    if rhs == binding.claim {
        Ok(())
    } else {
        Err(NormError::BindingMismatch {
            claim: binding.claim.to_u128(),
            reconstructed: rhs.to_u128(),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use algebra::ring::zq::Zq;

    type Q32 = Zq<4_294_967_197>;
    type Z1 = Zq<8_380_417>;

    const BASE: u64 = 8;
    const DELTA_F: usize = 3;

    /// Three digit planes over six response coordinates, within `|d| <= 4`.
    fn planes() -> Vec<Vec<i64>> {
        vec![
            vec![4, -3, 0, 1, -4, 2],
            vec![-4, 4, -1, 0, 3, -2],
            vec![1, -1, 4, -3, 0, 2],
        ]
    }

    fn bounds() -> Vec<u64> {
        vec![BASE / 2; DELTA_F]
    }

    #[test]
    fn integer_coordinates_and_energy_match_an_independent_computation() {
        let coords = integer_coordinates(&planes(), BASE);
        assert_eq!(coords.len(), 6);
        for (u, c) in coords.iter().enumerate() {
            let mut want = 0i64;
            for h in 0..DELTA_F {
                want += i64::try_from(BASE.pow(h as u32)).unwrap() * planes()[h][u];
            }
            assert_eq!(*c, i128::from(want), "coordinate {u}");
        }
        // Hand-computed from the fixture: the coordinates are
        //   4 - 8*4 + 64*1      =    36
        //  -3 + 8*4 - 64*1      =   -35
        //   0 - 8*1 + 64*4      =   248
        //   1 + 8*0 - 64*3      =  -191
        //  -4 + 8*3 + 64*0      =    20
        //   2 - 8*2 + 64*2      =   114
        // whose squares sum to 1296 + 1225 + 61504 + 36481 + 400 + 12996.
        assert_eq!(
            coords,
            vec![36i128, -35, 248, -191, 20, 114][..],
            "Eq. (116) coordinate by coordinate"
        );
        let energy = exact_energy(&coords).unwrap();
        let want: u128 = coords.iter().map(|c| (c * c) as u128).sum();
        assert_eq!(energy, want);
        assert_eq!(want, 113_902);
    }

    #[test]
    fn the_integer_energy_bounds_the_reduced_ring_energy() {
        // Eq. (117) with the inequality strict: a coordinate that wraps past
        // q/2 loses magnitude under centered reduction, so a ring-norm gate
        // would be weaker than the statement Akita proves.
        let big: Vec<i128> = vec![
            i128::from(Q32::MODULUS) + 3,
            -(i128::from(Q32::MODULUS) - 5),
            7,
        ];
        let reduced: Vec<Q32> = reduce_coords(&big);
        let exact = exact_energy(&big).unwrap();
        let ring = reduced_energy(&reduced).unwrap();
        assert!(ring < exact, "reduction must shrink: {ring} vs {exact}");
        assert_eq!(ring, 9 + 25 + 49);
    }

    #[test]
    fn u_dir_bounds_every_admissible_response() {
        let digit_bounds = vec![BASE / 2; DELTA_F];
        let limit = u_dir(6, BASE, &digit_bounds);
        // every digit assignment inside the certified alphabets respects it
        for trial in 0..200u64 {
            let p: Vec<Vec<i64>> = (0..DELTA_F)
                .map(|h| {
                    (0..6)
                        .map(|u| {
                            let span = (BASE / 2) as i64;
                            -span
                                + (((trial * 31 + u as u64 * 7 + h as u64 * 13) % (BASE / 2 + 1))
                                    as i64)
                        })
                        .collect()
                })
                .collect();
            let e = exact_energy(&integer_coordinates(&p, BASE)).unwrap();
            assert!(e <= limit, "trial {trial}: {e} > {limit}");
        }
        assert_eq!(limit, 6 * (4 + 8 * 4 + 64 * 4) * (4 + 8 * 4 + 64 * 4));
    }

    #[test]
    fn route_selection_follows_max_u_dir_s_max_below_q() {
        // q = 2^32 - 99: a small response is admissible directly.
        let small = u_dir(6, BASE, &[4, 4, 4]);
        assert_eq!(select(small, small, Q32::MODULUS), NormRoute::Direct);
        // a claim at or above the modulus is not
        assert_eq!(
            select(small, u128::from(Q32::MODULUS), Q32::MODULUS),
            NormRoute::DigitExpanded
        );
        assert_eq!(
            select(u128::from(Q32::MODULUS), small, Q32::MODULUS),
            NormRoute::DigitExpanded
        );
        // and on the smaller Z1 prime the same *response* is already outside the
        // direct window, which is the paper's reason for the second route
        let wide = u_dir(64, 16, &[8; 3]);
        assert_eq!(select(wide, wide, Z1::MODULUS), NormRoute::DigitExpanded);
    }

    #[test]
    fn direct_gate_names_its_refusal() {
        let coords = integer_coordinates(&planes(), BASE);
        let energy = exact_energy(&coords).unwrap();
        let d = u_dir(6, BASE, &bounds());
        assert_eq!(
            check_direct(&coords, energy, energy, d, Q32::MODULUS).unwrap(),
            energy
        );
        assert_eq!(
            check_direct(&coords, energy + 1, energy + 1, d, Q32::MODULUS),
            Err(NormError::Mismatch {
                actual: energy,
                claimed: energy + 1
            })
        );
        assert_eq!(
            check_direct(&coords, energy, energy, d, 1 << 16),
            Err(NormError::NotAdmissible {
                limit: d,
                modulus: 1 << 16
            })
        );
        assert_eq!(
            check_direct(&coords, energy, energy - 1, d, Q32::MODULUS),
            Err(NormError::NonCanonical {
                decoded: energy,
                max: energy - 1
            })
        );
    }

    #[test]
    fn digit_expanded_reconstruction_equals_the_direct_energy() {
        // Proposition 6.5 for every segmentation of the domain.
        let p = planes();
        let coords = integer_coordinates(&p, BASE);
        let energy = exact_energy(&coords).unwrap();
        for seg_len in [1usize, 2, 3, 6] {
            let segs = segments(6, seg_len);
            let claims: Vec<PairClaim<Q32>> =
                digit_pair_claims(&p, &segs, &bounds(), Q32::MODULUS).expect("admissible");
            assert_eq!(claims.len(), n_pair(segs.len(), DELTA_F));
            assert_eq!(
                reconstruct_from_pairs(&claims, &segs, &bounds(), BASE).unwrap(),
                energy,
                "seg_len {seg_len}"
            );
            assert_eq!(
                check_digit_expanded(&claims, &segs, &bounds(), BASE, energy, energy).unwrap(),
                energy
            );
        }
    }

    #[test]
    fn a_tampered_gram_claim_is_rejected_by_name() {
        let p = planes();
        let segs = segments(6, 3);
        let claims = digit_pair_claims::<Q32>(&p, &segs, &bounds(), Q32::MODULUS).unwrap();
        let energy = exact_energy(&integer_coordinates(&p, BASE)).unwrap();
        let mut tampered = claims.clone();
        tampered[2].residue += Q32::ONE;
        assert_eq!(
            check_digit_expanded(&tampered, &segs, &bounds(), BASE, energy, energy),
            Err(NormError::Mismatch {
                actual: energy + 2 * u128::from(BASE.pow(2)),
                claimed: energy
            })
        );
        // and a claim above the bound cannot ride through the reconstruction
        assert_eq!(
            check_digit_expanded(&claims, &segs, &bounds(), BASE, energy, energy - 1),
            Err(NormError::NonCanonical {
                decoded: energy,
                max: energy - 1
            })
        );
    }

    #[test]
    fn a_segment_too_wide_to_lift_is_refused() {
        // |I_t| B_h B_k >= q/2 destroys Lemma 6.4's uniqueness: the sender of a
        // wrapped residue must not be able to pass.
        let p: Vec<Vec<i64>> = (0..DELTA_F).map(|_| vec![4i64; 40]).collect();
        let bounds = vec![4u64; DELTA_F];
        let segs = segments(40, 40);
        let modulus = 137u64; // q/2 = 68 < 40*4*4 = 640
        assert!(!segment_admissible(40, 4, 4, modulus));
        assert_eq!(
            digit_pair_claims::<Q32>(&p, &segs, &bounds, modulus),
            Err(NormError::SegmentTooWide {
                len: 40,
                magnitude: 640,
                half_modulus: 68
            })
        );
        assert!(segment_admissible(1, 4, 4, modulus));
    }

    #[test]
    fn pair_ordering_is_the_canonical_one_and_complete() {
        let order = pair_order(2, 3);
        assert_eq!(order.len(), n_pair(2, 3));
        assert_eq!(n_pair(2, 3), 2 * 6);
        assert_eq!(order[0], (0, 0, 0));
        assert_eq!(order[1], (0, 0, 1));
        assert_eq!(order[2], (0, 0, 2));
        assert_eq!(order[3], (0, 1, 1));
        assert_eq!(order.last().unwrap(), &(1, 2, 2));
        // exactly the h <= k triples
        assert!(order.iter().all(|&(_, h, k)| h <= k));
        let mut seen: Vec<(usize, usize, usize)> = order.clone();
        seen.sort_unstable();
        seen.dedup();
        assert_eq!(seen.len(), order.len(), "no duplicate claim index");
    }

    #[test]
    fn padded_boolean_domain_keeps_the_response_order_and_zero_fills() {
        let coords: Vec<i128> = vec![3, -4, 5];
        let table: Vec<Q32> = pad_to_boolean::<Q32>(&coords, 8);
        assert_eq!(table.len(), 8);
        assert_eq!(table[0], Q32::from(3u64));
        assert_eq!(table[1], Q32::from(Q32::MODULUS - 4));
        assert!(table[3..].iter().all(|v| *v == Q32::ZERO));
        // the sum-check on this table squares to E_int (Eq. 120)
        let sum: Q32 = table
            .iter()
            .map(|v| v.square())
            .fold(Q32::ZERO, |a, b| a + b);
        assert_eq!(u128::from(sum.to_u128()), exact_energy(&coords).unwrap());
    }

    // --- the coefficient route: Eqs. (113) + (79), priced by the estimator ----

    #[test]
    fn delta_cert_is_eq_113_and_eq_79_is_the_product_it_feeds() {
        // `(b* - 1) (b^delta - 1)/(b - 1)` at b* = 8, b = 4, delta = 3.
        assert_eq!(delta_cert(8, 4, 3), 7 * (64 - 1) / 3);
        assert_eq!(delta_cert(8, 4, 3), 147);
        assert_eq!(coefficient_envelope(8, 4, 3), 4 * (64 - 1) / 3);
        assert_eq!(certified_challenge_difference(3), 6, "kappa_bar_1 = 2 omega");
        // Eq. (79), and p. 108's substitution eta = 4 omega Delta
        let radius = CollisionRadius::from_coefficient(6, 147).unwrap();
        assert_eq!(radius.value, 1_764, "eta_A = 2 kappa_bar_1 Delta_f^cert");
        assert_eq!(radius.value, 4 * 3 * 147, "p. 108's 4 omega Delta_f^cert");
        assert_eq!(radius.route, NormRoute::Coefficient);
        assert_eq!(radius.norm, CollisionNorm::Sup);
        assert_eq!(
            a_collision_radius(6, 147),
            Ok(1_764),
            "the free entry point and the tagged constructor agree"
        );
    }

    #[test]
    fn eq_79_is_never_looser_than_corollary_10_26_s_spelling_of_itself() {
        // Corollary 10.26 prices the same collision at `8 kappa_1 Z_inf`, i.e. with
        // twice Eq. (112)'s single-response envelope in place of Eq. (113)'s
        // difference envelope. Since `b* - 1 <= b*`, the (79) form must win whenever
        // `kappa_bar_1 = 2 kappa_1`. A schedule reaching for the looser figure would
        // over-price its own collisions, so the direction is pinned rather than
        // left to prose.
        for (base_star, base, digits, omega) in
            [(8u64, 8u64, 3usize, 1u64), (8, 4, 5, 3), (16, 8, 4, 2), (4, 4, 11, 5)]
        {
            let kappa_bar = certified_challenge_difference(omega);
            let via_79 =
                CollisionRadius::from_coefficient(kappa_bar, delta_cert(base_star, base, digits))
                    .unwrap();
            let via_corollary = CollisionRadius::coefficient_corollary(
                u128::from(omega),
                coefficient_envelope(base_star, base, digits),
            )
            .unwrap();
            assert!(
                via_79.value <= via_corollary.value,
                "{base_star}/{base}/{digits}: (79) {} > Cor 10.26 {}",
                via_79.value,
                via_corollary.value
            );
            assert_eq!(
                tighter(Some(via_corollary), Some(via_79)).unwrap(),
                via_79,
                "`tighter` must pick the (79) radius"
            );
            // p. 108's substitution, against the paper's own sentence: "its
            // coefficient-norm inner commitment is therefore queried at
            // eta_{A,j} = 4 omega_j Delta_f^cert".
            assert_eq!(
                via_79.value,
                4 * u128::from(omega) * delta_cert(base_star, base, digits)
            );
        }
    }

    #[test]
    fn radius_products_refuse_rather_than_saturate() {
        assert_eq!(
            CollisionRadius::from_coefficient(u128::MAX, 3),
            Err(NormError::RadiusOverflow)
        );
        assert_eq!(
            CollisionRadius::coefficient_corollary(u128::MAX, 2),
            Err(NormError::RadiusOverflow)
        );
        // Corollary 10.26's Euclidean radius, eta^2 = 64 Gamma^2 S_max
        let euclid = CollisionRadius::from_euclidean(4, 100).unwrap();
        assert_eq!(euclid.value, 64 * 4 * 100);
        assert_eq!(euclid.norm, CollisionNorm::Two);
        assert_eq!(
            CollisionRadius::from_euclidean(u128::MAX / 32, 64),
            Err(NormError::RadiusOverflow)
        );
    }

    #[test]
    fn an_l2_radius_becomes_a_coordinate_bound_by_rounding_up() {
        // 25600 is a perfect square and 25601 is not; the bound must not round
        // down to 160, which would claim hardness the radius does not carry.
        let exact = CollisionRadius::from_euclidean(4, 100).unwrap();
        assert_eq!(exact.coordinate_bound().unwrap(), 160);
        let loose = CollisionRadius {
            route: NormRoute::DigitExpanded,
            norm: CollisionNorm::Two,
            value: 25601,
        };
        assert_eq!(loose.coordinate_bound().unwrap(), 161);
        let sup = CollisionRadius::from_coefficient(6, 147).unwrap();
        assert_eq!(
            sup.coordinate_bound().unwrap(),
            1_764,
            "already a coordinate bound"
        );
    }

    /// An estimator that cannot price anything, to pin how `None` is treated.
    struct Silent;
    impl MsisEstimator for Silent {
        fn core_svp_bits(&self, _: &MsisInstance, _: &CollisionRadius) -> Option<u32> {
            None
        }
    }

    /// A `B`-shaped instance at a real ring dimension. The example's own `A` is
    /// `1 x 2` at `d = 4`, whose lattice is so small that `sis_block_size` answers
    /// with its `mu = 50` floor for every radius a schedule ever prices — so it
    /// cannot show the estimator's radius sensitivity, which is what this test is
    /// about. At `d = 256` the floor is far below the answer and it can.
    fn priced_a() -> MsisInstance {
        MsisInstance {
            role: "A",
            modulus: Q32::MODULUS,
            ring_dim: 256,
            rows: 2,
            cols: 4,
        }
    }

    /// The example's toy `A`, whose price saturates at the estimator's floor.
    fn toy_a() -> MsisInstance {
        MsisInstance {
            role: "A",
            modulus: Q32::MODULUS,
            ring_dim: 4,
            rows: 1,
            cols: 2,
        }
    }

    #[test]
    fn the_estimator_prices_a_tighter_radius_as_the_harder_instance() {
        let inst = priced_a();
        assert_eq!(inst.flat_rows(), 512);
        assert_eq!(inst.flat_cols(), 1024, "n m d flattened (Eq. 66's reading)");
        let est = CoreSvpEstimator;
        let small = CollisionRadius::from_coefficient(1, 100).unwrap();
        let big = CollisionRadius::from_coefficient(1, 100_000_000).unwrap();
        let tight = est
            .core_svp_bits(&inst, &small)
            .expect("the estimator prices a 100-wide radius");
        let loose = est
            .core_svp_bits(&inst, &big)
            .expect("and the 10^8-wide one too");
        assert!(
            tight > loose,
            "{tight} bits at radius {} vs {loose} at {}",
            small.value,
            big.value
        );
        // the contract is exactly that monotone gate
        let contract = SecurityContract {
            min_bits: (tight + loose) / 2,
        };
        assert!(contract.admits(&est, &inst, &small));
        assert!(!contract.admits(&est, &inst, &big));
        // an estimator that cannot price never admits, rather than admitting at zero
        assert!(!SecurityContract { min_bits: 0 }.admits(&Silent, &inst, &small));
        // ... and at the example's toy ranks it *does* saturate, so no route can be
        // discriminated by hardness there. Recorded rather than hidden: a schedule
        // that claimed a security level from these dimensions would be reading a
        // number that is the estimator's floor, not a property of its radius.
        let toy = toy_a();
        let floor_small = est.core_svp_bits(&toy, &small).unwrap();
        let floor_big = est.core_svp_bits(&toy, &big).unwrap();
        assert_eq!(
            floor_small, floor_big,
            "the toy instance floors both radii at the same {floor_small} bits"
        );
    }

    #[test]
    fn a_declared_radius_must_reach_what_the_fold_earned() {
        let inst = toy_a();
        let earned = CollisionRadius::from_coefficient(6, 147).unwrap();
        let est = CoreSvpEstimator;
        let priced = est.core_svp_bits(&inst, &earned).unwrap();
        // legal: the exact figure, under a contract the toy instance can meet
        assert_eq!(
            DeclaredRadius {
                declared: 1_764,
                earned
            }
            .check(&est, &inst, &SecurityContract { min_bits: 0 }),
            Ok(priced)
        );
        // legal arithmetic, refused contract
        assert_eq!(
            DeclaredRadius {
                declared: 1_764,
                earned
            }
            .check(&est, &inst, &SecurityContract {
                min_bits: priced + 1
            }),
            Err(NormError::ContractNotMet {
                bits: priced,
                min_bits: priced + 1
            })
        );
        // illegal: one short of the earned bound. Upward rounding is the only slack
        // p. 108 grants, and this is the direction that matters.
        assert_eq!(
            DeclaredRadius {
                declared: 1_763,
                earned
            }
            .check(&est, &inst, &SecurityContract { min_bits: 0 }),
            Err(NormError::RadiusUnderDeclared {
                declared: 1_763,
                earned: 1_764
            })
        );
        // an unpriceable query is refused as `NotPriced`, not as a hardness of zero
        assert_eq!(
            DeclaredRadius {
                declared: 10_000,
                earned
            }
            .check(&Silent, &inst, &SecurityContract { min_bits: 0 }),
            Err(NormError::NotPriced)
        );
        // an upward-rounded declaration is accepted and priced at what it declares
        let rounded = DeclaredRadius {
            declared: 2000,
            earned,
        };
        assert_eq!(
            rounded.check(&est, &inst, &SecurityContract { min_bits: 0 }),
            Ok(est
                .core_svp_bits(
                    &inst,
                    &CollisionRadius {
                        route: NormRoute::Coefficient,
                        norm: CollisionNorm::Sup,
                        value: 2000
                    }
                )
                .unwrap())
        );
    }

    #[test]
    fn the_coefficient_route_certifies_no_energy_statement() {
        assert!(!NormRoute::Coefficient.certifies_energy());
        assert!(NormRoute::Direct.certifies_energy());
        assert!(NormRoute::DigitExpanded.certifies_energy());
        // and `select`, which decides between the two *proofs* of Eq. (118), can
        // never return it: the coefficient route is a schedule choice, not an
        // outcome of Eq. (119)'s window.
        for (u, s, q) in [
            (1u128, 1u128, 65537u64),
            (u128::from(u64::MAX), 7, 65537),
            (5, u128::from(u64::MAX), 65537),
        ] {
            assert_ne!(select(u, s, q), NormRoute::Coefficient);
        }
    }

    // --- Eqs. (126)-(128): the pi binding ------------------------------------

    /// Eight response coordinates, three digit planes, digits inside `A_8`.
    fn cells_fixture() -> Vec<Vec<i64>> {
        vec![
            vec![4, -3, 0, 1, -4, 2, -1, 3],
            vec![-4, 4, -1, 0, 3, -2, 1, -3],
            vec![1, -1, 4, -3, 0, 2, -4, 1],
        ]
    }

    /// The same digits laid out plane-major, i.e. in Eq. (107)'s witness order.
    fn witness_of(planes: &[Vec<i64>]) -> Vec<Q32> {
        planes
            .iter()
            .flat_map(|p| p.iter().map(|&d| residue(d)))
            .collect()
    }

    fn residue(d: i64) -> Q32 {
        Q32::from(i128::from(d).rem_euclid(i128::from(Q32::MODULUS)) as u64)
    }

    /// `sum_u eq(r,u) v_u`: an independent reading of the multilinear extension of
    /// the length-`2^|r|` table `v` at `r`.
    fn eq_contraction(r: &[Q32], v: &[Q32]) -> Q32 {
        (0..v.len()).fold(Q32::ZERO, |acc, u| {
            acc + eq_weight(r, u, r.len()) * v[u]
        })
    }

    #[test]
    fn digit_map_native_is_eq_107_and_plane_major_is_eq_109() {
        let map = DigitMap::native(8, 4, 3, 0);
        assert_eq!(DigitMap::span_len(8, 3), 24);
        assert_eq!(map.span(), (0, 24));
        assert_eq!(map.n_a(), 8);
        assert_eq!(map.delta_f(), 3);
        for u in 0..8usize {
            for h in 0..3usize {
                let (j, k) = (u / 4, u % 4);
                assert_eq!(
                    map.address(u, h),
                    crate::pcs::fold_geom::address(j, 0, h, k, 1, 3, 4),
                    "(u,h) = ({u},{h})"
                );
                // "the coefficient coordinate changes first, then the digit, then
                // the native block": item `j` is outermost, so item 1's digits are
                // a whole `delta_f * d_A` further along, not one plane over.
                assert_eq!(map.address(u, h), (j * 3 + h) * 4 + k, "(u,h) = ({u},{h})");
            }
        }
        assert!(map.is_native(4));
        // the plane-major reading addresses the same span in the other order
        let planes = DigitMap::plane_major(8, 3, 0);
        for u in 0..8usize {
            for h in 0..3usize {
                assert_eq!(planes.address(u, h), h * 8 + u);
            }
        }
        assert!(!planes.is_native(4));
        assert_eq!(planes.span(), (0, 24));
        // the domain order is `u * delta_f + h`, so consecutive entries of the
        // declaration step through the *planes*, which is what makes the two
        // readings visibly different maps
        assert_eq!(&planes.cells()[..6], &[0, 8, 16, 1, 9, 17][..]);
        assert_eq!(&map.cells()[..6], &[0, 4, 8, 1, 5, 9][..]);
        // both are bijections onto the scheduled span, so both admit
        assert_eq!(DigitMap::admit(8, 3, 0, planes.cells()), Ok(planes.clone()));
        assert_eq!(DigitMap::admit(8, 3, 0, map.cells()), Ok(map.clone()));
        assert_ne!(map.cells(), planes.cells(), "and they are different maps");
        // a non-zero span offset shifts every address and nothing else
        let shifted = DigitMap::plane_major(8, 3, 10);
        assert_eq!(shifted.address(3, 2), 10 + 2 * 8 + 3);
        assert_eq!(
            DigitMap::admit(8, 3, 10, shifted.cells()),
            Ok(shifted),
            "the span is a schedule parameter, not a prover's claim"
        );
    }

    #[test]
    fn a_declared_map_must_be_a_bijection_onto_the_scheduled_span() {
        let honest = DigitMap::plane_major(8, 3, 0);
        assert_eq!(
            DigitMap::admit(8, 3, 0, honest.cells()),
            Ok(honest.clone()),
            "the honest declaration re-admits"
        );
        // two response coordinates reading one cell
        let mut doubled = honest.cells().to_vec();
        doubled[5] = doubled[0];
        assert_eq!(
            DigitMap::admit(8, 3, 0, &doubled),
            Err(NormError::NotInjective {
                pair: (1, 2),
                cell: 0
            })
        );
        // an address outside the scheduled span, in either direction
        let mut outside = honest.cells().to_vec();
        outside[7] = 24;
        assert_eq!(
            DigitMap::admit(8, 3, 0, &outside),
            Err(NormError::AddressOutsideSpan {
                pair: (2, 1),
                cell: 24
            })
        );
        let mut below = honest.cells().to_vec();
        below[0] = 9;
        assert_eq!(
            DigitMap::admit(8, 3, 10, &below),
            Err(NormError::AddressOutsideSpan {
                pair: (0, 0),
                cell: 9
            })
        );
        // and a domain the schedule does not fix
        assert_eq!(
            DigitMap::admit(8, 3, 0, &honest.cells()[..23]),
            Err(NormError::ImageMismatch { want: 24, got: 23 })
        );
    }

    #[test]
    fn eq_126_holds_for_the_honest_map_and_breaks_for_a_permuted_one() {
        let planes = cells_fixture();
        let coords = integer_coordinates(&planes, BASE);
        let witness = witness_of(&planes);
        let map = DigitMap::plane_major(8, 3, 0);
        let r: Vec<Q32> = vec![
            Q32::from(3u64),
            Q32::from(Q32::MODULUS - 7),
            Q32::from(11u64),
        ];
        let eta = Q32::from(5u64);
        // the norm proof's single final evaluation, `zint^(r)`
        let zint = pad_to_boolean::<Q32>(&coords, 8);
        let evals = [eq_contraction(&r, &zint)];
        let binding =
            pi_binding(&map, &r, eta, BASE, NormRoute::Direct, &evals, witness.len())
                .expect("the direct route owes one evaluation");
        assert_eq!(binding.claim, eta * evals[0], "Eq. (126)'s left side");
        assert_eq!(binding.route, NormRoute::Direct);
        check_pi_identity(&binding, &witness).expect("the honest map binds");
        // ... and the right side is the paper's own sum, rebuilt here from the
        // reconstructed integers rather than through `pi`, so the test is not a
        // restatement of the implementation.
        let rebuilt: Vec<Q32> = coords
            .iter()
            .map(|&z| residue(i64::try_from(z).unwrap()))
            .collect();
        assert_eq!(binding.claim, eta * eq_contraction(&r, &rebuilt));

        // A transposition is still a bijection onto the scheduled span, so it
        // re-admits and nothing structural can see it. Eq. (126) does see it,
        // which is exactly why the binding is a check in its own right.
        let mut swapped = map.cells().to_vec();
        swapped.swap(0, 1);
        let permuted = DigitMap::admit(8, 3, 0, &swapped).expect("still a bijection");
        assert!(!permuted.is_native(4));
        let broken =
            pi_binding(&permuted, &r, eta, BASE, NormRoute::Direct, &evals, witness.len())
                .unwrap();
        let wrong = broken
            .weights
            .iter()
            .zip(&witness)
            .fold(Q32::ZERO, |a, (w, x)| a + *w * *x);
        assert_ne!(wrong, broken.claim, "the transposition must bite");
        assert_eq!(
            check_pi_identity(&broken, &witness),
            Err(NormError::BindingMismatch {
                claim: broken.claim.to_u128(),
                reconstructed: wrong.to_u128(),
            })
        );
        // a one-off claim is refused too, so the check is not only about the map
        let lying = PiBinding {
            claim: binding.claim + Q32::ONE,
            weights: binding.weights.clone(),
            route: NormRoute::Direct,
        };
        assert_eq!(
            check_pi_identity(&lying, &witness),
            Err(NormError::BindingMismatch {
                claim: lying.claim.to_u128(),
                reconstructed: binding.claim.to_u128(),
            })
        );
        // and a witness that is not the one the weights were formed over
        assert_eq!(
            check_pi_identity(&binding, &witness[..16]),
            Err(NormError::ImageMismatch { want: 24, got: 16 })
        );
    }

    #[test]
    fn eq_127_binds_the_planes_with_eta_powers_not_the_response_base() {
        let planes = cells_fixture();
        let witness = witness_of(&planes);
        let map = DigitMap::plane_major(8, 3, 0);
        let r: Vec<Q32> = vec![
            Q32::from(3u64),
            Q32::from(Q32::MODULUS - 7),
            Q32::from(11u64),
        ];
        let eta = Q32::from(5u64);
        let evals: Vec<Q32> = planes
            .iter()
            .map(|p| eq_contraction(&r, &witness_of(&[p.clone()])))
            .collect();
        let binding = pi_binding(&map, &r, eta, BASE, NormRoute::DigitExpanded, &evals, 24)
            .expect("the expanded route owes delta_f evaluations");
        // the printed weight at cell pi(u,h) is `eta^(h+1) eq(r,u)`, with no b^h
        for u in 0..8usize {
            for h in 0..3usize {
                assert_eq!(
                    binding.weights[map.address(u, h)],
                    eta.pow((h + 1) as u64) * eq_weight(&r, u, 3),
                    "weight at pi({u},{h})"
                );
            }
        }
        assert_eq!(
            binding.claim,
            (0..3).fold(Q32::ZERO, |a, h| a + eta.pow((h + 1) as u64) * evals[h])
        );
        check_pi_identity(&binding, &witness).expect("Eq. (127) closes honestly");
        // outside the span there is nothing to bind, so the weights are zero
        assert!(binding.weights[..24].iter().any(|w| *w != Q32::ZERO));
        assert_eq!(binding.weights.len(), 24);
        // ... and the two routes really do bind different things: Eq. (126)'s
        // weights fold the response base in, Eq. (127)'s do not.
        let direct = pi_binding(&map, &r, eta, BASE, NormRoute::Direct, &[evals[0]], 24).unwrap();
        assert_ne!(direct.weights, binding.weights);
        assert_ne!(direct.claim, binding.claim);
    }

    #[test]
    fn a_binding_request_the_route_cannot_make_is_refused() {
        let map = DigitMap::plane_major(8, 3, 0);
        let r: Vec<Q32> = vec![Q32::ONE, Q32::from(2u64), Q32::from(3u64)];
        let eta = Q32::from(5u64);
        // the coefficient route has no norm proof, so there is nothing to bind:
        // refusing is the answer, not a weight table of zeros
        assert_eq!(
            pi_binding(&map, &r, eta, BASE, NormRoute::Coefficient, &[], 24),
            Err(NormError::MalformedEvaluations {
                left: 0,
                expected: 0
            })
        );
        // one evaluation short of the planes Eq. (127) reads
        assert_eq!(
            pi_binding(&map, &r, eta, BASE, NormRoute::DigitExpanded, &[eta], 24),
            Err(NormError::MalformedEvaluations {
                left: 1,
                expected: 3
            })
        );
        // ... and one too many for Eq. (126), which binds a single extension
        assert_eq!(
            pi_binding(&map, &r, eta, BASE, NormRoute::Direct, &[eta, eta], 24),
            Err(NormError::MalformedEvaluations {
                left: 2,
                expected: 1
            })
        );
        // a point that does not index the response domain
        assert_eq!(
            pi_binding(&map, &r[..2], eta, BASE, NormRoute::Direct, &[eta], 24),
            Err(NormError::DomainMismatch {
                cells: 8,
                point_bits: 2
            })
        );
    }

    /// The span must really be inside the witness: an address with no cell behind
    /// it is a schedule bug, not a prover's lie, so it is a hard refusal.
    #[test]
    #[should_panic(expected = "scheduled zhat digit span")]
    fn a_witness_shorter_than_the_scheduled_span_panics() {
        let map = DigitMap::plane_major(8, 3, 0);
        let r: Vec<Q32> = vec![Q32::ONE, Q32::from(2u64), Q32::from(3u64)];
        pi_binding(&map, &r, Q32::ONE, BASE, NormRoute::Direct, &[Q32::ONE], 23).unwrap();
    }

    /// The two halves meet: the weight table [`pi_binding`] returns is a legal
    /// sum-check factor, Eq. (128) adds it to an ordinary relation row, and the
    /// fused statement closes — while a false `C_bind` inside the fused claim is
    /// still refused, which is the only thing the fusion had better buy.
    #[test]
    fn eq_128_fuses_the_binding_summand_into_an_ordinary_relation_row() {
        use crate::sumcheck::fused;
        use algebra::crypto::xof::Shake256Xof;

        let planes = cells_fixture();
        let cells = witness_of(&planes);
        let map = DigitMap::plane_major(8, 3, 0);
        let r: Vec<Q32> = vec![
            Q32::from(3u64),
            Q32::from(Q32::MODULUS - 7),
            Q32::from(11u64),
        ];
        let eta = Q32::from(5u64);
        let zint = pad_to_boolean::<Q32>(&integer_coordinates(&planes, BASE), 8);
        let evals = [eq_contraction(&r, &zint)];
        // Eq. (128) is one sum-check over one cube, so the witness is padded to one
        let mut witness = cells;
        witness.resize(32, Q32::ZERO);
        let binding =
            pi_binding(&map, &r, eta, BASE, NormRoute::Direct, &evals, witness.len()).unwrap();
        check_pi_identity(&binding, &witness).expect("Eq. (126) closes on the padded witness");
        let bind = fused::Summand {
            factors: vec![binding.weights.clone(), witness.clone()],
            terms: vec![vec![0, 1]],
            claimed: binding.claim,
        };
        assert_eq!(
            bind.boolean_sum(),
            binding.claim,
            "zero padding keeps the Boolean sum, so the fused claim survives it"
        );
        // an "ordinary relation" row, whose claim reads no eta_norm at all
        let public: Vec<Q32> = (0..32u64).map(Q32::from).collect();
        let base = fused::Summand {
            factors: vec![public.clone(), witness.clone()],
            terms: vec![vec![0, 1]],
            claimed: Q32::ZERO,
        };
        let base = fused::Summand {
            claimed: base.boolean_sum(),
            ..base
        };
        let combined = fused::fuse(&base, &bind).expect("one cube");
        assert_eq!(
            combined.claimed,
            base.claimed + binding.claim,
            "C_base + C_bind"
        );
        assert_eq!(combined.terms, vec![vec![0, 1], vec![2, 3]], "renumbered P_bind");
        let mut p = fused::FsDegChallenger::<Shake256Xof, Q32>::new(b"akita/128");
        let proof = combined.prove(&mut p);
        let mut v = fused::FsDegChallenger::<Shake256Xof, Q32>::new(b"akita/128");
        assert!(combined.accepts(&proof, &mut v), "the honest fused run closes");
        // ... and a lie about C_bind is not admitted by hiding it in the sum
        let lie = fused::Summand {
            claimed: combined.claimed + Q32::ONE,
            ..combined.clone()
        };
        let mut p2 = fused::FsDegChallenger::<Shake256Xof, Q32>::new(b"akita/128");
        let lied = lie.prove(&mut p2);
        let mut v2 = fused::FsDegChallenger::<Shake256Xof, Q32>::new(b"akita/128");
        assert!(
            !lie.accepts(&lied, &mut v2),
            "fusing a false binding into a true relation must not admit it"
        );
    }
}
