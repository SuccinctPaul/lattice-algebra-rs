//! Exact-integer squared Euclidean norm gate (Z5; the slack-free route).
//!
//! The crate's other shortness arguments are **not** this one:
//! [`crate::shortness::balanced`] gates `‖·‖∞` over digit splits,
//! [`crate::shortness::gadget`] gates an approximate linear check with
//! provable slack, and [`crate::shortness::projection`] certifies `l2`
//! *approximately* through a Johnson–Lindenstrauss image with the GHL21
//! `√(128/30)` gap. Akita (eprint 2026/1983 §6.2) states outright that it
//! uses **no JL projection**: it checks the exact integer identity
//!
//! ```text
//! E_int(z) = Σᵤ (centered lift of zᵤ)²  ==  E_resp   ∧   E_resp ≤ S_max
//! ```
//!
//! on canonical fixed-width integers, rejecting a non-canonical or oversized
//! response outright. That is the "slack-free exact-ℓ2" direction survey §3
//! trend 1 identifies, and it is what tightens MSIS parameters. This module
//! is the **gate**; assembling it into a sumcheck range tree the way Akita's
//! equation (125) fuses it is scheme work and belongs in an example.
//!
//! # Direct route and its precondition
//!
//! The claimed norm is an element the verifier compares as an integer, so
//! the direct route is exact only while the quantity stays below the
//! modulus — otherwise two different integer norms are the same ring
//! element and the claim is ambiguous (Akita equation (119), which also
//! bounds `S_max` below `q`). Past that window the norm has to be assembled
//! from digit-plane Gram segments — [`exact_l2_gate_gram`], which is
//! [`Route::DigitGram`]. [`exact_l2_gate`] is the *direct* gate and still
//! refuses rather than approximating, so no scheme can silently take the
//! direct route beyond its validity; [`exact_l2_gate_routed`] is the entry
//! point that switches routes.
//!
//! # The digit-plane Gram route, transcribed
//!
//! Verbatim from eprint 2026/1983 §6.2 "Certifying the ℓ2 Response Norm"
//! (pp. 68–70), with the equation numbers the paper prints. The response
//! digits live in `δ_f` planes over `N_A = m_A d_A` base-field coordinates,
//! and `π : [N_A] × [δ_f] → [|w^(j+1)|]` addresses a coordinate's digit in
//! the committed witness:
//!
//! ```text
//! z_u^Z := Σ_{h<δ_f} b^h w^(j+1)(π(u,h))                          (116)
//! E_int(ẑ) := Σ_{u<N_A} (z_u^Z)²  satisfies  ‖z‖²_{2,coef} ≤ E_int(ẑ)   (117)
//! E_int(ẑ) = E_resp  ∧  E_resp ≤ S_max                            (118)
//! U_dir := N_A (Σ_{h<δ_f} b^h B_dig,h)²                           (119)
//! ```
//!
//! "The direct route is admissible only when `max{U_dir, S_max} < q`" (p. 69,
//! above their Eq. 120), and "The transcript carries `E_resp` in the canonical
//! fixed-width unsigned encoding determined by `S_max`. The verifier rejects
//! any noncanonical encoding and any decoded value outside `[0, S_max]`"
//! (p. 68) — which is [`decode_energy`], not a field element: the budget above
//! `q` is carried as an *independent integer*, so widening `S_max` never
//! widens the encoding through the modulus.
//!
//! When the norm can exceed `q`, "one field identity no longer determines its
//! integer value", so the norm is expanded into digit-plane inner products
//! over public consecutive segments `I_t` of `[N_A]`:
//!
//! ```text
//! p_{t,h,k} := Σ_{u∈I_t} z_h(u) z_k(u) ∈ F_q                      (121)
//! |I_t| · B_dig,h · B_dig,k < q/2      for every (t,h,k), h ≤ k   (122)
//! E_resp = Σ_t ( Σ_h b^{2h} p̄_{t,h,h} + 2 Σ_{h<k} b^{h+k} p̄_{t,h,k} )  (123)
//! N_pair = |{I_t}| · δ_f(δ_f + 1)/2                               (124)
//! ```
//!
//! with `p̄` the unique centered lift into `(−q/2, q/2)`. Lemma 6.4 (p. 70)
//! justifies the lift — "the triangle inequality and the digit bounds give
//! `|Σ_{u∈I_t} z_h(u)z_k(u)| ≤ |I_t| B_dig,h B_dig,k < q/2`, [and] there is
//! exactly one integer in `(−q/2, q/2)` with the claimed residue" — and
//! Proposition 6.5 ("expand `Σ_{u∈I_t}(Σ_h b^h z_h(u))²` and separate the
//! diagonal and off-diagonal digit-plane pairs") is [`reconstruct_energy`].
//! The paper's own account of what happens without (122) is the reason
//! [`gram_claims`] refuses instead of guessing: "The verifier … rejects if
//! they differ, **if the reconstruction is negative**, or if it exceeds
//! `S_max`" (p. 69).
//!
//! Fusion, which is scheme work and lives in `examples/akita.rs`, is their
//! Eq. (125): `Σ_x (P_rng(x) + ζ_norm P_norm(x)) = C_rng + ζ_norm C_norm` with
//! `P_norm(x) := z_int(x)²` in the direct case and
//! `P_norm(x) := Σ_{t,h≤k} ζ_pair^idx(t,h,k) 1_{I_t}(x) z_h(x) z_k(x)` in the
//! digit-expanded one, where "the direct norm term has degree two. Each
//! digit-pair term has degree three after its segment indicator is included."
//!
//! # Why the centered lift is the whole point
//!
//! A residue `q − 5` and the integer `-5` are the same ring element, but
//! their squares differ by `≈ q²`. Everything here lifts to the canonical
//! centered representative first, so the norm is a statement about integers.
//! Conversely, a witness whose integer norm exceeds `q` cannot pass under an
//! admissible bound even when the prover sends the residue `E_int mod q`,
//! which is exactly the wraparound the gate must not swallow.

use algebra::ring::traits::CenteredRing;
use algebra::ring::Ring;
use alloc::vec::Vec;
use core::fmt;

/// Why an exact-`l2` check refused to decide.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExactL2Error {
    /// The bound reaches the modulus, so the claim is ambiguous mod `q` and
    /// the digit-expanded route is required.
    NotAdmissible {
        /// The bound that failed to stay under the modulus.
        limit: u128,
        /// The modulus it must stay under.
        modulus: u64,
    },
    /// The squared-norm accumulation exceeded the `u128` window. Never
    /// wraps: an unprovable check is a refusal, not a pass.
    Overflow,
    /// The recomputed exact norm differs from the claimed response.
    Mismatch {
        /// What the witness actually squares to.
        actual: u128,
        /// What was claimed.
        claimed: u128,
    },
    /// The exact norm is correct arithmetic but exceeds the allowed bound.
    BoundExceeded {
        /// The computed squared norm.
        norm_sq: u128,
        /// The permitted squared bound `S_max`.
        max: u128,
    },
    /// The transmitted norm is not the canonical fixed-width unsigned encoding
    /// Eq. (118) prescribes, or decodes outside `[0, S_max]`.
    NonCanonical {
        /// What was decoded, when the length at least allowed decoding.
        decoded: u128,
        /// The public ceiling the encoding must fit under.
        max: u128,
    },
    /// A Gram segment is too long to lift uniquely, so Eq. (122) fails and
    /// Lemma 6.4's hypothesis is gone: the residue no longer determines an
    /// integer and the digit-expanded route must not be taken.
    SegmentTooWide {
        /// Segment length `|I_t|`.
        len: usize,
        /// `|I_t| B_dig,h B_dig,k`, the integer the residue would have to represent.
        magnitude: u128,
        /// `q/2`, the ceiling it must stay under.
        half_modulus: u128,
    },
}

impl fmt::Display for ExactL2Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ExactL2Error::NotAdmissible { limit, modulus } => write!(
                f,
                "direct route needs S_max < q, got {limit} against q = {modulus}"
            ),
            ExactL2Error::Overflow => write!(f, "squared-norm sum overflowed u128"),
            ExactL2Error::Mismatch { actual, claimed } => {
                write!(f, "claimed E_resp {claimed}, exact norm is {actual}")
            }
            ExactL2Error::BoundExceeded { norm_sq, max } => {
                write!(f, "exact norm {norm_sq} exceeds the bound {max}")
            }
            ExactL2Error::NonCanonical { decoded, max } => {
                write!(f, "decoded norm {decoded} is outside [0, {max}]")
            }
            ExactL2Error::SegmentTooWide {
                len,
                magnitude,
                half_modulus,
            } => write!(
                f,
                "segment of {len} cells spans {magnitude} >= q/2 = {half_modulus}, \
                 so its residue is not uniquely liftable"
            ),
        }
    }
}

/// The largest centered-lift magnitude among `coefs`.
pub fn max_magnitude<R: CenteredRing>(coefs: &[R]) -> u64 {
    coefs.iter().map(|c| c.abs_infinity()).max().unwrap_or(0)
}

/// Whether the direct route is admissible for this squared bound: `S_max`
/// must stay under the modulus, else an integer norm and that norm plus `q`
/// are indistinguishable to the claim.
pub fn direct_route_admissible<R: CenteredRing>(s_max: u128) -> bool {
    s_max < R::MODULUS as u128
}

/// The exact integer squared norm `Σ (centered lift)²`, accumulated in
/// `u128` with checked arithmetic.
///
/// # Errors
/// [`ExactL2Error::Overflow`] if the sum cannot be represented.
pub fn squared_norm<R: CenteredRing>(coefs: &[R]) -> Result<u128, ExactL2Error> {
    squared_norm_of_ints(&coefs.iter().map(|c| c.centered()).collect::<Vec<_>>())
}

/// The same checked-`u128` accumulation of [`squared_norm`] over coordinates
/// that are *already* integers — the shared seam behind both gates.
///
/// This exists because a protocol response is not always a ring vector: a
/// rounded commitment (Jindo eprint 2026/044 Fig. 3 step 3, p. 9:
/// `t̂ₖ = ⌊tₖ/B_t⌉`) is a vector of plain integers whose entries are bounded by
/// `q/(2B_t)` and carry no modular ambiguity at all. Routing it through the
/// same accumulator is what keeps the two gates from being able to disagree
/// about what a squared norm is.
///
/// # Errors
/// [`ExactL2Error::Overflow`] if the sum cannot be represented.
pub fn squared_norm_of_ints(values: &[i64]) -> Result<u128, ExactL2Error> {
    let mut acc: u128 = 0;
    for v in values {
        let v = i128::from(*v);
        let sq = u128::try_from(v.checked_mul(v).ok_or(ExactL2Error::Overflow)?)
            .map_err(|_| ExactL2Error::Overflow)?;
        acc = acc.checked_add(sq).ok_or(ExactL2Error::Overflow)?;
    }
    Ok(acc)
}

/// `⌈√n⌉`: the smallest `r` with `r² ≥ n`, from the platform's own floor root.
/// Rounding **up** is what lets a norm gate built from exact squared norms be
/// compared against an integer bound without ever becoming *more* permissive
/// than the real-number inequality it stands for.
///
/// [`crate::pcs::jl_compose::isqrt_ceil`] is the same three lines for the same
/// reason; both are written against `u128::isqrt` so there is no second square
/// root algorithm to drift.
pub fn isqrt_ceil(n: u128) -> u128 {
    let r = n.isqrt();
    // `r` is the *floor* root, so `r² ≤ n` and this multiply cannot overflow.
    if r * r == n {
        r
    } else {
        r + 1
    }
}

/// The gate shape Jindo's Fig. 7 lines 7–8 (p. 11) print: a **sum of `ℓ2`
/// norms** over several response parts,
///
/// ```text
/// ‖p₀‖₂ + ‖p₁‖₂ + ⋯ + ‖p_{k−1}‖₂ ≤ max
/// ```
///
/// — not a sum of *squares*. The three proofs of those two lines decide it the
/// same way: p. 18 (B.6) bounds each part by its own `ℓ∞` bound times
/// `√(dimension)` and *adds the roots*, p. 19 (B.8) and p. 20 (B.9) write the
/// displayed inequality with plain subscript-2 norms on the left of a bound
/// that is itself a sum of roots. The superscript-2 transcription some readers
/// bring away from the figure is the `ℓ2` subscript, not an exponent: the two
/// `2`s that do appear on `‖r‖` and `‖s‖` sit at the subscript baseline, and a
/// squared reading would make the paper's own arithmetic
/// (`B = b√((m₁+1)d) + B_χ√((µ+ν)d) + B_t√(µd)`, Theorem 3, p. 10) type-check
/// against nothing.
///
/// Each part is measured as `⌈‖pᵢ‖₂⌉` from its exact squared norm, so the sum
/// the gate compares is an **upper bound** on the real one: the gate is
/// conservative (it can reject a transcript whose true sum is at most `max` by
/// less than one unit per part, never the other way).
///
/// Unlike [`exact_l2_gate`] there is no `S_max < q` admissibility window here,
/// because nothing is *transmitted as a field element* for the verifier to
/// disambiguate: the verifier lifts each part to its centered representative
/// (the paper's representative convention, §3.1 p. 6: "`Z ∩ (−q/2, q/2]`") and
/// does integer arithmetic on it. A part whose coordinates are outside the
/// centered window is therefore a caller error, not a wraparound — which is why
/// the parts are `i64` here rather than ring elements.
///
/// Returns the bounded integer sum.
///
/// # Errors
/// [`ExactL2Error::Overflow`] if a part's squared norm or the sum leaves
/// `u128`, [`ExactL2Error::BoundExceeded`] if the sum exceeds `max`.
pub fn norm_sum_gate(parts: &[&[i64]], max: u128) -> Result<u128, ExactL2Error> {
    let mut sum: u128 = 0;
    for part in parts {
        let squared = squared_norm_of_ints(part)?;
        sum = sum
            .checked_add(isqrt_ceil(squared))
            .ok_or(ExactL2Error::Overflow)?;
    }
    if sum > max {
        return Err(ExactL2Error::BoundExceeded { norm_sq: sum, max });
    }
    Ok(sum)
}

/// The exact-`l2` gate: recompute `E_int`, require it to equal the claimed
/// response and to sit within the bound, and refuse to decide when the
/// direct route is not admissible.
///
/// Returns the verified exact squared norm.
///
/// # Errors
/// [`ExactL2Error::NotAdmissible`] outside the validity window,
/// [`ExactL2Error::Overflow`] beyond `u128`, [`ExactL2Error::Mismatch`] or
/// [`ExactL2Error::BoundExceeded`] for a false or oversized claim.
pub fn exact_l2_gate<R: CenteredRing>(
    coefs: &[R],
    claimed: u128,
    s_max: u128,
) -> Result<u128, ExactL2Error> {
    if !direct_route_admissible::<R>(s_max) {
        return Err(ExactL2Error::NotAdmissible {
            limit: s_max,
            modulus: R::MODULUS,
        });
    }
    let actual = squared_norm(coefs)?;
    if actual != claimed {
        return Err(ExactL2Error::Mismatch { actual, claimed });
    }
    if actual > s_max {
        return Err(ExactL2Error::BoundExceeded {
            norm_sq: actual,
            max: s_max,
        });
    }
    Ok(actual)
}

/// Which of §6.2's two proofs of the same statement decided a claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Route {
    /// One integer identity below the modulus: `max{U_dir, S_max} < q` (p. 69).
    Direct,
    /// Digit-plane Gram segments lifted and recombined (Eqs. 121–123).
    DigitGram,
}

impl fmt::Display for Route {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Route::Direct => f.write_str("direct"),
            Route::DigitGram => f.write_str("digit-expanded"),
        }
    }
}

/// One digit-plane Gram claim `p_{t,h,k}` of Eq. (121): the segment, the two
/// digit planes with `h <= k`, and the residue transmitted in `F_q`.
///
/// This is the crate's *only* Gram-claim type. [`crate::pcs::norm_route`]
/// re-exports it as `PairClaim` rather than keeping a second copy, so the
/// diagonal/off-diagonal weighting of Eq. (123) cannot drift between the gate
/// and the protocol statement.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct GramClaim<R> {
    /// Segment index `t`.
    pub segment: usize,
    /// Lower digit plane.
    pub h: usize,
    /// Upper digit plane, `h <= k`.
    pub k: usize,
    /// The claim as transmitted, in `F_q`.
    pub residue: R,
}

/// Public consecutive segments of `[0, n_a)`: the partition `I_t` of Eq. (121),
/// which the paper requires to be public ("Partition `[N_A]` into public
/// consecutive segments `I_t`", p. 69).
///
/// # Panics
/// If `n_a` or `seg_len` is zero.
pub fn segments(n_a: usize, seg_len: usize) -> Vec<(usize, usize)> {
    assert!(n_a > 0 && seg_len > 0, "segments must be non-empty");
    (0..n_a)
        .step_by(seg_len)
        .map(|start| (start, (start + seg_len).min(n_a)))
        .collect()
}

/// Eq. (122): `|I_t| B_dig,h B_dig,k < q/2`, the condition Lemma 6.4 needs for
/// the centered lift of a Gram residue to be the integer inner product.
pub fn segment_admissible(len: usize, b_dig_h: u64, b_dig_k: u64, modulus: u64) -> bool {
    let product = (len as u128)
        .saturating_mul(u128::from(b_dig_h))
        .saturating_mul(u128::from(b_dig_k));
    product < u128::from(modulus) / 2
}

/// `N_pair` of Eq. (124): how many Gram claims the digit-expanded route
/// transmits, i.e. the proof-size price of leaving the direct window.
pub const fn n_pair(segments: usize, delta_f: usize) -> usize {
    segments * delta_f * (delta_f + 1) / 2
}

/// The "public canonical ordering of triples `(t, h, k)`" of Eq. (125), the
/// order the verifier indexes its batching powers by.
pub fn pair_order(segments: usize, delta_f: usize) -> Vec<(usize, usize, usize)> {
    let mut out = Vec::with_capacity(n_pair(segments, delta_f));
    for t in 0..segments {
        for h in 0..delta_f {
            for k in h..delta_f {
                out.push((t, h, k));
            }
        }
    }
    out
}

/// `U_dir` of Eq. (119): the largest squared norm the *certified digit ranges*
/// can produce, `N_A (Σ_{h<δ_f} b^h B_dig,h)²`. The direct route may be taken
/// only when this and `S_max` both stay under `q`.
///
/// # Panics
/// If there is no digit plane or the digit weight leaves `u128`.
pub fn u_dir(n_a: usize, base: u64, digit_bounds: &[u64]) -> u128 {
    assert!(
        !digit_bounds.is_empty(),
        "there is at least one response digit plane"
    );
    let mut reach: u128 = 0;
    for (h, &b_dig) in digit_bounds.iter().enumerate() {
        let weight = u128::from(base)
            .checked_pow(h as u32)
            .expect("digit weight fits u128");
        reach += weight * u128::from(b_dig);
    }
    (n_a as u128).saturating_mul(reach.saturating_mul(reach))
}

/// §6.2's route test: direct iff `max{U_dir, S_max} < q`, digit-expanded
/// otherwise. A `u128` comparison, so it decides identically above `2³²`.
pub fn select_route(u_dir: u128, s_max: u128, modulus: u64) -> Route {
    if u_dir.max(s_max) < u128::from(modulus) {
        Route::Direct
    } else {
        Route::DigitGram
    }
}

/// The reconstructed integer response coordinate of Eq. (116),
/// `z_u^Z = Σ_{h<δ_f} b^h z_h(u)`, over the integers with no reduction.
///
/// # Panics
/// If the planes are empty, unequal, or a digit weight leaves `i128`.
pub fn integer_coordinate(planes: &[Vec<i64>], base: u64, u: usize) -> i128 {
    assert!(!planes.is_empty(), "the response needs a digit plane");
    let mut acc: i128 = 0;
    for (h, plane) in planes.iter().enumerate() {
        assert!(u < plane.len(), "coordinate {u} is outside digit plane {h}");
        let weight = i128::from(base)
            .checked_pow(h as u32)
            .expect("digit weight fits i128");
        acc += weight * i128::from(plane[u]);
    }
    acc
}

/// Every coordinate of Eq. (116), for `n_a = planes[0].len()`.
pub fn integer_coordinates(planes: &[Vec<i64>], base: u64) -> Vec<i128> {
    assert!(
        !planes.is_empty(),
        "the response needs at least one digit plane"
    );
    let n = planes[0].len();
    for p in planes.iter() {
        assert_eq!(p.len(), n, "digit planes must be equal length");
    }
    (0..n)
        .map(|u| integer_coordinate(planes, base, u))
        .collect()
}

/// `E_int(ẑ)` of Eq. (116)–(117): the exact integer squared norm of the
/// *reconstructed* coordinates, which bounds the reduced ring norm from above.
///
/// # Errors
/// [`ExactL2Error::Overflow`] if the sum leaves the `u128` window.
pub fn integer_energy(planes: &[Vec<i64>], base: u64) -> Result<u128, ExactL2Error> {
    let mut acc: u128 = 0;
    for u in 0..planes[0].len() {
        let z = integer_coordinate(planes, base, u);
        let sq = u128::try_from(z.checked_mul(z).ok_or(ExactL2Error::Overflow)?)
            .map_err(|_| ExactL2Error::Overflow)?;
        acc = acc.checked_add(sq).ok_or(ExactL2Error::Overflow)?;
    }
    Ok(acc)
}

/// Whether `planes` recomposes to `coords` modulo `q` — the binding between
/// Eq. (116)'s digits and the ring vector `z = G_{b,m_A} ẑ` the rest of the
/// protocol talks about. Without it the gate would certify digits of some
/// other response.
///
/// # Panics
/// If the plane widths and `coords.len()` disagree.
pub fn planes_reduce_to<R: Ring>(planes: &[Vec<i64>], coords: &[R], base: u64) -> bool {
    let reconstructed = integer_coordinates(planes, base);
    assert_eq!(
        reconstructed.len(),
        coords.len(),
        "the digit planes and the response coordinates must cover the same cells"
    );
    let modulus = i128::from(R::MODULUS);
    reconstructed.iter().zip(coords).all(|(&z, c)| {
        i128::try_from(c.to_u128()).expect("a residue fits i128") == z.rem_euclid(modulus)
    })
}

/// Every `p_{t,h,k}` of Eq. (121) as a transmitted residue, checking Eq. (122)
/// as it goes: a segment whose Gram sum cannot be lifted uniquely is refused
/// rather than silently wrapped.
///
/// # Errors
/// [`ExactL2Error::SegmentTooWide`] for the first inadmissible `(t, h, k)`.
pub fn gram_claims<R: Ring>(
    planes: &[Vec<i64>],
    segs: &[(usize, usize)],
    digit_bounds: &[u64],
    modulus: u64,
) -> Result<Vec<GramClaim<R>>, ExactL2Error> {
    let delta_f = planes.len();
    assert_eq!(
        digit_bounds.len(),
        delta_f,
        "every digit plane carries its own certified bound B_dig,h"
    );
    let mut out = Vec::with_capacity(n_pair(segs.len(), delta_f));
    for (t, &(lo, hi)) in segs.iter().enumerate() {
        for h in 0..delta_f {
            for k in h..delta_f {
                let len = hi - lo;
                let magnitude = (len as u128)
                    .saturating_mul(u128::from(digit_bounds[h]))
                    .saturating_mul(u128::from(digit_bounds[k]));
                if !segment_admissible(len, digit_bounds[h], digit_bounds[k], modulus) {
                    return Err(ExactL2Error::SegmentTooWide {
                        len,
                        magnitude,
                        half_modulus: u128::from(modulus) / 2,
                    });
                }
                let integer: i128 = (lo..hi)
                    .map(|u| i128::from(planes[h][u]) * i128::from(planes[k][u]))
                    .sum();
                out.push(GramClaim {
                    segment: t,
                    h,
                    k,
                    residue: R::from(integer.rem_euclid(i128::from(modulus)) as u64),
                });
            }
        }
    }
    Ok(out)
}

/// The unique centered lift into `(-q/2, q/2)` that Lemma 6.4 licenses.
fn centered_lift<R: Ring>(residue: &R) -> i128 {
    let modulus = i128::from(R::MODULUS);
    let raw = i128::try_from(residue.to_u128()).expect("a residue fits i128");
    if raw > modulus / 2 {
        raw - modulus
    } else {
        raw
    }
}

/// Eq. (123), Proposition 6.5: the integer squared norm rebuilt from the Gram
/// claims, weighting `b^{2h}` on the diagonal and `2 b^{h+k}` off it.
///
/// # Errors
/// [`ExactL2Error::SegmentTooWide`] when a claim's own bound does not license
/// the lift (Lemma 6.4's hypothesis re-checked on the receiver's side),
/// [`ExactL2Error::Overflow`] if the reconstruction is negative or leaves
/// `u128` — a negative reconstruction is exactly the case p. 69 tells the
/// verifier to reject.
pub fn reconstruct_energy<R: Ring>(
    claims: &[GramClaim<R>],
    segs: &[(usize, usize)],
    digit_bounds: &[u64],
    base: u64,
) -> Result<u128, ExactL2Error> {
    let half = i128::from(R::MODULUS) / 2;
    let mut total: i128 = 0;
    for claim in claims {
        let len = segs[claim.segment].1 - segs[claim.segment].0;
        let bound = (len as u128)
            .saturating_mul(u128::from(digit_bounds[claim.h]))
            .saturating_mul(u128::from(digit_bounds[claim.k]));
        if bound >= u128::try_from(half).unwrap_or(u128::MAX) {
            return Err(ExactL2Error::SegmentTooWide {
                len,
                magnitude: bound,
                half_modulus: u128::try_from(half).unwrap_or(u128::MAX),
            });
        }
        let weight = u128::from(base)
            .checked_pow((claim.h + claim.k) as u32)
            .expect("cross weight fits u128");
        let weight = if claim.h == claim.k {
            weight
        } else {
            weight.saturating_mul(2)
        };
        let term = i128::try_from(weight)
            .expect("weight fits i128")
            .checked_mul(centered_lift(&claim.residue))
            .ok_or(ExactL2Error::Overflow)?;
        total = total.checked_add(term).ok_or(ExactL2Error::Overflow)?;
    }
    u128::try_from(total).map_err(|_| ExactL2Error::Overflow)
}

/// The width in bytes of the canonical fixed-width unsigned encoding Eq. (118)
/// prescribes: "the canonical fixed-width unsigned encoding **determined by
/// `S_max`**". It is `S_max`, not `q`, that sets the width — the whole point of
/// the digit-expanded route is that the norm budget leaves the field.
pub fn energy_wire_bytes(s_max: u128) -> usize {
    let bits = 128 - s_max.leading_zeros();
    let width = ((bits as usize) + 7) / 8;
    if width == 0 {
        1
    } else {
        width
    }
}

/// The canonical encoding: exactly [`energy_wire_bytes`] little-endian bytes,
/// zero-padded, and nothing else.
pub fn encode_energy(s_max: u128, value: u128) -> Vec<u8> {
    assert!(
        value <= s_max,
        "a claim outside [0, S_max] has no canonical encoding"
    );
    value.to_le_bytes()[..energy_wire_bytes(s_max)].to_vec()
}

/// The verifier's decoding of Eq. (118): reject any noncanonical encoding —
/// wrong length, a set byte above the width, or a value outside `[0, S_max]` —
/// and only then hand back the integer the gate compares.
///
/// # Errors
/// [`ExactL2Error::NonCanonical`] for all three shapes of noncanonicity.
pub fn decode_energy(s_max: u128, bytes: &[u8]) -> Result<u128, ExactL2Error> {
    let width = energy_wire_bytes(s_max);
    if bytes.len() != width {
        return Err(ExactL2Error::NonCanonical {
            decoded: 0,
            max: s_max,
        });
    }
    let mut raw = [0u8; 16];
    raw[..width].copy_from_slice(bytes);
    let decoded = u128::from_le_bytes(raw);
    if decoded > s_max {
        return Err(ExactL2Error::NonCanonical {
            decoded,
            max: s_max,
        });
    }
    Ok(decoded)
}

/// The digit-expanded gate (Eqs. 118 + 123): decode canonically, rebuild the
/// integer norm from the Gram claims, and require equality with the claim and
/// `<= S_max`. This is the route that stays open past `S_max >= q`.
///
/// # Errors
/// [`ExactL2Error::NonCanonical`], [`ExactL2Error::SegmentTooWide`],
/// [`ExactL2Error::Mismatch`], [`ExactL2Error::BoundExceeded`],
/// [`ExactL2Error::Overflow`].
pub fn exact_l2_gate_gram<R: Ring>(
    claims: &[GramClaim<R>],
    segs: &[(usize, usize)],
    digit_bounds: &[u64],
    base: u64,
    claimed: u128,
    s_max: u128,
) -> Result<u128, ExactL2Error> {
    if claimed > s_max {
        return Err(ExactL2Error::NonCanonical {
            decoded: claimed,
            max: s_max,
        });
    }
    let rebuilt = reconstruct_energy(claims, segs, digit_bounds, base)?;
    if rebuilt != claimed {
        return Err(ExactL2Error::Mismatch {
            actual: rebuilt,
            claimed,
        });
    }
    if rebuilt > s_max {
        return Err(ExactL2Error::BoundExceeded {
            norm_sq: rebuilt,
            max: s_max,
        });
    }
    Ok(rebuilt)
}

/// The gate that switches routes: [`Route::Direct`] when §6.2's window is open,
/// [`Route::DigitGram`] when it is not, and never a refusal merely because the
/// norm crossed `q`.
///
/// Both routes are fed the *same* digit planes, so the statement they decide is
/// the same statement; `coords` is the reduced response `z` they must agree
/// with. Returns the verified exact squared norm and the route taken.
///
/// # Errors
/// As [`exact_l2_gate`] and [`exact_l2_gate_gram`].
#[allow(clippy::too_many_arguments)]
pub fn exact_l2_gate_routed<R: CenteredRing>(
    coords: &[R],
    planes: &[Vec<i64>],
    claimed: u128,
    s_max: u128,
    base: u64,
    seg_len: usize,
    digit_bounds: &[u64],
) -> Result<(u128, Route), ExactL2Error> {
    assert!(
        !planes.is_empty() && !planes[0].is_empty(),
        "the routed gate needs digit planes over at least one cell"
    );
    if !planes_reduce_to(planes, coords, base) {
        return Err(ExactL2Error::Mismatch {
            actual: integer_energy(planes, base)?,
            claimed,
        });
    }
    let n_a = planes[0].len();
    let limit = u_dir(n_a, base, digit_bounds);
    match select_route(limit, s_max, R::MODULUS) {
        Route::Direct => {
            exact_l2_gate(coords, claimed, s_max).map(|energy| (energy, Route::Direct))
        }
        Route::DigitGram => {
            let segs = segments(n_a, seg_len);
            let claims = gram_claims::<R>(planes, &segs, digit_bounds, R::MODULUS)?;
            exact_l2_gate_gram(&claims, &segs, digit_bounds, base, claimed, s_max)
                .map(|energy| (energy, Route::DigitGram))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;
    use alloc::string::ToString;
    use alloc::vec;
    use alloc::vec::Vec;

    type Fq = Zq<8380417>;
    const Q: u64 = 8_380_417;

    /// A residue by its non-negative representative.
    fn c(v: u64) -> Fq {
        Fq::from(v % Q)
    }

    /// A residue written from a negative integer.
    fn neg(v: u64) -> Fq {
        Fq::from(Q - v)
    }

    #[test]
    fn squared_norm_is_the_integer_sum_of_centered_squares() {
        assert_eq!(squared_norm(&[c(3), c(4), c(0)]).unwrap(), 25);
        let wide: Vec<Fq> = (1..=10).map(c).collect();
        let expect: u64 = (1..=10u64).map(|i| i * i).sum();
        assert_eq!(
            u64::try_from(squared_norm(&wide).unwrap()).unwrap(),
            expect,
            "cross-checked against an independent integer computation"
        );
    }

    #[test]
    fn a_residue_near_q_lifts_negative_so_its_square_stays_small() {
        // q-5 and -5 are the same ring element; the integer square is 25,
        // never (q-5)^2.
        let as_representative = [neg(5)];
        assert_eq!(squared_norm(&as_representative).unwrap(), 25);
        assert_eq!(
            squared_norm(&as_representative).unwrap(),
            squared_norm(&[c(5)]).unwrap()
        );
        assert_eq!(max_magnitude(&as_representative), 5);
    }

    #[test]
    fn gate_accepts_the_true_claim_at_the_boundary_and_rejects_above_it() {
        let v = [c(6), c(8)]; // 36 + 64
        assert_eq!(exact_l2_gate(&v, 100, 100).unwrap(), 100, "== S_max");
        assert_eq!(exact_l2_gate(&v, 100, 101).unwrap(), 100);
        assert_eq!(
            exact_l2_gate(&v, 100, 99),
            Err(ExactL2Error::BoundExceeded {
                norm_sq: 100,
                max: 99
            })
        );
    }

    #[test]
    fn gate_rejects_a_claim_that_does_not_match_the_witness() {
        let v = [c(6), c(8)];
        assert!(matches!(
            exact_l2_gate(&v, 101, 1_000),
            Err(ExactL2Error::Mismatch {
                actual: 100,
                claimed: 101
            })
        ));
    }

    #[test]
    fn reducing_the_claim_mod_q_does_not_bypass_the_bound() {
        // A half-modulus coordinate squares to ~q^2/4, far above any
        // admissible bound. Sending `E_int mod q` as the claim — what a
        // wraparound prover would do — must not be accepted.
        let heavy = [c(Q / 2)];
        let actual = squared_norm(&heavy).unwrap();
        assert!(actual > u128::from(Q), "the integer norm is above q");
        let s_max = u128::from(Q) - 1;
        assert!(direct_route_admissible::<Fq>(s_max));
        assert_eq!(
            exact_l2_gate(&heavy, actual % u128::from(Q), s_max),
            Err(ExactL2Error::Mismatch {
                actual,
                claimed: actual % u128::from(Q)
            })
        );
        // and the exact claim is still refused, just on the bound
        assert_eq!(
            exact_l2_gate(&heavy, actual, s_max),
            Err(ExactL2Error::BoundExceeded {
                norm_sq: actual,
                max: s_max
            })
        );
    }

    #[test]
    fn gate_refuses_the_direct_route_when_the_bound_reaches_q() {
        assert!(!direct_route_admissible::<Fq>(u128::from(Q)));
        assert_eq!(
            exact_l2_gate(&[c(1)], 1, u128::from(Q)),
            Err(ExactL2Error::NotAdmissible {
                limit: u128::from(Q),
                modulus: Q
            })
        );
    }

    #[test]
    fn exact_l2_disagrees_with_an_inf_gate_in_both_directions() {
        // 200 coordinates of magnitude 5 pass ‖·‖∞ ≤ 5 but their Euclidean
        // square is 5000, so a 4000 bound rejects: the gates are not
        // re-labelings of each other.
        let many_small: Vec<Fq> = (0..200).map(|_| c(5)).collect();
        assert!(max_magnitude(&many_small) <= 5, "passes the l∞ gate");
        assert_eq!(squared_norm(&many_small).unwrap(), 5_000);
        assert!(matches!(
            exact_l2_gate(&many_small, 5_000, 4_000),
            Err(ExactL2Error::BoundExceeded { .. })
        ));
        // ... and one coordinate of magnitude 60 fails ‖·‖∞ ≤ 5 while its
        // square 3600 sits under 4000: the converse disagreement.
        let one_big = [c(60)];
        assert!(max_magnitude(&one_big) > 5);
        assert_eq!(exact_l2_gate(&one_big, 3_600, 4_000).unwrap(), 3_600);
    }

    #[test]
    fn accumulation_is_exact_over_a_long_vector_and_never_wraps() {
        let v: Vec<Fq> = (0..5_000).map(|_| neg(7)).collect();
        let expect = 7u128 * 7 * 5_000;
        assert_eq!(squared_norm(&v).unwrap(), expect);
        // signs mixed in: the squares must add, not cancel
        let mut mixed = v.clone();
        for slot in &mut mixed[..2_500] {
            *slot = c(7);
        }
        assert_eq!(squared_norm(&mixed).unwrap(), expect);
    }

    // --- the digit-plane Gram fallback (Eqs. 116, 119, 121-124) ---

    /// A modulus small enough that a three-plane base-8 response routinely
    /// squares past it, which is precisely the regime the direct route cannot
    /// express. Prime (`2^11 - 9`), so `Zq` is a field.
    type Small = Zq<2039>;
    const SMALL_Q: u64 = 2_039;

    /// A residue by its non-negative representative in the small ring.
    fn s(v: u64) -> Small {
        Small::from(v % SMALL_Q)
    }

    /// Deterministic digit generator: `no_std` has no RNG, and a fixed tape
    /// keeps the brute-force pin reproducible.
    struct XorShift(u64);
    impl XorShift {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }
        fn digit(&mut self, lo: i64, hi: i64) -> i64 {
            let span = (hi - lo + 1) as u64;
            lo + (self.next() % span) as i64
        }
    }

    /// `δ_f` digit planes over `n_a` cells, each digit inside Akita's
    /// negatively biased alphabet `A_b = {-b/2, ..., b/2 - 1}` (Remark 6.1).
    fn random_planes(seed: u64, base: u64, delta_f: usize, n_a: usize) -> Vec<Vec<i64>> {
        let mut rng = XorShift(seed | 1);
        (0..delta_f)
            .map(|_| {
                (0..n_a)
                    .map(|_| rng.digit(-((base / 2) as i64), (base / 2) as i64 - 1))
                    .collect()
            })
            .collect()
    }

    /// E_int computed from scratch, sharing no code with the module: `i128::pow`
    /// and `as u128` instead of `checked_pow`/`try_from`, so an arithmetic
    /// mistake in the module cannot be mirrored here.
    fn brute_force_energy(planes: &[Vec<i64>], base: u64) -> u128 {
        let mut total: u128 = 0;
        for u in 0..planes[0].len() {
            let mut z: i128 = 0;
            for h in 0..planes.len() {
                z += i128::from(base).pow(h as u32) * i128::from(planes[h][u]);
            }
            total += (z * z) as u128;
        }
        total
    }

    /// The reduced response coordinates `z = G_{b,m_A} ẑ` of Eq. (117).
    fn reduce(planes: &[Vec<i64>], base: u64) -> Vec<Small> {
        integer_coordinates(planes, base)
            .iter()
            .map(|&z| s(z.rem_euclid(i128::from(SMALL_Q)) as u64))
            .collect()
    }

    #[test]
    fn the_gram_route_pins_against_a_brute_force_integer_sum() {
        // Every configuration here has E_int > q = 2039 (the minimum over the
        // 150 trials of each is printed in the assert message below), so the
        // field identity of Eq. (120) cannot decide it and only the
        // digit-expanded route can.
        let configs: [(u64, usize, usize, usize); 8] = [
            (8, 3, 6, 1),
            (8, 3, 6, 2),
            (8, 3, 6, 3),
            (4, 4, 8, 1),
            (4, 4, 8, 2),
            (16, 2, 5, 1),
            (2, 6, 7, 1),
            (8, 4, 9, 3),
        ];
        let mut pinned = 0usize;
        for (base, delta_f, n_a, seg_len) in configs {
            let bounds = vec![base / 2; delta_f];
            for trial in 0..150u64 {
                let planes = random_planes(trial * 977 + base, base, delta_f, n_a);
                let expected = brute_force_energy(&planes, base);
                assert!(
                    expected > u128::from(SMALL_Q),
                    "E_int {expected} must exceed q"
                );
                let segs = segments(n_a, seg_len);
                let claims = gram_claims::<Small>(&planes, &segs, &bounds, SMALL_Q)
                    .expect("Eq. (122) holds at this span");
                assert_eq!(claims.len(), n_pair(segs.len(), delta_f));
                assert_eq!(
                    reconstruct_energy(&claims, &segs, &bounds, base).unwrap(),
                    expected,
                    "base {base} delta_f {delta_f} n_a {n_a} seg_len {seg_len} trial {trial}"
                );
                assert_eq!(
                    integer_energy(&planes, base).unwrap(),
                    expected,
                    "Eq. (116)"
                );
                assert!(planes_reduce_to::<Small>(
                    &planes,
                    &reduce(&planes, base),
                    base
                ));
                pinned += 1;
            }
        }
        assert_eq!(pinned, 8 * 150, "every configuration must reach the pin");
    }

    #[test]
    fn the_direct_gate_refuses_where_the_routed_gate_decides() {
        // Same instance, same claim, two entry points: the direct gate keeps
        // its refusal (it holds no digits), the routed gate takes the fallback.
        let base = 8u64;
        let delta_f = 3usize;
        let n_a = 6usize;
        let planes = random_planes(1, base, delta_f, n_a);
        let bounds = vec![base / 2; delta_f];
        let coords = reduce(&planes, base);
        let energy = brute_force_energy(&planes, base);
        let s_max = energy;
        assert_eq!(
            exact_l2_gate(&coords, energy, s_max),
            Err(ExactL2Error::NotAdmissible {
                limit: s_max,
                modulus: SMALL_Q
            }),
            "S_max reaches q, so the direct route must still refuse"
        );
        let (got, route) =
            exact_l2_gate_routed(&coords, &planes, energy, s_max, base, 1, &bounds).unwrap();
        assert_eq!(got, energy);
        assert_eq!(route, Route::DigitGram);
        assert_eq!(route.to_string(), "digit-expanded");
    }

    #[test]
    fn both_routes_agree_when_the_direct_window_is_open() {
        // One plane, one cell, tiny digits: max{U_dir, S_max} < q, so the
        // selection must land on Direct and the two reconstructions coincide.
        let base = 8u64;
        let planes: Vec<Vec<i64>> = vec![vec![3, -2, 1, 1]];
        let bounds = vec![base / 2];
        let coords: Vec<Fq> = integer_coordinates(&planes, base)
            .iter()
            .map(|&z| Fq::from(z.rem_euclid(i128::from(Q)) as u64))
            .collect();
        let energy = brute_force_energy(&planes, base);
        let limit = u_dir(planes[0].len(), base, &bounds);
        assert_eq!(
            select_route(limit, energy, Q),
            Route::Direct,
            "Eq. (119) window"
        );
        let (got, route) =
            exact_l2_gate_routed(&coords, &planes, energy, energy, base, 1, &bounds).unwrap();
        assert_eq!(route, Route::Direct);
        assert_eq!(got, energy);
        // and the Gram route on the same data gives the identical integer
        let segs = segments(planes[0].len(), 1);
        let claims = gram_claims::<Fq>(&planes, &segs, &bounds, Q).unwrap();
        assert_eq!(
            exact_l2_gate_gram(&claims, &segs, &bounds, base, energy, energy).unwrap(),
            energy
        );
    }

    #[test]
    fn a_tampered_gram_residue_fails_by_name() {
        let base = 4u64;
        let planes = random_planes(31, base, 2, 6);
        let bounds = vec![base / 2; 2];
        let segs = segments(6, 1);
        let energy = brute_force_energy(&planes, base);
        let mut claims = gram_claims::<Small>(&planes, &segs, &bounds, SMALL_Q).unwrap();
        let off_by = claims
            .iter()
            .position(|&cl| cl.h != cl.k)
            .expect("an off-diagonal triple");
        // +1 on an off-diagonal claim moves the reconstruction by 2 b^{h+k}
        let weight = 2 * u128::from(base).pow((claims[off_by].h + claims[off_by].k) as u32);
        claims[off_by].residue += Small::ONE;
        assert_eq!(
            exact_l2_gate_gram(&claims, &segs, &bounds, base, energy, energy),
            Err(ExactL2Error::Mismatch {
                actual: energy + weight,
                claimed: energy
            })
        );
        // a claim above S_max never reaches the reconstruction at all
        assert_eq!(
            exact_l2_gate_gram(&claims, &segs, &bounds, base, energy + 1, energy),
            Err(ExactL2Error::NonCanonical {
                decoded: energy + 1,
                max: energy
            })
        );
    }

    #[test]
    fn the_eq_122_guard_is_what_makes_the_lift_unique() {
        // Two admissible digit vectors whose Gram sum differs by exactly one
        // modulus: they transmit the SAME residue and the verifier cannot tell
        // them apart. Eq. (122) is the only thing that stops this.
        type Tiny = Zq<13>;
        let base = 4u64;
        let heavy: Vec<i64> = vec![2, 2, 2, 2, 0, 0, 0, 0]; // Σ z² = 16
        let light: Vec<i64> = vec![1, 1, 1, 0, 0, 0, 0, 0]; // Σ z² = 3
        assert_eq!(
            heavy.iter().map(|v| v * v).sum::<i64>() % 13,
            light.iter().map(|v| v * v).sum::<i64>() % 13,
            "both planes must transmit the same residue mod 13"
        );
        let q = 13u64;
        let bounds = vec![base / 2];
        let wide = segments(8, 8);
        // |I_t| B_h B_k = 8 * 2 * 2 = 32 >= q/2 = 6 -> the lift is ambiguous
        assert!(!segment_admissible(8, 2, 2, q));
        assert_eq!(
            gram_claims::<Tiny>(&[heavy.clone()], &wide, &bounds, q),
            Err(ExactL2Error::SegmentTooWide {
                len: 8,
                magnitude: 32,
                half_modulus: 6
            })
        );
        // and the ambiguity is real, not hypothetical: the two vectors have
        // different exact norms while every claim they send is identical
        let e_heavy = brute_force_energy(&[heavy.clone()], base);
        let e_light = brute_force_energy(&[light.clone()], base);
        assert_eq!((e_heavy, e_light), (16, 3));
        // shrinking the segment restores uniqueness: |I_t| * 4 < q/2 needs q
        // away from 13, and then the two vectors separate.
        assert!(segment_admissible(1, 2, 2, SMALL_Q));
        for plane in [&heavy, &light] {
            let segs = segments(8, 1);
            let claims = gram_claims::<Small>(&[plane.clone()], &segs, &bounds, SMALL_Q).unwrap();
            assert_eq!(
                reconstruct_energy(&claims, &segs, &bounds, base).unwrap(),
                brute_force_energy(&[plane.clone()], base)
            );
        }
    }

    #[test]
    fn the_norm_claim_is_encoded_by_its_own_budget_not_by_the_modulus() {
        // Eq. (118): a fixed-width unsigned encoding determined by S_max. Above
        // 2^32 the budget is wider than any coefficient of the ring, which is
        // exactly the "independent integer budget" the route needs.
        assert_eq!(energy_wire_bytes(255), 1);
        assert_eq!(energy_wire_bytes(256), 2);
        assert_eq!(energy_wire_bytes(u128::from(u64::MAX)), 8);
        assert_eq!(energy_wire_bytes(u128::from(u64::MAX) + 1), 9);
        assert_eq!(energy_wire_bytes(0), 1, "a zero budget still sends a byte");
        let s_max = (1u128 << 40) + 7;
        let bytes = encode_energy(s_max, s_max);
        assert_eq!(bytes.len(), 6, "wider than q = 2^32 - 99's four bytes");
        assert_eq!(decode_energy(s_max, &bytes).unwrap(), s_max);
        // noncanonical shapes, each refused
        assert_eq!(
            decode_energy(s_max, &bytes[..5]),
            Err(ExactL2Error::NonCanonical {
                decoded: 0,
                max: s_max
            })
        );
        let mut padded = bytes.clone();
        padded.push(0);
        assert!(matches!(
            decode_energy(s_max, &padded),
            Err(ExactL2Error::NonCanonical { .. })
        ));
        let mut beyond = bytes.clone();
        beyond[5] |= 1 << 7; // sets bit 47, past S_max's bit 40
        match decode_energy(s_max, &beyond) {
            Err(ExactL2Error::NonCanonical { decoded, max }) => assert!(decoded > max),
            other => panic!("an out-of-range encoding must be named, got {other:?}"),
        }
        // a claim one above S_max is refused before any reconstruction runs
        assert_eq!(
            decode_energy(s_max, &encode_energy(s_max, s_max - 1)).unwrap(),
            s_max - 1
        );
    }

    #[test]
    fn digit_planes_that_do_not_reduce_to_the_response_are_refused() {
        // Without this binding the gate would certify the digits of some other
        // response, so the routed entry point must check Eq. (116) against `z`.
        let base = 8u64;
        let planes = random_planes(7, base, 3, 6);
        let bounds = vec![base / 2; 3];
        let energy = brute_force_energy(&planes, base);
        let mut other = planes.clone();
        other[0][0] += 1;
        let coords = reduce(&planes, base);
        assert!(!planes_reduce_to(&other, &coords, base));
        assert_eq!(
            exact_l2_gate_routed(&coords, &other, energy, energy, base, 1, &bounds),
            Err(ExactL2Error::Mismatch {
                actual: brute_force_energy(&other, base),
                claimed: energy
            })
        );
    }

    #[test]
    fn the_pair_order_is_complete_and_the_last_segment_may_be_short() {
        let order = pair_order(3, 4);
        assert_eq!(order.len(), n_pair(3, 4));
        assert_eq!(n_pair(3, 4), 3 * 4 * 5 / 2);
        assert_eq!(order[0], (0, 0, 0));
        assert_eq!(*order.last().unwrap(), (2, 3, 3));
        assert!(order.iter().all(|&(t, h, k)| t < 3 && h <= k && k < 4));
        // Eq. (121)'s partition of [N_A] must cover every cell exactly once
        let segs = segments(7, 3);
        assert_eq!(segs, vec![(0, 3), (3, 6), (6, 7)]);
        let covered: usize = segs.iter().map(|&(lo, hi)| hi - lo).sum();
        assert_eq!(covered, 7);
        let planes = random_planes(3, 8, 2, 7);
        let bounds = vec![4u64; 2];
        let claims = gram_claims::<Small>(&planes, &segs, &bounds, SMALL_Q).unwrap();
        assert_eq!(claims.len(), n_pair(3, 2));
        assert_eq!(
            reconstruct_energy(&claims, &segs, &bounds, 8).unwrap(),
            brute_force_energy(&planes, 8)
        );
    }

    #[test]
    fn u_dir_is_the_paper_formula_and_selects_the_route() {
        // U_dir = N_A (Σ_h b^h B_dig,h)^2, Eq. (119).
        assert_eq!(u_dir(6, 8, &[4, 4, 4]), 6 * (4 + 32 + 256) * (4 + 32 + 256));
        assert_eq!(u_dir(1, 2, &[1]), 1);
        // direct iff max{U_dir, S_max} < q
        assert_eq!(select_route(100, 100, 1_000), Route::Direct);
        assert_eq!(select_route(1_000, 100, 1_000), Route::DigitGram);
        assert_eq!(select_route(100, 1_000, 1_000), Route::DigitGram);
        // a u128-scale U_dir against a 32-bit q is decided in u128, not truncated
        let huge = u128::from(u64::MAX) * 4;
        assert_eq!(select_route(huge, 1, u64::MAX), Route::DigitGram);
        assert!(direct_route_admissible::<Fq>(u128::from(Q) - 1));
    }

    /// The integer seam and the ring seam must be the *same* arithmetic: a
    /// residue and its centered lift have the same squared norm, so a caller
    /// that already holds integers cannot get a different answer than one that
    /// holds ring elements.
    #[test]
    fn the_integer_and_ring_accumulators_agree_on_the_centered_lift() {
        let ints = [3i64, -4, 5, i64::try_from(Q / 2).unwrap() - 7];
        let ring: Vec<Fq> = ints
            .iter()
            .map(|&v| c(v.rem_euclid(Q as i64) as u64))
            .collect();
        assert_eq!(
            squared_norm_of_ints(&ints).unwrap(),
            squared_norm(&ring).unwrap()
        );
        // …and one coordinate past the centered window is still measured as the
        // integer it is, which is exactly why the gate demands lifts.
        assert_eq!(squared_norm_of_ints(&[-5]).unwrap(), 25);
        assert_eq!(squared_norm_of_ints(&[]).unwrap(), 0);
    }

    #[test]
    fn isqrt_ceil_never_underestimates_the_root() {
        assert_eq!(isqrt_ceil(0), 0);
        assert_eq!(isqrt_ceil(1), 1);
        assert_eq!(isqrt_ceil(25), 5, "an exact square stays put");
        assert_eq!(isqrt_ceil(26), 6);
        assert_eq!(isqrt_ceil(u128::MAX), 1 << 64);
        for n in [2u128, 3, 8, 9, 15, 16, 1_000_000, 1_000_001] {
            let r = isqrt_ceil(n);
            assert!(r * r >= n, "isqrt_ceil({n}) = {r} is below the root");
            assert!((r - 1) * (r - 1) < n, "isqrt_ceil({n}) is not the ceiling");
        }
    }

    #[test]
    fn norm_sum_gate_adds_roots_and_not_squares() {
        let a: Vec<i64> = vec![3, 4]; // ‖a‖₂ = 5
        let b: Vec<i64> = vec![5, 12]; // ‖b‖₂ = 13
        let parts: &[&[i64]] = &[&a, &b];
        assert_eq!(norm_sum_gate(parts, 18).unwrap(), 18, "5 + 13");
        assert_eq!(
            norm_sum_gate(parts, 17),
            Err(ExactL2Error::BoundExceeded {
                norm_sq: 18,
                max: 17
            })
        );
        // The returned quantity is the sum of *roots* (18), not the sum of
        // squares (25 + 169 = 194) a mis-transcribed gate would compare.
        assert_eq!(norm_sum_gate(parts, 100).unwrap(), 18);
        // the non-square part rounds up, so the gate stays conservative
        let odd: Vec<i64> = vec![1, 1, 1];
        assert_eq!(norm_sum_gate(&[&odd], 2).unwrap(), 2, "⌈√3⌉ = 2");
    }
}
