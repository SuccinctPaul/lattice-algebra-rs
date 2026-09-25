//! Digit alphabets and their vanishing predicates (Akita §3.3, §6.1, §4.5).
//!
//! Three things a lattice PCS must keep straight, and this module keeps
//! separate:
//!
//! 1. **the alphabet a digit is certified to lie in** — Akita uses the
//!    *negatively* biased balanced set `A_b = {-b/2, ..., b/2 - 1}`
//!    (Remark 6.1), not the positively biased centered set the crate's
//!    [`crate::pcs::gadget`] split emits;
//! 2. **the base a digit vector is recomposed in** — a segment may use any
//!    base `b <= b*` while the range proof certifies the single common
//!    alphabet `A_{b*}` (§5.4: "This separates the base that recomposes a
//!    response from the alphabet that bounds each of its digits");
//! 3. **the exact integer interval a `k`-digit expansion represents** —
//!    because `A_b` is asymmetric, so are its reaches (Eq. 111).
//!
//! # Verbatim from the paper
//!
//! Remark 6.1 (p. 68): "In practice, we use the negative-biased balanced range
//! `{−b⋆/2, . . . , b⋆/2 − 1}` for a power-of-two base `b⋆ ∈ {4, 8, 16, 32, 64}`.
//! The balanced range minimizes the digit norm for a fixed alphabet size. When
//! `b⋆` is even, its negative bias also enables the degree-halving identity in
//! Equation (114), since the two roots `k` and `−(k + 1)` have the same image
//! under `w ↦ w(w + 1)`." §1.1 footnote 8 (p. 7) adds that Hachi uses the same
//! alphabet, and gives three-bit digits as `b = 2³ = 8` over `{−4, . . . , 3}`.
//!
//! §5.4 (p. 63), which fixes the interval [`representable_interval`] and the
//! two envelopes this module reports:
//!
//! ```text
//! [−M_f, T_f],  M_f := (b/2)(b^δf − 1)/(b − 1),  T_f := (b/2 − 1)(b^δf − 1)/(b − 1)  (111)
//! β_fold^cert := (b⋆/2)(b^δf − 1)/(b − 1)                                        (112)
//! ```
//!
//! "The schedule requires `b ≤ b⋆`. These two bases give two different response
//! bounds" (p. 63), and "This second bound applies to every accepted response
//! and determines the Module-SIS collision radius. It is independent of how the
//! honest-response threshold used to select `δ_f` was obtained. When `b < b⋆`,
//! it is strictly larger than the canonical representable interval and cannot
//! be used to justify honest encodability."
//!
//! §5.4's native-block address, which is [`split_native`]'s layout exactly:
//!
//! ```text
//! pos(j, y, u, k) := ((j s + y) δ + u) d + k,  y ∈ [s], u ∈ [δ], k ∈ [d]      (107)
//! ```
//!
//! with the paper's "Thus the coefficient coordinate changes first, then the
//! digit, then the native block" (p. 63) and its per-role instances — "For
//! partial opening evaluations, `j` enumerates claim/block pairs and
//! `(D, d) = (d_op, d_D)`. For inner images, `j` enumerates claim/block/A-row
//! triples and `(D, d) = (d_A, d_B)`" — i.e. the same witness carries three
//! different ring dimensions, which is gap G1.
//!
//! # Why the negative bias is load-bearing, not cosmetic
//!
//! [`halved_vanishing`] evaluates the range predicate through the map
//! `s = w(w + 1)`: the two alphabet elements `k` and `-(k + 1)` share the
//! image `k(k + 1)`, so `Q_{b*}(w) = Q_sq(w(w + 1))` holds *exactly* with
//! `b*/2` factors instead of `b*` (Eq. 114). That halves the degree of every
//! range sum-check, and the same `w(w + 1)` is what makes the compression
//! digits' binariness constraint free (§6.2, Remark 6.2: the `{ -1, 0 }`
//! alphabet's vanishing polynomial *is* the derived value). The identity is
//! pinned in `halved_predicate_equals_the_full_alphabet_product`, together
//! with the negative result that the positively biased alphabet admits no
//! such rewrite — the bias is doing the work.
//!
//! # Negative-binary compression digits (§4.5)
//!
//! The F/H compression chains use the two-element alphabet `{-1, 0}` with
//! `delta = ceil(log2 q)` planes: coefficientwise, `x = sum_i 2^i xi_i (mod q)`
//! where `xi` is the negated binary expansion of `-x mod q`. Every coefficient
//! of a valid decomposition is in `{-1, 0}`, so two of them differ by at most
//! one — the collision bound `MSIS(n, m, 1)` the compression chain's binding
//! argument (Lemma 4.3) needs. [`decompose_planes`] emits the chain's
//! *plane-major* layout (digit `u` of coefficient `v` at position `v + s*u`),
//! which is the transpose of [`crate::pcs::gadget::split`]'s value-major one.

use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, AddAssign, Mul, Neg, Sub};

/// The inclusive `(lo, hi)` bounds of Akita's balanced alphabet
/// `A_b = {-b/2, ..., b/2 - 1}` for an even base `b` (§3.3).
///
/// # Panics
/// If `b < 2` or `b` is odd (the negative bias requires an even base).
pub const fn alphabet(base: u64) -> (i64, i64) {
    assert!(base >= 2 && base % 2 == 0, "Akita's alphabet needs an even base");
    let lo = -((base / 2) as i64);
    (lo, lo + base as i64 - 1)
}

/// The signed-digit alphabet `{ -1, 0 }` used by both compression maps
/// (§4.5, "Both stages use the negative-binary alphabet").
pub const BINARY_ALPHABET: (i64, i64) = (-1, 0);

/// `x^2 + x` — the derived value `s(x) := w(x)(w(x) + 1)` of §6.1.
///
/// One function serves both obligations Akita fuses into it: it is the map
/// under which the balanced alphabet halves, *and* the vanishing polynomial
/// of `{ -1, 0 }`, so a digit is a compression digit iff this evaluates to
/// zero (Remark 6.2).
pub fn derived<R: Ring>(w: &R) -> R {
    w.square() + *w
}

/// `Q_sq(s) = prod_{k < b/2} (s - k(k + 1))` evaluated at `s = w(w + 1)`
/// (Eq. 114): the degree-`b/2` form of the alphabet's vanishing polynomial.
pub fn halved_vanishing<R: Ring>(w: &R, base: u64) -> R {
    assert!(base >= 2 && base % 2 == 0, "a halved predicate needs an even base");
    let s = derived(w);
    let mut acc = R::ONE;
    for k in 0..base / 2 {
        let image = i128::from(k) * i128::from(k + 1);
        acc *= s - R::from((image % i128::from(R::MODULUS)) as u64);
    }
    acc
}

/// The largest integer a `digits`-plane balanced base-`base` expansion
/// represents, and its largest negative magnitude (Eq. 111):
/// `T_k = (b/2 - 1)(b^k - 1)/(b - 1)`, `M_k = (b/2)(b^k - 1)/(b - 1)`.
///
/// Returns `(negative_magnitude, positive_reach)`; the interval
/// `[-M_k, T_k]` contains exactly `b^k` integers (§3.3).
///
/// # Panics
/// If the base is not a power of two, or if `base * (base^k - 1)` would
/// overflow `u128` (an interval that wide is not a digit system).
pub fn representable_interval(base: u64, digits: usize) -> (u128, u128) {
    assert!(base >= 2 && base.is_power_of_two(), "base must be a power of two");
    let geom = pow_checked(base, digits) - 1; // b^k - 1
    let neg = u128::from(base / 2) * geom / u128::from(base - 1);
    let pos = u128::from(base / 2 - 1) * geom / u128::from(base - 1);
    (neg, pos)
}

/// `base^digits`, computed exactly, panicking on overflow rather than
/// saturating (a silently-clipped capacity would make the depth choice in
/// [`digit_depth`] under-size the response).
fn pow_checked(base: u64, digits: usize) -> u128 {
    try_pow(base, digits).expect("digit capacity overflows u128")
}

/// `base^digits` as `None` once it leaves `u128`. [`digit_depth`] needs the
/// fallible form: at base `2` the capacity overflows at `digits = 128`, exactly
/// where a search bound would otherwise panic instead of answering `None`.
fn try_pow(base: u64, digits: usize) -> Option<u128> {
    let mut acc: u128 = 1;
    for _ in 0..digits {
        acc = acc.checked_mul(u128::from(base))?;
    }
    Some(acc)
}

/// The least digit depth whose canonical interval `[-M_k, T_k]` contains the
/// symmetric threshold `threshold` (§5.4: "the selected threshold is rounded
/// up to the least digit depth whose canonical interval (111) contains it").
///
/// `None` when no depth at this base reaches the threshold, so a caller
/// cannot silently accept an unencodable response.
pub fn digit_depth(base: u64, threshold: u128) -> Option<usize> {
    assert!(base >= 2 && base.is_power_of_two(), "base must be a power of two");
    let mut digits = 1usize;
    while digits <= 128 {
        // The capacity itself is the stopping condition: past `u128` no depth
        // at this base can be evaluated, so the answer is "unreachable" rather
        // than a panic. At base 2 the capacity overflows at digits = 128.
        let geom = try_pow(base, digits)? - 1;
        // Saturating, not checked: an interval this wide already contains any
        // `u128` threshold, so saturating to the maximum answers `Some` — and
        // it never reaches `representable_interval`, which documents that it
        // panics instead.
        let neg = u128::from(base / 2).saturating_mul(geom) / u128::from(base - 1);
        let pos = u128::from(base / 2 - 1).saturating_mul(geom) / u128::from(base - 1);
        if pos >= threshold && neg >= threshold {
            return Some(digits);
        }
        digits += 1;
    }
    None
}

/// The verifier-enforced coefficient envelope of an *accepted* recomposed
/// response: `beta_fold = (b*/2) * (b^delta - 1)/(b - 1)` (Eq. 112).
///
/// This is deliberately wider than the honest canonical interval when the
/// recomposition base `b` is below the certified range base `b_star`; the
/// Module-SIS collision radius comes from here, never from the honest
/// threshold used to pick the depth.
pub fn cert_envelope(base_star: u64, base: u64, digits: usize) -> u128 {
    assert!(base >= 2 && base.is_power_of_two(), "base must be a power of two");
    u128::from(base_star / 2) * (pow_checked(base, digits) - 1) / u128::from(base - 1)
}

/// The certified *difference* envelope of two accepted responses:
/// `Delta_f = (b* - 1) * (b^delta - 1)/(b - 1)` (Eq. 113) — two digits of
/// `A_{b*}` differ by at most `b* - 1`.
pub fn cert_difference(base_star: u64, base: u64, digits: usize) -> u128 {
    assert!(base >= 2 && base.is_power_of_two(), "base must be a power of two");
    u128::from(base_star - 1) * (pow_checked(base, digits) - 1) / u128::from(base - 1)
}

/// The modulus as `i128`. [`Ring::to_u128`] documents `MODULUS <= u64::MAX`,
/// so the widening is always exact.
fn modulus_i128<R: Ring>() -> i128 {
    i128::try_from(u128::from(R::MODULUS)).expect("the modulus fits i128")
}

/// The canonical residue of `v` as a non-negative `i128`.
fn residue_i128<R: Ring>(v: &R) -> i128 {
    i128::try_from(v.to_u128()).expect("a canonical residue is below u64::MAX")
}

/// The exact balanced decomposition over a `PolyRing` slice, value-major: the
/// digit planes of one ring element follow each other, `out[j * DIGITS + k]`.
///
/// This is the layout [`crate::pcs::gadget::split`] emits, with the one
/// difference that matters: digits land in the *negatively* biased
/// `A_BASE = {-b/2, ..., b/2 - 1}` instead of `[-b/2 + 1, b/2]`, which is what
/// makes [`halved_vanishing`] an identity. A scheme whose range proof uses the
/// halved predicate must split with this function, not with `gadget::split`;
/// [`split_native`] is the same convention for the flat witness vectors the
/// recursive protocol needs, and this function is a thin re-labelling of it so
/// the two can never drift.
///
/// # Panics
/// If `BASE` is not a power of two `>= 2`, or if `[-M_DIGITS, T_DIGITS]`
/// cannot contain every canonical representative of `R` — the condition that
/// makes the split exact.
pub fn split<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    values: &[PolyRing<R, D>],
) -> Vec<PolyRing<R, D>> {
    assert!(
        BASE >= 2 && BASE.is_power_of_two(),
        "the digit base must be a power-of-two >= 2"
    );
    let flat: Vec<R> = values.iter().flat_map(|v| v.coefficients()).collect();
    let digits = split_native(&flat, D, 1, BASE, DIGITS);
    digits
        .chunks(D)
        .map(|c| PolyRing::from_coefficients(c.to_vec()))
        .collect()
}

/// The negative-binary decomposition `{ -1, 0 }` of §4.5: `planes = delta`
/// planes over `coeffs.len()` coefficients, emitted **plane-major** so that
/// digit `u` of coefficient `v` lands at `v + s*u` ("all coefficients' least
/// significant digits come first, then their next digits").
///
/// Returns the digit plane vector of length `planes * coeffs.len()`.
///
/// # Panics
/// If `planes < ceil(log2 q)` — fewer planes cannot cover every residue, and a
/// truncated chain would silently drop the top digit.
pub fn decompose_planes<R: Ring>(coeffs: &[R], planes: usize) -> Vec<R> {
    let need = planes_needed::<R>();
    assert!(
        planes >= need,
        "negative-binary needs ceil(log2 q) = {need} planes, got {planes}"
    );
    let modulus = modulus_i128::<R>();
    let mut out = vec![R::ZERO; planes * coeffs.len()];
    for (v, c) in coeffs.iter().enumerate() {
        // The binary expansion of `-x mod q`, negated: x = sum 2^i * (-bit_i).
        let negated = (modulus - residue_i128(c)).rem_euclid(modulus) as u64;
        for u in 0..planes {
            if (negated >> u) & 1 == 1 {
                out[v + coeffs.len() * u] = -R::ONE;
            }
        }
    }
    out
}

/// The recomposition map `G_{{-1,0}}` of §4.5: `planes` plane-major digit
/// vectors back to one coefficient per input coefficient, `sum_u 2^u * xi_v+su`.
///
/// `planes` is the number of digit planes, so `digits.len() == planes *
/// coeffs` must hold for some `coeffs`; the caller supplies it because the
/// padded ring completion (§4.5, "appending zeros to fill the last element")
/// makes the coefficient count not recoverable from the length alone.
///
/// # Panics
/// If `digits.len() != planes * coeffs`.
pub fn recompose_planes<R>(digits: &[R], planes: usize, coeffs: usize) -> Vec<R>
where
    R: Ring + Add<Output = R> + Sub<Output = R> + Mul<Output = R> + Neg<Output = R> + AddAssign,
{
    assert_eq!(
        digits.len(),
        planes * coeffs,
        "plane-major digits must be planes x coeffs long"
    );
    let mut out = vec![R::ZERO; coeffs];
    for u in 0..planes {
        let weight = R::from(1u64 << u);
        for v in 0..coeffs {
            out[v] += weight * digits[v + coeffs * u];
        }
    }
    out
}

/// `ceil(log2 q)` — the negative-binary depth `delta` of §4.5, i.e. the least
/// number of `{ -1, 0 }` planes that can reach every residue.
pub fn planes_needed<R: Ring>() -> usize {
    let mut planes = 0usize;
    while planes < 128 && (1u128 << planes) < u128::from(R::MODULUS) {
        planes += 1;
    }
    assert!(
        (1u128 << planes) >= u128::from(R::MODULUS),
        "modulus too large for a negative-binary depth"
    );
    planes
}

/// Zero-pads a flat coefficient vector up to a whole number of ring elements
/// of dimension `d` (§4.5's "appending zeros to fill the last element").
///
/// # Panics
/// If `d` is zero.
pub fn pad_to_ring<R: Ring>(coeffs: &[R], d: usize) -> Vec<R> {
    assert!(d > 0, "ring dimension must be positive");
    let rem = coeffs.len() % d;
    if rem == 0 {
        return coeffs.to_vec();
    }
    let mut out = coeffs.to_vec();
    out.extend(core::iter::repeat(R::ZERO).take(d - rem));
    out
}

/// The centered integer coefficients of a ring element — the lift every
/// exact-norm statement in [`crate::pcs::norm_route`] is computed over.
pub fn centered_coeffs<R: CenteredRing, const D: usize>(v: &PolyRing<R, D>) -> Vec<i64> {
    v.coefficients().iter().map(|c| c.centered()).collect()
}

/// Akita's exact balanced decomposition, on a **flat base-field coefficient
/// vector read as ring elements of dimension `d`**, emitted in Eq. (107)'s
/// native-block order: item `j`, native subcolumn `y`, digit `u`, coefficient
/// `k` at `((j * s + y) * digits + u) * d + k`.
///
/// This is the form the recursive witness needs (§5.4: "The witness is a vector
/// of base-field coefficients. Each segment retains its own ring dimension"),
/// where the segment's width `D` and native dimension `d` are schedule values
/// rather than types, so `s = D / d` subcolumns are folded in.
///
/// The digit convention is the negatively biased `A_base` of
/// [`crate::pcs::gadget::split`]'s comment; the difference is what makes
/// [`halved_vanishing`] an identity, so the two splits are *not*
/// interchangeable. Each coefficient's canonical integer lift is chosen with the
/// threshold `T = min(T_k, floor(q/2))` of §3.3, which keeps the lift inside
/// `[-M_k, T_k]` and so needs no extra digit.
///
/// Recomposition is [`join_native`]; the two are exact inverses, which the
/// `native_split_join_roundtrip_*` tests pin against an independent integer
/// computation.
///
/// # Panics
/// If `base` is not a power of two `>= 2`, if `d` or `digits` is zero, if `s`
/// does not divide the item width, or if `[-M_digits, T_digits]` cannot hold
/// `R`'s canonical representatives.
pub fn split_native<R: Ring>(
    flat: &[R],
    d: usize,
    s: usize,
    base: u64,
    digits: usize,
) -> Vec<R> {
    assert!(d >= 1 && digits >= 1 && s >= 1, "dimensions must be positive");
    assert!(
        base >= 2 && base.is_power_of_two(),
        "the digit base must be a power-of-two >= 2"
    );
    assert!(flat.len() % (d * s) == 0, "items must be whole native blocks");
    let (neg, pos) = representable_interval(base, digits);
    let threshold = pos.min(u128::from(R::MODULUS) / 2);
    assert!(
        neg >= u128::from(R::MODULUS) - threshold - 1,
        "depth {digits} at base {base} cannot represent the ring: negative reach {neg} < q - T = {}",
        u128::from(R::MODULUS) - threshold - 1
    );
    let neg_i = i128::try_from(neg).expect("interval fits i128");
    let pos_i = i128::try_from(pos).expect("interval fits i128");
    let threshold_i = i128::try_from(threshold).expect("threshold fits i128");
    let half = i128::try_from(base / 2).expect("base fits i128");
    let modulus = modulus_i128::<R>();
    let base_i = i128::try_from(base).expect("base fits i128");

    let items = flat.len() / (d * s);
    let mut out = vec![R::ZERO; items * s * digits * d];
    for j in 0..items {
        for y in 0..s {
            for k in 0..d {
                let src = flat[(j * s + y) * d + k];
                let value = residue_i128(&src);
                let mut rem = if value > threshold_i {
                    value - modulus
                } else {
                    value
                };
                debug_assert!(
                    rem >= -neg_i && rem <= pos_i,
                    "the threshold lift must land inside the canonical interval"
                );
                for u in 0..digits {
                    let mut dig = rem.rem_euclid(base_i);
                    if dig > half - 1 {
                        dig -= base_i;
                    }
                    rem = (rem - dig) / base_i;
                    out[((j * s + y) * digits + u) * d + k] =
                        R::from(
                            u64::try_from(dig.rem_euclid(modulus))
                                .expect("a residue below q fits u64"),
                        );
                }
                debug_assert_eq!(rem, 0, "the digits must consume the whole value");
            }
        }
    }
    out
}

/// The gadget map `G_{b, items * s}` in native-block form: recomposes
/// [`split_native`]'s output back to one coefficient per input slot.
///
/// # Panics
/// If the digit vector is not `items * s * digits * d` long.
pub fn join_native<R: Ring>(digits: &[R], d: usize, s: usize, base: u64, count: usize) -> Vec<R> {
    assert!(d >= 1 && s >= 1, "dimensions must be positive");
    assert!(
        digits.len() % (d * s) == 0 && (digits.len() / (d * s)) % count == 0,
        "digit vector must be items x s x digits x d"
    );
    let depth = digits.len() / (d * s * count);
    let mut out = vec![R::ZERO; count * s * d];
    for slot in 0..count * s {
        for k in 0..d {
            // value = sum_u base^u * digit_u, the gadget map G_{b, -}.
            let mut acc = R::ZERO;
            let mut power = R::ONE;
            let b = R::from(base);
            for u in 0..depth {
                acc += power * digits[(slot * depth + u) * d + k];
                power *= b;
            }
            out[slot * d + k] = acc;
        }
    }
    out
}

/// The `ceil(log2 q)` planes the negative-binary chain needs, for a modulus
/// given directly (so a caller holding `R::MODULUS` can ask without naming a
/// type).
pub const fn planes_for_modulus(modulus: u64) -> usize {
    let mut planes = 0usize;
    while planes < 128 && (1u128 << planes) < (modulus as u128) {
        planes += 1;
    }
    planes
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sumcheck::range::{centered_digits, centered_vanishing_eval};
    use crate::foundation::encoding::ring_to_u32;
    use algebra::ring::zq::Zq;

    /// Akita's Table 5 modulus: `2^32 - 99`, prime and `5 mod 8`, so
    /// `X^d + 1` does **not** split completely (no NTT past degree 2).
    type Q32 = Zq<4294967197>;
    /// The crate's NTT-friendly prime, kept as the contrasting case.
    type Z1 = Zq<8380417>;

    const Q32_V: u64 = 4_294_967_197;

    fn elt<R: Ring, const D: usize>(vals: &[i64]) -> PolyRing<R, D> {
        PolyRing::from_coefficients(
            vals.iter()
                .map(|&v| R::from(i128::from(v).rem_euclid(i128::from(R::MODULUS)) as u64))
                .collect::<Vec<_>>(),
        )
    }

    #[test]
    fn halved_predicate_equals_the_full_alphabet_product() {
        // Q_sq(w(w+1)) == prod_{a in A_b} (w - a), the Eq. (114) identity,
        // checked against the crate's existing interval vanishing polynomial
        // so the two implementations cannot both be quietly wrong.
        for base in [4u64, 8, 16] {
            let (lo, hi) = alphabet(base);
            assert_eq!((lo, hi), centered_digits(base), "the crate's centered interval");
            for w in (lo - 3)..=(hi + 3) {
                let x = Q32::from(i128::from(w).rem_euclid(i128::from(Q32_V)) as u64);
                assert_eq!(
                    halved_vanishing(&x, base),
                    centered_vanishing_eval(&x, base),
                    "w = {w} at base {base}"
                );
            }
            // and the predicate is nonzero just outside the alphabet
            let outside = Q32::from(i128::from(hi + 1).rem_euclid(i128::from(Q32_V)) as u64);
            assert_ne!(halved_vanishing(&outside, base), Q32::ZERO, "hi + 1 must not vanish");
        }
    }

    #[test]
    fn the_negative_bias_is_what_enables_the_halving() {
        // The positively biased interval [-b/2 + 1, b/2] (what
        // pcs::gadget::split emits) has NO halved rewrite through w(w+1):
        // if the alphabet convention were irrelevant this would pass too.
        //
        // The comparison must discount the *common zeros*. The two alphabets
        // share b - 1 = 7 of their 8 elements, so at those 7 points both
        // polynomials vanish and trivially agree — a raw agreement count is
        // therefore meaningless (the first version of this test failed on
        // exactly that arithmetic, reporting 7/12). The substantive claim is
        // that the two agree NOWHERE except at a shared root.
        let base = 8u64;
        let (lo, hi) = alphabet(base);
        let (plo, phi) = (-((base / 2) as i64) + 1, (base / 2) as i64);
        assert_eq!((plo, phi), (lo + 1, hi + 1), "the two shifts of each other");
        let mut agrees = Vec::new();
        let mut differs_nonzero = 0;
        for w in (lo - 3)..=(phi + 3) {
            let x = Q32::from(i128::from(w).rem_euclid(i128::from(Q32_V)) as u64);
            let mut full = Q32::ONE;
            for a in plo..=phi {
                full *= x - Q32::from(i128::from(a).rem_euclid(i128::from(Q32_V)) as u64);
            }
            let halved = halved_vanishing(&x, base);
            if halved == full {
                assert_eq!(
                    full,
                    Q32::ZERO,
                    "w = {w}: the halved form agreed off a shared root"
                );
                agrees.push(w);
            } else {
                differs_nonzero += 1;
            }
        }
        // The two forms agree on **exactly** the shared roots of the two
        // alphabets and on nothing else in the window: both vanish there, each
        // is a product over its own eight roots so an agreement off a root would
        // be a collision of two nonzero field elements, and the two roots each
        // alphabet lacks — `w = -4` (negative only) and `w = 4` (positive only)
        // — are precisely where they part. `A_8 ∩ A_8^+ = {-3, …, 3}`.
        assert_eq!(
            agrees,
            ((lo + 1)..=hi).collect::<Vec<i64>>(),
            "only shared roots may agree"
        );
        assert!(
            differs_nonzero >= 7,
            "the check must be non-vacuous, got {differs_nonzero} disagreeing points"
        );
        // Concretely, the two points where the bias is visible in one
        // evaluation: w = 4 is a root of the positive alphabet but not of the
        // negative one, and w = -4 is the reverse.
        let four = Q32::from(4u64);
        let minus_four = Q32::from(i128::from(-4i64).rem_euclid(i128::from(Q32_V)) as u64);
        assert_ne!(halved_vanishing(&four, base), Q32::ZERO, "4 ∉ A_8");
        assert_eq!(halved_vanishing(&minus_four, base), Q32::ZERO, "-4 ∈ A_8");
        // and the halved value really is the degree-halved product: at w = 4
        // it is prod_{k<4} (20 - k(k+1)) = 20 * 18 * 14 * 8.
        assert_eq!(
            halved_vanishing(&four, base),
            Q32::from(20u64 * 18 * 14 * 8),
            "s = w(w+1) = 20 against the images 0, 2, 6, 12"
        );
    }

    #[test]
    fn compression_digits_are_exactly_the_negabinary_expansion() {
        // x = sum 2^i xi_i (mod q) with xi in {-1,0}, for the residues that
        // break a naive unsigned split.
        let planes = planes_needed::<Q32>();
        assert_eq!(planes, 32, "ceil(log2 (2^32 - 99)) = 32");
        for x in [0u64, 1, 2, Q32_V - 1, Q32_V / 2, 1 << 20, (1 << 31) + 7] {
            let c = [Q32::from(x)];
            let d = decompose_planes(&c, planes);
            assert!(
                d.iter().all(|v| *v == Q32::ZERO || *v == -Q32::ONE),
                "digits must lie in {{-1, 0}}, x = {x}"
            );
            assert_eq!(recompose_planes(&d, planes, 1)[0], Q32::from(x), "x = {x}");
        }
        // Two valid decompositions differ coefficientwise by at most one --
        // the collision bound MSIS(n, m, 1) of Lemma 4.3.
        let a = decompose_planes(&[Q32::from(7u64)], planes);
        let b = decompose_planes(&[Q32::from(Q32_V - 7)], planes);
        for (x, y) in a.iter().zip(b.iter()) {
            let diff = *x - *y;
            assert!(diff == Q32::ZERO || diff == Q32::ONE || diff == -Q32::ONE);
        }
    }

    #[test]
    fn negabinary_is_exact_over_a_ring_and_over_the_non_ntt_one() {
        let planes = planes_needed::<Z1>();
        assert_eq!(planes, 23);
        // A fixture that straddles the top plane on purpose. Bit 22 of
        // `-x mod q` is set iff `x <= q - 2^22 = 4_186_113`, so the nine small
        // coefficients this test first used light the top plane in *every*
        // coordinate and say nothing about a truncated chain; these five set it
        // and four clear it.
        let coeffs: Vec<Z1> = [5u64, 301, 4_194_303, 4_194_304, 12_345, 777, 4_186_113]
            .iter()
            .chain([Z1::MODULUS - 1, Z1::MODULUS - 7].iter())
            .map(|&v| Z1::from(v))
            .collect();
        let digits = decompose_planes(&coeffs, planes);
        assert_eq!(digits.len(), coeffs.len() * planes);
        assert_eq!(recompose_planes(&digits, planes, coeffs.len()), coeffs);
        // Plane-major layout, stated exactly rather than at one index: digit
        // `u` of coefficient `v` sits at `v + coeffs.len() * u`, and it is `-1`
        // iff bit `u` of `-x mod q` is set.
        for (v, x) in coeffs.iter().enumerate() {
            let negated = (Z1::MODULUS - x.to_u128() as u64) % Z1::MODULUS;
            for u in 0..planes {
                let want = if (negated >> u) & 1 == 1 { -Z1::ONE } else { Z1::ZERO };
                assert_eq!(digits[v + coeffs.len() * u], want, "v={v} u={u}");
            }
        }
        // Non-degenerate at the top plane, which is the one a truncated chain
        // would silently drop: some coefficients set bit 22 of `-x mod q`, some
        // do not, and the all-zero coefficient is all-zero in every plane.
        let top = planes - 1;
        let set = (0..coeffs.len())
            .filter(|&v| digits[v + coeffs.len() * top] == -Z1::ONE)
            .count();
        let clear = (0..coeffs.len())
            .filter(|&v| digits[v + coeffs.len() * top] == Z1::ZERO)
            .count();
        assert!(
            set > 0 && set < coeffs.len(),
            "top plane must be mixed, got {set} of {} set",
            coeffs.len()
        );
        assert_eq!(set + clear, coeffs.len());
        let zero = decompose_planes(&[Z1::ZERO], planes);
        assert!(zero.iter().all(|d| *d == Z1::ZERO), "0 needs no digit");
        assert_eq!(decompose_planes(&[Z1::ZERO, Z1::ONE], planes)[0], Z1::ZERO);
    }

    #[test]
    fn split_digits_land_in_the_alphabet_and_recompose_back() {
        const B: u64 = 8;
        const K: usize = 11; // ceil(log_8 (2^32 - 99))
        assert_eq!(K, ((Q32_V as f64).ln() / (B as f64).ln()).ceil() as usize);
        let values: Vec<PolyRing<Q32, 4>> = (0..3)
            .map(|i| elt::<Q32, 4>(&[i * 991, -i * 7 - 3, Q32_V as i64 / 2 + i, 13]))
            .collect();
        let digits = split::<Q32, 4, B, K>(&values);
        assert_eq!(digits.len(), values.len() * K);
        let (lo, hi) = alphabet(B);
        for d in &digits {
            for c in d.coefficients() {
                let v = c.centered();
                assert!(lo <= v && v <= hi, "digit {v} outside [{lo},{hi}]");
            }
        }
        // recomposition is the crate's base-only `join` (not duplicated here)
        let back = crate::pcs::gadget::join::<Q32, 4, B, K>(&digits);
        for (v, r) in values.iter().zip(back.iter()) {
            assert_eq!(ring_to_u32::<Q32, 4>(v), ring_to_u32::<Q32, 4>(r));
        }
    }

    #[test]
    fn interval_and_depth_formulas_track_the_paper_statements() {
        // [-M_k, T_k] holds exactly b^k integers (Eq. 111 / S3.3)
        for (b, k) in [(4u64, 3usize), (8, 5), (16, 2), (2, 8)] {
            let (neg, pos) = representable_interval(b, k);
            assert_eq!(neg + pos + 1, u128::from(b).pow(k as u32), "b={b} k={k}");
        }
        // the least depth covering a threshold (S5.4 rounding rule)
        assert_eq!(digit_depth(8, 27), Some(2), "T_2 = 3*(64-1)/7 = 27");
        assert_eq!(digit_depth(8, 28), Some(3));
        assert_eq!(
            digit_depth(2, 1),
            None,
            "the negative binary alphabet never reaches a positive threshold"
        );
        // the verifier-enforced envelope is wider than the honest interval
        // whenever b < b* (Eq. 112 vs 111)
        assert_eq!(cert_envelope(8, 4, 3), 4 * (64 - 1) / 3);
        assert!(cert_envelope(8, 4, 3) > 3 * (64 - 1) / 3);
        assert_eq!(cert_difference(8, 4, 3), 7 * (64 - 1) / 3);
    }

    #[test]
    fn pad_to_ring_fills_only_the_last_element() {
        let c: Vec<Z1> = (0..5).map(Z1::from).collect();
        let p = pad_to_ring(&c, 4);
        assert_eq!(p.len(), 8);
        assert_eq!(&p[..5], &c[..]);
        assert!(p[5..].iter().all(|v| *v == Z1::ZERO));
        assert_eq!(pad_to_ring(&c, 1).len(), 5);
    }

    #[test]
    fn derived_value_vanishes_exactly_on_the_binary_alphabet() {
        // Remark 6.2: the compression digits' binariness constraint is the
        // same quadratic the range check already derives.
        for v in [0i64, -1] {
            let x = Q32::from(i128::from(v).rem_euclid(i128::from(Q32_V)) as u64);
            assert_eq!(derived(&x), Q32::ZERO, "{v} must satisfy w(w+1)=0");
        }
        for v in [1i64, -2, 2, 3] {
            let x = Q32::from(i128::from(v).rem_euclid(i128::from(Q32_V)) as u64);
            assert_ne!(derived(&x), Q32::ZERO, "{v} must fail the binary check");
        }
    }
}
