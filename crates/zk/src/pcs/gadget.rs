//! Exact base-2 gadget decomposition (Z7, PCS support).
//!
//! The Greyhound gadget is `G_ℓ = I_ℓ ⊗ [1, 2, …, 2^{δ−1}] ∈ R^{ℓ×ℓδ}`:
//! it maps a digit vector (block layout `v[j·δ + k]` = digit `k` of value
//! `j`) to the value vector by digit recombination. Its inverse `G⁻¹`
//! splits every scalar coefficient of a ring element into its `δ = 23`
//! binary digits — the canonical representative `0..q` always fits, so the
//! split is *exact* (no slack, unlike the Z5 [`crate::shortness::gadget`]
//! flavor) and the output is binary with `‖·‖∞ = 1`.
//!
//! Greyhound applies the gadget three times: `sᵢ = G_m⁻¹(fᵢ)` on the
//! witness, `t̂ᵢ = G_n⁻¹(tᵢ)` on the inner commitments (which are not
//! short enough to feed the outer key), and `ŵ = G_r⁻¹(w)` on the row
//! combination — everywhere the verifier reconstructs values with `G`.

use crate::foundation::encoding::{ring_from_u32, ring_to_u32};
use crate::pcs::{RingElt, Z1Coeff, DELTA, DIM};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::{vec, vec::Vec};

/// Splits every scalar coefficient of each ring element into its `δ`
/// binary digits (block layout: `out[j·δ + k]` holds digit `k` of
/// `values[j]` at every coefficient position).
///
/// Exact inverse of [`recombine_digits`]; the output is always binary
/// (`‖·‖∞ = 1`), which is the soundness load of the norm gates.
pub fn decompose_digits(values: &[RingElt]) -> Vec<RingElt> {
    let mut out = Vec::with_capacity(values.len() * DELTA);
    for v in values {
        let rep = ring_to_u32::<Z1Coeff, DIM>(v);
        for k in 0..DELTA {
            let mut digits = [0u32; DIM];
            for (d, &c) in digits.iter_mut().zip(rep.iter()) {
                *d = (c >> k) & 1;
            }
            out.push(ring_from_u32::<Z1Coeff, DIM>(&digits));
        }
    }
    out
}

/// Recombines a block-layout digit vector into `digits.len() / δ` value
/// ring elements (the gadget map `G`). **Requires binary digits** — for
/// short-but-not-binary blocks (the folded opening `z`) use
/// [`recombine_digits_mod`].
///
/// Digit sums are computed in the `u32` representative domain: binary
/// digits across `δ = 23` positions sum to at most `2^23 − 1 < q`, so the
/// recombination is exact with no modular reduction.
///
/// # Panics
/// If `digits.len()` is zero or not a multiple of [`DELTA`] (debug builds
/// also reject non-binary digits, which would silently wrap in release).
pub fn recombine_digits(digits: &[RingElt]) -> Vec<RingElt> {
    assert!(
        !digits.is_empty() && digits.len() % DELTA == 0,
        "gadget digit vector must be a non-empty multiple of δ"
    );
    let reps: Vec<[u32; DIM]> = digits.iter().map(ring_to_u32::<Z1Coeff, DIM>).collect();
    (0..digits.len() / DELTA)
        .map(|j| {
            let mut rep = [0u32; DIM];
            for (k, block) in reps[j * DELTA..(j + 1) * DELTA].iter().enumerate() {
                for (r, &c) in rep.iter_mut().zip(block.iter()) {
                    debug_assert!(c <= 1, "recombine_digits requires binary digits");
                    *r += c << k;
                }
            }
            ring_from_u32::<Z1Coeff, DIM>(&rep)
        })
        .collect()
}

/// The gadget map `G` with **modular** digit recombination: output value
/// `j` is `Σ_k 2^k·digits[j·δ + k]` over `R_q`.
///
/// This is the variant for digit blocks that are short but not binary —
/// in the evaluation protocol that is the folded opening
/// `z = Σᵢ cᵢ·sᵢ` (norm `≤ r·d`, well below the gates, but far from
/// binary), where the `u32` shift path of [`recombine_digits`] would
/// overflow.
pub fn recombine_digits_mod(digits: &[RingElt]) -> Vec<RingElt> {
    assert!(
        !digits.is_empty() && digits.len() % DELTA == 0,
        "gadget digit vector must be a non-empty multiple of δ"
    );
    (0..digits.len() / DELTA)
        .map(|j| {
            // Horner from the top digit down: acc ← 2·acc + d_k, for
            // k = δ−1 … 0 (so d_0 ends with weight 2⁰).
            let mut acc = PolyRing::<Z1Coeff, DIM>::from_coefficients(vec![Z1Coeff::ZERO; DIM]);
            for (_, block) in digits[j * DELTA..(j + 1) * DELTA].iter().enumerate().rev() {
                let doubled = acc.clone() + &acc;
                acc = doubled + block.clone();
            }
            acc
        })
        .collect()
}

/// Multiplies a ring element by the ordinary integer `m`.
///
/// The ring has characteristic `q`, so `m`-fold addition *is* multiplication
/// by `m`; this is done with doublings so no scalar-multiplication operator
/// is needed on the polynomial ring type.
fn scale_by_int<R: Ring, const N: usize>(x: &PolyRing<R, N>, m: u64) -> PolyRing<R, N> {
    let zero = PolyRing::<R, N>::from_coefficients(vec![R::ZERO; N]);
    let mut acc = zero.clone();
    let mut addend = x.clone();
    let mut m = m;
    while m > 0 {
        if m & 1 == 1 {
            acc += addend.clone();
        }
        addend = addend.clone() + &addend;
        m >>= 1;
    }
    acc
}

/// The digit half-width of a base: the largest centered digit magnitude.
pub const fn digit_half_width(base: u64) -> u64 {
    base / 2
}

/// The **positive** integer span of a `DIGITS`-plane base-`BASE` expansion: the
/// largest value `Σ_k BASE^k·d_k` reaches when every digit is at its ceiling.
///
/// `BASE = 2` has digits `{0, 1}` and spans `[0, 2^DIGITS − 1]`; `BASE ≥ 3`
/// runs through [`digit_planes`]' rounding, whose digit set is
/// `[−(BASE − ⌊BASE/2⌋ − 1), ⌊BASE/2⌋]`. For an **odd** base that is symmetric,
/// `±⌊BASE/2⌋·(BASE^DIGITS − 1)/(BASE − 1)` — the balanced-range identity that
/// makes balanced ternary reach `(3^t − 1)/2`. For an **even** base it is not:
/// the ceiling is `BASE/2` but the floor is `−(BASE/2 − 1)`, so this function
/// overstates the negative side and [`digit_low_span`] is the matching half.
/// The geometric sum is accumulated directly rather than divided, so no
/// intermediate overflows before the result saturates.
///
/// This pair, not `BASE^DIGITS > q`, is the exactness criterion. The two
/// disagree in the direction that matters: a base-16, 8-plane expansion has
/// `16⁸ = 2³² > q = 2³² − 99` *and* `digit_span = 2 290 649 224 ≥ (q−1)/2`,
/// yet it cannot consume the least-absolute representative `−2 004 318 072`
/// because that is below `digit_low_span = 2 004 318 071`; the greedy loop
/// leaves residual `−1` and the planes recompose to a value `q` away from the
/// input. See `an_even_base_digit_set_is_asymmetric_so_the_span_guard_lies`.
pub const fn digit_span<const BASE: u64, const DIGITS: usize>() -> u128 {
    let half = (BASE / 2) as u128;
    half.saturating_mul(geometric_sum::<BASE, DIGITS>())
}

/// `1 + BASE + … + BASE^{DIGITS−1} = (BASE^DIGITS − 1)/(BASE − 1)`, saturating.
const fn geometric_sum<const BASE: u64, const DIGITS: usize>() -> u128 {
    let mut geometric: u128 = 0;
    let mut term: u128 = 1;
    let mut k = 0;
    while k < DIGITS {
        geometric = geometric.saturating_add(term);
        term = term.saturating_mul(BASE as u128);
        k += 1;
    }
    geometric
}

/// The **negative** magnitude [`digit_span`] pairs with: how far below zero a
/// `DIGITS`-plane base-`BASE` greedy expansion actually reaches.
///
/// `digit_planes` reduces a digit into `[0, BASE)` and folds it down only when
/// it is *strictly* above `⌊BASE/2⌋`, so the digit set is
/// `[−(BASE − ⌊BASE/2⌋ − 1), ⌊BASE/2⌋]` — for an even `BASE ≥ 4` the floor sits
/// one short of the ceiling, and for `BASE = 2` the expansion is one-sided
/// (`0`, because it consumes the canonical representative in `[0, q)`).
pub const fn digit_low_span<const BASE: u64, const DIGITS: usize>() -> u128 {
    // `BASE < 2` is not a positional system (digit_planes refuses it); clamp so
    // this predicate cannot underflow while reporting it as reaching nothing.
    let low = if BASE < 2 { 0 } else { BASE - BASE / 2 - 1 };
    (low as u128).saturating_mul(geometric_sum::<BASE, DIGITS>())
}

/// The largest magnitude the representative a `BASE`-ary split expands can
/// have: canonical in `[0, q)` for the binary gadget, least-absolute for the
/// balanced one.
const fn representative_ceiling<const BASE: u64>(modulus: u64) -> u128 {
    if BASE == 2 {
        modulus as u128 - 1
    } else {
        (modulus as u128 - 1) / 2
    }
}

/// [`digit_span`] over a runtime base and plane count.
#[must_use]
pub fn digit_span_of(base: u64, digits: usize) -> u128 {
    let half = u128::from(base / 2);
    half.saturating_mul(geometric_sum_of(base, digits))
}

/// [`digit_low_span`] over a runtime base and plane count.
#[must_use]
pub fn digit_low_span_of(base: u64, digits: usize) -> u128 {
    let low = if base < 2 {
        0
    } else {
        base - base / 2 - 1
    };
    u128::from(low).saturating_mul(geometric_sum_of(base, digits))
}

/// `1 + base + … + base^{digits−1}`, saturating.
fn geometric_sum_of(base: u64, digits: usize) -> u128 {
    let mut geometric: u128 = 0;
    let mut term: u128 = 1;
    for _ in 0..digits {
        geometric = geometric.saturating_add(term);
        term = term.saturating_mul(u128::from(base));
    }
    geometric
}

/// Does a `DIGITS`-plane base-`BASE` expansion consume **every** representative
/// its base expands, on both sides?
///
/// [`digit_span`]'s positive half and [`digit_low_span`]'s negative half must
/// both reach the representative ceiling the base expands (canonical in `[0,q)`
/// for `BASE = 2`, least-absolute for `BASE > 2`). For an odd base the digit
/// set is symmetric so the two coincide, and this is exactly the papers'
/// `q̃ := ⌊log_δ q⌋ + 1` rule (2023/846 Def. 2.13): `δ^q̃ ≥ q ⟹
/// (δ/2)·(δ^q̃ − 1)/(δ − 1) ≥ (q − 1)/2`. For an even base the greedy digit set
/// is one short below zero, so the papers' rule needs a plane of headroom and
/// this predicate is what says whether it has it.
#[must_use]
pub const fn digit_expansion_is_exact<const BASE: u64, const DIGITS: usize>(modulus: u64) -> bool {
    let ceiling = representative_ceiling::<BASE>(modulus);
    digit_span::<BASE, DIGITS>() >= ceiling
        // `BASE = 2` never centers, so it has no negative side to reach.
        && (BASE == 2 || digit_low_span::<BASE, DIGITS>() >= ceiling)
}

/// [`digit_expansion_is_exact`] over a runtime base and plane count.
#[must_use]
pub fn digit_expansion_is_exact_of(base: u64, digits: usize, modulus: u64) -> bool {
    let ceiling = representative_ceiling_of(base, modulus);
    digit_span_of(base, digits) >= ceiling
        && (base == 2 || digit_low_span_of(base, digits) >= ceiling)
}

/// The representative window a runtime base expands on modulus `q`.
#[must_use]
pub fn representative_ceiling_of(base: u64, modulus: u64) -> u128 {
    if base == 2 {
        u128::from(modulus) - 1
    } else {
        (u128::from(modulus) - 1) / 2
    }
}

/// The shared base-`base` digit expansion behind [`split`] and
/// [`crate::pcs::dotproduct::Decomposition`], over the runtime base.
///
/// Which representative is expanded depends on the digit set the base admits:
/// - `base = 2`: digits `{0, 1}`, so the **canonical** representative in
///   `[0, q)` (the Greyhound / SLAP binary gadget);
/// - `base ≥ 3`: the symmetric digit set `[−⌊base/2⌋, ⌊base/2⌋]`, so the
///   **least-absolute** representative. That is what lets a *short* object be
///   decomposed in planes sized by its own magnitude rather than by `log q`
///   (LaBRADOR §5.4's `t₂` for the garbage `g⃗`); expanding a canonical value
///   near `q` would need `⌈log q/log base⌉` planes and defeat the budget.
///
/// Either way `value ≡ Σ_k base^k·plane_k (mod q)`, so the verifier's check is
/// a ring equality. Layout is `out[j·digits + k]` = plane `k` of `values[j]`,
/// every plane padded to the full ring degree.
///
/// # Panics
/// If `base < 2`, `digits == 0`, or some coefficient cannot be consumed by
/// `digits` planes. The refusal is **two-sided**: the greedy loop consumes
/// `[−digit_low_span_of(base, digits), digit_span_of(base, digits)]`, and past
/// either edge it leaves a residual, so the planes would recombine to a value
/// `q` away from the input. Testing `|x| ≤ digit_span_of` alone is not enough —
/// for an even base the negative edge is one digit short of the positive one.
pub fn digit_planes<R: Ring, const D: usize>(
    values: &[PolyRing<R, D>],
    base: u64,
    digits: usize,
) -> Vec<PolyRing<R, D>> {
    assert!(base >= 2, "a digit base below 2 is not a positional system");
    assert!(digits >= 1, "the gadget needs at least one digit");
    let modulus = i128::from(R::MODULUS);
    let half = i128::from(digit_half_width(base));
    let base_i = i128::from(base);
    let span = i128::try_from(digit_span_of(base, digits)).unwrap_or(i128::MAX);
    let low_span = i128::try_from(digit_low_span_of(base, digits)).unwrap_or(i128::MAX);
    // The digit `d = x mod base`, folded down when strictly above `half`.
    let digit_floor = -(base_i - half - 1);
    let mut out = Vec::with_capacity(values.len() * digits);
    for (j, v) in values.iter().enumerate() {
        let mut planes = vec![vec![R::ZERO; D]; digits];
        for (i, &c) in v.coefficients().iter().enumerate() {
            let mut x = i128::try_from(c.to_u128()).expect("a canonical residue fits i128");
            if base > 2 && 2 * x > modulus {
                x -= modulus;
            }
            assert!(
                x <= span && -x <= low_span,
                "coefficient {i} of value {j} is {x}, outside [{}, {span}] — the range a \
                 {digits}-plane base-{base} expansion consumes (its digit set is [{digit_floor}, \
                 {half}], asymmetric below zero when BASE is even; the greedy loop would leave a \
                 residual and the planes would recompose to a value q away from the input)",
                -low_span,
            );
            for plane in planes.iter_mut() {
                let mut d = x.rem_euclid(base_i);
                if d > half {
                    d -= base_i;
                }
                x = (x - d) / base_i;
                plane[i] = R::from(d.rem_euclid(modulus) as u64);
            }
            debug_assert_eq!(x, 0, "the two-sided range check above makes this exact");
        }
        out.extend(planes.into_iter().map(PolyRing::from_coefficients));
    }
    out
}

/// Exact gadget split, **generic over the instance**: ring degree `D`,
/// scalar ring `R`, digit base `BASE` and digit count `DIGITS`.
///
/// Layout matches [`decompose_digits`]: `out[j·DIGITS + k]` is digit plane
/// `k` of value `j`, i.e. a ring element whose coefficient `i` carries the
/// `k`-th digit of coefficient `i` of `values[j]`.
///
/// Digit convention (see [`digit_planes`], which this wraps):
/// - `BASE = 2` reproduces the binary gadget — digits `{0,1}` over the
///   canonical representative, `‖·‖∞ = 1`;
/// - `BASE > 2` gives **balanced (centered)** digits over the least-absolute
///   representative, which is what LaBRADOR's `t₁`/`t₂` splits and Akita's digit
///   planes need (survey §4 gaps G4). The digit set is
///   `[−(BASE − ⌊BASE/2⌋ − 1), ⌊BASE/2⌋]`, symmetric only for an **odd** base;
///   the digits satisfy `value = Σ_k digit_k · BASE^k` over the integers, hence
///   in `R_q`, exactly when [`digit_planes`]' two-sided range admits the input.
///
/// # Panics
/// If `BASE < 2`, `DIGITS == 0`, or a coefficient is outside the range the
/// expansion consumes — [`digit_span`] and [`digit_low_span`] must both reach
/// the representative ceiling for *every* residue of `R` to be splittable,
/// which is the predicate [`digit_expansion_is_exact`] decides. The guard here
/// is the (weaker, one-sided) `digit_span ≥ ceiling` that has always been in
/// this signature — for `BASE = 2` the usual `2^DIGITS > q − 1`, for a balanced
/// base `(BASE/2)·(BASE^DIGITS − 1)/(BASE − 1) ≥ (q − 1)/2` — and the
/// coefficient-level refusal is in [`digit_planes`]. `BASE^DIGITS > q` alone is
/// not enough on either count: see [`digit_span`]'s doc.
pub fn split<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    values: &[PolyRing<R, D>],
) -> Vec<PolyRing<R, D>> {
    assert!(
        digit_span::<BASE, DIGITS>() >= representative_ceiling::<BASE>(R::MODULUS),
        "a {DIGITS}-plane base-{BASE} expansion spans {} but must reach {} to be exact on Z_{}",
        digit_span::<BASE, DIGITS>(),
        representative_ceiling::<BASE>(R::MODULUS),
        R::MODULUS
    );
    digit_planes::<R, D>(values, BASE, DIGITS)
}

/// The gadget map `G` in its generic form: recombines `DIGITS` planes per
/// value as `Σ_k BASE^k · digits[j·DIGITS + k]`, over the ring.
///
/// # Panics
/// If `digits` is empty or not a multiple of `DIGITS`.
pub fn join<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    digits: &[PolyRing<R, D>],
) -> Vec<PolyRing<R, D>> {
    assert!(
        !digits.is_empty() && digits.len() % DIGITS == 0,
        "gadget digit vector must be a non-empty multiple of DIGITS"
    );
    (0..digits.len() / DIGITS)
        .map(|j| {
            // Horner from the top digit down: acc ← BASE·acc + d_k.
            let mut acc = PolyRing::<R, D>::from_coefficients(vec![R::ZERO; D]);
            for block in digits[j * DIGITS..(j + 1) * DIGITS].iter().rev() {
                acc = scale_by_int(&acc, BASE) + block.clone();
            }
            acc
        })
        .collect()
}

/// `BASE^DIGITS` as a `u128`, saturating on overflow.
///
/// This is *not* the exactness criterion — [`digit_span`] is — but the two
/// coincide for the binary gadget, and callers that size a gadget by eye
/// reason in capacities.
pub const fn capacity<const BASE: u64, const DIGITS: usize>() -> u128 {
    let mut acc: u128 = 1;
    let mut k = 0;
    while k < DIGITS {
        acc = match acc.checked_mul(BASE as u128) {
            Some(v) => v,
            None => return u128::MAX,
        };
        k += 1;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use algebra::ring::traits::CenteredRing;
    use algebra::ring::PolynomialQuotientRing;
    use alloc::vec;

    /// Deterministic test ring element with coefficients in `[-4, 4]`.
    fn test_elt(seed: u64) -> RingElt {
        let coeffs: Vec<_> = (0..DIM)
            .map(|j| from_centered::<Z1Coeff>(((seed as i64 * 7 + j as i64 * 5) % 9) - 4))
            .collect();
        algebra::ring::poly_ring::PolyRing::from_coefficients(coeffs)
    }

    #[test]
    fn decompose_recombine_is_exact_and_binary() {
        let values: Vec<RingElt> = (0..5).map(|i| test_elt(i + 1)).collect();
        let digits = decompose_digits(&values);
        assert_eq!(digits.len(), values.len() * DELTA);
        // every digit element is binary
        for d in &digits {
            for c in ring_to_u32::<Z1Coeff, DIM>(d) {
                assert!(c <= 1, "gadget digits must be binary");
            }
        }
        // recombination is the identity on the canonical representatives
        let rec = recombine_digits(&digits);
        assert_eq!(rec.len(), values.len());
        for (v, r) in values.iter().zip(&rec) {
            assert_eq!(
                ring_to_u32::<Z1Coeff, DIM>(v),
                ring_to_u32::<Z1Coeff, DIM>(r)
            );
        }
    }

    #[test]
    fn modular_recombine_matches_binary_path_and_wraps() {
        // On binary input both recombination paths agree exactly.
        let values: Vec<RingElt> = (0..3).map(|i| test_elt(i + 2)).collect();
        let digits = decompose_digits(&values);
        let fast = recombine_digits(&digits);
        let modular = recombine_digits_mod(&digits);
        for (f, m) in fast.iter().zip(&modular) {
            assert_eq!(
                ring_to_u32::<Z1Coeff, DIM>(f),
                ring_to_u32::<Z1Coeff, DIM>(m)
            );
        }

        // Short-but-not-binary digits: coefficients large enough to wrap
        // the u32 shift path (2^12 ≪ q) must reduce modulo q correctly.
        let mut heavy = [0u32; DIM];
        heavy[5] = 4096; // z-coefficient bound r·d ≪ 2^23
        let digit = ring_from_u32::<Z1Coeff, DIM>(&heavy);
        let block: Vec<RingElt> = (0..DELTA).map(|_| digit.clone()).collect();
        let out = &recombine_digits_mod(&block)[0];
        // coefficient 5 picks up Σ_k 2^k·4096 mod q, all others stay 0
        let expected = (4096u64 * ((1u64 << DELTA) - 1)) % 8_380_417;
        let rep = ring_to_u32::<Z1Coeff, DIM>(out);
        assert_eq!(rep[5], expected as u32);
        assert_eq!(rep[0], 0);
        assert_eq!(rep[6], 0);
    }

    #[test]
    fn recombine_rejects_bad_block_length() {
        let digits = decompose_digits(&[test_elt(1)]);
        let short = &digits[..digits.len() - 1];
        assert!(short.len() % DELTA != 0);
        let _ = std::panic::catch_unwind(|| recombine_digits(short))
            .expect_err("non-multiple of δ must panic");
    }

    #[test]
    fn digits_cover_full_coefficient_range() {
        // a coefficient at the top of the range needs all δ digits
        let mut coeffs = [0u32; DIM];
        coeffs[3] = 8_380_416; // q − 1
        let v = vec![ring_from_u32::<Z1Coeff, DIM>(&coeffs)];
        let rec = recombine_digits(&decompose_digits(&v));
        assert_eq!(ring_to_u32::<Z1Coeff, DIM>(&rec[0]), coeffs);
        // centered infinity norm of the digit elements is 1 everywhere
        for d in decompose_digits(&v) {
            for c in ring_to_u32::<Z1Coeff, DIM>(&d) {
                let centered = Z1Coeff::from(u64::from(c)).abs_infinity();
                assert!(centered <= 1);
            }
        }
    }

    #[test]
    fn generic_binary_split_matches_the_concrete_one() {
        // G1 slice: the generic path over the same (D, base 2, δ) must be
        // bit-identical to the instance Greyhound uses today.
        let values: Vec<RingElt> = (0..4).map(|i| test_elt(i + 1)).collect();
        let generic: Vec<RingElt> = super::split::<Z1Coeff, DIM, 2, DELTA>(&values);
        assert_eq!(generic, decompose_digits(&values));
        assert_eq!(
            super::join::<Z1Coeff, DIM, 2, DELTA>(&generic),
            recombine_digits_mod(&decompose_digits(&values))
        );
    }

    #[test]
    fn balanced_base_split_is_exact_and_within_the_half_width() {
        // G4 slice: base 16, 6 digits over the Z1 ring (16^6 ≫ q).
        const B16: u64 = 16;
        const K6: usize = 6;
        let values: Vec<RingElt> = (0..3).map(|i| test_elt(i + 1)).collect();
        let digits = super::split::<Z1Coeff, DIM, B16, K6>(&values);
        assert_eq!(digits.len(), values.len() * K6);

        // every digit coefficient lies in [-8, 8]
        for d in &digits {
            for c in ring_to_u32::<Z1Coeff, DIM>(d) {
                let mag = Z1Coeff::from(u64::from(c)).abs_infinity();
                assert!(mag <= digit_half_width(B16), "digit {c} out of range");
            }
        }
        // and recombination is the identity
        let back = super::join::<Z1Coeff, DIM, B16, K6>(&digits);
        for (v, r) in values.iter().zip(back.iter()) {
            assert_eq!(
                ring_to_u32::<Z1Coeff, DIM>(v),
                ring_to_u32::<Z1Coeff, DIM>(r)
            );
        }
    }

    #[test]
    fn balanced_digits_match_a_hand_computed_expansion() {
        // Independent of `join`: round-tripping alone would also pass if
        // split and join were wrong in matching ways, so the digits of four
        // hand-worked values are asserted directly.
        //   8 -> d0 = 8            (exactly at the half-width, not pushed up)
        //   9 -> d0 = -7, d1 = 1   (16 - 7)
        //  12 -> d0 = -4, d1 = 1   (16 - 4)
        // 100 -> d0 = 4, d1 = 6     (4 + 96)
        const B16: u64 = 16;
        type E64 = algebra::ring::poly_ring::PolyRing<Z1Coeff, 4>;
        let value = E64::from_coefficients(vec![
            from_centered::<Z1Coeff>(8),
            from_centered::<Z1Coeff>(9),
            from_centered::<Z1Coeff>(12),
            from_centered::<Z1Coeff>(100),
        ]);
        // 6 digits: 16^6 = 16 777 216 > q, which the capacity guard insists
        // on (a 2-digit call panics here rather than wrapping silently).
        const K6: usize = 6;
        let digits = super::split::<Z1Coeff, 4, B16, K6>(&[value]);
        assert_eq!(digits.len(), K6);
        let want_low = [8i64, -7, -4, 4];
        let want_high = [0i64, 1, 1, 6];
        for (i, (wl, wh)) in want_low.iter().zip(want_high.iter()).enumerate() {
            let l = digits[0].coefficients()[i].centered();
            let h = digits[1].coefficients()[i].centered();
            assert_eq!(l, *wl, "low digit of coefficient {i}");
            assert_eq!(h, *wh, "high digit of coefficient {i}");
        }
        // the remaining planes must be empty for these small values
        for plane in &digits[2..] {
            for c in plane.coefficients() {
                assert_eq!(c.centered(), 0, "planes above digit 1 must be zero here");
            }
        }
    }

    #[test]
    fn split_refuses_a_capacity_that_cannot_hold_the_modulus() {
        // 2^3 < q: the split would silently wrap, so it must panic.
        let values: Vec<RingElt> = vec![test_elt(1)];
        let r = std::panic::catch_unwind(|| super::split::<Z1Coeff, DIM, 2, 3>(&values));
        assert!(
            r.is_err(),
            "BASE^DIGITS <= q must be rejected, not approximated"
        );
    }

    #[test]
    fn a_smaller_ring_degree_works_too() {
        // The point of the generalization: another instance (d = 64) must be
        // expressible without touching the Z1 constants.
        type E64 = algebra::ring::poly_ring::PolyRing<Z1Coeff, 64>;
        let vals: Vec<E64> = (0..2)
            .map(|i| {
                let coeffs: Vec<_> = (0..64)
                    .map(|j| from_centered::<Z1Coeff>(((i * 13 + j) % 200) as i64 - 100))
                    .collect();
                E64::from_coefficients(coeffs)
            })
            .collect();
        let digits = super::split::<Z1Coeff, 64, 2, DELTA>(&vals);
        assert_eq!(digits.len(), 2 * DELTA);
        let back = super::join::<Z1Coeff, 64, 2, DELTA>(&digits);
        for (v, r) in vals.iter().zip(back.iter()) {
            assert_eq!(
                crate::foundation::encoding::ring_to_u32::<Z1Coeff, 64>(v),
                crate::foundation::encoding::ring_to_u32::<Z1Coeff, 64>(r)
            );
        }
    }

    #[test]
    fn digit_span_is_the_balanced_range() {
        // Binary: digits {0,1} span [0, 2^t − 1].
        assert_eq!(digit_span::<2, 1>(), 1);
        assert_eq!(digit_span::<2, 23>(), (1u128 << 23) - 1);
        // Balanced ternary: digits {−1,0,1} span ±(3^t − 1)/2.
        assert_eq!(digit_span::<3, 1>(), 1);
        assert_eq!(digit_span::<3, 4>(), (81 - 1) / 2);
        // Base 16: digits [−8, 8] span ±8·(16^t − 1)/15.
        assert_eq!(digit_span::<16, 1>(), 8);
        assert_eq!(digit_span::<16, 2>(), 8 + 8 * 16);
        assert_eq!(digit_span::<16, 8>(), 8 * ((16u128.pow(8) - 1) / 15));
        // The runtime form must agree with the const one at every shape.
        for base in 2..=17u64 {
            for digits in 1..12usize {
                let mut g = 0u128;
                let mut term = 1u128;
                for _ in 0..digits {
                    g = g.saturating_add(term);
                    term = term.saturating_mul(u128::from(base));
                }
                let hand = u128::from(base / 2).saturating_mul(g);
                assert_eq!(digit_span_of(base, digits), hand, "({base}, {digits})");
            }
        }
    }

    #[test]
    fn a_balanced_base_expands_the_least_absolute_representative() {
        // The bug this pins: with q = 2³² − 99, base 16 and 8 planes,
        // `16⁸ = 2³² > q` satisfied the old capacity guard, but the digits
        // only span ±2 290 649 168, so expanding a *canonical* value near q
        // left residual 1 and the planes recomposed to `value − 2³²` — wrong by
        // 99 in Z_q, not by a rounding fuzz. A balanced digit set must therefore
        // expand the least-absolute representative, which is what `digit_planes`
        // does; 7 planes are still too few and must be refused.
        //
        // Caveat this test does NOT cover, and
        // `an_even_base_digit_set_is_asymmetric_so_the_span_guard_lies` does:
        // 8 planes at base 16 reach `+2 290 649 224` but only
        // `−2 004 318 071`, so "every residue" holds of the positive half only.
        // These four values sit inside both halves.
        type Q5 = algebra::ring::zq::Zq<4_294_967_197>;
        const Q: u64 = 4_294_967_197;
        assert!(
            capacity::<16, 8>() > u128::from(Q),
            "the old guard was satisfied"
        );
        assert!(
            digit_span::<16, 8>() < u128::from(Q) - 1,
            "canonical would not fit"
        );
        assert!(digit_span::<16, 8>() >= representative_ceiling::<16>(Q));
        assert!(digit_span::<16, 7>() < representative_ceiling::<16>(Q));

        let values = vec![
            algebra::ring::poly_ring::PolyRing::<Q5, 4>::from_coefficients(vec![
                Q5::from(Q - 100),
                Q5::from(1u64),
                Q5::from(Q - 1),
                Q5::from(Q / 2),
            ]),
        ];
        let eight = super::split::<Q5, 4, 16, 8>(&values);
        assert_eq!(
            super::join::<Q5, 4, 16, 8>(&eight),
            values,
            "8 centered planes must round-trip every residue"
        );
        for plane in &eight {
            for c in plane.coefficients() {
                assert!(
                    c.abs_infinity() <= digit_half_width(16),
                    "digit {} exceeds the half-width",
                    c.abs_infinity()
                );
            }
        }
        let r = std::panic::catch_unwind(|| super::split::<Q5, 4, 16, 7>(&values));
        assert!(r.is_err(), "7 planes must be refused by the span");
    }

    /// The defect this pins, and the reason both trapdoor assemblies state their
    /// gadget base by hand.
    ///
    /// `digit_planes` folds a digit down only when it is *strictly* above
    /// `⌊BASE/2⌋`, so an even base has an asymmetric digit set: base 256 yields
    /// `[-127, 128]`, not `[-128, 128]`. `digit_span` scales the geometric sum by
    /// the *ceiling*, so the guard in `split` declares `256`/`4` planes exact at
    /// `q = 2³² − 99` (`2 155 905 152 ≥ 2 147 483 598`) when the expansion reaches
    /// only `−2 139 062 143` — short by `8 421 455`, i.e. `0.39 %` of the range.
    /// That is not a rounding fuzz: a value in the gap leaves residual `−1`, so
    /// the planes recompose to `value + 1 − q` and `G·G⁻¹(v) = v` fails outright,
    /// which is what `pcs::slap_tree`'s tests panic on with `(256, 4)`
    /// (`assertion \`left == right\` failed: the span check above makes this
    /// exact, left: -1, right: 0`). Both example assemblies therefore pick an
    /// exact shape — FMN `(8, 11)`, Akita `(8, 11)` — and the SLAP binary gadget
    /// is exact because base 2 never centers.
    ///
    /// The `digit_low_span` / `digit_expansion_is_exact` assertions cannot hold
    /// without those items, so this test does not compile against the behaviour
    /// it replaces; the `split` refusal at the end is the runtime half.
    #[test]
    fn an_even_base_digit_set_is_asymmetric_so_the_span_guard_lies() {
        type Q5 = algebra::ring::zq::Zq<4_294_967_197>;
        const Q: u64 = 4_294_967_197;
        let ceiling = representative_ceiling::<256>(Q);
        assert_eq!(
            ceiling,
            u128::from((Q - 1) / 2),
            "base 256 expands the centered rep"
        );

        // The guard `split` has always run: satisfied.
        assert!(digit_span::<256, 4>() >= ceiling);
        // The half it never looked at: NOT satisfied.
        assert_eq!(digit_low_span::<256, 4>(), 127 * ((256u128.pow(4) - 1) / 255));
        assert!(digit_low_span::<256, 4>() < ceiling);
        assert!(!digit_expansion_is_exact::<256, 4>(Q));
        assert!(digit_expansion_is_exact::<256, 5>(Q), "one plane of headroom fixes base 256");

        // An odd base has the symmetric digit set, so the papers' own
        // `q̃ := ⌊log_δ q⌋ + 1` (2023/846 Def. 2.13) is exact as stated.
        assert!(digit_span::<3, 21>() >= ceiling && digit_low_span::<3, 21>() >= ceiling);
        assert!(digit_expansion_is_exact::<3, 21>(Q));
        assert!(!digit_expansion_is_exact::<3, 20>(Q));
        assert!(digit_expansion_is_exact::<9, 11>(Q));
        assert!(!digit_expansion_is_exact::<9, 10>(Q));

        // Even bases: 16/8 (the case the module's own doc used to call exact) is
        // not; 16/9 is. 8/11 and 4/17 are, which is what FMN/Akita run on.
        assert!(!digit_expansion_is_exact::<16, 8>(Q));
        assert!(digit_expansion_is_exact::<16, 9>(Q));
        assert!(digit_expansion_is_exact::<8, 11>(Q));
        assert!(!digit_expansion_is_exact::<8, 10>(Q));
        assert!(digit_expansion_is_exact::<4, 17>(Q));
        assert!(!digit_expansion_is_exact::<4, 16>(Q));
        // Binary: one-sided over the canonical rep, and exact at 32 planes.
        assert!(digit_expansion_is_exact::<2, 32>(Q));
        assert!(!digit_expansion_is_exact::<2, 31>(Q));
        assert_eq!(digit_low_span::<2, 32>(), 0, "base 2 has no negative side");
        // the runtime form agrees with the const one at every shape probed above
        for (base, digits) in [(3u64, 21usize), (8, 11), (9, 10), (16, 8), (256, 4), (2, 32)] {
            assert_eq!(
                digit_expansion_is_exact_of(base, digits, Q),
                matches!((base, digits), (3, 21) | (8, 11) | (2, 32)),
                "({base}, {digits})"
            );
        }

        // The runtime half: a value inside the gap must be refused, not silently
        // mis-expanded. `-(q-1)/2` is `8 421 455` past base 256's negative reach.
        let gap = Q - (Q - 1) / 2;
        assert_eq!(u128::from(gap), u128::from(Q) - ceiling);
        let value = vec![algebra::ring::poly_ring::PolyRing::<Q5, 4>::from_coefficients(vec![
            Q5::from(gap),
            Q5::ZERO,
            Q5::ZERO,
            Q5::ZERO,
        ])];
        let refused = std::panic::catch_unwind(|| super::split::<Q5, 4, 256, 4>(&value));
        assert!(
            refused.is_err(),
            "a value below the negative reach must panic, not return planes that \
             recompose to value + 1 - q"
        );
        // The same value through an exact shape round-trips.
        let eight = super::split::<Q5, 4, 8, 11>(&value);
        assert_eq!(super::join::<Q5, 4, 8, 11>(&eight), value);
    }
}
