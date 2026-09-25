//! Vanishing-polynomial range and bit checks (Z3; survey §1.3 item 4).
//!
//! LatticeFold proves digit shortness with a vanishing polynomial instead
//! of a norm gate: `g_b(X) = ∏_{i=1..b}(X − i)(X + i)` has zero set exactly
//! `[−b, b]` over the centered integers, so a claim "`g_b(u) == 0`" on a
//! folded evaluation `u` certifies "every digit is in range" — and a
//! Booleanity claim "`X² − X == 0`" certifies bits. Both fold into the
//! batched sumcheck as one more assertion via [`range_claim_table`].
//!
//! # Exactness
//!
//! Over a **prime** ring the check is exact, not heuristic, for canonical
//! representatives: `g_b(w₀) ≡ 0 (mod q)` with `q` prime forces some factor
//! `w₀² ≡ i²`, i.e. `w₀ ≡ ±i (mod q)`; the representative `w₀ ∈ (−q/2, q/2]`
//! then equals `±i` exactly (the other root `q − i` lands outside the
//! centered range once `2b < q`). The same argument gives exact bits for
//! `X² − X` (`w₀, w₀ − 1 < q`, so `q | w₀(w₀ − 1)` forces `w₀ ∈ {0, 1}`).
//! Over power-of-two rings zero divisors make the vanishing check
//! unsound — [`range_check`] and [`bit_check`] assert primality, and the
//! 2-adic line keeps its norm gates.

use super::MatrixElement;
use algebra::ring::traits::CenteredRing;
use algebra::ring::Ring;
use alloc::vec::Vec;

/// Evaluates the digit-vanishing polynomial `g_b(w) = ∏_{i=1..b}(w² − i²)`
/// over the ring (Horner-free: `b` factors, `b` squarings).
///
/// # Panics
/// If `b == 0` (degenerate; the check would reduce to `w == 0`).
pub fn vanishing_eval<R: Ring>(w: &R, b: u64) -> R {
    assert!(b >= 1, "the vanishing polynomial needs at least one factor");
    // ∏_{i=0..b}(w − i)(w + i) = w²·∏_{i=1..b}(w² − i²): the i = 0 factor
    // is what puts 0 itself into the zero set [−b, b].
    let mut acc = w.square();
    for i in 1..=b {
        let i_sq = R::from(i * i);
        acc *= w.square() - i_sq;
    }
    acc
}

/// The digit-range check `g_b(w) == 0`: exact over prime rings for the
/// centered representative with `2·b < q` (see the module docs).
///
/// # Panics
/// If the ring is not prime (the vanishing check is unsound over `2^k`).
pub fn range_check<R: CenteredRing>(w: &R, b: u64) -> bool {
    assert!(
        R::IS_PRIME,
        "the vanishing range check is exact only over prime rings"
    );
    vanishing_eval(w, b) == R::ZERO
}

/// Evaluates the Booleanity polynomial `w² − w` (zero set exactly `{0,1}`).
pub fn bit_eval<R: Ring>(w: &R) -> R {
    w.square() - *w
}

/// The bit check `w² − w == 0`: exact over prime rings for canonical
/// representatives (see the module docs).
///
/// # Panics
/// If the ring is not prime (the vanishing check is unsound over `2^k`).
pub fn bit_check<R: Ring>(w: &R) -> bool {
    assert!(
        R::IS_PRIME,
        "the vanishing bit check is exact only over prime rings"
    );
    bit_eval(w) == R::ZERO
}

/// Turns a truth table into a **range claim** for the batched sumcheck:
/// the returned table is `g_b` applied position-wise, and its honest sum
/// is zero exactly when *every* entry is in `[−b, b]` (the "a sumcheck
/// over the ℓ variables proves every digit is in range" shape of survey
/// §1.3 item 4). Feed it to `batch::prove_batched` with claimed sum `0`.
///
/// # Panics
/// If the ring is not prime (see [`range_check`]).
pub fn range_claim_table<R>(table: &[R], b: u64) -> Vec<R>
where
    R: MatrixElement + Ring + Clone,
{
    assert!(
        R::IS_PRIME,
        "the vanishing range check is exact only over prime rings"
    );
    table.iter().map(|t| vanishing_eval(t, b)).collect()
}

/// The **centered** digit set of `b` values: `[lo, lo + b − 1]` with
/// `lo = −⌊b/2⌋`, so 16 digits are `{−8, …, 7}` and 3 are `{−1, 0, 1}`.
///
/// This is the set balanced base-`b` decomposition actually produces — and
/// it is *not* symmetric about zero when `b` is even, which is why the
/// symmetric [`vanishing_eval`] cannot express it.
pub const fn centered_digits(b: u64) -> (i64, i64) {
    assert!(b >= 1, "a digit set needs at least one value");
    let lo = -((b / 2) as i64);
    (lo, lo + b as i64 - 1)
}

/// The vanishing polynomial of an arbitrary integer interval:
/// `∏_{t = lo..=hi} (w − t)`, zero exactly on those integers.
///
/// # Panics
/// If `hi < lo` (empty interval) or the interval spans the modulus.
pub fn vanishing_eval_interval<R: Ring>(w: &R, lo: i64, hi: i64) -> R {
    assert!(hi >= lo, "the interval must not be empty");
    assert!(
        u128::try_from(hi - lo + 1)
            .map(|n| n < u128::from(R::MODULUS))
            .unwrap_or(true),
        "an interval of at least q values vanishes everywhere and proves nothing"
    );
    let mut acc = R::ONE;
    let mut t = lo;
    while t <= hi {
        acc *= *w - crate::foundation::sampling::from_centered::<R>(t);
        t += 1;
    }
    acc
}

/// The vanishing polynomial of the centered `b`-digit set.
///
/// For `b = 16` this is Hachi's balanced-norm gate (eprint 2026/156 eq. 23
/// specialised to centered digits), `∏_{i=−8..7}(w − i) = (w² + 8w) ·
/// ∏_{k=1..7}(w² − k²)` — degree 16, composed into the sumcheck round
/// polynomial on top of it.
pub fn centered_vanishing_eval<R: Ring>(w: &R, b: u64) -> R {
    let (lo, hi) = centered_digits(b);
    vanishing_eval_interval(w, lo, hi)
}

/// The centered-digit range check `g(w) == 0`: exact over prime rings for
/// the centered representative when `b < q` (same argument as
/// [`range_check`], with the zero set shifted).
///
/// # Panics
/// If the ring is not prime (unsound over `2^k`).
pub fn centered_range_check<R: CenteredRing>(w: &R, b: u64) -> bool {
    assert!(
        R::IS_PRIME,
        "the vanishing range check is exact only over prime rings"
    );
    centered_vanishing_eval(w, b) == R::ZERO
}

/// Like [`range_claim_table`] but for the **centered** `b`-digit set: a
/// table of `g_centered(t)` whose honest sum is zero exactly when every
/// entry lies in `[−⌊b/2⌋, ⌈b/2⌉ − 1]`.
///
/// # Panics
/// If the ring is not prime.
pub fn centered_range_claim_table<R>(table: &[R], b: u64) -> Vec<R>
where
    R: MatrixElement + Ring + Clone,
{
    assert!(
        R::IS_PRIME,
        "the vanishing range check is exact only over prime rings"
    );
    table
        .iter()
        .cloned()
        .map(|t| centered_vanishing_eval(&t, b))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    type Rq = Zq<8380417>;
    const Q: u64 = 8_380_417;

    fn w(v: i64) -> Rq {
        Rq::from(v.rem_euclid(Q as i64) as u64)
    }

    #[test]
    fn bit_check_is_exact_over_prime_ring() {
        assert!(bit_check(&w(0)));
        assert!(bit_check(&w(1)));
        // non-bits rejected, including representatives near the modulus
        for v in [2i64, 3, 17, 4_190_208, -1, -7] {
            assert!(!bit_check(&w(v)), "w = {v} must not pass the bit check");
        }
    }

    #[test]
    fn range_check_is_exact_over_prime_ring() {
        // [−3, 3] accepted
        for v in -3i64..=3 {
            assert!(range_check(&w(v), 3), "w = {v} in range must pass");
        }
        // just outside rejected on both sides
        for v in [-4i64, 4, 7, -100, 4_190_208] {
            assert!(!range_check(&w(v), 3), "w = {v} out of range must fail");
        }
    }

    #[test]
    fn vanishing_eval_matches_expanded_polynomial() {
        // cross-check against the expanded g_3 = X²(X²−1)(X²−4)(X²−9)
        let g = |x: &Rq| {
            let x2 = x.square();
            x2 * (x2 - Rq::from(1)) * (x2 - Rq::from(4)) * (x2 - Rq::from(9))
        };
        for v in [-5i64, -1, 0, 2, 11] {
            assert_eq!(vanishing_eval(&w(v), 3), g(&w(v)));
        }
    }

    #[test]
    fn range_claim_table_sums_to_zero_iff_all_in_range() {
        let good: Vec<Rq> = (0..16).map(|i| w((i % 7) as i64 - 3)).collect();
        let claim = range_claim_table(&good, 3);
        let sum = claim.iter().fold(Rq::zero(), |a, b| a + *b);
        assert_eq!(sum, Rq::ZERO, "all digits in range ⇒ vanishing sum 0");

        let mut bad = good.clone();
        bad[9] = w(4); // one digit out of range
        let claim = range_claim_table(&bad, 3);
        let sum = claim.iter().fold(Rq::zero(), |a, b| a + *b);
        assert_ne!(sum, Rq::ZERO, "a single out-of-range digit shows up");
    }

    #[test]
    fn bit_claim_rejects_non_prime_ring() {
        let result = std::panic::catch_unwind(|| {
            let two32 = Zq::<4294967296>::from(1u64);
            bit_check(&two32)
        });
        assert!(result.is_err(), "2-adic rings must refuse the check");
    }

    #[test]
    fn centered_digits_are_the_balanced_digit_set() {
        assert_eq!(centered_digits(16), (-8, 7));
        assert_eq!(centered_digits(3), (-1, 1));
        assert_eq!(centered_digits(2), (-1, 0));
        assert_eq!(centered_digits(1), (0, 0));
    }

    #[test]
    fn hachi_balanced_gate_is_our_centered_vanishing_polynomial() {
        // Hachi (2026/156, b = 16 centered digits): the published closed
        // form must agree with the interval product everywhere, which pins
        // its degree at 16 (the survey said 18).
        let closed = |w: &Rq| {
            let w2 = w.square();
            let mut acc = w2 + *w * Rq::from(8u64);
            for k in 1..=7u64 {
                acc *= w2 - Rq::from(k * k);
            }
            acc
        };
        for v in -40i64..=40 {
            assert_eq!(
                centered_vanishing_eval(&w(v), 16),
                closed(&w(v)),
                "c_bal and the interval product disagree at w = {v}"
            );
        }
    }

    #[test]
    fn centered_check_accepts_exactly_the_digit_set() {
        for t in -8i64..=7 {
            assert!(centered_range_check(&w(t), 16), "{t} is a digit");
        }
        for t in [-9i64, 8, 100, -1_000] {
            assert!(!centered_range_check(&w(t), 16), "{t} is not a digit");
        }
        // the symmetric gate cannot express this set: 8 must pass the
        // symmetric check and fail the centered one
        assert!(range_check(&w(8), 8));
        assert!(!centered_range_check(&w(8), 16));
    }

    #[test]
    fn centered_claim_table_sums_to_zero_iff_all_digits_in_range() {
        let good: Vec<Rq> = (0..16).map(|i| w((i as i64 % 16) - 8)).collect();
        let sum = centered_range_claim_table(&good, 16)
            .iter()
            .fold(Rq::zero(), |a, b| a + *b);
        assert_eq!(sum, Rq::ZERO);

        let mut bad = good.clone();
        bad[5] = w(8); // just outside the centered set
        let sum = centered_range_claim_table(&bad, 16)
            .iter()
            .fold(Rq::zero(), |a, b| a + *b);
        assert_ne!(sum, Rq::ZERO, "one off-center digit must show up");
    }

    #[test]
    fn interval_vanishing_rejects_an_interval_spanning_the_modulus() {
        // A polynomial vanishing on q or more points is the zero function
        // mod q and certifies nothing; the helper must refuse to build it.
        let r = std::panic::catch_unwind(|| vanishing_eval_interval(&w(3), 0, Q as i64));
        assert!(r.is_err(), "an interval of length q proves nothing");
    }
}
