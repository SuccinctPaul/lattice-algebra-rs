use crate::ring::number_theory::{is_prime_u64, primitive_root};
use crate::ring::reduction::ModularArithmetic;
use crate::ring::traits::{CenteredRing, Field, TwoAdicRing};
use crate::ring::Ring;
use core::fmt::*;
use core::iter::Sum;
use core::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};
use serde::{Deserialize, Serialize};

/// Z_q: Ring of integers mod q, for `2 <= q <= u64::MAX`.
///
/// Elements store the canonical representative in `[0, q)` as a `u64`, and
/// `+`/`-`/`*`/`inverse`/`centered` are correct over that whole range (the
/// boundary cases above `2^63` are covered by `ring::axiom_tests` and the
/// tests at the bottom of this file).
#[derive(Debug, Copy, Clone, PartialEq, Ord, PartialOrd, Eq, Serialize, Deserialize)]
pub struct Zq<const MODULUS: u64> {
    pub(crate) value: u64,
}

impl<const MODULUS: u64> Zq<MODULUS> {
    /// Largest representative, i.e. `MODULUS - 1`.
    pub const MAX: Self = Self { value: MODULUS - 1 };

    /// Creates a new Zq element from a raw value, ensures the value is within [0, MODULUS - 1].
    #[inline]
    pub fn new(value: u64) -> Self {
        Self {
            value: value % MODULUS,
        }
    }

    /// Returns the modular multiplicative inverse, if it exists.
    ///
    /// Extended Euclid with the Bézout coefficient carried reduced modulo `q`
    /// at every step. That keeps every intermediate inside `u128` across the
    /// whole documented domain `q <= u64::MAX`; the previous `i64` walk
    /// silently produced non-inverses above `2^63` and reported invertible
    /// elements as non-invertible near it.
    pub fn inverse(self) -> Option<Self> {
        let modulus = u128::from(MODULUS);
        let (mut r_prev, mut r) = (modulus, u128::from(self.value));
        let (mut t_prev, mut t) = (0u128, 1u128);

        while r != 0 {
            let quotient = r_prev / r;
            // `quotient * r <= r_prev`, so this never underflows.
            (r_prev, r) = (r, r_prev - quotient * r);
            // `quotient < q` and `t < q`, so the product fits `u128`.
            let t_new = (t_prev + modulus - (quotient * t) % modulus) % modulus;
            (t_prev, t) = (t, t_new);
        }

        (r_prev == 1).then_some(Self {
            value: t_prev as u64,
        })
    }

    /// Little-endian 8-byte encoding of the canonical representative.
    pub fn to_le_bytes(&self) -> [u8; 8] {
        self.value.to_le_bytes()
    }
    /// Rebuilds from a little-endian 8-byte encoding (reduced mod `q`).
    pub fn from_le_bytes(bytes: [u8; 8]) -> Self {
        Self::new(u64::from_le_bytes(bytes))
    }

    /// Big-endian 8-byte encoding of the canonical representative.
    pub fn to_be_bytes(&self) -> [u8; 8] {
        self.value.to_be_bytes()
    }
    /// Rebuilds from a big-endian 8-byte encoding (reduced mod `q`).
    pub fn from_be_bytes(bytes: [u8; 8]) -> Self {
        Self::new(u64::from_be_bytes(bytes))
    }
}

impl<const MODULUS: u64> Ring for Zq<MODULUS> {
    const MODULUS: u64 = MODULUS;
    const ZERO: Self = Self { value: 0 };
    const ONE: Self = Self { value: 1 };
    const IS_PRIME: bool = is_prime_u64(MODULUS);

    fn rand(rng: &mut impl rand::RngCore) -> Self {
        use crate::ring::sample::UniformZq;
        use rand::distr::uniform::UniformSampler;
        use rand::distr::Distribution;
        let sampler = UniformZq::new(Self::ZERO, Self::MAX).unwrap();
        Distribution::sample(&sampler, rng)
    }
    fn square(&self) -> Self {
        *self * *self
    }
    fn pow(&self, mut power: u64) -> Self {
        let mut result = Self::ONE;
        let mut base = *self;
        while power > 0 {
            if power & 1 == 1 {
                result *= base;
            }
            base *= base;
            power >>= 1;
        }
        result
    }
    fn to_u128(&self) -> u128 {
        u128::from(self.value)
    }
}

impl<const MODULUS: u64> Field for Zq<MODULUS> {
    fn inverse(&self) -> Option<Self> {
        Zq::<MODULUS>::inverse(*self)
    }
}

impl<const MODULUS: u64> TwoAdicRing for Zq<MODULUS> {
    const TWO_ADICITY: u32 = (MODULUS - 1).trailing_zeros();

    fn two_adic_generator(bits: usize) -> Self {
        assert!(
            bits as u32 <= Self::TWO_ADICITY,
            "requested order 2^{} exceeds the 2-adicity ({}) of q = {}",
            bits,
            Self::TWO_ADICITY,
            MODULUS
        );
        if bits == 0 {
            return Self::ONE;
        }
        assert!(
            Self::IS_PRIME,
            "two_adic_generator requires a prime modulus, got q = {MODULUS}"
        );
        // g is a generator of Z_q*, so g^((q-1)/2^bits) has order exactly 2^bits.
        let g = primitive_root::<Self>();
        g.pow((MODULUS - 1) >> bits)
    }
}

impl<const MODULUS: u64> CenteredRing for Zq<MODULUS> {
    /// Centered representative in `(-q/2, q/2]`, branch-free.
    ///
    /// For even `q` the half-open interval keeps `+q/2`; for odd `q` this is
    /// exactly the symmetric range `[-(q-1)/2, (q-1)/2]` used by FIPS 204.
    fn centered(&self) -> i64 {
        // u128 throughout: casting `value` or `MODULUS` to `i64` wraps for
        // `q > 2^63`. The magnitude is at most `q / 2 <= u64::MAX / 2
        // == i64::MAX`, so the final narrowing is exact over the whole
        // documented domain.
        let (v, q) = (u128::from(self.value), u128::from(MODULUS));
        let (plain, wrapped) = (v as i128, v.wrapping_sub(q) as i128);
        let mask = (i128::from(2 * v > q)).wrapping_neg();
        ((wrapped & mask) | (plain & !mask)) as i64
    }

    /// `|self|_inf = min(a, q - a)`, branch-free.
    fn abs_infinity(&self) -> u64 {
        let (a, b) = (self.value, MODULUS - self.value);
        crate::crypto::ct::select_u64(a < b, a, b)
    }
}

impl<const MODULUS: u64> Sum for Zq<MODULUS> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, Self::add)
    }
}

impl<const MODULUS: u64> From<u64> for Zq<MODULUS> {
    fn from(value: u64) -> Self {
        Self::new(value)
    }
}

/// Macro for arithmetic ops (+, -, *, +=, -=, *=)
macro_rules! impl_arithmetic {
    // Binary op and assign op for value and reference
    ($trait:ident, $assign_trait:ident, $method:ident, $assign_method:ident, $op:ident) => {
        impl<const MODULUS: u64> $trait for Zq<MODULUS> {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: Self) -> Self::Output {
                Self::new(<Self as ModularArithmetic<MODULUS>>::$op(
                    self.value, rhs.value,
                ))
            }
        }
        impl<const MODULUS: u64> $assign_trait for Zq<MODULUS> {
            #[inline]
            fn $assign_method(&mut self, rhs: Self) {
                self.value = <Self as ModularArithmetic<MODULUS>>::$op(self.value, rhs.value);
            }
        }
        impl<'a, const MODULUS: u64> $trait<&'a Self> for Zq<MODULUS> {
            type Output = Self;
            #[inline]
            fn $method(self, rhs: &'a Self) -> Self::Output {
                Self::new(<Self as ModularArithmetic<MODULUS>>::$op(
                    self.value, rhs.value,
                ))
            }
        }
        impl<'a, const MODULUS: u64> $assign_trait<&'a Self> for Zq<MODULUS> {
            #[inline]
            fn $assign_method(&mut self, rhs: &'a Self) {
                self.value = <Self as ModularArithmetic<MODULUS>>::$op(self.value, rhs.value);
            }
        }
    };
}

// Usage for Add, Mul, Sub
impl_arithmetic!(Add, AddAssign, add, add_assign, mod_add);
impl_arithmetic!(Mul, MulAssign, mul, mul_assign, mod_mul);
impl_arithmetic!(Sub, SubAssign, sub, sub_assign, mod_sub);

impl<const MODULUS: u64> Neg for Zq<MODULUS> {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self::Output {
        // Branch-free: `(MODULUS - v) % MODULUS` is 0 for v = 0 and
        // MODULUS - v otherwise.
        Self::new(MODULUS - self.value)
    }
}

impl<const MODULUS: u64> Div for Zq<MODULUS> {
    type Output = Self;
    #[inline]
    fn div(self, rhs: Self) -> Self::Output {
        if rhs.value == 0 {
            panic!("Division by zero");
        }
        let inv = rhs.inverse().expect("Divisor has no modular inverse");
        self * inv
    }
}

impl<const MODULUS: u64> Display for Zq<MODULUS> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "{}", self.value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::{format, string::String};
    use serde_json;
    type Zq17 = Zq<17>;

    #[test]
    fn test_new_and_from() {
        assert_eq!(Zq17::ZERO, Zq17::new(0));
        assert_eq!(Zq17::ZERO, Zq17::new(17));
        assert_eq!(Zq17::from(34), Zq17::ZERO);
        assert_eq!(Zq17::from(1), Zq17::ONE);
        assert_eq!(Zq17::from(18), Zq17::ONE);
        assert_eq!(Zq17::from(16), Zq17::new(16));
    }

    #[test]
    fn test_display_and_debug() {
        let a = Zq17::new(7);
        assert_eq!(format!("{a}",), "7");
        assert!(format!("{a}").contains("7"));
        let mut s = String::new();
        write!(&mut s, "{a}").unwrap();
        assert_eq!(s, "7");
    }

    #[test]
    fn test_add_and_add_assign() {
        let mut a = Zq17::new(5);
        let b = Zq17::new(13);
        assert_eq!(a + b, Zq17::new(1));
        a += b;
        assert_eq!(a, Zq17::new(1));
        let mut c = Zq17::new(16);
        c += Zq17::new(2);
        assert_eq!(c, Zq17::new(1));
        // Reference RHS
        let mut d = Zq17::new(3);
        let e = Zq17::new(4);
        d.add_assign(&e);
        assert_eq!(d, Zq17::new(7));
        assert_eq!(Zq17::new(2) + Zq17::new(3), Zq17::new(5));
    }

    #[test]
    fn test_sub_and_sub_assign() {
        let mut a = Zq17::new(3);
        let b = Zq17::new(5);
        assert_eq!(a - b, Zq17::new(15));
        a -= b;
        assert_eq!(a, Zq17::new(15));
        // Reference RHS
        let mut c = Zq17::new(2);
        let d = Zq17::new(4);
        c.sub_assign(&d);
        assert_eq!(c, Zq17::new(15));
        assert_eq!(Zq17::new(2) - Zq17::new(4), Zq17::new(15));
    }

    #[test]
    fn test_mul_and_mul_assign() {
        let mut a = Zq17::new(6);
        let b = Zq17::new(3);
        assert_eq!(a * b, Zq17::new(1));
        a *= b;
        assert_eq!(a, Zq17::new(1));
        // Reference RHS
        let mut c = Zq17::new(5);
        let d = Zq17::new(4);
        c.mul_assign(&d);
        assert_eq!(c, Zq17::new(3));
        assert_eq!(Zq17::new(5) * Zq17::new(4), Zq17::new(3));
    }

    #[test]
    fn test_neg() {
        assert_eq!(-Zq17::new(0), Zq17::new(0));
        assert_eq!(-Zq17::new(5), Zq17::new(12));
        assert_eq!(-Zq17::new(16), Zq17::new(1));
    }

    #[test]
    fn test_div_and_inverse() {
        let a = Zq17::new(8);
        let b = Zq17::new(2);
        assert_eq!(a / b, Zq17::new(4));
        assert_eq!(Zq17::new(1) / Zq17::new(2), Zq17::new(9)); // 2*9=18≡1 mod 17
        assert_eq!(Zq17::new(5).inverse(), Some(Zq17::new(7))); // 5*7=35≡1 mod 17
        assert_eq!(Zq17::new(0).inverse(), None);
    }

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn test_div_by_zero_panics() {
        let _ = Zq17::new(5) / Zq17::new(0);
    }

    // Regression tests for the documented domain `2 <= q <= u64::MAX`. Above
    // 2^63 the previous `i64`-based inverse saw a negative modulus and `+`
    // lost the 2^64 carry; both are asserted here and in `reduction::barrett`.

    type ZqBig = Zq<18446744073709551557>; // u64::MAX - 58, prime, > 2^63
    type ZqBelow63 = Zq<9223372036854775783>; // largest prime below 2^63
    const _: () = assert!(ZqBig::IS_PRIME, "test fixture must be prime");
    const _: () = assert!(ZqBelow63::IS_PRIME, "test fixture must be prime");
    // Root cause of the old failure, pinned: the domain reaches past
    // `i64::MAX`, so the previous `MODULUS as i64` cast started the extended
    // Euclid walk from a negative modulus.
    const _: () = assert!((ZqBig::MODULUS as i64) < 0);

    #[test]
    fn inverse_above_2_63_is_a_real_inverse() {
        for v in [1u64, 2, 3, 12345, ZqBig::MODULUS - 1] {
            let a = ZqBig::new(v);
            let inv = a
                .inverse()
                .unwrap_or_else(|| panic!("{v} is invertible mod a prime modulus"));
            assert_eq!(a * inv, ZqBig::ONE, "a * a^-1 != 1 for a = {v}");
        }
        // Exact values, so a silently-wrong inverse cannot slip past the
        // self-consistency check above.
        assert_eq!(
            ZqBig::new(3).inverse().map(|i| i.to_u128()),
            Some(6148914691236517186)
        );
        assert_eq!(
            ZqBig::new(12345).inverse().map(|i| i.to_u128()),
            Some(6398457523177343035)
        );
    }

    #[test]
    fn inverse_just_below_2_63_is_unchanged() {
        for v in [1u64, 3, 7, 123456789, ZqBelow63::MODULUS - 1] {
            let a = ZqBelow63::new(v);
            let inv = a
                .inverse()
                .unwrap_or_else(|| panic!("{v} is invertible mod a prime modulus"));
            assert_eq!(a * inv, ZqBelow63::ONE);
        }
        assert_eq!(
            ZqBelow63::new(3).inverse().map(|i| i.to_u128()),
            Some(6148914691236517189)
        );
    }

    #[test]
    fn inverse_matches_gcd_on_a_composite_modulus() {
        type ZqC = Zq<4294967296>; // 2^32, the LaBRADOR instance
        assert_eq!(ZqC::new(0).inverse(), None);
        assert!(
            ZqC::new(2).inverse().is_none(),
            "even residues are not invertible mod 2^32"
        );
        let odd = ZqC::new(3);
        assert_eq!(odd * odd.inverse().unwrap(), ZqC::ONE);
    }

    #[test]
    fn division_recovers_the_multiplier_at_the_top_of_the_domain() {
        let a = ZqBig::new(987654321);
        let b = ZqBig::new(123456789);
        assert_eq!((a * b) / b, a);
    }

    #[test]
    fn centered_is_exact_above_2_63() {
        type ZqG = Zq<18446744069414584321>; // Goldilocks: 2^64 - 2^32 + 1
        let q = ZqG::MODULUS;
        assert_eq!(ZqG::MAX.centered(), -1); // q - 1 centers to -1
        assert_eq!(ZqG::new(1).centered(), 1);
        assert_eq!(
            ZqG::new(q.div_ceil(2)).centered(),
            -(((q - 1) / 2) as i64),
            "the first value past q/2 must wrap to the negative side"
        );
        for v in [0u64, 1, 2, q / 2, q / 2 + 1, q - q / 4, q - 1] {
            let a = ZqG::new(v);
            let c = a.centered();
            let (c128, q128) = (i128::from(c), i128::from(q));
            assert_eq!(
                c128.rem_euclid(q128),
                i128::from(v),
                "centered(a) != a mod q"
            );
            assert!(
                2 * c128 > -q128 && 2 * c128 <= q128,
                "centered {c} outside (-q/2, q/2] for q = {q}"
            );
            assert_eq!(c.unsigned_abs(), a.abs_infinity());
        }
    }

    #[test]
    fn test_pow_and_square() {
        assert_eq!(Zq17::new(2).pow(3), Zq17::new(8));
        assert_eq!(Zq17::new(3).pow(4), Zq17::new(13));
        assert_eq!(Zq17::new(3).pow(16), Zq17::ONE);
        assert_eq!(Zq17::new(0).pow(0), Zq17::ONE);
        assert_eq!(Zq17::new(0).pow(5), Zq17::ZERO);
        assert_eq!(Zq17::new(5).square(), Zq17::new(8));
    }

    #[test]
    fn test_centered_and_infinity_norm() {
        // Odd q: symmetric range [-8, 8] for q = 17.
        assert_eq!(Zq17::new(0).centered(), 0);
        assert_eq!(Zq17::new(8).centered(), 8);
        assert_eq!(Zq17::new(9).centered(), -8);
        assert_eq!(Zq17::new(16).centered(), -1);
        // abs_infinity = min(a, q - a)
        assert_eq!(Zq17::new(0).abs_infinity(), 0);
        assert_eq!(Zq17::new(5).abs_infinity(), 5);
        assert_eq!(Zq17::new(12).abs_infinity(), 5);
        assert_eq!(Zq17::new(16).abs_infinity(), 1);
        // centered and abs_infinity agree in magnitude
        for i in 0..17u64 {
            let a = Zq17::new(i);
            assert_eq!(a.centered().unsigned_abs(), a.abs_infinity());
            assert!(a.leq_infinity(8));
            assert!(!a.leq_infinity(7) || a.abs_infinity() <= 7);
        }
        assert!(Zq17::new(5).leq_infinity(5));
        assert!(!Zq17::new(5).leq_infinity(4));

        // Even q = 8: interval is (-4, 4]
        type Zq8 = Zq<8>;
        assert_eq!(Zq8::new(4).centered(), 4);
        assert_eq!(Zq8::new(5).centered(), -3);
        assert_eq!(Zq8::new(0).centered(), 0);
    }

    #[test]
    fn test_random_and_rand() {
        let mut rng = rand::rng();
        let a = Zq17::rand(&mut rng);
        let b = Zq17::rand(&mut rng);
        assert!(a.value < 17);
        assert!(b.value < 17);
    }

    #[test]
    fn test_serde_roundtrip() {
        let mut rng = rand::rng();
        let lhs = Zq17::rand(&mut rng);
        let serde = serde_json::to_string(&lhs).unwrap();
        let rhs = serde_json::from_str::<Zq17>(&serde).unwrap();
        assert_eq!(lhs, rhs);
    }

    #[test]
    fn test_additive_inverse_property() {
        for i in 0..17 {
            let a = Zq17::new(i);
            assert_eq!(a + (-a), Zq17::ZERO);
        }
    }

    #[test]
    fn test_multiplicative_inverse_property() {
        for i in 1..17 {
            let a = Zq17::new(i);
            assert_eq!(a * a.inverse().unwrap(), Zq17::ONE);
        }
    }

    #[test]
    fn test_ring_axioms() {
        let a = Zq17::new(5);
        let b = Zq17::new(7);
        let c = Zq17::new(11);
        // Associativity
        assert_eq!((a + b) + c, a + (b + c));
        assert_eq!((a * b) * c, a * (b * c));
        // Commutativity
        assert_eq!(a + b, b + a);
        assert_eq!(a * b, b * a);
        // Distributivity
        assert_eq!(a * (b + c), (a * b) + (a * c));
    }

    #[test]
    fn test_edge_cases() {
        // MODULUS - 1
        let a = Zq17::new(16);
        let b = Zq17::new(1);
        assert_eq!(a + b, Zq17::ZERO);
        assert_eq!(a - b, Zq17::new(15));
        assert_eq!(a * b, a);
        assert_eq!(a * Zq17::ZERO, Zq17::ZERO);
        assert_eq!(Zq17::ZERO - a, Zq17::new(1));
    }

    #[test]
    fn test_serialization() {
        let z = Zq17::new(5);

        // Test serialization
        let serialized = serde_json::to_string(&z).unwrap();
        let deserialized: Zq17 = serde_json::from_str(&serialized).unwrap();

        assert_eq!(z, deserialized);
    }

    #[test]
    fn test_serialization_zero() {
        let z = Zq17::ZERO;

        let serialized = serde_json::to_string(&z).unwrap();
        let deserialized: Zq17 = serde_json::from_str(&serialized).unwrap();

        assert_eq!(z, deserialized);
    }

    #[test]
    fn test_serialization_max() {
        let z = Zq17::MAX;

        let serialized = serde_json::to_string(&z).unwrap();
        let deserialized: Zq17 = serde_json::from_str(&serialized).unwrap();

        assert_eq!(z, deserialized);
    }
}
