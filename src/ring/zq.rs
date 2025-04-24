use crate::ring::Ring;
use rand::RngCore;
use serde::{Deserialize, Serialize};
use std::fmt::*;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};
use std::random::{Random, RandomSource};

/// Z_q: Ring of integers mod q, where q <= 2^64.
#[derive(Debug, Copy, Clone, PartialEq, Ord, PartialOrd, Eq, Serialize, Deserialize)]
pub struct Zq<const MODULUS: u64> {
    value: u64,
}

impl<const MODULUS: u64> Zq<MODULUS> {
    /// Creates a new Zq element from a raw value, which ensure the value within the [0, MODULUS - 1].
    pub fn new(value: u64) -> Self {
        Self {
            value: value % Self::MODULUS,
        }
    }
    /// Helper function to calculate modular multiplicative inverse
    /// The Extended Euclidean Algorithm to find the modular multiplicative inverse of a modulo m.
    fn inverse(a: i64, m: i64) -> Option<u64> {
        let mut t = 0i64;
        let mut newt = 1i64;
        let mut r = m;
        let mut newr = a;

        while newr != 0 {
            let quotient = r / newr;
            (t, newt) = (newt, t - quotient * newt);
            (r, newr) = (newr, r - quotient * newr);
        }

        if r > 1 {
            None // a is not invertible
        } else {
            Some(((t + m as i64) % m as i64) as u64)
        }
    }
}

impl<const MODULUS: u64> Ring for Zq<MODULUS> {
    const MODULUS: u64 = MODULUS;
    fn rand(rng: &mut impl RngCore) -> Self {
        Self::new(rng.next_u64())
    }
    fn zero() -> Self {
        Self::new(0)
    }
    fn one() -> Self {
        Self::new(1)
    }
    fn square(&self) -> Self {
        let squared_value = (self.value as u128 * self.value as u128) % Self::MODULUS as u128;
        Self::new(squared_value as u64)
    }
    fn pow(&self, power: u64) -> Self {
        let mut base = self.clone();
        let mut result = Self::one();
        let mut exponent = power;

        while exponent > 0 {
            let local_base = base.clone();
            if exponent & 1 == 1 {
                result *= &local_base;
            }
            base = local_base.square();
            exponent >>= 1;
        }

        result
    }

    /// output the abs value, in Fq, equal to the value.
    fn abs(&self) -> u64 {
        self.value
    }
}

impl<const MODULUS: u64> Random for Zq<MODULUS> {
    fn random(source: &mut (impl RandomSource + ?Sized)) -> Self {
        Self::new(u64::random(source))
    }
}
impl<const MODULUS: u64> From<u64> for Zq<MODULUS> {
    fn from(value: u64) -> Self {
        Self::new(value)
    }
}

// Macro to generate arithmetic trait implementations
macro_rules! impl_arithmetic {
    ($trait:ident, $assign_trait:ident, $method:ident, $assign_method:ident, $op:ident) => {
        impl<const MODULUS: u64> $trait for Zq<MODULUS> {
            type Output = Self;

            fn $method(self, rhs: Self) -> Self::Output {
                Self::new(self.value.$op(rhs.value))
            }
        }

        impl<const MODULUS: u64> $assign_trait for Zq<MODULUS> {
            fn $assign_method(&mut self, rhs: Self) {
                self.value = self.value.$op(rhs.value) % Self::MODULUS;
            }
        }
    };
}

impl_arithmetic!(Add, AddAssign, add, add_assign, wrapping_add);

// impl_arithmetic!(Sub, SubAssign, sub, sub_assign, wrapping_sub);
// TODO:
//  - Implement Barrett reduction algorithm
//      https://www.nayuki.io/page/barrett-reduction-algorithm
//  - Implement Montgomery reduction algorithm
impl_arithmetic!(Mul, MulAssign, mul, mul_assign, wrapping_mul);

impl<const MODULUS: u64> Neg for Zq<MODULUS> {
    type Output = Self;

    fn neg(self) -> Self::Output {
        let value = if self.value == 0 {
            0
        } else {
            Self::MODULUS - self.value
        };
        Self { value }
    }
}
impl<const MODULUS: u64> Sub for Zq<MODULUS> {
    type Output = Self;

    // a−b mod q=(a+(q−b))mod q
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.value + Self::MODULUS - rhs.value)
    }
}

impl<const MODULUS: u64> SubAssign for Zq<MODULUS> {
    fn sub_assign(&mut self, rhs: Self) {
        self.value = (self.value + Self::MODULUS - rhs.value) % Self::MODULUS;
    }
}

impl<const MODULUS: u64> Div for Zq<MODULUS> {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        if rhs.value == 0 {
            panic!("Division by zero");
        }

        let inv = Self::inverse(rhs.value as i64, Self::MODULUS as i64)
            .expect("Divisor has no modular inverse");
        Self::new(self.value * inv)
    }
}

impl<'a, const MODULUS: u64> Add<&'a Self> for Zq<MODULUS> {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self::Output {
        Self::new(self.value + rhs.value)
    }
}

impl<'a, const MODULUS: u64> AddAssign<&'a Self> for Zq<MODULUS> {
    fn add_assign(&mut self, rhs: &'a Self) {
        self.value = (self.value + rhs.value) % Self::MODULUS;
    }
}

impl<'a, const MODULUS: u64> Mul<&'a Self> for Zq<MODULUS> {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self::Output {
        Self::new(self.value * rhs.value)
    }
}

impl<'a, const MODULUS: u64> MulAssign<&'a Self> for Zq<MODULUS> {
    fn mul_assign(&mut self, rhs: &'a Self) {
        self.value = (self.value * rhs.value) % Self::MODULUS;
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
    use std::random::DefaultRandomSource;
    type Zq17 = Zq<17>;

    #[test]
    fn test_new_Zq() {
        assert_eq!(Zq17::zero(), Zq17::new(Zq17::MODULUS));
        assert_eq!(Zq17::one(), Zq17::new(1));
    }

    #[test]
    fn test_Zq_to_string_and_display() {
        let mut rng = DefaultRandomSource::default();
        let lhs = Zq17::random(&mut rng);
        let str = lhs.to_string();
        println!("{:?}", lhs);
        println!("{}", lhs);
        println!("to_string: {:?}", str);
    }

    #[test]
    fn test_rand_Zq() {
        let mut rng = rand::thread_rng();
        let lhs = Zq17::rand(&mut rng);
        let rhs = Zq17::rand(&mut rng);
        assert_ne!(lhs, rhs);
    }

    #[test]
    fn test_Zq_addition() {
        assert_eq!(Zq17::new(8), Zq17::new(5) + Zq17::new(3)); // 13 mod 17 = 13
        assert_eq!(Zq17::new(15), Zq17::new(7) + Zq17::new(8)); // 15 mod 17 = 15
        assert_eq!(Zq17::new(1), Zq17::new(9) + Zq17::new(9)); // 18 mod 17 = 1
    }

    #[test]
    fn test_Zq_add_assign() {
        let mut a = Zq17::new(5);
        let b = Zq17::new(3);
        a += b;
        assert_eq!(a, Zq17::new(8));

        let mut c = Zq17::new(15);
        let d = Zq17::new(5);
        c += d;
        assert_eq!(c, Zq17::new(3)); // (15 + 5) % 17 = 3
    }

    #[test]
    fn test_Zq_mul_assign() {
        let mut a = Zq17::new(5);
        let b = Zq17::new(3);
        a *= b;
        assert_eq!(a, Zq17::new(15));

        let mut c = Zq17::new(15);
        let d = Zq17::new(5);
        c *= d;
        assert_eq!(c, Zq17::new(75)); // (15 + 5) % 17 = 3
    }

    #[test]
    fn test_Zq_subtraction() {
        let a = Zq17::new(5);
        let b = Zq17::new(3);
        assert_eq!(Zq17::new(2), a - b);
        assert_eq!(Zq17::new(16), Zq17::new(3) - Zq17::new(4)); // -1 mod 17 = 16
        assert_eq!(Zq17::new(0), Zq17::new(7) - Zq17::new(7));
    }

    #[test]
    fn test_Zq_multiplication() {
        let a = Zq17::new(5);
        let b = Zq17::new(3);
        assert_eq!(Zq17::new(15), a * b);
        assert_eq!(Zq17::new(1), Zq17::new(6) * Zq17::new(3)); // 18 mod 17 = 1
        assert_eq!(Zq17::new(0), Zq17::new(17) * Zq17::new(5)); // 85 mod 17 = 0
    }

    #[test]
    fn test_Zq_division() {
        let a = Zq17::new(8);
        let b = Zq17::new(2);
        assert_eq!(Zq17::new(4), a / b);
        assert_eq!(Zq17::new(1), Zq17::new(5) / Zq17::new(5));
        assert_eq!(Zq17::new(9), Zq17::new(1) / Zq17::new(2)); // 1 * 9 = 18 ≡ 1 (mod 17)
    }

    #[test]
    #[should_panic(expected = "Division by zero")]
    fn test_Zq_division_by_zero() {
        let a = Zq17::new(5);
        let b = Zq17::new(0);
        let _ = a / b;
    }

    #[test]
    fn test_Zq_negation() {
        assert_eq!(Zq17::new(0), -Zq17::new(0));
        assert_eq!(Zq17::new(12), -Zq17::new(5)); // -5 mod 17 = 12
        assert_eq!(Zq17::new(1), -Zq17::new(16));
    }

    #[test]
    fn test_Zq_additive_inverse() {
        for i in 0..17 {
            let a = Zq17::new(i);
            assert_eq!(Zq17::new(0), a + (-a));
        }
    }

    #[test]
    fn test_Zq_multiplicative_inverse() {
        for i in 1..17 {
            let a = Zq17::new(i);
            assert_eq!(Zq17::new(1), a * (Zq17::new(1) / a));
        }
    }

    #[test]
    fn test_Zq_associativity() {
        let a = Zq17::new(5);
        let b = Zq17::new(7);
        let c = Zq17::new(11);
        assert_eq!((a + b) + c, a + (b + c));
        assert_eq!((a * b) * c, a * (b * c));
    }

    #[test]
    fn test_Zq_commutativity() {
        let a = Zq17::new(5);
        let b = Zq17::new(7);
        assert_eq!(a + b, b + a);
        assert_eq!(a * b, b * a);
    }

    #[test]
    fn test_Zq_distributivity() {
        let a = Zq17::new(5);
        let b = Zq17::new(7);
        let c = Zq17::new(11);
        assert_eq!(a * (b + c), (a * b) + (a * c));
    }

    #[test]
    fn test_Zq_serde_and_deserde() {
        let mut rng = rand::thread_rng();
        let lhs = Zq17::rand(&mut rng);
        let serde = serde_json::to_string(&lhs).unwrap();
        let rhs = serde_json::from_str::<Zq17>(&serde).unwrap();
        assert_eq!(lhs, rhs);
    }
    #[test]
    fn test_Zq_pow() {
        // Test x^0 = 1 for any x
        assert_eq!(Zq17::new(5).pow(0), Zq17::one());
        assert_eq!(Zq17::new(0).pow(0), Zq17::one());

        // Test x^1 = x for any x
        assert_eq!(Zq17::new(7).pow(1), Zq17::new(7));

        // Test 0^x = 0 for x > 0
        assert_eq!(Zq17::new(0).pow(5), Zq17::zero());

        // Test some specific cases
        assert_eq!(Zq17::new(2).pow(3), Zq17::new(8)); // 2^3 = 8
        assert_eq!(Zq17::new(3).pow(4), Zq17::new(81)); // 3^4 = 81

        // Test a larger exponent
        assert_eq!(Zq17::new(2).pow(10), Zq17::new(1024)); // 2^10 = 1024

        // Test with modulus (assuming MODULUS = 17)
        assert_eq!(Zq17::new(3).pow(16), Zq17::one()); // 3^16 ≡ 1 (mod 17) by Fermat's Little Theorem
    }
}
