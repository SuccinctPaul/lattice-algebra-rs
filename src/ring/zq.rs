use crate::ring::Ring;
use crate::ring::reduction::ModularArithmetic;
use rand::RngCore;
use serde::{Deserialize, Serialize};
use std::fmt::*;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};
use std::random::{Random, RandomSource};

/// Z_q: Ring of integers mod q, where q <= 2^64.
#[derive(Debug, Copy, Clone, PartialEq, Ord, PartialOrd, Eq, Serialize, Deserialize)]
pub struct Zq<const MODULUS: u64> {
    pub(crate) value: u64,
}

impl<const MODULUS: u64> Zq<MODULUS> {
    /// Creates a new Zq element from a raw value, ensures the value is within [0, MODULUS - 1].
    #[inline]
    pub fn new(value: u64) -> Self {
        Self {
            value: value % MODULUS,
        }
    }

    /// Returns the modular multiplicative inverse, if it exists.
    pub fn inverse(self) -> Option<Self> {
        let (mut t, mut newt) = (0i64, 1i64);
        let (mut r, mut newr) = (MODULUS as i64, self.value as i64);

        while newr != 0 {
            let quotient = r / newr;
            (t, newt) = (newt, t - quotient * newt);
            (r, newr) = (newr, r - quotient * newr);
        }

        if r > 1 {
            None
        } else {
            let inv = ((t + MODULUS as i64) % MODULUS as i64) as u64;
            Some(Self::new(inv))
        }
    }

    pub fn to_le_bytes(&self) -> [u8; 8] {
        self.value.to_le_bytes()
    }
    pub fn from_le_bytes(bytes: [u8; 8]) -> Self {
        Self::new(u64::from_le_bytes(bytes))
    }

    pub fn to_be_bytes(&self) -> [u8; 8] {
        self.value.to_be_bytes()
    }
    pub fn from_be_bytes(bytes: [u8; 8]) -> Self {
        Self::new(u64::from_be_bytes(bytes))
    }
}

impl<const MODULUS: u64> Ring for Zq<MODULUS> {
    const MODULUS: u64 = MODULUS;
    const ZERO: Self = Self { value: 0 };
    const ONE: Self = Self { value: 1 };
    const MAX: Self = Self { value: MODULUS - 1 };

    fn rand(rng: &mut impl rand::RngCore) -> Self {
        Self::new(rng.next_u64())
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
    fn abs(&self) -> u64 {
        self.value
    }
    fn to_u128(&self) -> u128 {
        u128::from(self.value)
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
        if self.value == 0 {
            self
        } else {
            Self::new(MODULUS - self.value)
        }
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
        assert_eq!(format!("{}", a), "7");
        assert!(format!("{:?}", a).contains("7"));
        let mut s = String::new();
        write!(&mut s, "{}", a).unwrap();
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
        assert_eq!(Zq17::new(2) + &Zq17::new(3), Zq17::new(5));
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
        assert_eq!(Zq17::new(2) - &Zq17::new(4), Zq17::new(15));
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
        assert_eq!(Zq17::new(5) * &Zq17::new(4), Zq17::new(3));
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
    fn test_abs() {
        assert_eq!(Zq17::new(0).abs(), 0);
        assert_eq!(Zq17::new(5).abs(), 5);
        assert_eq!(Zq17::new(16).abs(), 16);
    }

    #[test]
    fn test_random_and_rand() {
        let mut rng = rand::thread_rng();
        let a = Zq17::rand(&mut rng);
        let b = Zq17::rand(&mut rng);
        assert!(a.value < 17);
        assert!(b.value < 17);
        assert_ne!(a, b); // Very unlikely to fail
        let mut src = std::random::DefaultRandomSource::default();
        let c = Zq17::random(&mut src);
        assert!(c.value < 17);
    }

    #[test]
    fn test_serde_roundtrip() {
        let mut rng = rand::thread_rng();
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
}
