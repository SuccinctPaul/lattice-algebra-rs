use crate::poly::UniPolynomial;
use std::fmt::{Debug, Display};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

/// Ring mod q
pub trait Ring:
    Add<Output = Self>
    + AddAssign
    + Mul<Output = Self>
    + MulAssign
    + Neg<Output = Self>
    + Sub<Output = Self>
    + SubAssign
    + Div<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> MulAssign<&'a Self>
    + Sized
    + Clone
    + Copy
    + Debug
    + PartialEq
    + Eq
    + Ord
    + PartialOrd
    + From<u64>
    + Send
    + Sync
    + Display
    + MatrixElement
{
    /// Modulus q
    const MODULUS: u64;
    /// Zero element (additive identity)
    const ZERO: Self;
    /// Multiplicative identity
    const ONE: Self;
    /// Max element, which equals `MODULUS - 1`
    const MAX: Self;

    fn rand(rng: &mut impl rand::RngCore) -> Self;
    /// Compute square of element.
    fn square(&self) -> Self;
    /// Computes self^exponent using exponentiation by squaring
    fn pow(&self, power: u64) -> Self;
    /// output the abs value,
    fn abs(&self) -> u64;

    /// As the MODULUS is limited in u64, so we can convert Ring to u128
    fn to_u128(&self) -> u128;
}

/// Polynomial Quotient Ring
/// eg: Z_q[x]/(x^d+1)
pub trait PolynomialQuotientRing:
    Add<Output = Self>
    + AddAssign
    + for<'a> Add<&'a Self, Output = Self>
    + Mul<Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + MulAssign
    + Sub<Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + SubAssign
    + Sized
    + Clone
    + Debug
    + PartialEq
    + Eq
    + Display
{
    type PolyCoeff: Ring;

    fn modulus() -> UniPolynomial<Self::PolyCoeff>;
    /// Remove leading zero coefficients
    fn normalize(&mut self);

    fn rand(rng: &mut impl rand::RngCore, degree: usize) -> Self;

    // generate a random PolyRing with default degree 'n', aka the bound degree.
    // TODO: Does it need to export the BOUND_DGREE in trait?
    fn rand_with_bound_degree(rng: &mut impl rand::RngCore) -> Self;

    /// Get the degree of the polynomial
    fn degree(&self) -> usize;

    /// Set the coefficient of the x^i term
    fn set_coefficient(&mut self, i: usize, value: Self::PolyCoeff);

    /// Evaluate the polynomial at a given point
    fn evaluate(&self, x: &Self::PolyCoeff) -> Self::PolyCoeff;

    /// Create a polynomial from a list of coefficients
    fn from_coefficients(coeffs: Vec<Self::PolyCoeff>) -> Self;

    /// Get all coefficients of the polynomial
    fn coefficients(&self) -> Vec<Self::PolyCoeff>;

    /// Check if the polynomial is zero
    fn is_zero(&self) -> bool;
}

/// Trait for types that can be used as matrix elements
pub trait MatrixElement:
    Clone
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + PartialEq
    + Eq
    + Display
    + Debug
    + Sum<Self>
{
    /// Returns the zero element
    fn zero() -> Self;
    /// Returns the one element
    fn one() -> Self;
    /// Returns a random element
    fn random(rng: &mut impl rand::RngCore) -> Self;
}
/// Implement MatrixElement for Ring
impl<R: Ring> MatrixElement for R {
    fn zero() -> Self {
        Self::ZERO
    }

    fn one() -> Self {
        Self::ONE
    }

    fn random(rng: &mut impl rand::RngCore) -> Self {
        Self::rand(rng)
    }
}
