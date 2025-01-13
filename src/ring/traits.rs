use crate::poly::Polynomial;
use std::fmt::{Debug, Display};
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};
use std::random::Random;

/// Ring of integers mod q
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
+ Sized
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
+ Random
+ From<u64>
+ Send
+ Sync
// + ToString
+ Display
{
    const MODULUS: u64;

    fn rand(rng: &mut impl rand::RngCore) -> Self;
    fn zero() -> Self;
    fn one() -> Self;
    fn square(&self) -> Self;
    /// Computes self^exponent using exponentiation by squaring
    fn pow(&self, power: u64) -> Self;

    // output the abs value, in Fq, equal to the value.
    fn abs(&self) -> u64;
}

/// Polynomial Ring
/// eg: Z_q[x]/(x^n+1)
pub trait PolynomialRingTrait:
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
    type PolyType: Polynomial;
    type PolyCoeff: Ring;

    fn modulus() -> Self::PolyType;
    /// Remove leading zero coefficients
    fn normalize(&mut self);

    fn rand(rng: &mut impl rand::RngCore, degree: usize) -> Self;

    // generate a random PolyRing with default degree 'n', aka the bound degree.
    // TODO: Does it need to export the BOUND_DGREE in trait?
    fn rand_with_bound_degree(rng: &mut impl rand::RngCore) -> Self;

    /// Create a zero polynomial
    fn zero() -> Self;

    /// Create a polynomial representing 1
    // fn one() -> Self;

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
