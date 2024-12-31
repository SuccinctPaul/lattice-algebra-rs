use crate::ring::Ring;
use rand::RngCore;
use std::fmt::{Debug, Display};
use std::ops::{
    Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub, SubAssign,
};

pub mod uni_poly;

pub trait Polynomial:
    Add<Output = Self>
    + AddAssign
    + for<'a> Add<&'a Self, Output = Self>
    + Mul<Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + MulAssign
    + Sub<Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + SubAssign
    + Div<Output = Self>
    + for<'a> Div<&'a Self, Output = Self>
    + DivAssign
    + Rem<Output = Self>
    + for<'a> Rem<&'a Self, Output = Self>
    + RemAssign
    + Sized
    + Clone
    + Debug
    + PartialEq
    + Eq
    + Display
{
    type Coefficient: Ring;

    fn rand(rng: &mut impl rand::RngCore, degree: usize) -> Self;
    /// Remove leading zero coefficients
    fn normalize(&mut self);

    /// Create a zero polynomial
    fn zero() -> Self;

    /// Create a polynomial representing 1
    // fn one() -> Self;

    /// Get the degree of the polynomial
    fn degree(&self) -> usize;

    /// Get the coefficient of the x^i term
    fn coefficient(&self, i: usize) -> Self::Coefficient;

    /// Set the coefficient of the x^i term
    fn set_coefficient(&mut self, i: usize, value: Self::Coefficient);

    /// Evaluate the polynomial at a given point
    fn evaluate(&self, x: &Self::Coefficient) -> Self::Coefficient;

    /// Create a polynomial from a list of coefficients
    fn from_coefficients(coeffs: Vec<Self::Coefficient>) -> Self;

    /// Get all coefficients of the polynomial
    fn coefficients(&self) -> Vec<Self::Coefficient>;

    /// Negate the polynomial
    fn negate(&self) -> Self;

    /// Compute the derivative of the polynomial
    fn derivative(&self) -> Self;

    /// Check if the polynomial is zero
    fn is_zero(&self) -> bool;

    /// Divide self by another polynomial, and returns the
    /// quotient and remainder.
    ///
    /// Reference: https://github.com/arkworks-rs/algebra/blob/9ce33e6ef1368a0f5b01b91e6df5bc5877129f30/poly/src/polynomial/univariate/mod.rs#L105
    fn divide_with_q_and_r(&self, divisor: &Self) -> Option<(Self, Self)>;

    // /// Compute the greatest common divisor of two polynomials
    // fn gcd(a: &Self, b: &Self) -> Self;
    //
    // /// Compute the extended Euclidean algorithm for polynomials
    // fn extended_gcd(a: &Self, b: &Self) -> (Self, Self, Self);
}
