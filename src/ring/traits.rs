//! Scalar-ring capability traits (L0).
//!
//! The capability set is deliberately decomposed instead of one "god trait":
//! upper layers declare the minimal capability they need, and the const
//! generics (`Zq<q>`) pick up capabilities at compile time.
//!
//! - [`Ring`]: commutative ring with unity (add / sub / mul / neg)
//! - [`Field`]: every non-zero element is invertible (implies [`Ring`])
//! - [`TwoAdicRing`]: the modulus is NTT friendly (implies [`Ring`])
//! - [`CenteredRing`]: centered representatives and the infinity norm
//! - [`MatrixElement`]: legacy matrix-container element requirement
//!
//! See `docs/src/pages/design/scalar-ring.mdx` for the design rationale.

use crate::poly::UniPolynomial;
use std::fmt::{Debug, Display};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Neg, Sub, SubAssign};

/// A commutative ring with unity, `Z_q` for `q >= 2`.
///
/// Deliberately minimal: ordering, display, division and matrix-container
/// concerns live in separate traits so that scheme layers can be generic over
/// exactly the algebra they use.
pub trait Ring:
    Sized
    + Copy
    + Clone
    + PartialEq
    + Eq
    + Debug
    + Send
    + Sync
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + From<u64>
{
    /// Modulus q (must be >= 2).
    const MODULUS: u64;
    /// Zero element (additive identity).
    const ZERO: Self;
    /// Multiplicative identity.
    const ONE: Self;

    /// Whether the modulus is prime, decided at compile time by a
    /// deterministic Miller-Rabin test. Algorithms that rely on primality
    /// (inverses, primitive roots) should assert on this flag.
    const IS_PRIME: bool = false;

    /// Uniformly random element of the ring.
    fn rand(rng: &mut impl rand::RngCore) -> Self;

    /// `self * self`.
    fn square(&self) -> Self;

    /// `self^power` by square-and-multiply.
    fn pow(&self, power: u64) -> Self;

    /// Widen to `u128` for intermediate arithmetic (`MODULUS <= u64::MAX`).
    fn to_u128(&self) -> u128;
}

/// A ring in which every non-zero element has a multiplicative inverse.
///
/// Division (`Div`) is intentionally not part of [`Ring`]: it is a field
/// operation. Polynomial division / remainder therefore require `R: Field`.
pub trait Field: Ring + Div<Output = Self> {
    /// Multiplicative inverse, `None` for zero (and for non-invertible
    /// elements when the modulus is composite).
    fn inverse(&self) -> Option<Self>;
}

/// A ring whose modulus is NTT friendly — the analogue of plonky3's
/// `TwoAdicField`.
///
/// A prime `q` admits an NTT of dimension `n` (with `n` a power of two) iff
/// `q ≡ 1 (mod 2n)`, i.e. `log2(2n) <= TWO_ADICITY`.
pub trait TwoAdicRing: Ring {
    /// Largest `b` such that `q ≡ 1 (mod 2^b)`, i.e. the 2-adicity of `q - 1`.
    const TWO_ADICITY: u32;

    /// An element of multiplicative order exactly `2^bits`.
    ///
    /// # Panics
    /// - If `bits > TWO_ADICITY`
    /// - If the modulus is not prime (a primitive root does not exist)
    fn two_adic_generator(bits: usize) -> Self;
}

/// Centered representatives and the infinity norm.
///
/// Both NIST PQC schemes and lattice ZK protocols reason about *signed*
/// coefficients (`|a|_inf = min(a, q - a)`); centralizing the semantics here
/// keeps ML-DSA norm checks and ZK soundness-slack accounting on one code path.
pub trait CenteredRing: Ring {
    /// Centered representative in the interval `(-q/2, q/2]`.
    fn centered(&self) -> i64;

    /// `|self|_inf = min(a, q - a)`.
    fn abs_infinity(&self) -> u64;

    /// `|self|_inf <= bound` (branch-free, safe on secret data).
    fn leq_infinity(&self, bound: u64) -> bool {
        self.abs_infinity() <= bound
    }
}

/// A polynomial quotient ring, e.g. `Z_q[x]/(x^d + 1)`.
///
/// Interim trait kept during the M0 refactor; M1 replaces it with the
/// representation-free `NegacyclicRing` / `CyclicRing` capabilities (see the
/// trait map in the design docs).
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

/// Requirement of the legacy generic matrix / vector containers.
///
/// Internal detail of the matrix module; scheme layers should use the
/// [`crate::module`] types instead (planned for M2, see the trait map in the
/// design docs).
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

/// Every displayable [`Ring`] element is a [`MatrixElement`].
impl<R> MatrixElement for R
where
    R: Ring + Display + Sum<R>,
{
    fn zero() -> Self {
        R::ZERO
    }

    fn one() -> Self {
        R::ONE
    }

    fn random(rng: &mut impl rand::RngCore) -> Self {
        R::rand(rng)
    }
}
