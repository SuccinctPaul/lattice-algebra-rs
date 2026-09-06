//! Polynomial Quotient Ring `R[x]/(x^n + 1)`
//!
//! This module provides an efficient implementation of polynomial rings
//! used in lattice-based cryptography.
//!
//! # Optimization Strategy
//!
//! For the special modulus `x^n + 1`, we use the property:
//! - `x^n ≡ -1 (mod x^n + 1)`
//! - Therefore `x^(n+k) ≡ -x^k`
//!
//! This allows O(n) reduction instead of O(n²) polynomial division.
//!
//! When NTT is available (q ≡ 1 mod 2n), we use negacyclic NTT for
//! O(n log n) multiplication.

use crate::ntt::{is_ntt_friendly, NttOperatorOptimized};
use crate::poly::UniPolynomial;
use crate::ring::MatrixElement;
use crate::ring::{PolynomialQuotientRing, Ring};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// A polynomial ring `R[x]/(x^n+1)` where R is a base ring and n is the degree bound.
///
/// # Type Parameters
/// - `R`: The coefficient ring (must implement `Ring`)
/// - `DEGREE_BOUND`: The polynomial degree bound `n` (ring dimension)
///
/// # Mathematical Definition
/// Elements are polynomials of degree < n with arithmetic modulo `x^n + 1`.
/// This defines a **negacyclic** (anticyclic) ring structure.
///
/// # Example
/// ```ignore
/// use lattice_algebra_rs::ring::poly_ring::PolyRing;
/// use lattice_algebra_rs::ring::zq::Zq;
///
/// type Zq17 = Zq<17>;
/// type R = PolyRing<Zq17, 8>;  // Z_17[x]/(x^8 + 1)
///
/// let a = R::from_coefficients(vec![Zq17::new(1), Zq17::new(2)]);
/// let b = R::from_coefficients(vec![Zq17::new(3), Zq17::new(4)]);
/// let c = a * b;  // Uses NTT if available, else negacyclic reduction
/// ```
#[derive(Debug, Clone, Eq, PartialEq, Serialize, Deserialize)]
pub struct PolyRing<R: Ring, const DEGREE_BOUND: usize> {
    #[serde(bound(serialize = "R: Serialize", deserialize = "R: Deserialize<'de>"))]
    pub inner: UniPolynomial<R>,
}

impl<R: Ring, const DEGREE_BOUND: usize> PolyRing<R, DEGREE_BOUND> {
    /// Creates a new PolyRing element from a polynomial.
    ///
    /// The polynomial is automatically reduced modulo `x^n + 1`.
    ///
    /// # Complexity
    /// - O(n) for polynomials of degree < 2n (using negacyclic reduction)
    /// - O(n²) for higher degree polynomials (fallback to division)
    pub fn new(poly: UniPolynomial<R>) -> Self {
        let n = DEGREE_BOUND;

        if n == 0 {
            // R[x]/(x^0 + 1) = R[x]/(2): the zero ring for invertible 2.
            return Self {
                inner: UniPolynomial::zero(),
            };
        }

        let coeffs = poly.coefficients();
        let deg = coeffs.len();

        // If already reduced, no work needed
        if deg <= n {
            return Self { inner: poly };
        }

        // Pure ring-op negacyclic fold: x^(n+k) ≡ -x^k, applied per block so
        // arbitrary input degrees reduce without polynomial division.
        let mut reduced = vec![R::ZERO; n];
        for (i, &c) in coeffs.iter().enumerate() {
            if (i / n) % 2 == 0 {
                reduced[i % n] += c;
            } else {
                reduced[i % n] -= c;
            }
        }

        let mut inner = UniPolynomial::from_coefficients(reduced);
        inner.normalize();
        Self { inner }
    }

    /// Creates a PolyRing element from coefficients without reduction.
    ///
    /// # Safety
    /// Caller must ensure coefficients represent a polynomial of degree < n.
    /// Use this for performance when you know the input is already reduced.
    #[inline]
    pub fn from_coefficients_unchecked(coeffs: Vec<R>) -> Self {
        Self {
            inner: UniPolynomial::from_coefficients(coeffs),
        }
    }

    /// Fast negacyclic reduction for polynomials of degree < 2n.
    ///
    /// Uses the property: x^n ≡ -1 (mod x^n + 1)
    ///
    /// For a polynomial c(x) = c_0 + c_1*x + ... + c_{2n-1}*x^{2n-1}:
    /// c(x) mod (x^n + 1) = (c_0 - c_n) + (c_1 - c_{n+1})*x + ... + (c_{n-1} - c_{2n-1})*x^{n-1}
    ///
    /// # Complexity: O(n)
    #[inline]
    fn reduce_negacyclic(coeffs: &[R], n: usize) -> Vec<R> {
        let mut result = vec![R::ZERO; n];

        for (i, &c) in coeffs.iter().enumerate() {
            if i < n {
                result[i] += c;
            } else {
                // x^(n+k) ≡ -x^k, so subtract
                result[i - n] -= c;
            }
        }

        // Normalize: remove trailing zeros
        while result.len() > 1 && result.last() == Some(&R::ZERO) {
            result.pop();
        }

        result
    }

    /// Performs negacyclic polynomial multiplication.
    ///
    /// Computes a(x) * b(x) mod (x^n + 1) using the negacyclic convolution.
    ///
    /// # Complexity
    /// - O(n log n) if NTT is available (q ≡ 1 mod 2n)
    /// - O(n²) otherwise (schoolbook + reduction)
    fn mul_negacyclic(a: &[R], b: &[R], n: usize) -> Vec<R> {
        // Check if NTT is available for this configuration
        if Self::is_ntt_available() && n.is_power_of_two() {
            Self::mul_ntt(a, b, n)
        } else {
            Self::mul_schoolbook_negacyclic(a, b, n)
        }
    }

    /// Checks if NTT can be used for this ring configuration.
    ///
    /// NTT requires:
    /// 1. n is a power of 2
    /// 2. q ≡ 1 (mod 2n) where q is the modulus of R
    #[inline]
    pub fn is_ntt_available() -> bool {
        let n = DEGREE_BOUND;
        n.is_power_of_two() && is_ntt_friendly::<R>(n)
    }

    /// NTT-based multiplication for negacyclic convolution.
    ///
    /// # Complexity: O(n log n)
    fn mul_ntt(a: &[R], b: &[R], n: usize) -> Vec<R> {
        // Pad inputs to length n
        let mut a_padded = vec![R::ZERO; n];
        let mut b_padded = vec![R::ZERO; n];

        for (i, &coeff) in a.iter().enumerate().take(n) {
            a_padded[i] = coeff;
        }
        for (i, &coeff) in b.iter().enumerate().take(n) {
            b_padded[i] = coeff;
        }

        // Use NTT for multiplication
        // We need to dispatch based on n at runtime
        Self::ntt_multiply_dispatch(&a_padded, &b_padded, n)
    }

    /// Dispatch NTT multiplication based on dimension.
    fn ntt_multiply_dispatch(a: &[R], b: &[R], n: usize) -> Vec<R> {
        // For compile-time known dimensions, we can use const generics
        // For runtime dispatch, we need to match on common sizes
        match n {
            2 => Self::ntt_multiply_sized::<2>(a, b),
            4 => Self::ntt_multiply_sized::<4>(a, b),
            8 => Self::ntt_multiply_sized::<8>(a, b),
            16 => Self::ntt_multiply_sized::<16>(a, b),
            32 => Self::ntt_multiply_sized::<32>(a, b),
            64 => Self::ntt_multiply_sized::<64>(a, b),
            128 => Self::ntt_multiply_sized::<128>(a, b),
            256 => Self::ntt_multiply_sized::<256>(a, b),
            512 => Self::ntt_multiply_sized::<512>(a, b),
            1024 => Self::ntt_multiply_sized::<1024>(a, b),
            _ => {
                // Fallback to schoolbook for unsupported sizes
                Self::mul_schoolbook_negacyclic(a, b, n)
            }
        }
    }

    /// NTT multiplication for a specific dimension.
    ///
    /// Uses `NttOperatorOptimized` with precomputed twiddle factors for
    /// better performance (avoids recomputing ω^k in each butterfly).
    fn ntt_multiply_sized<const N: usize>(a: &[R], b: &[R]) -> Vec<R> {
        // Check NTT compatibility at runtime
        if !is_ntt_friendly::<R>(N) {
            return Self::mul_schoolbook_negacyclic(a, b, N);
        }

        // Use optimized NTT with precomputed twiddle factors
        let ntt = NttOperatorOptimized::<R, N>::new();

        // Convert slices to fixed-size arrays
        let mut a_arr = [R::ZERO; N];
        let mut b_arr = [R::ZERO; N];

        for (i, &coeff) in a.iter().enumerate().take(N) {
            a_arr[i] = coeff;
        }
        for (i, &coeff) in b.iter().enumerate().take(N) {
            b_arr[i] = coeff;
        }

        let result = ntt.multiply_negacyclic(&a_arr, &b_arr);

        // Normalize result
        let mut coeffs: Vec<R> = result.to_vec();
        while coeffs.len() > 1 && coeffs.last() == Some(&R::ZERO) {
            coeffs.pop();
        }

        coeffs
    }

    /// Schoolbook multiplication with negacyclic reduction.
    ///
    /// # Complexity: O(n²)
    fn mul_schoolbook_negacyclic(a: &[R], b: &[R], n: usize) -> Vec<R> {
        // Compute full product (up to degree 2n-2)
        let mut product = vec![R::ZERO; 2 * n - 1];

        for (i, &ai) in a.iter().enumerate() {
            for (j, &bj) in b.iter().enumerate() {
                let k = i + j;
                if k < product.len() {
                    product[k] += ai * bj;
                }
            }
        }

        // Apply negacyclic reduction
        Self::reduce_negacyclic(&product, n)
    }
}

impl<R: Ring, const DEGREE_BOUND: usize> PolynomialQuotientRing for PolyRing<R, DEGREE_BOUND> {
    type PolyCoeff = R;

    /// Returns the modulus polynomial x^n + 1.
    ///
    /// This defines the anticyclic (negacyclic) lattice structure.
    fn modulus() -> UniPolynomial<Self::PolyCoeff> {
        let n = DEGREE_BOUND;
        if n == 0 {
            vec![R::from(2)]
        } else {
            let mut coeffs = vec![R::ZERO; n + 1];
            coeffs[0] = R::ONE; // Constant term: +1
            coeffs[n] = R::ONE; // Leading term: x^n
            coeffs
        }
        .into_iter()
        .collect::<Vec<_>>()
        .pipe(UniPolynomial::from_coefficients)
    }

    fn normalize(&mut self) {
        self.inner.normalize();
    }

    fn rand(rng: &mut impl RngCore, degree: usize) -> Self {
        let n = DEGREE_BOUND;
        let actual_degree = degree.min(n.saturating_sub(1));
        Self::new(UniPolynomial::rand(rng, actual_degree))
    }

    fn rand_with_bound_degree(rng: &mut impl RngCore) -> Self {
        let n = DEGREE_BOUND;
        if n == 0 {
            Self::rand(rng, 0)
        } else {
            Self::rand(rng, n - 1)
        }
    }

    fn degree(&self) -> usize {
        self.inner.degree()
    }

    fn set_coefficient(&mut self, i: usize, value: Self::PolyCoeff) {
        self.inner.set_coefficient(i, value);
    }

    fn evaluate(&self, x: &Self::PolyCoeff) -> Self::PolyCoeff {
        self.inner.evaluate(x)
    }

    fn from_coefficients(coeffs: Vec<Self::PolyCoeff>) -> Self {
        Self::new(UniPolynomial::from_coefficients(coeffs))
    }

    fn coefficients(&self) -> Vec<Self::PolyCoeff> {
        self.inner.coefficients()
    }

    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }
}

// Helper trait for pipe operator
trait Pipe: Sized {
    fn pipe<F, T>(self, f: F) -> T
    where
        F: FnOnce(Self) -> T,
    {
        f(self)
    }
}
impl<T> Pipe for T {}

// ============================================================================
// Arithmetic Operations
// ============================================================================

impl<R: Ring, const DEGREE_BOUND: usize> Add for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    /// Polynomial addition in the ring.
    ///
    /// Since degree of sum ≤ max(deg a, deg b) < n, no reduction needed.
    #[inline]
    fn add(self, rhs: Self) -> Self::Output {
        // Addition doesn't increase degree beyond n-1, so no reduction needed
        Self {
            inner: self.inner + rhs.inner,
        }
    }
}

impl<R: Ring, const DEGREE_BOUND: usize> AddAssign for PolyRing<R, DEGREE_BOUND> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        self.inner += rhs.inner;
    }
}

impl<'a, R: Ring, const DEGREE_BOUND: usize> Add<&'a Self> for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    #[inline]
    fn add(self, rhs: &'a Self) -> Self::Output {
        Self {
            inner: self.inner + &rhs.inner,
        }
    }
}

impl<R: Ring, const DEGREE_BOUND: usize> Neg for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    /// Coefficient-wise negation (additive inverse in the ring).
    #[inline]
    fn neg(self) -> Self {
        Self {
            inner: self.inner.negate(),
        }
    }
}

impl<R: Ring, const DEGREE_BOUND: usize> Sub for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    /// Polynomial subtraction in the ring.
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            inner: self.inner - rhs.inner,
        }
    }
}

impl<'a, R: Ring, const DEGREE_BOUND: usize> Sub<&'a Self> for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    #[inline]
    fn sub(self, rhs: &'a Self) -> Self::Output {
        Self {
            inner: self.inner - &rhs.inner,
        }
    }
}

impl<R: Ring, const DEGREE_BOUND: usize> SubAssign for PolyRing<R, DEGREE_BOUND> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        self.inner -= rhs.inner;
    }
}

impl<R: Ring, const DEGREE_BOUND: usize> Mul for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    /// Polynomial multiplication in `Z_q[x]/(x^n + 1)`.
    ///
    /// # Complexity
    /// - O(n log n) if NTT is available
    /// - O(n²) otherwise
    fn mul(self, rhs: Self) -> Self::Output {
        let n = DEGREE_BOUND;

        if n == 0 {
            return Self::new(self.inner * rhs.inner);
        }

        let a_coeffs = self.coefficients();
        let b_coeffs = rhs.coefficients();

        let result_coeffs = Self::mul_negacyclic(&a_coeffs, &b_coeffs, n);

        Self::from_coefficients_unchecked(result_coeffs)
    }
}

impl<'a, R: Ring, const DEGREE_BOUND: usize> Mul<&'a Self> for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self::Output {
        let n = DEGREE_BOUND;

        if n == 0 {
            return Self::new(self.inner * &rhs.inner);
        }

        let a_coeffs = self.coefficients();
        let b_coeffs = rhs.coefficients();

        let result_coeffs = Self::mul_negacyclic(&a_coeffs, &b_coeffs, n);

        Self::from_coefficients_unchecked(result_coeffs)
    }
}

impl<R: Ring, const DEGREE_BOUND: usize> MulAssign for PolyRing<R, DEGREE_BOUND> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

// ============================================================================
// Display and Other Traits
// ============================================================================

impl<R: Ring + Display, const DEGREE_BOUND: usize> Display for PolyRing<R, DEGREE_BOUND> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let coeffs = self.coefficients();
        if coeffs.is_empty() || (coeffs.len() == 1 && coeffs[0] == R::ZERO) {
            return write!(f, "0");
        }

        let mut first = true;
        for (i, coeff) in coeffs.iter().enumerate().rev() {
            if *coeff != R::ZERO {
                if !first {
                    write!(f, " + ")?;
                }
                first = false;

                match i {
                    0 => write!(f, "{coeff}")?,
                    1 => {
                        if *coeff == R::ONE {
                            write!(f, "x")?
                        } else {
                            write!(f, "{coeff}x")?
                        }
                    }
                    _ => {
                        if *coeff == R::ONE {
                            write!(f, "x^{i}")?
                        } else {
                            write!(f, "{coeff}x^{i}")?
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

impl<R: Ring + Display, const DEGREE_BOUND: usize> MatrixElement for PolyRing<R, DEGREE_BOUND> {
    fn zero() -> Self {
        Self {
            inner: UniPolynomial::zero(),
        }
    }

    fn one() -> Self {
        Self::from_coefficients(vec![R::ONE])
    }

    fn random(rng: &mut impl RngCore) -> Self {
        Self::rand_with_bound_degree(rng)
    }
}

impl<R: Ring, const DEGREE_BOUND: usize> Sum for PolyRing<R, DEGREE_BOUND> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(
            Self {
                inner: UniPolynomial::zero(),
            },
            Self::add,
        )
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::Zq17;

    // Helper function to create a test polynomial
    fn create_test_poly<R: Ring>(coeffs: Vec<u64>) -> PolyRing<R, 4> {
        let coeffs = coeffs.into_iter().map(|x| R::from(x)).collect();
        PolyRing::from_coefficients(coeffs)
    }

    #[test]
    fn test_new() {
        let poly = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);
        assert_eq!(
            poly.coefficients(),
            vec![Zq17::new(1), Zq17::new(2), Zq17::new(3), Zq17::new(4)]
        );
    }

    #[test]
    fn test_zero() {
        let zero = PolyRing::<Zq17, 4>::zero();
        assert!(zero.is_zero());
        assert_eq!(zero.coefficients(), vec![Zq17::ZERO]);
    }

    #[test]
    fn test_one() {
        let one = PolyRing::<Zq17, 4>::from_coefficients(vec![Zq17::ONE]);
        assert_eq!(one.coefficients(), vec![Zq17::ONE]);
    }

    #[test]
    fn test_degree() {
        let poly = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);
        assert_eq!(poly.degree(), 3);

        let zero = PolyRing::<Zq17, 4>::zero();
        assert_eq!(zero.degree(), 0);
    }

    #[test]
    fn test_addition() {
        let a = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);
        let b = create_test_poly::<Zq17>(vec![5, 6, 7, 8]);
        let sum = a + b;
        assert_eq!(
            sum.coefficients(),
            vec![
                Zq17::new(6),  // 1 + 5
                Zq17::new(8),  // 2 + 6
                Zq17::new(10), // 3 + 7
                Zq17::new(12)  // 4 + 8
            ]
        );
    }

    #[test]
    fn test_subtraction() {
        let a = create_test_poly::<Zq17>(vec![5, 6, 7, 8]);
        let b = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);
        let diff = a - b;
        assert_eq!(
            diff.coefficients(),
            vec![
                Zq17::new(4), // 5 - 1
                Zq17::new(4), // 6 - 2
                Zq17::new(4), // 7 - 3
                Zq17::new(4)  // 8 - 4
            ]
        );
    }

    #[test]
    fn test_multiplication_simple() {
        let a = create_test_poly::<Zq17>(vec![1, 2]);
        let b = create_test_poly::<Zq17>(vec![3, 4]);
        let product = a * b;
        // (1 + 2x)(3 + 4x) = 3 + 10x + 8x^2
        // In Zq17[x]/(x^4 + 1), degree < 4, no wraparound
        assert_eq!(
            product.coefficients(),
            vec![
                Zq17::new(3),  // 1 * 3
                Zq17::new(10), // 1 * 4 + 2 * 3
                Zq17::new(8),  // 2 * 4
            ]
        );
    }

    #[test]
    fn test_multiplication_with_wraparound() {
        // Test negacyclic wraparound: x^4 ≡ -1 (mod x^4 + 1)
        // a(x) = x^3, b(x) = x^2
        // a * b = x^5 = x^4 * x = -x (mod x^4 + 1)
        let a = PolyRing::<Zq17, 4>::from_coefficients(vec![
            Zq17::ZERO,
            Zq17::ZERO,
            Zq17::ZERO,
            Zq17::ONE,
        ]); // x^3
        let b = PolyRing::<Zq17, 4>::from_coefficients(vec![Zq17::ZERO, Zq17::ZERO, Zq17::ONE]); // x^2
        let product = a * b;

        // x^5 mod (x^4 + 1) = -x = (q-1)x = 16x
        assert_eq!(
            product.coefficients(),
            vec![Zq17::ZERO, Zq17::new(16)] // -x = 16x in Z_17
        );
    }

    #[test]
    fn test_multiplication_identity() {
        let a = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);
        let one = PolyRing::<Zq17, 4>::one();
        let product = a.clone() * one;
        assert_eq!(product.coefficients(), a.coefficients());
    }

    #[test]
    fn test_reduce_negacyclic() {
        let n = 4usize;
        // Polynomial: 1 + 2x + 3x^2 + 4x^3 + 5x^4 + 6x^5
        // x^4 ≡ -1, x^5 ≡ -x
        // Result: (1-5) + (2-6)x + 3x^2 + 4x^3 = -4 - 4x + 3x^2 + 4x^3
        // In Z_17: 13 + 13x + 3x^2 + 4x^3
        let coeffs = vec![
            Zq17::new(1),
            Zq17::new(2),
            Zq17::new(3),
            Zq17::new(4),
            Zq17::new(5),
            Zq17::new(6),
        ];
        let result = PolyRing::<Zq17, 4>::reduce_negacyclic(&coeffs, n);

        assert_eq!(
            result,
            vec![
                Zq17::new(13), // 1 - 5 = -4 = 13 mod 17
                Zq17::new(13), // 2 - 6 = -4 = 13 mod 17
                Zq17::new(3),
                Zq17::new(4),
            ]
        );
    }

    #[test]
    fn test_is_ntt_available() {
        // q = 17, n = 8: 17 ≡ 1 (mod 16) ✓
        assert!(PolyRing::<Zq17, 8>::is_ntt_available());

        // q = 17, n = 4: 17 ≡ 1 (mod 8) ✓
        assert!(PolyRing::<Zq17, 4>::is_ntt_available());

        // q = 17, n = 16: 17 ≡ 1 (mod 32)? 17 % 32 = 17 ≠ 1 ✗
        assert!(!PolyRing::<Zq17, 16>::is_ntt_available());
    }

    #[test]
    fn test_ntt_multiplication() {
        // Use n = 8 which is NTT-compatible with q = 17
        type R = PolyRing<Zq17, 8>;

        let a = R::from_coefficients(vec![Zq17::new(1), Zq17::new(2), Zq17::new(3)]);
        let b = R::from_coefficients(vec![Zq17::new(4), Zq17::new(5)]);

        let product = a.clone() * b.clone();

        // Verify commutativity
        let product2 = b * a;
        assert_eq!(product.coefficients(), product2.coefficients());
    }

    #[test]
    fn test_multiplication_associativity() {
        type R = PolyRing<Zq17, 8>;

        let a = R::from_coefficients(vec![Zq17::new(1), Zq17::new(2)]);
        let b = R::from_coefficients(vec![Zq17::new(3), Zq17::new(4)]);
        let c = R::from_coefficients(vec![Zq17::new(5), Zq17::new(6)]);

        let ab_c = (a.clone() * b.clone()) * c.clone();
        let a_bc = a * (b * c);

        assert_eq!(ab_c.coefficients(), a_bc.coefficients());
    }

    #[test]
    #[ignore]
    fn test_random() {
        let mut rng = rand::rng();
        let poly = PolyRing::<Zq17, 4>::random(&mut rng);
        if poly.is_zero() {
            assert_eq!(poly.degree(), 0);
        } else {
            assert!(poly.degree() < 4);
        }
    }

    #[test]
    fn test_evaluate() {
        let poly = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);
        let x = Zq17::new(2);
        // 1 + 2*2 + 3*2^2 + 4*2^3 = 1 + 4 + 12 + 32 = 49 mod 17 = 15
        assert_eq!(poly.evaluate(&x), Zq17::new(15));
    }

    #[test]
    fn test_normalize() {
        let mut poly = create_test_poly::<Zq17>(vec![1, 2, 3, 0]);
        poly.normalize();
        assert_eq!(
            poly.coefficients(),
            vec![Zq17::new(1), Zq17::new(2), Zq17::new(3)]
        );
    }

    #[test]
    fn test_serialization() {
        let poly = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);

        let serialized = serde_json::to_string(&poly).unwrap();
        let deserialized: PolyRing<Zq17, 4> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(poly, deserialized);
    }

    #[test]
    fn test_display() {
        let poly = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);
        let display = format!("{poly}");
        assert_eq!(display, "4x^3 + 3x^2 + 2x + 1");

        let zero = PolyRing::<Zq17, 4>::zero();
        assert_eq!(format!("{zero}"), "0");
    }

    #[test]
    fn test_sum() {
        let polys = vec![
            create_test_poly::<Zq17>(vec![1, 2]),
            create_test_poly::<Zq17>(vec![3, 4]),
            create_test_poly::<Zq17>(vec![5, 6]),
        ];
        let sum: PolyRing<Zq17, 4> = polys.into_iter().sum();
        assert_eq!(
            sum.coefficients(),
            vec![
                Zq17::new(9),  // 1 + 3 + 5
                Zq17::new(12)  // 2 + 4 + 6
            ]
        );
    }
}
