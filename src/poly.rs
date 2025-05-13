use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::ring::Ring;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};

use rand::RngCore;

/// A univariate polynomial over a ring R.
///
/// The polynomial is represented in little-endian format:
/// p(x) = a_0 + a_1 * x + ... + a_n * x^n
/// where coeffs = [a_0, a_1, ..., a_n]
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct UniPolynomial<R: Ring> {
    /// Coefficients of the polynomial in ascending order of degree
    coeffs: Vec<R>,
}

impl<R: Ring> UniPolynomial<R> {
    /// Creates a new polynomial from a vector of coefficients.
    ///
    /// # Arguments
    /// * `coeffs` - Vector of coefficients in ascending order of degree
    ///
    /// # Returns
    /// A new polynomial with leading zero coefficients removed
    pub fn new(mut coeffs: Vec<R>) -> Self {
        // Remove leading zeros
        while coeffs.len() > 1 && coeffs.last() == Some(&R::ZERO) {
            coeffs.pop();
        }
        Self { coeffs }
    }

    /// Multiplies the polynomial by a scalar value.
    ///
    /// # Arguments
    /// * `rhs` - The scalar value to multiply by
    ///
    /// # Returns
    /// A new polynomial representing the scalar multiplication
    pub fn scalar_mul(&self, rhs: &R) -> Self {
        if *rhs == R::ZERO {
            return Self::zero();
        }
        if *rhs == R::ONE {
            return self.clone();
        }
        let coeffs = self.coeffs.iter().map(|c| *c * *rhs).collect();
        Self::new(coeffs)
    }

    /// Generates a random polynomial of specified degree.
    ///
    /// # Arguments
    /// * `rng` - Random number generator
    /// * `degree` - The degree of the polynomial to generate
    ///
    /// # Returns
    /// A random polynomial with coefficients sampled from the ring R
    pub fn rand(rng: &mut impl RngCore, degree: usize) -> Self {
        let coeffs = (0..=degree).map(|_| R::rand(rng)).collect();
        Self::new(coeffs)
    }

    /// Removes leading zero coefficients from the polynomial.
    /// This operation is performed in-place.
    pub fn normalize(&mut self) {
        while self.coeffs.len() > 1 && self.coeffs.last() == Some(&R::ZERO) {
            self.coeffs.pop();
        }
    }

    /// Creates a zero polynomial (constant polynomial with value 0).
    ///
    /// # Returns
    /// A polynomial representing 0
    pub fn zero() -> Self {
        Self {
            coeffs: vec![R::ZERO],
        }
    }

    /// Returns the degree of the polynomial.
    /// The degree of the zero polynomial is defined as 0.
    ///
    /// # Returns
    /// The highest power of x with a non-zero coefficient
    pub fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            self.coeffs.len() - 1
        }
    }

    /// Returns the coefficient of the term with degree i.
    ///
    /// # Arguments
    /// * `i` - The degree of the term
    ///
    /// # Panics
    /// Panics if i is greater than the polynomial's degree
    pub fn coefficient(&self, i: usize) -> R {
        assert!(i <= self.degree(), "Index out of bounds");
        self.coeffs[i]
    }

    /// Sets the coefficient of the term with degree i.
    ///
    /// # Arguments
    /// * `i` - The degree of the term
    /// * `value` - The new coefficient value
    ///
    /// # Panics
    /// Panics if i is greater than the polynomial's degree
    pub fn set_coefficient(&mut self, i: usize, value: R) {
        assert!(i <= self.degree(), "Index out of bounds");
        self.coeffs[i] = value;
        self.normalize();
    }

    /// Evaluates the polynomial at a given point x.
    /// Uses Horner's method for efficient evaluation.
    ///
    /// # Arguments
    /// * `x` - The point at which to evaluate the polynomial
    ///
    /// # Returns
    /// The value of the polynomial at x
    pub fn evaluate(&self, x: &R) -> R {
        self.coeffs
            .iter()
            .rev()
            .fold(R::ZERO, |acc, coeff| acc * *x + *coeff)
    }

    /// Creates a polynomial from a vector of coefficients.
    /// Alias for `new()` for clarity in some contexts.
    ///
    /// # Arguments
    /// * `coeffs` - Vector of coefficients in ascending order of degree
    pub fn from_coefficients(coeffs: Vec<R>) -> Self {
        Self::new(coeffs)
    }

    /// Returns a copy of the polynomial's coefficients.
    ///
    /// # Returns
    /// Vector of coefficients in ascending order of degree
    pub fn coefficients(&self) -> Vec<R> {
        self.coeffs.clone()
    }

    /// Returns the negation of the polynomial.
    ///
    /// # Returns
    /// A new polynomial with all coefficients negated
    pub fn negate(&self) -> Self {
        Self::new(self.coeffs.iter().map(|c| -*c).collect())
    }

    /// Computes the derivative of the polynomial.
    ///
    /// # Returns
    /// A new polynomial representing the derivative
    pub fn derivative(&self) -> Self {
        if self.is_zero() || self.degree() == 0 {
            return Self::zero();
        }
        let coeffs = (1..=self.degree())
            .map(|i| self.coeffs[i] * R::from(i as u64))
            .collect();
        Self::new(coeffs)
    }

    /// Checks if the polynomial is the zero polynomial.
    ///
    /// # Returns
    /// True if the polynomial is zero, false otherwise
    pub fn is_zero(&self) -> bool {
        self.coeffs.len() == 1 && self.coeffs[0] == R::ZERO
    }

    /// Performs polynomial division with remainder.
    ///
    /// # Arguments
    /// * `divisor` - The polynomial to divide by
    ///
    /// # Returns
    /// Some((quotient, remainder)) if division is possible, None if divisor is zero
    ///
    /// # Panics
    /// Panics if attempting to divide by the zero polynomial
    pub fn divide_with_q_and_r(&self, divisor: &Self) -> Option<(Self, Self)> {
        if divisor.is_zero() {
            panic!("Dividing by zero polynomial");
        }
        if self.is_zero() {
            return Some((Self::zero(), Self::zero()));
        }
        if self.degree() < divisor.degree() {
            return Some((Self::zero(), self.clone()));
        }

        let mut remainder = self.coeffs.clone();
        let mut quotient = vec![R::ZERO; self.degree() - divisor.degree() + 1];
        let divisor_lead = divisor.coeffs[divisor.degree()];
        for k in (divisor.degree()..=self.degree()).rev() {
            if remainder[k] == R::ZERO {
                continue;
            }
            let q = remainder[k] / divisor_lead;
            quotient[k - divisor.degree()] = q;
            for j in 0..=divisor.degree() {
                remainder[k - divisor.degree() + j] -= q * divisor.coeffs[j];
            }
        }
        let r = remainder[..divisor.degree()].to_vec();
        Some((Self::new(quotient), Self::new(r)))
    }
}

impl<R: Ring> Add for UniPolynomial<R> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let max_len = std::cmp::max(self.coeffs.len(), rhs.coeffs.len());
        let coeffs = (0..max_len)
            .into_iter()
            .map(|n| {
                if n >= self.coeffs.len() {
                    rhs.coeffs[n]
                } else if n >= rhs.coeffs.len() {
                    self.coeffs[n]
                } else {
                    // n < self.0.len() && n < rhs.0.len()
                    self.coeffs[n] + rhs.coeffs[n]
                }
            })
            .collect::<Vec<R>>();
        Self::new(coeffs)
    }
}

impl<R: Ring> AddAssign for UniPolynomial<R> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}
impl<'a, R: Ring> Add<&'a Self> for UniPolynomial<R> {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self::Output {
        let max_len = std::cmp::max(self.coeffs.len(), rhs.coeffs.len());
        let coeffs = (0..max_len)
            .into_iter()
            .map(|n| {
                if n >= self.coeffs.len() {
                    rhs.coeffs[n]
                } else if n >= rhs.coeffs.len() {
                    self.coeffs[n]
                } else {
                    // n < self.0.len() && n < rhs.0.len()
                    self.coeffs[n] + rhs.coeffs[n]
                }
            })
            .collect::<Vec<R>>();
        Self::new(coeffs)
    }
}

// TODO: polynomial's multiplication can be implemented by the FFT- Fast Fourier Transform
impl<R: Ring> std::ops::Mul for UniPolynomial<R> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let mut coeffs: Vec<R> = vec![R::ZERO; self.coeffs.len() + rhs.coeffs.len() - 1];
        for n in 0..self.coeffs.len() {
            for m in 0..rhs.coeffs.len() {
                coeffs[n + m] += self.coeffs[n] * rhs.coeffs[m];
            }
        }
        Self::new(coeffs)
    }
}

// TODO: Use NTT to reduce the complexity O(d^2) to O(dlogd)
impl<'a, R: Ring> Mul<&'a Self> for UniPolynomial<R> {
    type Output = Self;
    fn mul(self, rhs: &Self) -> Self::Output {
        let mut coeffs: Vec<R> = vec![R::ZERO; self.coeffs.len() + rhs.coeffs.len() - 1];
        for n in 0..self.coeffs.len() {
            for m in 0..rhs.coeffs.len() {
                coeffs[n + m] += self.coeffs[n] * rhs.coeffs[m];
            }
        }
        Self::new(coeffs)
    }
}

impl<R: Ring> MulAssign for UniPolynomial<R> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = self.clone() * rhs;
    }
}

impl<R: Ring> Sub for UniPolynomial<R> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        let max_len = self.coeffs.len().max(rhs.coeffs.len());
        let mut result = Vec::with_capacity(max_len);

        for i in 0..max_len {
            let a = self.coeffs.get(i).cloned().unwrap_or_else(|| R::ZERO);
            let b = rhs.coeffs.get(i).cloned().unwrap_or_else(|| R::ZERO);
            result.push(a - b);
        }

        Self::new(result)
    }
}

impl<'a, R: Ring> Sub<&'a Self> for UniPolynomial<R> {
    type Output = Self;
    fn sub(self, rhs: &Self) -> Self::Output {
        let max_len = self.coeffs.len().max(rhs.coeffs.len());
        let mut result = Vec::with_capacity(max_len);

        for i in 0..max_len {
            let a = self.coeffs.get(i).cloned().unwrap_or_else(|| R::ZERO);
            let b = rhs.coeffs.get(i).cloned().unwrap_or_else(|| R::ZERO);
            result.push(a - b);
        }

        Self::new(result)
    }
}
impl<R: Ring> SubAssign for UniPolynomial<R> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = self.clone() - rhs;
    }
}
impl<'a, R: Ring> SubAssign<&'a Self> for UniPolynomial<R> {
    fn sub_assign(&mut self, rhs: &Self) {
        *self = self.clone() - rhs;
    }
}

impl<R: Ring> Div for UniPolynomial<R> {
    type Output = Self;

    fn div(self, divisor: Self) -> Self::Output {
        if let Some((q, r)) = self.divide_with_q_and_r(&divisor) {
            return q;
        }
        panic!("Dividing by zero polynomial")
    }
}

impl<'a, R: Ring> Div<&'a Self> for UniPolynomial<R> {
    type Output = Self;
    fn div(self, divisor: &Self) -> Self::Output {
        if let Some((q, r)) = self.divide_with_q_and_r(divisor) {
            return q;
        }
        panic!("Dividing by zero polynomial")
    }
}
impl<R: Ring> DivAssign for UniPolynomial<R> {
    fn div_assign(&mut self, rhs: Self) {
        *self = self.clone() / rhs;
    }
}
impl<'a, R: Ring> DivAssign<&'a Self> for UniPolynomial<R> {
    fn div_assign(&mut self, rhs: &Self) {
        *self = self.clone() / rhs;
    }
}

impl<R: Ring> Rem for UniPolynomial<R> {
    type Output = Self;

    fn rem(self, divisor: Self) -> Self::Output {
        if let Some((q, r)) = self.divide_with_q_and_r(&divisor) {
            return r;
        }
        panic!("Dividing by zero polynomial")
    }
}

impl<'a, R: Ring> Rem<&'a Self> for UniPolynomial<R> {
    type Output = Self;
    fn rem(self, divisor: &Self) -> Self::Output {
        if let Some((q, r)) = self.divide_with_q_and_r(divisor) {
            return r;
        }
        panic!("Dividing by zero polynomial")
    }
}
impl<R: Ring> RemAssign for UniPolynomial<R> {
    fn rem_assign(&mut self, rhs: Self) {
        *self = self.clone() % rhs;
    }
}
impl<'a, R: Ring> RemAssign<&'a Self> for UniPolynomial<R> {
    fn rem_assign(&mut self, rhs: &Self) {
        *self = self.clone() % rhs;
    }
}

/// Implementation of Display trait for pretty printing polynomials
impl<R: Ring> Display for UniPolynomial<R> {
    /// Formats the polynomial as a string in standard mathematical notation.
    ///
    /// # Examples
    /// - "0" for zero polynomial
    /// - "2x + 1" for linear polynomial
    /// - "x^2 + 3x + 2" for quadratic polynomial
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.coeffs.is_empty() || (self.coeffs.len() == 1 && self.coeffs[0] == R::ZERO) {
            return write!(f, "0");
        }

        let mut first = true;
        for (i, coeff) in self.coeffs.iter().enumerate().rev() {
            if *coeff != R::ZERO {
                if !first {
                    write!(f, " + ")?;
                }
                first = false;

                match i {
                    0 => write!(f, "{}", coeff)?,
                    1 => {
                        if *coeff == R::ONE {
                            write!(f, "x")?
                        } else {
                            write!(f, "{}x", coeff)?
                        }
                    }
                    _ => {
                        if *coeff == R::ONE {
                            write!(f, "x^{}", i)?
                        } else {
                            write!(f, "{}x^{}", coeff, i)?
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::Zq17;
    use rand::thread_rng;
    use std::ops::Neg;

    // Helper function to create test polynomials
    fn create_test_poly(coeffs: Vec<u64>) -> UniPolynomial<Zq17> {
        UniPolynomial::from_coefficients(coeffs.into_iter().map(|x| Zq17::new(x)).collect())
    }

    #[test]
    fn test_polynomial_creation() {
        // Test zero polynomial
        let zero = UniPolynomial::<Zq17>::zero();
        assert!(zero.is_zero());
        assert_eq!(zero.degree(), 0);
        assert_eq!(zero.coefficients(), vec![Zq17::ZERO]);

        // Test constant polynomial
        let const_poly = create_test_poly(vec![5]);
        assert!(!const_poly.is_zero());
        assert_eq!(const_poly.degree(), 0);
        assert_eq!(const_poly.coefficients(), vec![Zq17::new(5)]);

        // Test polynomial with leading zeros
        let poly = UniPolynomial::new(vec![Zq17::new(1), Zq17::new(2), Zq17::ZERO, Zq17::ZERO]);
        assert_eq!(poly.degree(), 1);
        assert_eq!(poly.coefficients(), vec![Zq17::new(1), Zq17::new(2)]);

        // Test high degree polynomial
        let coeffs = (0..20).map(Zq17::from).collect::<Vec<_>>();
        let poly = UniPolynomial::from_coefficients(coeffs.clone());
        assert_eq!(poly.degree(), 19);
        assert_eq!(poly.coefficients(), coeffs);
    }

    #[test]
    fn test_coefficient_operations() {
        let mut poly = create_test_poly(vec![1, 2, 3, 4]); // 4x^3 + 3x^2 + 2x + 1

        // Test coefficient access
        assert_eq!(poly.coefficient(0), Zq17::new(1));
        assert_eq!(poly.coefficient(1), Zq17::new(2));
        assert_eq!(poly.coefficient(2), Zq17::new(3));
        assert_eq!(poly.coefficient(3), Zq17::new(4));

        // Test coefficient setting
        poly.set_coefficient(1, Zq17::new(5));
        assert_eq!(poly.coefficient(1), Zq17::new(5));
        assert_eq!(
            poly.coefficients(),
            vec![Zq17::new(1), Zq17::new(5), Zq17::new(3), Zq17::new(4)]
        );

        // Test setting leading coefficient to zero
        poly.set_coefficient(3, Zq17::ZERO);
        assert_eq!(poly.degree(), 2);
        assert_eq!(
            poly.coefficients(),
            vec![Zq17::new(1), Zq17::new(5), Zq17::new(3)]
        );
    }

    #[test]
    #[should_panic(expected = "Index out of bounds")]
    fn test_coefficient_out_of_bounds() {
        let poly = create_test_poly(vec![1, 2, 3]);
        poly.coefficient(3); // Should panic
    }

    #[test]
    fn test_polynomial_arithmetic() {
        let p1 = create_test_poly(vec![1, 2, 3]); // 3x^2 + 2x + 1
        let p2 = create_test_poly(vec![4, 5, 6]); // 6x^2 + 5x + 4

        // Test addition
        let sum = p1.clone() + p2.clone();
        assert_eq!(
            sum.coefficients(),
            vec![Zq17::new(5), Zq17::new(7), Zq17::new(9)]
        );

        // Test subtraction
        let diff = p2.clone() - p1.clone();
        assert_eq!(
            diff.coefficients(),
            vec![Zq17::new(3), Zq17::new(3), Zq17::new(3)]
        );

        // Test multiplication
        let prod = p1.clone() * p2.clone();
        assert_eq!(
            prod.coefficients(),
            vec![
                Zq17::new(4),  // 1 * 4
                Zq17::new(13), // 1 * 5 + 2 * 4
                Zq17::new(28), // 1 * 6 + 2 * 5 + 3 * 4
                Zq17::new(27), // 2 * 6 + 3 * 5
                Zq17::new(18), // 3 * 6
            ]
        );

        // Test scalar multiplication
        let scalar = Zq17::new(2);
        let scaled = p1.scalar_mul(&scalar);
        assert_eq!(
            scaled.coefficients(),
            vec![Zq17::new(2), Zq17::new(4), Zq17::new(6)]
        );

        // Test negation
        let neg = p1.negate();
        assert_eq!(
            neg.coefficients(),
            vec![Zq17::new(16), Zq17::new(15), Zq17::new(14)]
        );
    }

    #[test]
    fn test_polynomial_division() {
        // Test division with remainder
        let p1 = create_test_poly(vec![1, 2, 1]); // x^2 + 2x + 1
        let p2 = create_test_poly(vec![1, 1]); // x + 1
        let (quotient, remainder) = p1.divide_with_q_and_r(&p2).unwrap();
        assert_eq!(quotient.coefficients(), vec![Zq17::new(1), Zq17::new(1)]); // x + 1
        assert!(remainder.is_zero());

        // Test division by higher degree polynomial
        let p3 = create_test_poly(vec![1, 1, 1]); // x^2 + x + 1
        let (quotient, remainder) = p1.divide_with_q_and_r(&p3).unwrap();
        assert_eq!(quotient.coefficients(), vec![Zq17::new(1)]);
        assert_eq!(remainder.coefficients(), vec![Zq17::new(0), Zq17::new(1)]);

        // Test division by zero polynomial
        let zero = UniPolynomial::<Zq17>::zero();
        let result = std::panic::catch_unwind(|| p1.divide_with_q_and_r(&zero));
        assert!(result.is_err());
    }

    #[test]
    fn test_polynomial_evaluation() {
        let poly = create_test_poly(vec![1, 2, 3]); // 3x^2 + 2x + 1

        // Test evaluation at x = 0
        assert_eq!(poly.evaluate(&Zq17::ZERO), Zq17::new(1));

        // Test evaluation at x = 1
        assert_eq!(poly.evaluate(&Zq17::ONE), Zq17::new(6));

        // Test evaluation at x = 2
        assert_eq!(poly.evaluate(&Zq17::new(2)), Zq17::new(17));

        // Test evaluation of zero polynomial
        let zero = UniPolynomial::<Zq17>::zero();
        assert_eq!(zero.evaluate(&Zq17::new(5)), Zq17::ZERO);
    }

    #[test]
    fn test_polynomial_derivative() {
        // Test derivative of quadratic polynomial
        let poly = create_test_poly(vec![1, 2, 3]); // 3x^2 + 2x + 1
        let deriv = poly.derivative();
        assert_eq!(deriv.coefficients(), vec![Zq17::new(2), Zq17::new(6)]); // 6x + 2

        // Test derivative of constant polynomial
        let const_poly = create_test_poly(vec![5]);
        assert!(const_poly.derivative().is_zero());

        // Test derivative of zero polynomial
        let zero = UniPolynomial::<Zq17>::zero();
        assert!(zero.derivative().is_zero());
    }

    #[test]
    fn test_random_polynomial_generation() {
        let mut rng = thread_rng();

        // Test random polynomial generation with different degrees
        for degree in 0..5 {
            let poly = UniPolynomial::<Zq17>::rand(&mut rng, degree);
            assert!(poly.degree() <= degree);
            assert!(!poly.coefficients().is_empty());
        }

        // Test that random polynomials are different
        let poly1 = UniPolynomial::<Zq17>::rand(&mut rng, 3);
        let poly2 = UniPolynomial::<Zq17>::rand(&mut rng, 3);
        assert_ne!(poly1, poly2);
    }

    #[test]
    fn test_polynomial_display() {
        let poly = create_test_poly(vec![1, 2, 3]); // 3x^2 + 2x + 1
        assert_eq!(poly.to_string(), "3x^2 + 2x + 1");

        let zero = UniPolynomial::<Zq17>::zero();
        assert_eq!(zero.to_string(), "0");

        let linear = create_test_poly(vec![2, 1]); // x + 2
        assert_eq!(linear.to_string(), "x + 2");

        let constant = create_test_poly(vec![5]); // 5
        assert_eq!(constant.to_string(), "5");
    }

    #[test]
    fn test_polynomial_assign_operations() {
        let mut p1 = create_test_poly(vec![1, 2, 3]);
        let p2 = create_test_poly(vec![4, 5, 6]);

        // Test add_assign
        p1 += p2.clone();
        assert_eq!(
            p1.coefficients(),
            vec![Zq17::new(5), Zq17::new(7), Zq17::new(9)]
        );

        // Test sub_assign
        p1 -= p2.clone();
        assert_eq!(
            p1.coefficients(),
            vec![Zq17::new(1), Zq17::new(2), Zq17::new(3)]
        );

        // Test mul_assign
        p1 *= p2.clone();
        assert_eq!(
            p1.coefficients(),
            vec![
                Zq17::new(4),
                Zq17::new(13),
                Zq17::new(28),
                Zq17::new(27),
                Zq17::new(18)
            ]
        );

        // Test div_assign and rem_assign
        let mut p3 = create_test_poly(vec![1, 2, 1]); // x^2 + 2x + 1
        let p4 = create_test_poly(vec![1, 1]); // x + 1
        p3 /= p4.clone();
        assert_eq!(p3.coefficients(), vec![Zq17::new(1), Zq17::new(1)]);
        p3 *= p4.clone();
        p3 %= p4;
        assert!(p3.is_zero());
    }

    #[test]
    fn test_polynomial_operations_with_references() {
        let p1 = create_test_poly(vec![1, 2, 3]);
        let p2 = create_test_poly(vec![4, 5, 6]);

        // Test addition with reference
        let sum = p1.clone() + &p2;
        assert_eq!(
            sum.coefficients(),
            vec![Zq17::new(5), Zq17::new(7), Zq17::new(9)]
        );

        // Test subtraction with reference
        let diff = p2.clone() - &p1;
        assert_eq!(
            diff.coefficients(),
            vec![Zq17::new(3), Zq17::new(3), Zq17::new(3)]
        );

        // Test multiplication with reference
        let prod = p1.clone() * &p2;
        assert_eq!(
            prod.coefficients(),
            vec![
                Zq17::new(4),
                Zq17::new(13),
                Zq17::new(28),
                Zq17::new(27),
                Zq17::new(18)
            ]
        );

        // Test division with reference
        let (quotient, remainder) = p1.divide_with_q_and_r(&p2).unwrap();
        assert_eq!(p1, p2 * quotient + remainder);
    }
}
