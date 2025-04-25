use crate::poly::Polynomial;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};

use crate::ring::Ring;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Rem, RemAssign, Sub, SubAssign};

use rayon::{current_num_threads, scope};

// Uni-var Polynomial
// p(x) = = a_0 + a_1 * X + ... + a_n * X^(n-1)
//
//
// coeffs: [a_0, a_1, ..., a_n]
//         (  0,   1,   ..., n)
// basis: X^[n-1]
//
// It's Little Endian.
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct UniPolynomial<R: Ring> {
    coeffs: Vec<R>,
}

impl<R: Ring> UniPolynomial<R> {
    pub fn new(mut coeffs: Vec<R>) -> Self {
        // Remove leading zeros
        while coeffs.len() > 1 && coeffs.last() == Some(&R::ZERO) {
            coeffs.pop();
        }
        Self { coeffs }
    }

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
}

impl<R: Ring> Polynomial for UniPolynomial<R> {
    type Coefficient = R;

    fn rand(rng: &mut impl rand::RngCore, degree: usize) -> Self {
        let coeffs = (0..=degree).map(|_| R::rand(rng)).collect();
        Self::new(coeffs)
    }

    fn normalize(&mut self) {
        while self.coeffs.len() > 1 && self.coeffs.last() == Some(&R::ZERO) {
            self.coeffs.pop();
        }
    }

    fn zero() -> Self {
        Self {
            coeffs: vec![R::ZERO],
        }
    }

    fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            self.coeffs.len() - 1
        }
    }

    fn coefficient(&self, i: usize) -> Self::Coefficient {
        assert!(i <= self.degree(), "Index out of bounds");
        self.coeffs[i]
    }

    fn set_coefficient(&mut self, i: usize, value: Self::Coefficient) {
        assert!(i <= self.degree(), "Index out of bounds");
        self.coeffs[i] = value;
        self.normalize();
    }

    fn evaluate(&self, x: &Self::Coefficient) -> Self::Coefficient {
        self.coeffs
            .iter()
            .rev()
            .fold(R::ZERO, |acc, coeff| acc * *x + *coeff)
    }

    fn from_coefficients(coeffs: Vec<Self::Coefficient>) -> Self {
        Self::new(coeffs)
    }

    fn coefficients(&self) -> Vec<Self::Coefficient> {
        self.coeffs.clone()
    }

    fn negate(&self) -> Self {
        Self::new(self.coeffs.iter().map(|c| -*c).collect())
    }

    fn derivative(&self) -> Self {
        if self.is_zero() || self.degree() == 0 {
            return Self::zero();
        }
        let coeffs = (1..=self.degree())
            .map(|i| self.coeffs[i] * R::from(i as u64))
            .collect();
        Self::new(coeffs)
    }

    fn is_zero(&self) -> bool {
        self.coeffs.len() == 1 && self.coeffs[0] == R::ZERO
    }

    fn divide_with_q_and_r(&self, divisor: &Self) -> Option<(Self, Self)> {
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

impl<R: Ring> Display for UniPolynomial<R> {
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
    use std::ops::Neg;
    #[test]
    fn test_ring_polynomial_display() {
        let poly = UniPolynomial::from_coefficients(vec![
            Zq17::new(3),
            Zq17::new(0),
            Zq17::new(2),
            Zq17::new(1),
        ]);
        // assert_eq!(poly.to_string(), "x^3 + 2x^2 + 3");
        println!("poly: {:?}", poly.to_string());
        let zero_poly = UniPolynomial::<Zq17>::zero();
        // assert_eq!(zero_poly.to_string(), "0");
        println!("zero_poly: {:?}", zero_poly.to_string());

        let linear_poly = UniPolynomial::from_coefficients(vec![Zq17::new(2), Zq17::new(1)]);
        // assert_eq!(linear_poly.to_string(), "1x + 2");
        println!("linear_poly: {:?}", linear_poly.to_string());
    }

    #[test]
    fn test_poly_addition() {
        let p1 = UniPolynomial::<Zq17>::from_coefficients(
            vec![3, 2, 1].into_iter().map(Zq17::from).collect(),
        ); // x^2 + 2x + 3
        let p2 = UniPolynomial::<Zq17>::from_coefficients(
            vec![6, 5, 4].into_iter().map(Zq17::from).collect(),
        ); // x^2 + 5x + 6
        let result = p1 + p2;
        assert_eq!(
            result.coeffs,
            vec![Zq17::new(9), Zq17::new(7), Zq17::new(5)]
        );
    }

    #[test]
    fn test_poly_subtraction() {
        let p1 = UniPolynomial::<Zq17>::from_coefficients(
            vec![6, 5, 4].into_iter().map(Zq17::from).collect(),
        ); // x^2 + 5x + 6
        let p2 = UniPolynomial::<Zq17>::from_coefficients(
            vec![3, 2, 1].into_iter().map(Zq17::from).collect(),
        ); // x^2 + 2x + 3
        let result = p1 - p2;
        assert_eq!(result.coeffs, vec![Zq17::new(3); 3]);

        //     s_tranpose_dot_u: "2x^3 + 7x^2 + 8x + 3"
        // ciphter_text.v:
        // "11x^3 + 7x^2 + x + 13"
        let p3 = UniPolynomial::<Zq17>::from_coefficients(
            vec![13, 1, 7, 11].into_iter().map(Zq17::from).collect(),
        );

        // 2x^3 + 7x^2 + 8x + 3
        let p4 = UniPolynomial::<Zq17>::from_coefficients(
            vec![3, 8, 7, 2].into_iter().map(Zq17::from).collect(),
        );

        let result = p3 - p4;
        println!("result: {:?}", result.to_string());
        assert_eq!(
            result.coeffs,
            vec![Zq17::new(10), Zq17::new(7).neg(), Zq17::ZERO, Zq17::new(9)]
        );
    }

    #[test]
    fn test_poly_multiplication() {
        let p1 = UniPolynomial::<Zq17>::from_coefficients(
            vec![1, 2].into_iter().map(Zq17::from).collect(),
        ); // 2x + 1
        let p2 = UniPolynomial::<Zq17>::from_coefficients(
            vec![3, 4].into_iter().map(Zq17::from).collect(),
        ); // 4x + 3
        // (2x + 1)*(4x+ 3)
        let result = p1 * p2;
        assert_eq!(
            result.coeffs,
            vec![Zq17::new(3), Zq17::new(10), Zq17::new(8)]
        );
    }

    #[test]
    fn test_poly_scalar_multiplication() {
        let p = UniPolynomial::<Zq17>::from_coefficients(
            vec![1, 2, 3].into_iter().map(Zq17::from).collect(),
        ); // x^2 + 2x + 3
        let q = Zq17::new(2);
        let result = p.scalar_mul(&q);
        assert_eq!(
            result.coeffs,
            vec![Zq17::new(2), Zq17::new(4), Zq17::new(6)]
        );
    }

    #[test]
    fn test_derivative() {
        // Test polynomial: 3x^3 + 2x^2 + x + 5
        let poly = UniPolynomial::from_coefficients(vec![
            Zq17::new(5),
            Zq17::new(1),
            Zq17::new(2),
            Zq17::new(3),
        ]);

        // Expected derivative: 9x^2 + 4x + 1
        let expected_derivative =
            UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(4), Zq17::new(9)]);

        assert_eq!(poly.derivative(), expected_derivative);

        // Test constant polynomial
        let constant_poly = UniPolynomial::from_coefficients(vec![Zq17::new(42)]);
        assert_eq!(constant_poly.derivative(), UniPolynomial::zero());

        // Test zero polynomial
        let zero_poly = UniPolynomial::<Zq17>::zero();
        assert_eq!(zero_poly.derivative(), UniPolynomial::zero());
    }
    #[test]
    fn test_negate() {
        // Test polynomial: 3x^2 + 2x + 1
        let poly = UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(2), Zq17::new(3)]);

        // Expected negation: -3x^2 - 2x - 1
        let expected_negation =
            UniPolynomial::from_coefficients(vec![-Zq17::new(1), -Zq17::new(2), -Zq17::new(3)]);

        assert_eq!(poly.negate(), expected_negation);

        // Test zero polynomial
        let zero_poly = UniPolynomial::<Zq17>::zero();
        assert_eq!(zero_poly.negate(), zero_poly);

        // Test negation of negation
        assert_eq!(poly.negate().negate(), poly);
    }
    #[test]
    fn test_poly_div_rem() {
        // Define polynomials
        let p1 = UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(2), Zq17::new(1)]); // x^2 + 2x + 1
        let p2 = UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(1)]); // x + 1

        // Perform division: (x^2 + 2x + 1)/(x + 1)
        let (quotient, remainder) = p1.clone().divide_with_q_and_r(&p2).unwrap();

        // Check quotient
        assert_eq!(quotient.coefficients(), vec![Zq17::new(1), Zq17::new(1)]); // x + 1

        // Check remainder
        assert!(remainder.is_zero()); // 0

        // Test division by higher degree polynomial
        let p3 = UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(1), Zq17::new(1)]); // x^2 + x + 1
        //  (x^2 + 2x + 1)/(x^2 + x + 1)
        let (quotient, remainder) = p1.divide_with_q_and_r(&p3).unwrap();

        // Check remainder is the same as the dividend
        assert_eq!(remainder.coefficients(), vec![Zq17::new(0), Zq17::new(1)]);
        assert_eq!(quotient.coefficients(), vec![Zq17::new(1)]);

        // (x^2 + x + 1)/(x^2 + 2x + 1)
        let (quotient, remainder) = p3.divide_with_q_and_r(&p1).unwrap();
        // Check remainder is the same as the dividend
        // assert_eq!(remainder.coefficients(), vec![Zq17::new(2), Zq17::new(2)]);
        assert_eq!(
            p3,
            (p1.clone() * quotient) + remainder,
            "divide_with_q_and_r error"
        );

        // Test division by zero polynomial
        let zero_poly = UniPolynomial::zero();
        let result = std::panic::catch_unwind(|| p1.divide_with_q_and_r(&zero_poly));
        assert!(result.is_err());
    }

    #[test]
    #[ignore]
    fn test_random_divide_poly() {
        let rng = &mut rand::thread_rng();

        for a_degree in 1..2 {
            for b_degree in 1..2 {
                let dividend = UniPolynomial::<Zq17>::rand(rng, a_degree);
                let divisor = UniPolynomial::<Zq17>::rand(rng, b_degree);
                println!("{a_degree}: dividend: {:?}", dividend.to_string());
                println!("{b_degree}: divisor: {:?}", divisor.to_string());
                if let Some((quotient, remainder)) = dividend.divide_with_q_and_r(&divisor) {
                    assert_eq!(
                        dividend,
                        (divisor * quotient) + remainder,
                        "divide_with_q_and_r error"
                    );
                    println!("Success");
                }
                println!("next\n");
            }
        }
    }

    #[test]
    #[ignore]
    fn divide_polynomials_random() {
        let rng = &mut rand::thread_rng();

        let a_degree = 2;
        let b_degree = 1;
        let dividend = UniPolynomial::<Zq17>::rand(rng, a_degree);
        let divisor = UniPolynomial::<Zq17>::rand(rng, b_degree);
        println!("{a_degree}: dividend: {:?}", dividend.to_string());
        println!("{b_degree}: divisor: {:?}", divisor.to_string());
        let quotient = dividend.clone().div(&divisor);
        let remainder = dividend.clone().rem(&divisor);
        assert_eq!(
            dividend,
            (divisor * quotient) + remainder,
            "divide_with_q_and_r error"
        );
        println!("Success");
    }

    #[test]
    fn test_mul_poly() {
        let p1 = UniPolynomial::<Zq17>::from_coefficients(
            vec![1, 2].into_iter().map(Zq17::from).collect(),
        ); // 2x + 1
        let p2 = UniPolynomial::<Zq17>::from_coefficients(
            vec![3, 4].into_iter().map(Zq17::from).collect(),
        ); // 4x + 3
        // (2x + 1)*(4x+ 3)
        let result = p1 * p2;
        assert_eq!(
            result.coeffs,
            vec![Zq17::new(3), Zq17::new(10), Zq17::new(8)]
        );
    }

    // #[test]
    // fn test_poly_scalar_multiplication() {
    //     let p = UniPolynomial::<Zq17>::from_coefficients(
    //         vec![1, 2, 3].into_iter().map(Zq17::from).collect(),
    //     ); // x^2 + 2x + 3
    //     let q = Zq17::new(2);
    //     let result = p.scalar_mul(&q);
    //     assert_eq!(
    //         result.coeffs,
    //         vec![Zq17::new(2), Zq17::new(4), Zq17::new(6)]
    //     );
    // }

    #[test]
    fn test_zero_and_constant_polynomials() {
        let zero = UniPolynomial::<Zq17>::zero();
        assert!(zero.is_zero());
        assert_eq!(zero.degree(), 0);
        assert_eq!(zero.coefficients(), vec![Zq17::ZERO]);

        let const_poly = UniPolynomial::from_coefficients(vec![Zq17::new(5)]);
        assert!(!const_poly.is_zero());
        assert_eq!(const_poly.degree(), 0);
        assert_eq!(const_poly.coefficients(), vec![Zq17::new(5)]);
    }

    // #[test]
    // fn test_add_assign_and_ref_rhs() {
    //     let mut p = UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(2)]);
    //     let q = UniPolynomial::from_coefficients(vec![Zq17::new(3), Zq17::new(4)]);
    //     p += q.clone();
    //     assert_eq!(p.coefficients(), vec![Zq17::new(4), Zq17::new(6)]);
    //     p += &q;
    //     assert_eq!(p.coefficients(), vec![Zq17::new(7), Zq17::new(10)]);
    // }

    #[test]
    fn test_sub_assign_and_ref_rhs() {
        let mut p = UniPolynomial::from_coefficients(vec![Zq17::new(5), Zq17::new(7)]);
        let q = UniPolynomial::from_coefficients(vec![Zq17::new(2), Zq17::new(3)]);
        p -= q.clone();
        assert_eq!(p.coefficients(), vec![Zq17::new(3), Zq17::new(4)]);
        p -= &q;
        assert_eq!(p.coefficients(), vec![Zq17::new(1), Zq17::new(1)]);
    }

    // #[test]
    // fn test_mul_assign_and_ref_rhs() {
    //     let mut p = UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(2)]);
    //     let q = UniPolynomial::from_coefficients(vec![Zq17::new(2), Zq17::new(1)]);
    //     p *= q.clone();
    //     assert_eq!(p.coefficients(), vec![Zq17::new(2), Zq17::new(5), Zq17::new(2)]);
    //     p *= &UniPolynomial::from_coefficients(vec![Zq17::new(1)]);
    //     assert_eq!(p.coefficients(), vec![Zq17::new(2), Zq17::new(5), Zq17::new(2)]);
    // }

    #[test]
    fn test_div_assign_and_rem_assign() {
        let mut p =
            UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(2), Zq17::new(1)]);
        let q = UniPolynomial::from_coefficients(vec![Zq17::new(1), Zq17::new(1)]);
        p /= q.clone();
        assert_eq!(p.coefficients(), vec![Zq17::new(1), Zq17::new(1)]);
        p *= q.clone();
        p %= q;
        assert!(p.is_zero());
    }

    #[test]
    fn test_evaluate_and_set_coefficient() {
        let mut poly = UniPolynomial::from_coefficients(vec![Zq17::new(2), Zq17::new(3)]);
        assert_eq!(poly.evaluate(&Zq17::new(2)), Zq17::new(8)); // 3*2 + 2 = 8
        poly.set_coefficient(0, Zq17::new(5));
        assert_eq!(poly.coefficient(0), Zq17::new(5));
        assert_eq!(poly.coefficients(), vec![Zq17::new(5), Zq17::new(3)]);
    }

    #[test]
    fn test_high_degree_polynomial() {
        let coeffs = (0..20).map(Zq17::from).collect::<Vec<_>>();
        let poly = UniPolynomial::from_coefficients(coeffs.clone());
        assert_eq!(poly.degree(), 19);
        assert_eq!(poly.coefficients(), coeffs);
    }
}
