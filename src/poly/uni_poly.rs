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
    // Constructor with normalize
    pub fn new(coeffs: Vec<R>) -> Self {
        let mut poly = Self { coeffs };
        poly.normalize();
        poly
    }

    fn scalar_mul(&self, rhs: &R) -> Self {
        let coeffs = if rhs == &R::one() {
            vec![R::one()]
        } else {
            self.coeffs.iter().map(|c| c.mul(rhs)).collect::<Vec<R>>()
        };
        Self::new(coeffs)
    }
}

impl<R: Ring> Polynomial for UniPolynomial<R> {
    type Coefficient = R;

    fn rand(rng: &mut impl rand::RngCore, degree: usize) -> Self {
        let coeffs = (0..degree + 1).map(|_| R::rand(rng)).collect::<Vec<_>>();
        Self::from_coefficients(coeffs)
    }

    // Remove leading zero coefficients
    fn normalize(&mut self) {
        while self.coeffs.len() > 1 && self.coeffs.last() == Some(&R::zero()) {
            self.coeffs.pop();
        }
    }

    fn zero() -> Self {
        Self {
            coeffs: vec![R::zero()],
        }
    }

    // The degree of the polynomial
    fn degree(&self) -> usize {
        if self.is_zero() {
            0
        } else {
            self.coeffs.len() - 1
        }
    }

    fn coefficient(&self, i: usize) -> Self::Coefficient {
        assert!(self.degree() >= i, "Index out of bounds");
        self.coeffs[i].clone()
    }

    fn set_coefficient(&mut self, i: usize, value: Self::Coefficient) {
        assert!(self.degree() >= i, "Index out of bounds");
        self.coeffs[i] = value;
        self.normalize();
    }

    // This evaluates a polynomial (in coefficient form) at `x`.
    fn evaluate(&self, x: &Self::Coefficient) -> Self::Coefficient {
        let coeffs = self.coeffs.clone();
        let poly_size = self.coeffs.len();

        // p(x) = = a_0 + a_1 * X + ... + a_n * X^(n-1), revert it and fold sum it
        fn eval<R: Ring>(poly: &[R], point: &R) -> R {
            poly.iter()
                .rev()
                .fold(R::one(), |acc, coeff| acc * point + coeff)
        }

        let num_threads = current_num_threads();
        if poly_size * 2 < num_threads {
            eval(&coeffs, x)
        } else {
            let chunk_size = (poly_size + num_threads - 1) / num_threads;
            let mut parts = vec![R::one(); num_threads];
            scope(|scope| {
                for (chunk_idx, (out, c)) in parts
                    .chunks_mut(1)
                    .zip(coeffs.chunks(chunk_size))
                    .enumerate()
                {
                    scope.spawn(move |_| {
                        let start = chunk_idx * chunk_size;
                        out[0] = eval(c, x) * x.pow(start as u64);
                    });
                }
            });
            parts.iter().fold(R::one(), |acc, coeff| acc + coeff)
        }
    }

    fn from_coefficients(coeffs: Vec<Self::Coefficient>) -> Self {
        Self::new(coeffs)
    }

    fn coefficients(&self) -> Vec<Self::Coefficient> {
        self.coeffs.clone()
    }

    fn negate(&self) -> Self {
        let negated_coeffs = self.coeffs.iter().map(|c| -c.clone()).collect();
        Self::new(negated_coeffs)
    }

    fn derivative(&self) -> Self {
        if self.is_zero() || self.degree() == 0 {
            return Self::zero();
        }

        let mut derivative_coeffs = Vec::with_capacity(self.degree());
        for (i, coeff) in self.coeffs.iter().enumerate().skip(1) {
            let new_coeff = coeff.clone() * R::from(i as u64);
            derivative_coeffs.push(new_coeff);
        }

        Self::from_coefficients(derivative_coeffs)
    }

    fn is_zero(&self) -> bool {
        self.coeffs.is_empty() || self.coeffs.iter().all(|c| c == &R::zero())
    }

    fn divide_with_q_and_r(&self, divisor: &Self) -> Option<(Self, Self)> {
        if self.is_zero() {
            Some((Self::zero(), Self::zero()))
        } else if divisor.is_zero() {
            panic!("Dividing by zero polynomial")
        } else if self.degree() < divisor.degree() {
            Some((Self::zero(), self.clone().into()))
        } else {
            // Now we know that self.degree() >= divisor.degree();
            let mut quotient = vec![R::zero(); self.degree() - divisor.degree() + 1];
            let mut remainder = self.clone();

            // Can unwrap here because we know self is not zero.
            let divisor_last = divisor.coeffs.last().unwrap();
            while !remainder.is_zero() && remainder.degree() >= divisor.degree() {
                let cur_q_coeff = remainder.coeffs.last().unwrap().clone() * divisor_last;
                let cur_q_degree = remainder.degree() - divisor.degree();
                quotient[cur_q_degree] = cur_q_coeff.clone();

                for (i, div_coeff) in divisor.coefficients().iter().enumerate() {
                    remainder.coeffs[cur_q_degree + i] -= cur_q_coeff.clone() * div_coeff;
                }
                while let Some(true) = remainder.coefficients().last().map(|c| c == &R::zero()) {
                    remainder.coeffs.pop();
                }
            }
            Some((Self::from_coefficients(quotient), remainder))
        }
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

impl<R: Ring> std::ops::Mul for UniPolynomial<R> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let mut coeffs: Vec<R> = vec![R::zero(); self.coeffs.len() + rhs.coeffs.len() - 1];
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
        let mut coeffs: Vec<R> = vec![R::zero(); self.coeffs.len() + rhs.coeffs.len() - 1];
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
            let a = self.coeffs.get(i).cloned().unwrap_or_else(R::zero);
            let b = rhs.coeffs.get(i).cloned().unwrap_or_else(R::zero);
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
            let a = self.coeffs.get(i).cloned().unwrap_or_else(R::zero);
            let b = rhs.coeffs.get(i).cloned().unwrap_or_else(R::zero);
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
        if self.coeffs.is_empty() || (self.coeffs.len() == 1 && self.coeffs[0] == R::zero()) {
            return write!(f, "0");
        }

        let mut first = true;
        for (i, coeff) in self.coeffs.iter().enumerate().rev() {
            if *coeff != R::zero() {
                if !first {
                    write!(f, " + ")?;
                }
                first = false;

                match i {
                    0 => write!(f, "{}", coeff)?,
                    1 => {
                        if *coeff == R::one() {
                            write!(f, "x")?
                        } else {
                            write!(f, "{}x", coeff)?
                        }
                    }
                    _ => {
                        if *coeff == R::one() {
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
    use crate::ring::zq::Zq;
    use std::ops::Neg;
    #[test]
    fn test_ring_polynomial_display() {
        let poly =
            UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(0), Zq::new(2), Zq::new(1)]);
        // assert_eq!(poly.to_string(), "x^3 + 2x^2 + 3");
        println!("poly: {:?}", poly.to_string());
        let zero_poly = UniPolynomial::<Zq>::zero();
        // assert_eq!(zero_poly.to_string(), "0");
        println!("zero_poly: {:?}", zero_poly.to_string());

        let linear_poly = UniPolynomial::from_coefficients(vec![Zq::new(2), Zq::new(1)]);
        // assert_eq!(linear_poly.to_string(), "1x + 2");
        println!("linear_poly: {:?}", linear_poly.to_string());
    }

    #[test]
    fn test_poly_addition() {
        let p1 = UniPolynomial::<Zq>::from_coefficients(
            vec![3, 2, 1].into_iter().map(Zq::from).collect(),
        ); // x^2 + 2x + 3
        let p2 = UniPolynomial::<Zq>::from_coefficients(
            vec![6, 5, 4].into_iter().map(Zq::from).collect(),
        ); // x^2 + 5x + 6
        let result = p1 + p2;
        assert_eq!(result.coeffs, vec![Zq::new(9), Zq::new(7), Zq::new(5)]);
    }

    #[test]
    fn test_poly_subtraction() {
        let p1 = UniPolynomial::<Zq>::from_coefficients(
            vec![6, 5, 4].into_iter().map(Zq::from).collect(),
        ); // x^2 + 5x + 6
        let p2 = UniPolynomial::<Zq>::from_coefficients(
            vec![3, 2, 1].into_iter().map(Zq::from).collect(),
        ); // x^2 + 2x + 3
        let result = p1 - p2;
        assert_eq!(result.coeffs, vec![Zq::new(3); 3]);

        //     s_tranpose_dot_u: "2x^3 + 7x^2 + 8x + 3"
        // ciphter_text.v:
        // "11x^3 + 7x^2 + x + 13"
        let p3 = UniPolynomial::<Zq>::from_coefficients(
            vec![13, 1, 7, 11].into_iter().map(Zq::from).collect(),
        );

        // 2x^3 + 7x^2 + 8x + 3
        let p4 = UniPolynomial::<Zq>::from_coefficients(
            vec![3, 8, 7, 2].into_iter().map(Zq::from).collect(),
        );

        let result = p3 - p4;
        println!("result: {:?}", result.to_string());
        assert_eq!(result.coeffs, vec![
            Zq::new(10),
            Zq::new(7).neg(),
            Zq::zero(),
            Zq::new(9)
        ]);
    }

    #[test]
    fn test_poly_multiplication() {
        let p1 =
            UniPolynomial::<Zq>::from_coefficients(vec![1, 2].into_iter().map(Zq::from).collect()); // 2x + 1
        let p2 =
            UniPolynomial::<Zq>::from_coefficients(vec![3, 4].into_iter().map(Zq::from).collect()); // 4x + 3
        // (2x + 1)*(4x+ 3)
        let result = p1 * p2;
        assert_eq!(result.coeffs, vec![Zq::new(3), Zq::new(10), Zq::new(8)]);
    }

    #[test]
    fn test_poly_scalar_multiplication() {
        let p = UniPolynomial::<Zq>::from_coefficients(
            vec![1, 2, 3].into_iter().map(Zq::from).collect(),
        ); // x^2 + 2x + 3
        let q = Zq::new(2);
        let result = p.scalar_mul(&q);
        assert_eq!(result.coeffs, vec![Zq::new(2), Zq::new(4), Zq::new(6)]);
    }

    #[test]
    fn test_derivative() {
        // Test polynomial: 3x^3 + 2x^2 + x + 5
        let poly =
            UniPolynomial::from_coefficients(vec![Zq::new(5), Zq::new(1), Zq::new(2), Zq::new(3)]);

        // Expected derivative: 9x^2 + 4x + 1
        let expected_derivative =
            UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(4), Zq::new(9)]);

        assert_eq!(poly.derivative(), expected_derivative);

        // Test constant polynomial
        let constant_poly = UniPolynomial::from_coefficients(vec![Zq::new(42)]);
        assert_eq!(constant_poly.derivative(), UniPolynomial::zero());

        // Test zero polynomial
        let zero_poly = UniPolynomial::<Zq>::zero();
        assert_eq!(zero_poly.derivative(), UniPolynomial::zero());
    }
    #[test]
    fn test_negate() {
        // Test polynomial: 3x^2 + 2x + 1
        let poly = UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(2), Zq::new(3)]);

        // Expected negation: -3x^2 - 2x - 1
        let expected_negation =
            UniPolynomial::from_coefficients(vec![-Zq::new(1), -Zq::new(2), -Zq::new(3)]);

        assert_eq!(poly.negate(), expected_negation);

        // Test zero polynomial
        let zero_poly = UniPolynomial::<Zq>::zero();
        assert_eq!(zero_poly.negate(), zero_poly);

        // Test negation of negation
        assert_eq!(poly.negate().negate(), poly);
    }
    #[test]
    fn test_poly_div_rem() {
        // Define polynomials
        let p1 = UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(2), Zq::new(1)]); // x^2 + 2x + 1
        let p2 = UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(1)]); // x + 1

        // Perform division: (x^2 + 2x + 1)/(x + 1)
        let (quotient, remainder) = p1.clone().divide_with_q_and_r(&p2).unwrap();

        // Check quotient
        assert_eq!(quotient.coefficients(), vec![Zq::new(1), Zq::new(1)]); // x + 1

        // Check remainder
        assert!(remainder.is_zero()); // 0

        // Test division by higher degree polynomial
        let p3 = UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(1), Zq::new(1)]); // x^2 + x + 1
        //  (x^2 + 2x + 1)/(x^2 + x + 1)
        let (quotient, remainder) = p1.divide_with_q_and_r(&p3).unwrap();

        // Check remainder is the same as the dividend
        assert_eq!(remainder.coefficients(), vec![Zq::new(0), Zq::new(1)]);
        assert_eq!(quotient.coefficients(), vec![Zq::new(1)]);

        // (x^2 + x + 1)/(x^2 + 2x + 1)
        let (quotient, remainder) = p3.divide_with_q_and_r(&p1).unwrap();
        // Check remainder is the same as the dividend
        // assert_eq!(remainder.coefficients(), vec![Zq::new(2), Zq::new(2)]);
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
                let dividend = UniPolynomial::<Zq>::rand(rng, a_degree);
                let divisor = UniPolynomial::<Zq>::rand(rng, b_degree);
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
        let dividend = UniPolynomial::<Zq>::rand(rng, a_degree);
        let divisor = UniPolynomial::<Zq>::rand(rng, b_degree);
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
        // p = 1 - x
        let p = UniPolynomial {
            coeffs: vec![Zq::one(), Zq::one().neg()],
        };
        // q = 1 + x
        let q = UniPolynomial {
            coeffs: vec![Zq::one(), Zq::one()],
        };

        assert_eq!(p.clone().mul(&q).coeffs, vec![
            Zq::one(),
            Zq::zero(),
            Zq::one().neg()
        ]);

        // add
        assert_eq!(p.clone().add(&q).coeffs, vec![Zq::new(2)]);

        // poly.mul(Zq)
        assert_eq!(p.scalar_mul(&Zq::new(5)).coeffs, vec![
            Zq::new(5),
            Zq::new(5).neg()
        ]);
    }
}
