use crate::poly::UniPolynomial;
use crate::ring::MatrixElement;
use crate::ring::{PolynomialQuotientRing, Ring};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

/// A polynomial ring R[x]/(x^d+1) where R is a base ring and d is the degree bound
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd, Serialize, Deserialize)]
pub struct PolyRing<R: Ring, const DEGREE_BOUND: u64> {
    #[serde(bound(serialize = "R: Serialize", deserialize = "R: Deserialize<'de>"))]
    pub inner: UniPolynomial<R>,
}

impl<R: Ring, const DEGREE_BOUND: u64> PolyRing<R, DEGREE_BOUND> {
    pub fn new(poly: UniPolynomial<R>) -> Self {
        let inner = poly % Self::modulus();
        Self { inner }
    }
}

impl<R: Ring, const DEGREE_BOUND: u64> PolynomialQuotientRing for PolyRing<R, DEGREE_BOUND> {
    type PolyCoeff = R;

    // Idea Lattice:
    //      f=x^n + 1 , defines anticyclic lattices.
    //      f=x^n - 1 , defines cyclic lattices.
    //
    // Reference: [2.2 Lattices](https://publi.math.unideb.hu/load_doc.php?p=1637&t=pap)
    fn modulus() -> UniPolynomial<Self::PolyCoeff> {
        let coeffs = if DEGREE_BOUND == 0 {
            vec![R::from(2)]
        } else {
            let mut coeffs = vec![R::ZERO; DEGREE_BOUND as usize + 1];
            coeffs[0] = R::ONE;
            coeffs[DEGREE_BOUND as usize] = R::ONE;
            coeffs
        };
        UniPolynomial::from_coefficients(coeffs)
    }

    fn normalize(&mut self) {
        self.inner.normalize();
    }

    fn rand(rng: &mut impl RngCore, degree: usize) -> Self {
        Self::new(UniPolynomial::rand(rng, degree))
    }

    fn rand_with_bound_degree(rng: &mut impl RngCore) -> Self {
        Self::rand(rng, DEGREE_BOUND as usize)
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

impl<R: Ring, const DEGREE_BOUND: u64> Add for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.inner + rhs.inner)
    }
}

impl<R: Ring, const DEGREE_BOUND: u64> AddAssign for PolyRing<R, DEGREE_BOUND> {
    fn add_assign(&mut self, rhs: Self) {
        self.inner += rhs.inner
    }
}

impl<'a, R: Ring, const DEGREE_BOUND: u64> Add<&'a Self> for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self::Output {
        Self::new(self.inner + &rhs.inner)
    }
}

impl<R: Ring, const DEGREE_BOUND: u64> Mul for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let product = self.inner.clone() * rhs.inner;
        let module_one = product % Self::modulus();
        Self::new(module_one)
    }
}

impl<'a, R: Ring, const DEGREE_BOUND: u64> Mul<&'a Self> for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self::Output {
        let product = self.inner.clone() * &rhs.inner;
        let module_one = product % Self::modulus();
        Self::new(module_one)
    }
}

impl<R: Ring, const DEGREE_BOUND: u64> MulAssign for PolyRing<R, DEGREE_BOUND> {
    fn mul_assign(&mut self, rhs: Self) {
        let product = self.inner.clone() * &rhs.inner;
        let module_one = product % Self::modulus();
        self.inner = module_one;
    }
}

impl<R: Ring, const DEGREE_BOUND: u64> Sub for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.inner - rhs.inner)
    }
}

impl<'a, R: Ring, const DEGREE_BOUND: u64> Sub<&'a Self> for PolyRing<R, DEGREE_BOUND> {
    type Output = Self;

    fn sub(self, rhs: &'a Self) -> Self::Output {
        Self::new(self.inner - &rhs.inner)
    }
}

impl<R: Ring, const DEGREE_BOUND: u64> SubAssign for PolyRing<R, DEGREE_BOUND> {
    fn sub_assign(&mut self, rhs: Self) {
        self.inner -= rhs.inner
    }
}

impl<R: Ring, const DEGREE_BOUND: u64> Display for PolyRing<R, DEGREE_BOUND> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.coefficients().is_empty()
            || (self.coefficients().len() == 1 && self.coefficients()[0] == R::ZERO)
        {
            return write!(f, "0");
        }

        let mut first = true;
        for (i, coeff) in self.coefficients().iter().enumerate().rev() {
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

impl<R: Ring, const DEGREE_BOUND: u64> MatrixElement for PolyRing<R, DEGREE_BOUND> {
    fn zero() -> Self {
        Self::new(UniPolynomial::zero())
    }

    fn one() -> Self {
        Self::from_coefficients(vec![R::ONE])
    }

    fn random(rng: &mut impl RngCore) -> Self {
        Self::rand_with_bound_degree(rng)
    }
}

impl<R: Ring, const DEGREE_BOUND: u64> Sum for PolyRing<R, DEGREE_BOUND> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), Self::add)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::Zq17;
    use serde_json;

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
    fn test_multiplication() {
        let a = create_test_poly::<Zq17>(vec![1, 2]);
        let b = create_test_poly::<Zq17>(vec![3, 4]);
        let product = a * b;
        // (1 + 2x)(3 + 4x) = 3 + 10x + 8x^2
        // In Zq17[x]/(x^4 + 1), this becomes 3 + 10x + 8x^2
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
    fn test_multiplication_with_modulus() {
        let a = create_test_poly::<Zq17>(vec![1, 2, 3, 4]);
        let b = create_test_poly::<Zq17>(vec![1, 0, 0, 0]);
        let product = a * b;
        // (1 + 2x + 3x^2 + 4x^3)(1) = 1 + 2x + 3x^2 + 4x^3
        assert_eq!(
            product.coefficients(),
            vec![Zq17::new(1), Zq17::new(2), Zq17::new(3), Zq17::new(4)]
        );
    }

    #[test]
    fn test_random() {
        let mut rng = rand::rng();
        let poly = PolyRing::<Zq17, 4>::random(&mut rng);
        if poly.is_zero() {
            println!("poly_is zero: ");
            assert_eq!(poly.degree(), 0);
        } else {
            assert!(poly.degree() <= 3); // Should be degree 3 for DEGREE_BOUND = 4
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
    fn test_set_coefficient() {
        let mut poly =
            PolyRing::<Zq17, 4>::from_coefficients(vec![Zq17::new(5), Zq17::new(2), Zq17::new(2)]);
        println!("poly degree: {:?}", poly.degree());
        poly.set_coefficient(0, Zq17::ZERO);
        poly.set_coefficient(1, Zq17::ZERO);
        poly.set_coefficient(2, Zq17::new(5));
        assert_eq!(
            poly.coefficients(),
            vec![Zq17::ZERO, Zq17::ZERO, Zq17::new(5)]
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
    fn test_serialization_zero() {
        let poly = PolyRing::<Zq17, 4>::zero();

        let serialized = serde_json::to_string(&poly).unwrap();
        let deserialized: PolyRing<Zq17, 4> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(poly, deserialized);
    }

    #[test]
    fn test_serialization_random() {
        let mut rng = rand::rng();
        let poly = PolyRing::<Zq17, 4>::random(&mut rng);

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
