use crate::poly::UniPolynomial;
use crate::ring::MatrixElement;
use crate::ring::zq::Zq;
use crate::ring::{PolynomialQuotientRing, Ring};
use rand::RngCore;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::iter::Sum;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

/// Polynomial Ring: R=Z_q[x]/(x^d+1), D mean the module poly2's degree
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct PolyRing<R: Ring, const DEGREE_BOUND: u64> {
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
        Self::new(self.inner + &rhs.inner)
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
