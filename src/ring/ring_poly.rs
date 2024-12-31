use crate::poly::Polynomial;
use crate::poly::uni_poly::UniPolynomial;
use crate::ring::{PolynomialRingTrait, Ring};
use rand::RngCore;
use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

// Z_q[x]/(x^n+1), N mean the module poly's degree
#[derive(Debug, Clone, Eq, PartialEq, Ord, PartialOrd)]
pub struct RingPolynomial<P: Polynomial, const DEGREE_BOUND: u64> {
    pub inner: P,
}
impl<P: Polynomial, const DEGREE_BOUND: u64> RingPolynomial<P, DEGREE_BOUND> {
    pub fn new(poly: P) -> Self {
        let inner = poly % Self::modulus();
        Self { inner }
    }
}

impl<P: Polynomial, const DEGREE_BOUND: u64> PolynomialRingTrait
    for RingPolynomial<P, DEGREE_BOUND>
{
    type PolyType = P;
    type PolyCoeff = P::Coefficient;

    // x^n + 1
    fn modulus() -> Self::PolyType {
        let coeffs = if DEGREE_BOUND == 0 {
            vec![P::Coefficient::from(2)]
        } else {
            let mut coeffs = vec![P::Coefficient::zero(); DEGREE_BOUND as usize + 1];
            coeffs[0] = P::Coefficient::one();
            coeffs[DEGREE_BOUND as usize] = P::Coefficient::one();
            coeffs
        };
        P::from_coefficients(coeffs)
    }

    fn normalize(&mut self) {
        self.inner.normalize();
    }

    fn rand(rng: &mut impl RngCore, degree: usize) -> Self {
        Self::new(P::rand(rng, degree))
    }

    fn rand_with_bound_degree(rng: &mut impl RngCore) -> Self {
        Self::rand(rng, DEGREE_BOUND as usize)
    }

    // fn rand_with_bound_degree(rng: &mut impl RngCore) -> Self {
    //     Self::rand(rng, DEGREE_BOUND as usize)
    // }

    fn zero() -> Self {
        Self::new(P::zero())
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
        Self::new(P::from_coefficients(coeffs))
    }

    fn coefficients(&self) -> Vec<Self::PolyCoeff> {
        self.inner.coefficients()
    }

    fn is_zero(&self) -> bool {
        self.inner.is_zero()
    }
}

impl<P: Polynomial, const DEGREE_BOUND: u64> Add for RingPolynomial<P, DEGREE_BOUND> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.inner + rhs.inner)
    }
}

impl<P: Polynomial, const DEGREE_BOUND: u64> AddAssign for RingPolynomial<P, DEGREE_BOUND> {
    fn add_assign(&mut self, rhs: Self) {
        self.inner += rhs.inner
    }
}

impl<'a, P: Polynomial, const DEGREE_BOUND: u64> Add<&'a Self> for RingPolynomial<P, DEGREE_BOUND> {
    type Output = Self;

    fn add(self, rhs: &'a Self) -> Self::Output {
        Self::new(self.inner + &rhs.inner)
    }
}

impl<P: Polynomial, const DEGREE_BOUND: u64> Mul for RingPolynomial<P, DEGREE_BOUND> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let product = self.inner.clone() * rhs.inner;
        let module_one = product % Self::modulus();
        Self::new(module_one)
    }
}

impl<'a, P: Polynomial, const DEGREE_BOUND: u64> Mul<&'a Self> for RingPolynomial<P, DEGREE_BOUND> {
    type Output = Self;

    fn mul(self, rhs: &'a Self) -> Self::Output {
        let product = self.inner.clone() * &rhs.inner;
        let module_one = product % Self::modulus();
        Self::new(module_one)
    }
}

impl<P: Polynomial, const DEGREE_BOUND: u64> MulAssign for RingPolynomial<P, DEGREE_BOUND> {
    fn mul_assign(&mut self, rhs: Self) {
        let product = self.inner.clone() * &rhs.inner;
        let module_one = product % Self::modulus();
        self.inner = module_one;
    }
}

impl<P: Polynomial, const DEGREE_BOUND: u64> Sub for RingPolynomial<P, DEGREE_BOUND> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.inner - rhs.inner)
    }
}

impl<'a, P: Polynomial, const DEGREE_BOUND: u64> Sub<&'a Self> for RingPolynomial<P, DEGREE_BOUND> {
    type Output = Self;

    fn sub(self, rhs: &'a Self) -> Self::Output {
        Self::new(self.inner + &rhs.inner)
    }
}

impl<P: Polynomial, const DEGREE_BOUND: u64> SubAssign for RingPolynomial<P, DEGREE_BOUND> {
    fn sub_assign(&mut self, rhs: Self) {
        self.inner -= rhs.inner
    }
}

impl<P: Polynomial, const DEGREE_BOUND: u64> Display for RingPolynomial<P, DEGREE_BOUND> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.coefficients().is_empty()
            || (self.coefficients().len() == 1 && self.coefficients()[0] == P::Coefficient::zero())
        {
            return write!(f, "0");
        }

        let mut first = true;
        for (i, coeff) in self.coefficients().iter().enumerate().rev() {
            if *coeff != P::Coefficient::zero() {
                if !first {
                    write!(f, " + ")?;
                }
                first = false;

                match i {
                    0 => write!(f, "{}", coeff)?,
                    1 => {
                        if *coeff == P::Coefficient::one() {
                            write!(f, "x")?
                        } else {
                            write!(f, "{}x", coeff)?
                        }
                    }
                    _ => {
                        if *coeff == P::Coefficient::one() {
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
