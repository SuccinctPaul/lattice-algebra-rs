use crate::ring::poly_ring::PolyRing;
use crate::ring::MatrixElement;
use serde::{Deserialize, Serialize};
use std::ops::{Add, Mul, Sub};

/// A matrix over a ring R
pub type RingVector<R> = GenericVector<R>;

/// A vector over a polynomial ring R[x]/(x^d+1)
pub type PolyRingVector<R, const DEGREE_BOUND: u64> = GenericVector<PolyRing<R, DEGREE_BOUND>>;

/// A generic vector type that supports arithmetic operations
/// for any type implementing MatrixElement trait
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GenericVector<T: MatrixElement> {
    #[serde(bound(serialize = "T: Serialize", deserialize = "T: Deserialize<'de>"))]
    elements: Vec<T>,
}

impl<T: MatrixElement> GenericVector<T> {
    /// Creates a new vector with the given elements
    pub fn new(elements: Vec<T>) -> Self {
        Self { elements }
    }

    /// Creates a zero vector of the given length
    pub fn zero(length: usize) -> Self {
        Self {
            elements: vec![T::zero(); length],
        }
    }

    /// Creates a random vector of the given length
    pub fn random(rng: &mut impl rand::RngCore, length: usize) -> Self {
        Self {
            elements: (0..length).map(|_| T::random(rng)).collect(),
        }
    }

    /// Returns the length of the vector
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Returns true if the vector is empty
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns a reference to the element at the given index
    pub fn get(&self, index: usize) -> Option<&T> {
        self.elements.get(index)
    }

    /// Returns a mutable reference to the element at the given index
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.elements.get_mut(index)
    }

    /// Returns an iterator over the vector elements
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.elements.iter()
    }

    /// Returns a mutable iterator over the vector elements
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.elements.iter_mut()
    }

    /// Returns the inner vector of elements
    pub fn into_inner(self) -> Vec<T> {
        self.elements
    }

    /// Returns a reference to the inner vector of elements
    pub fn as_slice(&self) -> &[T] {
        &self.elements
    }

    /// Returns a mutable reference to the inner vector of elements
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.elements
    }

    // /// Computes the Hamming weight of the vector (sum of absolute values)
    // pub fn hamming_weight(&self) -> u64 {
    //     self.elements.iter().fold(0, |acc, x| acc + x.abs())
    // }

    /// Computes the inner product (dot product) with another vector
    pub fn inner_product(&self, other: &Self) -> T {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");
        self.iter()
            .zip(other.iter())
            .map(|(a, b)| a.clone() * b.clone())
            .fold(T::zero(), |acc, x| acc + x)
    }

    /// Computes the Hadamard product (element-wise multiplication) with another vector
    pub fn hadamard_product(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");
        Self {
            elements: self
                .iter()
                .zip(other.iter())
                .map(|(a, b)| a.clone() * b.clone())
                .collect(),
        }
    }

    /// Multiplies the vector by a scalar
    pub fn scalar_mul(&self, scalar: T) -> Self {
        Self {
            elements: self.iter().map(|x| x.clone() * scalar.clone()).collect(),
        }
    }
}

impl<T: MatrixElement> Add for GenericVector<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");
        Self {
            elements: self
                .iter()
                .zip(other.iter())
                .map(|(a, b)| a.clone() + b.clone())
                .collect(),
        }
    }
}

impl<T: MatrixElement> Sub for GenericVector<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");
        Self {
            elements: self
                .iter()
                .zip(other.iter())
                .map(|(a, b)| a.clone() - b.clone())
                .collect(),
        }
    }
}

impl<T: MatrixElement> Mul<T> for GenericVector<T> {
    type Output = Self;

    fn mul(self, scalar: T) -> Self::Output {
        self.scalar_mul(scalar)
    }
}

impl<T: MatrixElement> From<Vec<T>> for GenericVector<T> {
    fn from(elements: Vec<T>) -> Self {
        Self::new(elements)
    }
}

#[cfg(test)]
mod ring_vector_tests {
    use crate::ring::Zq17;
    use crate::vector_tests;

    // Test RingVector with Zq17
    vector_tests!(Zq17, rand::rng());
}

#[cfg(test)]
mod poly_ring_vector_tests {
    use super::*;
    use crate::ring::Zq17;
    use crate::vector_tests;

    // Test PolyRingVector with Zq17 and degree bound 4
    vector_tests!(PolyRing<Zq17, 4>, rand::rng());
    // polynomial_vector_tests!(PolyRing<Zq17, 4>, rand::rng());
}

#[cfg(test)]
mod poly_vector_tests {
    use crate::poly::UniPolynomial;
    use crate::ring::Zq17;
    use crate::vector_tests;

    // Test PolynomialVector with Zq17
    vector_tests!(UniPolynomial<Zq17>, rand::rng());
    // polynomial_vector_tests!(UniPolynomial<Zq17>, rand::rng());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::Zq17;
    use serde_json;

    #[test]
    fn test_serialization() {
        let vector = GenericVector::new(vec![Zq17::new(1), Zq17::new(2), Zq17::new(3)]);

        let serialized = serde_json::to_string(&vector).unwrap();
        let deserialized: GenericVector<Zq17> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(vector, deserialized);
    }

    #[test]
    fn test_serialization_zero_vector() {
        let vector = GenericVector::<Zq17>::zero(3);

        let serialized = serde_json::to_string(&vector).unwrap();
        let deserialized: GenericVector<Zq17> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(vector, deserialized);
    }

    #[test]
    fn test_serialization_random_vector() {
        let mut rng = rand::rng();
        let vector = GenericVector::<Zq17>::random(&mut rng, 5);

        let serialized = serde_json::to_string(&vector).unwrap();
        let deserialized: GenericVector<Zq17> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(vector, deserialized);
    }
}
