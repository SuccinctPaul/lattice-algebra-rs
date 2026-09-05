//! Optimized Vector Implementation
//!
//! This module provides high-performance vector operations with:
//! - Optional parallel computation via `parallel` feature
//!
//! # Features
//! - `parallel`: Enables parallel vector operations using Rayon

use crate::ring::poly_ring::PolyRing;
use crate::ring::MatrixElement;
use serde::{Deserialize, Serialize};
use std::ops::{Add, Mul, Sub};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// A vector over a ring R
pub type RingVector<R> = GenericVector<R>;

/// A vector over a polynomial ring R[x]/(x^d+1)
pub type PolyRingVector<R, const DEGREE_BOUND: usize> = GenericVector<PolyRing<R, DEGREE_BOUND>>;

/// Threshold for parallel vector operations
#[cfg(feature = "parallel")]
const PARALLEL_THRESHOLD: usize = 256;

/// A generic vector type that supports arithmetic operations
/// for any type implementing MatrixElement trait.
///
/// When compiled with `parallel` feature, operations automatically
/// use parallel algorithms for large vectors.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GenericVector<T: MatrixElement> {
    #[serde(bound(serialize = "T: Serialize", deserialize = "T: Deserialize<'de>"))]
    elements: Vec<T>,
}

impl<T: MatrixElement> GenericVector<T> {
    /// Creates a new vector with the given elements.
    pub fn new(elements: Vec<T>) -> Self {
        Self { elements }
    }

    /// Creates a zero vector of the given length.
    pub fn zero(length: usize) -> Self {
        Self {
            elements: vec![T::zero(); length],
        }
    }

    /// Creates a random vector of the given length.
    pub fn random(rng: &mut impl rand::RngCore, length: usize) -> Self {
        Self {
            elements: (0..length).map(|_| T::random(rng)).collect(),
        }
    }

    /// Returns the length of the vector.
    #[inline]
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Returns true if the vector is empty.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Returns a reference to the element at the given index.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.elements.get(index)
    }

    /// Returns a mutable reference to the element at the given index.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.elements.get_mut(index)
    }

    /// Returns an iterator over the vector elements.
    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, T> {
        self.elements.iter()
    }

    /// Returns a mutable iterator over the vector elements.
    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, T> {
        self.elements.iter_mut()
    }

    /// Returns the inner vector of elements.
    pub fn into_inner(self) -> Vec<T> {
        self.elements
    }

    /// Returns a reference to the inner vector of elements.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.elements
    }

    /// Returns a mutable reference to the inner vector of elements.
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.elements
    }
}

// ============================================================================
// Sequential Implementation (default, no feature required)
// ============================================================================

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> GenericVector<T> {
    /// Computes the inner product (dot product) with another vector.
    pub fn inner_product(&self, other: &Self) -> T {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");
        self.iter()
            .zip(other.iter())
            .map(|(a, b)| a.clone() * b.clone())
            .fold(T::zero(), |acc, x| acc + x)
    }

    /// Computes the Hadamard product (element-wise multiplication) with another vector.
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

    /// Multiplies the vector by a scalar.
    pub fn scalar_mul(&self, scalar: T) -> Self {
        Self {
            elements: self.iter().map(|x| x.clone() * scalar.clone()).collect(),
        }
    }
}

// ============================================================================
// Parallel Implementation (requires `parallel` feature)
// ============================================================================

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> GenericVector<T> {
    /// Computes the inner product (dot product) with another vector.
    ///
    /// Automatically uses parallel computation for large vectors.
    pub fn inner_product(&self, other: &Self) -> T {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");

        if self.len() >= PARALLEL_THRESHOLD {
            self.elements
                .par_iter()
                .zip(other.elements.par_iter())
                .map(|(a, b)| a.clone() * b.clone())
                .reduce(T::zero, |acc, x| acc + x)
        } else {
            self.iter()
                .zip(other.iter())
                .map(|(a, b)| a.clone() * b.clone())
                .fold(T::zero(), |acc, x| acc + x)
        }
    }

    /// Computes the Hadamard product (element-wise multiplication) with another vector.
    ///
    /// Automatically uses parallel computation for large vectors.
    pub fn hadamard_product(&self, other: &Self) -> Self {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");

        if self.len() >= PARALLEL_THRESHOLD {
            Self {
                elements: self
                    .elements
                    .par_iter()
                    .zip(other.elements.par_iter())
                    .map(|(a, b)| a.clone() * b.clone())
                    .collect(),
            }
        } else {
            Self {
                elements: self
                    .iter()
                    .zip(other.iter())
                    .map(|(a, b)| a.clone() * b.clone())
                    .collect(),
            }
        }
    }

    /// Multiplies the vector by a scalar.
    ///
    /// Automatically uses parallel computation for large vectors.
    pub fn scalar_mul(&self, scalar: T) -> Self {
        if self.len() >= PARALLEL_THRESHOLD {
            Self {
                elements: self
                    .elements
                    .par_iter()
                    .map(|x| x.clone() * scalar.clone())
                    .collect(),
            }
        } else {
            Self {
                elements: self.iter().map(|x| x.clone() * scalar.clone()).collect(),
            }
        }
    }
}

// ============================================================================
// Arithmetic Operations
// ============================================================================

#[cfg(not(feature = "parallel"))]
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

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> Add for GenericVector<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");

        let elements = if self.len() >= PARALLEL_THRESHOLD {
            self.elements
                .par_iter()
                .zip(other.elements.par_iter())
                .map(|(a, b)| a.clone() + b.clone())
                .collect()
        } else {
            self.iter()
                .zip(other.iter())
                .map(|(a, b)| a.clone() + b.clone())
                .collect()
        };

        Self { elements }
    }
}

#[cfg(not(feature = "parallel"))]
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

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> Sub for GenericVector<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.len(), other.len(), "Vectors must have the same length");

        let elements = if self.len() >= PARALLEL_THRESHOLD {
            self.elements
                .par_iter()
                .zip(other.elements.par_iter())
                .map(|(a, b)| a.clone() - b.clone())
                .collect()
        } else {
            self.iter()
                .zip(other.iter())
                .map(|(a, b)| a.clone() - b.clone())
                .collect()
        };

        Self { elements }
    }
}

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> Mul<T> for GenericVector<T> {
    type Output = Self;

    fn mul(self, scalar: T) -> Self::Output {
        self.scalar_mul(scalar)
    }
}

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> Mul<T> for GenericVector<T> {
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

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod ring_vector_tests {
    use crate::ring::Zq17;
    use crate::vector_tests;

    vector_tests!(Zq17, rand::rng());
}

#[cfg(test)]
mod poly_ring_vector_tests {
    use super::*;
    use crate::ring::Zq17;
    use crate::vector_tests;

    vector_tests!(PolyRing<Zq17, 4>, rand::rng());
}

#[cfg(test)]
mod poly_vector_tests {
    use crate::poly::UniPolynomial;
    use crate::ring::Zq17;
    use crate::vector_tests;

    vector_tests!(UniPolynomial<Zq17>, rand::rng());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::Zq17;

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
