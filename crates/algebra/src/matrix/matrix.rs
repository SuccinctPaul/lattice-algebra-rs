//! Optimized Matrix Implementation
//!
//! This module provides a high-performance matrix implementation with:
//! - Contiguous memory layout (row-major) for cache efficiency
//! - Cache-friendly loop ordering (ikj pattern)
//! - Optional parallel operations via `parallel` feature
//!
//! # Features
//! - `parallel`: Enables parallel matrix operations using Rayon

use crate::ring::poly_ring::PolyRing;
use crate::ring::MatrixElement;
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fmt::{Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

/// A matrix over a ring R
pub type RingMatrix<R> = GenericMatrix<R>;

/// A matrix over a ring R
pub type PolynomialMatrix<R> = GenericMatrix<R>;

/// A matrix over a polynomial ring R[x]/(x^d+1)
pub type PolyRingMatrix<R, const DEGREE_BOUND: usize> = GenericMatrix<PolyRing<R, DEGREE_BOUND>>;

/// Threshold for parallel operations (row count)
#[cfg(feature = "parallel")]
const PARALLEL_THRESHOLD: usize = 32;

/// A generic matrix implementation with contiguous memory layout.
///
/// Uses row-major storage for cache efficiency.
/// When compiled with `parallel` feature, operations automatically
/// use parallel algorithms for large matrices.
///
/// # Memory Layout
/// Data is stored in a single contiguous `Vec<T>` in row-major order:
/// `data[i * cols + j]` accesses element at row `i`, column `j`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct GenericMatrix<T: MatrixElement> {
    #[serde(bound(serialize = "T: Serialize", deserialize = "T: Deserialize<'de>"))]
    pub rows: usize,
    #[serde(bound(serialize = "T: Serialize", deserialize = "T: Deserialize<'de>"))]
    pub cols: usize,
    /// Contiguous row-major storage
    #[serde(bound(serialize = "T: Serialize", deserialize = "T: Deserialize<'de>"))]
    data: Vec<T>,
}

impl<T: MatrixElement> GenericMatrix<T> {
    /// Computes the linear index for row-major storage.
    #[inline(always)]
    fn index(&self, row: usize, col: usize) -> usize {
        row * self.cols + col
    }

    /// Creates a new matrix with the given dimensions, initialized to zero.
    pub fn new(rows: usize, cols: usize) -> Self {
        Self {
            rows,
            cols,
            data: vec![T::zero(); rows * cols],
        }
    }

    /// Creates a random matrix with the given dimensions.
    pub fn random(rng: &mut impl rand::RngCore, rows: usize, cols: usize) -> Self {
        Self {
            rows,
            cols,
            data: (0..rows * cols).map(|_| T::random(rng)).collect(),
        }
    }

    /// Creates an identity matrix of the given size.
    pub fn identity(size: usize) -> Self {
        let mut matrix = Self::new(size, size);
        for i in 0..size {
            matrix.data[i * size + i] = T::one();
        }
        matrix
    }

    /// Returns the number of rows.
    #[inline]
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Returns the number of columns.
    #[inline]
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// Gets the element at the specified position.
    #[inline]
    pub fn get(&self, row: usize, col: usize) -> Option<&T> {
        if row < self.rows && col < self.cols {
            Some(&self.data[self.index(row, col)])
        } else {
            None
        }
    }

    /// Gets a mutable reference to the element at the specified position.
    #[inline]
    pub fn get_mut(&mut self, row: usize, col: usize) -> Option<&mut T> {
        if row < self.rows && col < self.cols {
            let idx = self.index(row, col);
            Some(&mut self.data[idx])
        } else {
            None
        }
    }

    /// Sets the element at the specified position.
    pub fn set(&mut self, row: usize, col: usize, value: T) -> Result<(), &'static str> {
        if row >= self.rows || col >= self.cols {
            return Err("Index out of bounds");
        }
        let idx = self.index(row, col);
        self.data[idx] = value;
        Ok(())
    }

    /// Returns a column vector.
    pub fn get_column(&self, col: usize) -> Vec<T> {
        assert!(col < self.cols, "Column index out of bounds");
        (0..self.rows)
            .map(|row| self.data[self.index(row, col)].clone())
            .collect()
    }

    /// Returns a row vector.
    pub fn get_row(&self, row: usize) -> Vec<T> {
        assert!(row < self.rows, "Row index out of bounds");
        let start = self.index(row, 0);
        self.data[start..start + self.cols].to_vec()
    }

    /// Computes the transpose of the matrix.
    pub fn transpose(&self) -> Self {
        let mut transposed = Self::new(self.cols, self.rows);
        for i in 0..self.rows {
            for j in 0..self.cols {
                transposed.data[j * self.rows + i] = self.data[self.index(i, j)].clone();
            }
        }
        transposed
    }

    /// Concatenates two matrices horizontally.
    pub fn concat_horizontal(&self, other: &Self) -> Self {
        assert_eq!(
            self.rows, other.rows,
            "Matrices must have same number of rows"
        );

        let new_cols = self.cols + other.cols;
        let mut data = vec![T::zero(); self.rows * new_cols];

        for i in 0..self.rows {
            for j in 0..self.cols {
                data[i * new_cols + j] = self.data[self.index(i, j)].clone();
            }
            for j in 0..other.cols {
                data[i * new_cols + self.cols + j] = other.data[other.index(i, j)].clone();
            }
        }

        Self {
            rows: self.rows,
            cols: new_cols,
            data,
        }
    }

    /// Concatenates two matrices vertically.
    pub fn concat_vertical(&self, other: &Self) -> Self {
        assert_eq!(
            self.cols, other.cols,
            "Matrices must have same number of columns"
        );

        let mut data = Vec::with_capacity((self.rows + other.rows) * self.cols);
        data.extend(self.data.iter().cloned());
        data.extend(other.data.iter().cloned());

        Self {
            rows: self.rows + other.rows,
            cols: self.cols,
            data,
        }
    }
}

// ============================================================================
// Sequential Implementation (default, no feature required)
// ============================================================================

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> GenericMatrix<T> {
    /// Multiplies the matrix by a scalar.
    pub fn scalar_mul(&self, scalar: T) -> Self {
        Self {
            rows: self.rows,
            cols: self.cols,
            data: self
                .data
                .iter()
                .map(|x| x.clone() * scalar.clone())
                .collect(),
        }
    }

    /// Computes the matrix multiplication.
    ///
    /// Uses cache-friendly ikj loop ordering.
    ///
    /// # Complexity
    /// O(n³) for n×n matrices
    pub fn matrix_mul(&self, other: &Self) -> Self {
        assert_eq!(
            self.cols, other.rows,
            "Matrix dimensions must be compatible"
        );

        let mut result = Self::new(self.rows, other.cols);

        // ikj loop ordering for better cache performance
        for i in 0..self.rows {
            for k in 0..self.cols {
                let a_ik = self.data[self.index(i, k)].clone();
                for j in 0..other.cols {
                    let idx = i * other.cols + j;
                    result.data[idx] = result.data[idx].clone()
                        + a_ik.clone() * other.data[k * other.cols + j].clone();
                }
            }
        }
        result
    }

    /// Computes the matrix-vector multiplication.
    pub fn vector_mul(&self, vector: &[T]) -> Vec<T> {
        assert_eq!(
            self.cols,
            vector.len(),
            "Vector length must match matrix columns"
        );

        (0..self.rows)
            .map(|i| {
                let row_start = i * self.cols;
                (0..self.cols)
                    .map(|j| self.data[row_start + j].clone() * vector[j].clone())
                    .fold(T::zero(), |acc, x| acc + x)
            })
            .collect()
    }
}

// ============================================================================
// Parallel Implementation (requires `parallel` feature)
// ============================================================================

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> GenericMatrix<T> {
    /// Multiplies the matrix by a scalar.
    ///
    /// Automatically uses parallel computation for large matrices.
    pub fn scalar_mul(&self, scalar: T) -> Self {
        if self.rows * self.cols >= PARALLEL_THRESHOLD * PARALLEL_THRESHOLD {
            Self {
                rows: self.rows,
                cols: self.cols,
                data: self
                    .data
                    .par_iter()
                    .map(|x| x.clone() * scalar.clone())
                    .collect(),
            }
        } else {
            Self {
                rows: self.rows,
                cols: self.cols,
                data: self
                    .data
                    .iter()
                    .map(|x| x.clone() * scalar.clone())
                    .collect(),
            }
        }
    }

    /// Computes the matrix multiplication.
    ///
    /// Automatically uses parallel computation for large matrices (rows >= 32).
    ///
    /// # Complexity
    /// O(n³) for n×n matrices, parallelized across rows
    pub fn matrix_mul(&self, other: &Self) -> Self {
        assert_eq!(
            self.cols, other.rows,
            "Matrix dimensions must be compatible"
        );

        if self.rows >= PARALLEL_THRESHOLD {
            // Parallel version
            let result_cols = other.cols;
            let self_cols = self.cols;

            let data: Vec<T> = (0..self.rows)
                .into_par_iter()
                .flat_map(|i| {
                    let mut row_result = vec![T::zero(); result_cols];

                    for k in 0..self_cols {
                        let a_ik = self.data[i * self_cols + k].clone();
                        for j in 0..result_cols {
                            row_result[j] = row_result[j].clone()
                                + a_ik.clone() * other.data[k * result_cols + j].clone();
                        }
                    }
                    row_result
                })
                .collect();

            Self {
                rows: self.rows,
                cols: result_cols,
                data,
            }
        } else {
            // Sequential version for small matrices
            let mut result = Self::new(self.rows, other.cols);

            for i in 0..self.rows {
                for k in 0..self.cols {
                    let a_ik = self.data[self.index(i, k)].clone();
                    for j in 0..other.cols {
                        let idx = i * other.cols + j;
                        result.data[idx] = result.data[idx].clone()
                            + a_ik.clone() * other.data[k * other.cols + j].clone();
                    }
                }
            }
            result
        }
    }

    /// Computes the matrix-vector multiplication.
    ///
    /// Automatically uses parallel computation for large matrices.
    pub fn vector_mul(&self, vector: &[T]) -> Vec<T> {
        assert_eq!(
            self.cols,
            vector.len(),
            "Vector length must match matrix columns"
        );

        if self.rows >= PARALLEL_THRESHOLD {
            (0..self.rows)
                .into_par_iter()
                .map(|i| {
                    let row_start = i * self.cols;
                    (0..self.cols)
                        .map(|j| self.data[row_start + j].clone() * vector[j].clone())
                        .fold(T::zero(), |acc, x| acc + x)
                })
                .collect()
        } else {
            (0..self.rows)
                .map(|i| {
                    let row_start = i * self.cols;
                    (0..self.cols)
                        .map(|j| self.data[row_start + j].clone() * vector[j].clone())
                        .fold(T::zero(), |acc, x| acc + x)
                })
                .collect()
        }
    }
}

// ============================================================================
// Arithmetic Operations
// ============================================================================

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> Add for GenericMatrix<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        Self {
            rows: self.rows,
            cols: self.cols,
            data: self
                .data
                .iter()
                .zip(other.data.iter())
                .map(|(a, b)| a.clone() + b.clone())
                .collect(),
        }
    }
}

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> Add for GenericMatrix<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        let data = if self.data.len() >= PARALLEL_THRESHOLD * PARALLEL_THRESHOLD {
            self.data
                .par_iter()
                .zip(other.data.par_iter())
                .map(|(a, b)| a.clone() + b.clone())
                .collect()
        } else {
            self.data
                .iter()
                .zip(other.data.iter())
                .map(|(a, b)| a.clone() + b.clone())
                .collect()
        };

        Self {
            rows: self.rows,
            cols: self.cols,
            data,
        }
    }
}

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> Sub for GenericMatrix<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        Self {
            rows: self.rows,
            cols: self.cols,
            data: self
                .data
                .iter()
                .zip(other.data.iter())
                .map(|(a, b)| a.clone() - b.clone())
                .collect(),
        }
    }
}

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> Sub for GenericMatrix<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        let data = if self.data.len() >= PARALLEL_THRESHOLD * PARALLEL_THRESHOLD {
            self.data
                .par_iter()
                .zip(other.data.par_iter())
                .map(|(a, b)| a.clone() - b.clone())
                .collect()
        } else {
            self.data
                .iter()
                .zip(other.data.iter())
                .map(|(a, b)| a.clone() - b.clone())
                .collect()
        };

        Self {
            rows: self.rows,
            cols: self.cols,
            data,
        }
    }
}

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> Mul for GenericMatrix<T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        self.matrix_mul(&other)
    }
}

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> Mul for GenericMatrix<T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        self.matrix_mul(&other)
    }
}

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> AddAssign for GenericMatrix<T> {
    fn add_assign(&mut self, other: Self) {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        for (a, b) in self.data.iter_mut().zip(other.data.iter()) {
            *a = a.clone() + b.clone();
        }
    }
}

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> AddAssign for GenericMatrix<T> {
    fn add_assign(&mut self, other: Self) {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        if self.data.len() >= PARALLEL_THRESHOLD * PARALLEL_THRESHOLD {
            self.data
                .par_iter_mut()
                .zip(other.data.par_iter())
                .for_each(|(a, b)| *a = a.clone() + b.clone());
        } else {
            for (a, b) in self.data.iter_mut().zip(other.data.iter()) {
                *a = a.clone() + b.clone();
            }
        }
    }
}

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> SubAssign for GenericMatrix<T> {
    fn sub_assign(&mut self, other: Self) {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        for (a, b) in self.data.iter_mut().zip(other.data.iter()) {
            *a = a.clone() - b.clone();
        }
    }
}

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> SubAssign for GenericMatrix<T> {
    fn sub_assign(&mut self, other: Self) {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        if self.data.len() >= PARALLEL_THRESHOLD * PARALLEL_THRESHOLD {
            self.data
                .par_iter_mut()
                .zip(other.data.par_iter())
                .for_each(|(a, b)| *a = a.clone() - b.clone());
        } else {
            for (a, b) in self.data.iter_mut().zip(other.data.iter()) {
                *a = a.clone() - b.clone();
            }
        }
    }
}

#[cfg(not(feature = "parallel"))]
impl<T: MatrixElement> MulAssign for GenericMatrix<T> {
    fn mul_assign(&mut self, other: Self) {
        *self = self.clone() * other;
    }
}

#[cfg(feature = "parallel")]
impl<T: MatrixElement + Send + Sync> MulAssign for GenericMatrix<T> {
    fn mul_assign(&mut self, other: Self) {
        *self = self.clone() * other;
    }
}

impl<T: MatrixElement> Display for GenericMatrix<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Matrix ({}x{}):", self.rows, self.cols)?;
        for i in 0..self.rows {
            write!(f, "[")?;
            for j in 0..self.cols {
                if j > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", self.data[i * self.cols + j])?;
            }
            writeln!(f, "]")?;
        }
        Ok(())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod poly_matrix_tests {
    use crate::matrix_tests;
    use crate::poly::UniPolynomial;
    use crate::ring::Zq17;

    matrix_tests!(UniPolynomial<Zq17>, rand::rng());
}

#[cfg(test)]
mod ring_matrix_tests {
    use crate::matrix_tests;
    use crate::ring::Zq17;

    matrix_tests!(Zq17, rand::rng());
}

#[cfg(test)]
mod poly_ring_matrix_tests {
    use super::*;
    use crate::ring::PolynomialQuotientRing;
    use crate::ring::Zq17;
    use crate::{matrix_tests, polynomial_matrix_tests};

    matrix_tests!(PolyRing<Zq17, 4>, rand::rng());
    polynomial_matrix_tests!(PolyRing<Zq17, 4>, rand::rng());
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::Zq17;

    #[test]
    fn test_serialization() {
        let mut matrix = GenericMatrix::<Zq17>::new(2, 2);
        matrix.set(0, 0, Zq17::new(1)).unwrap();
        matrix.set(0, 1, Zq17::new(2)).unwrap();
        matrix.set(1, 0, Zq17::new(3)).unwrap();
        matrix.set(1, 1, Zq17::new(4)).unwrap();

        let serialized = serde_json::to_string(&matrix).unwrap();
        let deserialized: GenericMatrix<Zq17> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(matrix, deserialized);
    }

    #[test]
    fn test_serialization_zero_matrix() {
        let matrix = GenericMatrix::<Zq17>::new(3, 3);

        let serialized = serde_json::to_string(&matrix).unwrap();
        let deserialized: GenericMatrix<Zq17> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(matrix, deserialized);
    }

    #[test]
    fn test_serialization_random_matrix() {
        let mut rng = rand::rng();
        let matrix = GenericMatrix::<Zq17>::random(&mut rng, 4, 4);

        let serialized = serde_json::to_string(&matrix).unwrap();
        let deserialized: GenericMatrix<Zq17> = serde_json::from_str(&serialized).unwrap();

        assert_eq!(matrix, deserialized);
    }
}
