//! https://matrixcalc.org/ helps a lot.
pub mod poly_matrix;
pub mod poly_ring_matrix;
pub mod ring_matrix;
pub mod vector_arithmatic;

use std::ops::{Add, Mul, Neg, Sub};

pub trait Matrix<T>: Sized + Clone + Add + Sub + Mul
where
    T: Clone + Add + Mul + Sub + PartialEq + Eq,
{
    /// Create a new matrix with the given number of rows and columns
    fn new(rows: usize, cols: usize) -> Self;

    /// Get the number of rows in the matrix
    fn rows(&self) -> usize;

    /// Get the number of columns in the matrix
    fn cols(&self) -> usize;

    /// Get the element at the specified row and column
    fn get(&self, row: usize, col: usize) -> Option<&T>;

    /// Set the element at the specified row and column
    fn set(&mut self, row: usize, col: usize, value: T) -> Result<(), &'static str>;

    /// Transpose the matrix
    fn transpose(&self) -> Self;

    /// Create an identity matrix of the given size
    ///
    /// Example:
    /// | 1 0 0 |
    /// | 0 1 0 |
    /// | 0 0 1 |
    fn identity(size: usize) -> Self;

    /// Multiply the matrix by a scalar
    ///
    /// Scalar multiplication involves multiplying every element of the matrix by a scalar value.
    fn scalar_mul(&self, scalar: T) -> Self;

    /// Calculate the determinant of the matrix (if square)
    fn determinant(&self) -> Option<T>;

    /// Invert the matrix (if possible)
    fn inverse(&self) -> Option<Self>;
}
