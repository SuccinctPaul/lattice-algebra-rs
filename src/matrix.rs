//! https://matrixcalc.org/ helps a lot.
// pub mod poly_matrix;
pub mod poly_ring_matrix;
pub mod ring_matrix;
pub mod vector_arithmatic;

use std::ops::{Add, Mul, Sub};

// By HORIZONTAL(extend cols): col added, rows fixed
// By VERTICAL(extend rows): col fixed, rows fixed
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub enum MatrixScalarType {
    HORIZONTAL,
    VERTICAL,
}

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

    /// Concat of columns of matrixs,(aka scalar matrix)
    /// 1. scalar VERTICAL, only extend rows.
    /// eg:
    ///     Matrix A is m*k, Matrix B is n*k, then concat(A, B) is (m+n)*k
    ///
    /// 2. scalar HORIZONTAL, only extent cols
    /// eg:
    ///     Matrix A is k*m, Matrix B is k*n, then concat(A, B) is k*(m+n)
    fn concat(&self, other: &Self, scalar_type: MatrixScalarType) -> Self;

    // fn from_vector(vector: Vec<T>, by_column_or_row: MatrixType) -> Self {
    //     match by_column_or_row {
    //         MatrixType::COLUMN => Self::from_col_vector(vector),
    //         MatrixType::ROW => Self::from_col_vector(vector),
    //     }
    // }

    // The vector will be a 1*n column matrix. Aka column vector.
    fn from_col_vector(vector: Vec<T>) -> Self {
        let mut matrix = Self::new(vector.len(), 1);

        for (row, v) in vector.into_iter().enumerate() {
            matrix.set(row, 0, v);
        }
        matrix
    }

    // fn from_col_rows(vector: Vec<T>) -> Self;
}
