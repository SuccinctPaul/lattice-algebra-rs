use crate::ring::poly_ring::PolyRing;
use crate::ring::MatrixElement;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};

/// A matrix over a ring R
pub type RingMatrix<R> = GenericMatrix<R>;

/// A matrix over a ring R
pub type PolynomialMatrix<R> = GenericMatrix<R>;

/// A matrix over a polynomial ring R[x]/(x^d+1)
pub type PolyRingMatrix<R, const DEGREE_BOUND: u64> = GenericMatrix<PolyRing<R, DEGREE_BOUND>>;

/// A generic matrix implementation that can work with any type implementing MatrixElement
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericMatrix<T: MatrixElement> {
    pub rows: usize,
    pub cols: usize,
    pub data: Vec<Vec<T>>,
}

impl<T: MatrixElement> GenericMatrix<T> {
    /// Creates a new matrix with the given dimensions
    pub fn new(rows: usize, cols: usize) -> Self {
        Self {
            rows,
            cols,
            data: vec![vec![T::zero(); cols]; rows],
        }
    }

    /// Creates a random matrix with the given dimensions
    pub fn random(rng: &mut impl rand::RngCore, rows: usize, cols: usize) -> Self {
        Self {
            rows,
            cols,
            data: (0..rows)
                .map(|_| (0..cols).map(|_| T::random(rng)).collect())
                .collect(),
        }
    }

    /// Creates an identity matrix of the given size
    pub fn identity(size: usize) -> Self {
        let mut matrix = Self::new(size, size);
        for i in 0..size {
            matrix.data[i][i] = T::one();
        }
        matrix
    }

    /// Returns the number of rows
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// Returns the number of columns
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// Gets the element at the specified position
    pub fn get(&self, row: usize, col: usize) -> Option<&T> {
        self.data.get(row)?.get(col)
    }

    /// Sets the element at the specified position
    pub fn set(&mut self, row: usize, col: usize, value: T) -> Result<(), &'static str> {
        if row >= self.rows || col >= self.cols {
            return Err("Index out of bounds");
        }
        self.data[row][col] = value;
        Ok(())
    }

    /// Returns a column vector
    pub fn get_column(&self, col: usize) -> Vec<T> {
        assert!(col < self.cols, "Column index out of bounds");
        self.data.iter().map(|row| row[col].clone()).collect()
    }

    /// Returns a row vector
    pub fn get_row(&self, row: usize) -> Vec<T> {
        assert!(row < self.rows, "Row index out of bounds");
        self.data[row].clone()
    }

    /// Computes the transpose of the matrix
    pub fn transpose(&self) -> Self {
        let mut transposed = Self::new(self.cols, self.rows);
        for i in 0..self.rows {
            for j in 0..self.cols {
                transposed.data[j][i] = self.data[i][j].clone();
            }
        }
        transposed
    }

    /// Multiplies the matrix by a scalar
    pub fn scalar_mul(&self, scalar: T) -> Self {
        let mut result = Self::new(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.data[i][j] = self.data[i][j].clone() * scalar.clone();
            }
        }
        result
    }

    /// Computes the matrix multiplication
    pub fn matrix_mul(&self, other: &Self) -> Self {
        assert_eq!(
            self.cols, other.rows,
            "Matrix dimensions must be compatible"
        );

        let mut result = Self::new(self.rows, other.cols);
        for i in 0..self.rows {
            for j in 0..other.cols {
                let mut sum = T::zero();
                for k in 0..self.cols {
                    sum = sum + self.data[i][k].clone() * other.data[k][j].clone();
                }
                result.data[i][j] = sum;
            }
        }
        result
    }

    /// Computes the matrix-vector multiplication
    pub fn vector_mul(&self, vector: &[T]) -> Vec<T> {
        assert_eq!(
            self.cols,
            vector.len(),
            "Vector length must match matrix columns"
        );

        (0..self.rows)
            .map(|i| {
                (0..self.cols)
                    .map(|j| self.data[i][j].clone() * vector[j].clone())
                    .sum()
            })
            .collect()
    }

    /// Concatenates two matrices horizontally
    pub fn concat_horizontal(&self, other: &Self) -> Self {
        assert_eq!(
            self.rows, other.rows,
            "Matrices must have same number of rows"
        );

        let mut result = Self::new(self.rows, self.cols + other.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.data[i][j] = self.data[i][j].clone();
            }
            for j in 0..other.cols {
                result.data[i][self.cols + j] = other.data[i][j].clone();
            }
        }
        result
    }

    /// Concatenates two matrices vertically
    pub fn concat_vertical(&self, other: &Self) -> Self {
        assert_eq!(
            self.cols, other.cols,
            "Matrices must have same number of columns"
        );

        let mut result = Self::new(self.rows + other.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.data[i][j] = self.data[i][j].clone();
            }
        }
        for i in 0..other.rows {
            for j in 0..other.cols {
                result.data[self.rows + i][j] = other.data[i][j].clone();
            }
        }
        result
    }
}

// Implement arithmetic operations
impl<T: MatrixElement> Add for GenericMatrix<T> {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        let mut result = Self::new(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.data[i][j] = self.data[i][j].clone() + other.data[i][j].clone();
            }
        }
        result
    }
}

impl<T: MatrixElement> Sub for GenericMatrix<T> {
    type Output = Self;

    fn sub(self, other: Self) -> Self {
        assert_eq!(self.rows, other.rows, "Matrices must have same dimensions");
        assert_eq!(self.cols, other.cols, "Matrices must have same dimensions");

        let mut result = Self::new(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.data[i][j] = self.data[i][j].clone() - other.data[i][j].clone();
            }
        }
        result
    }
}

impl<T: MatrixElement> Mul for GenericMatrix<T> {
    type Output = Self;

    fn mul(self, other: Self) -> Self {
        self.matrix_mul(&other)
    }
}

// Implement assignment operations
impl<T: MatrixElement> AddAssign for GenericMatrix<T> {
    fn add_assign(&mut self, other: Self) {
        *self = self.clone() + other;
    }
}

impl<T: MatrixElement> SubAssign for GenericMatrix<T> {
    fn sub_assign(&mut self, other: Self) {
        *self = self.clone() - other;
    }
}

impl<T: MatrixElement> MulAssign for GenericMatrix<T> {
    fn mul_assign(&mut self, other: Self) {
        *self = self.clone() * other;
    }
}

// Implement Display trait
impl<T: MatrixElement> Display for GenericMatrix<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Matrix ({}x{}):", self.rows, self.cols)?;
        for row in &self.data {
            write!(f, "[")?;
            for (i, elem) in row.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", elem)?;
            }
            writeln!(f, "]")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod poly_matrix_tests {
    use super::*;
    use crate::poly::UniPolynomial;
    use crate::ring::Zq17;
    use crate::{matrix_tests, polynomial_matrix_tests};

    matrix_tests!(UniPolynomial<Zq17>, rand::rng());
}

#[cfg(test)]
mod ring_matrix_tests {
    use super::*;
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
