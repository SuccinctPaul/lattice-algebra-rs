use crate::matrix::Matrix;
use crate::matrix::vector_arithmatic::VectorArithmatic;
use crate::poly::Polynomial;
use crate::poly::uni_poly::UniPolynomial;
use crate::ring::Ring;
use std::fmt;
use std::fmt::{Display, Formatter};
use std::ops::{Add, AddAssign, Div, Mul, Sub};

/// This defined `matrix` (rows * cols) （m × n）
#[derive(Debug, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct PolyMatrix<P: Polynomial> {
    pub rows: usize,
    pub cols: usize,
    pub values: Vec<Vec<P>>,
}

impl<P: Polynomial> PolyMatrix<P> {
    pub fn rand(
        rng: &mut impl rand::RngCore,
        rows: usize,
        cols: usize,
        poly_degree: usize,
    ) -> Self {
        let values = (0..rows)
            .map(|_| {
                (0..cols)
                    .map(|_| P::rand(rng, poly_degree))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        Self { cols, rows, values }
    }

    pub fn get_columns(&self, column_index: usize) -> Vec<P> {
        assert!(self.cols > column_index, "Column index out of bounds");

        self.values
            .iter()
            .map(|v| v.get(column_index).unwrap().clone())
            .collect::<Vec<_>>()
    }

    // pub fn from_vector(vector: Vec<P>) -> Self {
    //     for x in &vector {
    //         println!("from_vector.raw:  {}", x.to_string());
    //     }
    //
    //     let res = Self {
    //         rows: 1,
    //         cols: vector.len(),
    //         values: vec![vector],
    //     };
    //     for i in 0..res.rows {
    //         for j in 0..res.cols {
    //             let value = res.get(i, j).unwrap_or(&P::zero()).clone();
    //             println!("from_vector.res: {i},{j}: {}", value);
    //         }
    //     }
    //     res
    // }

    pub fn from_row_vector(vector: Vec<P>) -> Self {
        let res = Self {
            rows: 1,
            cols: vector.len(),
            values: vec![vector],
        };
        res
    }
    pub fn from_col_vector(vector: Vec<P>) -> Self {
        let mut matrix = Self::new(vector.len(), 1);

        for (row, v) in vector.into_iter().enumerate() {
            matrix.set(row, 0, v);
        }
        matrix
    }

    pub fn vec_dot_mul(a: &Vec<P>, b: &Vec<P>) -> P {
        assert_eq!(a.len(), b.len(), "Vectors must have the same length");

        let mut poly = a
            .iter()
            .zip(b.iter())
            .map(|(ai, bi)| ai.clone() * bi.clone())
            .fold(P::zero(), |acc, x| acc + x);
        poly.normalize();
        poly
    }
    // Add between two vectors.
    pub fn vec_add(a: &Vec<P>, b: &Vec<P>) -> Vec<P> {
        assert_eq!(a.len(), b.len(), "Vectors must have the same length");

        a.iter()
            .zip(b.iter())
            .map(|(ai, bi)| ai.clone() + bi.clone())
            .collect::<Vec<_>>()
    }
    // Add between two vectors.
    pub fn vec_sub(a: &Vec<P>, b: &Vec<P>) -> Vec<P> {
        assert_eq!(a.len(), b.len(), "Vectors must have the same length");

        a.iter()
            .zip(b.iter())
            .map(|(ai, bi)| ai.clone() - bi.clone())
            .collect::<Vec<_>>()
    }

    // Mul between two vectors.
    // It's a special case of matrix mul.
    pub fn vec_mul(a: &Vec<P>, b: &Vec<P>) -> Vec<P> {
        assert_eq!(a.len(), b.len(), "Vectors must have the same length");

        a.iter()
            .zip(b.iter())
            .map(|(ai, bi)| ai.clone() * bi.clone())
            .collect::<Vec<_>>()
    }

    // /// https://en.wikipedia.org/wiki/Dot_product
    // /// Suppose A(m * n), x(n) => A * x = y(m)
    // pub fn mul_vector(&self, vector: &Vec<P>) -> Vec<P> {
    //     let vec_matrix = Self::from_vector(vector, &self.values);
    //     // assert_eq!(
    //     //     self.cols,
    //     //     vector.len(),
    //     //     "Matrix columns must match vector length"
    //     // );
    //
    //     // self.values
    //     //     .iter()
    //     //     .map(|row| Self::vec_dot_mul(row, vector))
    //     //     .collect()
    // }

    /// https://en.wikipedia.org/wiki/Dot_product
    /// Suppose A(m * n), B(n, p) => A * B = C(m * p)
    pub fn mul_matrix(&self, m_b: &Self) -> Self {
        assert!(self.cols > 0 && m_b.rows > 0, "Matrices cannot be empty");
        assert_eq!(
            self.cols, m_b.rows,
            "Matrix dimensions must be compatible for multiplication"
        );

        let m = self.rows;
        let p = m_b.cols;

        let m_b_columns: Vec<Vec<P>> = (0..p).map(|j| m_b.get_columns(j)).collect();

        let matrix: Vec<Vec<P>> = (0..m)
            .map(|i| {
                let row_i = &self.values[i];
                (0..p)
                    .map(|j| Self::vec_dot_mul(row_i, &m_b_columns[j]))
                    .collect()
            })
            .collect();

        Self {
            rows: m,
            cols: p,
            values: matrix,
        }
    }
}

impl<P: Polynomial> Matrix<P> for PolyMatrix<P> {
    fn new(rows: usize, cols: usize) -> Self {
        Self {
            rows,
            cols,
            values: vec![vec![P::zero(); cols]; rows],
        }
    }

    fn rows(&self) -> usize {
        self.rows
    }

    fn cols(&self) -> usize {
        self.cols
    }

    fn get(&self, row: usize, col: usize) -> Option<&P> {
        assert!(row < self.rows, "row out of bounds");
        assert!(col < self.cols, "row out of bounds");
        self.values.get(row).and_then(|row| row.get(col))
    }

    fn set(&mut self, row: usize, col: usize, value: P) -> Result<(), &'static str> {
        assert!(row < self.rows, "row out of bounds");
        assert!(col < self.cols, "row out of bounds");
        self.values[row][col] = value;
        Ok(())
    }

    fn transpose(&self) -> Self {
        let mut transposed = Self::new(self.cols, self.rows);

        for i in 0..self.rows {
            for j in 0..self.cols {
                let value = self.get(i, j).unwrap_or(&P::zero()).clone();
                transposed.set(j, i, value).unwrap();
            }
        }
        transposed
    }

    fn identity(size: usize) -> Self {
        todo!()
    }

    fn scalar_mul(&self, scalar: P) -> Self {
        todo!()
    }

    fn determinant(&self) -> Option<P> {
        todo!()
    }

    fn inverse(&self) -> Option<Self> {
        todo!()
    }
}
impl<P: Polynomial> Add for PolyMatrix<P> {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        assert_eq!(
            self.cols, rhs.cols,
            "Matrix rows and cols are not the same length"
        );
        assert_eq!(
            self.rows, rhs.rows,
            "Matrix rows and cols are not the same length"
        );

        let values = self
            .values
            .into_iter()
            .zip(rhs.values.into_iter())
            .map(|(l_row, r_row)| {
                l_row
                    .into_iter()
                    .zip(r_row.into_iter())
                    .map(|(l, r)| l + r)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        Self {
            rows: self.rows,
            cols: self.cols,
            values,
        }
    }
}

impl<P: Polynomial> Sub for PolyMatrix<P> {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        assert_eq!(
            self.cols, rhs.cols,
            "Matrix rows and cols are not the same length"
        );
        assert_eq!(
            self.rows, rhs.rows,
            "Matrix rows and cols are not the same length"
        );

        let values = self
            .values
            .into_iter()
            .zip(rhs.values.into_iter())
            .map(|(l_row, r_row)| {
                l_row
                    .into_iter()
                    .zip(r_row.into_iter())
                    .map(|(l, r)| l - r)
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        Self {
            rows: self.rows,
            cols: self.cols,
            values,
        }
    }
}

impl<P: Polynomial> Mul for PolyMatrix<P> {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        self.mul_matrix(&rhs)
    }
}

impl<P: Polynomial> Display for PolyMatrix<P> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if self.cols == 0 || self.rows == 0 {
            return write!(f, "Empty");
        }
        println!("===================================");
        println!("Matrix: rows={}, cols={}", self.rows, self.cols);
        for (i, row) in self.values.iter().enumerate() {
            print!("|");

            for value in row.iter() {
                print!(" {},", value.to_string());
            }

            println!("|");
        }
        println!("===================================");

        Ok(())
    }
}
#[cfg(test)]
mod test {
    use crate::matrix::Matrix;
    use crate::matrix::poly_matrix::PolyMatrix;
    use crate::poly::Polynomial;
    use crate::poly::uni_poly::UniPolynomial;
    use crate::ring::Ring;
    use crate::ring::zq::Zq;
    use std::ops::{Mul, Neg};

    #[test]
    fn test_ring_matrix_new() {
        let matrix = PolyMatrix::<UniPolynomial<Zq>>::new(3, 4);
        println!("{:?}", matrix);
        println!("{:?}", matrix.to_string());
    }

    #[test]
    pub fn test_matrix_vec_dot_mul() {
        let poly_1 = UniPolynomial::from_coefficients(vec![Zq::one(), Zq::one(), Zq::one()]);
        let vec1 = vec![UniPolynomial::zero(), poly_1.clone()];
        let vec2 = vec![poly_1.clone(), UniPolynomial::zero()];
        assert_eq!(
            PolyMatrix::<UniPolynomial<Zq>>::vec_dot_mul(&vec1, &vec2),
            UniPolynomial::zero()
        );

        // [x+1, x-1]
        let vec3 = vec![
            UniPolynomial::from_coefficients(vec![Zq::one(), Zq::one()]),
            UniPolynomial::from_coefficients(vec![Zq::one().neg(), Zq::one()]),
        ];
        // [3x+1, x+3]
        let mut vec4 = vec![
            UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
            UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(1)]),
        ];
        assert_eq!(
            PolyMatrix::<UniPolynomial<Zq>>::vec_dot_mul(&vec3, &vec4),
            // -2 + 6x + 4x^2
            UniPolynomial::from_coefficients(vec![Zq::new(2).neg(), Zq::new(6), Zq::new(4)])
        );
    }

    #[test]
    pub fn test_matrix_transpose() {
        let m = 2;
        let matrix = PolyMatrix::<UniPolynomial<Zq>> {
            rows: m,
            cols: m,
            values: vec![
                vec![
                    UniPolynomial::zero(),
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
                ],
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::one(), Zq::new(2)]),
                    UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(4)]),
                ],
            ],
        };
        println!("{:?}", matrix.to_string());

        let transposed: PolyMatrix<UniPolynomial<Zq>> = matrix.transpose();
        let expect = PolyMatrix::<UniPolynomial<Zq>> {
            rows: m,
            cols: m,
            values: vec![
                vec![
                    UniPolynomial::zero(),
                    UniPolynomial::from_coefficients(vec![Zq::one(), Zq::new(2)]),
                ],
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
                    UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(4)]),
                ],
            ],
        };

        assert_eq!(transposed, expect);

        let recovered: PolyMatrix<UniPolynomial<Zq>> = transposed.transpose();
        assert_eq!(recovered, matrix);
    }

    #[test]
    fn test_matrix_add_and_sub() {
        let cols = 3;
        let rows = 4;
        let degree = 4;
        let rng = &mut rand::thread_rng();
        let lhs = PolyMatrix::<UniPolynomial<Zq>>::rand(rng, rows, cols, degree);
        let rhs = PolyMatrix::<UniPolynomial<Zq>>::rand(rng, rows, cols, degree);

        let sum = lhs.clone() + rhs.clone();

        let expect_lhs = sum.clone() - rhs.clone();
        assert_eq!(expect_lhs, lhs);
        let expect_rhs = sum.clone() - lhs.clone();
        assert_eq!(expect_rhs, rhs);
        let expect_sum = expect_lhs.clone() + expect_rhs.clone();
        assert_eq!(expect_sum, sum);
        let expect_zero = sum - rhs - lhs;
        assert_eq!(expect_zero, Matrix::new(rows, cols));
    }

    #[test]
    fn test_from_vector_by_row_and_col() {
        // [3x+1, x+3]
        let rhs = vec![
            UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
            UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(1)]),
        ];

        let p1 = PolyMatrix::from_col_vector(rhs.clone());
        let p2 = PolyMatrix::from_row_vector(rhs.clone());

        assert_eq!(p1, p2.transpose());
    }

    #[test]
    fn test_mul_vector() {
        let m = 2;
        let rng = &mut rand::thread_rng();
        let lhs = PolyMatrix {
            rows: m,
            cols: m,
            values: vec![
                // [x+1, x-1]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::one(), Zq::one()]),
                    UniPolynomial::from_coefficients(vec![Zq::one().neg(), Zq::one()]),
                ],
                // [x+1, x-2]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::one(), Zq::one()]),
                    UniPolynomial::from_coefficients(vec![Zq::new(2).neg(), Zq::one()]),
                ],
            ],
        };
        // [3x+1, x+3]
        let rhs = vec![
            UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
            UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(1)]),
        ];

        let expect = vec![
            // -2 + 6x + 4x^2
            UniPolynomial::from_coefficients(vec![Zq::new(2).neg(), Zq::new(6), Zq::new(4)]),
            // (4x^2 + 5x - 5)
            UniPolynomial::from_coefficients(vec![Zq::new(5).neg(), Zq::new(5), Zq::new(4)]),
        ];

        let rhs = PolyMatrix::from_col_vector(rhs);
        let res = lhs.mul(rhs);
        assert_eq!(PolyMatrix::from_col_vector(expect), res);
    }

    #[test]
    fn test_mul_matrix() {
        let m: usize = 2;
        let lhs = PolyMatrix {
            rows: m,
            cols: m,
            values: vec![
                // [x+1, x-1]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::one(), Zq::one()]),
                    UniPolynomial::from_coefficients(vec![Zq::one().neg(), Zq::one()]),
                ],
                // [x+1, x-2]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::one(), Zq::one()]),
                    UniPolynomial::from_coefficients(vec![Zq::new(2).neg(), Zq::one()]),
                ],
            ],
        };
        let rhs = PolyMatrix {
            rows: m,
            cols: m,
            values: vec![
                // [3x+1, x+3]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
                    UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(1)]),
                ],
                // [3x+1, x+1]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(1)]),
                ],
            ],
        };

        let expect = PolyMatrix {
            rows: m,
            cols: m,
            values: vec![
                // [2x + 6x^2, 2 + 4x + 2x^2]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::new(0), Zq::new(2), Zq::new(6)]),
                    UniPolynomial::from_coefficients(vec![Zq::new(2), Zq::new(4), Zq::new(2)]),
                ],
                // [-1 - x + 6x^2, 1 + 3x + 2x^2]
                vec![
                    UniPolynomial::from_coefficients(vec![
                        Zq::new(1).neg(),
                        Zq::new(1).neg(),
                        Zq::new(6),
                    ]),
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3), Zq::new(2)]),
                ],
            ],
        };
        let res = lhs.mul_matrix(&rhs);
        assert_eq!(expect, res);
    }

    #[test]
    fn test_matrix_scalar_mul_and_matrix_mul() {
        let m = 2;
        let mut rng = rand::thread_rng();

        let lhs = PolyMatrix {
            rows: m,
            cols: m,
            values: vec![
                // [x+1, x-1]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::one(), Zq::one()]),
                    UniPolynomial::from_coefficients(vec![Zq::one().neg(), Zq::one()]),
                ],
                // [x+1, x-2]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::one(), Zq::one()]),
                    UniPolynomial::from_coefficients(vec![Zq::new(2).neg(), Zq::one()]),
                ],
            ],
        };
        let rhs = PolyMatrix {
            rows: m,
            cols: m,
            values: vec![
                // [3x+1, x+3]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
                    UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(1)]),
                ],
                // [3x+1, x+1]
                vec![
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
                    UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(1)]),
                ],
            ],
        };
        // [3x+1, x+3]
        let x = vec![
            UniPolynomial::from_coefficients(vec![Zq::new(1), Zq::new(3)]),
            UniPolynomial::from_coefficients(vec![Zq::new(3), Zq::new(1)]),
        ];
        let x = PolyMatrix::from_col_vector(x);

        // A*B*x
        let res1 = PolyMatrix::<UniPolynomial<Zq>>::mul_matrix(&lhs, &rhs).mul(x.clone());
        // A*(B*x)
        let res2 = lhs.mul(rhs.mul(x));
        assert_eq!(res1, res2);
    }
}
