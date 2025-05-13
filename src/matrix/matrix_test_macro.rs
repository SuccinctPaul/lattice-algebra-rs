use crate::matrix::matrix::GenericMatrix;
use crate::ring::MatrixElement;
use crate::ring::PolynomialQuotientRing;
use rand::RngCore;

/// Macro to generate matrix tests for any type implementing MatrixElement
#[macro_export]
macro_rules! matrix_tests {
    ($type:ty, $rng:expr) => {
        #[cfg(test)]
        mod tests {
            use super::*;
            use crate::matrix::matrix::GenericMatrix;
            use crate::ring::MatrixElement;
            use rand::RngCore;

            #[test]
            fn test_matrix_creation() {
                let matrix = GenericMatrix::<$type>::new(2, 3);
                assert_eq!(matrix.rows(), 2);
                assert_eq!(matrix.cols(), 3);
                assert!(matrix.get(0, 0).unwrap() == &<$type>::zero());
            }

            #[test]
            fn test_matrix_identity() {
                let matrix = GenericMatrix::<$type>::identity(3);
                assert_eq!(matrix.rows(), 3);
                assert_eq!(matrix.cols(), 3);
                assert!(matrix.get(0, 0).unwrap() == &<$type>::one());
                assert!(matrix.get(0, 1).unwrap() == &<$type>::zero());
            }

            #[test]
            fn test_matrix_arithmetic() {
                let mut rng = $rng;
                let a = GenericMatrix::<$type>::random(&mut rng, 2, 2);
                let b = GenericMatrix::<$type>::random(&mut rng, 2, 2);

                // Test addition
                let sum = a.clone() + b.clone();
                assert_eq!(sum.rows(), 2);
                assert_eq!(sum.cols(), 2);

                // Test subtraction
                let diff = a.clone() - b.clone();
                assert_eq!(diff.rows(), 2);
                assert_eq!(diff.cols(), 2);

                // Test multiplication
                let prod = a * b;
                assert_eq!(prod.rows(), 2);
                assert_eq!(prod.cols(), 2);
            }

            #[test]
            fn test_matrix_vector_mul() {
                let mut rng = $rng;
                let matrix = GenericMatrix::<$type>::random(&mut rng, 2, 3);
                let vector = vec![<$type>::random(&mut rng); 3];

                let result = matrix.vector_mul(&vector);
                assert_eq!(result.len(), 2);
            }

            #[test]
            fn test_matrix_concat() {
                let mut rng = $rng;
                let a = GenericMatrix::<$type>::random(&mut rng, 2, 2);
                let b = GenericMatrix::<$type>::random(&mut rng, 2, 2);

                // Test horizontal concatenation
                let h_concat = a.clone().concat_horizontal(&b);
                assert_eq!(h_concat.rows(), 2);
                assert_eq!(h_concat.cols(), 4);

                // Test vertical concatenation
                let v_concat = a.concat_vertical(&b);
                assert_eq!(v_concat.rows(), 4);
                assert_eq!(v_concat.cols(), 2);
            }

            #[test]
            fn test_matrix_transpose() {
                let mut rng = $rng;
                let matrix = GenericMatrix::<$type>::random(&mut rng, 3, 2);
                let transposed = matrix.transpose();

                assert_eq!(transposed.rows(), 2);
                assert_eq!(transposed.cols(), 3);

                // Verify transpose properties
                for i in 0..matrix.rows() {
                    for j in 0..matrix.cols() {
                        assert_eq!(matrix.get(i, j).unwrap(), transposed.get(j, i).unwrap());
                    }
                }
            }

            #[test]
            fn test_matrix_scalar_mul() {
                let mut rng = $rng;
                let matrix = GenericMatrix::<$type>::random(&mut rng, 2, 2);
                let scalar = <$type>::random(&mut rng);

                let result = matrix.scalar_mul(scalar.clone());
                assert_eq!(result.rows(), matrix.rows());
                assert_eq!(result.cols(), matrix.cols());

                // Verify each element is multiplied by scalar
                for i in 0..matrix.rows() {
                    for j in 0..matrix.cols() {
                        assert_eq!(
                            result.get(i, j).unwrap(),
                            &(matrix.get(i, j).unwrap().clone() * scalar.clone())
                        );
                    }
                }
            }

            #[test]
            fn test_matrix_zero() {
                let matrix = GenericMatrix::<$type>::new(2, 2);
                for i in 0..2 {
                    for j in 0..2 {
                        assert_eq!(matrix.get(i, j).unwrap(), &<$type>::zero());
                    }
                }
            }

            #[test]
            fn test_matrix_identity_mul() {
                let mut rng = $rng;
                let matrix = GenericMatrix::<$type>::random(&mut rng, 2, 2);
                let identity = GenericMatrix::<$type>::identity(2);

                let result = matrix.clone() * identity;
                assert_eq!(result, matrix);
            }
        }
    };
}

/// Macro to generate additional polynomial-specific matrix tests
#[macro_export]
macro_rules! polynomial_matrix_tests {
    ($type:ty, $rng:expr) => {
        #[cfg(test)]
        mod polynomial_tests {
            use super::*;
            use crate::matrix::matrix::GenericMatrix;
            use crate::ring::MatrixElement;
            use rand::RngCore;

            #[test]
            fn test_polynomial_matrix_mul() {
                let mut rng = $rng;
                let a = GenericMatrix::<$type>::random(&mut rng, 2, 2);
                let b = GenericMatrix::<$type>::random(&mut rng, 2, 2);

                // Test polynomial multiplication
                let prod = a.clone() * b.clone();
                assert_eq!(prod.rows(), 2);
                assert_eq!(prod.cols(), 2);

                // Verify polynomial properties
                for i in 0..prod.rows() {
                    for j in 0..prod.cols() {
                        let element = prod.get(i, j).unwrap();
                        assert!(element.degree() <= <$type>::modulus().degree());
                    }
                }
            }

            #[test]
            fn test_polynomial_matrix_vector_mul() {
                let mut rng = $rng;
                let matrix = GenericMatrix::<$type>::random(&mut rng, 2, 2);
                let vector = vec![<$type>::random(&mut rng); 2];

                let result = matrix.vector_mul(&vector);
                assert_eq!(result.len(), 2);

                // Verify polynomial properties of result
                for element in result {
                    assert!(element.degree() <= <$type>::modulus().degree());
                }
            }
        }
    };
}
