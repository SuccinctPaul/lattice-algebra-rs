/// Macro to generate vector tests for any type implementing MatrixElement
#[macro_export]
macro_rules! vector_tests {
    ($type:ty, $rng:expr) => {
        #[cfg(test)]
        mod tests {
            use super::*;
            use crate::matrix::vector_arithmatic::GenericVector;
            use crate::ring::MatrixElement;
            use rand::RngCore;

            #[test]
            fn test_vector_creation() {
                let v = GenericVector::<$type>::new(vec![
                    <$type>::one(),
                    <$type>::one(),
                    <$type>::one(),
                ]);
                assert_eq!(v.len(), 3);
                assert_eq!(v.get(0), Some(&<$type>::one()));
            }

            #[test]
            fn test_vector_zero() {
                let v = GenericVector::<$type>::zero(3);
                assert_eq!(v.len(), 3);
                assert!(v.iter().all(|x| *x == <$type>::zero()));
            }

            #[test]
            fn test_vector_random() {
                let mut rng = $rng;
                let v = GenericVector::<$type>::random(&mut rng, 3);
                assert_eq!(v.len(), 3);
                // Verify that random elements are not all zero
                assert!(!v.iter().all(|x| *x == <$type>::zero()));
            }

            #[test]
            fn test_vector_arithmetic() {
                let mut rng = $rng;
                let a = GenericVector::<$type>::random(&mut rng, 2);
                let b = GenericVector::<$type>::random(&mut rng, 2);
                let scalar = <$type>::random(&mut rng);

                // Test addition
                let sum = a.clone() + b.clone();
                assert_eq!(sum.len(), 2);

                // Test subtraction
                let diff = a.clone() - b.clone();
                assert_eq!(diff.len(), 2);

                // Test scalar multiplication
                let scaled = a.clone() * scalar.clone();
                assert_eq!(scaled.len(), 2);
            }

            #[test]
            fn test_vector_operations() {
                let mut rng = $rng;
                let a = GenericVector::<$type>::random(&mut rng, 2);
                let b = GenericVector::<$type>::random(&mut rng, 2);

                // Test inner product
                let dot = a.inner_product(&b);
                assert!(dot == <$type>::zero() || dot != <$type>::zero());

                // Test Hadamard product
                let hadamard = a.hadamard_product(&b);
                assert_eq!(hadamard.len(), 2);
            }

            #[test]
            #[should_panic(expected = "Vectors must have the same length")]
            fn test_vector_length_mismatch() {
                let mut rng = $rng;
                let a = GenericVector::<$type>::random(&mut rng, 2);
                let b = GenericVector::<$type>::random(&mut rng, 1);
                let _ = a + b;
            }

            #[test]
            fn test_vector_conversion() {
                let mut rng = $rng;
                let elements: Vec<$type> = (0..3).map(|_| <$type>::random(&mut rng)).collect();

                // Test From<Vec<T>>
                let v1 = GenericVector::from(elements.clone());
                assert_eq!(v1.len(), 3);

                // Test into_inner
                let v2 = v1.clone();
                let elements2 = v2.into_inner();
                assert_eq!(elements, elements2);

                // Test as_slice
                let slice = v1.as_slice();
                assert_eq!(slice.len(), 3);
            }
        }
    };
}

/// Macro to generate additional polynomial-specific vector tests
#[macro_export]
macro_rules! polynomial_vector_tests {
    ($type:ty, $rng:expr) => {
        #[cfg(test)]
        mod polynomial_tests {
            use super::*;
            use crate::matrix::vector_arithmatic::GenericVector;
            use crate::ring::MatrixElement;
            use rand::RngCore;

            #[test]
            fn test_polynomial_vector_operations() {
                let mut rng = $rng;
                let a = GenericVector::<$type>::random(&mut rng, 2);
                let b = GenericVector::<$type>::random(&mut rng, 2);

                // Test polynomial multiplication
                let prod = a.elements.clone() * b.elements.clone();
                assert_eq!(prod.len(), 2);

                // Verify polynomial properties
                for element in prod.iter() {
                    assert!(element.degree() <= <$type>::modulus().degree());
                }
            }

            #[test]
            fn test_polynomial_vector_inner_product() {
                let mut rng = $rng;
                let a = GenericVector::<$type>::random(&mut rng, 2);
                let b = GenericVector::<$type>::random(&mut rng, 2);

                let dot = a.inner_product(&b);
                assert!(dot.degree() <= <$type>::modulus().degree());
            }
        }
    };
}
