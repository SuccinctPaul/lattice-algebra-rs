use crate::matrix::matrix::GenericMatrix;
use crate::ring::{MatrixElement, PolynomialQuotientRing, Ring};

pub fn debug_polyring_matrix<E: MatrixElement>(label: &str, matrix: &GenericMatrix<E>) {
    println!(
        "{label}: row*col={:?}*{:?}, data: {:?}",
        matrix.rows, matrix.cols, matrix.data
    );
}

pub fn debug_poly_ring<P: PolynomialQuotientRing>(label: &str, poly: &P) {
    println!("{label}: value: {:?}", poly.to_string());
}
