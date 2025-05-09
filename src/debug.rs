use crate::matrix::poly_ring_matrix::PolyRingMatrix;
use crate::ring::PolynomialQuotientRing;

pub fn debug_polyring_matrix<P: PolynomialQuotientRing>(label: &str, matrix: &PolyRingMatrix<P>) {
    println!(
        "{label}: row*col={:?}*{:?}, value: {:?}",
        matrix.rows, matrix.cols, matrix.values
    );
}

pub fn debug_poly_ring<P: PolynomialQuotientRing>(label: &str, poly: &P) {
    println!("{label}: value: {:?}", poly.to_string());
}
