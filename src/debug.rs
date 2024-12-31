use crate::matrix::poly_ring_matrix::PolyRingMatrix;
use crate::ring::PolynomialRingTrait;

pub fn debug_poly_matrix<P: PolynomialRingTrait>(label: &str, matrix: &PolyRingMatrix<P>) {
    println!(
        "{label}: row*col={:?}*{:?}, value: {:?}",
        matrix.rows, matrix.cols, matrix.values
    );
}

pub fn debug_poly_ring<P: PolynomialRingTrait>(label: &str, poly: &P) {
    println!("{label}: value: {:?}", poly.to_string());
}
