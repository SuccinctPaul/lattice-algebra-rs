//! τ-sparse challenge polynomials (L2).
//!
//! ML-DSA challenges are SampleInBall polynomials: exactly `τ` coefficients
//! are ±1, all others zero. Multiplying such a challenge into a dense
//! polynomial costs `O(τ·N)` via monomial shifts, beating the NTT path —
//! this type captures both the representation and the fast multiply.

use crate::poly::UniPolynomial;
use crate::ring::poly_ring::PolyRing;
use crate::ring::PolynomialQuotientRing;
use crate::ring::TwoAdicRing;
use std::marker::PhantomData;

use crate::ring::Ring;

/// A sparse polynomial over `R` with `degree_bound` slots.
///
/// Invariant: positions are strictly increasing and every stored sign is ±1
/// (zero entries are not stored).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SparsePolynomial<R: Ring> {
    /// `(sign, position)` pairs, signs in `{-1, +1}`, positions ascending.
    terms: Vec<(i8, usize)>,
    degree_bound: usize,
    /// Keeps the target coefficient ring in the type.
    _marker: PhantomData<R>,
}

impl<R: Ring> SparsePolynomial<R> {
    /// Builds a sparse polynomial from a dense sign vector: `signs[p] ∈
    /// {-1, 0, +1}` for every position `p < degree_bound`. Zero entries are
    /// dropped.
    ///
    /// # Panics
    /// If any entry is outside `{-1, 0, +1}` or the slice is longer than
    /// `degree_bound`.
    pub fn from_sign_vector(signs: &[i8], degree_bound: usize) -> Self {
        assert!(
            signs.len() <= degree_bound,
            "sign vector longer than degree bound"
        );
        let mut terms = Vec::new();
        for (p, &s) in signs.iter().enumerate() {
            match s {
                0 => {}
                1 => terms.push((1, p)),
                -1 => terms.push((-1, p)),
                _ => panic!("sparse challenge signs must be in {{-1, 0, +1}}"),
            }
        }
        Self {
            terms,
            degree_bound,
            _marker: PhantomData,
        }
    }

    /// Number of non-zero coefficients (`τ` for ML-DSA challenges).
    pub fn num_nonzero(&self) -> usize {
        self.terms.len()
    }

    /// The degree bound (ring dimension) this polynomial lives in.
    pub fn degree_bound(&self) -> usize {
        self.degree_bound
    }

    /// Iterates `(sign, position)` pairs.
    pub fn iter(&self) -> impl Iterator<Item = (i8, usize)> + '_ {
        self.terms.iter().copied()
    }

    /// Expands to the dense coefficient vector (ascending powers).
    pub fn to_coeff_vec(&self) -> Vec<R> {
        let mut out = vec![R::ZERO; self.degree_bound];
        for &(s, p) in &self.terms {
            out[p] = if s > 0 { R::ONE } else { -R::ONE };
        }
        out
    }

    /// Expands to a dense [`UniPolynomial`].
    pub fn to_dense(&self) -> UniPolynomial<R> {
        UniPolynomial::from_coefficients(self.to_coeff_vec())
    }
}

impl<R: TwoAdicRing> SparsePolynomial<R> {
    /// `self * dense` in `Z_q[X]/(X^N + 1)` in `O(τ·N)`.
    ///
    /// Multiplying by the monomial `X^p` is a rotation with a sign flip on
    /// the wrapped half, so each sparse term contributes one pass over `N`
    /// coefficients.
    pub fn mul_dense<const N: usize>(&self, dense: &PolyRing<R, N>) -> PolyRing<R, N> {
        assert_eq!(
            self.degree_bound, N,
            "sparse challenge degree bound must equal ring dimension"
        );
        let n = N;
        let dense_coeffs = dense.coefficients();
        let mut acc = vec![R::ZERO; n];
        for &(s, p) in &self.terms {
            let plus = s > 0;
            for (k, &d) in dense_coeffs.iter().enumerate() {
                let dst = p + k;
                if dst < n {
                    if plus {
                        acc[dst] += d;
                    } else {
                        acc[dst] -= d;
                    }
                } else {
                    // x^{p+k} ≡ -x^{p+k-N} mod (X^N + 1)
                    if plus {
                        acc[dst - n] -= d;
                    } else {
                        acc[dst - n] += d;
                    }
                }
            }
        }
        let mut inner = UniPolynomial::from_coefficients(acc);
        inner.normalize();
        PolyRing { inner }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::zq::Zq;
    use rand::{Rng, SeedableRng};

    type Zq17 = Zq<17>;
    type R = PolyRing<Zq17, 8>;

    fn dense(v: &[u64]) -> R {
        R::from_coefficients(v.iter().map(|&x| Zq17::new(x)).collect())
    }

    #[test]
    fn from_sign_vector_drops_zeros() {
        let sp = SparsePolynomial::<Zq17>::from_sign_vector(&[1, 0, 0, -1, 0, 0, 0, 1], 8);
        assert_eq!(sp.num_nonzero(), 3);
        let collected: Vec<_> = sp.iter().collect();
        assert_eq!(collected, vec![(1, 0), (-1, 3), (1, 7)]);
    }

    #[test]
    #[should_panic(expected = "signs must be")]
    fn rejects_non_unit_signs() {
        SparsePolynomial::<Zq17>::from_sign_vector(&[2], 8);
    }

    #[test]
    fn mul_dense_matches_dense_product() {
        // sparse (1 at 0, -1 at 3) times dense (1 + 2x + 3x^2)
        let sp = SparsePolynomial::<Zq17>::from_sign_vector(&[1, 0, 0, -1, 0, 0, 0, 0], 8);
        let d = dense(&[1, 2, 3]);
        let got = sp.mul_dense(&d);

        let expected = dense(&[1, 2, 3]) - dense(&[0, 0, 0, 1, 2, 3]);
        assert_eq!(got, expected);
    }

    #[test]
    fn mul_dense_wraps_negacyclically() {
        // x^7 * x^1 = x^8 ≡ -1  (mod X^8 + 1): a constant.
        let sp = SparsePolynomial::<Zq17>::from_sign_vector(&[0, 0, 0, 0, 0, 0, 0, 1], 8);
        let d = dense(&[0, 1]);
        let got = sp.mul_dense(&d);
        assert_eq!(got.coefficients(), vec![-Zq17::ONE]);

        // x^7 * x^2 = x^9 ≡ -x
        let sp = SparsePolynomial::<Zq17>::from_sign_vector(&[0, 0, 0, 0, 0, 0, 0, 1], 8);
        let d = dense(&[0, 0, 1]);
        let got = sp.mul_dense(&d);
        assert_eq!(got.coefficients(), vec![Zq17::ZERO, -Zq17::ONE]);
    }

    #[test]
    fn mul_dense_matches_ring_multiplication() {
        let mut rng = rand::rngs::StdRng::seed_from_u64(7);
        for _ in 0..8 {
            let signs: Vec<i8> = (0..8)
                .map(|_| {
                    if rng.random_bool(0.8) {
                        0
                    } else if rng.random() {
                        1
                    } else {
                        -1
                    }
                })
                .collect();
            let sp = SparsePolynomial::<Zq17>::from_sign_vector(&signs, 8);
            let dv: Vec<u64> = (0..8).map(|_| rng.random_range(0..17)).collect();
            let d = dense(&dv);

            let dense_repr = R::from_coefficients(sp.to_dense().coefficients());
            assert_eq!(sp.mul_dense(&d), dense_repr * d);
        }
    }
}
