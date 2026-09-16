//! The Ajtai commitment key over the Z2 ring — the single implementation
//! every Z2-ring protocol commits through (L5).
//!
//! `A ∈ R^{N×M}` is derived from a seed via the raw-coefficient expansion
//! ([`crate::foundation::sampling::uniform_matrix_from_seed`], domain `b""`
//! unless labeled) and stays dense in coefficient representation; opening
//! is the matrix-vector product `A·x`.
//!
//! Historically this type existed once per protocol (`Z2CommitKey`,
//! `IpaKey`, `ShortKey`, `LfKey`, the two `FoldKey` matrices) with identical
//! bodies; the public protocol-facing names survive as type aliases, and
//! the folding key composes two labeled [`AjtaiKey`]s.

use crate::foundation::sampling::uniform_matrix_from_seed;
use crate::instance::simd::z2_mul;
use algebra::ring::MatrixElement;

use crate::instance::ring::{Z2Coeff, Z2Ring, D};

/// Ring-element products above which `mul_vec` distributes its independent
/// output rows across the rayon pool (`parallel` feature). Every real
/// instance clears this by orders of magnitude.
#[cfg(feature = "parallel")]
const PAR_MIN_TERMS: usize = 1024;

/// Ajtai commitment key `A ∈ R^{N×M}` over the Z2 ring.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AjtaiKey<const N: usize, const M: usize> {
    a: Vec<Vec<Z2Ring>>,
}

impl<const N: usize, const M: usize> AjtaiKey<N, M> {
    /// Derives the key from a seed (default domain).
    pub fn setup(seed: &[u8; 32]) -> Self {
        Self::setup_labeled(b"", seed)
    }

    /// Derives the key from a seed under an explicit domain label (the
    /// folding layer uses distinct labels for its witness/error matrices).
    pub fn setup_labeled(domain: &[u8], seed: &[u8; 32]) -> Self {
        Self {
            a: uniform_matrix_from_seed::<Z2Coeff, D>(domain, seed, N, M),
        }
    }

    /// `A·x`.
    ///
    /// Output rows are independent, so with the `parallel` feature large
    /// keys distribute rows across the rayon pool (results are
    /// order-preserving and identical to the sequential product).
    pub fn mul_vec(&self, x: &[Z2Ring]) -> Vec<Z2Ring> {
        debug_assert_eq!(x.len(), M);

        #[cfg(feature = "parallel")]
        if N * M >= PAR_MIN_TERMS {
            use rayon::prelude::*;

            return self
                .a
                .par_iter()
                .map(|row| {
                    let mut acc = Z2Ring::zero();
                    for (a_ij, xj) in row.iter().zip(x.iter()) {
                        acc += z2_mul(a_ij, xj);
                    }
                    acc
                })
                .collect();
        }

        (0..N)
            .map(|i| {
                let mut acc = Z2Ring::zero();
                for (a_ij, xj) in self.a[i].iter().zip(x.iter()) {
                    acc += z2_mul(a_ij, xj);
                }
                acc
            })
            .collect()
    }

    /// `A·x` — alias of [`AjtaiKey::mul_vec`] under the historical
    /// "commit to a (short) vector" name.
    pub fn commit(&self, x: &[Z2Ring]) -> Vec<Z2Ring> {
        self.mul_vec(x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn key_is_deterministic_and_domain_separated() {
        let seed = [7u8; 32];
        let k1: AjtaiKey<4, 2> = AjtaiKey::setup(&seed);
        let k2: AjtaiKey<4, 2> = AjtaiKey::setup(&seed);
        assert_eq!(k1, k2);

        let kl: AjtaiKey<4, 2> = AjtaiKey::setup_labeled(b"other", &seed);
        assert_ne!(k1, kl, "labels must separate expansions");

        let x = vec![Z2Ring::one(), Z2Ring::one()];
        assert_eq!(k1.commit(&x), k1.mul_vec(&x));
        assert_eq!(k1.mul_vec(&x).len(), 4);
    }
}
