//! Module-lattice layer (L3): vectors and matrices over
//! `R_q = Z_q[X]/(X^N + 1)` with dimensions encoded in types.
//!
//! This is the shared working object of ML-KEM, ML-DSA, Ajtai/SIS
//! commitments and LaBRADOR-style protocols. The NTT-domain variants
//! (`ModuleMatrixNtt` etc.) let a commitment matrix stay transformed for its
//! whole lifetime — the single most impactful ML-DSA optimization.
//!
//! `ExpandA` (seed → matrix) lives here too: both the NTT-domain variant
//! used by ML-DSA and the coefficient-domain variant needed by ML-KEM.

pub mod rounding;

use crate::crypto::sampling::{sample_uniform_coeff, BitStream};
use crate::crypto::xof::Xof;
use crate::ntt::NttDomain;
use crate::ntt::NttOperatorOptimized;
use crate::poly::UniPolynomial;
use crate::ring::poly_ring::PolyRing;
use crate::ring::traits::{CenteredRing, TwoAdicRing};
use crate::ring::PolynomialQuotientRing;
use crate::ring::Ring;
use std::ops::{Add, Neg, Sub};

// ===========================================================================
// Module vectors (coefficient domain)
// ===========================================================================

/// A vector of `K` polynomials in `R_q`, i.e. an element of `R_q^K`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleVector<R: Ring, const K: usize, const N: usize> {
    polys: [PolyRing<R, N>; K],
}

impl<R: Ring, const K: usize, const N: usize> ModuleVector<R, K, N> {
    /// Builds a vector from `K` polynomials.
    pub fn new(polys: [PolyRing<R, N>; K]) -> Self {
        Self { polys }
    }

    /// Builds a vector by applying `f` to each index.
    pub fn from_fn(f: impl FnMut(usize) -> PolyRing<R, N>) -> Self {
        Self {
            polys: std::array::from_fn(f),
        }
    }

    /// The zero vector.
    pub fn zero() -> Self {
        Self::from_fn(|_| PolyRing {
            inner: UniPolynomial::zero(),
        })
    }

    /// Borrows the `i`-th polynomial.
    pub fn get(&self, i: usize) -> &PolyRing<R, N> {
        &self.polys[i]
    }

    /// Mutably borrows the `i`-th polynomial.
    pub fn get_mut(&mut self, i: usize) -> &mut PolyRing<R, N> {
        &mut self.polys[i]
    }

    /// Borrows all polynomials.
    pub fn polys(&self) -> &[PolyRing<R, N>; K] {
        &self.polys
    }

    /// Inner product `Σ self_i · other_i` in `R_q`.
    #[must_use]
    pub fn inner_product(&self, other: &Self) -> PolyRing<R, N> {
        let mut acc: Option<PolyRing<R, N>> = None;
        for (a, b) in self.polys.iter().zip(&other.polys) {
            let p = a.clone() * b.clone();
            acc = Some(match acc {
                Some(s) => s + p,
                None => p,
            });
        }
        acc.unwrap_or_else(|| PolyRing {
            inner: UniPolynomial::zero(),
        })
    }

    /// `self * c` for a scalar polynomial `c ∈ R_q` (e.g. the sparse
    /// challenge times a secret vector).
    #[must_use]
    pub fn mul_scalar(&self, c: &PolyRing<R, N>) -> Self {
        Self::from_fn(|i| c.clone() * self.polys[i].clone())
    }

    /// Transforms every polynomial into the NTT domain.
    pub fn to_ntt(&self, op: &NttOperatorOptimized<R, N>) -> ModuleVectorNtt<R, K, N>
    where
        R: TwoAdicRing,
    {
        ModuleVectorNtt {
            polys: std::array::from_fn(|i| self.polys[i].to_ntt(op)),
        }
    }
}

impl<R: CenteredRing, const K: usize, const N: usize> ModuleVector<R, K, N> {
    /// `‖self‖_∞ = max over all coefficients of |c|_∞`, computed without
    /// early exits or data-dependent branches (safe on secret data).
    pub fn infinity_norm(&self) -> u64 {
        let mut m = 0u64;
        for p in &self.polys {
            for c in p.coefficients() {
                let a = c.abs_infinity();
                m = crate::crypto::ct::select_u64(a > m, a, m);
            }
        }
        m
    }
}

impl<R: Ring, const K: usize, const N: usize> Add for ModuleVector<R, K, N> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        let mut iter = self.polys.into_iter().zip(rhs.polys).map(|(x, y)| x + y);
        Self {
            polys: std::array::from_fn(|_| iter.next().unwrap()),
        }
    }
}

impl<R: Ring, const K: usize, const N: usize> Sub for ModuleVector<R, K, N> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        let mut iter = self.polys.into_iter().zip(rhs.polys).map(|(x, y)| x - y);
        Self {
            polys: std::array::from_fn(|_| iter.next().unwrap()),
        }
    }
}

impl<R: Ring, const K: usize, const N: usize> Neg for ModuleVector<R, K, N> {
    type Output = Self;
    fn neg(self) -> Self {
        let mut iter = self.polys.into_iter().map(|x| -x);
        Self {
            polys: std::array::from_fn(|_| iter.next().unwrap()),
        }
    }
}

// ===========================================================================
// Module vectors (NTT domain)
// ===========================================================================

/// A `R_q^K` vector stored in the NTT domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleVectorNtt<R: TwoAdicRing, const K: usize, const N: usize> {
    polys: [NttDomain<R, N>; K],
}

impl<R: TwoAdicRing, const K: usize, const N: usize> ModuleVectorNtt<R, K, N> {
    /// Borrows all polynomials.
    pub fn polys(&self) -> &[NttDomain<R, N>; K] {
        &self.polys
    }

    /// Domain-wise addition.
    #[must_use]
    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            polys: std::array::from_fn(|i| self.polys[i].add(&rhs.polys[i])),
        }
    }

    /// Domain-wise subtraction.
    #[must_use]
    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            polys: std::array::from_fn(|i| self.polys[i].sub(&rhs.polys[i])),
        }
    }

    /// Transforms back into the coefficient domain.
    pub fn from_ntt(self, op: &NttOperatorOptimized<R, N>) -> ModuleVector<R, K, N> {
        let mut iter = self.polys.into_iter().map(|p| PolyRing::from_ntt(p, op));
        ModuleVector {
            polys: std::array::from_fn(|_| iter.next().unwrap()),
        }
    }
}

// ===========================================================================
// Module matrices
// ===========================================================================

/// A `K × L` matrix over `R_q` (coefficient domain).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleMatrix<R: Ring, const K: usize, const L: usize, const N: usize> {
    entries: [[PolyRing<R, N>; L]; K],
}

impl<R: Ring, const K: usize, const L: usize, const N: usize> ModuleMatrix<R, K, L, N> {
    /// Builds a matrix entry-by-entry (`f(row, col)`).
    pub fn from_fn(mut f: impl FnMut(usize, usize) -> PolyRing<R, N>) -> Self {
        Self {
            entries: std::array::from_fn(|i| std::array::from_fn(|j| f(i, j))),
        }
    }

    /// `self · v` in the coefficient domain (reference path; production
    /// paths use [`ModuleMatrixNtt::mul_vec_ntt`]).
    #[must_use]
    pub fn mul_vec(&self, v: &ModuleVector<R, L, N>) -> ModuleVector<R, K, N> {
        ModuleVector::from_fn(|i| {
            let mut acc: Option<PolyRing<R, N>> = None;
            for (a, b) in self.entries[i].iter().zip(v.polys().iter()) {
                let p = a.clone() * b.clone();
                acc = Some(match acc {
                    Some(s) => s + p,
                    None => p,
                });
            }
            acc.unwrap_or_else(|| PolyRing {
                inner: UniPolynomial::zero(),
            })
        })
    }

    /// Transforms every entry into the NTT domain (`K·L` transforms; do this
    /// once and keep the result).
    pub fn to_ntt(&self, op: &NttOperatorOptimized<R, N>) -> ModuleMatrixNtt<R, K, L, N>
    where
        R: TwoAdicRing,
    {
        ModuleMatrixNtt {
            entries: std::array::from_fn(|i| {
                std::array::from_fn(|j| self.entries[i][j].to_ntt(op))
            }),
        }
    }
}

/// A `K × L` matrix over `R_q` stored in the NTT domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleMatrixNtt<R: TwoAdicRing, const K: usize, const L: usize, const N: usize> {
    entries: [[NttDomain<R, N>; L]; K],
}

impl<R: TwoAdicRing, const K: usize, const L: usize, const N: usize> ModuleMatrixNtt<R, K, L, N> {
    /// Builds a matrix entry-by-entry in the NTT domain (`f(row, col)`).
    pub fn from_fn(mut f: impl FnMut(usize, usize) -> NttDomain<R, N>) -> Self {
        Self {
            entries: std::array::from_fn(|i| std::array::from_fn(|j| f(i, j))),
        }
    }

    /// `Â · v̂` entirely in the NTT domain: `K·L` pointwise multiplies and
    /// `K` domain additions, no transforms.
    #[must_use]
    pub fn mul_vec_ntt(&self, v: &ModuleVectorNtt<R, L, N>) -> ModuleVectorNtt<R, K, N> {
        ModuleVectorNtt {
            polys: std::array::from_fn(|i| {
                let mut acc: Option<NttDomain<R, N>> = None;
                for (a, b) in self.entries[i].iter().zip(v.polys().iter()) {
                    acc = Some(match acc {
                        Some(s) => s.add(&a.mul(b)),
                        None => a.mul(b),
                    });
                }
                acc.unwrap_or_else(NttDomain::zero)
            }),
        }
    }

    /// Borrows the entry at `(row, col)`.
    pub fn get(&self, i: usize, j: usize) -> &NttDomain<R, N> {
        &self.entries[i][j]
    }
}

// ===========================================================================
// ExpandA: seed → matrix
// ===========================================================================

/// Rejection-samples one NTT-domain polynomial from a fresh XOF stream
/// (FIPS 204 `RejNTTPoly` / `ExpandA`): coefficients are full-width uniform
/// over `[0, q)` drawn with masked rejection.
///
/// The XOF instance must already be bound to the seed and the entry indices;
/// index encoding is the caller's policy (ML-DSA uses `XOF(ρ, j, i)` with
/// single-byte indices).
pub fn sample_coeffs_from_xof<X: Xof, R: Ring, const N: usize>(xof: X) -> [R; N] {
    let mut xof = xof;
    let mut stream = BitStream::new(&mut xof);
    std::array::from_fn(|_| sample_uniform_coeff::<R>(&mut stream))
}

impl<R: TwoAdicRing, const K: usize, const L: usize, const N: usize> ModuleMatrixNtt<R, K, L, N> {
    /// FIPS 204 `ExpandA(ρ)`: builds `Â` directly in the NTT domain.
    ///
    /// Entry `(i, j)` is derived from the stream `XOF(ρ, j, i)` with
    /// single-byte indices, matching FIPS 204. Every coefficient is accepted
    /// with probability ≈ `q / 2^bitlen(q)` (≈ 0.9998 for `q = 8380417`).
    pub fn expand_from_seed<X: Xof>(seed: &[u8; 32]) -> Self {
        Self::from_fn(|i, j| {
            let mut xof = X::new(&[]);
            xof.absorb(seed);
            xof.absorb(&[j as u8, i as u8]);
            NttDomain::from_values(sample_coeffs_from_xof::<X, R, N>(xof))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::xof::Shake128Xof;
    use crate::ring::zq::Zq;

    type Zq17 = Zq<17>;
    type R = PolyRing<Zq17, 8>;
    type Vec3 = ModuleVector<Zq17, 3, 8>;
    type Mat3 = ModuleMatrix<Zq17, 3, 3, 8>;

    fn poly(v: &[i64]) -> R {
        R::from_coefficients(
            v.iter()
                .map(|&x| Zq17::new(x.rem_euclid(17) as u64))
                .collect(),
        )
    }

    #[test]
    fn vector_arithmetic_basics() {
        let a = Vec3::new([poly(&[1]), poly(&[2]), poly(&[3])]);
        let b = Vec3::new([poly(&[10]), poly(&[20]), poly(&[30])]);
        assert_eq!((a.clone() + b.clone()).polys()[1], poly(&[22]));
        assert_eq!((-b.clone()).polys()[0], poly(&[-10]));
        assert_eq!((b.clone() - a.clone()).polys()[2], poly(&[27]));
        let _ = a - b;
    }

    #[test]
    fn matrix_times_vector_matches_ntt_domain_path() {
        let m = Mat3::from_fn(|i, j| poly(&[(i * 5 + j * 3 + 1) as i64, (i + j) as i64, 7]));
        let v = Vec3::new([poly(&[1, 2]), poly(&[3]), poly(&[4, 5, 6])]);

        let op = NttOperatorOptimized::<Zq17, 8>::new();
        let via_ntt = m.to_ntt(&op).mul_vec_ntt(&v.to_ntt(&op)).from_ntt(&op);
        assert_eq!(m.mul_vec(&v), via_ntt);
    }

    #[test]
    fn ntt_vector_add_sub() {
        let op = NttOperatorOptimized::<Zq17, 8>::new();
        let a = Vec3::new([poly(&[1]), poly(&[2]), poly(&[3])]).to_ntt(&op);
        let b = Vec3::new([poly(&[1]), poly(&[2]), poly(&[3])]).to_ntt(&op);
        let sum = a.add(&b).from_ntt(&op);
        assert_eq!(sum.polys()[0], poly(&[2]));
        let diff = a.sub(&b).from_ntt(&op);
        assert_eq!(diff.polys()[1], poly(&[0]));
    }

    #[test]
    fn infinity_norm_is_max_over_coefficients() {
        let v = Vec3::new([poly(&[1]), poly(&[16, 2]), poly(&[3])]);
        // q = 17: |16|_∞ = 1, so the max is |3|_∞ = 3.
        assert_eq!(v.infinity_norm(), 3);
    }

    #[test]
    fn expand_from_seed_is_deterministic_and_shape_correct() {
        type Mat = ModuleMatrixNtt<Zq17, 2, 2, 8>;
        let seed = [7u8; 32];
        let m1 = Mat::expand_from_seed::<Shake128Xof>(&seed);
        let m2 = Mat::expand_from_seed::<Shake128Xof>(&seed);
        assert_eq!(m1, m2);

        // Different seeds give different matrices (overwhelming probability).
        let m3 = Mat::expand_from_seed::<Shake128Xof>(&[8u8; 32]);
        assert_ne!(m1, m3);
    }

    #[test]
    fn expand_matches_manual_sampling() {
        type Mat = ModuleMatrixNtt<Zq17, 1, 1, 8>;
        let seed = [9u8; 32];
        let m = Mat::expand_from_seed::<Shake128Xof>(&seed);

        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(&seed);
        xof.absorb(&[0u8, 0u8]); // j = 0 (column), i = 0 (row)
        let manual_values = sample_coeffs_from_xof::<Shake128Xof, Zq17, 8>(xof);
        assert_eq!(m.get(0, 0).values(), &manual_values);
    }
}
