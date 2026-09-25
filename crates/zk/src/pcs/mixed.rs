//! Mixed row/column contraction over block matrices (Z7 support).
//!
//! The tree- and folding-line protocols in `docs/survey-lattice-pcs.md` —
//! CMNW's opening (eprint 2024/281 Fig. 7), Maltese's folding (2026/2067),
//! Grand Danois's rotation-matrix row folding (2026/1196) — are written
//! almost entirely in terms of two operations on an `m × k` block matrix of
//! ring elements:
//!
//! ```text
//! (I_m ⊗ xᵀ)·M   contract every row against x   → m ring elements
//! (cᵀ ⊗ I_k)·M   combine the rows with weights c → k ring elements
//! ```
//!
//! and on the fact that the two can be applied in either order:
//!
//! ```text
//! ⟨c, (I_m ⊗ xᵀ)M⟩  =  Σ_{i,j} cᵢ·Mᵢⱼ·xⱼ  =  ⟨(cᵀ ⊗ I_k)M, x⟩
//! ```
//!
//! That identity is what lets a prover fold *columns* in one step and a
//! verifier fold *rows* in another and still land on the same equation — so
//! it is checked here against ring arithmetic, not assumed.
//!
//! [`crate::pcs::nested::TensorGadget`] supplies the `(I_m ⊗ A)` key
//! application; this module supplies the `(I_m ⊗ xᵀ)` / `(cᵀ ⊗ I_k)` vector
//! contractions that surround it.

use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// An `m × k` matrix of ring elements, row-major.
#[derive(Clone, PartialEq, Eq)]
pub struct BlockMat<R: Ring, const D: usize> {
    rows: usize,
    cols: usize,
    data: Vec<PolyRing<R, D>>,
}

impl<R: Ring, const D: usize> fmt::Debug for BlockMat<R, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "BlockMat({}×{})", self.rows, self.cols)
    }
}

/// Why a block-matrix operation refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MixedError {
    /// A vector did not match the axis it was applied to.
    WrongLength {
        /// Length supplied.
        got: usize,
        /// Length the axis requires.
        expected: usize,
    },
    /// A flat buffer was not a whole number of rows.
    Ragged {
        /// Element count supplied.
        len: usize,
        /// Row width it had to divide.
        cols: usize,
    },
}

impl fmt::Display for MixedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MixedError::WrongLength { got, expected } => {
                write!(f, "vector of length {got} against an axis of {expected}")
            }
            MixedError::Ragged { len, cols } => {
                write!(f, "{len} elements do not fill rows of width {cols}")
            }
        }
    }
}

fn zero_elt<R: Ring, const D: usize>() -> PolyRing<R, D> {
    PolyRing::from_coefficients(vec![R::ZERO; D])
}

/// `Σᵢ aᵢ·bᵢ` over the ring.
///
/// # Panics
/// If the vectors differ in length.
pub fn dot<R: Ring, const D: usize>(a: &[PolyRing<R, D>], b: &[PolyRing<R, D>]) -> PolyRing<R, D> {
    assert_eq!(a.len(), b.len(), "ring dot needs equal lengths");
    let mut acc = zero_elt::<R, D>();
    for (x, y) in a.iter().zip(b.iter()) {
        acc += x.clone() * y.clone();
    }
    acc
}

impl<R: Ring, const D: usize> BlockMat<R, D> {
    /// Wraps row-major data of shape `rows × cols`.
    ///
    /// # Errors
    /// [`MixedError::Ragged`] unless `data.len() == rows * cols`.
    pub fn new(rows: usize, cols: usize, data: Vec<PolyRing<R, D>>) -> Result<Self, MixedError> {
        if data.len() != rows * cols {
            return Err(MixedError::Ragged {
                len: data.len(),
                cols: rows * cols,
            });
        }
        Ok(Self { rows, cols, data })
    }

    /// Builds a matrix from `rows` vectors of equal length.
    ///
    /// # Errors
    /// [`MixedError::Ragged`] if the rows disagree in length.
    pub fn from_rows(rows: &[&[PolyRing<R, D>]]) -> Result<Self, MixedError> {
        let cols = rows.first().map_or(0, |r| r.len());
        if rows.iter().any(|r| r.len() != cols) {
            return Err(MixedError::Ragged {
                len: rows.iter().map(|r| r.len()).sum(),
                cols,
            });
        }
        Ok(Self {
            rows: rows.len(),
            cols,
            data: rows.iter().flat_map(|r| r.iter().cloned()).collect(),
        })
    }

    /// Row count.
    pub const fn rows(&self) -> usize {
        self.rows
    }

    /// Column count.
    pub const fn cols(&self) -> usize {
        self.cols
    }

    /// Row `i`.
    ///
    /// # Panics
    /// If `i >= rows` (indexing, not a protocol input).
    pub fn row(&self, i: usize) -> &[PolyRing<R, D>] {
        &self.data[i * self.cols..(i + 1) * self.cols]
    }

    /// Iterate the rows, left to right.
    pub fn row_iter(&self) -> impl Iterator<Item = &[PolyRing<R, D>]> {
        self.data.chunks(self.cols)
    }

    /// Column `j`.
    ///
    /// # Panics
    /// If `j >= cols`.
    pub fn column(&self, j: usize) -> Vec<PolyRing<R, D>> {
        (0..self.rows)
            .map(|i| self.data[i * self.cols + j].clone())
            .collect()
    }

    /// `(I_rows ⊗ xᵀ)·M` — contract every row against `x`, giving `rows`
    /// ring elements. This is CMNW's step `(I_{r₀} ⊗ x₁ᵀ)` and its
    /// `(I_{r₀r₁} ⊗ x₂ᵀ)` nested variant.
    ///
    /// # Errors
    /// [`MixedError::WrongLength`] unless `x.len() == cols`.
    pub fn contract_cols(&self, x: &[PolyRing<R, D>]) -> Result<Vec<PolyRing<R, D>>, MixedError> {
        if x.len() != self.cols {
            return Err(MixedError::WrongLength {
                got: x.len(),
                expected: self.cols,
            });
        }
        Ok((0..self.rows).map(|i| dot(self.row(i), x)).collect())
    }

    /// `(cᵀ ⊗ I_cols)·M` — combine rows with the weights `c`, giving `cols`
    /// ring elements. This is CMNW's `(c₁ᵀ ⊗ I_{r₁nα})s₁` and its
    /// `(c₂ᵀ ⊗ I_{r₂nα})e`.
    ///
    /// # Errors
    /// [`MixedError::WrongLength`] unless `c.len() == rows`.
    pub fn contract_rows(&self, c: &[PolyRing<R, D>]) -> Result<Vec<PolyRing<R, D>>, MixedError> {
        if c.len() != self.rows {
            return Err(MixedError::WrongLength {
                got: c.len(),
                expected: self.rows,
            });
        }
        let mut out = vec![zero_elt::<R, D>(); self.cols];
        for (i, w) in c.iter().enumerate() {
            for (o, v) in out.iter_mut().zip(self.row(i)) {
                *o += w.clone() * v.clone();
            }
        }
        Ok(out)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::encoding::ring_to_u32;
    use crate::foundation::sampling::from_centered;
    use crate::pcs::{RingElt, Z1Coeff, DIM};

    fn elt(seed: u64, i: usize, j: usize) -> RingElt {
        let coeffs: Vec<_> = (0..DIM)
            .map(|t| {
                let v = (seed as i64 * 17 + i as i64 * 3 + j as i64 * 5 + t as i64) % 13;
                from_centered::<Z1Coeff>(v - 6)
            })
            .collect();
        RingElt::from_coefficients(coeffs)
    }

    fn matrix(rows: usize, cols: usize) -> BlockMat<Z1Coeff, DIM> {
        let data = (0..rows)
            .flat_map(|i| (0..cols).map(move |j| elt(2, i, j)))
            .collect();
        BlockMat::new(rows, cols, data).expect("shaped")
    }

    fn vec_of(len: usize, salt: u64) -> Vec<RingElt> {
        (0..len).map(|j| elt(salt, 0, j)).collect()
    }

    /// The count of a coefficient position, used to compare the two
    /// contraction orders as plain integers.
    fn const_term(v: &RingElt) -> u64 {
        u64::from(ring_to_u32::<Z1Coeff, DIM>(v)[0])
    }

    #[test]
    fn contraction_matches_expanded_double_sum() {
        // ⟨c, (I⊗xᵀ)M⟩ and ⟨(cᵀ⊗I)M, x⟩ must both equal Σ_{i,j} cᵢMᵢⱼxⱼ.
        // This is the mixed-product law the protocols lean on; if either
        // contraction were transposed it would fail.
        let m = matrix(3, 4);
        let c = vec_of(3, 11);
        let x = vec_of(4, 13);
        let by_cols_then_rows = dot(&c, &m.contract_cols(&x).expect("cols"));
        let by_rows_then_cols = dot(&m.contract_rows(&c).expect("rows"), &x);
        assert_eq!(by_cols_then_rows, by_rows_then_cols);

        // and an independent expansion, term by term
        let mut expanded = zero_elt::<Z1Coeff, DIM>();
        for (ci, row) in c.iter().zip(m.row_iter()) {
            for (mij, xj) in row.iter().zip(x.iter()) {
                expanded += ci.clone() * mij.clone() * xj.clone();
            }
        }
        assert_eq!(by_cols_then_rows, expanded);
    }

    #[test]
    fn contract_cols_is_the_row_wise_dot_product() {
        let m = matrix(2, 3);
        let x = vec_of(3, 7);
        let got = m.contract_cols(&x).expect("ok");
        assert_eq!(got.len(), 2);
        for (got_i, row) in got.iter().zip(m.row_iter()) {
            assert_eq!(got_i, &dot(row, &x), "each output is that row against x");
        }
    }

    #[test]
    fn contract_rows_is_the_weighted_row_combination() {
        let m = matrix(3, 2);
        let c = vec_of(3, 5);
        let got = m.contract_rows(&c).expect("ok");
        assert_eq!(got.len(), 2);
        // column-wise: out[j] = Σᵢ cᵢ·Mᵢⱼ
        for (j, got_j) in got.iter().enumerate() {
            assert_eq!(got_j, &dot(&c, &m.column(j)));
        }
    }

    #[test]
    fn contractions_are_linear_in_the_weights() {
        let m = matrix(3, 4);
        let c = vec_of(3, 11);
        let d = vec_of(3, 12);
        let x = vec_of(4, 13);
        let summed: Vec<RingElt> = c
            .iter()
            .zip(d.iter())
            .map(|(a, b)| a.clone() + b.clone())
            .collect();
        let lhs = m.contract_rows(&summed).expect("ok");
        let r1 = m.contract_rows(&c).expect("ok");
        let r2 = m.contract_rows(&d).expect("ok");
        let rhs: Vec<RingElt> = r1
            .iter()
            .zip(r2.iter())
            .map(|(a, b)| a.clone() + b.clone())
            .collect();
        assert_eq!(lhs, rhs);

        // same on the column axis
        let summed_x: Vec<RingElt> = x.iter().map(|v| v.clone() + v.clone()).collect();
        let doubled = m.contract_cols(&summed_x).expect("ok");
        let twice = m.contract_cols(&x).expect("ok");
        for (a, b) in doubled.iter().zip(twice.iter()) {
            assert_eq!(const_term(a), (2 * const_term(b)) % Z1Coeff::MODULUS);
        }
    }

    #[test]
    fn contractions_work_on_a_non_ntt_friendly_ring() {
        // The reason BlockMat was generalised: CMNW/Hachi/Serval/Maltese need
        // q ≡ 5 (mod 8), where no NTT-backed path exists at all. The
        // either-order law must still hold there.
        use algebra::ring::zq::Zq;
        type Q5 = Zq<4294967197>;
        const MOD8: u64 = 4_294_967_197;
        assert_eq!(MOD8 % 8, 5);
        assert_eq!((MOD8 - 1).trailing_zeros(), 2);

        let e = |i: usize, j: usize, salt: u64| {
            let c = (0..64)
                .map(|t| Q5::from(((salt * 97 + (i * 7 + j * 13 + t) as u64) % 5000) % MOD8))
                .collect();
            PolyRing::<Q5, 64>::from_coefficients(c)
        };
        let data: Vec<_> = (0..3)
            .flat_map(|i| (0..4).map(move |j| e(i, j, 1)))
            .collect();
        let m = BlockMat::<Q5, 64>::new(3, 4, data).expect("shaped");
        let c: Vec<_> = (0..3).map(|i| e(i, 0, 2)).collect();
        let x: Vec<_> = (0..4).map(|j| e(0, j, 3)).collect();

        let left = dot(&c, &m.contract_cols(&x).expect("cols"));
        let right = dot(&m.contract_rows(&c).expect("rows"), &x);
        assert_eq!(left, right, "the mixed-product law must not need an NTT");

        let mut expanded = zero_elt::<Q5, 64>();
        for (ci, row) in c.iter().zip(m.row_iter()) {
            for (mij, xj) in row.iter().zip(x.iter()) {
                expanded += ci.clone() * mij.clone() * xj.clone();
            }
        }
        assert_eq!(left, expanded);
    }

    #[test]
    fn rejects_vectors_on_the_wrong_axis() {
        let m = matrix(3, 4);
        assert_eq!(
            m.contract_cols(&vec_of(3, 7)),
            Err(MixedError::WrongLength {
                got: 3,
                expected: 4
            })
        );
        assert_eq!(
            m.contract_rows(&vec_of(4, 7)),
            Err(MixedError::WrongLength {
                got: 4,
                expected: 3
            })
        );
    }

    #[test]
    fn rejects_ragged_buffers() {
        let data: Vec<RingElt> = (0..7).map(|j| elt(1, 0, j)).collect();
        assert!(matches!(
            BlockMat::new(3, 4, data),
            Err(MixedError::Ragged { len: 7, cols: 12 })
        ));
        let rows: Vec<Vec<RingElt>> = vec![
            (0..3).map(|j| elt(1, 0, j)).collect(),
            (0..2).map(|j| elt(1, 1, j)).collect(),
        ];
        let refs: Vec<&[RingElt]> = rows.iter().map(|r| r.as_slice()).collect();
        assert!(matches!(
            BlockMat::from_rows(&refs),
            Err(MixedError::Ragged { .. })
        ));
    }
}
