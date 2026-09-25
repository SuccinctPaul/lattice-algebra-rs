//! Coefficient-level linear algebra and the ring ↔ coefficient bridge (Z7
//! support).
//!
//! Every matrix type in the crate so far lives **over the ring**
//! ([`crate::pcs::key::RingMatrixKey`], [`crate::pcs::mixed::BlockMat`]): its
//! entries are elements of `R_q = Z_q[X]/(X^d+1)` and its products are ring
//! products. The shortness/projection line of the concrete schemes cannot be
//! expressed that way. CMNW (2024/281, App. A Eq. 20–22) draws
//!
//! ```text
//! p⃗ := (I_{r₁} ⊗ P) · e⃗  ∈ Z_q^{λ·r₁},   P ← χ^{λ × r₂nαd},   B ← Z_q^{l×λ}
//! ```
//!
//! where `e⃗` is the **coefficient vector** of `e` — so `P` mixes the `d`
//! coefficients inside one ring element, which no ring-level matrix can do
//! (a ring element acting by multiplication is `d`-banded circulant, and `χ`
//! is none of that). The projection is therefore a genuinely separate
//! capability, and it is what makes the trick work: `‖P·e⃗‖ ≤ (r₂nαd)·‖e‖∞`
//! holds with overwhelming probability over a *field*-level random matrix,
//! which is the approximate range proof CMNW runs instead of a gadget
//! decomposition of the opening.
//!
//! The bridge back to the ring is the σ-pairing identity ([`sigma_pairing_vec`],
//! the vector form of [`crate::pcs::packing::pairing_of`]): with `n⃗` the `i`-th
//! row of `B·P` read as a *ring* vector,
//!
//! ```text
//! const( ⟨σ(n), e⟩_R )  =  ⟨b⃗, P·e⃗⟩_{Z_q}
//! ```
//!
//! because `const(g·σ(h)) = Σ_k g_k·h_k` coefficientwise. That single identity
//! is CMNW Eq. (21)–(22): the prover can compute the *ring* quantity
//! `γ_{i,j} = ⟨σ(n), e_j⟩` from `P` and `e` alone (it never sees `B`), and the
//! verifier checks its constant term against `⟨b⃗, p⃗_j⟩`, which it computes
//! from the two messages it did see. The tests below pin both halves.
//!
//! Layering: `foundation → pcs::projection`. Nothing here is scheme-specific;
//! Grand Danois' `Π` Johnson–Lindenstrauss map and Maltese's coefficient-level
//! folding read as the same two contractions.

use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

use crate::pcs::packing::sigma_of;

/// Domain label for every derivation in this module.
const PROJ_DOMAIN: &[u8] = b"lattice-algebra/Z7/projection";

/// Why a coefficient-level operation refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FieldShapeError {
    /// Length supplied.
    pub got: usize,
    /// Length required.
    pub expected: usize,
}

impl fmt::Display for FieldShapeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "coefficient-level shape mismatch: got {}, expected {}",
            self.got, self.expected
        )
    }
}

/// A dense `rows × cols` matrix over the coefficient ring `R` (which for the
/// projection line is the base field `Z_q`, not the polynomial ring).
///
/// Entries are stored row-major.
#[derive(Clone, PartialEq, Eq)]
pub struct FieldMat<R: Ring> {
    rows: usize,
    cols: usize,
    data: Vec<R>,
}

impl<R: Ring> fmt::Debug for FieldMat<R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FieldMat<{}x{}>", self.rows, self.cols)
    }
}

/// Squeeze `n` field elements uniformly from `xof`, with no modular bias:
/// each entry takes a 128-bit draw reduced mod `q`.
fn squeeze_entries<X: Xof, R: Ring>(xof: &mut X, n: usize) -> Vec<R> {
    (0..n)
        .map(|_| {
            let mut buf = [0u8; 16];
            xof.squeeze(&mut buf);
            let raw = u128::from_le_bytes(buf);
            R::from((raw % u128::from(R::MODULUS)) as u64)
        })
        .collect()
}

impl<R: Ring> FieldMat<R> {
    /// Wraps explicit entries, row-major.
    ///
    /// # Panics
    /// Unless `entries.len() == rows * cols`.
    pub fn from_entries(rows: usize, cols: usize, entries: Vec<R>) -> Self {
        assert_eq!(
            entries.len(),
            rows * cols,
            "entry count must match rows × cols"
        );
        Self {
            rows,
            cols,
            data: entries,
        }
    }

    /// `M ← Z_q^{rows×cols}`: a uniformly random matrix, i.e. CMNW's
    /// soundness-boosting challenge `B`.
    pub fn uniform(label: &[u8], seed: &[u8; 32], rows: usize, cols: usize) -> Self {
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(PROJ_DOMAIN);
        xof.absorb(b"uniform");
        xof.absorb_labeled(label, seed);
        xof.absorb(&(rows as u64).to_le_bytes());
        xof.absorb(&(cols as u64).to_le_bytes());
        Self::from_entries(rows, cols, squeeze_entries(&mut xof, rows * cols))
    }

    /// `M ← χ^{rows×cols}` with `χ` uniform on `{−1, 0, 1}`: the small
    /// projection challenge `P`.
    ///
    /// The three values are taken with equal probability by reducing one byte
    /// mod 3, so the distribution is exact rather than approximate.
    pub fn ternary(label: &[u8], seed: &[u8; 32], rows: usize, cols: usize) -> Self {
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(PROJ_DOMAIN);
        xof.absorb(b"ternary");
        xof.absorb_labeled(label, seed);
        xof.absorb(&(rows as u64).to_le_bytes());
        xof.absorb(&(cols as u64).to_le_bytes());
        let entries = (0..rows * cols)
            .map(|_| {
                let mut buf = [0u8; 1];
                xof.squeeze(&mut buf);
                match buf[0] % 3 {
                    0 => R::ZERO,
                    1 => R::ONE,
                    _ => R::ZERO - R::ONE,
                }
            })
            .collect();
        Self::from_entries(rows, cols, entries)
    }

    /// Row count.
    pub const fn rows(&self) -> usize {
        self.rows
    }

    /// Column count.
    pub const fn cols(&self) -> usize {
        self.cols
    }

    /// Entry `(i, j)`.
    pub fn get(&self, i: usize, j: usize) -> Option<&R> {
        if i < self.rows && j < self.cols {
            Some(&self.data[i * self.cols + j])
        } else {
            None
        }
    }

    /// Row `i`.
    ///
    /// # Panics
    /// If `i >= rows`.
    pub fn row(&self, i: usize) -> &[R] {
        assert!(i < self.rows, "row index out of range");
        &self.data[i * self.cols..(i + 1) * self.cols]
    }

    /// `M · v` over `R`.
    ///
    /// # Errors
    /// [`FieldShapeError`] unless `v.len() == cols`.
    pub fn apply(&self, v: &[R]) -> Result<Vec<R>, FieldShapeError> {
        if v.len() != self.cols {
            return Err(FieldShapeError {
                got: v.len(),
                expected: self.cols,
            });
        }
        Ok((0..self.rows).map(|i| dot(self.row(i), v)).collect())
    }

    /// `A · B` over `R`.
    ///
    /// # Errors
    /// [`FieldShapeError`] unless `A.cols == B.rows`; the reported lengths are
    /// the two sides that disagreed.
    pub fn matmul(&self, other: &Self) -> Result<Self, FieldShapeError> {
        if self.cols != other.rows {
            return Err(FieldShapeError {
                got: other.rows,
                expected: self.cols,
            });
        }
        let data = (0..self.rows)
            .flat_map(|i| {
                (0..other.cols).map(move |j| {
                    let mut acc = R::ZERO;
                    for k in 0..self.cols {
                        acc = acc + self.data[i * self.cols + k] * other.data[k * other.cols + j];
                    }
                    acc
                })
            })
            .collect();
        Ok(Self {
            rows: self.rows,
            cols: other.cols,
            data,
        })
    }

    /// `(I_m ⊗ M) · v` — apply the same coefficient-level map to each of `m`
    /// consecutive blocks of `v`.
    ///
    /// This is CMNW Eq. (20): `e⃗` split into `r₁` blocks of `r₂nαd`
    /// coefficients, each projected independently to `λ` field elements.
    ///
    /// # Errors
    /// [`FieldShapeError`] unless `v.len() == blocks * self.cols`.
    pub fn project_blocks(&self, v: &[R], blocks: usize) -> Result<Vec<R>, FieldShapeError> {
        if v.len() != blocks * self.cols {
            return Err(FieldShapeError {
                got: v.len(),
                expected: blocks * self.cols,
            });
        }
        let mut out = Vec::with_capacity(blocks * self.rows);
        for block in v.chunks(self.cols) {
            out.extend_from_slice(&self.apply(block)?);
        }
        Ok(out)
    }
}

/// `Σ_k a_k·b_k` over `R`.
///
/// # Panics
/// If the vectors differ in length.
pub fn dot<R: Ring>(a: &[R], b: &[R]) -> R {
    assert_eq!(a.len(), b.len(), "coefficient dot needs equal lengths");
    let mut acc = R::ZERO;
    for (x, y) in a.iter().zip(b.iter()) {
        acc = acc + *x * *y;
    }
    acc
}

/// Flatten a ring vector to its coefficient vector (ascending powers, block by
/// block).
///
/// Each element contributes exactly `D` coefficients: [`PolyRing`] stores its
/// coefficients trimmed of trailing zeros, so a sparse element still occupies a
/// full ring slot here. Skipping that padding shifts every later block and
/// silently breaks the σ-pairing identity below.
pub fn to_coeffs<R: Ring, const D: usize>(v: &[PolyRing<R, D>]) -> Vec<R> {
    let mut out = Vec::with_capacity(v.len() * D);
    for p in v {
        let coeffs = p.coefficients();
        out.extend(coeffs.iter().copied());
        out.resize(out.len() + D - coeffs.len(), R::ZERO);
    }
    out
}

/// Inverse of [`to_coeffs`]: group `D` consecutive coefficients per ring
/// element, in ascending power order.
///
/// # Panics
/// If `scalars.len()` is not a multiple of `D`.
pub fn from_coeffs<R: Ring, const D: usize>(scalars: &[R]) -> Vec<PolyRing<R, D>> {
    assert!(
        !scalars.is_empty() && scalars.len() % D == 0,
        "coefficient count must be a non-empty multiple of the ring degree"
    );
    scalars
        .chunks(D)
        .map(|chunk| PolyRing::from_coefficients(chunk.to_vec()))
        .collect()
}

/// The constant coefficient of a ring element.
pub fn const_term<R: Ring, const D: usize>(p: &PolyRing<R, D>) -> R {
    p.coefficients()[0]
}

/// `Σ_l σ(n_l)·e_l` over the ring — the quantity CMNW Eq. (21) calls
/// `⟨σ₋₁(n), e⟩`.
///
/// Its constant term is the *coefficient-level* inner product
/// `⟨n⃗, e⃗⟩_{Z_q}` (see [`crate::pcs::packing::pairing_of`]), which is what
/// lets a prover that only knows `P` commit to a value the verifier can
/// recompute from `B` and `p⃗`.
///
/// # Panics
/// If the vectors differ in length.
pub fn sigma_pairing_vec<R: Ring, const D: usize>(
    n: &[PolyRing<R, D>],
    e: &[PolyRing<R, D>],
) -> PolyRing<R, D> {
    assert_eq!(
        n.len(),
        e.len(),
        "sigma pairing needs equal-length ring vectors"
    );
    let zero = PolyRing::from_coefficients(vec![R::ZERO; D]);
    n.iter()
        .zip(e.iter())
        .fold(zero, |acc, (a, b)| acc + sigma_of(a) * b.clone())
}

/// CMNW Eq. (21)–(22), the prover's side of the shortness triangle: the
/// `γ` stack.
///
/// `n_rows` are the rows `nᵢ` of `B·P` **already grouped into ring elements**
/// (see [`from_coeffs`]), `e_blocks` the `r₁` blocks `eⱼ` of the partial
/// witness. Entry `(i, j)` is `⟨σ(nᵢ), eⱼ⟩ = Σ_k σ(nᵢ[k])·eⱼ[k]`.
///
/// The output is laid out block-major: block `j` holds
/// `(γ_{1,j}, …, γ_{l,j})`, which is exactly the flattening Eq. (22) stacks, so
/// `(c₂ᵀ ⊗ I_l)·γ` is [`crate::pcs::mixed::BlockMat::contract_rows`] on it.
pub fn gamma_stack<R: Ring, const D: usize>(
    n_rows: &[&[PolyRing<R, D>]],
    e_blocks: &[&[PolyRing<R, D>]],
) -> Vec<PolyRing<R, D>> {
    e_blocks
        .iter()
        .flat_map(|e| n_rows.iter().map(move |n| sigma_pairing_vec(n, e)))
        .collect()
}

/// CMNW Eq. (22): the matrix `N ∈ R^{l×r₂nα}` whose row `i` is `σ(nᵢ)`, in
/// row-major order. With it, `γ_{i,j}` is the `(i, j)` entry of
/// `(I_{r₁} ⊗ N)·e`, which is what makes check (7) a plain ring-level product.
pub fn sigma_matrix<R: Ring, const D: usize>(n_rows: &[&[PolyRing<R, D>]]) -> Vec<PolyRing<R, D>> {
    n_rows
        .iter()
        .flat_map(|row| row.iter().map(sigma_of))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use algebra::ring::zq::Zq;

    /// CMNW/Hachi's regime: `2³² − 99` is prime and `≡ 5 (mod 8)`, so this
    /// instance has no NTT — every test here must pass without one.
    type Q5 = Zq<4294967197>;
    const D: usize = 8;

    fn ring_vec(seed: u64, len: usize) -> Vec<PolyRing<Q5, D>> {
        (0..len)
            .map(|i| {
                let coeffs: Vec<_> = (0..D)
                    .map(|k| {
                        let v = (seed as i64 * 31 + i as i64 * 7 + k as i64) % 11;
                        from_centered::<Q5>(v - 5)
                    })
                    .collect();
                PolyRing::from_coefficients(coeffs)
            })
            .collect()
    }

    fn field_vec(seed: u64, len: usize) -> Vec<Q5> {
        (0..len)
            .map(|i| {
                let v = (seed as i64 * 131 + i as i64 * 17) % 977;
                from_centered::<Q5>(v)
            })
            .collect()
    }

    #[test]
    fn dot_matches_a_hand_computed_value() {
        // 2·5 + (−3)·7 + 0·11 = −11, taken mod q.
        let a = [Q5::from(2), Q5::ZERO - Q5::from(3), Q5::ZERO];
        let b = [Q5::from(5), Q5::from(7), Q5::from(11)];
        assert_eq!(dot(&a, &b), Q5::ZERO - Q5::from(11));
    }

    #[test]
    #[should_panic(expected = "equal lengths")]
    fn dot_refuses_ragged_inputs() {
        dot(&[Q5::ONE], &[Q5::ONE, Q5::ONE]);
    }

    #[test]
    fn matmul_applies_the_same_way_as_two_applications() {
        // The protocol relies on `(I⊗B)·(I⊗P)·e⃗ = (I⊗B·P)·e⃗`, so the
        // un-blocked form must associate first.
        let p = FieldMat::<Q5>::ternary(b"p", &[7u8; 32], 5, 4);
        let b = FieldMat::<Q5>::uniform(b"b", &[9u8; 32], 3, 5);
        let e = field_vec(3, 4);
        let left = b.matmul(&p).expect("shapes").apply(&e).expect("shapes");
        let right = b.apply(&p.apply(&e).expect("shapes")).expect("shapes");
        assert_eq!(left, right);
    }

    #[test]
    fn project_blocks_matches_block_by_block_application() {
        let p = FieldMat::<Q5>::ternary(b"p", &[1u8; 32], 3, 4);
        let e = field_vec(11, 8);
        let folded = p.project_blocks(&e, 2).expect("shapes");
        let manual = [
            p.apply(&e[..4]).expect("shapes"),
            p.apply(&e[4..]).expect("shapes"),
        ]
        .concat();
        assert_eq!(folded, manual);
        // A wrong block count is refused rather than silently truncated.
        assert_eq!(
            p.project_blocks(&e, 3),
            Err(FieldShapeError {
                got: 8,
                expected: 12
            })
        );
    }

    #[test]
    fn ternary_entries_are_exactly_minus_one_zero_or_one() {
        let p = FieldMat::<Q5>::ternary(b"p", &[2u8; 32], 16, 16);
        let neg = Q5::ZERO - Q5::ONE;
        let mut seen = [0u32; 3];
        for i in 0..16 {
            for j in 0..16 {
                let v = *p.get(i, j).expect("in range");
                let idx = if v == Q5::ZERO {
                    0
                } else if v == Q5::ONE {
                    1
                } else if v == neg {
                    2
                } else {
                    panic!("projection entry {v:?} is outside {{-1,0,1}}")
                };
                seen[idx] += 1;
            }
        }
        // 256 draws over three values: each must actually occur, or the byte
        // reduction is broken in a way a single-cell assertion would hide.
        assert!(seen.iter().all(|&c| c > 20), "distribution {seen:?}");
    }

    #[test]
    fn labels_and_shapes_separate_the_streams() {
        let a = FieldMat::<Q5>::uniform(b"x", &[0u8; 32], 4, 4);
        let b = FieldMat::<Q5>::uniform(b"y", &[0u8; 32], 4, 4);
        assert_ne!(a.row(0), b.row(0));
        let wide = FieldMat::<Q5>::uniform(b"x", &[0u8; 32], 4, 5);
        assert_ne!(a.row(0), wide.row(0));
    }

    #[test]
    fn coefficient_grouping_round_trips() {
        let v = ring_vec(5, 6);
        assert_eq!(from_coeffs::<Q5, D>(&to_coeffs(&v)), v);
        let flat = field_vec(5, 6 * D);
        assert_eq!(to_coeffs(&from_coeffs::<Q5, D>(&flat)), flat);
    }

    /// `PolyRing` trims trailing zeros, so flattening must pad back to `D` per
    /// element or every later block shifts by the number of zeros dropped.
    #[test]
    fn flattening_pads_sparse_elements_to_a_full_ring_slot() {
        let sparse = vec![
            PolyRing::<Q5, D>::from_coefficients(vec![Q5::from(3)]),
            PolyRing::<Q5, D>::from_coefficients(vec![Q5::ONE, Q5::ZERO]),
        ];
        let flat = to_coeffs(&sparse);
        assert_eq!(flat.len(), 2 * D);
        assert_eq!(flat[0], Q5::from(3));
        assert!(flat[1..D].iter().all(|c| *c == Q5::ZERO));
        assert_eq!(from_coeffs::<Q5, D>(&flat), sparse);
    }

    #[test]
    #[should_panic(expected = "multiple of the ring degree")]
    fn grouping_refuses_a_partial_last_element() {
        from_coeffs::<Q5, D>(&field_vec(1, D - 1));
    }

    /// CMNW App. A, the sentence under Eq. (21): "the constant coefficient of
    /// `⟨σ₋₁(nᵢ), eⱼ⟩ ∈ R_q` is equal to `⟨b⃗ᵢ, p⃗_j⟩`".
    #[test]
    fn sigma_pairing_constant_term_is_the_coefficient_dot() {
        const R1: usize = 2; // block count, CMNW's r₁
        let p = FieldMat::<Q5>::ternary(b"p", &[3u8; 32], 6, 4 * D);
        let b = FieldMat::<Q5>::uniform(b"b", &[4u8; 32], 2, 6);
        let e_blocks = [ring_vec(6, 4), ring_vec(7, 4)];
        let e_flat = to_coeffs(&e_blocks.concat());

        // Verifier side: p⃗ = (I⊗P)·e⃗, then the field dot with each row of B.
        let projected = p.project_blocks(&e_flat, R1).expect("shapes");
        // Prover side: rows of B·P, read back as ring vectors.
        let bp = b.matmul(&p).expect("shapes");

        for i in 0..b.rows() {
            let n_ring = from_coeffs::<Q5, D>(bp.row(i));
            for j in 0..R1 {
                let gamma = sigma_pairing_vec(&n_ring, &e_blocks[j]);
                assert_eq!(
                    const_term(&gamma),
                    dot(b.row(i), &projected[j * p.rows()..(j + 1) * p.rows()]),
                    "check (d) fails on row {i}, block {j}"
                );
            }
        }
    }

    /// CMNW Eq. (22): the `γ` stack is the ring-level product with the matrix
    /// `N` whose rows are `σ(nᵢ)`, so each entry must agree with the
    /// independent ring-dot implementation in [`crate::pcs::mixed`].
    #[test]
    fn sigma_pairing_equals_the_ring_dot_of_the_sigma_row() {
        use crate::pcs::mixed::dot as ring_dot;
        for seed in 0..3u64 {
            let n = ring_vec(seed, 5);
            let e = ring_vec(seed + 100, 5);
            let sigma_row: Vec<PolyRing<Q5, D>> = n.iter().map(sigma_of).collect();
            assert_eq!(sigma_pairing_vec(&n, &e), ring_dot(&sigma_row, &e));
        }
    }

    #[test]
    #[should_panic(expected = "equal-length ring vectors")]
    fn sigma_pairing_refuses_mismatched_vectors() {
        sigma_pairing_vec(&ring_vec(1, 3), &ring_vec(2, 4));
    }

    /// Eq. (22): the block-major `γ` stack is the ring-level product
    /// `(I_{r₁} ⊗ N)·e` with `N` the σ-row matrix — checked against the
    /// independent [`BlockMat`] contraction.
    #[test]
    fn gamma_stack_is_the_tensor_product_of_the_sigma_matrix() {
        use crate::pcs::mixed::BlockMat;
        let n_rows = [ring_vec(1, 4), ring_vec(2, 4)];
        let e_blocks = [ring_vec(3, 4), ring_vec(4, 4)];
        let n_refs: Vec<&[PolyRing<Q5, D>]> = n_rows.iter().map(|r| r.as_slice()).collect();
        let e_refs: Vec<&[PolyRing<Q5, D>]> = e_blocks.iter().map(|r| r.as_slice()).collect();

        let gamma = gamma_stack(&n_refs, &e_refs);
        let n_mat = BlockMat::<Q5, D>::new(n_rows.len(), 4, sigma_matrix(&n_refs)).expect("shapes");
        let expected = [
            n_mat.contract_cols(&e_blocks[0]).expect("shapes"),
            n_mat.contract_cols(&e_blocks[1]).expect("shapes"),
        ]
        .concat();
        assert_eq!(gamma, expected);
        assert_eq!(gamma.len(), n_rows.len() * e_blocks.len());
    }

    #[test]
    fn matmul_reports_the_disagreeing_dimension() {
        let a = FieldMat::<Q5>::uniform(b"a", &[0u8; 32], 2, 3);
        let b = FieldMat::<Q5>::uniform(b"b", &[0u8; 32], 4, 2);
        assert_eq!(
            a.matmul(&b),
            Err(FieldShapeError {
                got: 4,
                expected: 3
            })
        );
    }
}
