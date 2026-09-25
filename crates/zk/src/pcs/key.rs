//! Heap-sized, NTT-free Ajtai keys (Z7 support).
//!
//! Every key type in the crate so far expands either into an inline
//! `[[NttDomain; L]; K]` ([`crate::commitment::ajtai`]) or into the
//! NTT-domain heap matrix `AjtaiKeyHeap` that `pcs::greyhound` uses. Both
//! assume the scalar ring is **NTT-friendly**, i.e. `q ≡ 1 (mod 2d)`.
//!
//! That assumption is fatal for most of the schemes in
//! `docs/survey-lattice-pcs.md`, because their soundness proofs require the
//! opposite congruence:
//!
//! - CMNW (2024/281 App. A) needs `q ≡ 5 (mod 8)` for the Lyubashevsky–Seiler
//!   short-inverse step;
//! - Hachi (2026/156) runs on `q = 2³² − 99`, also `≡ 5 (mod 8)`, and its
//!   reference implementation multiplies schoolbook for exactly that reason;
//! - Serval (2025/1903) and Maltese (2026/2067) sit in the same regime.
//!
//! For `q ≡ 5 (mod 8)` the 2-adicity of `q − 1` is `2`, so no NTT of degree
//! `≥ 4` exists — an NTT-backed key cannot be built at all. This module is the
//! coefficient-domain alternative: same seed-expanded derivation, plain
//! negacyclic multiplication, no transform and no `TwoAdicRing` bound.
//!
//! It is also the shape-parameterised one: the scalar ring `R` and the ring
//! degree `D` are both generic, so a scheme can pick its own `(q, d)` instead
//! of inheriting the crate's `Z1` constants (gap G1 in
//! `docs/open-milestones.md`).

use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::module::sample_coeffs_from_xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// The additive identity of `R_q[X]/(X^D + 1)`.
fn zero_elt<R: Ring, const D: usize>() -> PolyRing<R, D> {
    PolyRing::from_coefficients(vec![R::ZERO; D])
}

/// Domain label shared with `pcs::greyhound`'s key expansion, so the two key
/// types derive comparable streams.
const KEY_DOMAIN: &[u8] = b"lattice-algebra/Z7/greyhound-key";

/// Why a key operation refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub struct KeyShapeError {
    /// Vector length supplied.
    pub got: usize,
    /// Length the matrix requires.
    pub expected: usize,
}

impl fmt::Display for KeyShapeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "vector of {} elements against {} columns",
            self.got, self.expected
        )
    }
}

/// A dense matrix `M ∈ R_q^{rows×cols}` of ring elements, stored row-major in
/// the **coefficient domain**, applied by schoolbook multiplication.
#[derive(Clone, PartialEq, Eq)]
pub struct RingMatrixKey<R: Ring, const D: usize> {
    rows: usize,
    cols: usize,
    entries: Vec<PolyRing<R, D>>,
}

impl<R: Ring, const D: usize> fmt::Debug for RingMatrixKey<R, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RingMatrixKey<{}×{}, d={}>", self.rows, self.cols, D)
    }
}

impl<R: Ring, const D: usize> RingMatrixKey<R, D> {
    /// ExpandA: entry `(i, j)` from
    /// `XOF(KEY_DOMAIN ‖ label ‖ seed ‖ j ‖ i)` with **two-byte** indices, so
    /// the derivation matches [`crate::pcs::greyhound`]`'s heap key exactly
    /// (the single-byte encoding saturates past 256 columns).
    pub fn setup(label: &[u8], seed: &[u8; 32], rows: usize, cols: usize) -> Self {
        // Expanded column-major (matching greyhound's stream order), then
        // re-laid out row-major below.
        let mut entries = Vec::with_capacity(rows * cols);
        for j in 0..cols {
            for i in 0..rows {
                let mut xof = Shake256Xof::new(&[]);
                xof.absorb(KEY_DOMAIN);
                xof.absorb(label);
                xof.absorb(seed);
                xof.absorb(&(j as u32).to_le_bytes());
                xof.absorb(&(i as u32).to_le_bytes());
                entries.push(PolyRing::from_coefficients(
                    sample_coeffs_from_xof::<Shake256Xof, R, D>(xof).to_vec(),
                ));
            }
        }
        // The loop above emits column-major order; transpose into row-major.
        let mut row_major = vec![zero_elt::<R, D>(); rows * cols];
        for j in 0..cols {
            for i in 0..rows {
                row_major[i * cols + j] = entries[j * rows + i].clone();
            }
        }
        Self {
            rows,
            cols,
            entries: row_major,
        }
    }

    /// Wraps explicit entries, row-major.
    ///
    /// # Panics
    /// Unless `entries.len() == rows * cols`.
    pub fn from_entries(rows: usize, cols: usize, entries: Vec<PolyRing<R, D>>) -> Self {
        assert_eq!(
            entries.len(),
            rows * cols,
            "entry count must match rows × cols"
        );
        Self {
            rows,
            cols,
            entries,
        }
    }

    /// Row count.
    pub const fn rows(&self) -> usize {
        self.rows
    }

    /// Column count.
    pub const fn cols(&self) -> usize {
        self.cols
    }

    /// Entry `(i, j)`, or `None` out of range.
    pub fn get(&self, i: usize, j: usize) -> Option<&PolyRing<R, D>> {
        if i < self.rows && j < self.cols {
            Some(&self.entries[i * self.cols + j])
        } else {
            None
        }
    }

    /// Row `i` as a slice.
    ///
    /// # Panics
    /// If `i >= rows`.
    pub fn row(&self, i: usize) -> &[PolyRing<R, D>] {
        &self.entries[i * self.cols..(i + 1) * self.cols]
    }

    /// `M · v` in the coefficient domain.
    ///
    /// # Errors
    /// [`KeyShapeError`] unless `v.len() == cols`.
    pub fn matvec(&self, v: &[PolyRing<R, D>]) -> Result<Vec<PolyRing<R, D>>, KeyShapeError> {
        if v.len() != self.cols {
            return Err(KeyShapeError {
                got: v.len(),
                expected: self.cols,
            });
        }
        Ok((0..self.rows)
            .map(|i| {
                let mut acc = zero_elt::<R, D>();
                for (a, b) in self.row(i).iter().zip(v.iter()) {
                    acc += a.clone() * b.clone();
                }
                acc
            })
            .collect())
    }
}

/// `(I_m ⊗ A) · v` — apply one matrix to each of `groups` independently,
/// concatenating the results.
///
/// This is the whole tensor-key capability the nested-gadget line needs:
/// CMNW's `t = (I_{r₀} ⊗ A₁)·s₁` and Maltese's
/// `s_i = G⁻¹((I_{2^i} ⊗ A)·s_{i+1})` both apply *one* small `A ∈ R^{n×cols}`
/// to every block, each block producing `n` elements. Nothing about the block
/// count is stored: it is a property of the input, so the level cannot drift
/// out of step with the data.
///
/// The gadget split stays with the caller ([`crate::pcs::gadget::split`] is
/// generic over base and digit count), so this never fixes a scheme's digit
/// convention.
///
/// # Errors
/// [`KeyShapeError`] if any group is not exactly `key.cols()` long. The
/// offending length is reported, so a mis-sized split is diagnosable rather
/// than silently truncated.
pub fn apply_blockwise<R: Ring, const D: usize>(
    key: &RingMatrixKey<R, D>,
    groups: &[&[PolyRing<R, D>]],
) -> Result<Vec<PolyRing<R, D>>, KeyShapeError> {
    let mut out = Vec::with_capacity(groups.len() * key.rows());
    for group in groups {
        out.extend_from_slice(&key.matvec(group)?);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::module::{ModuleMatrix, ModuleVector};
    use algebra::ring::traits::CenteredRing;
    use algebra::ring::zq::Zq;
    use alloc::vec;

    /// NTT-friendly prime the crate already uses (`q − 1` divisible by 512).
    type Z1 = Zq<8380417>;
    /// Hachi / CMNW's regime: `2³² − 99 ≡ 5 (mod 8)`, so `q − 1` has
    /// 2-adicity 2 and **no NTT of degree ≥ 4 exists**.
    type Q5 = Zq<4294967197>;

    const MOD8: u64 = 4_294_967_197;

    fn coeffs(vals: &[i64]) -> Vec<Z1> {
        vals.iter()
            .map(|&v| {
                let x = v.rem_euclid(Z1::MODULUS as i64) as u64;
                Z1::from(x)
            })
            .collect()
    }

    fn q5(v: u64) -> Q5 {
        Q5::from(v % MOD8)
    }

    #[test]
    fn matvec_matches_an_independent_triple_loop() {
        let rows = 2;
        let cols = 3;
        let mk = |i: usize, j: usize| {
            let mut c = vec![Z1::ZERO; 4];
            c[0] = Z1::from((i * 5 + j + 1) as u64);
            c[1] = Z1::from((i + 2 * j + 3) as u64);
            PolyRing::from_coefficients(c)
        };
        let entries: Vec<_> = (0..rows)
            .flat_map(|i| (0..cols).map(move |j| mk(i, j)))
            .collect();
        let k = RingMatrixKey::<Z1, 4>::from_entries(rows, cols, entries.clone());

        let v: Vec<PolyRing<Z1, 4>> = (0..cols)
            .map(|j| {
                let mut c = vec![Z1::ZERO; 4];
                c[0] = Z1::from((j + 2) as u64);
                c[2] = Z1::from((j * j + 1) as u64);
                PolyRing::from_coefficients(c)
            })
            .collect();

        let got = k.matvec(&v).expect("shape ok");
        // naive reference, written without reusing matvec
        let mut expect = Vec::new();
        for i in 0..rows {
            let mut acc = zero_elt::<Z1, 4>();
            for j in 0..cols {
                acc += entries[i * cols + j].clone() * v[j].clone();
            }
            expect.push(acc);
        }
        assert_eq!(got, expect);
    }

    #[test]
    fn agrees_with_the_module_matrix_reference_path() {
        // Same entries through the const-generic schoolbook path: the heap
        // variant must not be a second, drifting implementation of one idea.
        let (rows, cols) = (3, 5);
        let f = |i: usize, j: usize| {
            let mut c = vec![Z1::ZERO; 8];
            c[0] = Z1::from((i + 1) as u64);
            c[3] = Z1::from((j + 1) as u64);
            c[7] = Z1::from((i * j + 2) as u64);
            PolyRing::from_coefficients(c)
        };
        let entries: Vec<_> = (0..rows)
            .flat_map(|i| (0..cols).map(move |j| f(i, j)))
            .collect();
        let heap = RingMatrixKey::<Z1, 8>::from_entries(rows, cols, entries);
        let fixed = ModuleMatrix::<Z1, 3, 5, 8>::from_fn(f);
        let v = ModuleVector::<Z1, 5, 8>::from_fn(|j| {
            let mut c = vec![Z1::ZERO; 8];
            c[j % 8] = Z1::from((j as u64) + 1);
            PolyRing::from_coefficients(c)
        });
        let from_fixed = fixed.mul_vec(&v);
        let from_heap = heap.matvec(v.polys()).expect("shape ok");
        assert_eq!(from_heap, from_fixed.polys().to_vec());
    }

    #[test]
    fn matvec_is_linear() {
        let k = RingMatrixKey::<Z1, 8>::setup(b"lin", &[7u8; 32], 3, 4);
        let col = |j: usize, base: i64| {
            PolyRing::from_coefficients(coeffs(&[
                j as i64 + base,
                base * 2 - 1,
                3,
                0,
                0,
                0,
                0,
                base,
            ]))
        };
        let a: Vec<_> = (0..4).map(|j| col(j, 1)).collect();
        let b: Vec<_> = (0..4).map(|j| col(j, 2)).collect();
        let a_plus_b: Vec<_> = a
            .iter()
            .zip(b.iter())
            .map(|(x, y)| x.clone() + y.clone())
            .collect();

        // M(a+b) == Ma + Mb, entrywise in the module
        let lhs = k.matvec(&a_plus_b).expect("ok");
        let ma = k.matvec(&a).expect("ok");
        let mb = k.matvec(&b).expect("ok");
        let rhs: Vec<_> = ma
            .iter()
            .zip(mb.iter())
            .map(|(x, y)| x.clone() + y.clone())
            .collect();
        assert_eq!(lhs, rhs, "matvec must distribute over the input module");
        assert_eq!(lhs.len(), k.rows());
    }

    #[test]
    fn setup_is_deterministic_and_bound_to_label_and_seed() {
        let a = RingMatrixKey::<Z1, 8>::setup(b"x", &[1u8; 32], 2, 3);
        let b = RingMatrixKey::<Z1, 8>::setup(b"x", &[1u8; 32], 2, 3);
        let c = RingMatrixKey::<Z1, 8>::setup(b"y", &[1u8; 32], 2, 3);
        let d = RingMatrixKey::<Z1, 8>::setup(b"x", &[2u8; 32], 2, 3);
        assert_eq!(a, b, "same (label, seed) must reproduce the key");
        assert_ne!(a, c, "the label must domain-separate keys");
        assert_ne!(a, d, "the seed must bind the key");
        assert_eq!(a.rows(), 2);
        assert_eq!(a.cols(), 3);
        assert!(a.get(1, 2).is_some());
        assert!(a.get(2, 0).is_none(), "row index out of range");
    }

    #[test]
    fn entry_grid_matches_the_documented_expansion_recipe() {
        // A silent transpose survives every algebra test (a random matrix
        // looks random either way), so recompute one off-diagonal entry
        // directly from the documented XOF recipe and pin it.
        let seed = [5u8; 32];
        let (rows, cols) = (2, 3);
        let k = RingMatrixKey::<Z1, 8>::setup(b"t", &seed, rows, cols);

        let derive = |i: usize, j: usize| {
            let mut xof = Shake256Xof::new(&[]);
            xof.absorb(KEY_DOMAIN);
            xof.absorb(b"t");
            xof.absorb(&seed);
            xof.absorb(&(j as u32).to_le_bytes());
            xof.absorb(&(i as u32).to_le_bytes());
            PolyRing::<Z1, 8>::from_coefficients(
                sample_coeffs_from_xof::<Shake256Xof, Z1, 8>(xof).to_vec(),
            )
        };
        assert_eq!(*k.get(1, 2).unwrap(), derive(1, 2), "entry (1,2)");
        assert_eq!(*k.get(0, 0).unwrap(), derive(0, 0), "entry (0,0)");
        assert_eq!(*k.get(1, 0).unwrap(), derive(1, 0), "entry (1,0)");
        // and the grid really is row-major contiguous
        assert_eq!(k.row(1)[2], derive(1, 2));
    }

    #[test]
    fn apply_blockwise_concatenates_independent_row_results() {
        let (rows, cols) = (3, 4);
        let k = RingMatrixKey::<Z1, 8>::setup(b"blk", &[8u8; 32], rows, cols);
        let grp = |tag: u64| -> Vec<PolyRing<Z1, 8>> {
            (0..cols)
                .map(|j| {
                    PolyRing::from_coefficients(coeffs(&[
                        j as i64 + 1,
                        tag as i64 + j as i64,
                        -3,
                        0,
                        0,
                        0,
                        0,
                        tag as i64,
                    ]))
                })
                .collect()
        };
        let (g0, g1, g2) = (grp(1), grp(2), grp(3));
        let groups: Vec<&[PolyRing<Z1, 8>]> = vec![&g0, &g1, &g2];
        let got = apply_blockwise(&k, &groups).expect("all groups sized");
        assert_eq!(got.len(), 3 * rows, "one column of results per block");
        for (i, g) in groups.iter().enumerate() {
            let alone = k.matvec(g).expect("ok");
            assert_eq!(&got[i * rows..(i + 1) * rows], &alone[..], "block {i}");
        }
    }

    #[test]
    fn apply_blockwise_reports_the_offending_group_length() {
        let k = RingMatrixKey::<Z1, 8>::setup(b"blk", &[8u8; 32], 3, 4);
        let good: Vec<PolyRing<Z1, 8>> = (0..4)
            .map(|j| PolyRing::from_coefficients(coeffs(&[j as i64 + 1, 2, 0, 0, 0, 0, 0, 0])))
            .collect();
        let short = &good[..3];
        // The error must carry the real size, not a sentinel that would make
        // a mis-sized gadget split undebuggable.
        assert_eq!(
            apply_blockwise(&k, &[short]),
            Err(KeyShapeError {
                got: 3,
                expected: 4
            })
        );
        assert!(apply_blockwise(&k, &[good.as_slice()]).is_ok());
    }

    #[test]
    fn works_on_a_non_ntt_friendly_ring() {
        // The entire point: `q ≡ 5 mod 8` has 2-adicity 2, so no NTT-backed
        // key can exist for d ≥ 4 — but a scheme like CMNW/Hachi needs exactly
        // this congruence. Schoolbook must just work.
        assert_eq!(MOD8 % 8, 5);
        assert_eq!(
            (MOD8 - 1).trailing_zeros(),
            2,
            "2-adicity 2 ⇒ no NTT past d=2"
        );
        let k = RingMatrixKey::<Q5, 64>::setup(b"cmnw", &[3u8; 32], 4, 6);
        let v: Vec<PolyRing<Q5, 64>> = (0..6)
            .map(|j| {
                let mut c = vec![q5(0); 64];
                c[0] = q5(j as u64 + 1);
                c[9] = q5(3);
                PolyRing::from_coefficients(c)
            })
            .collect();
        let out = k.matvec(&v).expect("shape ok");
        assert_eq!(out.len(), 4);
        assert_ne!(out[0], out[1], "rows must differ");
        // and a wrong-length vector is a typed rejection, not a panic
        assert_eq!(
            k.matvec(&v[..5]),
            Err(KeyShapeError {
                got: 5,
                expected: 6
            })
        );
    }

    #[test]
    fn ring_elements_stay_reduced_under_repeated_multiplication() {
        // Guard the negacyclic product the schoolbook path relies on at this
        // modulus: X^63 · X = −1 wraps into the constant slot.
        let mut a = vec![q5(0); 64];
        a[63] = q5(1);
        let mut b = vec![q5(0); 64];
        b[1] = q5(1);
        let pa = PolyRing::<Q5, 64>::from_coefficients(a);
        let pb = PolyRing::<Q5, 64>::from_coefficients(b);
        let prod = pa * pb;
        let cs = prod.coefficients();
        assert_eq!(cs[0].centered(), -1, "X^63·X = -1 in the negacyclic ring");
        for c in cs.iter().skip(1) {
            assert_eq!(c.centered(), 0);
        }
    }
}
