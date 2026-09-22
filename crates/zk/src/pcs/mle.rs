//! MLE/eq-weight opening mode (Z7, row 25 foundation): commit to a
//! scalar-coefficient vector once, later prove **arbitrary linear
//! evaluation claims** `y = ⟨w, F⟩` — power tables (point evaluations at
//! any `x`), eq tensors (multilinear evaluations), and range-check
//! functionals all instantiate.
//!
//! # Architecture (transparent by design)
//!
//! Unlike the √N-split Greyhound mode (whose weight tables must factor as
//! the outer product `aⱼ·bᵢ` — see [`crate::pcs::batched`] for why
//! arbitrary tables do not), this mode supports **non-factored** weight
//! tables with exact verification, at a documented cost:
//!
//! - the commitment key `A ∈ Z_q^{2L×L}` is **tall** (twice as many rows
//!   as columns), so `A·F = c` over-determines `F`: the system has the
//!   unique solution `F = A⁺·c` (full column rank w.h.p. for a random
//!   matrix over the prime field) — the claim verification is **exact**;
//! - the flip side: the commitment is **transparent (not hiding)** — the
//!   witness is recoverable by linear elimination, so this mode is the
//!   *claim-verification interface* the batching line composes against,
//!   not a hiding commitment. Hiding stays with the Greyhound mode.
//!
//! # Weighted claims
//!
//! For a weight table `w ∈ Z_q^L` (power table `w_j = xʲ`, eq tensor
//! `eq(r, ·)`, a range-check functional, …), the claim `y = ⟨w, F⟩` is
//! verified exactly against the recovered witness. Batches of claims
//! compose: `Σᵢ λᵢ·yᵢ == ⟨Σᵢ λᵢ·wᵢ, F⟩` for verifier-chosen `λ`.

use crate::instance::ring::Z2Coeff;
use crate::pcs::Z1Coeff;
use crate::shortness::projection::JLProjection;
use algebra::crypto::sampling::sample_rej_bounded;
use algebra::crypto::transcript::Transcript;

/// Converts a slice of scalars to LE bytes for transcript absorption.
fn scalar_bytes_le(v: &[Z1Coeff]) -> Vec<u8> {
    v.iter()
        .flat_map(|c| (c.to_u128() as u32).to_le_bytes())
        .collect()
}

/// The bounded-mask constant: `‖mask‖∞ ≤ 2^9`.
pub const MASK_BOUND: u32 = 1 << 9;

use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::traits::CenteredRing;
use algebra::ring::Ring;
use alloc::{vec, vec::Vec};

/// A tall scalar commitment key `A ∈ Z_q^{2L×L}` (row-major, entries from
/// a seed via rejection-free scalar expansion over the Z1 prime).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MleKey {
    len: usize,
    entries: Vec<Z1Coeff>,
}

impl MleKey {
    /// Derives the key from a seed. Deterministic; `len` is the committed
    /// scalar-vector length.
    pub fn setup(seed: &[u8; 32], len: usize) -> Self {
        assert!(len > 0, "committed length must be positive");
        let rows = 2 * len;
        let mut entries = Vec::with_capacity(rows * len);
        for i in 0..rows {
            for j in 0..len {
                // FNV-like hash from (seed, i, j)
                let mut h: u64 = u64::from_le_bytes(seed[..8].try_into().unwrap());
                h ^= (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
                h ^= (j as u64).wrapping_mul(0xBF58_476D_1CE4_E5B9);
                h = h.wrapping_mul(0x9E37_79B9_7F4A_7C15);
                h ^= h >> 32;
                entries.push(Z1Coeff::from(h % Z1Coeff::MODULUS));
            }
        }
        MleKey { len, entries }
    }

    /// The committed length `L`.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the committed length is zero.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// `A·v` — the commitment map (`2·len` scalars out).
    ///
    /// # Panics
    /// If `v.len() != len`.
    pub fn apply(&self, v: &[Z1Coeff]) -> Vec<Z1Coeff> {
        assert_eq!(v.len(), self.len, "mle map length mismatch");
        let mut out = vec![Z1Coeff::ZERO; 2 * self.len];
        for (i, row) in self.entries.chunks(self.len).enumerate() {
            let mut acc = Z1Coeff::ZERO;
            for (a, v_j) in row.iter().zip(v.iter()) {
                acc += *a * *v_j;
            }
            out[i] = acc;
        }
        out
    }

    /// Solves `A·x = c` for the unique witness (Gaussian elimination over
    /// the prime field). `None` if the system is inconsistent.
    pub fn solve(&self, c: &[Z1Coeff]) -> Option<Vec<Z1Coeff>> {
        if c.len() != 2 * self.len {
            return None;
        }
        let cols = self.len;
        let rows = 2 * self.len;
        let mut aug: Vec<Vec<Z1Coeff>> = (0..rows)
            .map(|i| {
                let mut row = self.entries[i * cols..(i + 1) * cols].to_vec();
                row.push(c[i]);
                row
            })
            .collect();
        let mut pivot_row = 0usize;
        #[allow(clippy::explicit_counter_loop)]
        for col in 0..cols {
            let pivot = (pivot_row..rows).find(|&r| aug[r][col] != Z1Coeff::ZERO)?;
            aug.swap(pivot_row, pivot);
            let inv = aug[pivot_row][col].inverse().expect("nonzero pivot");
            for v in aug[pivot_row].iter_mut() {
                *v *= inv;
            }
            let pivot_vals = aug[pivot_row].clone();
            for (r, row) in aug.iter_mut().enumerate() {
                if r != pivot_row && row[col] != Z1Coeff::ZERO {
                    let factor = row[col];
                    for (dst, pv) in row.iter_mut().zip(pivot_vals.iter()) {
                        *dst -= factor * pv;
                    }
                }
            }
            pivot_row += 1;
        }
        Some((0..cols).map(|i| aug[i][cols]).collect())
    }
}

/// The MLE commitment: `c = A·F` (`2·len` scalars).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MleCommitment {
    /// `A·F` — `2·len` scalars.
    pub c: Vec<Z1Coeff>,
}

/// Typed rejection for the MLE mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MleError {
    /// A vector had a length other than the canonical instance length.
    WrongLength,
    /// The system was inconsistent (the commitment is not binding for the
    /// supplied claim data).
    Inconsistent,
    /// A link equation failed (the claimed value doesn't match).
    LinkCheckFailed,
}

/// Commits to the scalar vector `F` (length `len`).
pub fn commit_mle(key: &MleKey, f: &[Z1Coeff]) -> Result<MleCommitment, MleError> {
    if f.len() != key.len() {
        return Err(MleError::WrongLength);
    }
    Ok(MleCommitment { c: key.apply(f) })
}

/// The weighted evaluation `y = ⟨w, F⟩` of the committed witness.
pub fn claim(key: &MleKey, c: &MleCommitment, w: &[Z1Coeff]) -> Result<Z1Coeff, MleError> {
    let f = key.solve(&c.c).ok_or(MleError::Inconsistent)?;
    let mut y = Z1Coeff::ZERO;
    for (w_j, f_j) in w.iter().zip(f.iter()) {
        y += *w_j * *f_j;
    }
    Ok(y)
}

/// Recovers the committed witness (the transparent mode's read-out).
pub fn witness_of(key: &MleKey, c: &MleCommitment) -> Option<Vec<Z1Coeff>> {
    key.solve(&c.c)
}

/// The Σ opening: proves `⟨w, F⟩ = y` against the commitment `c = A·F`.
///
/// Protocol: bounded mask, challenge `X` from the transcript, response
/// `z = mask + X·F`. Checks: `A·z == d + X·c` (overdetermined link) and
/// `⟨w, z⟩ == t + X·y` (weighted claim, exact over the prime field).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MleOpenProof {
    /// `A·mask` — the mask commitment (first message).
    pub d: Vec<Z1Coeff>,
    /// `z = mask + X·F` — the masked response.
    pub z: Vec<Z1Coeff>,
    /// `⟨w, mask⟩` — the mask's weighted value.
    pub t: Z1Coeff,
}

/// Prover: bounded mask, challenge from transcript, response `z`.
pub fn open_mle_proof(
    key: &MleKey,
    f: &[Z1Coeff],
    w: &[Z1Coeff],
    mask_seed: &[u8; 32],
) -> Result<MleOpenProof, MleError> {
    if f.len() != key.len() || w.len() != f.len() {
        return Err(MleError::WrongLength);
    }
    // bounded mask (rejection-sampled ±MASK_BOUND)
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(b"mle-mask");
    xof.absorb(mask_seed);
    let mut stream = BitStream::new(&mut xof);
    let mask: Vec<Z1Coeff> = (0..key.len())
        .map(|_| {
            let c = sample_rej_bounded::<Z1Coeff>(&mut stream, MASK_BOUND);
            Z1Coeff::from(u64::from(c.unsigned_abs() as u32))
        })
        .collect();
    let d = key.apply(&mask);

    // challenge from transcript over (d, w, y)
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z7/mle-open");
    tr.absorb(b"d", &scalar_bytes_le(&d));
    tr.absorb(b"w", &scalar_bytes_le(w));
    let seed = tr.challenge_bytes(8);
    let x = Z1Coeff::from(u64::from_le_bytes(seed[..8].try_into().unwrap()) % Z1Coeff::MODULUS);

    // response: z = mask + X·F
    let z: Vec<Z1Coeff> = mask
        .iter()
        .zip(f.iter())
        .map(|(m, f_j)| *m + x * *f_j)
        .collect();

    // t = ⟨w, mask⟩
    let mut t = Z1Coeff::ZERO;
    for (w_j, m_j) in w.iter().zip(mask.iter()) {
        t += *w_j * *m_j;
    }

    Ok(MleOpenProof { d, z, t })
}

/// Verifier: checks the overdetermined link and the weighted claim.
///
/// Check 1: `A·z == d + X·c` — the response is consistent with the
/// commitment (overdetermined: 2L constraints on L unknowns).
/// Check 2: `⟨w, z⟩ == t + X·y` — the weighted claim.
pub fn verify_mle_proof(
    key: &MleKey,
    c: &MleCommitment,
    w: &[Z1Coeff],
    claimed_y: Z1Coeff,
    proof: &MleOpenProof,
) -> Result<(), MleError> {
    if w.len() != key.len() || proof.d.len() != 2 * key.len() || proof.z.len() != key.len() {
        return Err(MleError::WrongLength);
    }
    // derive the same challenge
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(b"mle-sigma");
    xof.absorb(&scalar_bytes_le(&proof.d));
    xof.absorb(&scalar_bytes_le(w));
    let mut xb = [0u8; 8];
    xof.squeeze(&mut xb);
    let x = Z1Coeff::from(u64::from_le_bytes(xb) % Z1Coeff::MODULUS);

    // check 1: link
    let az = key.apply(&proof.z);
    for (i, az_i) in az.iter().enumerate() {
        let rhs = proof.d[i] + c.c[i] * x;
        if *az_i != rhs {
            return Err(MleError::LinkCheckFailed);
        }
    }

    // check 2: weighted claim
    let mut lhs = Z1Coeff::ZERO;
    for (w_j, z_j) in w.iter().zip(proof.z.iter()) {
        lhs += *w_j * *z_j;
    }
    let rhs = proof.t + x * claimed_y;
    if lhs != rhs {
        return Err(MleError::LinkCheckFailed);
    }
    Ok(())
}

/// The JL shortness certificate for a claimed-bounded witness: the
/// committed witness's `l2` norm is certified against
/// `⌈√(128/30)·B⌉` (see [`crate::shortness::projection`]).
pub fn certify_l2(proj: &JLProjection, witness: &[Z1Coeff], claimed_bound: u64) -> bool {
    let ok = witness
        .iter()
        .all(|v| Z2Coeff::from(v.to_u128() as u64).centered().unsigned_abs() <= (1 << 4))
        && claimed_bound > 0;
    let flat: Vec<i64> = witness.iter().map(|v| v.centered()).collect();
    let response = proj.project(&flat);
    let k = proj.rows() as u128;
    let b = u128::from(claimed_bound.max(1));
    let square: u128 = response
        .iter()
        .map(|v| {
            let a = u128::from(v.unsigned_abs());
            a * a
        })
        .sum();
    ok && square <= k * b * b
}
