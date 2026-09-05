//! Ajtai/SIS commitments `C = A·s` with short openings (L5, Z1).
//!
//! The commitment key `A ∈ R_q^{K×L}` is derived deterministically from a
//! seed via `ExpandA` and stays resident in the NTT domain. Opening to two
//! different short vectors `s ≠ s'` with the same commitment yields the
//! short kernel vector `s − s'` of `A`, which breaks Module-SIS — binding
//! is therefore parameterized by the MSIS instance
//! `(q, K, L, ‖·‖∞ ≤ 2·B_S)` (see the slack analysis in the Z1 docs).

use crate::crypto::xof::Shake128Xof;
use crate::module::ModuleMatrixNtt;
use crate::module::ModuleVector;
use crate::ntt::NttOperatorOptimized;
use crate::ring::poly_ring::PolyRing;
use crate::ring::zq::Zq;
use crate::ring::PolynomialQuotientRing;
use crate::ring::Ring;
use std::marker::PhantomData;

/// Ring shared by the Z1 instances: the ML-DSA ring.
pub type Z1Ring = Zq<8380417>;
/// Ring dimension.
pub const RING_DIM: usize = 256;
/// Modulus.
pub const Q: i64 = 8_380_417;

/// Scalar parameters of a commitment/Σ-protocol instance.
///
/// Norm accounting (full slack analysis in the Z1 docs):
/// - witnesses satisfy `‖s‖∞ ≤ B_S`;
/// - masks satisfy `‖y‖∞ < B_Y` (power of two);
/// - challenges have `TAU` non-zero ±1 coefficients → `‖c·s‖∞ ≤ TAU·B_S`;
/// - responses satisfy `‖z‖∞ ≤ B_Z = B_Y − TAU·B_S` (prover rejection loop).
pub trait SisParams: 'static {
    /// Challenge non-zero count.
    const TAU: u32;
    /// Witness coefficient bound.
    const B_S: i64;
    /// Mask coefficient bound (power of two).
    const B_Y: i64;

    /// Response bound `B_Y − TAU·B_S`.
    const B_Z: i64 = Self::B_Y - (Self::TAU as i64) * Self::B_S;
}

/// The Z1 research instance on the ML-DSA ring. Module dimensions are const
/// generics at the type level (`Z1Key<K, L>`); parameter sizing must be
/// confirmed with the lattice-estimator before any security claim.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Z1Instance;

impl SisParams for Z1Instance {
    const TAU: u32 = 39;
    const B_S: i64 = 4;
    const B_Y: i64 = 1 << 19;
}

/// Ajtai commitment key: `Â ∈ R_q^{K×L}` (NTT domain, resident) derived
/// from a seed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CommitmentKey<P: SisParams, const K: usize, const L: usize, const N: usize> {
    a_hat: ModuleMatrixNtt<Z1Ring, K, L, N>,
    seed: [u8; 32],
    _p: PhantomData<P>,
}

/// Commitment scheme trait: `C = A·s` for short `s`.
///
/// `Self` is the commitment key; `K`/`L`/`N` are the module dimensions of
/// the key type.
pub trait LatticeCommitment<R: Ring, const K: usize, const L: usize, const N: usize>:
    Sized
{
    /// The opening witness vector type (short module vector).
    type Witness;
    /// The commitment value type.
    type Commitment;

    /// Derives the public commitment key from a seed.
    fn setup(seed: &[u8; 32]) -> Self;

    /// `C ← A·s`.
    fn commit(&self, s: &Self::Witness) -> Self::Commitment;
}

impl<P: SisParams, const K: usize, const L: usize, const N: usize>
    LatticeCommitment<Z1Ring, K, L, N> for CommitmentKey<P, K, L, N>
{
    type Witness = ModuleVector<Z1Ring, L, N>;
    type Commitment = ModuleVector<Z1Ring, K, N>;

    fn setup(seed: &[u8; 32]) -> Self {
        Self {
            a_hat: ModuleMatrixNtt::expand_from_seed::<Shake128Xof>(seed),
            seed: *seed,
            _p: PhantomData,
        }
    }

    fn commit(&self, s: &Self::Witness) -> Self::Commitment {
        let op = NttOperatorOptimized::<Z1Ring, N>::new();
        self.a_hat.mul_vec_ntt(&s.to_ntt(&op)).from_ntt(&op)
    }
}

impl<P: SisParams, const K: usize, const L: usize, const N: usize> CommitmentKey<P, K, L, N> {
    /// The binding seed (instance binding for Fiat–Shamir).
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// Borrows `Â` (NTT domain).
    pub fn a_hat(&self) -> &ModuleMatrixNtt<Z1Ring, K, L, N> {
        &self.a_hat
    }
}

/// Builds a short witness vector from per-polynomial centered coefficients,
/// rejecting anything that violates the witness bound `‖s‖∞ ≤ B_S`.
pub fn witness_from_coeffs<P: SisParams, const L: usize, const N: usize>(
    rows: &[[i64; N]],
) -> Option<ModuleVector<Z1Ring, L, N>> {
    if rows.len() != L {
        return None;
    }
    for row in rows {
        for &c in row.iter() {
            if c.abs() > P::B_S {
                return None;
            }
        }
    }
    Some(ModuleVector::from_fn(|i| {
        PolyRing::<Z1Ring, N>::from_coefficients(
            rows[i]
                .iter()
                .map(|&c| Z1Ring::new(c.rem_euclid(Q) as u64))
                .collect(),
        )
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn short_witness(seed: u8) -> ModuleVector<Z1Ring, 6, RING_DIM> {
        let mut rows = Vec::new();
        for i in 0..6 {
            let mut row = [0i64; RING_DIM];
            for (j, c) in row.iter_mut().enumerate() {
                *c = ((seed as i64 + i as i64 * 7 + j as i64 * 3) % 9) - 4;
            }
            rows.push(row);
        }
        witness_from_coeffs::<Z1Instance, 6, RING_DIM>(&rows).unwrap()
    }

    #[test]
    fn commitment_is_deterministic_and_discriminates() {
        let key: CommitmentKey<Z1Instance, 8, 6, RING_DIM> = CommitmentKey::setup(&[1u8; 32]);
        let s = short_witness(3);
        let c1 = key.commit(&s);
        let c2 = key.commit(&s);
        assert_eq!(c1, c2, "commitment must be deterministic");

        // A different (still short) witness gives a different commitment
        // with overwhelming probability — a collision would be an MSIS
        // solution for this key.
        let s_other = short_witness(4);
        let c3 = key.commit(&s_other);
        assert_ne!(c1, c3);
    }

    #[test]
    fn witness_bound_is_enforced() {
        let mut rows = vec![[0i64; RING_DIM]; 6];
        rows[0][0] = Z1Instance::B_S + 1; // out of bound
        assert!(witness_from_coeffs::<Z1Instance, 6, RING_DIM>(&rows).is_none());
        assert!(witness_from_coeffs::<Z1Instance, 5, RING_DIM>(&rows).is_none());
    }
}
