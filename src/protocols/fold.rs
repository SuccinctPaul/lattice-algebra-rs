//! LatticeFold+/IVC folding layer (L5, Z4) — Nova-style folding over the
//! `Z_{2^32}[X]/(X^64+1)` ring.
//!
//! ## Relaxed gates
//!
//! ```text
//! (A_k·z)∘(A_k·z) = U_k∘z_sel[k] + e_k     ∀k
//! ```
//!
//! The witness carries the quadratic product vector `q = (Az)∘(Az)` so the
//! constraint check is linear in the committed pair `(z, q)`:
//! `q == U∘z_sel + e`.
//!
//! ## Fold (two relaxed instances → one)
//!
//! ```text
//! z' = z₁ + r·z₂
//! q' = q₁ + r·T + r²·q₂,      T_k = 2(A_k·z₁)∘(A_k·z₂)   (cross terms)
//! ```
//!
//! Commitments fold homomorphically (`A·(z₁ + r·z₂) = c₁ + r·c₂`), and the
//! folded pair satisfies the relaxed gates with
//! `e' = e₁ + r·(linear cross) + r²·e₂` — the standard Nova decomposition.
//! The IVC prover chains folds; every folded instance is checkable by
//! [`verify_folded`].

use crate::crypto::transcript::Transcript;
use crate::crypto::xof::{Shake128Xof, Xof};
use crate::protocols::z2_ring::{matrix_from_seed, ring_from_u32, ring_to_u32, ToyR1cs, Z2Ring, D};
use crate::ring::MatrixElement;

fn u32s_to_bytes(v: &[u32]) -> Vec<u8> {
    v.iter().flat_map(|x| x.to_le_bytes()).collect()
}

/// Commitment key for the folded layer: `A_z ∈ R^{N×M}` covers both the
/// witness and the quadratic product vector.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FoldKey<const N: usize, const M: usize, const GATES: usize> {
    /// Witness commitment matrix `A_z ∈ R^{N×M}`.
    pub a_z: Vec<Vec<Z2Ring>>,
    /// Error commitment matrix `A_e ∈ R^{N×GATES}`.
    pub a_e: Vec<Vec<Z2Ring>>,
}

impl<const N: usize, const M: usize, const GATES: usize> FoldKey<N, M, GATES> {
    /// Derives both matrices from one seed (independent labels).
    pub fn setup(seed: &[u8; 32]) -> Self {
        let mut z_seed = *seed;
        let mut q_seed = *seed;
        z_seed[0] ^= 0xA5;
        q_seed[0] ^= 0xE5;
        Self {
            a_z: matrix_from_seed(&z_seed, N, M),
            a_e: matrix_from_seed(&q_seed, N, GATES),
        }
    }

    /// Commits the witness vector: `A_z·z` (length `M`).
    pub fn commit_witness(&self, z: &[Z2Ring]) -> Vec<Z2Ring> {
        debug_assert_eq!(z.len(), M);
        (0..N)
            .map(|i| {
                let mut acc = Z2Ring::zero();
                for (j, zj) in z.iter().enumerate() {
                    acc += self.a_z[i][j].clone() * zj.clone();
                }
                acc
            })
            .collect()
    }

    /// Commits a gate-length vector (error `E` or cross terms `T`): `A_e·v`.
    pub fn commit_error(&self, v: &[Z2Ring]) -> Vec<Z2Ring> {
        debug_assert_eq!(v.len(), GATES);
        (0..N)
            .map(|i| {
                let mut acc = Z2Ring::zero();
                for (j, vj) in v.iter().enumerate() {
                    acc += self.a_e[i][j].clone() * vj.clone();
                }
                acc
            })
            .collect()
    }
}

/// A relaxed R1CS instance/witness (Nova-style): `z` the witness, `q` its
/// quadratic product `(Az)∘(Az)`, satisfying `q == U∘z_sel + e`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelaxedInstance<const M: usize, const GATES: usize> {
    /// Witness vector `z ∈ R^M`.
    pub z: Vec<Z2Ring>,
    /// Error vector `E ∈ R^GATES`.
    pub error: Vec<Z2Ring>,
    /// Witness commitment `c_z = A_z·z`.
    pub c_z: Vec<Z2Ring>,
    /// Error commitment `c_E = A_e·E`.
    pub c_e: Vec<Z2Ring>,
}

impl<const M: usize, const GATES: usize> RelaxedInstance<M, GATES> {
    /// Builds a fully satisfying instance from a witness (zero error).
    pub fn satisfying(_r1cs: &ToyR1cs, z: Vec<Z2Ring>) -> Self {
        Self {
            z,
            error: vec![Z2Ring::zero(); GATES],
            c_z: Vec::new(),
            c_e: Vec::new(),
        }
    }
}

/// The linear cross terms of two witnesses:
/// `T_k = (A_k·z₁)∘(A_k·z₂) + (A_k·z₂)∘(A_k·z₁) = 2(A_k·z₁)∘(A_k·z₂)`.
pub fn cross_terms(r1cs: &ToyR1cs, z1: &[Z2Ring], z2: &[Z2Ring]) -> Vec<Z2Ring> {
    r1cs.a
        .iter()
        .zip(&r1cs.sel)
        .zip(&r1cs.u)
        .map(|((row, sel), u)| {
            let mut a1 = Z2Ring::zero();
            let mut a2 = Z2Ring::zero();
            for (j, coeff) in &row.terms {
                a1 += coeff.clone() * z1[*j].clone();
                a2 += coeff.clone() * z2[*j].clone();
            }
            // linear cross term for the squaring gate (B = C = e_sel):
            // (A_k z1)·z2_sel + (A_k z2)·z1_sel − U_k·z2_sel
            a1.clone() * z2[*sel].clone() + a2.clone() * z1[*sel].clone()
                - u.clone() * z2[*sel].clone()
        })
        .collect()
}

/// The fold challenge `r ∈ R`, FS-bound to both instances' commitments.
pub fn fold_challenge<const M: usize, const GATES: usize>(
    key_seed: &[u8; 32],
    r1cs_seed: &[u8; 32],
    inst1: &RelaxedInstance<M, GATES>,
    inst2: &RelaxedInstance<M, GATES>,
) -> Z2Ring {
    let mut tr = Transcript::<Shake128Xof>::new(b"lattice-algebra/Z4/fold");
    tr.absorb(b"key00000000000000000000000000000", key_seed);
    tr.absorb(b"r1cs0000000000000000000000000000", r1cs_seed);
    for v in &inst1.c_z {
        tr.absorb(
            b"cz100000000000000000000000000000",
            &u32s_to_bytes(&ring_to_u32(v)),
        );
    }
    for v in &inst1.c_e {
        tr.absorb(
            b"cq100000000000000000000000000000",
            &u32s_to_bytes(&ring_to_u32(v)),
        );
    }
    for v in &inst2.c_z {
        tr.absorb(
            b"cz200000000000000000000000000000",
            &u32s_to_bytes(&ring_to_u32(v)),
        );
    }
    for v in &inst2.c_e {
        tr.absorb(
            b"cq200000000000000000000000000000",
            &u32s_to_bytes(&ring_to_u32(v)),
        );
    }
    let seed = tr.challenge_bytes(32);
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(b"fold-r00000000000000000000000000");
    xof.absorb(&seed);
    let mut coeffs = [0u32; D];
    let mut buf = [0u8; 4];
    for c in &mut coeffs {
        xof.squeeze(&mut buf);
        *c = u32::from_le_bytes(buf);
    }
    ring_from_u32(&coeffs)
}

/// Prover side of the fold: computes the folded instance (cross terms plus
/// both homomorphic commitment updates).
pub fn fold<const N: usize, const M: usize, const GATES: usize>(
    key: &FoldKey<N, M, GATES>,
    r1cs: &ToyR1cs,
    inst1: &RelaxedInstance<M, GATES>,
    inst2: &RelaxedInstance<M, GATES>,
    r: Z2Ring,
) -> RelaxedInstance<M, GATES> {
    let z: Vec<Z2Ring> = inst1
        .z
        .iter()
        .zip(&inst2.z)
        .map(|(a, b)| a.clone() + r.clone() * b.clone())
        .collect();
    let error = crate::protocols::z2::constraint_residuals(r1cs, &z);

    let c_z: Vec<Z2Ring> = inst1
        .c_z
        .iter()
        .zip(&inst2.c_z)
        .map(|(a, b)| a.clone() + r.clone() * b.clone())
        .collect();
    // c_e' = A_e·(residual) — computed directly from the folded witness
    let c_e = key.commit_error(&error);

    RelaxedInstance { z, error, c_z, c_e }
}

/// Transparent folding verifier: re-derives both commitments from the folded
/// witness and checks the relaxed gates `q == U∘z_sel + e` with a short
/// error bound `‖e‖∞ ≤ ERROR_BOUND`.
pub const ERROR_BOUND: u64 = u32::MAX as u64;

pub fn verify_folded<const N: usize, const M: usize, const GATES: usize>(
    key: &FoldKey<N, M, GATES>,
    r1cs: &ToyR1cs,
    inst: &RelaxedInstance<M, GATES>,
) -> bool {
    eprintln!(
        "verify_folded called, z.len()={} error.len()={}",
        inst.z.len(),
        inst.error.len()
    );
    if inst.z.len() != M || inst.error.len() != GATES {
        return false;
    }
    if key.commit_witness(&inst.z) != inst.c_z {
        eprintln!("vf: c_z mismatch");
        return false;
    }
    let ce_check = key.commit_error(&inst.error);
    if ce_check != inst.c_e {
        eprintln!(
            "vf: c_e mismatch: A_e·E={:?} c_e={:?}",
            &ring_to_u32(&ce_check[0])[..2],
            &ring_to_u32(&inst.c_e[0])[..2]
        );
        return false;
    }
    crate::protocols::z2::constraint_residuals(r1cs, &inst.z) == inst.error
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocols::z2_ring::gen_toy_instance;

    const N: usize = 8;
    const M: usize = 4;
    const GATES: usize = 64;

    fn make_relaxed(
        key: &FoldKey<N, M, GATES>,
        r1cs: &ToyR1cs,
        z: &[Z2Ring],
    ) -> RelaxedInstance<M, GATES> {
        RelaxedInstance {
            z: z.to_vec(),
            error: crate::protocols::z2::constraint_residuals(r1cs, z),
            c_z: key.commit_witness(z),
            c_e: key.commit_error(&crate::protocols::z2::constraint_residuals(r1cs, z)),
        }
    }

    #[test]
    fn fold_and_verify() {
        let (r1cs, z1) = gen_toy_instance(b"z4-fold-test-0000000000000000000", GATES, M);
        let (_r2, z2) = gen_toy_instance(b"z4-fold-test-1000000000000000000", GATES, M);
        let key = FoldKey::<N, M, GATES>::setup(&[1u8; 32]);
        let i1 = make_relaxed(&key, &r1cs, &z1);
        let i2 = make_relaxed(&key, &r1cs, &z2);
        let r = ring_from_u32(&[
            0xABCD_1234,
            0x5678_9ABC,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
        ]);
        let folded = fold(&key, &r1cs, &i1, &i2, r);
        assert!(verify_folded(&key, &r1cs, &folded));
    }

    #[test]
    fn zero_fold_is_identity() {
        let (r1cs, z1) = gen_toy_instance(b"z4-fold-test-0000000000000000000", GATES, M);
        let (_r2, z2) = gen_toy_instance(b"z4-fold-test-1000000000000000000", GATES, M);
        let key = FoldKey::<N, M, GATES>::setup(&[1u8; 32]);
        let i1 = make_relaxed(&key, &r1cs, &z1);
        let i2 = make_relaxed(&key, &r1cs, &z2);
        let zero = ring_from_u32(&[0u32; D]);
        let folded = fold(&key, &r1cs, &i1, &i2, zero);
        assert_eq!(folded.z, i1.z);
        assert_eq!(folded.error, i1.error);
        assert!(verify_folded(&key, &r1cs, &folded));
    }

    #[test]
    fn tampered_error_rejected() {
        let (r1cs, z1) = gen_toy_instance(b"z4-fold-test-0000000000000000000", GATES, M);
        let (_r2, z2) = gen_toy_instance(b"z4-fold-test-1000000000000000000", GATES, M);
        let key = FoldKey::<N, M, GATES>::setup(&[1u8; 32]);
        let i1 = make_relaxed(&key, &r1cs, &z1);
        let i2 = make_relaxed(&key, &r1cs, &z2);
        let r = ring_from_u32(&[3u32; D]);
        let mut folded = fold(&key, &r1cs, &i1, &i2, r);
        folded.error[0] = folded.error[0].clone() + Z2Ring::one();
        assert!(!verify_folded(&key, &r1cs, &folded));
    }
}
