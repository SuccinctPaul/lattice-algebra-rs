//! HVZK Σ-protocol over the Z2 ring: zero-knowledge short opening of an
//! Ajtai commitment — the K2 *blinding* step for the committed-opening
//! line (Z2 and up).
//!
//! # Statement
//!
//! Public: Ajtai key `A ∈ R^{N×M}`, commitment `c = A·w`. The prover
//! demonstrates knowledge of a short `w` (`‖w‖∞ ≤ B_W`) **without
//! revealing `w`**: the response `z = y + C·w` is rejection-sampled to a
//! masked distribution, which is exactly the blinding the compact opening
//! line lacked.
//!
//! # Protocol (FS-compiled, HVZK)
//!
//! ```text
//! y ← centered-bounded (‖y‖∞ < B_Y)
//! d = A·y                    ──c, d──▶  C ← small non-unit challenge
//! z = y + C·w                ──z──▶     1. A·z == d + C·c   (exact)
//!                                       2. ‖z‖∞ ≤ B_Z       (HVZK gate)
//! ```
//!
//! The challenge is
//! [`nonunit_small_poly`](crate::foundation::sampling::nonunit_small_poly):
//! coefficients in `{-1,0,1}` conditioned on an even
//! coefficient sum — small enough for short responses (`‖C‖₁ ≤ N`), yet a
//! genuine non-unit, so the cancellation argument survives. Soundness is
//! the standard relaxed forking extraction: two accepting transcripts with
//! the same `d` yield `A·(z1 − z2) = (d1 − d2) + (C1 − C2)·c` with
//! `‖z1 − z2‖∞ ≤ 2·B_Z` — knowledge of a short preimage up to the relaxed
//! slack, with the transcript distribution masked by the rejection loop
//! (HVZK). Full relation soundness (no slack) additionally needs the
//! recursive commitment mode of the opening line.

use crate::commitment::key::AjtaiKey;
use crate::foundation::fs::absorb_rings;
use crate::foundation::sampling::{centered_bounded_poly, nonunit_small_poly};
use crate::instance::ring::{infinity_norm, Z2Coeff, Z2Ring, D};
use algebra::crypto::sampling::BitStream;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use alloc::vec::Vec;

/// Witness coefficient bound `‖w‖∞ ≤ B_W`.
pub const B_W: u64 = 1 << 8;
/// Mask coefficient bound (power of two). Sized so the rejection loop's
/// per-attempt acceptance stays high: the response bound costs
/// `64·B_W = 2^14` of headroom across 256 masked coefficients, giving
/// `1 − e^{−256·2^14/B_Y}` — ≈22% at `B_Y = 2^24`.
pub const B_Y: u64 = 1 << 24;
/// Response bound `B_Y − ‖C‖₁,max·B_W` with `‖C‖₁ ≤ N = 64` (small
/// non-unit challenge).
pub const B_Z: u64 = B_Y - 64 * B_W;

/// Rejection-sampled HVZK proof: mask commitment `d = A·y` and response
/// `z = y + C·w`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Proof<const N: usize, const M: usize> {
    /// Mask commitment `d = A·y` (first message).
    pub d: Vec<Z2Ring>,
    /// Response `z = y + C·w`.
    pub z: Vec<Z2Ring>,
}

/// The challenge for a (c, d) pair: a small non-unit derived after both
/// commitments are absorbed.
fn challenge(key_seed: &[u8; 32], c: &[Z2Ring], d: &[Z2Ring]) -> Z2Ring {
    let mut tr = Transcript::<Shake256Xof>::new(b"lattice-algebra/Z6/z2-sigma");
    tr.absorb(b"key", key_seed);
    absorb_rings(&mut tr, b"c", c);
    absorb_rings(&mut tr, b"d", d);
    let seed = tr.challenge_bytes(64);
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(b"C");
    xof.absorb(&seed);
    let mut stream = BitStream::new(&mut xof);
    nonunit_small_poly::<Z2Coeff, Shake256Xof, D>(&mut stream)
}

/// Prover: rejection-samples the mask until the response fits `B_Z`
/// (HVZK; statistically bounded re-rolls, deterministic re-seeding).
///
/// # Errors
/// [`SigmaError::RejectionLimit`] if 128 attempts all exceed the response
/// bound (statistically unreachable for the default parameters).
/// # Example
///
/// ```rust
/// use zk::commitment::key::AjtaiKey;
/// use zk::foundation::encoding::ring_from_u32;
/// use zk::instance::ring::{Z2Ring, D};
/// use zk::sigma::z2::{prove, verify};
///
/// let key_seed = [1u8; 32];
/// let key = AjtaiKey::<8, 4>::setup(&key_seed);
/// let w: Vec<Z2Ring> = (0..4).map(|j| {
///     ring_from_u32(&{ let mut c = [0u32; D]; c[j * 7 % D] = (j + 1) as u32; c })
/// }).collect();
/// let c = key.mul_vec(&w);
///
/// let proof = prove(&key, &key_seed, &w, &c, &[9u8; 32]).expect("honest prove");
/// assert!(verify(&key, &key_seed, &c, &proof));
/// ```
pub fn prove<const N: usize, const M: usize>(
    key: &AjtaiKey<N, M>,
    key_seed: &[u8; 32],
    w: &[Z2Ring],
    c: &[Z2Ring],
    randomness: &[u8; 32],
) -> Result<Proof<N, M>, SigmaError> {
    debug_assert_eq!(w.len(), M);
    let mut rng_seed = *randomness;
    for _ in 0..128 {
        let mut xof = Shake256Xof::new(&[]);
        xof.absorb(b"mask");
        xof.absorb(&rng_seed);
        let mut stream = BitStream::new(&mut xof);
        let y: Vec<Z2Ring> = (0..M)
            .map(|_| centered_bounded_poly::<Z2Coeff, _, D>(&mut stream, (B_Y - 1) as u32))
            .collect();
        let d = key.mul_vec(&y);
        let challenge = challenge(key_seed, c, &d);
        let z: Vec<Z2Ring> = y
            .iter()
            .zip(w)
            .map(|(yi, wi)| yi.clone() + challenge.clone() * wi.clone())
            .collect();
        if infinity_norm(&z) <= B_Z {
            return Ok(Proof { d, z });
        }
        // deterministic re-seed for the next attempt
        let mut reseed = Shake256Xof::new(&[]);
        reseed.absorb(&rng_seed);
        reseed.absorb(b"retry");
        rng_seed.copy_from_slice(&reseed.squeeze_vec(32));
    }
    Err(SigmaError::RejectionLimit)
}

/// Verifier: exact linear link plus the HVZK norm gate.
pub fn verify<const N: usize, const M: usize>(
    key: &AjtaiKey<N, M>,
    key_seed: &[u8; 32],
    c: &[Z2Ring],
    proof: &Proof<N, M>,
) -> bool {
    if proof.d.len() != N || proof.z.len() != M || c.len() != N {
        return false;
    }
    if infinity_norm(&proof.z) > B_Z {
        return false;
    }
    let challenge = challenge(key_seed, c, &proof.d);
    let az = key.mul_vec(&proof.z);
    for i in 0..N {
        let rhs = proof.d[i].clone() + challenge.clone() * c[i].clone();
        if az[i] != rhs {
            return false;
        }
    }
    true
}

/// Relaxed forking extractor: two accepting transcripts sharing the mask
/// commitment `d` yield `A·(z1 − z2) = (d1 − d2) + (C1 − C2)·c` with
/// `‖z1 − z2‖∞ ≤ 2·B_Z` — short-preimage knowledge up to the relaxed
/// slack.
pub fn extract(z1: &[Z2Ring], z2: &[Z2Ring]) -> (Vec<Z2Ring>, Vec<Z2Ring>) {
    debug_assert_eq!(z1.len(), z2.len());
    (
        z1.iter()
            .zip(z2)
            .map(|(a, b)| a.clone() - b.clone())
            .collect(),
        Vec::new(),
    )
}

/// Typed rejection for the Σ-protocol (no panics on secret-dependent
/// paths).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SigmaError {
    /// The rejection loop exceeded its budget (statistically unreachable).
    RejectionLimit,
}

#[cfg(test)]
mod tests {
    use super::*;

    const N: usize = 8;
    const M: usize = 4;

    fn instance(seed: u8) -> (AjtaiKey<N, M>, Vec<Z2Ring>, Vec<Z2Ring>, [u8; 32]) {
        let key_seed = {
            let mut s = [0u8; 32];
            s[0] = seed;
            s
        };
        let key = AjtaiKey::<N, M>::setup(&key_seed);
        // small honest witness: ‖w‖∞ ≤ 4 ≪ B_W
        let w: Vec<Z2Ring> = (0..M)
            .map(|j| {
                crate::foundation::encoding::ring_from_u32(&{
                    let mut c = [0u32; D];
                    c[j * 7 % D] = (1 + j) as u32;
                    c
                })
            })
            .collect();
        let c = key.mul_vec(&w);
        (key, w, c, key_seed)
    }

    #[test]
    fn honest_hvzk_proof_verifies() {
        let (key, w, c, key_seed) = instance(1);
        let proof = prove(&key, &key_seed, &w, &c, &[5u8; 32]).expect("honest prove must succeed");
        assert!(verify(&key, &key_seed, &c, &proof));
        // determinism
        let again = prove(&key, &key_seed, &w, &c, &[5u8; 32]).unwrap();
        assert_eq!(proof, again);
    }

    #[test]
    fn wrong_commitment_and_tamper_rejected() {
        let (key, w, c, key_seed) = instance(2);
        let proof = prove(&key, &key_seed, &w, &c, &[6u8; 32]).unwrap();

        // different commitment
        let (_k2, _w2, c2, _s2) = instance(3);
        assert!(!verify(&key, &key_seed, &c2, &proof));

        // tampered response breaks the exact link
        let mut bad = proof.clone();
        let mut coeffs = crate::foundation::encoding::ring_to_u32(&bad.z[0]);
        coeffs[0] ^= 1;
        bad.z[0] = crate::foundation::encoding::ring_from_u32(&coeffs);
        assert!(!verify(&key, &key_seed, &c, &bad));
    }

    #[test]
    fn response_is_masked_and_extract_relaxes() {
        // the response must NOT be a deterministic function of (c, w)
        // alone: different randomness gives different (d, z) — the blinding
        let (key, w, c, key_seed) = instance(4);
        let p1 = prove(&key, &key_seed, &w, &c, &[1u8; 32]).unwrap();
        let p2 = prove(&key, &key_seed, &w, &c, &[2u8; 32]).unwrap();
        assert_ne!(p1.d, p2.d, "mask commitments must differ per randomness");
        assert_ne!(p1.z, p2.z);

        // forking extractor: relaxed relation A·(z1−z2) = (d1−d2) + (C1−C2)·c
        let (z_diff, _) = extract(&p1.z, &p2.z);
        let d_diff: Vec<Z2Ring> =
            p1.d.iter()
                .zip(&p2.d)
                .map(|(a, b)| a.clone() - b.clone())
                .collect();
        let c1 = challenge(&key_seed, &c, &p1.d);
        let c2 = challenge(&key_seed, &c, &p2.d);
        let v = c1.clone() - c2.clone();
        let lhs = key.mul_vec(&z_diff);
        for i in 0..N {
            let rhs = d_diff[i].clone() + v.clone() * c[i].clone();
            assert_eq!(lhs[i], rhs, "relaxed extraction identity must hold");
        }
    }
}
