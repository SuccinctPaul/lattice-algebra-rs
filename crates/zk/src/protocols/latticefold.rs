//! LatticeFold-style folding: linear fold + batch balanced decomposition +
//! splitting query over `R = Z_{2^32}[X]/(X^64+1)` (L5, Z5).
//!
//! This is the *decomposition-based* folding line of LatticeFold/LatticeFold+
//! — distinct from the Nova-style relaxed-instance folding in
//! [`crate::protocols::fold`]: here two **committed short witnesses** are
//! folded into one committed vector whose shortness is re-certified through
//! its `b`-bit balanced digits, without ever opening the folded vector.
//!
//! # Protocol
//!
//! Instance: Ajtai key `A ∈ R^{N×M}`, commitments `c₁ = A·w₁`, `c₂ = A·w₂`
//! with `‖wᵢ‖∞ ≤ B_w`.
//!
//! ```text
//! r  ← H(c₁, c₂)          small-norm ring challenge (hyperball, ‖r‖₁ ≤ B_r)
//! w' = w₁ + r·w₂          (fold;  ‖w'‖∞ ≤ B_w·(1 + B_r), homomorphic: c' = c₁ + r·c₂)
//! d₀..d_{L−1} ← decompose(w')    balanced b-bit digits, ‖dᵢ‖∞ ≤ 2^{b−1}
//!                                with w' = Σ 2^{bi}·dᵢ  (EXACT in R — see below)
//! cᵢ = A·dᵢ                      digit commitments
//!                     ──c', {cᵢ}──▶  ζ ← H(c₁, c₂, c', {cᵢ})   (splitting query)
//! d̃ = Σ ζⁱ·dᵢ            ──d̃──▶
//! ```
//!
//! Verifier (all checks linear in committed values, then one norm gate):
//! 1. `c' == c₁ + r·c₂` — homomorphic fold;
//! 2. `c' == Σ 2^{bi}·cᵢ` — decomposition consistency (exact; a violating
//!    digit set would give the short kernel vector `w' − Σ 2^{bi}·dᵢ`,
//!    breaking Module-SIS);
//! 3. `Σ ζⁱ·cᵢ == A·d̃` — the batched opening (ζ chosen *after* `{cᵢ}` are
//!    absorbed, so the digit set is fixed before the query opens it);
//! 4. `‖d̃‖∞ ≤ splitting_norm_bound(B_ζ)` — the honest `d̃` is short by norm
//!    accounting: `‖Σ ζⁱ·dᵢ‖∞ ≤ Σ ‖ζⁱ‖₁·2^{b−1} ≤ Σ B_ζⁱ·2^{b−1}`
//!    (`l1` is sub-multiplicative under the negacyclic convolution). A
//!    forger replacing the digits must make `Σ ζⁱ·cᵢ` land in
//!    `A·{short vectors of R^M}` — for a tall random `A` that image is a
//!    vanishing fraction of `R^N`, and the grinding probability is the
//!    Schwartz–Zippel slack of the challenge space.
//!
//! # Why the decomposition is exact and quotient-free
//!
//! In `Z_{2^32}` every coefficient `x` has a balanced radix-`2^b`
//! representation `x = Σ_{i<L} 2^{bi}·dᵢ + 2^{bL}·q` with digits
//! `dᵢ ∈ (−2^{b−1}, 2^{b−1}]`; choosing `L = 32/b` makes `2^{bL} ≡ 0` in the
//! ring, so the quotient term disappears and `w' = Σ 2^{bi}·dᵢ` **exactly**
//! (per coefficient, hence per ring element). This is what lets the verifier
//! check consistency without any slack — and what LatticeFold exploits to
//! recurse: each level replaces one committed vector by `L` short committed
//! digit vectors.

use crate::fs::absorb_rings;
use crate::protocols::short::{infinity_norm, split_balanced};
use crate::protocols::z2_ring::{Z2Coeff, Z2Ring, D};
use crate::sampling::{hyperball_vec, uniform_matrix_from_seed};
use algebra::crypto::sampling::BitStream;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::ring::MatrixElement;

/// Digit width `b` of the balanced decomposition.
pub const DIGIT_BITS: u32 = 8;
/// Number of digits `L = 32/b` (the quotient vanishes in `Z_{2^32}`).
pub const NUM_DIGITS: usize = (32 / DIGIT_BITS) as usize;

/// Ajtai commitment key for the decomposition layer: `A ∈ R^{N×M}`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LfKey<const N: usize, const M: usize> {
    a: Vec<Vec<Z2Ring>>,
}

impl<const N: usize, const M: usize> LfKey<N, M> {
    /// Derives the key from a seed.
    pub fn setup(seed: &[u8; 32]) -> Self {
        Self {
            a: uniform_matrix_from_seed::<Z2Coeff, D>(b"", seed, N, M),
        }
    }

    /// `A·x`.
    pub fn mul_vec(&self, x: &[Z2Ring]) -> Vec<Z2Ring> {
        debug_assert_eq!(x.len(), M);
        (0..N)
            .map(|i| {
                let mut acc = Z2Ring::zero();
                for (j, xj) in x.iter().enumerate() {
                    acc += self.a[i][j].clone() * xj.clone();
                }
                acc
            })
            .collect()
    }
}

/// The constant ring element `2^{bi}`.
fn pow2_digit(i: usize) -> Z2Ring {
    let mut coeffs = [0u32; D];
    coeffs[0] = 1u32 << (DIGIT_BITS * i as u32);
    crate::encoding::ring_from_u32(&coeffs)
}

/// Balanced `b`-bit decomposition of a ring vector into `L` digit vectors:
/// `w = Σ 2^{bi}·dᵢ` **exactly** in the ring, `‖dᵢ‖∞ ≤ 2^{b−1}`.
///
/// Implemented as `L` successive balanced splits (peel off the low digits,
/// recurse on the quotient). The final quotient `q` with
/// `w = Σ 2^{bi}·dᵢ + 2^{bL}·q` satisfies `|q| ≤ 1` and is discarded — its
/// ring image is `0` because `2^{bL} ≡ 0` in `Z_{2^32}`.
pub fn decompose_balanced<const M: usize>(w: &[Z2Ring]) -> Vec<Vec<Z2Ring>> {
    let mut digits = Vec::with_capacity(NUM_DIGITS);
    let mut remaining: Vec<Z2Ring> = w.to_vec();
    for _ in 0..NUM_DIGITS {
        let (high, low) = split_balanced(&remaining, DIGIT_BITS);
        digits.push(low);
        remaining = high;
    }
    digits
}

/// Rebuilds `Σ 2^{bi}·dᵢ` (the exact inverse of [`decompose_balanced`]).
pub fn recompose<const M: usize>(digits: &[Vec<Z2Ring>]) -> Vec<Z2Ring> {
    debug_assert_eq!(digits.len(), NUM_DIGITS);
    let mut acc: Vec<Z2Ring> = vec![Z2Ring::zero(); M];
    for (i, d) in digits.iter().enumerate() {
        let w = pow2_digit(i);
        for (a, dj) in acc.iter_mut().zip(d) {
            *a += w.clone() * dj.clone();
        }
    }
    acc
}

/// A-priori infinity-norm bound of the folded witness:
/// `‖w₁ + r·w₂‖∞ ≤ B_w·(1 + ‖r‖₁)`.
pub fn fold_norm_bound(b_w: u64, l1_r: u64) -> u64 {
    b_w.saturating_add(b_w.saturating_mul(l1_r))
}

/// Norm gate for the batched digit opening: `Σ_{i<L} B_ζⁱ·2^{b−1}` — the
/// provable bound on `‖Σ ζⁱ·dᵢ‖∞` given `‖ζ‖₁ ≤ B_ζ` (geometric sum; the
/// `l1` norm is sub-multiplicative under the ring convolution).
pub fn splitting_norm_bound(l1_zeta: u64) -> u64 {
    let digit_bound = 1u64 << (DIGIT_BITS - 1);
    let mut bound = 0u64;
    let mut term = 1u64;
    for _ in 0..NUM_DIGITS {
        bound = bound.saturating_add(term.saturating_mul(digit_bound));
        term = term.saturating_mul(l1_zeta);
    }
    bound
}

/// Squeezes a single-element hyperball challenge (`‖ζ‖∞ ≤ 1`,
/// `‖ζ‖₁ ≤ l1_bound`) from a domain-separated re-expansion of a transcript
/// seed (the crate's standard three-step FS shape).
fn hyperball_challenge(domain: &[u8], seed: &[u8], l1_bound: u64) -> Z2Ring {
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(domain);
    xof.absorb(seed);
    let mut stream = BitStream::new(&mut xof);
    hyperball_vec::<Z2Coeff, Shake128Xof, D>(&mut stream, 1, 1, l1_bound, 1 << 20)
        .expect("hyperball challenge must sample for sound parameters")
        .remove(0)
}

/// Fold challenge `r` (`‖r‖∞ ≤ 1`, `‖r‖₁ ≤ l1_bound`) bound to the key and
/// both commitments.
pub fn fold_challenge(key_seed: &[u8; 32], c1: &[Z2Ring], c2: &[Z2Ring], l1_bound: u64) -> Z2Ring {
    let mut tr = Transcript::<Shake128Xof>::new(b"lattice-algebra/Z5/latticefold");
    tr.absorb(b"key", key_seed);
    absorb_rings(&mut tr, b"c1", c1);
    absorb_rings(&mut tr, b"c2", c2);
    hyperball_challenge(b"fold-r", &tr.challenge_bytes(64), l1_bound)
}

/// The transcript parts of the splitting query: both commitments, the folded
/// commitment and every digit commitment (shared by prover and verifier so
/// the absorbed bytes can never drift).
fn splitting_parts<'a>(
    c1: &'a [Z2Ring],
    c2: &'a [Z2Ring],
    c_prime: &'a [Z2Ring],
    digit_comms: &'a [Vec<Z2Ring>],
) -> Vec<(Vec<u8>, &'a [Z2Ring])> {
    let mut parts = vec![
        (b"c1".to_vec(), c1),
        (b"c2".to_vec(), c2),
        (b"cp".to_vec(), c_prime),
    ];
    for (i, ci) in digit_comms.iter().enumerate() {
        parts.push((vec![b'd', b'0' + i as u8], ci.as_slice()));
    }
    parts
}

/// Splitting query `ζ` (`‖ζ‖∞ ≤ 1`, `‖ζ‖₁ ≤ l1_bound`), derived after the
/// folded and digit commitments are absorbed — the digit set is fixed before
/// the query opens it.
fn splitting_challenge(
    c1: &[Z2Ring],
    c2: &[Z2Ring],
    c_prime: &[Z2Ring],
    digit_comms: &[Vec<Z2Ring>],
    l1_bound: u64,
) -> Z2Ring {
    let mut tr = Transcript::<Shake128Xof>::new(b"lattice-algebra/Z5/latticefold");
    for (label, rings) in splitting_parts(c1, c2, c_prime, digit_comms) {
        absorb_rings(&mut tr, &label, rings);
    }
    hyperball_challenge(b"splitting-zeta", &tr.challenge_bytes(64), l1_bound)
}

/// Prover side: folds two committed witnesses, decomposes the folded vector
/// into balanced digits, and answers the splitting query.
///
/// Returns the commitments `(c₁, c₂, c')` (all derived deterministically
/// from the witnesses and key) and the proof. `l1_r`/`l1_zeta` are the
/// hyperball budgets for the two challenges (kept as explicit parameters so
/// callers can match their security level).
pub fn prove_fold_decompose<const N: usize, const M: usize>(
    key: &LfKey<N, M>,
    key_seed: &[u8; 32],
    w1: &[Z2Ring],
    w2: &[Z2Ring],
    l1_r: u64,
    l1_zeta: u64,
) -> (Vec<Z2Ring>, Vec<Z2Ring>, LfProof<N, M>) {
    debug_assert_eq!(w1.len(), M);
    debug_assert_eq!(w2.len(), M);
    let c1 = key.mul_vec(w1);
    let c2 = key.mul_vec(w2);
    let r = fold_challenge(key_seed, &c1, &c2, l1_r);

    let c_prime: Vec<Z2Ring> = c1
        .iter()
        .zip(&c2)
        .map(|(a, b)| a.clone() + r.clone() * b.clone())
        .collect();

    let w_prime: Vec<Z2Ring> = w1
        .iter()
        .zip(w2)
        .map(|(a, b)| a.clone() + r.clone() * b.clone())
        .collect();
    let digits = decompose_balanced::<M>(&w_prime);
    debug_assert_eq!(
        recompose::<M>(&digits),
        w_prime,
        "decomposition must be exact"
    );
    let digit_comms: Vec<Vec<Z2Ring>> = digits.iter().map(|d| key.mul_vec(d)).collect();

    // splitting query, bound to the folded commitment and all digit commitments
    let zeta = splitting_challenge(&c1, &c2, &c_prime, &digit_comms, l1_zeta);

    // d̃ = Σ ζⁱ·dᵢ (Horner)
    let mut d_tilde: Vec<Z2Ring> = vec![Z2Ring::zero(); M];
    for d in digits.iter().rev() {
        for (a, dj) in d_tilde.iter_mut().zip(d) {
            *a = a.clone() * zeta.clone() + dj.clone();
        }
    }

    (
        c1,
        c2,
        LfProof {
            c_prime,
            digit_comms,
            d_tilde,
        },
    )
}

/// Proof for the fold+decompose statement: the folded commitment, the `L`
/// digit commitments, and the single batched digit opening.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LfProof<const N: usize, const M: usize> {
    /// Folded commitment `c' = c₁ + r·c₂`.
    pub c_prime: Vec<Z2Ring>,
    /// Digit commitments `cᵢ = A·dᵢ` (`L` vectors of length `N`).
    pub digit_comms: Vec<Vec<Z2Ring>>,
    /// Batched digit opening `d̃ = Σ ζⁱ·dᵢ`.
    pub d_tilde: Vec<Z2Ring>,
}

/// Verifies the fold+decompose statement for committed witnesses `c₁`, `c₂`.
/// The `l1` budgets must match the prover's (they parameterize the challenge
/// distribution and the norm gate).
pub fn verify_fold_decompose<const N: usize, const M: usize>(
    key: &LfKey<N, M>,
    key_seed: &[u8; 32],
    c1: &[Z2Ring],
    c2: &[Z2Ring],
    l1_r: u64,
    l1_zeta: u64,
    proof: &LfProof<N, M>,
) -> bool {
    if c1.len() != N || c2.len() != N || proof.c_prime.len() != N {
        return false;
    }
    if proof.digit_comms.len() != NUM_DIGITS
        || proof.digit_comms.iter().any(|ci| ci.len() != N)
        || proof.d_tilde.len() != M
    {
        return false;
    }
    let r = fold_challenge(key_seed, c1, c2, l1_r);

    // 1. homomorphic fold
    let c_prime: Vec<Z2Ring> = c1
        .iter()
        .zip(c2)
        .map(|(a, b)| a.clone() + r.clone() * b.clone())
        .collect();
    if c_prime != proof.c_prime {
        return false;
    }

    // 2. decomposition consistency: c' == Σ 2^{bi}·cᵢ (exact)
    let mut combined: Vec<Z2Ring> = vec![Z2Ring::zero(); N];
    for (i, ci) in proof.digit_comms.iter().enumerate() {
        let w = pow2_digit(i);
        for (a, cij) in combined.iter_mut().zip(ci) {
            *a += w.clone() * cij.clone();
        }
    }
    if combined != proof.c_prime {
        return false;
    }

    // 3. splitting query: Σ ζⁱ·cᵢ == A·d̃
    let zeta = splitting_challenge(c1, c2, &c_prime, &proof.digit_comms, l1_zeta);

    let mut lhs: Vec<Z2Ring> = vec![Z2Ring::zero(); N];
    for ci in proof.digit_comms.iter().rev() {
        for (a, cij) in lhs.iter_mut().zip(ci) {
            *a = a.clone() * zeta.clone() + cij.clone();
        }
    }
    if lhs != key.mul_vec(&proof.d_tilde) {
        return false;
    }

    // 4. norm gate on the batched opening
    infinity_norm(&proof.d_tilde) <= splitting_norm_bound(l1_zeta)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::encoding::{ring_from_u32, ring_to_u32};
    use algebra::crypto::xof::Xof;

    const N: usize = 8;
    const M: usize = 4;

    fn seed32(tag: &[u8]) -> [u8; 32] {
        let mut s = [0u8; 32];
        s[..tag.len()].copy_from_slice(tag);
        s
    }

    fn rnd_vec(xof: &mut Shake128Xof, len: usize, mask: u32) -> Vec<Z2Ring> {
        (0..len)
            .map(|_| {
                let mut coeffs = [0u32; D];
                let mut buf = [0u8; 4];
                for c in &mut coeffs {
                    xof.squeeze(&mut buf);
                    *c = u32::from_le_bytes(buf) & mask;
                }
                ring_from_u32(&coeffs)
            })
            .collect()
    }

    #[test]
    fn decomposition_is_exact_and_digits_are_short() {
        let mut xof = Shake128Xof::new(&[]);
        let w = rnd_vec(&mut xof, M, u32::MAX);
        let digits = decompose_balanced::<M>(&w);
        assert_eq!(digits.len(), NUM_DIGITS);
        for d in &digits {
            assert!(
                infinity_norm(d) <= 1u64 << (DIGIT_BITS - 1),
                "digit must be b-bit balanced"
            );
        }
        assert_eq!(recompose::<M>(&digits), w, "decomposition must be exact");
    }

    #[test]
    fn honest_fold_decompose_verifies() {
        let key_seed = seed32(b"lf-key-0");
        let key = LfKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"witnesses");
        let w1 = rnd_vec(&mut xof, M, 0x0000_FFFF); // 16-bit witnesses
        let w2 = rnd_vec(&mut xof, M, 0x0000_FFFF);

        let l1_r = 48;
        let l1_zeta = 48;
        let (c1, c2, proof) =
            prove_fold_decompose::<N, M>(&key, &key_seed, &w1, &w2, l1_r, l1_zeta);
        assert_eq!(c1, key.mul_vec(&w1));
        assert_eq!(c2, key.mul_vec(&w2));
        assert!(verify_fold_decompose::<N, M>(
            &key, &key_seed, &c1, &c2, l1_r, l1_zeta, &proof
        ));
    }

    #[test]
    fn tampered_digit_commitment_rejected() {
        let key_seed = seed32(b"lf-key-1");
        let key = LfKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"witnesses");
        let w1 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let w2 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let (c1, c2, mut proof) = prove_fold_decompose::<N, M>(&key, &key_seed, &w1, &w2, 48, 48);

        // shift one digit commitment: consistency + splitting checks fail
        let mut coeffs = ring_to_u32(&proof.digit_comms[1][0]);
        coeffs[0] ^= 1;
        proof.digit_comms[1][0] = ring_from_u32(&coeffs);
        assert!(!verify_fold_decompose::<N, M>(
            &key, &key_seed, &c1, &c2, 48, 48, &proof
        ));
    }

    #[test]
    fn tampered_batched_opening_rejected() {
        let key_seed = seed32(b"lf-key-2");
        let key = LfKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"witnesses");
        let w1 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let w2 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let (c1, c2, mut proof) = prove_fold_decompose::<N, M>(&key, &key_seed, &w1, &w2, 48, 48);

        let mut coeffs = ring_to_u32(&proof.d_tilde[2]);
        coeffs[3] ^= 1;
        proof.d_tilde[2] = ring_from_u32(&coeffs);
        assert!(!verify_fold_decompose::<N, M>(
            &key, &key_seed, &c1, &c2, 48, 48, &proof
        ));
    }

    #[test]
    fn mismatched_commitments_rejected() {
        let key_seed = seed32(b"lf-key-3");
        let key = LfKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"witnesses");
        let w1 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let w2 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let (_c1, _c2, proof) = prove_fold_decompose::<N, M>(&key, &key_seed, &w1, &w2, 48, 48);

        // verify against commitments of different witnesses
        let w3 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let other1 = key.mul_vec(&w3);
        assert!(!verify_fold_decompose::<N, M>(
            &key,
            &key_seed,
            &other1,
            &key.mul_vec(&w2),
            48,
            48,
            &proof
        ));
    }

    #[test]
    fn norm_bounds_are_consistent_with_the_honest_run() {
        // The folded witness respects fold_norm_bound, and the honest batched
        // opening respects splitting_norm_bound — the two accounting helpers
        // must be tight enough to gate the honest case.
        let key_seed = seed32(b"lf-key-4");
        let key = LfKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"witnesses");
        let w1 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let w2 = rnd_vec(&mut xof, M, 0x0000_FFFF);
        let l1_r = 48;
        let (c1, c2, proof) = prove_fold_decompose::<N, M>(&key, &key_seed, &w1, &w2, l1_r, 48);

        let b_w = 1u64 << 16;
        assert!(infinity_norm(&w1) <= b_w && infinity_norm(&w2) <= b_w);
        let r = fold_challenge(&key_seed, &c1, &c2, l1_r);
        let w_prime: Vec<Z2Ring> = w1
            .iter()
            .zip(&w2)
            .map(|(a, b)| a.clone() + r.clone() * b.clone())
            .collect();
        assert!(infinity_norm(&w_prime) <= fold_norm_bound(b_w, l1_r));
        assert!(infinity_norm(&proof.d_tilde) <= splitting_norm_bound(48));
    }
}
