//! Projection argument: approximate shortness for committed vectors —
//! the digit-based flavor (`z = z₀ + b·z₁` norm control) used across the
//! LaBRADOR recursion, LNP22 decomposition arguments and LatticeFold's
//! quotient/residue checks.
//!
//! # Statement
//!
//! Public: Ajtai key `A ∈ R^{N×M}`, commitment `c = A·w`, a public target
//! vector `t ∈ R^M`, the challenge `ζ ∈ R` and two claimed bounds.
//! The prover demonstrates
//!
//! ```text
//! ‖v‖∞ ≤ 2^γ·B_h + 2^{γ−1},   v := w − ζ·t
//! ```
//!
//! without revealing `w` (or `v`) as such — only **short digits** leave the
//! prover, which is what lets a recursion keep every accumulated object
//! Ajtai-committable.
//!
//! # Protocol (transparent, one level)
//!
//! ```text
//! v = w − ζ·t                      (prover-side; verifier holds c and t)
//! v = 2^γ·h + l   (balanced split: ‖l‖∞ ≤ 2^{γ−1}, exact in R)
//!                     ──h, l──▶
//! ```
//!
//! Verifier:
//! 1. `A·(2^γ·h + l) == c − ζ·(A·t)` — **exact** linear link (no slack:
//!    the balanced split reconstructs `v` exactly in the ring);
//! 2. `‖l‖∞ ≤ 2^{γ−1}` and `‖h‖∞ ≤ B_h` — digit gates.
//!
//! Soundness: the link plus the binding of `A` pins `v` (a second accepting
//! digit pair with a different `v` would yield the short kernel vector
//! `v − v′`, breaking Module-SIS), so the digit gates certify the norm
//! bound `‖v‖∞ ≤ 2^γ·B_h + 2^{γ−1}` (see [`certified_bound`]). A prover
//! whose `v` actually violates the bound cannot shrink the high digits: the
//! exact link forces the revealed `h` to be the true high part of `v`.
//!
//! Where the bound has content: `B_h` is the *accounting* bound the caller
//! carries for the high digits (e.g. the high part of a batched-opening
//! response whose low part was peeled off — a recursion commits exactly
//! these `h` under a fresh Ajtai key and proves their shortness at the
//! next level, shrinking `B_h` level by level). This module is the
//! reusable core step of that recursion, and of the LatticeFold-style
//! quotient/residue checks ([`crate::folding::latticefold`]).
//!
//! Relation to the literature: LaBRADOR's *own* shortness proof is a
//! different, l2-based mechanism (modular Johnson–Lindenstrauss projections
//! carried as extra inner-product equations, norm gap ≈ 2.07) — a sister
//! primitive, not implemented here. This module is the decomposition-digit
//! variant shared by LaBRADOR's per-round norm control, LNP22 and
//! LatticeFold.

use crate::commitment::key::AjtaiKey;
use crate::foundation::encoding::{ring_from_u32, ring_to_u32};
use crate::foundation::fs::absorb_rings;
use crate::foundation::sampling::{from_centered, hyperball_ring_from_seed};
use crate::instance::ring::{infinity_norm, pow2_const, Z2Coeff, Z2Ring, D};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Shake128Xof;
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};

/// Ajtai commitment key for shortness arguments: `A ∈ R^{N×M}` derived from
/// a seed — the shared [`AjtaiKey`] under the protocol-historical name.
pub type ShortKey<const N: usize, const M: usize> = AjtaiKey<N, M>;

/// The norm bound a projection proof certifies: `2^γ·B_h + 2^{γ−1}`.
pub fn certified_bound(gamma: u32, high_bound: u64) -> u64 {
    (1u64 << gamma) * high_bound + (1u64 << (gamma - 1))
}

/// Balanced `2^γ` split of one ring vector: `v = 2^γ·high + low` **exactly**
/// in the ring, with `‖low‖∞ ≤ 2^{γ−1}` by construction.
///
/// Per coefficient (centered representative `x`): the low digit is the
/// centered residue of `x` mod `2^γ` (`low ∈ (−2^{γ−1}, 2^{γ−1}]`), and the
/// high part is the exact quotient `(x − low)/2^γ` reduced back into the
/// ring. Because the split is exact per coefficient, the ring identity
/// holds with no carry and no slack.
pub fn split_balanced(v: &[Z2Ring], gamma: u32) -> (Vec<Z2Ring>, Vec<Z2Ring>) {
    debug_assert!((1..32).contains(&gamma));
    let half = 1i64 << (gamma - 1);
    let mut highs = Vec::with_capacity(v.len());
    let mut lows = Vec::with_capacity(v.len());
    for r in v {
        let mut hi_coeffs = [0u32; D];
        let mut lo_coeffs = [0u32; D];
        for ((dst_hi, dst_lo), c) in hi_coeffs
            .iter_mut()
            .zip(lo_coeffs.iter_mut())
            .zip(r.coefficients())
        {
            let x = c.centered();
            let m = x.rem_euclid(1i64 << gamma);
            let low = if m > half { m - (1i64 << gamma) } else { m };
            let high = (x - low) >> gamma;
            *dst_hi = from_centered::<Z2Coeff>(high).to_u128() as u32;
            *dst_lo = from_centered::<Z2Coeff>(low).to_u128() as u32;
        }
        highs.push(ring_from_u32(&hi_coeffs));
        lows.push(ring_from_u32(&lo_coeffs));
    }
    (highs, lows)
}

/// Rebuilds `2^γ·high + low` (the exact inverse of [`split_balanced`]).
pub fn join_balanced(high: &[Z2Ring], low: &[Z2Ring], gamma: u32) -> Vec<Z2Ring> {
    debug_assert_eq!(high.len(), low.len());
    let mut out = Vec::with_capacity(high.len());
    for (h, l) in high.iter().zip(low) {
        let hc = ring_to_u32(h);
        let lc = ring_to_u32(l);
        let mut coeffs = [0u32; D];
        for j in 0..D {
            coeffs[j] = (hc[j] << gamma).wrapping_add(lc[j]);
        }
        out.push(ring_from_u32(&coeffs));
    }
    out
}

/// FS challenge for a projection statement: a small-norm ring element
/// (`‖ζ‖∞ ≤ b`, `‖ζ‖₁ ≤ B`) derived from the transcript
/// `H(key seed ‖ c ‖ t)` — the hyperball distribution keeps the caller's
/// norm accounting tight (`‖ζ·t‖∞ ≤ ‖ζ‖₁·‖t‖∞`).
pub fn projection_challenge<const N: usize, const M: usize>(
    key_seed: &[u8; 32],
    c: &[Z2Ring],
    t: &[Z2Ring],
    coeff_bound: u32,
    l1_bound: u64,
) -> Z2Ring {
    let mut tr = Transcript::<Shake128Xof>::new(b"lattice-algebra/Z5/projection");
    tr.absorb(b"key", key_seed);
    absorb_rings(&mut tr, b"c", c);
    absorb_rings(&mut tr, b"t", t);
    let seed = tr.challenge_bytes(64);
    hyperball_ring_from_seed::<Z2Coeff, D>(b"zeta", &seed, coeff_bound, l1_bound)
}

/// Proof for the projection statement: the two digit vectors of the balanced
/// split (both short — that is the point of the argument).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProjectionProof<const M: usize> {
    /// High part `h` of `v = 2^γ·h + l` (must satisfy `‖h‖∞ ≤ B_h`).
    pub high: Vec<Z2Ring>,
    /// Low part `l` (bounded by construction: `‖l‖∞ ≤ 2^{γ−1}`).
    pub low: Vec<Z2Ring>,
}

/// Proves the projection statement `‖w − ζ·t‖∞ ≤ certified_bound(γ, B_h)`
/// for the committed vector `c = A·w`.
pub fn prove_projection<const N: usize, const M: usize>(
    w: &[Z2Ring],
    t: &[Z2Ring],
    zeta: &Z2Ring,
    gamma: u32,
) -> ProjectionProof<M> {
    debug_assert_eq!(w.len(), M);
    debug_assert_eq!(t.len(), M);
    let zeta_t: Vec<Z2Ring> = t.iter().map(|ti| zeta.clone() * ti.clone()).collect();
    let v: Vec<Z2Ring> = w
        .iter()
        .zip(&zeta_t)
        .map(|(wi, zti)| wi.clone() - zti.clone())
        .collect();
    let (high, low) = split_balanced(&v, gamma);
    ProjectionProof { high, low }
}

/// Verifies the projection statement. `c = A·w` is the public commitment,
/// `high_bound` the claimed `B_h`; acceptance certifies
/// `‖w − ζ·t‖∞ ≤ certified_bound(γ, B_h)`.
pub fn verify_projection<const N: usize, const M: usize>(
    key: &ShortKey<N, M>,
    c: &[Z2Ring],
    t: &[Z2Ring],
    zeta: &Z2Ring,
    gamma: u32,
    high_bound: u64,
    proof: &ProjectionProof<M>,
) -> bool {
    if proof.high.len() != M || proof.low.len() != M || c.len() != N || t.len() != M {
        return false;
    }
    // digit gates
    if infinity_norm(&proof.low) > 1u64 << (gamma - 1) {
        return false;
    }
    if infinity_norm(&proof.high) > high_bound {
        return false;
    }
    // exact linear link: A·(2^γ·h + l) == c − ζ·(A·t)
    let s = pow2_const(gamma);
    let recon: Vec<Z2Ring> = proof
        .high
        .iter()
        .zip(&proof.low)
        .map(|(h, l)| s.clone() * h.clone() + l.clone())
        .collect();
    let lhs = key.mul_vec(&recon);
    let at = key.mul_vec(t);
    let rhs: Vec<Z2Ring> = c
        .iter()
        .zip(&at)
        .map(|(ci, ati)| ci.clone() - zeta.clone() * ati.clone())
        .collect();
    lhs == rhs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::encoding::ring_from_u32;
    use algebra::crypto::xof::Xof;
    use algebra::ring::MatrixElement;

    const N: usize = 8;
    const M: usize = 4;

    fn seed32(tag: &[u8]) -> [u8; 32] {
        let mut s = [0u8; 32];
        s[..tag.len()].copy_from_slice(tag);
        s
    }

    fn rnd_ring(xof: &mut Shake128Xof, mask: u32) -> Z2Ring {
        let mut coeffs = [0u32; D];
        let mut buf = [0u8; 4];
        for c in &mut coeffs {
            xof.squeeze(&mut buf);
            *c = u32::from_le_bytes(buf) & mask;
        }
        ring_from_u32(&coeffs)
    }

    fn rnd_vec(xof: &mut Shake128Xof, len: usize, mask: u32) -> Vec<Z2Ring> {
        (0..len).map(|_| rnd_ring(xof, mask)).collect()
    }

    #[test]
    fn split_is_exact_with_bounded_low_digits() {
        let mut xof = Shake128Xof::new(&[]);
        let v = rnd_vec(&mut xof, M, u32::MAX);
        for gamma in [1u32, 4, 8, 12, 24] {
            let (high, low) = split_balanced(&v, gamma);
            assert_eq!(
                join_balanced(&high, &low, gamma),
                v,
                "balanced split must reconstruct exactly (γ = {gamma})"
            );
            assert!(
                infinity_norm(&low) <= 1u64 << (gamma - 1),
                "low digits exceed the balanced bound (γ = {gamma})"
            );
        }
    }

    #[test]
    fn honest_projection_verifies_and_bound_holds() {
        let key_seed = seed32(b"short-key-0");
        let key = ShortKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"witness");
        // w with 16-bit coefficients, t with 4-bit coefficients
        let w = rnd_vec(&mut xof, M, 0xFFFF_0000);
        let t = rnd_vec(&mut xof, M, 0x0000_000F);
        let c = key.mul_vec(&w);

        let zeta = projection_challenge::<N, M>(&key_seed, &c, &t, 1, 56);
        let gamma = 12;
        let proof = prove_projection::<N, M>(&w, &t, &zeta, gamma);

        // Pick B_h as the honest high norm; the certified bound must cover
        // the true ‖v‖∞ (it is a provable over-approximation).
        let v_norm = infinity_norm(&{
            let zt: Vec<Z2Ring> = t.iter().map(|ti| zeta.clone() * ti.clone()).collect();
            w.iter()
                .zip(&zt)
                .map(|(a, b)| a.clone() - b.clone())
                .collect::<Vec<Z2Ring>>()
        });
        let high_bound = infinity_norm(&proof.high);
        assert!(verify_projection::<N, M>(
            &key, &c, &t, &zeta, gamma, high_bound, &proof
        ));
        assert!(v_norm <= certified_bound(gamma, high_bound));
    }

    #[test]
    fn tampered_digit_breaks_the_link() {
        let key_seed = seed32(b"short-key-1");
        let key = ShortKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"witness");
        let w = rnd_vec(&mut xof, M, 0xFFFF_0000);
        let t = rnd_vec(&mut xof, M, 0x0000_000F);
        let c = key.mul_vec(&w);
        let zeta = projection_challenge::<N, M>(&key_seed, &c, &t, 1, 56);
        let gamma = 8;
        let mut proof = prove_projection::<N, M>(&w, &t, &zeta, gamma);

        // flip one low-digit bit: exact link must fail
        let mut coeffs = ring_to_u32(&proof.low[0]);
        coeffs[0] ^= 1;
        proof.low[0] = ring_from_u32(&coeffs);
        let high_bound = infinity_norm(&proof.high);
        assert!(!verify_projection::<N, M>(
            &key, &c, &t, &zeta, gamma, high_bound, &proof
        ));
    }

    #[test]
    fn overclaimed_bound_is_rejected() {
        let key_seed = seed32(b"short-key-2");
        let key = ShortKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"witness");
        let w = rnd_vec(&mut xof, M, 0xFFFF_0000);
        let t = rnd_vec(&mut xof, M, 0x0000_000F);
        let c = key.mul_vec(&w);
        let zeta = projection_challenge::<N, M>(&key_seed, &c, &t, 1, 56);
        let gamma = 8;
        let proof = prove_projection::<N, M>(&w, &t, &zeta, gamma);
        let high_norm = infinity_norm(&proof.high);
        assert!(high_norm > 0, "test expects a non-trivial high norm");
        assert!(!verify_projection::<N, M>(
            &key,
            &c,
            &t,
            &zeta,
            gamma,
            high_norm - 1,
            &proof
        ));
    }

    #[test]
    fn false_shortness_claim_cannot_pass_a_tight_gate() {
        // A prover whose v genuinely has huge high digits cannot shrink
        // them: the exact link forces h to be the true high part of v.
        let key_seed = seed32(b"short-key-3");
        let key = ShortKey::<N, M>::setup(&key_seed);
        let mut xof = Shake128Xof::new(&[]);
        xof.absorb(b"huge-witness");
        let w = rnd_vec(&mut xof, M, u32::MAX); // full-entropy coefficients
        let t = vec![Z2Ring::zero(); M];
        let c = key.mul_vec(&w);
        let zeta = projection_challenge::<N, M>(&key_seed, &c, &t, 1, 56);
        let gamma = 8;
        let proof = prove_projection::<N, M>(&w, &t, &zeta, gamma);
        // Claim a small B_h: the honest (forced) high digits must fail it.
        assert!(infinity_norm(&proof.high) > 1_000);
        assert!(!verify_projection::<N, M>(
            &key, &c, &t, &zeta, gamma, 1_000, &proof
        ));
    }
}
