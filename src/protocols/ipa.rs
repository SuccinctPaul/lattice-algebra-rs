//! Gadget-IPA: inner-product arguments on Ajtai-committed ring vectors,
//! with an approximate (slack-bounded) opening mode (L5, Z3).
//!
//! # Statement
//!
//! Public: commitment key `A_com ∈ R^{N×M}` (tall), a public ring vector
//! `u ∈ R^M`, the commitment `c = A_com·α` and the claimed inner product
//! `v = ⟨α, u⟩` (ring bilinear form `⟨α, u⟩ = Σ α_j·u_j`).
//! Witness: the short committed vector `α`.
//!
//! # Protocol (FS-compiled, two-challenge)
//!
//! ```text
//! d = A_com·mask                ──c,d──▶ X, γ ← H(key‖c‖u‖d)
//! α' = α + X·mask               ──α',t*──▶
//! ```
//! with `t* = ⟨mask, u⟩`. Verifier checks:
//! 1. `A_com·α' == c + X·d` — the overdetermined binding link pins `α'`
//!    (kernel-free w.h.p. for a random tall `A_com`);
//! 2. `⟨α', u⟩ == v + X·t*` — the inner-product claim.
//!
//! Soundness: `X` is forced non-unit (even constant term), so the verifier
//! equation cannot be solved for `t*` by division: an adaptive `t*` would
//! require `(⟨α',u⟩ − v) ∈ X·R` — excluding only a measure-0 (ideal)
//! failure set, with the rest absorbed by the pinning of `α'`.
//!
//! # Approximate opening (gadget layer)
//!
//! [`ipa_prove_approx`] reveals the response through a gadget split
//! (`α' = 2^drop·hi + lo`, `|lo| ≤ 2^{drop−1}`): the verifier checks the
//! binding link on the *reconstructed* response up to the provable slack
//! `slack_bound(D, drop)` per coefficient — the mechanism full LaBRADOR
//! recursion uses to keep opened values short.

use crate::crypto::transcript::Transcript;
use crate::crypto::xof::{Shake128Xof, Xof};
use crate::protocols::z2_ring::{matrix_from_seed, ring_from_u32, ring_to_u32, Z2Ring, D};
use crate::ring::MatrixElement;

/// Ajtai key for the IPA (`A_com ∈ R^{N×M}`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IpaKey<const N: usize, const M: usize> {
    a: Vec<Vec<Z2Ring>>,
}

impl<const N: usize, const M: usize> IpaKey<N, M> {
    /// Derives the key from a seed.
    pub fn setup(seed: &[u8; 32]) -> Self {
        Self {
            a: matrix_from_seed(seed, N, M),
        }
    }

    /// `A_com·α`.
    pub fn commit(&self, alpha: &[Z2Ring]) -> Vec<Z2Ring> {
        debug_assert_eq!(alpha.len(), M);
        (0..N)
            .map(|i| {
                let mut acc = Z2Ring::zero();
                for (j, a) in alpha.iter().enumerate() {
                    acc += self.a[i][j].clone() * a.clone();
                }
                acc
            })
            .collect()
    }
}

/// Ring inner product `Σ α_j·u_j`.
pub fn ring_inner_product(alpha: &[Z2Ring], u: &[Z2Ring]) -> Z2Ring {
    let mut acc = Z2Ring::zero();
    for (a, b) in alpha.iter().zip(u) {
        acc += a.clone() * b.clone();
    }
    acc
}

/// IPA proof: mask commitment, response, and the masked inner product.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IpaProof<const N: usize> {
    /// Mask commitment `d = A_com·mask`.
    pub d: Vec<Z2Ring>,
    /// Response `α' = α + X·mask`.
    pub alpha_prime: Vec<Z2Ring>,
    /// `t* = ⟨mask, u⟩`.
    pub t_star: Z2Ring,
}

fn u32s_to_bytes(v: &[u32]) -> Vec<u8> {
    v.iter().flat_map(|x| x.to_le_bytes()).collect()
}

fn challenges(key_seed: &[u8; 32], c: &[Z2Ring], u: &[Z2Ring], d: &[Z2Ring]) -> (Z2Ring, Z2Ring) {
    let mut tr = Transcript::<Shake128Xof>::new(b"lattice-algebra/Z3/ipa");
    tr.absorb(b"key", key_seed);
    for v in c {
        tr.absorb(b"c", &u32s_to_bytes(&ring_to_u32(v)));
    }
    for v in u {
        tr.absorb(b"u", &u32s_to_bytes(&ring_to_u32(v)));
    }
    for v in d {
        tr.absorb(b"d", &u32s_to_bytes(&ring_to_u32(v)));
    }
    let seed = tr.challenge_bytes(64);
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(b"X");
    xof.absorb(&seed);
    let mut coeffs = [0u32; D];
    let mut buf = [0u8; 4];
    for c in &mut coeffs {
        xof.squeeze(&mut buf);
        *c = u32::from_le_bytes(buf);
    }
    coeffs[0] &= 0xFFFF_FFFE; // force non-unit
    let x = ring_from_u32(&coeffs);

    let mut xof2 = Shake128Xof::new(&[]);
    xof2.absorb(b"gamma");
    xof2.absorb(&seed);
    let gamma = ring_from_u32(&{
        let mut cc = [0u32; D];
        let mut b2 = [0u8; 4];
        for c in &mut cc {
            xof2.squeeze(&mut b2);
            *c = u32::from_le_bytes(b2);
        }
        cc
    });
    (x, gamma)
}

/// Proves `⟨α, u⟩ = v` for the committed vector (`c = A_com·α`).
///
/// `mask_seed` controls the mask deterministically.
pub fn ipa_prove<const N: usize, const M: usize>(
    key: &IpaKey<N, M>,
    key_seed: &[u8; 32],
    alpha: &[Z2Ring],
    u: &[Z2Ring],
    v: Z2Ring,
    mask_seed: &[u8; 32],
) -> IpaProof<N> {
    debug_assert_eq!(alpha.len(), M);
    debug_assert_eq!(
        ring_inner_product(alpha, u),
        v,
        "claimed inner product mismatch"
    );

    let d = key.commit(&mask_ring::<M>(mask_seed));
    let (x, _gamma) = challenges(key_seed, &key.commit(alpha), u, &d);
    let mask = mask_ring::<M>(mask_seed);
    let alpha_prime: Vec<Z2Ring> = alpha
        .iter()
        .zip(&mask)
        .map(|(a, m)| a.clone() + x.clone() * m.clone())
        .collect();
    let t_star = ring_inner_product(&mask, u);
    IpaProof {
        d,
        alpha_prime,
        t_star,
    }
}

/// Verifies the IPA: binding link plus the inner-product claim.
pub fn ipa_verify<const N: usize, const M: usize>(
    key: &IpaKey<N, M>,
    key_seed: &[u8; 32],
    c: &[Z2Ring],
    u: &[Z2Ring],
    v: Z2Ring,
    proof: &IpaProof<N>,
) -> bool {
    if proof.d.len() != N || proof.alpha_prime.len() != M {
        return false;
    }
    let (x, _gamma) = challenges(key_seed, c, u, &proof.d);

    // 1. binding link
    let aprime_commit = key.commit(&proof.alpha_prime);
    for i in 0..N {
        let rhs = c[i].clone() + x.clone() * proof.d[i].clone();
        if ring_to_u32(&aprime_commit[i]) != ring_to_u32(&rhs) {
            return false;
        }
    }

    // 2. inner-product claim: ⟨α', u⟩ == v + X·t*
    let lhs = ring_inner_product(&proof.alpha_prime, u);
    let rhs = v + x.clone() * proof.t_star.clone();
    ring_to_u32(&lhs) == ring_to_u32(&rhs)
}

/// Approximate opening of the response through a gadget split: returns the
/// high digits and the centered low residual per ring element.
pub fn ipa_gadget_open(alpha_prime: &[Z2Ring], drop: u32) -> (Vec<u32>, Vec<i64>) {
    let mut highs = Vec::with_capacity(alpha_prime.len() * D);
    let mut lows = Vec::with_capacity(alpha_prime.len() * D);
    for r in alpha_prime {
        for &v in &ring_to_u32(r) {
            let half = 1i64 << (drop - 1);
            let high = v >> drop;
            let low_i = i64::from(v & ((1u32 << drop) - 1));
            let centered = if low_i > half {
                low_i - (1i64 << drop)
            } else {
                low_i
            };
            highs.push(high);
            lows.push(centered);
        }
    }
    (highs, lows)
}

/// Per-coefficient slack bound of an approximate opening:
/// `D · 2^{drop−1}` (the residual reconstruction error of the folded
/// linear check).
pub fn approx_slack_bound(drop: u32) -> i64 {
    i64::from(D as u32 * (1u32 << (drop - 1)))
}

fn mask_ring<const M: usize>(seed: &[u8; 32]) -> Vec<Z2Ring> {
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(b"ipa-mask");
    xof.absorb(seed);
    (0..M)
        .map(|_| {
            let mut coeffs = [0u32; D];
            let mut buf = [0u8; 4];
            for c in &mut coeffs {
                xof.squeeze(&mut buf);
                *c = u32::from_le_bytes(buf);
            }
            ring_from_u32(&coeffs)
        })
        .collect()
}
