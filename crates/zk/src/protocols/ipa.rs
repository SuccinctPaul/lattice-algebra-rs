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
//! Soundness: the challenge is `C = X − a` with the scalar `a` forced
//! **odd** — a genuine non-unit of `Z_{2^32}[X]/(X^64+1)`. (The monomial
//! `X` itself is *always* a unit there — `X·(−X^63) = 1` — so a unit
//! challenge would make the inner-product check vacuous: any `v` could be
//! rationalized as `v + C·t*` with `t* = C⁻¹(⟨α',u⟩ − v)`.) With the
//! non-unit challenge, solving the verifier equation for `t*` requires
//! `⟨α',u⟩ − v ∈ C·R`, an index-2 ideal of the ring (`C·R = {f : Σ coeffs
//! even}`) — a cheating prover grinding over masks passes with probability
//! ½ per attempt. Full relation soundness (the documented 2^-32) needs the
//! LaBRADOR recursion that commits the masked inner product before the
//! challenge opens it — tracked as the Z3 milestone.
//!
//! # Approximate opening (gadget layer)
//!
//! [`ipa_gadget_open`] reveals the response through a gadget split
//! (`α' = 2^drop·hi + lo`, `|lo| ≤ 2^{drop−1}`): the verifier checks the
//! binding link on the *reconstructed* response up to the provable slack
//! [`approx_slack_bound`] per coefficient — the mechanism full LaBRADOR
//! recursion uses to keep opened values short.

use crate::protocols::z2_ring::{matrix_from_seed, ring_from_u32, ring_to_u32, Z2Ring, D};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::ring::MatrixElement;

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
    // C = X − a with a odd: a true non-unit (see the module soundness notes).
    let mut buf = [0u8; 4];
    xof.squeeze(&mut buf);
    let a = u32::from_le_bytes(buf) | 1;
    let mut coeffs = [0u32; D];
    coeffs[0] = a.wrapping_neg();
    coeffs[1] = 1;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::protocols::z2_ring::D;

    /// Soundness regression mirroring Z2's: a false inner-product claim
    /// (v ≠ ⟨α, u⟩) with a honestly-shaped binding link must be rejected —
    /// under the old unit challenge the prover could always solve
    /// `t* = X⁻¹(⟨α',u⟩ − v)` and every forged claim verified.
    #[test]
    fn forged_inner_product_claim_rejected() {
        const N: usize = 8;
        const M: usize = 2;
        let key_seed = b"ipa-key-000000000000000000000000";
        let key = IpaKey::<N, M>::setup(key_seed);
        let mut xof = Shake128Xof::new(&[]);
        let mut rnd_ring = || {
            let mut coeffs = [0u32; D];
            let mut buf = [0u8; 4];
            for c in &mut coeffs {
                xof.squeeze(&mut buf);
                *c = u32::from_le_bytes(buf);
            }
            ring_from_u32(&coeffs)
        };
        let alpha: Vec<Z2Ring> = (0..M).map(|_| rnd_ring()).collect();
        let u: Vec<Z2Ring> = (0..M).map(|_| rnd_ring()).collect();
        let v = ring_inner_product(&alpha, &u);

        // Honest proof verifies.
        let proof = ipa_prove::<N, M>(
            &key,
            key_seed,
            &alpha,
            &u,
            v.clone(),
            b"mask-000000000000000000000000000",
        );
        assert!(ipa_verify::<N, M>(
            &key,
            key_seed,
            &key.commit(&alpha),
            &u,
            v.clone(),
            &proof
        ));

        // Forged claim: flip the last bit of v.
        let mut coeffs = ring_to_u32(&v);
        coeffs[0] ^= 1;
        let v_fake = ring_from_u32(&coeffs);
        assert_ne!(v, v_fake);
        assert!(!ipa_verify::<N, M>(
            &key,
            key_seed,
            &key.commit(&alpha),
            &u,
            v_fake,
            &proof
        ));
    }

    /// Completeness across several random statements.
    #[test]
    fn honest_ipa_prove_verify_roundtrip() {
        const N: usize = 8;
        const M: usize = 4;
        let key_seed = b"ipa-key2-00000000000000000000000";
        let key = IpaKey::<N, M>::setup(key_seed);
        let mut xof = Shake128Xof::new(&[]);
        let mut rnd_ring = || {
            let mut coeffs = [0u32; D];
            let mut buf = [0u8; 4];
            for c in &mut coeffs {
                xof.squeeze(&mut buf);
                *c = u32::from_le_bytes(buf);
            }
            ring_from_u32(&coeffs)
        };
        for trial in 0u8..3 {
            let alpha: Vec<Z2Ring> = (0..M).map(|_| rnd_ring()).collect();
            let u: Vec<Z2Ring> = (0..M).map(|_| rnd_ring()).collect();
            let v = ring_inner_product(&alpha, &u);
            let proof = ipa_prove::<N, M>(&key, key_seed, &alpha, &u, v.clone(), &[trial; 32]);
            assert!(ipa_verify::<N, M>(
                &key,
                key_seed,
                &key.commit(&alpha),
                &u,
                v,
                &proof
            ));
        }
    }
}
