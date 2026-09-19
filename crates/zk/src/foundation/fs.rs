//! Fiat–Shamir challenge derivation (L5 utilities).
//!
//! Every FS-compiled protocol in this crate follows the same three-step
//! shape:
//!
//! 1. absorb the bound public values into a domain-separated
//!    [`Transcript`];
//! 2. squeeze a seed (`challenge_bytes`);
//! 3. re-expand the seed in a **fresh**, labeled XOF stream and shape the
//!    challenge from it (uniform ring element, sparse in-ball polynomial,
//!    non-unit linear challenge — see [`crate::foundation::sampling`]).
//!
//! Step 3 uses a new XOF instance (rather than squeezing the transcript
//! directly) so that differently-shaped challenges are drawn from
//! independently labeled streams — the FIPS 203/204 derivation pattern.
//! [`seed_stream`] implements it; [`absorb_rings`] implements the
//! absorb-half for ring vectors.

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::Ring;
// Needed only under some `cfg` (test or feature); the plain lib build
// does not use it, so the lint cannot be satisfied by deleting it.
#[allow(unused_imports)]
use alloc::vec::Vec;

use crate::foundation::encoding::{ring_to_u32, u32s_to_le_bytes};

/// Expands a Fiat–Shamir seed into a fresh XOF stream bound to `domain`.
///
/// `seed` is typically `Transcript::challenge_bytes` output; the fresh
/// instance + label keeps per-challenge-shape streams independent.
pub fn seed_stream<X: Xof>(domain: &[u8], seed: &[u8]) -> X {
    let mut xof = X::new(&[]);
    xof.absorb(domain);
    xof.absorb(seed);
    xof
}

/// Absorbs a vector of ring elements into the transcript under one label.
///
/// Coefficients are serialized as raw little-endian `u32`s (ascending
/// powers) — the canonical transcript encoding for moduli up to `2^32`.
pub fn absorb_rings<X: Xof, R: Ring, const N: usize>(
    transcript: &mut Transcript<X>,
    label: &[u8],
    rings: &[PolyRing<R, N>],
) {
    for r in rings {
        transcript.absorb(label, &u32s_to_le_bytes(&ring_to_u32(r)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::crypto::xof::Shake256Xof;
    use algebra::ring::zq::Zq;
    use algebra::ring::PolynomialQuotientRing;

    type R32 = Zq<4294967296>;

    #[test]
    fn seed_stream_is_deterministic_and_domain_separated() {
        let draw = |domain: &[u8]| {
            let mut x = seed_stream::<Shake256Xof>(domain, b"seed");
            x.squeeze_vec(32)
        };
        assert_eq!(draw(b"a"), draw(b"a"));
        assert_ne!(draw(b"a"), draw(b"b"));
    }

    #[test]
    fn absorb_rings_matches_manual_absorb() {
        let rings: Vec<PolyRing<R32, 8>> = (0..3)
            .map(|i| {
                let mut coeffs = [0u32; 8];
                coeffs[0] = i + 1;
                PolyRing::from_coefficients(
                    coeffs.iter().map(|&c| R32::from(u64::from(c))).collect(),
                )
            })
            .collect();

        let manual = |domain: &[u8]| -> Vec<u8> {
            let mut tr = Transcript::<Shake256Xof>::new(domain);
            for r in &rings {
                tr.absorb(b"lbl", &u32s_to_le_bytes(&ring_to_u32(r)));
            }
            tr.challenge_bytes(32)
        };
        let helper = |domain: &[u8]| -> Vec<u8> {
            let mut tr = Transcript::<Shake256Xof>::new(domain);
            absorb_rings(&mut tr, b"lbl", &rings);
            tr.challenge_bytes(32)
        };
        assert_eq!(manual(b"eq"), helper(b"eq"));
    }
}
