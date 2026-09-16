//! Wire-format helpers (L5 utilities): ring elements ↔ little-endian bytes.
//!
//! Two consumers with different granularity share these conversions:
//! transcripts absorb coefficient bytes to bind public values, and proofs
//! serialize responses for the wire. Both use the same canonical encoding —
//! raw little-endian `u32` coefficients in ascending power order — so
//! "what the verifier re-absorbs" and "what the prover sends" can never
//! drift apart.

use algebra::ring::poly_ring::PolyRing;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;

/// Packs a slice of `u32`s into little-endian bytes.
pub fn u32s_to_le_bytes(values: &[u32]) -> Vec<u8> {
    values.iter().flat_map(|v| v.to_le_bytes()).collect()
}

/// Unpacks little-endian bytes into `u32`s (inverse of [`u32s_to_le_bytes`]).
///
/// Returns `None` unless `bytes.len()` is a multiple of 4.
pub fn le_bytes_to_u32s(bytes: &[u8]) -> Option<Vec<u32>> {
    if bytes.len() % 4 != 0 {
        return None;
    }
    Some(
        bytes
            .chunks_exact(4)
            .map(|c| u32::from_le_bytes(c.try_into().expect("chunk of 4")))
            .collect(),
    )
}

/// Raw `u32` coefficients of a ring element (ascending powers).
///
/// # Panics
/// If the modulus exceeds `2^32` — then the canonical representatives
/// `0..q` no longer fit in a `u32` and the wire encoding cannot represent
/// them.
pub fn ring_to_u32<R: Ring, const N: usize>(r: &PolyRing<R, N>) -> [u32; N] {
    assert!(
        R::MODULUS <= u64::from(u32::MAX) + 1,
        "ring modulus {} does not fit the u32 wire encoding",
        R::MODULUS
    );
    let mut out = [0u32; N];
    for (dst, c) in out.iter_mut().zip(r.coefficients()) {
        *dst = c.to_u128() as u32;
    }
    out
}

/// Builds a ring element from raw `u32` coefficients (ascending powers).
///
/// # Panics
/// If the modulus exceeds `2^32` (see [`ring_to_u32`]).
pub fn ring_from_u32<R: Ring, const N: usize>(coeffs: &[u32; N]) -> PolyRing<R, N> {
    assert!(
        R::MODULUS <= u64::from(u32::MAX) + 1,
        "ring modulus {} does not fit the u32 wire encoding",
        R::MODULUS
    );
    PolyRing::from_coefficients(coeffs.iter().map(|&c| R::from(u64::from(c))).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    type R32 = Zq<4294967296>;

    #[test]
    fn u32_packing_roundtrip() {
        let values = [0u32, 1, 0xDEAD_BEEF, u32::MAX];
        let bytes = u32s_to_le_bytes(&values);
        assert_eq!(bytes.len(), 16);
        assert_eq!(le_bytes_to_u32s(&bytes).as_deref(), Some(values.as_slice()));
        assert_eq!(le_bytes_to_u32s(&bytes[..15]), None);
    }

    #[test]
    fn ring_u32_roundtrip() {
        let mut coeffs = [0u32; 16];
        coeffs[0] = 0x1234_5678;
        coeffs[15] = 42;
        let r = ring_from_u32::<R32, 16>(&coeffs);
        assert_eq!(ring_to_u32(&r), coeffs);
    }

    #[test]
    fn ring_encoding_matches_manual_byte_packing() {
        // Pin the historical encoding: each coefficient as 4 LE bytes.
        let mut coeffs = [0u32; 4];
        coeffs[1] = 0xAABB_CCDD;
        let r = ring_from_u32::<R32, 4>(&coeffs);
        assert_eq!(
            u32s_to_le_bytes(&ring_to_u32(&r)),
            u32s_to_le_bytes(&coeffs)
        );
    }
}
