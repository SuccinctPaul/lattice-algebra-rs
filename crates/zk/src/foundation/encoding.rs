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
use alloc::vec;
use alloc::vec::Vec;

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

/// Bytes per coefficient in the width-generic wire encoding.
///
/// At least 4, so every ring with `q ≤ 2³²` encodes bit-identically to
/// `u32s_to_le_bytes(&ring_to_u32(r))` — transcripts and proof bytes already in
/// the tests depend on that. Above `2³²` the field grows to fit the largest
/// representable value, which is what closes gap G7 for the encoding layer
/// (several schemes in `docs/survey-lattice-pcs.md` need `log q` of 60–276).
pub const fn coeff_wire_bytes(modulus: u64) -> usize {
    // Bit width of `q − 1`, the largest value a coefficient can take.
    let bits = 64 - (modulus - 1).leading_zeros();
    let needed = (bits as usize + 7) / 8;
    if needed < 4 {
        4
    } else {
        needed
    }
}

/// Raw little-endian coefficients of a ring element, `W` bytes per coefficient
/// where `W = coeff_wire_bytes(q)` (ascending powers).
///
/// Unlike [`ring_to_u32`] this never refuses a large modulus, so it is the
/// encoding a scheme with `q > 2³²` absorbs and serializes with. Every slot is
/// emitted even when [`PolyRing`] trimmed the trailing zeros that produced it.
pub fn ring_to_le_bytes<R: Ring, const N: usize>(r: &PolyRing<R, N>) -> Vec<u8> {
    let width = coeff_wire_bytes(R::MODULUS);
    let mut out = vec![0u8; N * width];
    for (i, c) in r.coefficients().iter().enumerate().take(N) {
        let v = c.to_u128().to_le_bytes();
        out[i * width..(i + 1) * width].copy_from_slice(&v[..width]);
    }
    out
}

/// Inverse of [`ring_to_le_bytes`].
///
/// Returns `None` unless `bytes.len()` is exactly `N * coeff_wire_bytes(q)`.
pub fn ring_from_le_bytes<R: Ring, const N: usize>(bytes: &[u8]) -> Option<PolyRing<R, N>> {
    let width = coeff_wire_bytes(R::MODULUS);
    if bytes.len() != N * width {
        return None;
    }
    let mut coeffs = Vec::with_capacity(N);
    for chunk in bytes.chunks_exact(width) {
        let mut raw = [0u8; 16];
        raw[..width].copy_from_slice(chunk);
        coeffs.push(R::from(u128::from_le_bytes(raw) as u64));
    }
    Some(PolyRing::from_coefficients(coeffs))
}

/// `u64` representatives of a ring element (ascending powers).
///
/// The `u32` form [`ring_to_u32`] refuses moduli above `2³²`; this is the same
/// canonical-representative view for the whole `u64` range a [`Ring`] can
/// carry, which is what the wide gadget and projection paths need.
pub fn ring_to_u64<R: Ring, const N: usize>(r: &PolyRing<R, N>) -> [u64; N] {
    let mut out = [0u64; N];
    for (dst, c) in out.iter_mut().zip(r.coefficients()) {
        *dst = c.to_u128() as u64;
    }
    out
}

/// Builds a ring element from raw `u64` coefficients (ascending powers).
pub fn ring_from_u64<R: Ring, const N: usize>(coeffs: &[u64; N]) -> PolyRing<R, N> {
    PolyRing::from_coefficients(coeffs.iter().map(|&c| R::from(c)).collect())
}

#[cfg(test)]
mod wide_tests {
    use super::*;
    use algebra::ring::zq::Zq;

    /// `Z1`, the crate's ML-DSA-shaped prime.
    type Small = Zq<8380417>;
    /// Exactly `2³²`, the boundary [`ring_to_u32`] still accepts.
    type Boundary = Zq<4294967296>;
    /// The largest known 64-bit prime — `2⁶⁴ − 59`, far past the `u32` wall.
    type Wide = Zq<18446744073709551557>;

    #[test]
    fn wire_width_fits_the_modulus_and_never_shrinks_below_four() {
        assert_eq!(coeff_wire_bytes(8380417), 4);
        assert_eq!(coeff_wire_bytes(4093), 4, "clamped, not 2");
        assert_eq!(coeff_wire_bytes(4294967296), 4, "q = 2³² still needs 4 bytes");
        assert_eq!(coeff_wire_bytes(1 << 33), 5);
        assert_eq!(coeff_wire_bytes(u64::MAX), 8);
    }

    #[test]
    fn byte_encoding_matches_the_historical_u32_path_below_2_pow_32() {
        // Transcripts absorb these bytes. If this ever stops holding, every
        // KAT and every FS challenge in the crate changes.
        //
        // The coefficients must be *canonical*: `ring_from_u32` reduces mod q,
        // so a value ≥ q encodes as its residue and would not round-trip to the
        // input bytes (that reduction is what the second half of this test pins).
        let mut coeffs = [0u32; 8];
        coeffs[0] = 8_331_521; // < q, and not a round number in hex
        coeffs[7] = 8_380_416; // q − 1
        let r = ring_from_u32::<Small, 8>(&coeffs);
        assert_eq!(ring_to_le_bytes(&r), u32s_to_le_bytes(&coeffs));
        let b = ring_from_u32::<Boundary, 8>(&[u32::MAX; 8]);
        assert_eq!(ring_to_le_bytes(&b), u32s_to_le_bytes(&[u32::MAX; 8]));

        // 0xFF0102 = 16_711_938 = 8_380_417 + 8_331_521, so it reduces to
        // 8_331_521; both paths agree on that residue, which is why the
        // round-trip assertion above needs canonical inputs.
        let mut unreduced = [0u32; 8];
        unreduced[0] = 16_711_938;
        let r = ring_from_u32::<Small, 8>(&unreduced);
        assert_eq!(ring_to_u32(&r)[0], 8_331_521);
        assert_eq!(ring_to_le_bytes(&r), u32s_to_le_bytes(&ring_to_u32(&r)));
    }

    #[test]
    fn a_modulus_above_2_pow_32_round_trips() {
        // This is gap G7: `ring_to_u32` panics on `Wide`, the byte path does
        // not, and a coefficient that cannot fit 32 bits survives the trip.
        let mut coeffs = [0u64; 4];
        coeffs[0] = 1u64 << 40;
        coeffs[3] = u64::MAX - 60;
        let r = ring_from_u64::<Wide, 4>(&coeffs);
        assert_eq!(ring_to_u64(&r), coeffs);
        let bytes = ring_to_le_bytes(&r);
        assert_eq!(bytes.len(), 4 * 8);
        assert_eq!(ring_from_le_bytes::<Wide, 4>(&bytes), Some(r));
    }

    #[test]
    fn a_trailing_zero_element_still_fills_its_slots() {
        // `PolyRing` trims trailing zeros; the wire form must not.
        let sparse = PolyRing::<Wide, 4>::from_coefficients(vec![Zq::from(7u64)]);
        assert_eq!(ring_to_le_bytes(&sparse).len(), 32);
        let mut expect = [0u64; 4];
        expect[0] = 7;
        assert_eq!(ring_to_u64(&sparse), expect);
        assert_eq!(
            ring_from_le_bytes::<Wide, 4>(&ring_to_le_bytes(&sparse)),
            Some(sparse)
        );
    }

    #[test]
    fn decoding_refuses_the_wrong_length() {
        assert_eq!(ring_from_le_bytes::<Wide, 4>(&[0u8; 31]), None);
        assert_eq!(ring_from_le_bytes::<Small, 2>(&[0u8; 9]), None);
    }
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
