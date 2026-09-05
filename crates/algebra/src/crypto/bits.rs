//! Bit-level packing of coefficient vectors (L4, wire format).
//!
//! NIST PQC wire formats pack `q`-ary coefficients into fixed-width bit
//! fields (ML-KEM 12-bit public keys, ML-DSA 13/18/20-bit signature parts).
//! Bit order is little-endian within bytes, matching the specifications.

/// Ceiling division by 8.
#[inline]
pub(crate) fn div_ceil8(x: usize) -> usize {
    x.div_ceil(8)
}

/// Appends `bits`-per-coefficient encodings of `coeffs` to `out` (bit-LSB
/// first within each byte). The output bit length is `coeffs.len() * bits`,
/// zero-padded to a whole byte.
///
/// # Panics
/// If any coefficient is `>= 2^bits`.
pub fn pack_bits(coeffs: &[u64], bits: u32, out: &mut Vec<u8>) {
    assert!(bits > 0 && bits <= 32, "unsupported field width");
    let max = 1u64 << bits;
    let total_bits = coeffs.len() * bits as usize;
    out.resize(out.len() + div_ceil8(total_bits), 0);
    // Fields occupy the front of the appended region bit-by-bit; only the
    // high bits of the very last byte are zero padding.
    let start_bit = out.len() * 8 - div_ceil8(total_bits) * 8;

    for (i, &c) in coeffs.iter().enumerate() {
        assert!(c < max, "coefficient {c} does not fit in {bits} bits");
        for b in 0..bits {
            let bit = (c >> b) & 1;
            if bit == 1 {
                let pos = start_bit + i * bits as usize + b as usize;
                out[pos / 8] |= 1 << (pos % 8);
            }
        }
    }
}

/// Inverse of [`pack_bits`]: reads `n` coefficients of `bits` bits each from
/// the front of `bytes`, returning them and consuming the packed prefix.
///
/// # Panics
/// If `bytes` is shorter than `n * bits` bits.
pub fn unpack_bits(bytes: &mut &[u8], n: usize, bits: u32) -> Vec<u64> {
    let total_bits = n * bits as usize;
    assert!(
        bytes.len() * 8 >= total_bits,
        "not enough bytes to unpack {n} x {bits} bits"
    );

    let mut out = Vec::with_capacity(n);
    let mut pos = 0usize;
    for _ in 0..n {
        let mut v = 0u64;
        for b in 0..bits as usize {
            let bit = (bytes[pos / 8] >> (pos % 8)) & 1;
            v |= (bit as u64) << b;
            pos += 1;
        }
        out.push(v);
    }
    *bytes = &bytes[div_ceil8(total_bits)..];
    out
}

/// Encodes coefficients that are already reduced to `< 2^bits` into a
/// fixed-size byte vector.
pub fn to_packed_bytes(coeffs: &[u64], bits: u32) -> Vec<u8> {
    let mut out = Vec::with_capacity(div_ceil8(coeffs.len() * bits as usize));
    pack_bits(coeffs, bits, &mut out);
    out
}

/// Decodes a full packed buffer (inverse of [`to_packed_bytes`]).
pub fn from_packed_bytes(bytes: &[u8], n: usize, bits: u32) -> Vec<u64> {
    let mut slice = bytes;
    unpack_bits(&mut slice, n, bits)
}

/// High-bit compression used by ML-KEM/ML-DSA encodings: keeps the top
/// `bits` of each coefficient (i.e. drops the trailing `drop` bits).
///
/// Values are taken modulo `q`: coefficients in `[0, q)` are first scaled
/// `>> drop`, so the output fits in `bitlen(q - 1) - drop` bits.
pub fn compress_high(coeffs: &[u64], q: u64, drop: u32) -> Vec<u64> {
    coeffs.iter().map(|&c| (c % q) >> drop).collect()
}

/// Decompresses [`compress_high`] output back into `[0, q)` by shifting left
/// (no rounding, matching the coarse ML-KEM `Decompress` shape used in tests).
pub fn decompress_high(compressed: &[u64], drop: u32) -> Vec<u64> {
    compressed.iter().map(|&c| c << drop).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip_12_bit() {
        let coeffs: Vec<u64> = (0..256).map(|i| (i * 13) % 3329).collect();
        let packed = to_packed_bytes(&coeffs, 12);
        assert_eq!(packed.len(), 256 * 12 / 8);
        assert_eq!(from_packed_bytes(&packed, 256, 12), coeffs);
    }

    #[test]
    fn roundtrip_13_18_20_bit_odd_widths() {
        for bits in [13u32, 18, 20, 23] {
            let n = 37; // non-multiple of 8 exercises padding
            let coeffs: Vec<u64> = (0..n).map(|i| (i as u64 * 2654435761) >> 8).collect();
            let coeffs: Vec<u64> = coeffs.iter().map(|&c| c % (1u64 << bits)).collect();
            let packed = to_packed_bytes(&coeffs, bits);
            assert_eq!(packed.len(), div_ceil8(n * bits as usize));
            assert_eq!(from_packed_bytes(&packed, n, bits), coeffs);
        }
    }

    #[test]
    #[should_panic(expected = "does not fit")]
    fn rejects_oversized_coefficients() {
        to_packed_bytes(&[4096], 12);
    }

    #[test]
    fn compress_decompress_roundtrip_shape() {
        let q = 8380417u64;
        let coeffs: Vec<u64> = (0..64).map(|i| (i * 123457) % q).collect();
        let high = compress_high(&coeffs, q, 13);
        assert!(high.iter().all(|&c| c < (q >> 13) + 1));
        let back = decompress_high(&high, 13);
        // Compression is lossy: assert the shape, and that values stay < q.
        assert!(back.iter().all(|&c| c < q));
        // Highest bits survive.
        for (o, &c) in back.iter().zip(&coeffs) {
            assert_eq!(o >> 13, c >> 13);
        }
    }
}
