//! FIPS 203 coefficient encodings: `ByteEncode_d`/`ByteDecode_d` and
//! `Compress_d`/`Decompress_d`.
//!
//! Byte encodings pack `d`-bit coefficients LSB-first into bytes; decoding
//! is total over correctly-sized inputs (values ≥ q can arise from hostile
//! ciphertexts and are handled by modular arithmetic downstream). The
//! compress/decompress pair implements the spec's round-half-up rounding in
//! pure integer arithmetic (`q` is odd, so `Compress_d` never hits ties).

use super::params::N;
use super::params::Q;

/// FIPS 203 `ByteEncode_d`: serializes 256 coefficients in `[0, 2^d)` into
/// `32·d` bytes, LSB-first.
pub(crate) fn byte_encode(f: &[u64; N], d: usize) -> Vec<u8> {
    debug_assert!((1..=12).contains(&d), "FIPS 203 uses d ∈ [1, 12]");
    debug_assert!(f.iter().all(|&v| v < 1 << d), "coefficient out of range");
    let mut out = vec![0u8; N * d / 8];
    for (i, &v) in f.iter().enumerate() {
        for j in 0..d {
            let bit = ((v >> j) & 1) as u8;
            let pos = i * d + j;
            out[pos / 8] |= bit << (pos % 8);
        }
    }
    out
}

/// FIPS 203 `ByteDecode_d`: parses `32·d` bytes into 256 `d`-bit integers.
/// The caller must supply exactly `32·d` bytes.
pub(crate) fn byte_decode(bytes: &[u8], d: usize) -> [u64; N] {
    debug_assert!((1..=12).contains(&d));
    assert_eq!(bytes.len(), N * d / 8, "ByteDecode_d input length");
    let mut out = [0u64; N];
    for (i, slot) in out.iter_mut().enumerate() {
        let mut acc = 0u64;
        for j in 0..d {
            let pos = i * d + j;
            acc |= (((bytes[pos / 8] >> (pos % 8)) & 1) as u64) << j;
        }
        *slot = acc;
    }
    out
}

/// FIPS 203 `Compress_d(x) = round(2^d/q · x) mod 2^d` (round-half-up; no
/// ties occur because `q` is odd).
#[inline]
pub(crate) fn compress(x: u64, d: u32) -> u64 {
    debug_assert!((1..=12).contains(&d) && x < Q);
    let two_pow_d = 1u64 << d;
    (((x * two_pow_d) + Q / 2) / Q) % two_pow_d
}

/// FIPS 203 `Decompress_d(y) = round(q/2^d · y)` (round-half-up).
#[inline]
pub(crate) fn decompress(y: u64, d: u32) -> u64 {
    debug_assert!((1..=12).contains(&d) && y < 1 << d);
    let two_pow_d = 1u64 << d;
    (2 * y * Q + two_pow_d) / (2 * two_pow_d)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn byte_encode_decode_roundtrip() {
        for d in 1..=12u32 {
            let mut f = [0u64; N];
            let mut state = 0x1234_5678u64;
            for slot in f.iter_mut() {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                *slot = state % (1 << d);
            }
            let bytes = byte_encode(&f, d as usize);
            assert_eq!(bytes.len(), 32 * d as usize);
            assert_eq!(byte_decode(&bytes, d as usize), f);
        }
    }

    #[test]
    fn compress_decompress_roundtrip() {
        // ‖Decompress_d(Compress_d(x)) − x‖ in the centered-mod-q sense is
        // at most ~q/2^{d+1} for every x.
        for d in 1..=12u32 {
            let step = (Q / 97).max(1);
            let mut x = 0u64;
            while x < Q {
                let back = decompress(compress(x, d), d) % Q;
                let raw = back.abs_diff(x);
                let err = raw.min(Q - raw);
                assert!(
                    err <= (Q + (1 << d)) / (2 << d) + 1,
                    "d={d} x={x} err={err}"
                );
                x += step;
            }
        }
    }

    #[test]
    fn compress_range_and_known_values() {
        // Compress lands in [0, 2^d); x = 0 compresses to 0. For x = q−1 the
        // rounded value 2^d wraps to 0 whenever 2^d/q < ½ (d ≤ 10), while
        // d ∈ {11, 12} keeps the top bucket.
        for d in 1..=12u32 {
            assert_eq!(compress(0, d), 0);
        }
        for d in 1..=10u32 {
            assert_eq!(compress(Q - 1, d), 0);
        }
        assert_eq!(compress(Q - 1, 11), 2047);
        assert_eq!(compress(Q - 1, 12), 4095);
        // Decompress_1(1) = round(q/2) = 1665 (half rounds up).
        assert_eq!(decompress(1, 1), 1665);
        assert_eq!(decompress(0, 1), 0);
    }
}
