//! Port of the Falcon reference `codec.c`: key and signature encodings.
//!
//! Conventions shared by all functions: values are packed most-significant
//! chunk first (big-endian bit order) into the output stream, trailing
//! padding bits must be zero, and any violation (value out of range,
//! buffer too small, forbidden pattern, non-zero padding) is reported by
//! returning 0 — encode functions return the byte count written, decode
//! functions the number of bytes consumed.
//!
//! - `modq_*`: fixed-length encoding, 14 bits per coefficient (< q).
//! - `trim_i8_*`: fixed-length `bits`-bit two's-complement chunks; the
//!   all-ones value −2^(bits−1) is forbidden so the encoding is injective.
//! - `comp_*`: variable-length signature coefficients (see
//!   [`comp_encode`]).
#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

/// Reference `modq_encode`: n 14-bit values packed most-significant chunk
/// first (big-endian bit order), zero-padded to a byte boundary.
pub fn modq_encode(out: &mut [u8], x: &[u16]) -> usize {
    let n = x.len();
    for &v in x {
        if v as u32 >= 12289 {
            return 0;
        }
    }
    let out_len = (n * 14 + 7) >> 3;
    if out_len > out.len() {
        return 0;
    }
    let mut acc: u32 = 0;
    let mut acc_len: i32 = 0;
    let mut u = 0usize;
    for &v in x {
        acc = (acc << 14) | v as u32;
        acc_len += 14;
        while acc_len >= 8 {
            acc_len -= 8;
            out[u] = (acc >> acc_len) as u8;
            u += 1;
        }
    }
    if acc_len > 0 {
        out[u] = (acc << (8 - acc_len)) as u8;
    }
    out_len
}

/// Reference `modq_decode`. Returns the number of input bytes consumed.
pub fn modq_decode(x: &mut [u16], input: &[u8]) -> usize {
    let n = x.len();
    let in_len = (n * 14 + 7) >> 3;
    if in_len > input.len() {
        return 0;
    }
    let mut acc: u32 = 0;
    let mut acc_len: i32 = 0;
    let mut u = 0usize;
    for b in input.iter().take(in_len) {
        acc = (acc << 8) | *b as u32;
        acc_len += 8;
        while acc_len >= 14 && u < n {
            acc_len -= 14;
            let w = (acc >> acc_len) & 0x3FFF;
            if w >= 12289 {
                return 0;
            }
            x[u] = w as u16;
            u += 1;
        }
    }
    if (acc & ((1u32 << acc_len) - 1)) != 0 {
        return 0;
    }
    in_len
}

/// Reference `trim_i8_encode`: n signed values as fixed `bits`-bit
/// two's-complement chunks (bit width from `MAX_FG_BITS`); values beyond
/// ±(2^(bits−1) − 1) are rejected so the −2^(bits−1) pattern stays unused.
pub fn trim_i8_encode(out: &mut [u8], x: &[i8], bits: u32) -> usize {
    let n = x.len();
    let maxv = (1i32 << (bits - 1)) - 1;
    let minv = -maxv;
    for &v in x {
        if (v as i32) < minv || (v as i32) > maxv {
            return 0;
        }
    }
    let out_len = (n * bits as usize + 7) >> 3;
    if out_len > out.len() {
        return 0;
    }
    let mut acc: u32 = 0;
    let mut acc_len: u32 = 0;
    let mask = (1u32 << bits) - 1;
    let mut u = 0usize;
    for &v in x {
        acc = (acc << bits) | ((v as u8 as u32) & mask);
        acc_len += bits;
        while acc_len >= 8 {
            acc_len -= 8;
            out[u] = (acc >> acc_len) as u8;
            u += 1;
        }
    }
    if acc_len > 0 {
        out[u] = (acc << (8 - acc_len)) as u8;
    }
    out_len
}

/// Reference `trim_i8_decode`. Returns the number of input bytes consumed.
pub fn trim_i8_decode(x: &mut [i8], bits: u32, input: &[u8]) -> usize {
    let n = x.len();
    let in_len = (n * bits as usize + 7) >> 3;
    if in_len > input.len() {
        return 0;
    }
    let mut u = 0usize;
    let mut acc: u32 = 0;
    let mut acc_len: u32 = 0;
    let mask1 = (1u32 << bits) - 1;
    let mask2 = 1u32 << (bits - 1);
    let mut buf = 0usize;
    while u < n {
        acc = (acc << 8) | input[buf] as u32;
        buf += 1;
        acc_len += 8;
        while acc_len >= bits && u < n {
            acc_len -= bits;
            let mut w = (acc >> acc_len) & mask1;
            w |= (w & mask2).wrapping_neg();
            if w == mask2.wrapping_neg() {
                // The -2^(bits-1) value is forbidden.
                return 0;
            }
            x[u] = w as i8;
            u += 1;
        }
    }
    if (acc & ((1u32 << acc_len) - 1)) != 0 {
        return 0;
    }
    in_len
}

/// Reference `comp_encode`: variable-length signature coefficient encoding
/// (the spec's compressed-signature format). Coefficients must lie in
/// [−2047, 2047]; each is emitted as: 1 sign bit, the low 7 bits of |v|,
/// then w = |v| >> 7 zero bits terminated by a single one — a unary
/// length prefix, 9 + w bits per coefficient.
pub fn comp_encode(out: &mut [u8], x: &[i16]) -> usize {
    let _n = x.len();
    for &v in x {
        if !(-2047..=2047).contains(&v) {
            return 0;
        }
    }
    let mut acc: u32 = 0;
    let mut acc_len: u32 = 0;
    let mut v = 0usize;
    for &val in x {
        // Sign bit first.
        acc <<= 1;
        let mut t = val as i32;
        if t < 0 {
            t = -t;
            acc |= 1;
        }
        let mut w = t as u32;

        // Low 7 bits of the absolute value.
        acc <<= 7;
        acc |= w & 127;
        w >>= 7;
        acc_len += 8;

        // As many zeros as necessary, then a one.
        acc <<= w + 1;
        acc |= 1;
        acc_len += w + 1;

        while acc_len >= 8 {
            acc_len -= 8;
            if v >= out.len() {
                return 0;
            }
            out[v] = (acc >> acc_len) as u8;
            v += 1;
        }
    }
    if acc_len > 0 {
        if v >= out.len() {
            return 0;
        }
        out[v] = (acc << (8 - acc_len)) as u8;
        v += 1;
    }
    v
}

/// Reference `comp_decode`: inverse of [`comp_encode`]; additionally
/// rejects a negative zero ("-0"), any implied magnitude above 2047, and
/// non-zero trailing padding. Returns the number of input bytes consumed.
pub fn comp_decode(x: &mut [i16], input: &[u8]) -> usize {
    let n = x.len();
    let mut acc: u32 = 0;
    let mut acc_len: u32 = 0;
    let mut v = 0usize;
    for slot in x.iter_mut().take(n) {
        if v >= input.len() {
            return 0;
        }
        acc = (acc << 8) | input[v] as u32;
        v += 1;
        let b = acc >> acc_len;
        let s = b & 128;
        let mut m = b & 127;

        loop {
            if acc_len == 0 {
                if v >= input.len() {
                    return 0;
                }
                acc = (acc << 8) | input[v] as u32;
                v += 1;
                acc_len = 8;
            }
            acc_len -= 1;
            if ((acc >> acc_len) & 1) != 0 {
                break;
            }
            m += 128;
            if m > 2047 {
                return 0;
            }
        }

        // "-0" is forbidden.
        if s != 0 && m == 0 {
            return 0;
        }
        *slot = if s != 0 { -(m as i16) } else { m as i16 };
    }
    if (acc & ((1u32 << acc_len) - 1)) != 0 {
        return 0;
    }
    v
}

/// Reference `max_fg_bits[]`.
pub const MAX_FG_BITS: [u8; 11] = [0, 8, 8, 8, 8, 8, 7, 7, 6, 6, 5];

/// Reference `max_FG_bits[]` for F, G (always 8 bits).
pub const MAX_BIG_FG_BITS: [u8; 11] = [0, 8, 8, 8, 8, 8, 8, 8, 8, 8, 8];

/// Reference `max_sig_bits[]`.
#[allow(dead_code)]
pub const MAX_SIG_BITS: [u8; 11] = [0, 10, 11, 11, 12, 12, 12, 12, 12, 12, 12];
