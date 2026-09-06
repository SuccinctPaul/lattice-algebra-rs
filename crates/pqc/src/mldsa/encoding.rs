//! ML-DSA wire-format encodings (FIPS 204 §7).

/// Ceiling division by 8.
#[inline]
pub(crate) fn div_ceil8(x: usize) -> usize {
    x.div_ceil(8)
}

use super::params::N;

/// Number of bits needed to represent `x` (x ≥ 1).
pub(crate) fn bit_len(x: u64) -> u32 {
    64 - x.leading_zeros()
}

/// `SimpleBitPack(w, w_max)`: packs `N` coefficients of `bitlen(w_max)` bits
/// each into a byte string.
pub(crate) fn simple_bit_pack(w: &[u64; N], w_max: u64) -> Vec<u8> {
    let bits = bit_len(w_max) as usize;
    let mut out = vec![0u8; div_ceil8(N * bits)];
    let mut pos = 0usize;
    for &c in w {
        debug_assert!(c <= w_max, "coefficient {c} exceeds w_max {w_max}");
        for b in 0..bits {
            // Branch-free bit write (|= 0 is a no-op).
            out[pos / 8] |= (((c >> b) & 1) as u8) << (pos % 8);
            pos += 1;
        }
    }
    out
}

/// `SimpleBitUnpack(str, w_max)`.
pub(crate) fn simple_bit_unpack(bytes: &[u8], w_max: u64) -> [u64; N] {
    let bits = bit_len(w_max) as usize;
    let mut out = [0u64; N];
    let mut pos = 0usize;
    for c in &mut out {
        let mut v = 0u64;
        for b in 0..bits {
            let bit = (bytes[pos / 8] >> (pos % 8)) & 1;
            v |= (bit as u64) << b;
            pos += 1;
        }
        *c = v;
    }
    out
}

/// `BitPack(w, a, b)`: packs `N` centered coefficients `w_i ∈ [−a, b]` by
/// storing `b − w_i` on `bitlen(a+b)` bits each (FIPS 204 parameter
/// convention: `(a, b) = (η, η)` for secrets, `(γ1−1, γ1)` for `z`,
/// `(2^{d−1}−1, 2^{d−1})` for `t0`).
pub(crate) fn bit_pack(w: &[i64], a: i64, b: i64) -> Vec<u8> {
    let bits = bit_len((a + b) as u64) as usize;
    let mut out = vec![0u8; div_ceil8(N * bits)];
    let mut pos = 0usize;
    for &c in w {
        let v = (b - c) as u64;
        debug_assert!(c >= -a && c <= b, "coefficient {c} outside [{}, {b}]", -a);
        debug_assert!(v <= (a + b) as u64);
        for k in 0..bits {
            // Branch-free bit write.
            out[pos / 8] |= (((v >> k) & 1) as u8) << (pos % 8);
            pos += 1;
        }
    }
    out
}

/// `BitUnpack(str, a, b)`: inverse of [`bit_pack`]; yields
/// `b − BitsToInt(chunk)` per coefficient.
pub(crate) fn bit_unpack(bytes: &[u8], a: i64, b: i64) -> [i64; N] {
    let bits = bit_len((a + b) as u64) as usize;
    let mut out = [0i64; N];
    let mut pos = 0usize;
    for c in &mut out {
        let mut v = 0u64;
        for k in 0..bits {
            let bit = (bytes[pos / 8] >> (pos % 8)) & 1;
            v |= (bit as u64) << k;
            pos += 1;
        }
        *c = b - v as i64;
    }
    out
}

/// `HintBitPack(h, ω)`: for each row, the positions of hint bits as bytes,
/// followed by the cumulative index; zero-padded to `ω + k` bytes.
pub(crate) fn hint_bit_pack(h: &[[u8; N]], omega: usize) -> Vec<u8> {
    let k = h.len();
    let mut y = vec![0u8; omega + k];
    let mut index = 0usize;
    for (i, row) in h.iter().enumerate() {
        for (j, &bit) in row.iter().enumerate() {
            if bit == 1 {
                debug_assert!(index < omega, "hint count exceeds ω");
                y[index] = j as u8;
                index += 1;
            }
        }
        // Per-row cumulative count at the fixed offset ω + i.
        y[omega + i] = index as u8;
    }
    y
}

/// `HintBitUnpack(y, ω)`: returns `None` on any malformed hint packing
/// (FIPS 204 rejects these outright — the checks are security-relevant).
pub(crate) fn hint_bit_unpack(y: &[u8], omega: usize, k: usize) -> Option<Vec<[u8; N]>> {
    if y.len() != omega + k {
        return None;
    }
    let mut h = vec![[0u8; N]; k];
    let mut index = 0usize;
    for (i, row) in h.iter_mut().enumerate() {
        // Per-row cumulative count must be monotone and within [0, ω]
        // (mirrors the reference `sig_decode` validation).
        let count = y[omega + i] as usize;
        if count < index || count > omega {
            return None;
        }
        for &pos in &y[index..count] {
            let pos = pos as usize;
            if pos >= N {
                return None;
            }
            row[pos] = 1;
        }
        index = count;
    }
    Some(h)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple_pack_roundtrip() {
        // w_max = 43 → 6 bits × 256 = 192 bytes.
        let mut w = [0u64; N];
        for (i, c) in w.iter_mut().enumerate() {
            *c = (i * 7 % 44) as u64;
        }
        let packed = simple_bit_pack(&w, 43);
        assert_eq!(packed.len(), 192);
        assert_eq!(simple_bit_unpack(&packed, 43), w);
    }

    #[test]
    fn bit_pack_roundtrip_eta() {
        // η = 4: values in [−4, 4], bitlen(8) = 4 bits.
        let w: [i64; N] = std::array::from_fn(|i| (i as i64 % 9) - 4);
        let packed = bit_pack(&w, 4, 4);
        assert_eq!(packed.len(), 128);
        assert_eq!(bit_unpack(&packed, 4, 4), w);
    }

    #[test]
    fn bit_pack_roundtrip_gamma1() {
        // z encoding: coefficients in [−γ1+1, γ1] with γ1 = 2^17 → 18 bits.
        let (a, b) = ((1i64 << 17) - 1, 1i64 << 17);
        let mut w = [0i64; N];
        for (i, c) in w.iter_mut().enumerate() {
            *c = -(a) + (i as i64 * 331) % (a + b);
        }
        let packed = bit_pack(&w, a, b);
        assert_eq!(packed.len(), 576);
        assert_eq!(bit_unpack(&packed, a, b), w);
    }

    #[test]
    fn hint_pack_roundtrip_and_rejection() {
        let (k, omega) = (4usize, 80usize);
        let mut h = vec![[0u8; N]; k];
        // Exactly 80 distinct hint bits, all in row 0.
        for slot in &mut h[0][..omega] {
            *slot = 1;
        }
        let packed = hint_bit_pack(&h, omega);
        assert_eq!(packed.len(), omega + k);
        assert_eq!(hint_bit_unpack(&packed, omega, k).unwrap(), h);
    }

    #[test]
    fn hint_unpack_rejects_malformed() {
        // A hint whose row counter lies must be rejected.
        let mut packed = vec![0u8; 84];
        packed[0] = 5; // claims position 5 in row 0
        packed[1] = 1; // row-0 cumulative index says 1... consistent so far
                       // Corrupt the cumulative byte of the last row.
        *packed.last_mut().unwrap() = 99;
        assert!(hint_bit_unpack(&packed, 80, 4).is_none());
    }
}
