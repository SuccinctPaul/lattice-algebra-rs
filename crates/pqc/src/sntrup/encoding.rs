//! Encoding for Streamlined NTRU Prime: the mixed-radix `Encode`/`Decode`
//! compressor (ports of `Encode.c`/`Decode.c`), the branchless
//! `crypto_sort_uint32` used by `Short_fromlist`, and the small-polynomial
//! packing.

use super::params::SntrupParams;
use super::poly::{self, mod_uint14, q12, Fq, Small};

// ===========================================================================
// crypto_sort_uint32 (uint32.c)
// ===========================================================================

/// `uint32_MINMAX`: branchless min-max, returns `(min, max)`.
#[inline]
fn minmax_u32_pair(xi: u32, yi: u32) -> (u32, u32) {
    let xy = xi ^ yi;
    let mut c = yi.wrapping_sub(xi);
    c ^= xy & (c ^ yi ^ 0x8000_0000);
    c >>= 31;
    c = c.wrapping_neg();
    c &= xy;
    (xi ^ c, yi ^ c)
}

/// `crypto_sort_uint32`: the supercop branchless unsigned sort.
pub fn crypto_sort_uint32(x: &mut [u32]) {
    let n = x.len();
    if n < 2 {
        return;
    }
    let mut top: usize = 1;
    while top < n - top {
        top += top;
    }
    let mut p = top;
    while p > 0 {
        for i in 0..n - p {
            if i & p == 0 {
                let (a, b) = minmax_u32_pair(x[i], x[i + p]);
                x[i] = a;
                x[i + p] = b;
            }
        }
        let mut q = top;
        while q > p {
            for i in 0..n - q {
                if i & p == 0 {
                    let (a, b) = minmax_u32_pair(x[i + p], x[i + q]);
                    x[i + p] = a;
                    x[i + q] = b;
                }
            }
            q >>= 1;
        }
        p >>= 1;
    }
}

// ===========================================================================
// Short_fromlist
// ===========================================================================

/// `Short_fromlist`: build a weight-`w` ternary polynomial from `p` random
/// 32-bit words: the first `w` words are forced even, the rest are forced
/// ≡ 1 (mod 2), the whole list is sorted, and the low 2 bits map
/// {0,1,2,3} → {−1,0,1,0}—weighted by which slots survived the sort.
pub fn short_fromlist<P: SntrupParams>(input: &[u32]) -> Vec<Small> {
    let p = P::P;
    let w = P::W;
    let mut l = vec![0u32; p];
    for (i, slot) in l.iter_mut().enumerate() {
        *slot = if i < w {
            input[i] & (u32::MAX - 1) // force even
        } else {
            (input[i] & (u32::MAX - 2)) | 1 // force odd
        };
    }
    crypto_sort_uint32(&mut l);
    l.iter().map(|&v| ((v & 3) as i8) - 1).collect()
}

// ===========================================================================
// Mixed-radix Encode / Decode
// ===========================================================================

/// `Encode`: compress `len` digits, digit `i` in `[0, M[i])`, into the
/// minimal little-endian byte string implied by pairwise radix products.
pub fn encode(out: &mut Vec<u8>, r: &[u16], m: &[u16]) {
    let len = m.len();
    debug_assert_eq!(r.len(), len);
    if len == 1 {
        let mut rr = r[0] as u32;
        let mut mm = m[0] as u32;
        while mm > 1 {
            out.push((rr & 0xff) as u8);
            rr >>= 8;
            mm = (mm + 255) >> 8;
        }
        return;
    }
    let len2 = len.div_ceil(2);
    let mut r2 = vec![0u16; len2];
    let mut m2 = vec![0u16; len2];
    let mut i = 0usize;
    while i < len - 1 {
        let m0 = m[i] as u32;
        let mut rr = r[i] as u32 + r[i + 1] as u32 * m0;
        let mut mm = m[i + 1] as u32 * m0;
        while mm >= 16384 {
            out.push((rr & 0xff) as u8);
            rr >>= 8;
            mm = (mm + 255) >> 8;
        }
        r2[i / 2] = rr as u16;
        m2[i / 2] = mm as u16;
        i += 2;
    }
    if i < len {
        r2[i / 2] = r[i];
        m2[i / 2] = m[i];
    }
    encode(out, &r2, &m2);
}

/// `Decode`: inverse of [`encode`].
pub fn decode(out: &mut Vec<u16>, s: &[u8], m: &[u16]) {
    let len = m.len();
    if len == 1 {
        let v = if m[0] == 1 {
            0
        } else if m[0] <= 256 {
            mod_uint14(s[0] as u32, m[0] as u32)
        } else {
            mod_uint14(s[0] as u32 + ((s[1] as u16 as u32) << 8), m[0] as u32)
        };
        out.push(v);
        return;
    }
    let len2 = len.div_ceil(2);
    let mut r2: Vec<u16> = Vec::with_capacity(len2);
    let mut m2 = vec![0u16; len2];
    let mut bottomr = vec![0u16; len / 2];
    let mut bottomt = vec![1u32; len / 2];

    let mut sp = 0usize;
    let mut i = 0usize;
    while i < len - 1 {
        let mm = m[i] as u32 * m[i + 1] as u32;
        if mm > 256 * 16383 {
            bottomt[i / 2] = 256 * 256;
            bottomr[i / 2] = (s[sp] as u16).wrapping_add(256u16.wrapping_mul(s[sp + 1] as u16));
            sp += 2;
            m2[i / 2] = ((((mm + 255) >> 8) + 255) >> 8) as u16;
        } else if mm >= 16384 {
            bottomt[i / 2] = 256;
            bottomr[i / 2] = s[sp] as u16;
            sp += 1;
            m2[i / 2] = ((mm + 255) >> 8) as u16;
        } else {
            bottomt[i / 2] = 1;
            bottomr[i / 2] = 0;
            m2[i / 2] = mm as u16;
        }
        i += 2;
    }
    if i < len {
        m2[i / 2] = m[i];
    }
    decode(&mut r2, &s[sp..], &m2);

    i = 0;
    let _ = &bottomr;
    let _ = &bottomt;
    while i < len - 1 {
        let mut rr = bottomr[i / 2] as u32;
        rr += bottomt[i / 2] * r2[i / 2] as u32;
        // uint32_divmod_uint14(r1, r0, rr, m[i])
        let r0 = (rr % m[i] as u32) as u16;
        let r1 = rr / m[i] as u32;
        let r1 = mod_uint14(r1, m[i + 1] as u32);
        out.push(r0);
        out.push(r1);
        i += 2;
    }
    if i < len {
        out.push(r2[i / 2]);
    }
}

// ===========================================================================
// Small / Rq / Rounded packing
// ===========================================================================

/// `Small_encode`: pack `p` ternary values, 4 per byte (2 bits each,
/// offset by 1), plus one trailing coefficient (p ≡ 1 mod 4).
pub fn small_encode<P: SntrupParams>(f: &[Small]) -> Vec<u8> {
    let p = P::P;
    let mut out = Vec::with_capacity(P::SMALL_BYTES);
    let mut it = f.iter();
    for _ in 0..p / 4 {
        let mut x = (it.next().unwrap() + 1) as u8;
        x += ((it.next().unwrap() + 1) as u8) << 2;
        x += ((it.next().unwrap() + 1) as u8) << 4;
        x += ((it.next().unwrap() + 1) as u8) << 6;
        out.push(x);
    }
    out.push((it.next().unwrap() + 1) as u8);
    out
}

/// `Small_decode`.
pub fn small_decode<P: SntrupParams>(s: &[u8]) -> Vec<Small> {
    let p = P::P;
    let mut out = Vec::with_capacity(p);
    let mut it = s.iter();
    for _ in 0..p / 4 {
        let mut x = *it.next().unwrap();
        for _ in 0..4 {
            out.push((x & 3) as Small - 1);
            x >>= 2;
        }
    }
    out.push((it.next().unwrap() & 3) as poly::Small - 1);
    out
}

/// `Rq_encode`: encode centered coefficients as `r + ⌈q/2⌉` digits of
/// radix `q`.
pub fn rq_encode<P: SntrupParams>(r: &[Fq]) -> Vec<u8> {
    let p = P::P;
    let rr: Vec<u16> = r.iter().map(|&v| (v + q12::<P>()) as u16).collect();
    let m = vec![P::Q; p];
    let mut out = Vec::with_capacity(P::RQ_BYTES);
    encode(&mut out, &rr, &m);
    out
}

/// `Rq_decode`.
pub fn rq_decode<P: SntrupParams>(s: &[u8]) -> Vec<poly::Fq> {
    let p = P::P;
    let m = vec![P::Q; p];
    let mut rr = Vec::with_capacity(p);
    decode(&mut rr, s, &m);
    rr.into_iter().map(|v| v as poly::Fq - q12::<P>()).collect()
}

/// `Rounded_encode`: map coefficients to `((r+⌈q/2⌉)·10923)>>15` (≈ /3)
/// and encode with radix `(q+2)/3`.
pub fn rounded_encode<P: SntrupParams>(r: &[Fq]) -> Vec<u8> {
    let p = P::P;
    let rr: Vec<u16> = r
        .iter()
        .map(|&v| (((v + q12::<P>()) as i32 * 10923) >> 15) as u16)
        .collect();
    let m = vec![P::Q.div_ceil(3); p];
    let mut out = Vec::with_capacity(P::ROUNDED_BYTES);
    encode(&mut out, &rr, &m);
    out
}

/// `Rounded_decode`.
pub fn rounded_decode<P: SntrupParams>(s: &[u8]) -> Vec<poly::Fq> {
    let p = P::P;
    let m = vec![P::Q.div_ceil(3); p];
    let mut rr = Vec::with_capacity(p);
    decode(&mut rr, s, &m);
    rr.into_iter()
        .map(|v| v as poly::Fq * 3 - q12::<P>())
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sntrup::params::Sntrup761;

    #[test]
    fn encode_decode_roundtrip() {
        // Rq roundtrip: digits of radix q.
        let r: Vec<u16> = (0..761u32).map(|i| ((i * 7919) % 4591) as u16).collect();
        let m = vec![Sntrup761::Q; 761];
        let mut out = Vec::new();
        encode(&mut out, &r, &m);
        assert_eq!(out.len(), Sntrup761::RQ_BYTES);
        let mut back = Vec::new();
        decode(&mut back, &out, &m);
        assert_eq!(back, r);

        // Rounded roundtrip: digits of radix (q+2)/3.
        let base = Sntrup761::Q.div_ceil(3);
        let r: Vec<u16> = (0..761u32)
            .map(|i| ((i * 7919) % base as u32) as u16)
            .collect();
        let m = vec![base; 761];
        let mut out = Vec::new();
        encode(&mut out, &r, &m);
        assert_eq!(out.len(), Sntrup761::ROUNDED_BYTES);
        let mut back = Vec::new();
        decode(&mut back, &out, &m);
        assert_eq!(back, r);
    }

    #[test]
    fn small_roundtrip() {
        let f: Vec<Small> = (0..761).map(|i| ((i % 3) as i8) - 1).collect();
        let enc = small_encode::<Sntrup761>(&f);
        assert_eq!(enc.len(), Sntrup761::SMALL_BYTES);
        assert_eq!(small_decode::<Sntrup761>(&enc), f);
    }

    #[test]
    fn sort_sorts() {
        let mut v: Vec<u32> = (0..761u32).map(|i| i.wrapping_mul(0x9E3779B1)).collect();
        let mut sorted = v.clone();
        sorted.sort_unstable();
        crypto_sort_uint32(&mut v);
        assert_eq!(v, sorted);
    }
}
