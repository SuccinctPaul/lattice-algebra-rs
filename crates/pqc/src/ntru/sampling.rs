//! Secret / randomness sampling for NTRU (ports of `sample_iid.c`,
//! `sample.c` and the `crypto_sort_int32` sorting network used by
//! `sample_fixed_type`).

use super::params::NtruParams;
use super::poly::Poly;

/// `int32_MINMAX`: branchless min-max from the supercop integer-sort
/// reference — returns `(min, max)`.
#[inline]
fn minmax_i32(a: i32, b: i32) -> (i32, i32) {
    let ab = b ^ a;
    let mut c = (b as i64).wrapping_sub(a as i64) as i32;
    c ^= ab & (c ^ b);
    c >>= 31;
    c &= ab;
    (a ^ c, b ^ c)
}

/// `crypto_sort_int32`: the supercop branchless integer sort
/// (`crypto_sort/int32`), verbatim control flow.
fn crypto_sort_int32(x: &mut [i32]) {
    let n = x.len();
    let mut top: usize = 1;
    while top < n - top {
        top += top;
    }

    let mut p = top;
    while p >= 1 {
        let mut i = 0usize;
        while i + 2 * p <= n {
            for j in i..i + p {
                let (a, b) = (x[j], x[j + p]);
                let (a, b) = minmax_i32(a, b);
                x[j] = a;
                x[j + p] = b;
            }
            i += 2 * p;
        }
        let upto = n.wrapping_sub(p);
        for j in i..upto {
            let (a, b) = (x[j], x[j + p]);
            let (a, b) = minmax_i32(a, b);
            x[j] = a;
            x[j + p] = b;
        }

        let (mut i, mut j) = (0usize, 0usize);
        let mut q = top;
        while q > p {
            // One round of the merge; `goto done` skips the tail of this
            // round and continues with q >>= 1.
            let mut goto_done = false;
            if j != i {
                loop {
                    if j == n - q {
                        goto_done = true;
                        break;
                    }
                    let mut a = x[j + p];
                    let mut r = q;
                    while r > p {
                        let b = x[j + r];
                        let (a2, b2) = minmax_i32(a, b);
                        a = a2;
                        x[j + r] = b2;
                        r >>= 1;
                    }
                    x[j + p] = a;
                    j += 1;
                    if j == i + p {
                        i += 2 * p;
                        break;
                    }
                }
            }
            if !goto_done {
                while i + p <= n - q {
                    for j2 in i..i + p {
                        let mut a = x[j2 + p];
                        let mut r = q;
                        while r > p {
                            let b = x[j2 + r];
                            let (a2, b2) = minmax_i32(a, b);
                            a = a2;
                            x[j2 + r] = b2;
                            r >>= 1;
                        }
                        x[j2 + p] = a;
                    }
                    i += 2 * p;
                }
                j = i;
                while j < n - q {
                    let mut a = x[j + p];
                    let mut r = q;
                    while r > p {
                        let b = x[j + r];
                        let (a2, b2) = minmax_i32(a, b);
                        a = a2;
                        x[j + r] = b2;
                        r >>= 1;
                    }
                    x[j + p] = a;
                    j += 1;
                }
            }
            q >>= 1;
        }
        if p == 1 {
            break;
        }
        p >>= 1;
    }
}

/// `sample_iid`: uniform ternary from `n−1` random bytes via the
/// reference's byte-wise mod-3 fold (Pr[0] = 86/256, Pr[±1] = 85/256).
pub fn sample_iid<P: NtruParams>(uniform: &[u8]) -> Poly {
    let n = P::N;
    assert_eq!(uniform.len(), n - 1, "sample_iid input length");
    let mut r = vec![0u16; n];
    for i in 0..n - 1 {
        r[i] = mod3_sample(uniform[i]);
    }
    r
}

fn mod3_sample(b: u8) -> u16 {
    let mut r = b as u16; // the reference folds a u16; input bytes ≡ themselves
    r = (r >> 4) + (r & 0xf);
    r = (r >> 2) + (r & 0x3);
    r = (r >> 2) + (r & 0x3);
    let t = r as i16 - 3;
    let c = t >> 15;
    ((c & r as i16) ^ (!c & t)) as u16
}

/// `sample_fixed_type` (HPS): `r` has exactly `WEIGHT/2` coefficients of
/// 1 and `WEIGHT/2` of 2 (rest 0), derived by sorting 30-bit words carved
/// from `u` with forced low bits. Consumes `ceil(30·(n−1)/8)` bytes.
pub fn sample_fixed_type<P: NtruParams>(u: &[u8]) -> Poly {
    let n = P::N;
    assert!(u.len() >= (30 * (n - 1)).div_ceil(8), "sample_fixed_type input length");
    let mut s = vec![0i32; n - 1];

    let mut i = 0usize;
    while i < (n - 1) / 4 {
        let u15 = |k: usize| u[15 * i + k] as i32 as u32;
        s[4 * i] = ((u15(0) << 2) + (u15(1) << 10) + (u15(2) << 18) + (u15(3) << 26)) as i32;
        s[4 * i + 1] = (((u15(3) & 0xc0) >> 4)
            + (u15(4) << 4)
            + (u15(5) << 12)
            + (u15(6) << 20)
            + (u15(7) << 28)) as i32;
        s[4 * i + 2] = (((u15(7) & 0xf0) >> 2)
            + (u15(8) << 6)
            + (u15(9) << 14)
            + (u15(10) << 22)
            + (u15(11) << 30)) as i32;
        s[4 * i + 3] = ((u15(11) & 0xfc)
            + (u15(12) << 8)
            + (u15(13) << 16)
            + (u15(14) << 24)) as i32;
        i += 1;
    }
    if (n - 1) > ((n - 1) / 4) * 4 {
        // (n−1) ≡ 2 (mod 4)
        let i = (n - 1) / 4;
        let u15 = |k: usize| u[15 * i + k] as i32 as u32;
        s[4 * i] = ((u15(0) << 2) + (u15(1) << 10) + (u15(2) << 18) + (u15(3) << 26)) as i32;
        s[4 * i + 1] = (((u15(3) & 0xc0) >> 4)
            + (u15(4) << 4)
            + (u15(5) << 12)
            + (u15(6) << 20)
            + (u15(7) << 28)) as i32;
    }

    let weight = P::WEIGHT;
    for v in s.iter_mut().take(weight / 2) {
        *v |= 1;
    }
    for v in s.iter_mut().take(weight).skip(weight / 2) {
        *v |= 2;
    }

    crypto_sort_int32(&mut s);

    let mut r = vec![0u16; n];
    for (dst, &src) in r.iter_mut().take(n - 1).zip(s.iter()) {
        *dst = (src & 3) as u16;
    }
    r[n - 1] = 0;
    r
}

/// `sample_iid_plus` (HRSS): sample_iid, then conditionally flip signs of
/// even-index coefficients so that ⟨x·r, r⟩ ≥ 0.
pub fn sample_iid_plus<P: NtruParams>(uniform: &[u8]) -> Poly {
    let n = P::N;
    let mut r = sample_iid::<P>(uniform);

    // Map {0,1,2} → {0,1,2^16−1}.
    for c in r.iter_mut().take(n - 1) {
        let shifted = *c >> 1;
        *c |= shifted.wrapping_neg();
    }

    // s = ⟨x·r, r⟩ (r[n−1] = 0).
    let mut s: u16 = 0;
    for i in 0..n - 1 {
        s = s.wrapping_add(r[i + 1].wrapping_mul(r[i]));
    }

    // Extract the sign of s (sign(0) = 1).
    let sign: u16 = 1 | (s >> 15).wrapping_neg();

    for i in (0..n).step_by(2) {
        r[i] = sign.wrapping_mul(r[i]);
    }

    // Map {0,1,2^16−1} → {0,1,2}.
    for c in r.iter_mut() {
        *c = 3 & (*c ^ (*c >> 15));
    }
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ntru::params::NtruHps2048677;

    #[test]
    fn sort_sorts() {
        let mut v: Vec<i32> = (0..677i32).map(|i| (i * 7919 % 677) - 300).collect();
        let mut sorted = v.clone();
        sorted.sort_unstable();
        crypto_sort_int32(&mut v);
        assert_eq!(v, sorted);
    }

    #[test]
    fn fixed_type_weight() {
        let u: Vec<u8> = (0..(30 * 676_usize).div_ceil(8)).map(|i| (i * 37 + 11) as u8).collect();
        let g = sample_fixed_type::<NtruHps2048677>(&u);
        let ones = g.iter().filter(|&&c| c == 1).count();
        let twos = g.iter().filter(|&&c| c == 2).count();
        assert_eq!(ones, NtruHps2048677::WEIGHT / 2);
        assert_eq!(twos, NtruHps2048677::WEIGHT / 2);
        assert_eq!(g[676], 0);
    }
}
