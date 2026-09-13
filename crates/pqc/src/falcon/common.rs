//! Port of the Falcon reference `common.c` (hash-to-point, norm tests)
//! plus the `inner_shake256_context` wrapper (reference `shake.c`, backed
//! by the `sha3` crate).
#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::Shake256;

/// Reference `inner_shake256_context`: absorb with [`Self::inject`], switch
/// to squeezing with [`Self::flip`], draw with [`Self::extract`].
pub struct InnerShake256 {
    reader: sha3::Shake256Reader,
}

impl InnerShake256 {
    /// Reference `i_shake256_init` + one or more `i_shake256_inject` calls.
    pub fn inject_all(parts: &[&[u8]]) -> Self {
        let mut hasher = Shake256::default();
        for part in parts {
            hasher.update(part);
        }
        Self {
            reader: hasher.finalize_xof(),
        }
    }

    /// Reference `i_shake256_extract`.
    pub fn extract(&mut self, out: &mut [u8]) {
        self.reader.read(out);
    }
}

/// Reference `hash_to_point_vartime`: squeeze 16-bit samples, reject values
/// ≥ 61445 (= 5·12289), reduce the rest mod 12289. The rejection keeps the
/// result uniform: the accepted range [0, 5q) is exactly five periods of q.
pub fn hash_to_point_vartime(sc: &mut InnerShake256, x: &mut [u16]) {
    let mut n = x.len();
    let mut u = 0usize;
    while n > 0 {
        let mut buf = [0u8; 2];
        sc.extract(&mut buf);
        let mut w = ((buf[0] as u32) << 8) | buf[1] as u32;
        if w < 61445 {
            while w >= 12289 {
                w -= 12289;
            }
            x[u] = w as u16;
            u += 1;
            n -= 1;
        }
    }
}

/// Acceptance bounds for the squared l2-norm, indexed by logn (inclusive
/// bounds, floor(beta^2)). Only logn = 9 (Falcon-512) and logn = 10
/// (Falcon-1024) are used by the public API.
const L2BOUND: [u32; 11] = [
    0, 101498, 208714, 428865, 892039, 1852696, 3842630, 7959734, 16468416, 34034726, 70265242,
];

/// Reference `is_short`: accept iff ‖(s1,s2)‖² ≤ bound.
pub fn is_short(s1: &[i16], s2: &[i16], logn: u32) -> bool {
    let n = 1usize << logn;
    // `ng` accumulates the sign bit of the running sum so that a u32
    // wraparound in the squared-norm accumulation turns into a huge final
    // value (hence a rejection) rather than a small one.
    let mut s: u32 = 0;
    let mut ng: u32 = 0;
    for u in 0..n {
        let z1 = s1[u] as i32;
        s = s.wrapping_add((z1 * z1) as u32);
        ng |= s;
        let z2 = s2[u] as i32;
        s = s.wrapping_add((z2 * z2) as u32);
        ng |= s;
    }
    s |= (ng >> 31).wrapping_neg();
    s <= L2BOUND[logn as usize]
}

/// Reference `is_short_half`: accept iff sqn + ‖s2‖² ≤ bound.
pub fn is_short_half(sqn: u32, s2: &[i16], logn: u32) -> bool {
    let n = 1usize << logn;
    // Same overflow-to-reject trick as `is_short`: if the incoming sqn or
    // the running sum overflows u32, `ng` forces a huge final value.
    let mut sqn = sqn;
    let ng = (sqn >> 31).wrapping_neg();
    for &z in s2.iter().take(n) {
        let zi = z as i32;
        sqn = sqn.wrapping_add((zi * zi) as u32);
    }
    let s = sqn | ng;
    s <= L2BOUND[logn as usize]
}
