//! The FIPS 203 transform on 8×32-bit lanes (`simd-mlkem` feature).
//!
//! Everything lane-specific about ML-KEM's NTT lives here, isolated from the
//! scalar reference transform in [`super::ntt`]: the Montgomery constants,
//! the Montgomery-form twiddle table and the two lane transforms. Scheme
//! code carries no lane code unless the feature is on.
//!
//! The multiply-reduce runs as an in-lane Montgomery reduction with
//! `R = 2^16` on Montgomery-form twiddles (exact: all intermediates stay
//! below 2^29); the pair updates reuse the
//! [`algebra::simd`](algebra::simd) modular slice kernels, so every
//! representative is back below `q` after each layer and the results are
//! bit-identical to the scalar transforms (asserted by the drift test in
//! [`super::ntt`] and the ACVP KATs). Layers with block length ≥ 8
//! vectorize; the innermost layers stay scalar.

use super::ntt::{mul_mod, HALF_N_INV, Q_U64, ZETAS};
use super::params::{N, Q};
use algebra::simd::{mod_add_assign_u32, mod_sub_u32};
use wide::u32x8;

/// `q^{-1} mod 2^16` by Newton iteration (const-evaluable; `q` is odd).
const fn inv_mod_2_16() -> u64 {
    let mut x: u64 = 1; // exact inverse mod 2
    let mut round = 0;
    while round < 5 {
        // Precision doubles each round: 2 → 4 → 8 → 16 → 32 ≥ 16.
        x = x.wrapping_mul(2u64.wrapping_sub(Q_U64.wrapping_mul(x)));
        round += 1;
    }
    x & 0xFFFF
}

/// `−q^{−1} mod 2^16` — the Montgomery reduction constant for `R = 2^16`.
pub(super) const QINV16: u64 = (1u64 << 16) - inv_mod_2_16();

/// Montgomery-form twiddles: `ZETAS_MONT[i] = ZETAS[i]·2^16 mod q`. A lane
/// butterfly computes `mont_mul(a_hi, ZETAS_MONT[i]) = ζ·a_hi mod q`, so the
/// `2^{-16}` factor of the in-lane Montgomery reduction cancels exactly.
const ZETAS_MONT: [u64; 128] = {
    let mut table = [0u64; 128];
    let mut i = 0;
    while i < 128 {
        table[i] = (ZETAS[i] << 16) % Q_U64;
        i += 1;
    }
    table
};

/// FIPS 203 NTT (forward) on lanes: coefficients in `[0, q)` →
/// evaluation-domain values `f̂[i] = f(ζ^(2·brv8(i)+1))`, exactly the
/// reference layout.
pub(super) fn ntt_lane(a: &mut [u64; N]) {
    const Q32: u32 = Q as u32;
    const LANES: usize = 8;

    debug_assert!(a.iter().all(|&v| v < Q_U64));
    let mut v = [0u32; N];
    for (dst, &src) in v.iter_mut().zip(a.iter()) {
        *dst = src as u32;
    }

    let qv = u32x8::new([Q32; LANES]);
    let qinv_v = u32x8::new([QINV16 as u32; LANES]);
    let mut scratch = [0u32; N / 2];
    let mut i = 1usize;
    let mut len = N / 2;
    while len >= 2 {
        let mut start = 0;
        while start < N {
            let zeta = ZETAS[i];
            i += 1;
            if len >= LANES {
                let (lo, hi) = v[start..start + 2 * len].split_at_mut(len);
                let zv = u32x8::new([ZETAS_MONT[i - 1] as u32; LANES]);
                let t = &mut scratch[..len];
                // `t[j] = ζ·a[j+len] mod q`: in-lane Montgomery reduction.
                // `len` is a multiple of 8 for every vectorized layer, so no
                // scalar tail is needed here.
                for (tc, hc) in t.chunks_exact_mut(LANES).zip(hi.chunks_exact(LANES)) {
                    let prod = u32x8::new(hc.try_into().unwrap()) * zv;
                    let m = (prod * qinv_v) & u32x8::new([0xFFFF; LANES]);
                    let r = (prod + m * qv) >> 16u32;
                    let reduced = (r.cmp_lt(qv)).blend(r, r - qv);
                    tc.copy_from_slice(&reduced.to_array());
                }
                // Butterfly: a[j+len] ← a[j] − t first (it still reads the
                // old low half), then a[j] ← a[j] + t in place.
                mod_sub_u32(hi, lo, t, Q32);
                mod_add_assign_u32(lo, t, Q32);
            } else {
                for j in start..start + len {
                    let t = mul_mod(zeta, v[j + len] as u64) as u32;
                    let x = v[j];
                    v[j + len] = if x >= t { x - t } else { x + Q32 - t };
                    let sum = x + t;
                    v[j] = if sum >= Q32 { sum - Q32 } else { sum };
                }
            }
            start += 2 * len;
        }
        len >>= 1;
    }

    for (dst, &src) in a.iter_mut().zip(v.iter()) {
        *dst = src as u64;
    }
}

/// FIPS 203 inverse NTT (Algorithm 10) on lanes: same descending plain
/// `Zetas` traversal as the scalar transform, finally scaled by `128⁻¹`.
pub(super) fn intt_lane(a: &mut [u64; N]) {
    const Q32: u32 = Q as u32;
    const LANES: usize = 8;

    debug_assert!(a.iter().all(|&v| v < Q_U64));
    let mut v = [0u32; N];
    for (dst, &src) in v.iter_mut().zip(a.iter()) {
        *dst = src as u32;
    }

    let qv = u32x8::new([Q32; LANES]);
    let qinv_v = u32x8::new([QINV16 as u32; LANES]);
    let mut scratch = [0u32; N / 2];
    let mut i = 127usize;
    let mut len = 2;
    while len <= N / 2 {
        let mut start = 0;
        while start < N {
            let zeta = ZETAS[i];
            i -= 1;
            if len >= LANES {
                let (lo, hi) = v[start..start + 2 * len].split_at_mut(len);
                let zv = u32x8::new([ZETAS_MONT[i + 1] as u32; LANES]);
                let du = &mut scratch[..len];
                // `du = a[j+len] − a[j] (mod q)` — hi MINUS lo, before
                // either slot moves (see the scalar-path comment).
                mod_sub_u32(du, hi, lo, Q32);
                for dc in du.chunks_exact_mut(LANES) {
                    let prod = u32x8::new(dc.try_into().unwrap()) * zv;
                    let m = (prod * qinv_v) & u32x8::new([0xFFFF; LANES]);
                    let r = (prod + m * qv) >> 16u32;
                    let reduced = (r.cmp_lt(qv)).blend(r, r - qv);
                    dc.copy_from_slice(&reduced.to_array());
                }
                mod_add_assign_u32(lo, hi, Q32);
                hi.copy_from_slice(du);
            } else {
                for j in start..start + len {
                    let t = v[j];
                    let u = v[j + len];
                    let sum = t + u;
                    v[j] = if sum >= Q32 { sum - Q32 } else { sum };
                    let du = if u >= t { u - t } else { u + Q32 - t };
                    v[j + len] = mul_mod(du as u64, zeta) as u32;
                }
            }
            start += 2 * len;
        }
        len <<= 1;
    }
    // Seven layers ⇒ scale by 128⁻¹ (see the scalar path).
    for c in v.iter_mut() {
        *c = mul_mod(*c as u64, HALF_N_INV) as u32;
    }

    for (dst, &src) in a.iter_mut().zip(v.iter()) {
        *dst = src as u64;
    }
}
