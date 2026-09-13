//! Port of the Falcon reference `keygen.c`: Gaussian polynomial generation,
//! the exact NTRU equation solver (RNS + 31-bit-word bignum + Babai
//! reduction) and the top-level keygen loop.

#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

use super::fpr::*;
use super::tables::PRIMES;

/// Reference `MAX_BL_SMALL[]`: limb counts (31-bit words) per coefficient
/// of the "small" polynomials (f, g and the level-wise halves) at each RNS
/// depth.
const MAX_BL_SMALL: [usize; 11] = [1, 1, 2, 2, 4, 7, 14, 27, 53, 106, 209];

/// Reference `MAX_BL_LARGE[]`: limb counts for the "large" (full-width)
/// lifted F/G coefficients at each depth.
const MAX_BL_LARGE: [usize; 10] = [2, 2, 5, 7, 12, 21, 40, 78, 157, 308];

/// Reference `BITLENGTH[]`: expected bit length (avg, std) of the
/// intermediate f/g values per depth; drives the Babai-reduction scaling.
const BITLENGTH: [(i32, i32); 11] = [
    (4, 0),
    (11, 1),
    (24, 1),
    (50, 1),
    (102, 1),
    (202, 2),
    (401, 4),
    (794, 5),
    (1577, 8),
    (3138, 13),
    (6308, 25),
];

/// Deepest depth at which the k·(f, g) subtraction is still done through
/// the NTT-based path (`poly_sub_scaled_ntt`); deeper levels use the plain
/// bignum path (`poly_sub_scaled`).
const DEPTH_INT_FG: u32 = 4;

// ====================================================================
// Modular arithmetic modulo a small prime p (2^30 < p < 2^31).
// ====================================================================

/// Map a small signed integer into [0, p).
#[inline]
fn modp_set(x: i32, p: u32) -> u32 {
    let mut w = x as u32;
    w = w.wrapping_add(p & (w >> 31).wrapping_neg());
    w
}

/// Normalize a modular integer around 0.
#[inline]
fn modp_norm(x: u32, p: u32) -> i32 {
    x.wrapping_sub(p & ((((p + 1) >> 1).wrapping_sub(x) >> 31).wrapping_neg())) as i32
}

/// −1/p mod 2^31.
fn modp_ninv31(p: u32) -> u32 {
    let mut y = 2u32.wrapping_sub(p);
    for _ in 0..4 {
        y = y.wrapping_mul(2u32.wrapping_sub(p.wrapping_mul(y)));
    }
    0x7FFF_FFFF & y.wrapping_neg()
}

/// R = 2^31 mod p.
#[inline]
fn modp_r(p: u32) -> u32 {
    (1u32 << 31).wrapping_sub(p)
}

/// Modular addition (operands and result in [0, p)).
#[inline]
fn modp_add(a: u32, b: u32, p: u32) -> u32 {
    let d = a.wrapping_add(b).wrapping_sub(p);
    d.wrapping_add(p & (d >> 31).wrapping_neg())
}

/// Modular subtraction (operands and result in [0, p)).
#[inline]
fn modp_sub(a: u32, b: u32, p: u32) -> u32 {
    let d = a.wrapping_sub(b);
    d.wrapping_add(p & (d >> 31).wrapping_neg())
}

/// Montgomery multiplication modulo p.
#[inline]
fn modp_montymul(a: u32, b: u32, p: u32, p0i: u32) -> u32 {
    let z = (a as u64) * (b as u64);
    let w = ((z.wrapping_mul(p0i as u64)) & 0x7FFF_FFFF).wrapping_mul(p as u64);
    let d = ((z.wrapping_add(w)) >> 31) as u32;
    let d = d.wrapping_sub(p);
    d.wrapping_add(p & (d >> 31).wrapping_neg())
}

/// R2 = 2^62 mod p.
fn modp_r2(p: u32, p0i: u32) -> u32 {
    let mut z = modp_r(p);
    z = modp_add(z, z, p);
    for _ in 0..5 {
        z = modp_montymul(z, z, p, p0i);
    }
    let z = z.wrapping_add(p & (z & 1).wrapping_neg());
    z >> 1
}

/// 2^(31·x) mod p (x ≤ 2^11), Montgomery representation.
#[inline]
fn modp_rx(x: u32, p: u32, p0i: u32, r2: u32) -> u32 {
    let x = x - 1;
    let mut r = r2;
    let mut z = modp_r(p);
    let mut i = 0u32;
    while (1u32 << i) <= x {
        if (x & (1u32 << i)) != 0 {
            z = modp_montymul(z, r, p, p0i);
        }
        r = modp_montymul(r, r, p, p0i);
        i += 1;
    }
    z
}

/// Division modulo prime p.
fn modp_div(a: u32, b: u32, p: u32, p0i: u32, r: u32) -> u32 {
    let e = p - 2;
    let mut z = r;
    for i in (0..=30).rev() {
        z = modp_montymul(z, z, p, p0i);
        let z2 = modp_montymul(z, b, p, p0i);
        z ^= (z ^ z2) & ((e >> i) & 1).wrapping_neg();
    }
    z = modp_montymul(z, 1, p, p0i);
    modp_montymul(a, z, p, p0i)
}

/// Reference `modp_mkgm2`.
fn modp_mkgm2(gm: &mut [u32], igm: &mut [u32], logn: u32, g: u32, p: u32, p0i: u32) {
    let n = 1usize << logn;
    let r2 = modp_r2(p, p0i);
    let mut g = modp_montymul(g, r2, p, p0i);
    let mut k = logn;
    while k < 10 {
        g = modp_montymul(g, g, p, p0i);
        k += 1;
    }
    let ig = modp_div(r2, g, p, p0i, modp_r(p));
    let mut x1 = modp_r(p);
    let mut x2 = modp_r(p);
    k = 10 - logn;
    for u in 0..n {
        let v = super::tables::REV10[u << k] as usize;
        gm[v] = x1;
        igm[v] = x2;
        x1 = modp_montymul(x1, g, p, p0i);
        x2 = modp_montymul(x2, ig, p, p0i);
    }
}

/// Reference `modp_NTT2_ext`.
fn modp_ntt2_ext(a: &mut [u32], stride: usize, gm: &[u32], logn: u32, p: u32, p0i: u32) {
    if logn == 0 {
        return;
    }
    let n = 1usize << logn;
    let mut t = n;
    let mut m = 1usize;
    while m < n {
        let ht = t >> 1;
        let mut v1 = 0usize;
        for u in 0..m {
            let s = gm[m + u];
            let r1base = v1 * stride;
            let r2base = r1base + ht * stride;
            for v in 0..ht {
                let x = a[r1base + v * stride];
                let y = modp_montymul(a[r2base + v * stride], s, p, p0i);
                a[r1base + v * stride] = modp_add(x, y, p);
                a[r2base + v * stride] = modp_sub(x, y, p);
            }
            v1 += t;
        }
        t = ht;
        m <<= 1;
    }
}

/// Reference `modp_iNTT2_ext`.
fn modp_intt2_ext(a: &mut [u32], stride: usize, igm: &[u32], logn: u32, p: u32, p0i: u32) {
    if logn == 0 {
        return;
    }
    let n = 1usize << logn;
    let mut t = 1usize;
    let mut m = n;
    while m > 1 {
        let hm = m >> 1;
        let dt = t << 1;
        let mut v1 = 0usize;
        for u in 0..hm {
            let s = igm[hm + u];
            let r1base = v1 * stride;
            let r2base = r1base + t * stride;
            for v in 0..t {
                let x = a[r1base + v * stride];
                let y = a[r2base + v * stride];
                a[r1base + v * stride] = modp_add(x, y, p);
                a[r2base + v * stride] = modp_montymul(modp_sub(x, y, p), s, p, p0i);
            }
            v1 += dt;
        }
        t = dt;
        m >>= 1;
    }
    let ni = 1u32 << (31 - logn);
    for k in 0..n {
        a[k * stride] = modp_montymul(a[k * stride], ni, p, p0i);
    }
}

#[inline]
fn modp_ntt2(a: &mut [u32], gm: &[u32], logn: u32, p: u32, p0i: u32) {
    modp_ntt2_ext(a, 1, gm, logn, p, p0i);
}

#[inline]
fn modp_intt2(a: &mut [u32], igm: &[u32], logn: u32, p: u32, p0i: u32) {
    modp_intt2_ext(a, 1, igm, logn, p, p0i);
}

/// Reference `modp_poly_rec_res`.
fn modp_poly_rec_res(f: &mut [u32], logn: u32, p: u32, p0i: u32, r2: u32) {
    let hn = 1usize << (logn - 1);
    for u in 0..hn {
        let w0 = f[u << 1];
        let w1 = f[(u << 1) + 1];
        f[u] = modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
    }
}

// ====================================================================
// Bignum: 31-bit words, two's complement.
//
// Integers are little-endian arrays of 31-bit limbs; the sign lives in
// bit 30 of the most significant limb (see `zint_one_to_plain`). All
// loops run over the full limb count, so control flow never depends on
// the values — matching the reference `zint*` helpers of keygen.c.
// ====================================================================

/// Conditionally compute a − b over 31-bit limbs (two's complement):
/// subtracts when `ctl` is 1, leaves `a` untouched when `ctl` is 0.
/// Returns the borrow out of the most significant limb.
fn zint_sub(a: &mut [u32], b: &[u32], ctl: u32) -> u32 {
    let mut cc: u32 = 0;
    let m = ctl.wrapping_neg();
    for u in 0..a.len() {
        let aw = a[u];
        let w = aw.wrapping_sub(b[u]).wrapping_sub(cc);
        cc = w >> 31;
        a[u] = aw ^ ((w & 0x7FFF_FFFF) ^ aw) & m;
    }
    cc
}

/// Multiply a bignum by a small (≤ 31-bit) unsigned integer; returns the
/// carry out of the top limb.
fn zint_mul_small(m: &mut [u32], x: u32) -> u32 {
    let mut cc: u32 = 0;
    for v in m.iter_mut() {
        let z = (*v as u64) * (x as u64) + cc as u64;
        *v = (z as u32) & 0x7FFF_FFFF;
        cc = (z >> 31) as u32;
    }
    cc
}

/// Reduce an unsigned big-endian 31-bit-limb integer modulo the prime p
/// (Horner over the limbs); the result is in Montgomery representation.
fn zint_mod_small_unsigned(d: &[u32], p: u32, p0i: u32, r2: u32) -> u32 {
    let mut x: u32 = 0;
    let mut u = d.len();
    while u > 0 {
        u -= 1;
        x = modp_montymul(x, r2, p, p0i);
        let mut w = d[u];
        w = w.wrapping_sub(p);
        w = w.wrapping_add(p & (w >> 31).wrapping_neg());
        x = modp_add(x, w, p);
    }
    x
}

/// Same as `zint_mod_small_unsigned` for a signed value: `rx` must be
/// 2^(31·len) mod p in Montgomery form and is subtracted when the top
/// limb's sign bit (bit 30) is set.
fn zint_mod_small_signed(d: &[u32], p: u32, p0i: u32, r2: u32, rx: u32) -> u32 {
    if d.is_empty() {
        return 0;
    }
    let mut z = zint_mod_small_unsigned(d, p, p0i, r2);
    z = modp_sub(z, rx & -((d[d.len() - 1] >> 30) as i32) as u32, p);
    z
}

/// x += y·s over 31-bit limbs (unsigned multiplier); `x` carries one extra
/// limb that receives the final carry.
fn zint_add_mul_small(x: &mut [u32], y: &[u32], s: u32) {
    let mut cc: u32 = 0;
    for u in 0..y.len() {
        let xw = x[u];
        let yw = y[u];
        let z = (yw as u64) * (s as u64) + (xw as u64) + (cc as u64);
        x[u] = (z as u32) & 0x7FFF_FFFF;
        cc = (z >> 31) as u32;
    }
    x[y.len()] = cc;
}

/// Normalize x into [−m/2, m/2) for the multi-limb modulus `p`: subtract
/// p once when x > p/2, comparing from the most significant limb down.
fn zint_norm_zero(x: &mut [u32], p: &[u32]) {
    let len = x.len();
    let mut r: u32 = 0;
    let mut bb: u32 = 0;
    let mut u = len;
    while u > 0 {
        u -= 1;
        let wx = x[u];
        let wp = (p[u] >> 1) | (bb << 30);
        bb = p[u] & 1;
        let cc0 = wp.wrapping_sub(wx);
        let cc = ((cc0.wrapping_neg()) >> 31) | (cc0 >> 31).wrapping_neg();
        r |= cc & (r & 1).wrapping_sub(1);
    }
    zint_sub(x, p, r >> 31);
}

/// Rebuild `num` integers from their residues modulo the first `xlen`
/// PRIMES (each integer is `xlen` limbs at stride `xstride`) with the
/// incremental Garner/CRT method: level u corrects every value by
/// (x_u − x mod P_{<u})·P_{<u} using the precomputed Montgomery-form
/// coefficient s from the PRIMES table. When `normalize_signed` is set,
/// results are re-centered around zero against the product P.
fn zint_rebuild_crt(
    xx: &mut [u32],
    xlen: usize,
    xstride: usize,
    num: usize,
    normalize_signed: bool,
    tmp: &mut [u32],
) {
    tmp[0] = PRIMES[0].0;
    for u in 1..xlen {
        let (p, _g, s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        for v in 0..num {
            let base = v * xstride;
            let xp = xx[base + u];
            let xq = zint_mod_small_unsigned(&xx[base..base + u], p, p0i, r2);
            let xr = modp_montymul(s, modp_sub(xp, xq, p), p, p0i);
            zint_add_mul_small(&mut xx[base..], &tmp[..u], xr);
        }
        tmp[u] = zint_mul_small(&mut tmp[..u], p);
    }
    if normalize_signed {
        for v in 0..num {
            let base = v * xstride;
            let x = &mut xx[base..base + xlen];
            let pvec = &tmp[..xlen];
            zint_norm_zero(x, pvec);
        }
    }
}

/// Conditionally negate a bignum (`ctl` = 0 or 1), propagating the carry
/// chain so the two's complement stays correct.
fn zint_negate(a: &mut [u32], ctl: u32) {
    let mut cc = ctl;
    let m = ctl.wrapping_neg() >> 1;
    for v in a.iter_mut() {
        let aw = (*v ^ m).wrapping_add(cc);
        *v = aw & 0x7FFF_FFFF;
        cc = aw >> 31;
    }
}

/// Apply the linear combination a' = xa·a + xb·b, b' = ya·a + yb·b to two
/// signed 31-bit-limb integers (coefficients are small i64 scalars, one
/// Bézout half-GCD step's worth). Outputs whose top limb came out
/// negative are negated back to positive; the return value carries a flag
/// bit for each output that was negated.
fn zint_co_reduce(a: &mut [u32], b: &mut [u32], xa: i64, xb: i64, ya: i64, yb: i64) -> u32 {
    let len = a.len();
    let mut cca: i64 = 0;
    let mut ccb: i64 = 0;
    for u in 0..len {
        let wa = a[u] as u64;
        let wb = b[u] as u64;
        let za = wa
            .wrapping_mul(xa as u64)
            .wrapping_add(wb.wrapping_mul(xb as u64))
            .wrapping_add(cca as u64);
        let zb = wa
            .wrapping_mul(ya as u64)
            .wrapping_add(wb.wrapping_mul(yb as u64))
            .wrapping_add(ccb as u64);
        if u > 0 {
            a[u - 1] = (za as u32) & 0x7FFF_FFFF;
            b[u - 1] = (zb as u32) & 0x7FFF_FFFF;
        }
        cca = (za as i64) >> 31;
        ccb = (zb as i64) >> 31;
    }
    a[len - 1] = cca as u32;
    b[len - 1] = ccb as u32;

    let nega = ((cca as u64) >> 63) as u32;
    let negb = ((ccb as u64) >> 63) as u32;
    zint_negate(a, nega);
    zint_negate(b, negb);
    nega | (negb << 1)
}

/// Fold the top limb's borrow back into `a`: conditional subtract of the
/// modulus `m`, so a value that overflowed into [m, 2m) (or went negative
/// under `neg`) ends in [0, m).
fn zint_finish_mod(a: &mut [u32], m: &[u32], neg: u32) {
    let len = a.len();
    let mut cc: u32 = 0;
    for u in 0..len {
        cc = a[u].wrapping_sub(m[u]).wrapping_sub(cc) >> 31;
    }
    let xm = neg.wrapping_neg() >> 1;
    let ym = ((neg as i32) | (1 - cc as i32)).wrapping_neg() as u32;
    let mut cc = neg;
    for u in 0..len {
        let aw = a[u];
        let mw = (m[u] ^ xm) & ym;
        let aw = aw.wrapping_sub(mw).wrapping_sub(cc);
        a[u] = aw & 0x7FFF_FFFF;
        cc = aw >> 31;
    }
}

/// `zint_co_reduce` with reduction modulo the multi-limb modulus `m`: the
/// low-limb folding factors fa/fb come from a Montgomery-style reduction
/// with −m^−1 mod 2^31, and both outputs end in [0, m).
#[allow(clippy::too_many_arguments)]
fn zint_co_reduce_mod(
    a: &mut [u32],
    b: &mut [u32],
    m: &[u32],
    m0i: u32,
    xa: i64,
    xb: i64,
    ya: i64,
    yb: i64,
) {
    let len = a.len();
    let mut cca: i64 = 0;
    let mut ccb: i64 = 0;
    let fa = a[0]
        .wrapping_mul(xa as u32)
        .wrapping_add(b[0].wrapping_mul(xb as u32))
        .wrapping_mul(m0i)
        & 0x7FFF_FFFF;
    let fb = a[0]
        .wrapping_mul(ya as u32)
        .wrapping_add(b[0].wrapping_mul(yb as u32))
        .wrapping_mul(m0i)
        & 0x7FFF_FFFF;
    for u in 0..len {
        let wa = a[u] as u64;
        let wb = b[u] as u64;
        let za = wa
            .wrapping_mul(xa as u64)
            .wrapping_add(wb.wrapping_mul(xb as u64))
            .wrapping_add((m[u] as u64).wrapping_mul(fa as u64))
            .wrapping_add(cca as u64);
        let zb = wa
            .wrapping_mul(ya as u64)
            .wrapping_add(wb.wrapping_mul(yb as u64))
            .wrapping_add((m[u] as u64).wrapping_mul(fb as u64))
            .wrapping_add(ccb as u64);
        if u > 0 {
            a[u - 1] = (za as u32) & 0x7FFF_FFFF;
            b[u - 1] = (zb as u32) & 0x7FFF_FFFF;
        }
        cca = (za as i64) >> 31;
        ccb = (zb as i64) >> 31;
    }
    a[len - 1] = cca as u32;
    b[len - 1] = ccb as u32;
    zint_finish_mod(a, m, ((cca as u64) >> 63) as u32);
    zint_finish_mod(b, m, ((ccb as u64) >> 63) as u32);
}

/// Half-GCD (binary extended Bézout) over the signed 31-bit-limb integers
/// `x` and `y` (both expected odd): computes u, v with u·x + v·y = gcd,
/// 31 bits per iteration, carrying the coefficient updates through
/// `zint_co_reduce_mod`. Returns 1 iff the final gcd is exactly 1, else 0.
fn zint_bezout(u: &mut [u32], v: &mut [u32], x: &[u32], y: &[u32], tmp: &mut [u32]) -> i32 {
    let len = x.len();
    if len == 0 {
        return 0;
    }

    let (u0, v0) = (&mut u[..], &mut v[..]);
    let (u1, rest) = tmp.split_at_mut(len);
    let (v1, rest) = rest.split_at_mut(len);
    let (a, b) = rest.split_at_mut(len);

    let x0i = modp_ninv31(x[0]);
    let y0i = modp_ninv31(y[0]);

    a.copy_from_slice(x);
    b.copy_from_slice(y);
    u0[0] = 1;
    u0[1..len].fill(0);
    v0.fill(0);
    u1.copy_from_slice(y);
    v1.copy_from_slice(x);
    v1[0] = v1[0].wrapping_sub(1);

    let mut num: u32 = 62 * (len as u32) + 30;
    while num >= 30 {
        let mut c0: u32 = u32::MAX;
        let mut c1: u32 = u32::MAX;
        let mut a0: u32 = 0;
        let mut a1: u32 = 0;
        let mut b0: u32 = 0;
        let mut b1: u32 = 0;
        for j in (0..len).rev() {
            let aw = a[j];
            let bw = b[j];
            a0 ^= (a0 ^ aw) & c0;
            a1 ^= (a1 ^ aw) & c1;
            b0 ^= (b0 ^ bw) & c0;
            b1 ^= (b1 ^ bw) & c1;
            c1 = c0;
            c0 &= (((aw | bw).wrapping_add(0x7FFF_FFFF)) >> 31).wrapping_sub(1);
        }
        a1 |= a0 & c1;
        a0 &= !c1;
        b1 |= b0 & c1;
        b0 &= !c1;
        let mut a_hi = ((a0 as u64) << 31) + a1 as u64;
        let mut b_hi = ((b0 as u64) << 31) + b1 as u64;
        let mut a_lo = a[0];
        let mut b_lo = b[0];

        let mut pa: i64 = 1;
        let mut pb: i64 = 0;
        let mut qa: i64 = 0;
        let mut qb: i64 = 1;
        for i in 0..31 {
            let rz = b_hi.wrapping_sub(a_hi);
            let rt = ((rz ^ ((a_hi ^ b_hi) & (a_hi ^ rz))) >> 63) as u32;

            let oa = (a_lo >> i) & 1;
            let ob = (b_lo >> i) & 1;
            let cab = oa & ob & rt;
            let cba = oa & ob & !rt;
            let ca = cab | (oa ^ 1);

            a_lo = a_lo.wrapping_sub(b_lo & cab.wrapping_neg());
            a_hi = a_hi.wrapping_sub(b_hi & (cab as i64).wrapping_neg() as u64);
            pa -= qa & -(cab as i64);
            pb -= qb & -(cab as i64);
            b_lo = b_lo.wrapping_sub(a_lo & cba.wrapping_neg());
            b_hi = b_hi.wrapping_sub(a_hi & (cba as i64).wrapping_neg() as u64);
            qa -= pa & -(cba as i64);
            qb -= pb & -(cba as i64);

            a_lo = a_lo.wrapping_add(a_lo & ca.wrapping_sub(1));
            pa += pa & ((ca as i64) - 1);
            pb += pb & ((ca as i64) - 1);
            a_hi ^= (a_hi ^ (a_hi >> 1)) & (ca as i64).wrapping_neg() as u64;
            b_lo = b_lo.wrapping_add(b_lo & ca.wrapping_neg());
            qa += qa & -(ca as i64);
            qb += qb & -(ca as i64);
            b_hi ^= (b_hi ^ (b_hi >> 1)) & (ca as u64).wrapping_sub(1);
        }

        let r = zint_co_reduce(a, b, pa, pb, qa, qb);
        let pa = pa - ((pa + pa) & -((r & 1) as i64));
        let pb = pb - ((pb + pb) & -((r & 1) as i64));
        let qa = qa - ((qa + qa) & -((r >> 1) as i64));
        let qb = qb - ((qb + qb) & -((r >> 1) as i64));
        zint_co_reduce_mod(u0, u1, y, y0i, pa, pb, qa, qb);
        zint_co_reduce_mod(v0, v1, x, x0i, pa, pb, qa, qb);

        num = num.wrapping_sub(30);
    }

    let mut rc = a[0] ^ 1;
    for j in 1..len {
        rc |= a[j];
    }
    (1 - (((rc | rc.wrapping_neg()) >> 31) as i32)) & (x[0] & y[0]) as i32
}

/// x += k·y·2^(31·sch + scl) with a small signed multiplier k; limbs of
/// `y` beyond its length are filled with its sign extension.
fn zint_add_scaled_mul_small(x: &mut [u32], y: &[u32], k: i32, sch: u32, scl: u32) {
    if y.is_empty() {
        return;
    }
    let ysign = (y[y.len() - 1] >> 30).wrapping_neg() >> 1;
    let mut tw: u32 = 0;
    let mut cc: i32 = 0;
    for u in sch as usize..x.len() {
        let v = u - sch as usize;
        let wy = if v < y.len() { y[v] } else { ysign };
        let wys = ((wy << scl) & 0x7FFF_FFFF) | tw;
        tw = wy >> (31 - scl);
        let z = (wys as i64)
            .wrapping_mul(k as i64)
            .wrapping_add(x[u] as i32 as i64)
            .wrapping_add(cc as i64);
        x[u] = (z as u32) & 0x7FFF_FFFF;
        cc = ((z as u64) >> 31) as i32;
    }
}

/// x −= y·2^(31·sch + scl), with sign extension beyond `y`'s length.
fn zint_sub_scaled(x: &mut [u32], y: &[u32], sch: u32, scl: u32) {
    if y.is_empty() {
        return;
    }
    let ysign = (y[y.len() - 1] >> 30).wrapping_neg() >> 1;
    let mut tw: u32 = 0;
    let mut cc: u32 = 0;
    for u in sch as usize..x.len() {
        let v = u - sch as usize;
        let wy = if v < y.len() { y[v] } else { ysign };
        let wys = ((wy << scl) & 0x7FFF_FFFF) | tw;
        tw = wy >> (31 - scl);
        let w = x[u].wrapping_sub(wys).wrapping_sub(cc);
        x[u] = w & 0x7FFF_FFFF;
        cc = w >> 31;
    }
}

/// Read the low limb of a bignum as a signed i32 by replicating the limb
/// sign bit (bit 30) into the i32 sign position.
#[inline]
fn zint_one_to_plain(x: &[u32]) -> i32 {
    let mut w = x[0];
    w |= (w & 0x4000_0000) << 1;
    w as i32
}

// ====================================================================
// Conversions and polynomial level helpers.
// ====================================================================

/// Convert the multi-precision coefficients of a polynomial (`flen` limbs
/// per coefficient at stride `fstride`) into soft-float values: each
/// coefficient is sign-folded and accumulated limb by limb in base 2^31.
fn poly_big_to_fp(d: &mut [Fpr], f: &[u32], flen: usize, fstride: usize, logn: u32) {
    let n = 1usize << logn;
    if flen == 0 {
        for v in d.iter_mut().take(n) {
            *v = FPR_ZERO;
        }
        return;
    }
    for u in 0..n {
        let fp = &f[u * fstride..];
        let neg = (fp[flen - 1] >> 30).wrapping_neg();
        let xm = neg >> 1;
        let mut cc = neg & 1;
        let mut x = FPR_ZERO;
        let mut fsc = FPR_ONE;
        for v in 0..flen {
            let mut w = (fp[v] ^ xm).wrapping_add(cc);
            cc = w >> 31;
            w &= 0x7FFF_FFFF;
            w = w.wrapping_sub((w << 1) & neg);
            x = fpr_add(x, fpr_mul(fpr_of(w as i32 as i64), fsc));
            fsc = fpr_mul(fsc, FPR_PTWO31);
        }
        d[u] = x;
    }
}

/// Convert big-integer coefficients back to i8; fails (returns false) if
/// any coefficient falls outside ±lim.
fn poly_big_to_small(d: &mut [i8], s: &[u32], lim: i32, logn: u32) -> bool {
    let n = 1usize << logn;
    for u in 0..n {
        let z = zint_one_to_plain(&s[u..]);
        if z < -lim || z > lim {
            return false;
        }
        d[u] = z as i8;
    }
    true
}

/// F −= k·g and G −= k·g on multi-precision coefficients (plain bignum
/// path): for each output coefficient u the scaled k[u]·g is folded in,
/// negating k and restarting from coefficient 0 at the negacyclic wrap
/// (u + v = n − 1, because X^n = −1).
#[allow(clippy::too_many_arguments)]
fn poly_sub_scaled(
    big_f: &mut [u32],
    flen: usize,
    fstride: usize,
    f: &[u32],
    glen: usize,
    gstride: usize,
    k: &[i32],
    sch: u32,
    scl: u32,
    logn: u32,
) {
    let n = 1usize << logn;
    for u in 0..n {
        let mut kf = -k[u];
        let mut xoff = u * fstride;
        let mut yoff = 0usize;
        for v in 0..n {
            {
                let x = &mut big_f[xoff..xoff + flen];
                let y = &f[yoff..yoff + glen];
                zint_add_scaled_mul_small(x, y, kf, sch, scl);
            }
            if u + v == n - 1 {
                xoff = 0;
                kf = -kf;
            } else {
                xoff += fstride;
            }
            yoff += gstride;
        }
    }
}

/// Same subtraction as `poly_sub_scaled` but with the product k·g
/// computed through an NTT over the first `tlen` primes (k is small, g is
/// multi-limb), CRT-rebuilt to plain bignums before the scaled
/// subtraction. Used at shallow depths where NTT amortizes better.
#[allow(clippy::too_many_arguments)]
fn poly_sub_scaled_ntt(
    big_f: &mut [u32],
    flen: usize,
    fstride: usize,
    f: &[u32],
    glen: usize,
    gstride: usize,
    k: &[i32],
    sch: u32,
    scl: u32,
    logn: u32,
) {
    let n = 1usize << logn;
    let tlen = glen + 1;

    let mut gm = vec![0u32; n];
    let mut igm = vec![0u32; n];
    let mut fk = vec![0u32; n * tlen];
    let mut t1 = vec![0u32; n];

    for u in 0..tlen {
        let (p, g, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        let rx = modp_rx(glen as u32, p, p0i, r2);
        modp_mkgm2(&mut gm, &mut igm, logn, g, p, p0i);

        for v in 0..n {
            t1[v] = modp_set(k[v], p);
        }
        modp_ntt2(&mut t1, &gm, logn, p, p0i);
        for v in 0..n {
            let y = &f[v * gstride..v * gstride + glen];
            fk[v * tlen + u] = zint_mod_small_signed(y, p, p0i, r2, rx);
        }
        modp_ntt2_ext(&mut fk[u..], tlen, &gm, logn, p, p0i);
        for v in 0..n {
            let x = modp_montymul(t1[v], fk[v * tlen + u], p, p0i);
            fk[v * tlen + u] = modp_montymul(x, r2, p, p0i);
        }
        modp_intt2_ext(&mut fk[u..], tlen, &igm, logn, p, p0i);
    }

    zint_rebuild_crt(&mut fk, tlen, tlen, n, true, &mut t1);

    for u in 0..n {
        let x = &mut big_f[u * fstride..u * fstride + flen];
        let y = &fk[u * tlen..u * tlen + tlen];
        zint_sub_scaled(x, y, sch, scl);
    }
}

// ====================================================================
// make_fg: f and g at a given depth, RNS(+NTT).
// ====================================================================

/// One descent step of the NTRU-solve preprocessing (degree n -> n/2):
/// from the RNS residues of f and g at depth `depth`, compute the
/// half-degree polynomials f_d and g_d of the resultant descent
/// f_d(Y) = f0(Y)² − Y·f1(Y)² for f = f0(Y²) + Y·f1(Y²); in NTT terms
/// this is the paired butterfly w0·w1 below ((ζ²)^(n/2) = ζ^n = −1 keeps
/// the half-size transform negacyclic). `in_ntt` / `out_ntt` say whether
/// the level's residues arrive in, and must stay in, NTT domain; the
/// full-degree f, g are always CRT-rebuilt into plain signed bignums in
/// their (`fs`/`gs`) regions.
fn make_fg_step(data: &mut [u32], logn: u32, depth: usize, in_ntt: bool, out_ntt: bool) {
    let n = 1usize << logn;
    let hn = n >> 1;
    let slen = MAX_BL_SMALL[depth];
    let tlen = MAX_BL_SMALL[depth + 1];

    let off_fd = 0usize;
    let off_gd = off_fd + hn * tlen;
    let off_fs = off_gd + hn * tlen;
    let off_gs = off_fs + n * slen;
    let off_t1 = off_gs + n * slen;

    data.copy_within(0..2 * n * slen, off_fs);

    // Per-prime twiddle tables (kept outside `data`: mkgm2 writes all
    // 2^logn slots, which would clobber the fd/fs regions otherwise).
    let mut gm = vec![0u32; n];
    let mut igm = vec![0u32; n];

    for u in 0..slen {
        let (p, g, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        modp_mkgm2(&mut gm, &mut igm, logn, g, p, p0i);

        for v in 0..n {
            data[off_t1 + v] = data[off_fs + v * slen + u];
        }
        if !in_ntt {
            modp_ntt2(&mut data[off_t1..off_t1 + n], &gm, logn, p, p0i);
        }
        for v in 0..hn {
            let w0 = data[off_t1 + (v << 1)];
            let w1 = data[off_t1 + (v << 1) + 1];
            data[off_fd + v * tlen + u] = modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
        }
        if in_ntt {
            modp_intt2_ext(&mut data[off_fs + u..], slen, &igm, logn, p, p0i);
        }

        for v in 0..n {
            data[off_t1 + v] = data[off_gs + v * slen + u];
        }
        if !in_ntt {
            modp_ntt2(&mut data[off_t1..off_t1 + n], &gm, logn, p, p0i);
        }
        for v in 0..hn {
            let w0 = data[off_t1 + (v << 1)];
            let w1 = data[off_t1 + (v << 1) + 1];
            data[off_gd + v * tlen + u] = modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
        }
        if in_ntt {
            modp_intt2_ext(&mut data[off_gs + u..], slen, &igm, logn, p, p0i);
        }

        if !out_ntt {
            modp_intt2_ext(&mut data[off_fd + u..], tlen, &igm, logn - 1, p, p0i);
            modp_intt2_ext(&mut data[off_gd + u..], tlen, &igm, logn - 1, p, p0i);
        }
    }

    {
        let mut fs = data[off_fs..off_fs + n * slen].to_vec();
        let mut scratch = vec![0u32; slen.max(1)];
        zint_rebuild_crt(&mut fs, slen, slen, n, true, &mut scratch);
        data[off_fs..off_fs + n * slen].copy_from_slice(&fs);
    }
    {
        let mut gs = data[off_gs..off_gs + n * slen].to_vec();
        let mut scratch = vec![0u32; slen.max(1)];
        zint_rebuild_crt(&mut gs, slen, slen, n, true, &mut scratch);
        data[off_gs..off_gs + n * slen].copy_from_slice(&gs);
    }

    for u in slen..tlen {
        let (p, g, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        let rx = modp_rx(slen as u32, p, p0i, r2);
        modp_mkgm2(&mut gm, &mut igm, logn, g, p, p0i);

        for v in 0..n {
            let x = &data[off_fs + v * slen..off_fs + v * slen + slen];
            data[off_t1 + v] = zint_mod_small_signed(x, p, p0i, r2, rx);
        }
        modp_ntt2(&mut data[off_t1..off_t1 + n], &gm, logn, p, p0i);
        for v in 0..hn {
            let w0 = data[off_t1 + (v << 1)];
            let w1 = data[off_t1 + (v << 1) + 1];
            data[off_fd + v * tlen + u] = modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
        }
        for v in 0..n {
            let x = &data[off_gs + v * slen..off_gs + v * slen + slen];
            data[off_t1 + v] = zint_mod_small_signed(x, p, p0i, r2, rx);
        }
        modp_ntt2(&mut data[off_t1..off_t1 + n], &gm, logn, p, p0i);
        for v in 0..hn {
            let w0 = data[off_t1 + (v << 1)];
            let w1 = data[off_t1 + (v << 1) + 1];
            data[off_gd + v * tlen + u] = modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
        }

        if !out_ntt {
            modp_intt2_ext(&mut data[off_fd + u..], tlen, &igm, logn - 1, p, p0i);
            modp_intt2_ext(&mut data[off_gd + u..], tlen, &igm, logn - 1, p, p0i);
        }
    }
}

/// Required data-buffer size (words) for `make_fg`: worst case over the
/// descent levels of the residue regions plus the per-prime scratch
/// (gm/igm/t1), and the initial f‖g region at the top.
fn make_fg_buflen(logn_top: u32, depth: usize) -> usize {
    let mut maxw = 2 * (1usize << logn_top);
    for d in 0..depth {
        let nd = 1usize << (logn_top - d as u32);
        let slen = MAX_BL_SMALL[d];
        let tlen = MAX_BL_SMALL[d + 1];
        maxw = maxw.max(nd * tlen + 2 * nd * slen + 4 * nd);
    }
    let nfin = 1usize << (logn_top - depth as u32);
    let slen_end = MAX_BL_SMALL[depth];
    maxw.max(2 * nfin * slen_end)
}

/// Reference `make_fg`: lay out f and g as RNS residues (f first, then g,
/// one word per prime) and run `depth` descent steps toward the resultant
/// form used by the NTRU solve. With `out_ntt` the final (half-degree)
/// residues stay in NTT domain.
fn make_fg(f: &[i8], g: &[i8], logn_top: u32, depth: usize, out_ntt: bool) -> Vec<u32> {
    let n_top = 1usize << logn_top;
    let mut data = vec![0u32; make_fg_buflen(logn_top, depth)];
    let p0 = PRIMES[0].0;
    for u in 0..n_top {
        data[u] = modp_set(f[u] as i32, p0);
        data[n_top + u] = modp_set(g[u] as i32, p0);
    }

    if depth == 0 && out_ntt {
        let p = PRIMES[0].0;
        let p0i = modp_ninv31(p);
        let mut gm = vec![0u32; n_top];
        let mut igm = vec![0u32; n_top];
        modp_mkgm2(&mut gm, &mut igm, logn_top, PRIMES[0].1, p, p0i);
        modp_ntt2(&mut data[..n_top], &gm, logn_top, p, p0i);
        modp_ntt2(&mut data[n_top..2 * n_top], &gm, logn_top, p, p0i);
        return data;
    }

    for d in 0..depth {
        make_fg_step(
            &mut data,
            logn_top - d as u32,
            d,
            d != 0,
            (d + 1) < depth || out_ntt,
        );
    }
    data
}

/// Reference `solve_NTRU_deepest`: bottom of the descent, where f and g
/// have been reduced to integers (their resultants modulo the primes,
/// CRT-rebuilt into bignums). A Bézout gives F0, G0 with
/// F0·Res(f) ± G0·Res(g) = 1; scaling both by q yields the deepest-level
/// solution of f·G − g·F = q. Fails if the resultants are not coprime or
/// the ×q multiplication overflows the limb budget.
fn solve_ntru_deepest(logn_top: u32, f: &[i8], g: &[i8], tmp: &mut [u32]) -> bool {
    let len = MAX_BL_SMALL[logn_top as usize];

    let data = make_fg(f, g, logn_top, logn_top as usize, false);
    // Resultants: data[0..len] (f) and data[len..2len] (g).
    let mut fp_gp = vec![0u32; 2 * len];
    fp_gp[..len].copy_from_slice(&data[..len]);
    fp_gp[len..2 * len].copy_from_slice(&data[len..2 * len]);

    let mut scratch = vec![0u32; 4 * len];
    zint_rebuild_crt(&mut fp_gp, len, len, 2, false, &mut scratch);

    let fp = fp_gp[..len].to_vec();
    let gp = fp_gp[len..2 * len].to_vec();
    let mut g_out = vec![0u32; len];
    let mut f_out = vec![0u32; len];
    let bez = zint_bezout(&mut g_out, &mut f_out, &fp, &gp, &mut scratch);
    if bez == 0 {
        return false;
    }
    if zint_mul_small(&mut f_out, 12289) != 0 || zint_mul_small(&mut g_out, 12289) != 0 {
        return false;
    }
    tmp[..len].copy_from_slice(&f_out);
    tmp[len..2 * len].copy_from_slice(&g_out);
    true
}

/// Reference `solve_NTRU_intermediate`: lift the half-degree (F, G)
/// solution from `tmp` to the current level by the per-prime NTT pairing
/// (the reverse of the `make_fg_step` butterfly), then Babai-reduce:
/// k = round((F·adj(f) + G·adj(g)) / (f·adj(f) + g·adj(g))) is evaluated
/// with FFT-domain polynomial arithmetic and subtracted, iterating while
/// the working precision (`scale_k`, stepped down 25 bits at a time)
/// still allows the multiplier to fit within the ±(2^31 − 1) check.
#[allow(clippy::too_many_arguments)]
fn solve_ntru_intermediate(
    logn_top: u32,
    f: &[i8],
    g: &[i8],
    depth: usize,
    tmp: &mut [u32],
) -> bool {
    let logn = logn_top - depth as u32;
    let n = 1usize << logn;
    let hn = n >> 1;

    let slen = MAX_BL_SMALL[depth];
    let dlen = MAX_BL_SMALL[depth + 1];
    let llen = MAX_BL_LARGE[depth];

    // Fd/Gd from the deeper level (tmp: hn ints of dlen words each).
    let fd = tmp[..dlen * hn].to_vec();
    let gd = tmp[dlen * hn..2 * dlen * hn].to_vec();

    // f,g for this level in RNS+NTT (2n ints of slen words).
    let mut fg = make_fg(f, g, logn_top, depth, true);

    let mut ft = vec![0u32; n * llen];
    let mut gt = vec![0u32; n * llen];
    let _t1 = vec![0u32; (2 * n * slen).max(2 * hn * dlen).max(2 * n)];

    for u in 0..llen {
        let (p, _g, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        let rx = modp_rx(dlen as u32, p, p0i, r2);
        for v in 0..hn {
            let xs = &fd[v * dlen..v * dlen + dlen];
            let ys = &gd[v * dlen..v * dlen + dlen];
            ft[u + v * llen] = zint_mod_small_signed(xs, p, p0i, r2, rx);
            gt[u + v * llen] = zint_mod_small_signed(ys, p, p0i, r2, rx);
        }
    }

    for u in 0..llen {
        let (p, g_gen, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);

        if u == slen {
            let mut scratch = vec![0u32; slen.max(1)];
            let mut ftc = fg[..n * slen].to_vec();
            zint_rebuild_crt(&mut ftc, slen, slen, n, true, &mut scratch);
            fg[..n * slen].copy_from_slice(&ftc);
            let mut gtc = fg[n * slen..2 * n * slen].to_vec();
            zint_rebuild_crt(&mut gtc, slen, slen, n, true, &mut scratch);
            fg[n * slen..2 * n * slen].copy_from_slice(&gtc);
        }

        let mut gm = vec![0u32; n];
        let mut igm = vec![0u32; n];
        let mut fx = vec![0u32; n];
        let mut gx = vec![0u32; n];

        modp_mkgm2(&mut gm, &mut igm, logn, g_gen, p, p0i);

        if u < slen {
            for v in 0..n {
                fx[v] = fg[v * slen + u];
                gx[v] = fg[n * slen + v * slen + u];
            }
            modp_intt2_ext(&mut fg[u..], slen, &igm, logn, p, p0i);
            modp_intt2_ext(&mut fg[n * slen + u..], slen, &igm, logn, p, p0i);
        } else {
            let rx = modp_rx(slen as u32, p, p0i, r2);
            for v in 0..n {
                let x = &fg[v * slen..v * slen + slen];
                let y = &fg[n * slen + v * slen..n * slen + v * slen + slen];
                fx[v] = zint_mod_small_signed(x, p, p0i, r2, rx);
                gx[v] = zint_mod_small_signed(y, p, p0i, r2, rx);
            }
            modp_ntt2(&mut fx, &gm, logn, p, p0i);
            modp_ntt2(&mut gx, &gm, logn, p, p0i);
        }

        let mut fp_ = vec![0u32; hn];
        let mut gp_ = vec![0u32; hn];
        for v in 0..hn {
            fp_[v] = ft[u + v * llen];
            gp_[v] = gt[u + v * llen];
        }
        modp_ntt2(&mut fp_, &gm, logn - 1, p, p0i);
        modp_ntt2(&mut gp_, &gm, logn - 1, p, p0i);

        for v in 0..hn {
            let fta = fx[v << 1];
            let ftb = fx[(v << 1) + 1];
            let gta = gx[v << 1];
            let gtb = gx[(v << 1) + 1];
            let mfp = modp_montymul(fp_[v], r2, p, p0i);
            let mgp = modp_montymul(gp_[v], r2, p, p0i);
            ft[u + v * (llen << 1)] = modp_montymul(gtb, mfp, p, p0i);
            ft[u + (v * 2 + 1) * llen] = modp_montymul(gta, mfp, p, p0i);
            gt[u + v * (llen << 1)] = modp_montymul(ftb, mgp, p, p0i);
            gt[u + (v * 2 + 1) * llen] = modp_montymul(fta, mgp, p, p0i);
        }
        modp_intt2_ext(&mut ft[u..], llen, &igm, logn, p, p0i);
        modp_intt2_ext(&mut gt[u..], llen, &igm, logn, p, p0i);
    }

    let mut scratch = vec![0u32; llen.max(1)];
    {
        let mut ftc = ft.clone();
        zint_rebuild_crt(&mut ftc, llen, llen, n, true, &mut scratch);
        ft.copy_from_slice(&ftc);
        let mut gtc = gt.clone();
        zint_rebuild_crt(&mut gtc, llen, llen, n, true, &mut scratch);
        gt.copy_from_slice(&gtc);
    }

    // Babai reduction.
    let mut rt3 = vec![0u64; n];
    let mut rt4 = vec![0u64; n];
    let mut rt5 = vec![0u64; n];
    let mut rt1 = vec![0u64; n];
    let mut rt2 = vec![0u64; n];
    let mut k = vec![0i32; n];

    let rlen0 = slen.min(10);
    poly_big_to_fp(&mut rt3, &fg[slen - rlen0..], rlen0, slen, logn);
    poly_big_to_fp(&mut rt4, &fg[n * slen + slen - rlen0..], rlen0, slen, logn);

    let scale_fg = 31 * (slen - rlen0) as i32;
    let minbl_fg = BITLENGTH[depth].0 - 6 * BITLENGTH[depth].1;
    let maxbl_fg = BITLENGTH[depth].0 + 6 * BITLENGTH[depth].1;

    super::fft::fft(&mut rt3, logn);
    super::fft::fft(&mut rt4, logn);
    super::fft::poly_invnorm2_fft(&mut rt5, &rt3, &rt4, logn);
    super::fft::poly_adj_fft(&mut rt3, logn);
    super::fft::poly_adj_fft(&mut rt4, logn);

    let mut fglen = llen;
    let mut maxbl_fg_current = 31 * llen as i32;
    let mut scale_k = 31 * llen as i32 - minbl_fg;

    loop {
        let rlen = fglen.min(10);
        let scale_fg_current = 31 * (fglen - rlen) as i32;
        poly_big_to_fp(&mut rt1, &ft[fglen - rlen..], rlen, llen, logn);
        poly_big_to_fp(&mut rt2, &gt[fglen - rlen..], rlen, llen, logn);

        super::fft::fft(&mut rt1, logn);
        super::fft::fft(&mut rt2, logn);
        super::fft::poly_mul_fft(&mut rt1, &rt3, logn);
        super::fft::poly_mul_fft(&mut rt2, &rt4, logn);
        super::fft::poly_add(&mut rt2, &rt1, logn);
        super::fft::poly_mul_autoadj_fft(&mut rt2, &rt5, logn);
        super::fft::ifft(&mut rt2, logn);

        let mut dc = scale_k - scale_fg_current + scale_fg;

        let mut pt = if dc < 0 { FPR_TWO } else { FPR_ONEHALF };
        if dc < 0 {
            dc = -dc;
        }
        let mut pdc = FPR_ONE;
        while dc != 0 {
            if (dc & 1) != 0 {
                pdc = fpr_mul(pdc, pt);
            }
            dc >>= 1;
            pt = fpr_sqr(pt);
        }

        for u in 0..n {
            let xv = fpr_mul(rt2[u], pdc);

            // Occasionally the values go out of bounds when the algorithm
            // fails; reject the candidate instead of invoking fpr_rint.
            if !fpr_lt(FPR_MTWO31M1, xv) || !fpr_lt(xv, FPR_PTWO31M1) {
                return false;
            }
            k[u] = fpr_rint(xv) as i32;
        }
        let sch = (scale_k / 31) as u32;
        let scl = (scale_k % 31) as u32;
        if depth <= DEPTH_INT_FG as usize {
            poly_sub_scaled_ntt(
                &mut ft,
                fglen,
                llen,
                &fg[..n * slen],
                slen,
                slen,
                &k,
                sch,
                scl,
                logn,
            );
            poly_sub_scaled_ntt(
                &mut gt,
                fglen,
                llen,
                &fg[n * slen..2 * n * slen],
                slen,
                slen,
                &k,
                sch,
                scl,
                logn,
            );
        } else {
            poly_sub_scaled(
                &mut ft,
                fglen,
                llen,
                &fg[..n * slen],
                slen,
                slen,
                &k,
                sch,
                scl,
                logn,
            );
            poly_sub_scaled(
                &mut gt,
                fglen,
                llen,
                &fg[n * slen..2 * n * slen],
                slen,
                slen,
                &k,
                sch,
                scl,
                logn,
            );
        }

        let new_maxbl_fg = scale_k + maxbl_fg + 10;
        if new_maxbl_fg < maxbl_fg_current {
            maxbl_fg_current = new_maxbl_fg;
            if (fglen as i32) * 31 >= maxbl_fg_current + 31 {
                fglen -= 1;
            }
        }

        if scale_k <= 0 {
            break;
        }
        scale_k -= 25;
        if scale_k < 0 {
            scale_k = 0;
        }
    }

    if fglen < slen {
        for u in 0..n {
            let sw = (ft[u * llen + fglen - 1] >> 30).wrapping_neg() >> 1;
            for v in fglen..slen {
                ft[u * llen + v] = sw;
            }
            let sw = (gt[u * llen + fglen - 1] >> 30).wrapping_neg() >> 1;
            for v in fglen..slen {
                gt[u * llen + v] = sw;
            }
        }
    }

    // Compress to slen words; output order: first all F rows, then all G.
    for u in 0..n {
        tmp[u * slen..u * slen + slen].copy_from_slice(&ft[u * llen..u * llen + slen]);
        tmp[(n + u) * slen..(n + u) * slen + slen].copy_from_slice(&gt[u * llen..u * llen + slen]);
    }
    true
}

/// Reference `solve_NTRU_binary_depth1`: the depth-1 lift, handled
/// specially: the lifted candidates are reduced modulo the `llen` large
/// primes, and the Babai reduction is a single pass done entirely in the
/// fpr (FFT) domain — k = round((F·adj(f) + G·adj(g))·invnorm(f, g)) —
/// before subtracting k·(f, g). Fails if the multiplier leaves
/// ±(2^63 − 1).
fn solve_ntru_binary_depth1(logn_top: u32, f: &[i8], g: &[i8], tmp: &mut [u32]) -> bool {
    let depth = 1usize;
    let logn = logn_top - 1;
    let n_top = 1usize << logn_top;
    let n = 1usize << logn;
    let hn = n >> 1;

    let slen = MAX_BL_SMALL[depth];
    let dlen = MAX_BL_SMALL[depth + 1];
    let llen = MAX_BL_LARGE[depth];

    // Fd/Gd from the deeper level.
    let fd = tmp[..dlen * hn].to_vec();
    let gd = tmp[dlen * hn..2 * dlen * hn].to_vec();

    // Ft/Gt: n ints of llen words.
    let mut ft = vec![0u32; n * llen];
    let mut gt = vec![0u32; n * llen];

    // Reduce Fd/Gd modulo llen primes.
    for u in 0..llen {
        let (p, _g, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        let rx = modp_rx(dlen as u32, p, p0i, r2);
        for v in 0..hn {
            let xs = &fd[v * dlen..v * dlen + dlen];
            let ys = &gd[v * dlen..v * dlen + dlen];
            ft[u + v * llen] = zint_mod_small_signed(xs, p, p0i, r2, rx);
            gt[u + v * llen] = zint_mod_small_signed(ys, p, p0i, r2, rx);
        }
    }

    let mut ft_gt = vec![0u32; 2 * n * llen];
    ft_gt[..n * llen].copy_from_slice(&ft);
    ft_gt[n * llen..].copy_from_slice(&gt);
    let mut ft = ft_gt[..n * llen].to_vec();
    let mut gt = ft_gt[n * llen..].to_vec();
    let mut fg = vec![0u32; 2 * n * slen];

    for u in 0..llen {
        let (p, g_gen, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);

        let mut gm = vec![0u32; n_top];
        let mut igm = vec![0u32; n_top];
        let mut fx = vec![0u32; n_top];
        let mut gx = vec![0u32; n_top];

        modp_mkgm2(&mut gm, &mut igm, logn_top, g_gen, p, p0i);

        for v in 0..n_top {
            fx[v] = modp_set(f[v] as i32, p);
            gx[v] = modp_set(g[v] as i32, p);
        }
        modp_ntt2(&mut fx, &gm, logn_top, p, p0i);
        modp_ntt2(&mut gx, &gm, logn_top, p, p0i);
        let mut e = logn_top;
        while e > logn {
            modp_poly_rec_res(&mut fx, e, p, p0i, r2);
            modp_poly_rec_res(&mut gx, e, p, p0i, r2);
            e -= 1;
        }

        // Compress tables to degree-n layout.
        let mut gm_n = gm[..n].to_vec();
        let mut igm_n = igm[..n].to_vec();
        fx.truncate(n);
        gx.truncate(n);

        let mut fp_ = vec![0u32; hn];
        let mut gp_ = vec![0u32; hn];
        for v in 0..hn {
            fp_[v] = ft[u + v * llen];
            gp_[v] = gt[u + v * llen];
        }
        modp_ntt2(&mut fp_, &gm_n, logn - 1, p, p0i);
        modp_ntt2(&mut gp_, &gm_n, logn - 1, p, p0i);

        for v in 0..hn {
            let fta = fx[v << 1];
            let ftb = fx[(v << 1) + 1];
            let gta = gx[v << 1];
            let gtb = gx[(v << 1) + 1];
            let mfp = modp_montymul(fp_[v], r2, p, p0i);
            let mgp = modp_montymul(gp_[v], r2, p, p0i);
            ft[u + v * (llen << 1)] = modp_montymul(gtb, mfp, p, p0i);
            ft[u + (v * 2 + 1) * llen] = modp_montymul(gta, mfp, p, p0i);
            gt[u + v * (llen << 1)] = modp_montymul(ftb, mgp, p, p0i);
            gt[u + (v * 2 + 1) * llen] = modp_montymul(fta, mgp, p, p0i);
        }
        modp_intt2_ext(&mut ft[u..], llen, &igm_n, logn, p, p0i);
        modp_intt2_ext(&mut gt[u..], llen, &igm_n, logn, p, p0i);

        if u < slen {
            modp_intt2(&mut fx, &igm_n, logn, p, p0i);
            modp_intt2(&mut gx, &igm_n, logn, p, p0i);
            for v in 0..n {
                fg[v * slen + u] = fx[v];
                fg[n * slen + v * slen + u] = gx[v];
            }
        }
        let _ = (&mut gm_n, &mut igm_n);
    }

    // CRT rebuild: F‖G then f‖g (matching the reference's single-call
    // layout where F and G, and f and g, are consecutive).
    ft_gt[..n * llen].copy_from_slice(&ft);
    ft_gt[n * llen..].copy_from_slice(&gt);
    {
        let mut scratch = vec![0u32; llen.max(1)];
        let mut ftgt = ft_gt.clone();
        zint_rebuild_crt(&mut ftgt, llen, llen, n << 1, true, &mut scratch);
        ft_gt.copy_from_slice(&ftgt);
    }
    {
        let mut scratch = vec![0u32; slen.max(1)];
        zint_rebuild_crt(&mut fg, slen, slen, n << 1, true, &mut scratch);
    }

    // Babai reduction (single pass, fpr domain).
    let mut rt1 = vec![0u64; n];
    let mut rt2 = vec![0u64; n];
    let mut rt3 = vec![0u64; n];
    let mut rt4 = vec![0u64; n];
    poly_big_to_fp(&mut rt1, &ft_gt[..n * llen], llen, llen, logn);
    poly_big_to_fp(&mut rt2, &ft_gt[n * llen..], llen, llen, logn);
    poly_big_to_fp(&mut rt3, &fg[..n * slen], slen, slen, logn);
    poly_big_to_fp(&mut rt4, &fg[n * slen..], slen, slen, logn);

    super::fft::fft(&mut rt1, logn);
    super::fft::fft(&mut rt2, logn);
    super::fft::fft(&mut rt3, logn);
    super::fft::fft(&mut rt4, logn);

    let mut rt5 = vec![0u64; n];
    let mut rt6 = vec![0u64; n];
    super::fft::poly_add_muladj_fft(&mut rt5, &rt1, &rt2, &rt3, &rt4, logn);
    super::fft::poly_invnorm2_fft(&mut rt6, &rt3, &rt4, logn);
    super::fft::poly_mul_autoadj_fft(&mut rt5, &rt6, logn);

    super::fft::ifft(&mut rt5, logn);
    {
        for u in 0..n {
            let z = rt5[u];
            if !fpr_lt(z, FPR_PTWO63M1) || !fpr_lt(FPR_MTWO63M1, z) {
                return false;
            }
            rt5[u] = fpr_of(fpr_rint(z));
        }
    }
    super::fft::fft(&mut rt5, logn);

    super::fft::poly_mul_fft(&mut rt3, &rt5, logn);
    super::fft::poly_mul_fft(&mut rt4, &rt5, logn);
    super::fft::poly_sub(&mut rt1, &rt3, logn);
    super::fft::poly_sub(&mut rt2, &rt4, logn);
    super::fft::ifft(&mut rt1, logn);
    super::fft::ifft(&mut rt2, logn);

    for u in 0..n {
        tmp[u] = fpr_rint(rt1[u]) as u32;
        tmp[n + u] = fpr_rint(rt2[u]) as u32;
    }
    true
}

/// Reference `solve_NTRU_binary_depth0`: final lift at the top level,
/// done modulo the single prime PRIMES[0]: build the full-degree
/// candidates from the depth-1 result, then one FFT round-trip computes
/// k = round((F·adj(f) + G·adj(g)) / (f·adj(f) + g·adj(g))) and F − k·f,
/// G − k·g are reduced back to signed small coefficients. The NTRU
/// equation itself is checked by the caller (`solve_ntru`).
fn solve_ntru_binary_depth0(logn: u32, f: &[i8], g: &[i8], tmp: &mut [u32]) -> bool {
    let n = 1usize << logn;
    let hn = n >> 1;

    let (p, g0, _s) = PRIMES[0];
    let p0i = modp_ninv31(p);
    let r2 = modp_r2(p, p0i);

    let mut fp_ = vec![0u32; hn];
    let mut gp_ = vec![0u32; hn];
    let mut ft = vec![0u32; n];
    let mut gt = vec![0u32; n];
    let mut gm = vec![0u32; n];
    let mut igm = vec![0u32; n];

    modp_mkgm2(&mut gm, &mut igm, logn, g0, p, p0i);

    for u in 0..hn {
        fp_[u] = modp_set(zint_one_to_plain(&tmp[u..]), p);
        gp_[u] = modp_set(zint_one_to_plain(&tmp[hn + u..]), p);
    }
    modp_ntt2(&mut fp_, &gm, logn - 1, p, p0i);
    modp_ntt2(&mut gp_, &gm, logn - 1, p, p0i);

    for u in 0..n {
        ft[u] = modp_set(f[u] as i32, p);
        gt[u] = modp_set(g[u] as i32, p);
    }
    modp_ntt2(&mut ft, &gm, logn, p, p0i);
    modp_ntt2(&mut gt, &gm, logn, p, p0i);

    let mut u = 0usize;
    while u < n {
        let fta = ft[u];
        let ftb = ft[u + 1];
        let gta = gt[u];
        let gtb = gt[u + 1];
        let mfp = modp_montymul(fp_[u >> 1], r2, p, p0i);
        let mgp = modp_montymul(gp_[u >> 1], r2, p, p0i);
        ft[u] = modp_montymul(gtb, mfp, p, p0i);
        ft[u + 1] = modp_montymul(gta, mfp, p, p0i);
        gt[u] = modp_montymul(ftb, mgp, p, p0i);
        gt[u + 1] = modp_montymul(fta, mgp, p, p0i);
        u += 2;
    }
    modp_intt2(&mut ft, &igm, logn, p, p0i);
    modp_intt2(&mut gt, &igm, logn, p, p0i);

    // F and G (normal domain) — rename for the Babai step.
    let mut f_ntt = ft.clone();
    let mut g_ntt = gt.clone();

    // F*adj(f)+G*adj(g) in t1; f*adj(f)+g*adj(g) in t2 (mod p, NTT).
    let mut t1 = vec![0u32; n];
    let mut t2 = vec![0u32; n];
    let mut t4 = vec![0u32; n];
    let mut t5 = vec![0u32; n];
    let mut t1gm = vec![0u32; n];
    let mut t2gm = vec![0u32; n];

    modp_mkgm2(&mut t1gm, &mut t2gm, logn, g0, p, p0i);
    modp_ntt2(&mut f_ntt, &t1gm, logn, p, p0i);
    modp_ntt2(&mut g_ntt, &t1gm, logn, p, p0i);

    t4[0] = modp_set(f[0] as i32, p);
    t5[0] = t4[0];
    for u in 1..n {
        t4[u] = modp_set(f[u] as i32, p);
        t5[n - u] = modp_set(-(f[u] as i32), p);
    }
    modp_ntt2(&mut t4, &t1gm, logn, p, p0i);
    modp_ntt2(&mut t5, &t1gm, logn, p, p0i);
    for u in 0..n {
        let w = modp_montymul(t5[u], r2, p, p0i);
        t2[u] = modp_montymul(w, f_ntt[u], p, p0i);
        t1[u] = modp_montymul(w, t4[u], p, p0i);
    }

    t4[0] = modp_set(g[0] as i32, p);
    t5[0] = t4[0];
    for u in 1..n {
        t4[u] = modp_set(g[u] as i32, p);
        t5[n - u] = modp_set(-(g[u] as i32), p);
    }
    modp_ntt2(&mut t4, &t1gm, logn, p, p0i);
    modp_ntt2(&mut t5, &t1gm, logn, p, p0i);
    for u in 0..n {
        let w = modp_montymul(t5[u], r2, p, p0i);
        t2[u] = modp_add(t2[u], modp_montymul(w, g_ntt[u], p, p0i), p);
        t1[u] = modp_add(t1[u], modp_montymul(w, t4[u], p, p0i), p);
    }

    modp_mkgm2(&mut t1gm, &mut t4, logn, g0, p, p0i);
    modp_intt2(&mut t2, &t4, logn, p, p0i);
    modp_intt2(&mut t1, &t4, logn, p, p0i);
    // t2 holds F·adj(f)+G·adj(g); t1 holds f·adj(f)+g·adj(g).
    // Normalize both around zero (reference: t1 ← norm(t2), t2 ← norm(t3)).
    for u in 0..n {
        let fg_sum = modp_norm(t2[u], p) as u32;
        let ff_sum = modp_norm(t1[u], p) as u32;
        t1[u] = fg_sum;
        t2[u] = ff_sum;
    }

    // FFT-based rounded division: k = round(t1 / t2).
    let mut rt3 = vec![0u64; n];
    for u in 0..n {
        rt3[u] = fpr_of(t2[u] as i32 as i64);
    }
    super::fft::fft(&mut rt3, logn);
    let mut rt2f = vec![0u64; hn];
    rt2f.copy_from_slice(&rt3[..hn]);
    let mut rt3b = vec![0u64; n];
    for u in 0..n {
        rt3b[u] = fpr_of(t1[u] as i32 as i64);
    }
    super::fft::fft(&mut rt3b, logn);
    super::fft::poly_div_autoadj_fft(&mut rt3b, &rt2f, logn);
    super::fft::ifft(&mut rt3b, logn);
    for u in 0..n {
        t1[u] = modp_set(fpr_rint(rt3b[u]) as i32, p);
    }

    // F − k·f and G − k·g.
    let mut t2gm2 = vec![0u32; n];
    let mut t3gm2 = vec![0u32; n];
    let mut t4b = vec![0u32; n];
    let mut t5b = vec![0u32; n];
    modp_mkgm2(&mut t2gm2, &mut t3gm2, logn, g0, p, p0i);
    for u in 0..n {
        t4b[u] = modp_set(f[u] as i32, p);
        t5b[u] = modp_set(g[u] as i32, p);
    }
    modp_ntt2(&mut t1, &t2gm2, logn, p, p0i);
    modp_ntt2(&mut t4b, &t2gm2, logn, p, p0i);
    modp_ntt2(&mut t5b, &t2gm2, logn, p, p0i);
    for u in 0..n {
        let kw = modp_montymul(t1[u], r2, p, p0i);
        f_ntt[u] = modp_sub(f_ntt[u], modp_montymul(kw, t4b[u], p, p0i), p);
        g_ntt[u] = modp_sub(g_ntt[u], modp_montymul(kw, t5b[u], p, p0i), p);
    }
    modp_intt2(&mut f_ntt, &t3gm2, logn, p, p0i);
    modp_intt2(&mut g_ntt, &t3gm2, logn, p, p0i);
    for u in 0..n {
        f_ntt[u] = modp_norm(f_ntt[u], p) as u32;
        g_ntt[u] = modp_norm(g_ntt[u], p) as u32;
    }

    tmp[..n].copy_from_slice(&f_ntt);
    tmp[n..2 * n].copy_from_slice(&g_ntt);
    true
}

/// Reference `solve_NTRU`: solve f·G − g·F = q mod (X^n + 1) for the
/// small polynomials (F, G) given small (f, g): descend to the deepest
/// level (resultants + Bézout), lift back up (intermediate levels, then
/// the two binary levels), convert to i8 within ±lim and verify the NTRU
/// equation mod PRIMES[0] before accepting.
#[allow(clippy::too_many_arguments)]
pub fn solve_ntru(
    logn: u32,
    big_f: &mut [i8],
    big_g: &mut [i8],
    f: &[i8],
    g: &[i8],
    lim: i32,
    tmp: &mut [u32],
) -> bool {
    let n = 1usize << logn;

    if !solve_ntru_deepest(logn, f, g, tmp) {
        return false;
    }

    if logn <= 2 {
        let mut depth = logn as usize;
        while depth > 0 {
            depth -= 1;
            if !solve_ntru_intermediate(logn, f, g, depth, tmp) {
                return false;
            }
        }
    } else {
        let mut depth = logn as usize;
        while depth > 2 {
            depth -= 1;
            if !solve_ntru_intermediate(logn, f, g, depth, tmp) {
                return false;
            }
        }
        if !solve_ntru_binary_depth1(logn, f, g, tmp) {
            return false;
        }
        if !solve_ntru_binary_depth0(logn, f, g, tmp) {
            return false;
        }
    }

    let mut big_f_v = vec![0i8; n];
    let mut big_g_v = vec![0i8; n];
    if !poly_big_to_small(&mut big_f_v, &tmp[..n], lim, logn)
        || !poly_big_to_small(&mut big_g_v, &tmp[n..2 * n], lim, logn)
    {
        return false;
    }

    // Verify f·G − g·F = q mod phi mod p.
    let (p, g0, _s) = PRIMES[0];
    let p0i = modp_ninv31(p);
    let mut gm = vec![0u32; n];
    let mut g_t = vec![0u32; n];
    let mut f_t = vec![0u32; n];
    let mut f_t2 = vec![0u32; n];
    let mut g_t2 = vec![0u32; n];
    modp_mkgm2(&mut gm, &mut g_t, logn, g0, p, p0i);
    for u in 0..n {
        g_t[u] = modp_set(big_g_v[u] as i32, p);
    }
    for u in 0..n {
        f_t[u] = modp_set(f[u] as i32, p);
        g_t2[u] = modp_set(g[u] as i32, p);
        f_t2[u] = modp_set(big_f_v[u] as i32, p);
    }
    modp_ntt2(&mut f_t, &gm, logn, p, p0i);
    modp_ntt2(&mut g_t2, &gm, logn, p, p0i);
    modp_ntt2(&mut f_t2, &gm, logn, p, p0i);
    modp_ntt2(&mut g_t, &gm, logn, p, p0i);
    let r = modp_montymul(12289, 1, p, p0i);
    for u in 0..n {
        let z = modp_sub(
            modp_montymul(f_t[u], g_t[u], p, p0i),
            modp_montymul(g_t2[u], f_t2[u], p, p0i),
            p,
        );
        if z != r {
            return false;
        }
    }
    big_f.copy_from_slice(&big_f_v);
    big_g.copy_from_slice(&big_g_v);
    true
}

// ====================================================================
// Gaussian key generation.
// ====================================================================

/// Reference `gauss_1024_12289` table: 27 decreasing 63-bit thresholds of
/// the reference's discrete-Gaussian distribution used for f, g.
const GAUSS_1024_12289: [u64; 27] = [
    1283868770400643928,
    6416574995475331444,
    4078260278032692663,
    2353523259288686585,
    1227179971273316331,
    575931623374121527,
    242543240509105209,
    91437049221049666,
    30799446349977173,
    9255276791179340,
    2478152334826140,
    590642893610164,
    125206034929641,
    23590435911403,
    3948334035941,
    586753615614,
    77391054539,
    9056793210,
    940121950,
    86539696,
    7062824,
    510971,
    32764,
    1862,
    94,
    4,
    0,
];

/// Draw one 64-bit little-endian word from the hash-based RNG.
fn get_rng_u64(rng: &mut super::common::InnerShake256) -> u64 {
    let mut tmp = [0u8; 8];
    rng.extract(&mut tmp);
    u64::from_le_bytes(tmp)
}

/// Reference `mkgauss`: one Gaussian-centered integer per call. Each
/// component draw takes a sign bit plus a 63-bit value scanned
/// (branchlessly) against the decreasing `GAUSS_1024_12289` thresholds;
/// for logn < 10, 2^(10−logn) draws are summed so the variance matches
/// the per-degree keygen distribution.
fn mkgauss(rng: &mut super::common::InnerShake256, logn: u32) -> i32 {
    let g = 1usize << (10 - logn);
    let mut val: i32 = 0;
    for _ in 0..g {
        let mut r = get_rng_u64(rng);
        let neg = (r >> 63) as u32;
        r &= !(1u64 << 63);
        let mut f = ((r.wrapping_sub(GAUSS_1024_12289[0])) >> 63) as u32;

        let mut v: u32 = 0;
        let mut r2 = get_rng_u64(rng);
        r2 &= !(1u64 << 63);
        for k in 1..GAUSS_1024_12289.len() {
            let t = (((r2.wrapping_sub(GAUSS_1024_12289[k])) >> 63) as u32) ^ 1;
            v |= (k as u32) & -((t & (f ^ 1)) as i32) as u32;
            f |= t;
        }

        v = (v ^ neg.wrapping_neg()).wrapping_add(neg);
        val += v as i32;
    }
    val
}

/// Reference `poly_small_mkgauss`.
fn poly_small_mkgauss(rng: &mut super::common::InnerShake256, f: &mut [i8], logn: u32) {
    let n = 1usize << logn;
    let mut mod2: u32 = 0;
    for u in 0..n {
        let s = loop {
            let s = mkgauss(rng, logn);
            if !(-127..=127).contains(&s) {
                continue;
            }
            if u == n - 1 {
                if (mod2 ^ ((s & 1) as u32)) == 0 {
                    continue;
                }
            } else {
                mod2 ^= (s & 1) as u32;
            }
            break s;
        };
        f[u] = s as i8;
    }
}

/// Reference `poly_small_sqnorm`.
fn poly_small_sqnorm(f: &[i8], logn: u32) -> u32 {
    let n = 1usize << logn;
    let mut s: u32 = 0;
    let mut ng: u32 = 0;
    for &z in f.iter().take(n) {
        let zi = z as i32;
        s = s.wrapping_add((zi * zi) as u32);
        ng |= s;
    }
    s | (ng >> 31).wrapping_neg()
}

/// Reference `poly_small_to_fp`.
fn poly_small_to_fp(x: &mut [Fpr], f: &[i8], logn: u32) {
    let n = 1usize << logn;
    for u in 0..n {
        x[u] = fpr_of(f[u] as i64);
    }
}

/// Reference `keygen(rng, f, g, F, G=NULL, h, logn, tmp)`: G is recomputed
/// at signing time, so it is not returned.
pub fn keygen(
    rng: &mut super::common::InnerShake256,
    f: &mut [i8],
    g: &mut [i8],
    big_f: &mut [i8],
    h: &mut [u16],
    logn: u32,
) {
    let n = 1usize << logn;

    loop {
        poly_small_mkgauss(rng, f, logn);
        poly_small_mkgauss(rng, g, logn);

        let lim = 1i32 << (super::codec::MAX_FG_BITS[logn as usize] - 1);
        let mut ok = true;
        for u in 0..n {
            if f[u] as i32 >= lim
                || f[u] as i32 <= -lim
                || g[u] as i32 >= lim
                || g[u] as i32 <= -lim
            {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }

        // Reject when ‖(f, g)‖² is too large (reference bound: 16823);
        // `norm` saturates on u32 overflow like the other norm helpers.
        let normf = poly_small_sqnorm(f, logn);
        let normg = poly_small_sqnorm(g, logn);
        let norm = (normf.wrapping_add(normg)) | ((normf | normg) >> 31).wrapping_neg();
        if norm >= 16823 {
            continue;
        }

        // Orthogonalized vector norm bound: per FFT point compute
        // q²·(|adj(f)|² + |adj(g)|²)/(|f|² + |g|²); the sum (bnorm) is
        // the reference's "orthogonalized norm" of the scaled basis and
        // bounds the size of the F, G that solve_ntru will produce.
        let mut rt1 = vec![0u64; n];
        let mut rt2 = vec![0u64; n];
        let mut rt3 = vec![0u64; n];
        poly_small_to_fp(&mut rt1, f, logn);
        poly_small_to_fp(&mut rt2, g, logn);
        super::fft::fft(&mut rt1, logn);
        super::fft::fft(&mut rt2, logn);
        super::fft::poly_invnorm2_fft(&mut rt3, &rt1, &rt2, logn);
        super::fft::poly_adj_fft(&mut rt1, logn);
        super::fft::poly_adj_fft(&mut rt2, logn);
        super::fft::poly_mulconst(&mut rt1, FPR_Q, logn);
        super::fft::poly_mulconst(&mut rt2, FPR_Q, logn);
        super::fft::poly_mul_autoadj_fft(&mut rt1, &rt3, logn);
        super::fft::poly_mul_autoadj_fft(&mut rt2, &rt3, logn);
        super::fft::ifft(&mut rt1, logn);
        super::fft::ifft(&mut rt2, logn);
        let mut bnorm = FPR_ZERO;
        for u in 0..n {
            bnorm = fpr_add(bnorm, fpr_sqr(rt1[u]));
            bnorm = fpr_add(bnorm, fpr_sqr(rt2[u]));
        }
        if !fpr_lt(bnorm, FPR_BNORM_MAX) {
            continue;
        }

        // h = g/f mod phi mod q.
        if !super::mq::compute_public(h, f, g, logn) {
            continue;
        }

        // Solve the NTRU equation for F (and G).
        let lim = (1i32 << (super::codec::MAX_BIG_FG_BITS[logn as usize] - 1)) - 1;
        let mut tmp = vec![0u32; FALCON_KEYGEN_TMP_WORDS[logn as usize]];
        let mut g_tmp = vec![0i8; n];
        if !solve_ntru(logn, big_f, &mut g_tmp, f, g, lim, &mut tmp) {
            continue;
        }
        break;
    }
}

/// Temporary-buffer size per logn, in 31-bit words (the reference's
/// FALCON_KEYGEN_TEMP_* byte counts divided by 4).
const FALCON_KEYGEN_TMP_WORDS: [usize; 11] = [0, 17, 34, 28, 56, 112, 224, 448, 896, 1792, 3584];
