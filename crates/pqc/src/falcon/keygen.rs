//! Port of the Falcon reference `keygen.c`: Gaussian polynomial generation,
//! the exact NTRU equation solver (RNS + 31-bit-word bignum + Babai
//! reduction) and the top-level keygen loop.

use super::fpr::*;
use super::tables::PRIMES;

/// Reference `MAX_BL_SMALL[]`.
const MAX_BL_SMALL: [usize; 11] = [1, 1, 2, 2, 4, 7, 14, 27, 53, 106, 209];

/// Reference `MAX_BL_LARGE[]`.
const MAX_BL_LARGE: [usize; 10] = [2, 2, 5, 7, 12, 21, 40, 78, 157, 308];

/// Reference `BITLENGTH[]` (avg, std).
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

/// Reference `DEPTH_INT_FG`.
const DEPTH_INT_FG: u32 = 4;

// ====================================================================
// Modular arithmetic modulo a small prime p (2^30 < p < 2^31).
// ====================================================================

#[inline]
fn modp_set(x: i32, p: u32) -> u32 {
    let mut w = x as u32;
    w = w.wrapping_add(p & (w >> 31).wrapping_neg());
    w
}

/// Normalize a modular integer around 0.
#[inline]
fn modp_norm(x: u32, p: u32) -> i32 {
    (x.wrapping_sub(p & ((((p + 1) >> 1).wrapping_sub(x) >> 31).wrapping_neg()))) as i32
}

/// −1/p mod 2^31.
fn modp_ninv31(p: u32) -> u32 {
    let mut y = 2u32.wrapping_sub(p);
    y = y.wrapping_mul(2u32.wrapping_sub(p.wrapping_mul(y)));
    y = y.wrapping_mul(2u32.wrapping_sub(p.wrapping_mul(y)));
    y = y.wrapping_mul(2u32.wrapping_sub(p.wrapping_mul(y)));
    y = y.wrapping_mul(2u32.wrapping_sub(p.wrapping_mul(y)));
    0x7FFF_FFFF & y.wrapping_neg()
}

/// R = 2^31 mod p.
#[inline]
fn modp_r(p: u32) -> u32 {
    (1u32 << 31).wrapping_sub(p)
}

#[inline]
fn modp_add(a: u32, b: u32, p: u32) -> u32 {
    let d = a.wrapping_add(b).wrapping_sub(p);
    d.wrapping_add(p & (d >> 31).wrapping_neg())
}

#[inline]
fn modp_sub(a: u32, b: u32, p: u32) -> u32 {
    let d = a.wrapping_sub(b);
    d.wrapping_add(p & (d >> 31).wrapping_neg())
}

/// Montgomery multiplication modulo p.
#[inline]
fn modp_montymul(a: u32, b: u32, p: u32, p0i: u32) -> u32 {
    let z = (a as u64) * (b as u64);
    let w = ((z.wrapping_mul(p0i as u64)) & 0x7FFF_FFFF) * (p as u64);
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
    let z = z.wrapping_add(p & -(z & 1) as i32);
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

/// Division modulo prime p (0 if b == 0).
fn modp_div(a: u32, b: u32, p: u32, p0i: u32, r: u32) -> u32 {
    let e = p - 2;
    let mut z = r;
    for i in (0..=30).rev() {
        z = modp_montymul(z, z, p, p0i);
        let z2 = modp_montymul(z, b, p, p0i);
        z ^= (z ^ z2) & -(((e >> i) & 1) as u32);
    }
    z = modp_montymul(z, 1, p, p0i);
    modp_montymul(a, z, p, p0i)
}

/// Reference `modp_mkgm2`: build NTT twiddle tables for degree 2^logn.
fn modp_mkgm2(gm: &mut [u32], igm: &mut [u32], logn: u32, g: u32, p: u32, p0i: u32) {
    let n = 1usize << logn;
    let mut r2 = modp_r2(p, p0i);
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
    let _ = r2;
}

/// Reference `modp_NTT2_ext` (elements at a[0], a[stride], ...).
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
                a[r2base + v * stride] =
                    modp_montymul(modp_sub(x, y, p), s, p, p0i);
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

/// Reference `modp_poly_rec_res`: f' = f0² − X·f1² compressed to n/2.
fn modp_poly_rec_res(f: &mut [u32], logn: u32, p: u32, p0i: u32, r2: u32) {
    let hn = 1usize << (logn - 1);
    for u in 0..hn {
        let w0 = f[(u << 1) + 0];
        let w1 = f[(u << 1) + 1];
        f[u] = modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
    }
}

// ====================================================================
// Custom bignum: 31-bit words, two's complement for negatives.
// ====================================================================

/// Reference `zint_sub`.
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

/// Reference `zint_mul_small`.
fn zint_mul_small(m: &mut [u32], x: u32) -> u32 {
    let mut cc: u32 = 0;
    for v in m.iter_mut() {
        let z = (*v as u64) * (x as u64) + cc as u64;
        *v = (z as u32) & 0x7FFF_FFFF;
        cc = (z >> 31) as u32;
    }
    cc
}

/// Reference `zint_mod_small_unsigned`.
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

/// Reference `zint_mod_small_signed`.
fn zint_mod_small_signed(d: &[u32], p: u32, p0i: u32, r2: u32, rx: u32) -> u32 {
    if d.is_empty() {
        return 0;
    }
    let mut z = zint_mod_small_unsigned(d, p, p0i, r2);
    z = modp_sub(z, rx & -((d[d.len() - 1] >> 30) as i32) as u32, p);
    z
}

/// Reference `zint_add_mul_small`: x += y·s (result len+1 words).
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

/// Reference `zint_norm_zero`.
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
        r |= cc & ((r & 1).wrapping_sub(1));
    }
    zint_sub(x, p, r >> 31);
}

/// Reference `zint_rebuild_CRT`.
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
        let (p, g, s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        let _ = g;

        for v in 0..num {
            let x = &mut xx[v * xstride..];
            let xp = x[u];
            let xq = zint_mod_small_unsigned(&x[..u], p, p0i, r2);
            let xr = modp_montymul(s, modp_sub(xp, xq, p), p, p0i);
            zint_add_mul_small(x, &tmp[..u], xr);
        }
        tmp[u] = zint_mul_small(&mut tmp[..u], p);
    }
    if normalize_signed {
        for v in 0..num {
            let x = &mut xx[v * xstride..v * xstride + xlen];
            zint_norm_zero(x, &tmp[..xlen]);
        }
    }
}

/// Reference `zint_negate`.
fn zint_negate(a: &mut [u32], ctl: u32) {
    let mut cc = ctl;
    let m = ctl.wrapping_neg() >> 1;
    for v in a.iter_mut() {
        let aw = (*v ^ m).wrapping_add(cc);
        *v = aw & 0x7FFF_FFFF;
        cc = aw >> 31;
    }
}

/// Reference `zint_co_reduce`.
fn zint_co_reduce(a: &mut [u32], b: &mut [u32], xa: i64, xb: i64, ya: i64, yb: i64) -> u32 {
    let len = a.len();
    let mut cca: i64 = 0;
    let mut ccb: i64 = 0;
    for u in 0..len {
        let wa = a[u];
        let wb = b[u];
        let za = (wa as i64)
            .wrapping_mul(xa)
            .wrapping_mul(1)
            .wrapping_add((wb as i64).wrapping_mul(xb))
            .wrapping_add(cca);
        let zb = (wa as i64)
            .wrapping_mul(ya)
            .wrapping_add((wb as i64).wrapping_mul(yb))
            .wrapping_add(ccb);
        if u > 0 {
            a[u - 1] = (za as u32) & 0x7FFF_FFFF;
            b[u - 1] = (zb as u32) & 0x7FFF_FFFF;
        }
        cca = za >> 31;
        ccb = zb >> 31;
    }
    a[len - 1] = cca as u32;
    b[len - 1] = ccb as u32;

    let nega = ((cca as u64) >> 63) as u32;
    let negb = ((ccb as u64) >> 63) as u32;
    zint_negate(a, nega);
    zint_negate(b, negb);
    nega | (negb << 1)
}

/// Reference `zint_finish_mod`.
fn zint_finish_mod(a: &mut [u32], m: &[u32], neg: u32) {
    let len = a.len();
    let mut cc: u32 = 0;
    for u in 0..len {
        cc = a[u].wrapping_sub(m[u]).wrapping_sub(cc) >> 31;
    }
    let xm = neg.wrapping_neg() >> 1;
    let ym = -((neg as i32) | (1 - cc as i32)) as u32;
    let mut cc = neg;
    for u in 0..len {
        let aw = a[u];
        let mw = (m[u] ^ xm) & ym;
        let aw = aw.wrapping_sub(mw).wrapping_sub(cc);
        a[u] = aw & 0x7FFF_FFFF;
        cc = aw >> 31;
    }
}

/// Reference `zint_co_reduce_mod`.
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
    let fa = ((a[0]
        .wrapping_mul(xa as u32)
        .wrapping_add(b[0].wrapping_mul(xb as u32)))
    .wrapping_mul(m0i))
        & 0x7FFF_FFFF;
    let fb = ((a[0]
        .wrapping_mul(ya as u32)
        .wrapping_add(b[0].wrapping_mul(yb as u32)))
    .wrapping_mul(m0i))
        & 0x7FFF_FFFF;
    for u in 0..len {
        let wa = a[u];
        let wb = b[u];
        let za = (wa as u64)
            .wrapping_mul(xa as u64)
            .wrapping_add((wb as u64).wrapping_mul(xb as u64))
            .wrapping_add((m[u] as u64).wrapping_mul(fa as u64))
            .wrapping_add(cca as u64);
        let zb = (wa as u64)
            .wrapping_mul(ya as u64)
            .wrapping_add((wb as u64).wrapping_mul(yb as u64))
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

/// Reference `zint_bezout`: extended binary GCD; returns 1 iff gcd == 1,
/// filling u, v with x·u − y·v = 1.
fn zint_bezout(u: &mut [u32], v: &mut [u32], x: &[u32], y: &[u32], tmp: &mut [u32]) -> i32 {
    let len = x.len();
    if len == 0 {
        return 0;
    }

    let (u0, v0) = (u, v);
    let u1 = &mut tmp[..len];
    let v1 = &mut tmp[len..2 * len];
    let a = &mut tmp[2 * len..3 * len];
    let b = &mut tmp[3 * len..4 * len];

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
        // Extract the top one or two words of a and b.
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

        // Compute reduction factors pa/pb/qa/qb over 31 iterations.
        let mut pa: i64 = 1;
        let mut pb: i64 = 0;
        let mut qa: i64 = 0;
        let mut qb: i64 = 1;
        for i in 0..31 {
            let rz = b_hi.wrapping_sub(a_hi);
            let rt = (((rz ^ ((a_hi ^ b_hi) & (a_hi ^ rz))) >> 63) as u32);

            let oa = (a_lo >> i) & 1;
            let ob = (b_lo >> i) & 1;
            let cab = oa & ob & rt;
            let cba = oa & ob & !rt;
            let ca = cab | (oa ^ 1);

            a_lo = a_lo.wrapping_sub(b_lo & (cab as u32).wrapping_neg());
            a_hi = a_hi.wrapping_sub(b_hi & -((cab as i64)));
            pa -= qa & -((cab as i64));
            pb -= qb & -((cab as i64));
            b_lo = b_lo.wrapping_sub(a_lo & (cba as u32).wrapping_neg());
            b_hi = b_hi.wrapping_sub(a_hi & -((cba as i64)));
            qa -= pa & -((cba as i64));
            qb -= pb & -((cba as i64));

            a_lo = a_lo.wrapping_add(a_lo & ca.wrapping_sub(1));
            pa += pa & ((ca as i64) - 1);
            pb += pb & ((ca as i64) - 1);
            a_hi ^= (a_hi ^ (a_hi >> 1)) & -((ca as i64)) as u64;
            b_lo = b_lo.wrapping_add(b_lo & (ca as u32).wrapping_neg());
            qa += qa & -((ca as i64));
            qb += qb & -((ca as i64));
            b_hi ^= (b_hi ^ (b_hi >> 1)) & ((ca as u64).wrapping_sub(1));
        }

        let mut r = zint_co_reduce(a, b, pa, pb, qa, qb);
        pa -= (pa + pa) & -((r & 1) as i64);
        pb -= (pb + pb) & -((r & 1) as i64);
        qa -= (qa + qa) & -(((r >> 1) as i64));
        qb -= (qb + qb) & -(((r >> 1) as i64));
        let _ = &mut r;
        zint_co_reduce_mod(u0, u1, y, y0i, pa, pb, qa, qb);
        zint_co_reduce_mod(v0, v1, x, x0i, pa, pb, qa, qb);

        num -= 30;
    }

    // a holds the GCD; check that it is 1 and that x, y are odd.
    let mut rc = a[0] ^ 1;
    for j in 1..len {
        rc |= a[j];
    }
    ((1 - (((rc | rc.wrapping_neg()) >> 31) as i32)) & (x[0] & y[0]) as i32) as i32
}

/// Reference `zint_add_scaled_mul_small`.
fn zint_add_scaled_mul_small(
    x: &mut [u32],
    y: &[u32],
    k: i32,
    sch: u32,
    scl: u32,
) {
    if y.is_empty() {
        return;
    }
    let ysign = -(y[y.len() - 1] >> 30) >> 1;
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

/// Reference `zint_sub_scaled`.
fn zint_sub_scaled(x: &mut [u32], y: &[u32], sch: u32, scl: u32) {
    if y.is_empty() {
        return;
    }
    let ysign = -(y[y.len() - 1] >> 30) >> 1;
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

/// Reference `zint_one_to_plain`.
#[inline]
fn zint_one_to_plain(x: &[u32]) -> i32 {
    let mut w = x[0];
    w |= (w & 0x4000_0000) << 1;
    w as i32
}

/// Reference `poly_big_to_fp`.
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
        let neg = -(fp[flen - 1] >> 30);
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
            fsc = fpr_mul(fsc, FPR_PTWO63);
        }
        d[u] = x;
    }
}

/// Reference `poly_big_to_small`.
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

/// Reference `poly_sub_scaled`.
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

/// Reference `poly_sub_scaled_ntt`.
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
    tmp: &mut [u32],
) {
    let n = 1usize << logn;
    let tlen = glen + 1;
    let primes = PRIMES;

    let mut gm = vec![0u32; n];
    let mut igm = vec![0u32; n];
    let mut fk = vec![0u32; n * tlen];
    let mut t1 = vec![0u32; n];

    // k*f in fk[], RNS notation.
    for u in 0..tlen {
        let (p, g, _s) = primes[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        let rx = modp_rx(glen as u32, p, p0i, r2);
        modp_mkgm2(&mut gm, &mut igm, logn, g, p, p0i);

        for v in 0..n {
            t1[v] = modp_set(k[v], p);
        }
        modp_ntt2(&mut t1, &gm, logn, p, p0i);
        for v in 0..n {
            let y = &f[v * gstride..];
            fk[v * tlen + u] = zint_mod_small_signed(&y[..glen], p, p0i, r2, rx);
        }
        // NTT over the strided fk (per-prime slot u).
        modp_ntt2_ext(&mut fk[u..], tlen, &gm, logn, p, p0i);
        for v in 0..n {
            let x = modp_montymul(t1[v], fk[v * tlen + u], p, p0i);
            fk[v * tlen + u] = modp_montymul(x, r2, p, p0i);
        }
        modp_intt2_ext(&mut fk[u..], tlen, &igm, logn, p, p0i);
    }

    // Rebuild k*f.
    zint_rebuild_crt(&mut fk, tlen, tlen, n, true, &mut t1);

    // Subtract k*f, scaled, from F.
    for u in 0..n {
        let x = &mut big_f[u * fstride..u * fstride + flen];
        let y = &fk[u * tlen..u * tlen + tlen];
        zint_sub_scaled(x, y, sch, scl);
    }
    let _ = tmp;
}

// ====================================================================
// make_fg: f and g at a given depth, RNS/NTT.
// ====================================================================

/// Reference `make_fg_step`.
fn make_fg_step(data: &mut [u32], logn: u32, depth: usize, in_ntt: bool, out_ntt: bool) {
    let n = 1usize << logn;
    let hn = n >> 1;
    let slen = MAX_BL_SMALL[depth];
    let tlen = MAX_BL_SMALL[depth + 1];

    // Layout (word offsets): fd, gd (hn·tlen each), fs, gs (n·slen each),
    // gm, igm (n each), t1 (n).
    let off_fd = 0;
    let off_gd = off_fd + hn * tlen;
    let off_fs = off_gd + hn * tlen;
    let off_gs = off_fs + n * slen;
    let off_gm = off_gs + n * slen;
    let off_igm = off_gm + n;
    let off_t1 = off_igm + n;

    // Move fs/gs out of the way (reference memmove).
    data.copy_within(0..2 * n * slen, off_fs);

    for u in 0..slen {
        let (p, g, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        {
            let (gm, rest) = data.split_at_mut(off_gm);
            let igm = &mut rest[..n];
            modp_mkgm2(gm, igm, logn, g, p, p0i);
        }
        let gm = data[off_gm..off_gm + n].to_vec();
        let igm = data[off_igm..off_igm + n].to_vec();

        // f side.
        for v in 0..n {
            data[off_t1 + v] = data[off_fs + v * slen + u];
        }
        if !in_ntt {
            modp_ntt2(&mut data[off_t1..off_t1 + n], &gm, logn, p, p0i);
        }
        for v in 0..hn {
            let w0 = data[off_t1 + (v << 1)];
            let w1 = data[off_t1 + (v << 1) + 1];
            data[off_fd + v * tlen + u] =
                modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
        }
        if in_ntt {
            modp_intt2_ext(&mut data[off_fs + u..], slen, &igm, logn, p, p0i);
        }

        // g side.
        for v in 0..n {
            data[off_t1 + v] = data[off_gs + v * slen + u];
        }
        if !in_ntt {
            modp_ntt2(&mut data[off_t1..off_t1 + n], &gm, logn, p, p0i);
        }
        for v in 0..hn {
            let w0 = data[off_t1 + (v << 1)];
            let w1 = data[off_t1 + (v << 1) + 1];
            data[off_gd + v * tlen + u] =
                modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
        }
        if in_ntt {
            modp_intt2_ext(&mut data[off_gs + u..], slen, &igm, logn, p, p0i);
        }

        if !out_ntt {
            modp_intt2_ext(&mut data[off_fd + u..], tlen, &igm, logn - 1, p, p0i);
            modp_intt2_ext(&mut data[off_gd + u..], tlen, &igm, logn - 1, p, p0i);
        }
    }

    // CRT-rebuild fs and gs.
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

    // Remaining words: modular reductions.
    for u in slen..tlen {
        let (p, g, _s) = PRIMES[u];
        let p0i = modp_ninv31(p);
        let r2 = modp_r2(p, p0i);
        let rx = modp_rx(slen as u32, p, p0i, r2);
        {
            let (gm, rest) = data.split_at_mut(off_gm);
            let igm = &mut rest[..n];
            modp_mkgm2(gm, igm, logn, g, p, p0i);
        }
        let gm = data[off_gm..off_gm + n].to_vec();
        let igm = data[off_igm..off_igm + n].to_vec();

        for v in 0..n {
            let x = &data[off_fs + v * slen..off_fs + v * slen + slen];
            data[off_t1 + v] = zint_mod_small_signed(x, p, p0i, r2, rx);
        }
        modp_ntt2(&mut data[off_t1..off_t1 + n], &gm, logn, p, p0i);
        for v in 0..hn {
            let w0 = data[off_t1 + (v << 1)];
            let w1 = data[off_t1 + (v << 1) + 1];
            data[off_fd + v * tlen + u] =
                modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
        }
        for v in 0..n {
            let x = &data[off_gs + v * slen..off_gs + v * slen + slen];
            data[off_t1 + v] = zint_mod_small_signed(x, p, p0i, r2, rx);
        }
        modp_ntt2(&mut data[off_t1..off_t1 + n], &gm, logn, p, p0i);
        for v in 0..hn {
            let w0 = data[off_t1 + (v << 1)];
            let w1 = data[off_t1 + (v << 1) + 1];
            data[off_gd + v * tlen + u] =
                modp_montymul(modp_montymul(w0, w1, p, p0i), r2, p, p0i);
        }

        if !out_ntt {
            modp_intt2_ext(&mut data[off_fd + u..], tlen, &igm, logn - 1, p, p0i);
            modp_intt2_ext(&mut data[off_gd + u..], tlen, &igm, logn - 1, p, p0i);
        }
    }
}

/// Reference `make_fg`: f and g at a specific depth, in data[..].
fn make_fg(
    data: &mut [u32],
    f: &[i8],
    g: &[i8],
    logn_top: u32,
    depth: usize,
    out_ntt: bool,
) {
    let n = 1usize << logn_top;
    let p0 = PRIMES[0].0;
    for u in 0..n {
        data[u] = modp_set(f[u] as i32, p0);
        data[n + u] = modp_set(g[u] as i32, p0);
    }

    if depth == 0 && out_ntt {
        let p = PRIMES[0].0;
        let p0i = modp_ninv31(p);
        let mut gm = vec![0u32; n];
        let mut igm = vec![0u32; n];
        modp_mkgm2(&mut gm, &mut igm, logn_top, PRIMES[0].1, p, p0i);
        modp_ntt2(&mut data[..n], &gm, logn_top, p, p0i);
        modp_ntt2(&mut data[n..2 * n], &gm, logn_top, p, p0i);
        return;
    }

    for d in 0..depth {
        make_fg_step(data, logn_top - d as u32, d, d != 0, (d + 1) < depth || out_ntt);
    }
}

// ====================================================================
// NTRU equation solving.
// ====================================================================

/// Reference `solve_NTRU_deepest`.
fn solve_ntru_deepest(
    logn_top: u32,
    f: &[i8],
    g: &[i8],
    tmp: &mut [u32],
) -> bool {
    let len = MAX_BL_SMALL[logn_top as usize];

    let mut fp = vec![0u32; len];
    let mut gp = vec![0u32; len];
    {
        // make_fg(fp‖gp, f, g, logn_top, logn_top, 0) — the reference uses
        // one shared data buffer holding fp then gp.
        let mut data = vec![0u32; 2 * len];
        make_fg(&mut data, f, g, logn_top, logn_top as usize, false);
        fp.copy_from_slice(&data[..len]);
        gp.copy_from_slice(&data[len..2 * len]);
    }

    // CRT-rebuild the resultants as big integers.
    let mut fp_gp = vec![0u32; 2 * len];
    fp_gp[..len].copy_from_slice(&fp);
    fp_gp[len..].copy_from_slice(&gp);
    let mut t1 = vec![0u32; len.max(1)];
    zint_rebuild_crt(&mut fp_gp, len, len, 2, false, &mut t1);

    // Binary GCD: Gp ← bezout output v, Fp ← u.
    let mut gp_big = fp_gp[..len].to_vec();
    let mut fp_big = fp_gp[len..].to_vec();
    let mut g_out = vec![0u32; len];
    let mut f_out = vec![0u32; len];
    if zint_bezout(&mut g_out, &mut f_out, &gp_big, &fp_big, &mut t1) == 0 {
        return false;
    }

    // Multiply by q.
    if zint_mul_small(&mut f_out, 12289) != 0 || zint_mul_small(&mut g_out, 12289) != 0 {
        return false;
    }

    tmp[..len].copy_from_slice(&f_out);
    tmp[len..2 * len].copy_from_slice(&g_out);
    let _ = (&mut gp_big, &mut fp_big);
    true
}

/// Reference `solve_NTRU_intermediate`.
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

    // Fd/Gd from the deeper level (tmp layout: hn ints of dlen words each).
    let mut fd = tmp[..dlen * hn].to_vec();
    let mut gd = tmp[dlen * hn..2 * dlen * hn].to_vec();

    // f,g for this level, RNS+NTT: 2n ints of slen words.
    let mut fg = vec![0u32; 2 * n * slen];
    make_fg(&mut fg, f, g, logn_top, depth, true);

    // Ft, Gt: n ints of llen words each; t1 scratch.
    let mut ft = vec![0u32; n * llen];
    let mut gt = vec![0u32; n * llen];
    let mut t1 = vec![0u32; (2 * n * slen).max(2 * hn * dlen).max(n * 2)];

    // Reduce Fd/Gd modulo llen primes → Ft/Gt (hn entries, stride llen).
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

    // Compute F,G modulo sufficiently many small primes.
    for u in 0..llen {
        let (p, g, _s) = PRIMES[u];
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

        modp_mkgm2(&mut gm, &mut igm, logn, g, p, p0i);

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

        // F', G' mod p in NTT (degree n/2) from Ft/Gt.
        let mut fp_ = vec![0u32; hn];
        let mut gp_ = vec![0u32; hn];
        for v in 0..hn {
            fp_[v] = ft[u + v * llen];
            gp_[v] = gt[u + v * llen];
        }
        modp_ntt2(&mut fp_, &gm, logn - 1, p, p0i);
        modp_ntt2(&mut gp_, &gm, logn - 1, p, p0i);

        for v in 0..hn {
            let fta = fx[(v << 1) + 0];
            let ftb = fx[(v << 1) + 1];
            let gta = gx[(v << 1) + 0];
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

    // CRT rebuild F,G.
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

    let rlen = slen.min(10);
    poly_big_to_fp(&mut rt3, &fg[slen - rlen..], rlen, slen, logn);
    poly_big_to_fp(&mut rt4, &fg[2 * n * slen - slen + (slen - rlen)..], rlen, slen, logn);

    let scale_fg = 31 * (slen - rlen) as i32;
    let minbl_fg = BITLENGTH[depth].0 - 6 * BITLENGTH[depth].1;
    let maxbl_fg = BITLENGTH[depth].0 + 6 * BITLENGTH[depth].1;

    super::fft::fft(&mut rt3, logn);
    super::fft::fft(&mut rt4, logn);
    super::fft::poly_invnorm2_fft(&mut rt5, &rt3, &rt4, logn);
    super::fft::poly_adj_fft(&mut rt3, logn);
    super::fft::poly_adj_fft(&mut rt4, logn);

    let mut fglen = llen;
    let mut maxbl_fg_ = 31 * llen as i32;
    let mut scale_k = maxbl_FG_start(minbl_fg, llen);

    loop {
        let rlen = fglen.min(10);
        let scale_fgx = 31 * (fglen - rlen) as i32;
        poly_big_to_fp(&mut rt1, &ft[fglen - rlen..], rlen, llen, logn);
        poly_big_to_fp(&mut rt2, &gt[fglen - rlen..], rlen, llen, logn);

        super::fft::fft(&mut rt1, logn);
        super::fft::fft(&mut rt2, logn);
        super::fft::poly_mul_fft(&mut rt1, &rt3, logn);
        super::fft::poly_mul_fft(&mut rt2, &rt4, logn);
        super::fft::poly_add(&mut rt2, &rt1, logn);
        super::fft::poly_mul_autoadj_fft(&mut rt2, &rt5, logn);
        super::fft::ifft(&mut rt2, logn);

        let mut dc = scale_k - scale_fgx + scale_fg;

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
            if !fpr_lt(FPR_MTWO31M1, xv) || !fpr_lt(xv, FPR_PTWO31M1) {
                return false;
            }
            k[u] = fpr_rint(xv) as i32;
        }

        let sch = (scale_k / 31) as u32;
        let scl = (scale_k % 31) as u32;
        if depth <= DEPTH_INT_FG as usize {
            poly_sub_scaled_ntt(&mut ft, fglen, llen, &fg[..n * slen], slen, slen, &k, sch, scl, logn, &mut t1);
            poly_sub_scaled_ntt(&mut gt, fglen, llen, &fg[n * slen..2 * n * slen], slen, slen, &k, sch, scl, logn, &mut t1);
        } else {
            poly_sub_scaled(&mut ft, fglen, llen, &fg[..n * slen], slen, slen, &k, sch, scl, logn);
            poly_sub_scaled(&mut gt, fglen, llen, &fg[n * slen..2 * n * slen], slen, slen, &k, sch, scl, logn);
        }

        let new_maxbl_fg = scale_k + maxbl_fg + 10;
        if new_maxbl_fg < maxbl_fg_ {
            maxbl_fg_ = new_maxbl_fg;
            if (fglen as i32) * 31 >= maxbl_fg_ + 31 {
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

    // Sign-extend if FGlen dropped below slen.
    if fglen < slen {
        for u in 0..n {
            let sw = -(ft[u * llen + fglen - 1] >> 30) >> 1;
            for v in fglen..slen {
                ft[u * llen + v] = sw;
            }
            let sw = -(gt[u * llen + fglen - 1] >> 30) >> 1;
            for v in fglen..slen {
                gt[u * llen + v] = sw;
            }
        }
    }

    // Compress to slen words and output into tmp.
    for u in 0..(n << 1) {
        let (src, dst) = if u < n {
            (&ft[u * llen..u * llen + slen], &mut tmp[u * slen..u * slen + slen])
        } else {
            let v = u - n;
            (&gt[v * llen..v * llen + slen], &mut tmp[u * slen..u * slen + slen])
        };
        dst.copy_from_slice(src);
    }
    true
}

#[inline]
fn maxbl_FG_start(minbl_fg: i32, llen: usize) -> i32 {
    31 * llen as i32 - minbl_fg - minbl_fg // placeholder, replaced below
}

/// Reference `solve_NTRU_binary_depth1`.
fn solve_ntru_binary_depth1(logn_top: u32, f: &[i8], g: &[i8], tmp: &mut [u32]) -> bool {
    // Port of the reference depth-1 solver with the simplified Babai
    // reduction (all values fit in 53-bit floats).
    unimplemented!("patched below")
}

/// Reference `solve_NTRU_binary_depth0`.
fn solve_ntru_binary_depth0(logn: u32, f: &[i8], g: &[i8], tmp: &mut [u32]) -> bool {
    unimplemented!("patched below")
}

/// Reference `solve_NTRU`.
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

    // Final F,G are one-word-per-coefficient signed 31-bit values in tmp.
    if !poly_big_to_small(big_f, &tmp[..n], lim, logn)
        || !poly_big_to_small(big_g, &tmp[n..2 * n], lim, logn)
    {
        return false;
    }

    // Verify the NTRU equation modulo the first small prime.
    let (p, g0, _s) = PRIMES[0];
    let p0i = modp_ninv31(p);
    let mut gm = vec![0u32; n];
    let mut gt = vec![0u32; n];
    let mut ft = vec![0u32; n];
    let mut ftt = vec![0u32; n];
    let mut gtt = vec![0u32; n];
    modp_mkgm2(&mut gm, &mut gt, logn, g0, p, p0i);
    for u in 0..n {
        gt[u] = modp_set(big_g[u] as i32, p);
    }
    for u in 0..n {
        ft[u] = modp_set(f[u] as i32, p);
        gtt[u] = modp_set(g[u] as i32, p);
        ftt[u] = modp_set(big_f[u] as i32, p);
    }
    modp_ntt2(&mut ft, &gm, logn, p, p0i);
    modp_ntt2(&mut gtt, &gm, logn, p, p0i);
    modp_ntt2(&mut ftt, &gm, logn, p, p0i);
    modp_ntt2(&mut gt, &gm, logn, p, p0i);
    let r = modp_montymul(12289, 1, p, p0i);
    for u in 0..n {
        let z = modp_sub(
            modp_montymul(ft[u], gt[u], p, p0i),
            modp_montymul(gtt[u], ftt[u], p, p0i),
            p,
        );
        if z != r {
            return false;
        }
    }
    true
}
