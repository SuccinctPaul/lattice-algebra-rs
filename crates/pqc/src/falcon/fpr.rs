//! Port of the Falcon reference `fpr` soft-float layer (`fpr.h`/`fpr.c`,
//! falcon512int variant): IEEE-754 binary64 values carried in a `u64`,
//! manipulated with integer-only algorithms so that results are bit-identical
//! across platforms. Every function is a faithful transcription of the
//! round-3 reference code; the integer form is what makes the sampler
//! reproducible without relying on `f64` rounding configurations.

#![allow(clippy::too_many_arguments)]

use super::tables::{FPR_GM_TAB, FPR_P2_TAB};

pub type Fpr = u64;

// ------------------------------------------------------------------
// Constants (reference fpr.h values, already in encoded form).
// ------------------------------------------------------------------

pub const FPR_Q: Fpr = 4667981563525332992;
pub const FPR_INVERSE_OF_Q: Fpr = 4545632735260551042;
pub const FPR_INV_2SQRSIGMA0: Fpr = 4594603506513722306;
pub const FPR_INV_SIGMA: [Fpr; 11] = [
    0,
    4574611497772390042,
    4574501679055810265,
    4574396282908341804,
    4574245855758572086,
    4574103865040221165,
    4573969550563515544,
    4573842244705920822,
    4573721358406441454,
    4573606369665796042,
    4573496814039276259,
];
pub const FPR_SIGMA_MIN: [Fpr; 11] = [
    0,
    4607707126469777035,
    4607777455861499430,
    4607846828256951418,
    4607949175006100261,
    4608049571757433526,
    4608148125896792003,
    4608244935301382692,
    4608340089478362016,
    4608433670533905013,
    4608525754002622308,
];
pub const FPR_LOG2: Fpr = 4604418534313441775;
pub const FPR_INV_LOG2: Fpr = 4609176140021203710;
pub const FPR_BNORM_MAX: Fpr = 4670353323383631276;
pub const FPR_ZERO: Fpr = 0;
pub const FPR_ONE: Fpr = 4607182418800017408;
pub const FPR_TWO: Fpr = 4611686018427387904;
pub const FPR_ONEHALF: Fpr = 4602678819172646912;
pub const FPR_INVSQRT2: Fpr = 4604544271217802189;
pub const FPR_INVSQRT8: Fpr = 4600040671590431693;
pub const FPR_PTWO31: Fpr = 4746794007248502784;
pub const FPR_PTWO31M1: Fpr = 4746794007244308480;
pub const FPR_MTWO31M1: Fpr = 13970166044099084288;
pub const FPR_PTWO63M1: Fpr = 4890909195324358656;
pub const FPR_MTWO63M1: Fpr = 14114281232179134464;
pub const FPR_PTWO63: Fpr = 4890909195324358656;

// ------------------------------------------------------------------
// Shift helpers (reference fpr.h).
// ------------------------------------------------------------------

#[inline]
fn fpr_ursh(x: u64, n: i32) -> u64 {
    let x = x ^ ((x ^ (x >> 32)) & (((n >> 5) as i64).wrapping_neg() as u64));
    x >> (n & 31)
}

#[inline]
fn fpr_irsh(x: i64, n: i32) -> i64 {
    let x = x ^ ((x ^ (x >> 32)) & ((n >> 5) as i64).wrapping_neg());
    x >> (n & 31)
}

#[inline]
#[allow(dead_code)]
fn fpr_ulsh(x: u64, n: i32) -> u64 {
    let x = x ^ ((x ^ (x << 32)) & (((n >> 5) as i64).wrapping_neg() as u64));
    x << (n & 31)
}

// ------------------------------------------------------------------
// Value construction (reference FPR()).
// ------------------------------------------------------------------

#[inline]
fn fpr_build(s: i32, e: i32, m: u64) -> Fpr {
    let e = e.wrapping_add(1076);
    let t0 = ((e as u32) >> 31) as u64;
    let m = m & t0.wrapping_sub(1);
    let t1 = (m >> 54) as i64;
    let e = (e as i64) & -t1;
    let mut x = (((s as u64) << 63) | (m >> 2)).wrapping_add(((e as i64) as u64) << 52);
    let f = (m & 7u64) as u32;
    x = x.wrapping_add((0xC8u64 >> f) & 1);
    x
}

/// Reference `FPR_NORM64`: normalize the mantissa and adjust the exponent.
#[inline]
fn fpr_norm64(m: &mut u64, e: &mut i32) {
    *e -= 63;

    let mut nt = ((*m) >> 32) as u32;
    nt = (nt | nt.wrapping_neg()) >> 31;
    *m ^= (*m ^ ((*m) << 32)) & ((nt as u64).wrapping_sub(1));
    *e += (nt as i32) << 5;

    nt = ((*m) >> 48) as u32;
    nt = (nt | nt.wrapping_neg()) >> 31;
    *m ^= (*m ^ ((*m) << 16)) & ((nt as u64).wrapping_sub(1));
    *e += (nt as i32) << 4;

    nt = ((*m) >> 56) as u32;
    nt = (nt | nt.wrapping_neg()) >> 31;
    *m ^= (*m ^ ((*m) << 8)) & ((nt as u64).wrapping_sub(1));
    *e += (nt as i32) << 3;

    nt = ((*m) >> 60) as u32;
    nt = (nt | nt.wrapping_neg()) >> 31;
    *m ^= (*m ^ ((*m) << 4)) & ((nt as u64).wrapping_sub(1));
    *e += (nt as i32) << 2;

    nt = ((*m) >> 62) as u32;
    nt = (nt | nt.wrapping_neg()) >> 31;
    *m ^= (*m ^ ((*m) << 2)) & ((nt as u64).wrapping_sub(1));
    *e += (nt as i32) << 1;

    nt = ((*m) >> 63) as u32;
    *m ^= (*m ^ ((*m) << 1)) & (nt as u64);
    *e += nt as i32;
}

/// Reference `fpr_scaled(i, sc)`.
pub fn fpr_scaled(i: i64, sc: i32) -> Fpr {
    let s = ((i as u64) >> 63) as i32;
    let mut i = (i ^ (s as i64).wrapping_neg()).wrapping_add(s as i64);
    let mut m = i as u64;
    let mut e = 9i32.wrapping_add(sc);
    fpr_norm64(&mut m, &mut e);
    m |= ((((m as u32) & 0x1FF).wrapping_add(0x1FF)) as u64);
    m >>= 9;
    let t = ((((i as u64) | (i as u64).wrapping_neg()) >> 63) as u32) as u64;
    m &= t.wrapping_neg();
    e &= -((t as i64) as i32);
    fpr_build(s, e, m)
}

/// Reference `fpr_of(i)`.
#[inline]
pub fn fpr_of(i: i64) -> Fpr {
    fpr_scaled(i, 0)
}

/// Reference `fpr_rint(x)`.
pub fn fpr_rint(x: Fpr) -> i64 {
    let mut m: u64;
    let d: u64;
    let mut e: i32;
    let dd: u32;
    let f: u32;

    m = ((x << 10) | (1u64 << 62)) & ((1u64 << 63) - 1);
    e = 1085 - (((x >> 52) as u32 & 0x7FF) as i32);
    m &= ((((e - 64) as u32) >> 31).wrapping_neg()) as u64;
    e &= 63;
    d = fpr_ulsh(m, 63 - e);
    dd = (d as u32) | (((d >> 32) as u32) & 0x1FFF_FFFF);
    f = ((d >> 61) as u32) | ((dd | dd.wrapping_neg()) >> 31);
    m = fpr_ursh(m, e).wrapping_add((0xC8u64 >> f) & 1);
    let s = (x >> 63) as i64;
    ((m as i64) ^ -s).wrapping_add(s)
}

/// Reference `fpr_floor(x)`.
pub fn fpr_floor(x: Fpr) -> i64 {
    let e = ((x >> 52) as u32 & 0x7FF) as i32;
    let t = x >> 63;
    let mut xi = (((x << 10) | (1u64 << 62)) & ((1u64 << 63) - 1)) as i64;
    xi = (xi ^ -((t as i64) & 0xF)).wrapping_add(t as i64);
    let cc = 1085 - e;
    xi = fpr_irsh(xi, cc & 63);
    let mask = ((((63 - cc) as u32) >> 31).wrapping_neg()) as i64;
    xi ^= (xi ^ -((t as i64) & 0xF)) & mask;
    xi
}

/// Reference `fpr_trunc(x)`.
pub fn fpr_trunc(x: Fpr) -> i64 {
    let e = ((x >> 52) as u32 & 0x7FF) as i32;
    let mut xu = ((x << 10) | (1u64 << 62)) & ((1u64 << 63) - 1);
    let cc = 1085 - e;
    xu = fpr_ursh(xu, cc & 63);
    xu &= ((((cc - 64) as u32) >> 31).wrapping_neg()) as u64;
    let t = x >> 63;
    xu = (xu ^ t.wrapping_neg()).wrapping_add(t);
    xu as i64
}

/// Reference `fpr_add(x, y)` (fpr.c).
pub fn fpr_add(x: Fpr, y: Fpr) -> Fpr {
    let m63: u64 = (1u64 << 63) - 1;
    let za = (x & m63).wrapping_sub(y & m63);
    let cs = ((za >> 63) as u32)
        | (1u32.wrapping_sub((za.wrapping_neg() >> 63) as u32)) & ((x >> 63) as u32);
    let m = (x ^ y) & (cs as u64).wrapping_neg();
    let x = x ^ m;
    let y = y ^ m;
    let mut ex = ((x >> 52) as u32) as i32;
    let sx = ex >> 11;
    ex &= 0x7FF;
    let mut m = ((((ex + 0x7FF) >> 11) as u32) as u64) << 52;
    let mut xu = ((x & ((1u64 << 52) - 1)) | m) << 3;
    ex -= 1078;
    let mut ey = ((y >> 52) as u32) as i32;
    let sy = ey >> 11;
    ey &= 0x7FF;
    m = ((((ey + 0x7FF) >> 11) as u32) as u64) << 52;
    let mut yu = ((y & ((1u64 << 52) - 1)) | m) << 3;
    ey -= 1078;
    let mut cc = ex - ey;
    yu &= ((((cc - 60) as u32) >> 31).wrapping_neg()) as u64;
    cc &= 63;
    m = fpr_ulsh_literal(1, cc) - 1;
    yu |= (yu & m).wrapping_add(m);
    yu = fpr_ursh(yu, cc);
    xu = xu.wrapping_add(yu.wrapping_sub((yu << 1) & ((sx ^ sy) as u64).wrapping_neg()));
    fpr_norm64(&mut xu, &mut ex);
    xu |= ((((xu as u32) & 0x1FF).wrapping_add(0x1FF)) as u64);
    xu >>= 9;
    ex += 9;
    fpr_build(sx, ex, xu)
}

/// Literal 1-bit shift used by `fpr_add` (avoids the ulsh helper's masking).
#[inline]
fn fpr_ulsh_literal(x: u64, n: i32) -> u64 {
    debug_assert!(n >= 0 && n < 63);
    x << n
}

/// Reference `fpr_sub(x, y)`.
#[inline]
pub fn fpr_sub(x: Fpr, y: Fpr) -> Fpr {
    fpr_add(x, y ^ (1u64 << 63))
}

/// Reference `fpr_neg(x)`.
#[inline]
pub fn fpr_neg(x: Fpr) -> Fpr {
    x ^ (1u64 << 63)
}

/// Reference `fpr_half(x)`.
#[inline]
pub fn fpr_half(x: Fpr) -> Fpr {
    let x = x.wrapping_sub(1u64 << 52);
    let t = ((((x >> 52) as u32) & 0x7FF).wrapping_add(1)) >> 11;
    x & ((t as u64).wrapping_sub(1))
}

/// Reference `fpr_double(x)`.
#[inline]
pub fn fpr_double(x: Fpr) -> Fpr {
    let inc = (((((x >> 52) as u32) & 0x7FF).wrapping_add(0x7FF)) >> 11) as u64;
    x.wrapping_add(inc << 52)
}

/// Reference `fpr_mul(x, y)` (fpr.c).
pub fn fpr_mul(x: Fpr, y: Fpr) -> Fpr {
    let xu = (x & ((1u64 << 52) - 1)) | (1u64 << 52);
    let yu = (y & ((1u64 << 52) - 1)) | (1u64 << 52);
    let x0 = (xu as u32) & 0x01FF_FFFF;
    let x1 = ((xu >> 25) as u32) & 0x01FF_FFFF;
    let y0 = (yu as u32) & 0x01FF_FFFF;
    let y1 = ((yu >> 25) as u32) & 0x01FF_FFFF;
    let mut z0: u32;
    let mut z1: u32;
    let mut z2: u32;

    let mut w = (x0 as u64) * (y0 as u64);
    z0 = (w as u32) & 0x01FF_FFFF;
    z1 = ((w >> 25) as u32) & 0x01FF_FFFF;
    w = (x0 as u64) * (y1 as u64);
    z1 = z1.wrapping_add((w as u32) & 0x01FF_FFFF);
    z2 = ((w >> 25) as u32) & 0x01FF_FFFF;
    w = (x1 as u64) * (y0 as u64);
    z1 = z1.wrapping_add((w as u32) & 0x01FF_FFFF);
    z2 = z2.wrapping_add((w >> 25) as u32);
    let mut zu = (x1 as u64) * (y1 as u64);
    z2 = z2.wrapping_add(z1 >> 25);
    z1 &= 0x01FF_FFFF;
    zu = zu.wrapping_add(z2);
    zu |= (((z0 | z1).wrapping_add(0x01FF_FFFF)) >> 25) as u64;
    let zv = (zu >> 1) | (zu & 1);
    w = zu >> 55;
    zu ^= (zu ^ zv) & (w as u64).wrapping_neg();
    let ex = ((x >> 52) as u32 & 0x7FF) as i32;
    let ey = ((y >> 52) as u32 & 0x7FF) as i32;
    let mut e = ex + ey - 2100 + (w as i32);
    let s = (((x ^ y) >> 63) as u32) as i32;
    let d = (((ex + 0x7FF) & (ey + 0x7FF)) >> 11) as i64;
    zu &= (d as u64).wrapping_neg();
    fpr_build(s, e, zu)
}

/// Reference `fpr_sqr(x)`.
#[inline]
pub fn fpr_sqr(x: Fpr) -> Fpr {
    fpr_mul(x, x)
}

/// Reference `fpr_div(x, y)` (fpr.c).
pub fn fpr_div(x: Fpr, y: Fpr) -> Fpr {
    let mut xu = (x & ((1u64 << 52) - 1)) | (1u64 << 52);
    let mut yu = (y & ((1u64 << 52) - 1)) | (1u64 << 52);
    let mut q: u64 = 0;
    for _ in 0..55 {
        let b = ((xu.wrapping_sub(yu)) >> 63).wrapping_sub(1);
        xu -= b & yu;
        q |= b & 1;
        xu <<= 1;
        q <<= 1;
    }
    q |= (xu | xu.wrapping_neg()) >> 63;
    let q2 = (q >> 1) | (q & 1);
    let w = q >> 55;
    q ^= (q ^ q2) & (w as u64).wrapping_neg();
    let ex = ((x >> 52) as u32 & 0x7FF) as i32;
    let ey = ((y >> 52) as u32 & 0x7FF) as i32;
    let mut e = ex - ey - 55 + (w as i32);
    let mut s = (((x ^ y) >> 63) as u32) as i64;
    let d = (ex as i64 + 0x7FF) >> 11;
    s &= d;
    e &= -(d as i32);
    q &= (d as u64).wrapping_neg();
    fpr_build(s as i32, e, q)
}

/// Reference `fpr_inv(x)`.
#[inline]
pub fn fpr_inv(x: Fpr) -> Fpr {
    fpr_div(FPR_ONE, x)
}

/// Reference `fpr_sqrt(x)` (fpr.c).
pub fn fpr_sqrt(x: Fpr) -> Fpr {
    let mut xu = (x & ((1u64 << 52) - 1)) | (1u64 << 52);
    let ex = ((x >> 52) as u32 & 0x7FF) as i32;
    let mut e = ex - 1023;
    xu = xu.wrapping_add(xu & -((e & 1) as u64));
    e >>= 1;
    xu <<= 1;
    let mut q: u64 = 0;
    let mut s: u64 = 0;
    let mut r: u64 = 1u64 << 53;
    for _ in 0..54 {
        let t = s.wrapping_add(r);
        let b = ((xu.wrapping_sub(t)) >> 63).wrapping_sub(1);
        s = s.wrapping_add((r << 1) & b);
        xu = xu.wrapping_sub(t & b);
        q = q.wrapping_add(r & b);
        xu <<= 1;
        r >>= 1;
    }
    q <<= 1;
    q |= (xu | xu.wrapping_neg()) >> 63;
    e -= 54;
    q &= -(((ex as i64 + 0x7FF) >> 11) as u64);
    fpr_build(0, e, q)
}

/// Reference `fpr_lt(x, y)`.
#[inline]
pub fn fpr_lt(x: Fpr, y: Fpr) -> bool {
    let xi = x as i64;
    let yi = y as i64;
    let cc0 = (xi < yi) as i32;
    let cc1 = (xi > yi) as i32;
    (cc0 ^ ((cc0 ^ cc1) & ((((x & y) >> 63) as u32) as i32))) != 0
}

/// Reference `fpr_expm_p63(x, ccs)` (fpr.c).
pub fn fpr_expm_p63(x: Fpr, ccs: Fpr) -> u64 {
    const C: [u64; 13] = [
        0x00000004741183A3,
        0x00000036548CFC06,
        0x0000024FDCBF140A,
        0x0000171D939DE045,
        0x0000D00CF58F6F84,
        0x000680681CF796E3,
        0x002D82D8305B0FEA,
        0x011111110E066FD0,
        0x0555555555070F00,
        0x155555555581FF00,
        0x400000000002B400,
        0x7FFFFFFFFFFF4800,
        0x8000000000000000,
    ];
    let mut z: u64;
    let mut y: u64;

    y = C[0];
    z = (fpr_trunc(fpr_mul(x, FPR_PTWO63)) as u64) << 1;
    for item in C.iter().skip(1) {
        let z0 = z as u32;
        let z1 = (z >> 32) as u32;
        let y0 = y as u32;
        let y1 = (y >> 32) as u32;
        let a = (z0 as u64) * (y1 as u64) + (((z0 as u64) * (y0 as u64)) >> 32);
        let b = (z1 as u64) * (y0 as u64);
        let mut c = (a >> 32) + (b >> 32);
        c += (((a as u32) as u64).wrapping_add((b as u32) as u64)) >> 32;
        c = c.wrapping_add((z1 as u64) * (y1 as u64));
        y = item.wrapping_sub(c);
    }
    z = (fpr_trunc(fpr_mul(ccs, FPR_PTWO63)) as u64) << 1;
    let z0 = z as u32;
    let z1 = (z >> 32) as u32;
    let y0 = y as u32;
    let y1 = (y >> 32) as u32;
    let a = (z0 as u64) * (y1 as u64) + (((z0 as u64) * (y0 as u64)) >> 32);
    let b = (z1 as u64) * (y0 as u64);
    y = (a >> 32) + (b >> 32);
    y = y.wrapping_add((((a as u32) as u64).wrapping_add((b as u32) as u64)) >> 32);
    y = y.wrapping_add((z1 as u64) * (y1 as u64));
    y
}

/// Reference `fpr_gm_tab` (extracted table).
#[inline]
pub fn fpr_gm_tab(i: usize) -> Fpr {
    FPR_GM_TAB[i]
}

/// Reference `fpr_p2_tab` (extracted table).
#[inline]
pub fn fpr_p2_tab(i: usize) -> Fpr {
    FPR_P2_TAB[i]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn constants_roundtrip_through_f64() {
        // The encoded constants are IEEE-754 bit patterns; decode and sanity
        // check a few against the spec's real values.
        assert_eq!(f64::from_bits(FPR_Q), 12289.0);
        assert!((f64::from_bits(FPR_INVERSE_OF_Q) - 1.0 / 12289.0).abs() < 1e-20);
        assert_eq!(f64::from_bits(FPR_ONE), 1.0);
        assert_eq!(f64::from_bits(FPR_TWO), 2.0);
        assert_eq!(f64::from_bits(FPR_ONEHALF), 0.5);
        assert_eq!(f64::from_bits(FPR_LOG2), std::f64::consts::LN_2);
        assert_eq!(
            f64::from_bits(FPR_INV_2SQRSIGMA0),
            1.0 / (2.0 * 1.8205_f64.powi(2))
        );
    }

    #[test]
    fn arithmetic_matches_f64() {
        // The soft-float must agree with hardware f64 for these exact cases.
        let of = |v: f64| fpr_of(v as i64);
        let add = f64::from_bits(fpr_add(of(5), of(-9)));
        assert_eq!(add, -4.0);
        let mul = f64::from_bits(fpr_mul(fpr_of(123), fpr_of(-45)));
        assert_eq!(mul, -5535.0);
        let sqrt = f64::from_bits(fpr_sqrt(fpr_of(144)));
        assert_eq!(sqrt, 12.0);
        let div = f64::from_bits(fpr_div(fpr_of(1000), fpr_of(8)));
        assert_eq!(div, 125.0);
        assert!(fpr_lt(of(3), of(7)));
        assert!(!fpr_lt(of(-7), of(-9)));
        assert_eq!(fpr_rint(fpr_of(42)), 42);
        assert_eq!(fpr_floor(fpr_of(-42)), -42);
        assert_eq!(fpr_trunc(fpr_of(-42)), -42);
    }
}
