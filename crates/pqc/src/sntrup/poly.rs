//! Core arithmetic for Streamlined NTRU Prime, ported from the round-3
//! reference `kem.c`: `F_3` values are `−1/0/1` (`i8`), `F_q` values are
//! centered `−(q−1)/2 … (q−1)/2` (`i16`), in the ring
//! `R = Z[x]/(x^p − x − 1)`.

use super::params::SntrupParams;

/// Centered `F_3` value.
pub type Small = i8;
/// Centered `F_q` value.
pub type Fq = i16;

/// `⌈q/2⌉`-style half-modulus offset (`(q−1)/2`) used for the centered
/// representatives.
#[inline]
pub fn q12<P: SntrupParams>() -> Fq {
    ((P::Q - 1) / 2) as Fq
}

/// `F3_freeze`: reduce an integer to `−1/0/1`.
#[inline]
pub fn f3_freeze(x: i16) -> Small {
    // Signed (Euclidean) reduction — the reference's int32_mod_uint14.
    ((x + 1).rem_euclid(3) - 1) as Small
}

/// `Fq_freeze`: reduce an integer to the centered representatives.
#[inline]
pub fn fq_freeze<P: SntrupParams>(x: i32) -> Fq {
    ((x + q12::<P>() as i32).rem_euclid(P::Q as i32) - q12::<P>() as i32) as Fq
}

/// `uint32_mod_uint14`: `x mod m` for `1 ≤ m < 16384` (the reference's
/// constant-time division computes exactly this value).
#[inline]
pub fn mod_uint14(x: u32, m: u32) -> u16 {
    debug_assert!((1..16384).contains(&m));
    (x % m) as u16
}

/// `R3_fromRq`: reduce a mod-q polynomial coefficient-wise mod 3.
pub fn r3_from_rq<P: SntrupParams>(r: &[Fq]) -> Vec<Small> {
    r.iter().map(|&v| f3_freeze(v)).collect()
}

/// `R3_mult`: `h = f·g` in `R3 = Z_3[x]/(x^p − x − 1)`.
pub fn r3_mult<P: SntrupParams>(f: &[Small], g: &[Small]) -> Vec<Small> {
    let p = P::P;
    let mut fg = vec![0 as Small; 2 * p - 1];
    for i in 0..p {
        let mut result: Small = 0;
        for j in 0..=i {
            result = f3_freeze(result as i16 + f[j] as i16 * g[i - j] as i16);
        }
        fg[i] = result;
    }
    for i in p..2 * p - 1 {
        let mut result: Small = 0;
        for j in (i - p + 1)..p {
            result = f3_freeze(result as i16 + f[j] as i16 * g[i - j] as i16);
        }
        fg[i] = result;
    }
    // Reduction mod (x^p − x − 1): x^p ≡ x + 1.
    let mut out = vec![0 as Small; p];
    out.copy_from_slice(&fg[..p]);
    for i in (p..2 * p - 1).rev() {
        let t = fg[i];
        out[i - p] = f3_freeze(out[i - p] as i16 + t as i16);
        out[i - p + 1] = f3_freeze(out[i - p + 1] as i16 + t as i16);
    }
    out
}

/// `Weightw_mask`: `0` if `r` has exactly `w` odd coefficients, else `−1`.
pub fn weightw_mask<P: SntrupParams>(r: &[Small]) -> i16 {
    let mut weight: i32 = 0;
    for &v in r.iter() {
        weight += (v & 1) as i32;
    }
    if weight == P::W as i32 {
        0
    } else {
        -1
    }
}

/// `Round`: round each coefficient to the nearest multiple of 3.
pub fn round3<P: SntrupParams>(a: &[Fq]) -> Vec<Fq> {
    a.iter().map(|&v| v - f3_freeze(v) as Fq).collect()
}

/// `Rq_mult_small`: `h = f·g` with small `g` in `Rq = Z_q[x]/(x^p − x − 1)`.
pub fn rq_mult_small<P: SntrupParams>(f: &[Fq], g: &[Small]) -> Vec<Fq> {
    let p = P::P;
    let mut fg = vec![0 as Fq; 2 * p - 1];
    for i in 0..p {
        let mut result: i32 = 0;
        for j in 0..=i {
            result = fq_freeze::<P>(result + f[j] as i32 * g[i - j] as i32) as i32;
        }
        fg[i] = result as Fq;
    }
    for i in p..2 * p - 1 {
        let mut result: i32 = 0;
        for j in (i - p + 1)..p {
            result = fq_freeze::<P>(result + f[j] as i32 * g[i - j] as i32) as i32;
        }
        fg[i] = result as Fq;
    }
    let mut out = vec![0 as Fq; p];
    out.copy_from_slice(&fg[..p]);
    for i in (p..2 * p - 1).rev() {
        let t = fg[i];
        out[i - p] = fq_freeze::<P>(out[i - p] as i32 + t as i32);
        out[i - p + 1] = fq_freeze::<P>(out[i - p + 1] as i32 + t as i32);
    }
    out
}

/// `Rq_mult3`: `h = 3f` in `Rq`.
pub fn rq_mult3<P: SntrupParams>(f: &[Fq]) -> Vec<Fq> {
    f.iter().map(|&v| fq_freeze::<P>(3 * v as i32)).collect()
}

/// `Fq_recip`: `a^(q−2) mod q` by square-and-multiply-free iterated
/// multiplication (q−2 steps), as the reference computes small inverses.
fn fq_recip<P: SntrupParams>(a1: Fq) -> Fq {
    let mut ai = a1;
    for _ in 1..P::Q as i32 - 2 {
        ai = fq_freeze::<P>(a1 as i32 * ai as i32);
    }
    ai
}

/// `R3_recip`: inverse of `in` in `R3`; returns `None` if `in` is not
/// invertible (the keygen loop resamples). Port of the reference's
/// constant-time extended GCD over `F_3[x]/(x^p − x − 1)`.
pub fn r3_recip<P: SntrupParams>(input: &[Small]) -> Option<Vec<Small>> {
    let p = P::P;
    let mut f = vec![0 as Small; p + 1];
    let mut g = vec![0 as Small; p + 1];
    let mut v = vec![0 as Small; p + 1];
    let mut r = vec![0 as Small; p + 1];

    r[0] = 1;
    f[0] = 1;
    f[p - 1] = -1;
    f[p] = -1;
    for i in 0..p {
        g[p - 1 - i] = input[i];
    }

    let mut delta: i16 = 1;
    for _loop in 0..(2 * p - 1) {
        for i in (1..=p).rev() {
            v[i] = v[i - 1];
        }
        v[0] = 0;

        let sign = -g[0] * f[0];
        let swap = int16_negative_mask(-delta) & int16_nonzero_mask(g[0] as i16);
        delta ^= swap & (delta ^ (-delta));
        delta += 1;

        for i in 0..=p {
            let t = swap & ((f[i] as i16) ^ (g[i] as i16));
            f[i] = ((f[i] as i16) ^ t) as Small;
            g[i] = ((g[i] as i16) ^ t) as Small;
            let t = swap & ((v[i] as i16) ^ (r[i] as i16));
            v[i] = ((v[i] as i16) ^ t) as Small;
            r[i] = ((r[i] as i16) ^ t) as Small;
        }

        for i in 0..=p {
            g[i] = f3_freeze(g[i] as i16 + sign as i16 * f[i] as i16);
        }
        for i in 0..=p {
            r[i] = f3_freeze(r[i] as i16 + sign as i16 * v[i] as i16);
        }

        for i in 0..p {
            g[i] = g[i + 1];
        }
        g[p] = 0;
    }

    let sign = f[0];
    let mut out = vec![0 as Small; p];
    for i in 0..p {
        out[i] = sign * v[p - 1 - i];
    }
    if delta == 0 {
        Some(out)
    } else {
        None
    }
}

/// `Rq_recip3`: `out = 1/(3·in)` in `Rq`; always succeeds for keygen
/// inputs. Port of the reference's constant-time extended GCD mod q.
pub fn rq_recip3<P: SntrupParams>(input: &[Small]) -> Vec<Fq> {
    let p = P::P;
    let mut f = vec![0 as Fq; p + 1];
    let mut g = vec![0 as Fq; p + 1];
    let mut v = vec![0 as Fq; p + 1];
    let mut r = vec![0 as Fq; p + 1];

    r[0] = fq_recip::<P>(3);
    f[0] = 1;
    f[p - 1] = -1;
    f[p] = -1;
    for i in 0..p {
        g[p - 1 - i] = input[i] as Fq;
    }

    let mut delta: i16 = 1;
    for _loop in 0..(2 * p - 1) {
        for i in (1..=p).rev() {
            v[i] = v[i - 1];
        }
        v[0] = 0;

        let swap = int16_negative_mask(-delta) & int16_nonzero_mask(g[0]);
        delta ^= swap & (delta ^ (-delta));
        delta += 1;

        for i in 0..=p {
            let t = swap & ((f[i] as i16) ^ (g[i] as i16));
            f[i] = ((f[i] as i16) ^ t) as Fq;
            g[i] = ((g[i] as i16) ^ t) as Fq;
            let t = swap & ((v[i] as i16) ^ (r[i] as i16));
            v[i] = ((v[i] as i16) ^ t) as Fq;
            r[i] = ((r[i] as i16) ^ t) as Fq;
        }

        let f0 = f[0] as i32;
        let g0 = g[0] as i32;
        for i in 0..=p {
            g[i] = fq_freeze::<P>(f0 * g[i] as i32 - g0 * f[i] as i32);
        }
        for i in 0..=p {
            r[i] = fq_freeze::<P>(f0 * r[i] as i32 - g0 * v[i] as i32);
        }

        for i in 0..p {
            g[i] = g[i + 1];
        }
        g[p] = 0;
    }

    let scale = fq_recip::<P>(f[0]);
    let mut out = vec![0 as Fq; p];
    for i in 0..p {
        out[i] = fq_freeze::<P>(scale as i32 * v[p - 1 - i] as i32);
    }
    out
}

/// `int16_negative_mask`: `−1` if `x < 0`, else `0`.
#[inline]
fn int16_negative_mask(x: i16) -> i16 {
    -((x >> 15) & 1)
}

/// `int16_nonzero_mask`: `−1` if `x != 0`, else `0`.
#[inline]
fn int16_nonzero_mask(x: i16) -> i16 {
    if x != 0 {
        -1
    } else {
        0
    }
}
