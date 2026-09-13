//! Port of the Falcon reference `vrfy.c`: arithmetic modulo q = 12289
//! (Montgomery form, R = 2^16), the q-NLL NTT, and the verification /
//! key-completion functions.
#![allow(clippy::needless_range_loop, clippy::too_many_arguments)]

use super::common::is_short;
use super::tables::{GMB, IGMB};

/// The Falcon modulus: q = 12289 = 3·2^12 + 1 (prime, 2-adicity 12), so
/// negacyclic NTTs of length up to 2^11 exist — enough for n ≤ 1024.
const Q: u32 = 12289;
/// −q^−1 mod 2^16 (Montgomery reduction constant for `mq_montymul`).
const Q0I: u32 = 12287;
/// R² mod q with R = 2^16: multiplying by it moves a value into
/// Montgomery representation.
const R2: u32 = 10952;

/// Reduce a small signed integer modulo q (input in [-q/2, q/2]).
#[inline]
fn mq_conv_small(x: i32) -> u32 {
    let mut y = x as u32;
    y = y.wrapping_add(Q & ((y >> 31).wrapping_neg()));
    y
}

/// Addition modulo q (operands in 0..q-1).
#[inline]
fn mq_add(x: u32, y: u32) -> u32 {
    let d = x.wrapping_add(y).wrapping_sub(Q);
    d.wrapping_add(Q & (d >> 31).wrapping_neg())
}

/// Subtraction modulo q (operands in 0..q-1).
#[inline]
fn mq_sub(x: u32, y: u32) -> u32 {
    let d = x.wrapping_sub(y);
    d.wrapping_add(Q & (d >> 31).wrapping_neg())
}

/// Halving modulo q.
#[inline]
fn mq_rshift1(x: u32) -> u32 {
    let x = x.wrapping_add(Q & (x & 1).wrapping_neg());
    x >> 1
}

/// Montgomery multiplication: x·y/R mod q.
#[inline]
fn mq_montymul(x: u32, y: u32) -> u32 {
    let z = x.wrapping_mul(y);
    let w = (z.wrapping_mul(Q0I) & 0xFFFF).wrapping_mul(Q);
    let z = (z.wrapping_add(w)) >> 16;
    let z = z.wrapping_sub(Q);
    z.wrapping_add(Q & (z >> 31).wrapping_neg())
}

/// Division by y modulo q (exponentiation with the q−2 addition chain).
#[inline]
fn mq_div_12289(x: u32, y: u32) -> u32 {
    let y0 = mq_montymul(y, R2);
    let y1 = mq_montymul(y0, y0);
    let y2 = mq_montymul(y1, y0);
    let y3 = mq_montymul(y2, y1);
    let y4 = mq_montymul(y3, y3);
    let y5 = mq_montymul(y4, y4);
    let y6 = mq_montymul(y5, y5);
    let y7 = mq_montymul(y6, y6);
    let y8 = mq_montymul(y7, y7);
    let y9 = mq_montymul(y8, y2);
    let y10 = mq_montymul(y9, y8);
    let y11 = mq_montymul(y10, y10);
    let y12 = mq_montymul(y11, y11);
    let y13 = mq_montymul(y12, y9);
    let y14 = mq_montymul(y13, y13);
    let y15 = mq_montymul(y14, y14);
    let y16 = mq_montymul(y15, y10);
    let y17 = mq_montymul(y16, y16);
    let y18 = mq_montymul(y17, y0);
    mq_montymul(y18, x)
}

/// Negacyclic NTT over Z_q[X]/(X^n + 1), coefficient -> evaluation form.
/// The `GMB` twiddles are pre-multiplied by R = 2^16, so each level's
/// `mq_montymul` applies a twiddle with no net Montgomery factor: plain
/// residues in, plain residues out.
fn mq_ntt(a: &mut [u16], logn: u32) {
    let n = 1usize << logn;
    let mut t = n;
    let mut m = 1usize;
    while m < n {
        let ht = t >> 1;
        let mut j1 = 0usize;
        for i in 0..m {
            let s = GMB[m + i] as u32;
            let j2 = j1 + ht;
            for j in j1..j2 {
                let u_val = a[j] as u32;
                let v = mq_montymul(a[j + ht] as u32, s);
                a[j] = mq_add(u_val, v) as u16;
                a[j + ht] = mq_sub(u_val, v) as u16;
            }
            j1 += t;
        }
        t = ht;
        m <<= 1;
    }
}

/// Inverse NTT over Z_q[X]/(X^n + 1) (undoes [`mq_ntt`]), evaluation ->
/// coefficient form; the final step divides by n with `mq_montymul` and
/// 1/n expressed in Montgomery representation (ni = R/n, obtained by
/// halving R logn times).
fn mq_intt(a: &mut [u16], logn: u32) {
    let n = 1usize << logn;
    let mut t = 1usize;
    let mut m = n;
    while m > 1 {
        let hm = m >> 1;
        let dt = t << 1;
        let mut j1 = 0usize;
        for i in 0..hm {
            let j2 = j1 + t;
            let s = IGMB[hm + i] as u32;
            for j in j1..j2 {
                let u_val = a[j] as u32;
                let v = a[j + t] as u32;
                a[j] = mq_add(u_val, v) as u16;
                let w = mq_sub(u_val, v);
                a[j + t] = mq_montymul(w, s) as u16;
            }
            j1 += dt;
        }
        t = dt;
        m = hm;
    }
    // Divide by n, in Montgomery representation.
    let mut ni: u32 = 1 << 16; // R
    let mut mm = n;
    while mm > 1 {
        ni = mq_rshift1(ni);
        mm >>= 1;
    }
    for v in a.iter_mut().take(n) {
        *v = mq_montymul(*v as u32, ni) as u16;
    }
}

/// Montgomery conversion for a whole polynomial.
fn mq_poly_tomonty(f: &mut [u16], logn: u32) {
    let n = 1usize << logn;
    for v in f.iter_mut().take(n) {
        *v = mq_montymul(*v as u32, R2) as u16;
    }
}

/// Pointwise Montgomery multiplication (NTT domain).
fn mq_poly_montymul_ntt(f: &mut [u16], g: &[u16], logn: u32) {
    let n = 1usize << logn;
    for u in 0..n {
        f[u] = mq_montymul(f[u] as u32, g[u] as u32) as u16;
    }
}

/// f = f − g (mod q).
fn mq_poly_sub(f: &mut [u16], g: &[u16], logn: u32) {
    let n = 1usize << logn;
    for u in 0..n {
        f[u] = mq_sub(f[u] as u32, g[u] as u32) as u16;
    }
}

/// Reference `to_ntt_monty(h, logn)`: NTT of h with every coefficient
/// moved into Montgomery representation (scaled by R), so that a pointwise
/// `mq_montymul` against it yields the plain (unscaled) product.
pub fn to_ntt_monty(h: &mut [u16], logn: u32) {
    mq_ntt(h, logn);
    mq_poly_tomonty(h, logn);
}

/// Reference `verify_raw(c0, s2, h, logn)`: recompute −s1 = s2·h − c0
/// modulo (X^n + 1, q) from the hash-derived point `c0`, the decoded
/// signature coefficient `s2` and the NTT/Montgomery public key `h` (as
/// produced by [`to_ntt_monty`]), then accept iff ‖(s1, s2)‖² ≤ beta²
/// (`is_short`). The signature carries only s2; s1 is rederived here.
pub fn verify_raw(c0: &[u16], s2: &[i16], h: &[u16], logn: u32) -> bool {
    let n = 1usize << logn;
    let mut tt = vec![0u16; n];

    // Reduce s2 modulo q.
    for u in 0..n {
        let mut w = s2[u] as i32 as u32;
        w = w.wrapping_add(Q & (w >> 31).wrapping_neg());
        tt[u] = w as u16;
    }

    // -s1 = s2*h - c0 mod phi mod q.
    mq_ntt(&mut tt, logn);
    mq_poly_montymul_ntt(&mut tt, h, logn);
    mq_intt(&mut tt, logn);
    mq_poly_sub(&mut tt, c0, logn);

    // Normalize -s1 into [-q/2..q/2]. The comparison is done on unsigned
    // words (logical shift), matching the reference's uint32 arithmetic.
    let mut norm = vec![0i16; n];
    for u in 0..n {
        let mut w = tt[u] as i32;
        let over = ((Q >> 1).wrapping_sub(w as u32) >> 31) as i32;
        w -= (Q as i32) & -over;
        norm[u] = w as i16;
    }

    is_short(&norm, s2, logn)
}

/// Reference `compute_public(h, f, g, logn)`: h = g/f mod phi mod q.
pub fn compute_public(h: &mut [u16], f: &[i8], g: &[i8], logn: u32) -> bool {
    let n = 1usize << logn;
    let mut tt = vec![0u16; n];
    for u in 0..n {
        tt[u] = mq_conv_small(f[u] as i32) as u16;
        h[u] = mq_conv_small(g[u] as i32) as u16;
    }
    mq_ntt(h, logn);
    mq_ntt(&mut tt, logn);
    for u in 0..n {
        if tt[u] == 0 {
            return false;
        }
        h[u] = mq_div_12289(h[u] as u32, tt[u] as u32) as u16;
    }
    mq_intt(h, logn);
    true
}

/// Reference `complete_private(G, f, g, F, logn)`: G = (F·g + q)/f.
pub fn complete_private(g_out: &mut [i8], f: &[i8], g: &[i8], big_f: &[i8], logn: u32) -> bool {
    let n = 1usize << logn;
    let mut t1 = vec![0u16; n];
    let mut t2 = vec![0u16; n];
    for u in 0..n {
        t1[u] = mq_conv_small(g[u] as i32) as u16;
        t2[u] = mq_conv_small(big_f[u] as i32) as u16;
    }
    mq_ntt(&mut t1, logn);
    mq_ntt(&mut t2, logn);
    mq_poly_tomonty(&mut t1, logn);
    mq_poly_montymul_ntt(&mut t1, &t2, logn);
    for u in 0..n {
        t2[u] = mq_conv_small(f[u] as i32) as u16;
    }
    mq_ntt(&mut t2, logn);
    for u in 0..n {
        if t2[u] == 0 {
            return false;
        }
        t1[u] = mq_div_12289(t1[u] as u32, t2[u] as u32) as u16;
    }
    mq_intt(&mut t1, logn);
    for u in 0..n {
        let mut w = t1[u] as i32;
        w -= (Q as i32) & !((w as i32 - ((Q >> 1) as i32)) >> 31);
        let gi = w;
        if !(-127..=127).contains(&gi) {
            return false;
        }
        g_out[u] = gi as i8;
    }
    true
}
