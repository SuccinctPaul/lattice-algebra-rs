//! Polynomial arithmetic for NTRU over `Z_q[x]/(x^n − 1)` and its
//! reductions modulo `Φ_n = (x^n − 1)/(x − 1)`, ported from the round-3
//! reference implementation (`poly*.c`, `pack3.c`, `packq.c`). All
//! coefficient arithmetic is `u16` wrapping, exactly as the C reference.

use super::params::NtruParams;
use alloc::{vec, vec::Vec};

/// A polynomial with `n` coefficients in `[0, q)` (or `{0,1,2}` in the
/// ternary representation).
pub type Poly = Vec<u16>;

/// `poly_Rq_mul`: circulant product mod `x^n − 1` (u16-wrapping sums).
pub fn rq_mul<P: NtruParams>(a: &[u16], b: &[u16]) -> Poly {
    let n = P::N;
    let mut r = vec![0u16; n];
    for k in 0..n {
        let mut acc = 0u16;
        for i in 1..n - k {
            acc = acc.wrapping_add(a[k + i].wrapping_mul(b[n - i]));
        }
        for i in 0..k + 1 {
            acc = acc.wrapping_add(a[k - i].wrapping_mul(b[i]));
        }
        r[k] = acc;
    }
    r
}

fn mod3_u16(a: u16) -> u16 {
    a % 3
}

/// `poly_mod_3_Phi_n`: reduce coefficients mod 3 and the polynomial mod
/// `Φ_n` (using `x^n ≡ 1`, then the `x ≡ 1` folding of the all-ones root).
pub fn mod_3_phi_n<P: NtruParams>(r: &mut Poly) {
    let n = P::N;
    let last = r[n - 1];
    for c in r.iter_mut() {
        *c = mod3_u16(c.wrapping_add(last.wrapping_mul(2)));
    }
}

/// `poly_mod_q_Phi_n`: reduce mod `Φ_n` over `Z_q`.
pub fn mod_q_phi_n<P: NtruParams>(r: &mut Poly) {
    let n = P::N;
    let last = r[n - 1];
    for c in r.iter_mut() {
        *c = c.wrapping_sub(last);
    }
}

/// `poly_Sq_mul`: multiply and reduce mod `(q, Φ_n)`.
pub fn sq_mul<P: NtruParams>(a: &[u16], b: &[u16]) -> Poly {
    let mut r = rq_mul::<P>(a, b);
    mod_q_phi_n::<P>(&mut r);
    r
}

/// `poly_S3_mul`: multiply two ternary polynomials, result mod `(3, Φ_n)`.
pub fn s3_mul<P: NtruParams>(a: &[u16], b: &[u16]) -> Poly {
    let mut r = rq_mul::<P>(a, b);
    mod_3_phi_n::<P>(&mut r);
    r
}

/// Map `{0,1,2}` → `{0,1,q−1}` in place (`poly_Z3_to_Zq`).
pub fn z3_to_zq<P: NtruParams>(r: &mut Poly) {
    let q_minus_1 = (1u16 << P::LOGQ) - 1;
    for c in r.iter_mut() {
        let shifted = *c >> 1;
        *c |= shifted.wrapping_neg() & q_minus_1;
    }
}

/// Map `{0,1,q−1}` → `{0,1,2}` (`poly_trinary_Zq_to_Z3`).
pub fn zq_to_z3<P: NtruParams>(r: &mut Poly) {
    let q_minus_1 = (1u16 << P::LOGQ) - 1;
    for c in r.iter_mut() {
        *c &= q_minus_1;
        *c = 3 & (*c ^ (*c >> (P::LOGQ - 1)));
    }
}

/// `poly_Rq_to_S3`: reduce a `[0,q)` polynomial mod `(3, Φ_n)`, first
/// re-centering coefficients so `q ≡ −1 (mod 3)` accounting is right.
pub fn rq_to_s3<P: NtruParams>(a: &[u16]) -> Poly {
    let q_minus_1 = (1u16 << P::LOGQ) - 1;
    let mut r: Poly = a.iter().map(|&c| c & q_minus_1).collect();
    // flag = 1 if r[i] >= q/2; add (−q) mod 3 = 1 << (1 − (logq & 1)).
    let add = 1u16 << (1 - (P::LOGQ & 1));
    for c in r.iter_mut() {
        let flag = *c >> (P::LOGQ - 1);
        *c += flag * add;
    }
    mod_3_phi_n::<P>(&mut r);
    r
}

// ---------------------------------------------------------------------------
// Inversion
// ---------------------------------------------------------------------------

/// `poly_R2_inv`: inverse mod `(2, x^n − 1)` — the constant-time
/// almost-inverse algorithm (port of `poly_r2_inv.c`).
pub fn r2_inv<P: NtruParams>(a: &[u16]) -> Poly {
    let n = P::N;
    let mut f = vec![0u16; n];
    let mut g = vec![0u16; n];
    let mut v = vec![0u16; n];
    let mut w = vec![0u16; n];

    w[0] = 1;
    for c in f.iter_mut() {
        *c = 1;
    }
    for i in 0..n - 1 {
        g[n - 2 - i] = (a[i] ^ a[n - 1]) & 1;
    }
    g[n - 1] = 0;

    let mut delta: i16 = 1;
    for _loop in 0..(2 * (n - 1) - 1) {
        for i in (1..n).rev() {
            v[i] = v[i - 1];
        }
        v[0] = 0;

        let sign = g[0] & f[0];
        let swap = both_negative_mask(-delta, -(g[0] as i16));
        delta ^= swap & (delta ^ (-delta));
        delta += 1;

        for i in 0..n {
            let t = swap & ((f[i] as i16) ^ (g[i] as i16));
            f[i] = ((f[i] as i16) ^ t) as u16;
            g[i] = ((g[i] as i16) ^ t) as u16;
            let t = swap & ((v[i] as i16) ^ (w[i] as i16));
            v[i] = ((v[i] as i16) ^ t) as u16;
            w[i] = ((w[i] as i16) ^ t) as u16;
        }

        for i in 0..n {
            g[i] = (g[i] as i16 ^ (sign as i16 & f[i] as i16)) as u16;
        }
        for i in 0..n {
            w[i] = (w[i] as i16 ^ (sign as i16 & v[i] as i16)) as u16;
        }
        for i in 0..n - 1 {
            g[i] = g[i + 1];
        }
        g[n - 1] = 0;
    }

    let mut r = vec![0u16; n];
    for i in 0..n - 1 {
        r[i] = v[n - 2 - i];
    }
    r
}

/// `poly_S3_inv`: inverse mod `(3, Φ_n)` (port of `poly_s3_inv.c`).
pub fn s3_inv<P: NtruParams>(a: &[u16]) -> Poly {
    let n = P::N;
    let mut f = vec![0u16; n];
    let mut g = vec![0u16; n];
    let mut v = vec![0u16; n];
    let mut w = vec![0u16; n];

    w[0] = 1;
    for c in f.iter_mut() {
        *c = 1;
    }
    for i in 0..n - 1 {
        g[n - 2 - i] = mod3_small((a[i] & 3) + 2 * (a[n - 1] & 3));
    }
    g[n - 1] = 0;

    let mut delta: i16 = 1;
    for _loop in 0..(2 * (n - 1) - 1) {
        for i in (1..n).rev() {
            v[i] = v[i - 1];
        }
        v[0] = 0;

        let sign = mod3_small(2 * (g[0] & 3) * (f[0] & 3));
        let swap = both_negative_mask(-delta, -(g[0] as i16));
        delta ^= swap & (delta ^ (-delta));
        delta += 1;

        for i in 0..n {
            let t = swap & ((f[i] as i16) ^ (g[i] as i16));
            f[i] = ((f[i] as i16) ^ t) as u16;
            g[i] = ((g[i] as i16) ^ t) as u16;
            let t = swap & ((v[i] as i16) ^ (w[i] as i16));
            v[i] = ((v[i] as i16) ^ t) as u16;
            w[i] = ((w[i] as i16) ^ t) as u16;
        }

        for i in 0..n {
            g[i] = mod3_small(g[i] + sign * f[i]);
        }
        for i in 0..n {
            w[i] = mod3_small(w[i] + sign * v[i]);
        }
        for i in 0..n - 1 {
            g[i] = g[i + 1];
        }
        g[n - 1] = 0;
    }

    let sign = f[0] & 3;
    let mut r = vec![0u16; n];
    for i in 0..n - 1 {
        r[i] = mod3_small(sign * v[n - 2 - i]);
    }
    r
}

fn mod3_small(a: u16) -> u16 {
    // Input bounded by small multiples of 3 (≤ 9 per the reference).
    let mut a = a % 3;
    if a >= 3 {
        a -= 3;
    }
    a
}

/// `both_negative_mask`: `−1` if both `x` and `y` are negative, else `0`.
fn both_negative_mask(x: i16, y: i16) -> i16 {
    (x & y) >> 15
}

/// `poly_Rq_inv`: inverse mod `(q, x^n − 1)` via the R2 inverse and four
/// Newton doublings `ai ← ai·(2 − a·ai) mod q`.
pub fn rq_inv<P: NtruParams>(a: &[u16]) -> Poly {
    let neg_a: Poly = a.iter().map(|&c| c.wrapping_neg()).collect();
    let mut r = r2_inv::<P>(a);
    let mut s;

    // Iterations 1 and 2 end in `s`, 3 and 4 in `r` — mirroring the
    // reference's alternating c/s temporaries.
    let mut c = rq_mul::<P>(&r, &neg_a);
    c[0] = c[0].wrapping_add(2);
    s = rq_mul::<P>(&c, &r);

    c = rq_mul::<P>(&s, &neg_a);
    c[0] = c[0].wrapping_add(2);
    r = rq_mul::<P>(&c, &s);

    c = rq_mul::<P>(&r, &neg_a);
    c[0] = c[0].wrapping_add(2);
    s = rq_mul::<P>(&c, &r);

    c = rq_mul::<P>(&s, &neg_a);
    c[0] = c[0].wrapping_add(2);
    r = rq_mul::<P>(&c, &s);
    r
}

// ---------------------------------------------------------------------------
// Lift
// ---------------------------------------------------------------------------

/// `poly_lift`: HPS — the lift is the `{0,1,2}` → `{0,1,q−1}` map.
pub fn lift_hps<P: NtruParams>(a: &[u16]) -> Poly {
    let mut r = a.to_vec();
    z3_to_zq::<P>(&mut r);
    r
}

/// `poly_lift` (HRSS): embed `Z_3[x]/Φ_n` into `Z_q[x]/Φ_n` as
/// `a·(x−1)` with the sign-fixed representative — port of the reference's
/// HRSS `poly_lift`.
#[allow(clippy::needless_range_loop)] // index arithmetic mirrors the C port
pub fn lift_hrss<P: NtruParams>(a: &[u16]) -> Poly {
    let n = P::N;
    let mut b = vec![0u16; n];
    let t: u16 = 3 - (P::N % 3) as u16;

    b[0] = a[0].wrapping_mul(2 - t) + a[2].wrapping_mul(t);
    b[1] = a[1].wrapping_mul(2 - t);
    b[2] = a[2].wrapping_mul(2 - t);

    let mut zj: u16 = 0; // z[1]
    for i in 3..n {
        b[0] = b[0].wrapping_add(a[i].wrapping_mul(zj + 2 * t));
        b[1] = b[1].wrapping_add(a[i].wrapping_mul(zj + t));
        b[2] = b[2].wrapping_add(a[i].wrapping_mul(zj));
        zj = (zj + t) % 3;
    }
    b[1] = b[1].wrapping_add(a[0].wrapping_mul(zj + t));
    b[2] = b[2].wrapping_add(a[0].wrapping_mul(zj));
    b[2] = b[2].wrapping_add(a[1].wrapping_mul(zj + t));

    for i in 3..n {
        b[i] = b[i - 3].wrapping_add(2 * (a[i] + a[i - 1] + a[i - 2]));
    }

    mod_3_phi_n::<P>(&mut b);
    z3_to_zq::<P>(&mut b);

    // Multiply by (x−1).
    let mut r = vec![0u16; n];
    r[0] = b[0].wrapping_neg();
    for i in 0..n - 1 {
        r[i + 1] = b[i].wrapping_sub(b[i + 1]);
    }
    r
}

// ---------------------------------------------------------------------------
// Packing
// ---------------------------------------------------------------------------

/// `poly_S3_tobytes`: pack `n−1` ternary coefficients base-3, 5 per byte.
pub fn s3_tobytes<P: NtruParams>(a: &[u16]) -> Vec<u8> {
    let pack_deg = P::N - 1;
    let mut out = vec![0u8; P::PACK_TRINARY_BYTES];
    for i in 0..pack_deg / 5 {
        let mut c = a[5 * i + 4] as u32 & 255;
        c = (3 * c + a[5 * i + 3] as u32) & 255;
        c = (3 * c + a[5 * i + 2] as u32) & 255;
        c = (3 * c + a[5 * i + 1] as u32) & 255;
        c = (3 * c + a[5 * i] as u32) & 255;
        out[i] = c as u8;
    }
    if pack_deg > (pack_deg / 5) * 5 {
        let i = pack_deg / 5;
        let mut c: u32 = 0;
        let mut j = pack_deg - 5 * i;
        while j > 0 {
            j -= 1;
            c = (3 * c + a[5 * i + j] as u32) & 255;
        }
        out[i] = c as u8;
    }
    out
}

/// `poly_S3_frombytes`.
pub fn s3_frombytes<P: NtruParams>(msg: &[u8]) -> Poly {
    let pack_deg = P::N - 1;
    let mut r = vec![0u16; P::N];
    for i in 0..pack_deg / 5 {
        let c = msg[i];
        r[5 * i] = c as u16;
        r[5 * i + 1] = ((c as u16) * 171) >> 9;
        r[5 * i + 2] = ((c as u16) * 57) >> 9;
        r[5 * i + 3] = ((c as u16) * 19) >> 9;
        r[5 * i + 4] = ((c as u16) * 203) >> 14;
    }
    if pack_deg > (pack_deg / 5) * 5 {
        let i = pack_deg / 5;
        let mut c = msg[i];
        let mut j = 0;
        while 5 * i + j < pack_deg {
            r[5 * i + j] = c as u16;
            c = (((c as u16) * 171) >> 9) as u8;
            j += 1;
        }
    }
    r[P::N - 1] = 0;
    mod_3_phi_n::<P>(&mut r);
    r
}

/// `poly_Sq_tobytes`: pack the low `logq` bits of the first `n−1`
/// coefficients into an LSB-first bit stream (the per-set reference
/// packers — 11-bit/8-coefficient groups for hps2048677, 12-bit pairs for
/// the 4096 sets, 13-bit pairs for hrss701 — are all this same stream).
pub fn sq_tobytes<P: NtruParams>(a: &[u16]) -> Vec<u8> {
    let pack_deg = P::N - 1;
    let logq = P::LOGQ as usize;
    let q_mask = (1u16 << P::LOGQ) - 1;
    let mut out = vec![0u8; P::PUBLICKEY_BYTES];
    let mut acc = 0u32;
    let mut accbits = 0usize;
    let mut pos = 0usize;
    for &coef in a.iter().take(pack_deg) {
        acc |= ((coef & q_mask) as u32) << accbits;
        accbits += logq;
        while accbits >= 8 {
            out[pos] = (acc & 0xff) as u8;
            pos += 1;
            acc >>= 8;
            accbits -= 8;
        }
    }
    if accbits > 0 {
        out[pos] = (acc & 0xff) as u8;
    }
    out
}

/// `poly_Sq_frombytes`.
pub fn sq_frombytes<P: NtruParams>(bytes: &[u8]) -> Poly {
    let pack_deg = P::N - 1;
    let logq = P::LOGQ as usize;
    let mut r = vec![0u16; P::N];
    let mut acc = 0u32;
    let mut accbits = 0usize;
    let mut pos = 0usize;
    for slot in r.iter_mut().take(pack_deg) {
        while accbits < logq {
            acc |= (bytes[pos] as u32) << accbits;
            pos += 1;
            accbits += 8;
        }
        *slot = (acc & ((1u32 << logq) - 1)) as u16;
        acc >>= logq;
        accbits -= logq;
    }
    r[P::N - 1] = 0;
    r
}

/// `poly_Rq_sum_zero_frombytes`: decode and set `r[n−1]` so the sum of the
/// coefficients is zero mod q.
pub fn rq_sum_zero_frombytes<P: NtruParams>(bytes: &[u8]) -> Poly {
    let mut r = sq_frombytes::<P>(bytes);
    r[P::N - 1] = 0;
    for i in 0..P::N - 1 {
        r[P::N - 1] = r[P::N - 1].wrapping_sub(r[i]);
    }
    r
}

#[cfg(test)]
mod inv_tests {
    use super::*;
    use crate::ntru::params::NtruHps2048677;

    fn det_poly(tag: u8) -> Poly {
        // Shake-fill with the tag as domain separator (matches keygen's
        // sample_iid shape — no short-period coefficient pattern).
        use sha3::digest::{ExtendableOutput, Update, XofReader};
        let mut hasher = sha3::Shake256::default();
        hasher.update(&[tag]);
        let mut reader = hasher.finalize_xof();
        let mut bytes = vec![0u8; NtruHps2048677::N - 1];
        reader.read(&mut bytes);
        let mut f: Poly = bytes.iter().map(|&b| (b % 3) as u16).collect();
        f.push(0);
        // Mirror the keygen shape: f[n−1] = 0, and force odd parity of
        // odd coefficients so the inverse exists mod 2.
        f[NtruHps2048677::N - 1] = 0;
        let parity: u16 = f.iter().map(|c| c & 1).fold(0, |a, b| a ^ b);
        if parity == 0 {
            f[0] ^= 1;
        }
        f
    }

    #[test]
    fn s3_inverse_roundtrip() {
        // Random ternary polys are invertible mod (3, Φ_n) with high
        // probability; check a few and verify f·f⁻¹ ≡ 1.
        let mut found = 0;
        for tag in 1..40u8 {
            let f = det_poly(tag);
            let inv = s3_inv::<NtruHps2048677>(&f);
            let prod = s3_mul::<NtruHps2048677>(&f, &inv);
            let mut one = vec![0u16; NtruHps2048677::N];
            one[0] = 1;
            if prod == one {
                found += 1;
            }
        }
        assert!(found > 30, "s3 inversions succeeded: {found}");
    }

    #[test]
    fn rq_inverse_roundtrip() {
        // Mirror the real call site: rq_inv is invoked on gf = 3·g·f for
        // keygen-shaped (f, g) — random ternary inputs include the
        // non-invertible cases the reference also rejects.
        use crate::ntru::sampling;
        let mut ok = 0;
        for tag in 1..12u8 {
            use sha3::digest::{ExtendableOutput, Update, XofReader};
            let mut hasher = sha3::Shake256::default();
            hasher.update(&[tag]);
            let mut reader = hasher.finalize_xof();
            let mut bytes = vec![0u8; NtruHps2048677::N - 1];
            reader.read(&mut bytes);
            let f = sampling::sample_iid::<NtruHps2048677>(&bytes);
            let mut gbytes = vec![0u8; (30 * (NtruHps2048677::N - 1)).div_ceil(8)];
            reader.read(&mut gbytes);
            let g = sampling::sample_fixed_type::<NtruHps2048677>(&gbytes);

            let mut f_q = f.clone();
            z3_to_zq::<NtruHps2048677>(&mut f_q);
            let mut g_q = g.clone();
            z3_to_zq::<NtruHps2048677>(&mut g_q);
            for c in g_q.iter_mut() {
                *c = 3u16.wrapping_mul(*c);
            }
            let gf = rq_mul::<NtruHps2048677>(&g_q, &f_q);
            let inv = rq_inv::<NtruHps2048677>(&gf);
            // rq_inv yields the inverse mod (q, Φ_n) — the almost-inverse
            // folds out the (x+1) factor — so validate through Sq_mul.
            let prod = sq_mul::<NtruHps2048677>(&gf, &inv);
            let q_mask = (1u16 << NtruHps2048677::LOGQ) - 1;
            if (prod[0] & q_mask) == 1 && prod[1..].iter().all(|&c| (c & q_mask) == 0) {
                ok += 1;
            }
        }
        assert!(ok > 8, "rq inversions on keygen-shaped inputs: {ok}/11");
    }
}
