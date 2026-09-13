//! Port of the Falcon reference `fft.c`: complex FFT over the splitting
//! field of `X^N + 1`, plus the polynomial helpers used by key generation
//! and signing. All arithmetic goes through the [`super::fpr`] soft-float.
//!
//! Layout invariant: a degree-n polynomial modulo X^n + 1 is held in n
//! `Fpr` slots organized as n/2 complex FFT points — index `u < n/2` is
//! the real part and index `u + n/2` the imaginary part of point `u`.
//! The twiddles come from `FPR_GM_TAB` as consecutive (re, im) pairs of
//! the roots of the FFT embedding (Z[X]/(X^n+1) ↪ C[X]/(X^(n/2) − i)),
//! indexed exactly the way [`fft`]/[`ifft`] consume them. Adjacency of
//! real/imaginary halves is what all the pointwise helpers below rely on.

use super::fpr::*;

/// Reference `FFT(f, logn)`.
pub fn fft(f: &mut [Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    let mut t = hn;
    let mut m: usize = 2;
    for _u in 1..logn {
        let ht = t >> 1;
        let hm = m >> 1;
        let mut j1 = 0usize;
        for i1 in 0..hm {
            let j2 = j1 + ht;
            let s_re = fpr_gm_tab((m + i1) << 1);
            let s_im = fpr_gm_tab(((m + i1) << 1) + 1);
            for j in j1..j2 {
                let (x_re, x_im) = (f[j], f[j + hn]);
                let (mut y_re, mut y_im) = (f[j + ht], f[j + ht + hn]);
                // y = y * s
                let d_re = fpr_sub(fpr_mul(y_re, s_re), fpr_mul(y_im, s_im));
                let d_im = fpr_add(fpr_mul(y_re, s_im), fpr_mul(y_im, s_re));
                y_re = d_re;
                y_im = d_im;
                // f[j] = x + y ; f[j+ht] = x - y
                f[j] = fpr_add(x_re, y_re);
                f[j + hn] = fpr_add(x_im, y_im);
                f[j + ht] = fpr_sub(x_re, y_re);
                f[j + ht + hn] = fpr_sub(x_im, y_im);
            }
            j1 += t;
        }
        t = ht;
        m <<= 1;
    }
}

/// Reference `iFFT(f, logn)`: inverse of [`fft`] (evaluation -> coefficient
/// form), ending with the 1/n scaling taken from `fpr_p2_tab`.
pub fn ifft(f: &mut [Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    let mut t = 1usize;
    let mut m = n;
    let mut u = logn;
    while u > 1 {
        let hm = m >> 1;
        let dt = t << 1;
        let mut i1 = 0usize;
        let mut j1 = 0usize;
        while j1 < hn {
            let j2 = j1 + t;
            let s_re = fpr_gm_tab((hm + i1) << 1);
            let s_im = fpr_neg(fpr_gm_tab(((hm + i1) << 1) + 1));
            for j in j1..j2 {
                let (x_re, x_im) = (f[j], f[j + hn]);
                let (y_re, y_im) = (f[j + t], f[j + t + hn]);
                f[j] = fpr_add(x_re, y_re);
                f[j + hn] = fpr_add(x_im, y_im);
                let xr = fpr_sub(x_re, y_re);
                let xi = fpr_sub(x_im, y_im);
                f[j + t] = fpr_sub(fpr_mul(xr, s_re), fpr_mul(xi, s_im));
                f[j + t + hn] = fpr_add(fpr_mul(xr, s_im), fpr_mul(xi, s_re));
            }
            i1 += 1;
            j1 += dt;
        }
        t = dt;
        m = hm;
        u -= 1;
    }
    if logn > 0 {
        let ni = fpr_p2_tab(logn as usize);
        for v in f.iter_mut().take(n) {
            *v = fpr_mul(*v, ni);
        }
    }
}

/// Reference `poly_adj_fft`: replace a by its adjoint a*(X) = a(−X) mod
/// (X^n + 1). In FFT representation the adjoint is the complex conjugate
/// of every point, i.e. negating all imaginary parts (the second half).
pub fn poly_adj_fft(a: &mut [Fpr], logn: u32) {
    let n = 1usize << logn;
    for v in a[n >> 1..n].iter_mut() {
        *v = fpr_neg(*v);
    }
}

/// Reference `poly_mul_fft`: a = a * b (FFT domain).
pub fn poly_mul_fft(a: &mut [Fpr], b: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let (a_re, a_im) = (a[u], a[u + hn]);
        let (b_re, b_im) = (b[u], b[u + hn]);
        a[u] = fpr_sub(fpr_mul(a_re, b_re), fpr_mul(a_im, b_im));
        a[u + hn] = fpr_add(fpr_mul(a_re, b_im), fpr_mul(a_im, b_re));
    }
}

/// Reference `poly_muladj_fft`: a = a * adj(b) (FFT domain).
pub fn poly_muladj_fft(a: &mut [Fpr], b: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let (a_re, a_im) = (a[u], a[u + hn]);
        let (b_re, b_im) = (b[u], fpr_neg(b[u + hn]));
        a[u] = fpr_sub(fpr_mul(a_re, b_re), fpr_mul(a_im, b_im));
        a[u + hn] = fpr_add(fpr_mul(a_re, b_im), fpr_mul(a_im, b_re));
    }
}

/// Reference `poly_mulselfadj_fft`: a = a * adj(a) (FFT domain).
pub fn poly_mulselfadj_fft(a: &mut [Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let (a_re, a_im) = (a[u], a[u + hn]);
        a[u] = fpr_add(fpr_sqr(a_re), fpr_sqr(a_im));
        a[u + hn] = FPR_ZERO;
    }
}

/// Reference `poly_mulconst`.
pub fn poly_mulconst(a: &mut [Fpr], x: Fpr, logn: u32) {
    let n = 1usize << logn;
    for v in a.iter_mut().take(n) {
        *v = fpr_mul(*v, x);
    }
}

/// Reference `poly_add`.
pub fn poly_add(a: &mut [Fpr], b: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    for u in 0..n {
        a[u] = fpr_add(a[u], b[u]);
    }
}

/// Reference `poly_sub`.
pub fn poly_sub(a: &mut [Fpr], b: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    for u in 0..n {
        a[u] = fpr_sub(a[u], b[u]);
    }
}

/// Reference `poly_div_fft`: a = a / b (FFT domain).
pub fn poly_div_fft(a: &mut [Fpr], b: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let (a_re, a_im) = (a[u], a[u + hn]);
        let (b_re, b_im) = (b[u], b[u + hn]);
        let m = fpr_inv(fpr_add(fpr_sqr(b_re), fpr_sqr(b_im)));
        let b_re = fpr_mul(b_re, m);
        let b_im = fpr_mul(fpr_neg(b_im), m);
        a[u] = fpr_sub(fpr_mul(a_re, b_re), fpr_mul(a_im, b_im));
        a[u + hn] = fpr_add(fpr_mul(a_re, b_im), fpr_mul(a_im, b_re));
    }
}

/// Reference `poly_invnorm2_fft`: d = 1/(a*adj(a) + b*adj(b)) (FFT domain).
pub fn poly_invnorm2_fft(d: &mut [Fpr], a: &[Fpr], b: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let (a_re, a_im) = (a[u], a[u + hn]);
        let (b_re, b_im) = (b[u], b[u + hn]);
        d[u] = fpr_inv(fpr_add(
            fpr_add(fpr_sqr(a_re), fpr_sqr(a_im)),
            fpr_add(fpr_sqr(b_re), fpr_sqr(b_im)),
        ));
    }
}

/// Reference `poly_mul_autoadj_fft` (auto-adjoint: imaginary half is zero).
pub fn poly_mul_autoadj_fft(a: &mut [Fpr], b: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        a[u] = fpr_mul(a[u], b[u]);
        a[u + hn] = fpr_mul(a[u + hn], b[u]);
    }
}

/// Reference `poly_div_autoadj_fft`.
pub fn poly_div_autoadj_fft(a: &mut [Fpr], b: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let ib = fpr_inv(b[u]);
        a[u] = fpr_mul(a[u], ib);
        a[u + hn] = fpr_mul(a[u + hn], ib);
    }
}

/// Reference `poly_ldl_fft`: in-place LDL decomposition of the Gram matrix
/// of the 2×2 hermitian system [[g00, g01], [adj(g01), g11]]: g00 is
/// overwritten with d00, g01 with l10 = g01/g00 and g11 with
/// d11 = g11 − l10·adj(g01) (using the original g01). Performed per FFT
/// point, hence still exact pointwise algebra.
pub fn poly_ldl_fft(g00: &mut [Fpr], g01: &mut [Fpr], g11: &mut [Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let (g00_re, g00_im) = (g00[u], g00[u + hn]);
        let (g01_re, g01_im) = (g01[u], g01[u + hn]);
        let (g11_re, g11_im) = (g11[u], g11[u + hn]);
        // mu = g01 / g00
        let m_norm = fpr_add(fpr_sqr(g00_re), fpr_sqr(g00_im));
        let m_inv = fpr_inv(m_norm);
        let b_re = fpr_mul(g00_re, m_inv);
        let b_im = fpr_mul(fpr_neg(g00_im), m_inv);
        let mu_re = fpr_sub(fpr_mul(g01_re, b_re), fpr_mul(g01_im, b_im));
        let mu_im = fpr_add(fpr_mul(g01_re, b_im), fpr_mul(g01_im, b_re));
        // g01 = mu * adj(g01)  (with the ORIGINAL g01 values)
        let t_re = fpr_sub(fpr_mul(mu_re, g01_re), fpr_mul(mu_im, fpr_neg(g01_im)));
        let t_im = fpr_add(fpr_mul(mu_re, fpr_neg(g01_im)), fpr_mul(mu_im, g01_re));
        g11[u] = fpr_sub(g11_re, t_re);
        g11[u + hn] = fpr_sub(g11_im, t_im);
        g01[u] = mu_re;
        g01[u + hn] = fpr_neg(mu_im);
    }
}

/// Reference `poly_LDLmv_fft`: LDL with separate outputs (d11, l10).
pub fn poly_ldlmv_fft(
    d11: &mut [Fpr],
    l10: &mut [Fpr],
    g00: &[Fpr],
    g01: &[Fpr],
    g11: &[Fpr],
    logn: u32,
) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let (g00_re, g00_im) = (g00[u], g00[u + hn]);
        let (g01_re, g01_im) = (g01[u], g01[u + hn]);
        let (g11_re, g11_im) = (g11[u], g11[u + hn]);
        let m_norm = fpr_add(fpr_sqr(g00_re), fpr_sqr(g00_im));
        let m_inv = fpr_inv(m_norm);
        let b_re = fpr_mul(g00_re, m_inv);
        let b_im = fpr_mul(fpr_neg(g00_im), m_inv);
        let mu_re = fpr_sub(fpr_mul(g01_re, b_re), fpr_mul(g01_im, b_im));
        let mu_im = fpr_add(fpr_mul(g01_re, b_im), fpr_mul(g01_im, b_re));
        let t_re = fpr_sub(fpr_mul(mu_re, g01_re), fpr_mul(mu_im, fpr_neg(g01_im)));
        let t_im = fpr_add(fpr_mul(mu_re, fpr_neg(g01_im)), fpr_mul(mu_im, g01_re));
        d11[u] = fpr_sub(g11_re, t_re);
        d11[u + hn] = fpr_sub(g11_im, t_im);
        l10[u] = mu_re;
        l10[u + hn] = fpr_neg(mu_im);
    }
}

/// Reference `poly_neg`.
pub fn poly_neg(a: &mut [Fpr], logn: u32) {
    let n = 1usize << logn;
    for v in a.iter_mut().take(n) {
        *v = fpr_neg(*v);
    }
}

/// Reference `poly_add_muladj_fft`: d = F·adj(f) + G·adj(g) (FFT domain).
pub fn poly_add_muladj_fft(
    d: &mut [Fpr],
    big_f: &[Fpr],
    big_g: &[Fpr],
    f: &[Fpr],
    g: &[Fpr],
    logn: u32,
) {
    let n = 1usize << logn;
    let hn = n >> 1;
    for u in 0..hn {
        let (f_re, f_im) = (big_f[u], big_f[u + hn]);
        let (g_re, g_im) = (big_g[u], big_g[u + hn]);
        let (ff_re, ff_im) = (f[u], f[u + hn]);
        let (gg_re, gg_im) = (g[u], g[u + hn]);
        // a = F * adj(f)
        let a_re = fpr_sub(fpr_mul(f_re, ff_re), fpr_mul(f_im, fpr_neg(ff_im)));
        let a_im = fpr_add(fpr_mul(f_re, fpr_neg(ff_im)), fpr_mul(f_im, ff_re));
        // b = G * adj(g)
        let b_re = fpr_sub(fpr_mul(g_re, gg_re), fpr_mul(g_im, fpr_neg(gg_im)));
        let b_im = fpr_add(fpr_mul(g_re, fpr_neg(gg_im)), fpr_mul(g_im, gg_re));
        d[u] = fpr_add(a_re, b_re);
        d[u + hn] = fpr_add(a_im, b_im);
    }
}

/// Reference `poly_split_fft`.
pub fn poly_split_fft(f0: &mut [Fpr], f1: &mut [Fpr], f: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    let qn = hn >> 1;
    f0[0] = f[0];
    f1[0] = f[hn];
    for u in 0..qn {
        let (a_re, a_im) = (f[u << 1], f[(u << 1) + hn]);
        let (b_re, b_im) = (f[(u << 1) + 1], f[(u << 1) + 1 + hn]);
        let t_re = fpr_add(a_re, b_re);
        let t_im = fpr_add(a_im, b_im);
        f0[u] = fpr_half(t_re);
        f0[u + qn] = fpr_half(t_im);
        let c_re = fpr_sub(a_re, b_re);
        let c_im = fpr_sub(a_im, b_im);
        let s_re = fpr_gm_tab((u + hn) << 1);
        let s_im = fpr_neg(fpr_gm_tab(((u + hn) << 1) + 1));
        let t_re = fpr_sub(fpr_mul(c_re, s_re), fpr_mul(c_im, s_im));
        let t_im = fpr_add(fpr_mul(c_re, s_im), fpr_mul(c_im, s_re));
        f1[u] = fpr_half(t_re);
        f1[u + qn] = fpr_half(t_im);
    }
}

/// Reference `poly_merge_fft`.
pub fn poly_merge_fft(f: &mut [Fpr], f0: &[Fpr], f1: &[Fpr], logn: u32) {
    let n = 1usize << logn;
    let hn = n >> 1;
    let qn = hn >> 1;
    f[0] = f0[0];
    f[hn] = f1[0];
    for u in 0..qn {
        let (a_re, a_im) = (f0[u], f0[u + qn]);
        let s_re = fpr_gm_tab((u + hn) << 1);
        let s_im = fpr_gm_tab(((u + hn) << 1) + 1);
        let b_re = fpr_sub(fpr_mul(f1[u], s_re), fpr_mul(f1[u + qn], s_im));
        let b_im = fpr_add(fpr_mul(f1[u], s_im), fpr_mul(f1[u + qn], s_re));
        let t_re = fpr_add(a_re, b_re);
        let t_im = fpr_add(a_im, b_im);
        f[u << 1] = t_re;
        f[(u << 1) + hn] = t_im;
        let t_re = fpr_sub(a_re, b_re);
        let t_im = fpr_sub(a_im, b_im);
        f[(u << 1) + 1] = t_re;
        f[(u << 1) + 1 + hn] = t_im;
    }
}
