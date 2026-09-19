//! Port of the Falcon reference `sign.c`: Fast Fourier sampling and the
//! signature loop (`do_sign_dyn` + `sign_dyn`).
//!
//! The reference C code passes overlapping raw pointers (quasi-cyclic
//! matrix halves sharing one buffer). Here the callee-visible regions are
//! materialized as fresh buffers at each recursion; the reference discards
//! those regions after the recursive call, so the value semantics are
//! identical and the floating-point operation sequence is unchanged.

use super::common::is_short_half;
use super::fpr::*;
use super::prng::Prng;
use alloc::vec;

/// Reference `smallints_to_fpr`.
fn smallints_to_fpr(r: &mut [Fpr], t: &[i8]) {
    for (dst, &src) in r.iter_mut().zip(t.iter()) {
        *dst = fpr_of(src as i64);
    }
}

/// Reference `samplerZ` context: sigma_min plus the ChaCha20 PRNG.
pub struct SamplerCtx {
    sigma_min: Fpr,
    p: Prng,
}

/// Reference `gaussian0_sampler`: half-Gaussian centered on 0 with
/// σ = 1.8205, sampled at 72-bit precision.
fn gaussian0_sampler(p: &mut Prng) -> i32 {
    const DIST: [u32; 54] = [
        10745844, 3068844, 3741698, 5559083, 1580863, 8248194, 2260429, 13669192, 2736639, 708981,
        4421575, 10046180, 169348, 7122675, 4136815, 30538, 13063405, 7650655, 4132, 14505003,
        7826148, 417, 16768101, 11363290, 31, 8444042, 8086568, 1, 12844466, 265321, 0, 1232676,
        13644283, 0, 38047, 9111839, 0, 870, 6138264, 0, 14, 12545723, 0, 0, 3104126, 0, 0, 28824,
        0, 0, 198, 0, 0, 1,
    ];

    let lo = p.get_u64();
    let hi = p.get_u8() as u32;
    let v0 = lo as u32 & 0xFF_FFFF;
    let v1 = ((lo >> 24) as u32) & 0xFF_FFFF;
    let v2 = ((lo >> 48) as u32) | (hi << 16);

    // DIST packs 18 consecutive 72-bit thresholds as triples of three
    // 24-bit lanes (big-endian: DIST[u] is the most significant lane). The
    // loop borrow-chains the 72-bit draw through the comparisons and
    // counts, branchlessly, how many thresholds the draw stays under.
    let mut z: i32 = 0;
    let mut u = 0usize;
    while u < DIST.len() {
        let w0 = DIST[u + 2];
        let w1 = DIST[u + 1];
        let w2 = DIST[u];
        let mut cc = (v0.wrapping_sub(w0)) >> 31;
        cc = (v1.wrapping_sub(w1).wrapping_sub(cc)) >> 31;
        cc = (v2.wrapping_sub(w2).wrapping_sub(cc)) >> 31;
        z += cc as i32;
        u += 3;
    }
    z
}

/// Reference `BerExp`: Bernoulli variable with parameter exp(-x).
fn berexp(p: &mut Prng, x: Fpr, ccs: Fpr) -> i32 {
    // Reduce x modulo log(2): x = s·log(2) + r, 0 <= r < log(2).
    let mut s = fpr_trunc(fpr_mul(x, FPR_INV_LOG2)) as i32;
    let r = fpr_sub(x, fpr_mul(fpr_of(s as i64), FPR_LOG2));

    // Saturate s at 63.
    let sw = (s as u32)
        ^ ((s as u32 ^ 63) & ((((63u32.wrapping_sub(s as u32)) >> 31) != 0) as u32).wrapping_neg());
    s = sw as i32;

    // exp(-r) scaled to 2^63, up to 2^64, right-shifted by s.
    let z = ((fpr_expm_p63(r, ccs) << 1).wrapping_sub(1)) >> s;

    // Lazy byte-comparison with the PRNG output.
    let mut i: i32 = 64;
    let mut w: u32;
    loop {
        i -= 8;
        w = (p.get_u8() as u32).wrapping_sub(((z >> i) as u32) & 0xFF);
        if !(w == 0 && i > 0) {
            break;
        }
    }
    (w >> 31) as i32
}

/// Reference `sampler`: discrete Gaussian centered on mu with standard
/// deviation sigma (given via isigma = 1/sigma, 1.2 <= sigma <= 1.9).
pub fn sampler(spc: &mut SamplerCtx, mu: Fpr, isigma: Fpr) -> i32 {
    // mu = s + r with s integer and 0 <= r < 1.
    let s = fpr_floor(mu) as i32;
    let r = fpr_sub(mu, fpr_of(s as i64));

    // dss = 1/(2·sigma²); ccs = sigma_min / sigma.
    let dss = fpr_half(fpr_sqr(isigma));
    let ccs = fpr_mul(isigma, spc.sigma_min);

    loop {
        // Bimodal base sample: z = b + (2b−1)·z0.
        let z0 = gaussian0_sampler(&mut spc.p);
        let b = (spc.p.get_u8() & 1) as i32;
        let z = b + ((b << 1) - 1) * z0;

        // Rejection: keep z with probability exp(-x).
        let mut x = fpr_mul(fpr_sqr(fpr_sub(fpr_of(z as i64), r)), dss);
        x = fpr_sub(x, fpr_mul(fpr_of((z0 * z0) as i64), FPR_INV_2SQRSIGMA0));
        if berexp(&mut spc.p, x, ccs) != 0 {
            return s + z;
        }
    }
}

/// Reference `ffSampling_fft_dyntree` (Fast Fourier sampling over the LDL
/// levels of the Gram matrix, computed on the fly rather than from a
/// precomputed tree). Each level LDL-decomposes the 2×2 Gram system,
/// splits the d00/d11 polynomials to the two half-size sub-trees, samples
/// the right child first, propagates the correction t0 += (t1 − z1)·l10
/// through the FFT embedding, then samples the left child. At the leaf
/// (logn 0) both coordinates are sampled directly with
/// sigma = sqrt(g00[0])·FPR_INV_SIGMA[orig_logn].
#[allow(clippy::too_many_arguments)]
fn ffsampling_dyntree(
    spc: &mut SamplerCtx,
    t0: &mut [Fpr],
    t1: &mut [Fpr],
    g00: &mut [Fpr],
    g01: &mut [Fpr],
    g11: &mut [Fpr],
    orig_logn: u32,
    logn: u32,
    tmp: &mut [Fpr],
) {
    if logn == 0 {
        // Deepest level: the leaf is g00[0], normalized by sigma.
        let leaf = fpr_mul(fpr_sqrt(g00[0]), FPR_INV_SIGMA[orig_logn as usize]);
        t0[0] = fpr_of(sampler(spc, t0[0], leaf) as i64);
        t1[0] = fpr_of(sampler(spc, t1[0], leaf) as i64);
        return;
    }

    let n = 1usize << logn;
    let hn = n >> 1;

    // LDL decomposition in place: g00 keeps d00, g01 gets l10, g11 gets d11.
    super::fft::poly_ldl_fft(g00, g01, g11, logn);

    // Split d00 and d11; save l10 in tmp.
    {
        let g00c = g00.to_vec();
        let (ta, tb) = tmp.split_at_mut(hn);
        super::fft::poly_split_fft(ta, &mut tb[..hn], &g00c, logn);
        g00.copy_from_slice(&tmp[..n]);
        let g11c = g11.to_vec();
        let (ta, tb) = tmp.split_at_mut(hn);
        super::fft::poly_split_fft(ta, &mut tb[..hn], &g11c, logn);
        g11.copy_from_slice(&tmp[..n]);
        let g01c = g01.to_vec();
        tmp[..n].copy_from_slice(&g01c);
        g01[..hn].copy_from_slice(&g00[..hn]);
        g01[hn..n].copy_from_slice(&g11[..hn]);
    }
    // Left sub-tree Gram: (g00, g00+hn as g01-slot, g01 as g11-slot)
    //   materialized: lg00 = g00[0..hn] (real) — the callee at logn-1 reads
    //   its g00 = [g00[..hn], g00[hn..n]] and its g11 = g01[..hn] etc.
    // Following the reference pointers exactly:
    //   left  callee(g00 = &g00[..], g01 = &g00[hn..], g11 = &g01[..])
    //   right callee(g00 = &g11[..], g01 = &g11[hn..], g11 = &g01[hn..])
    // Each callee touches: g00[..n/2], g01[0..n/4] (into g00's tail), g11[0..n/4].

    // Split t1; right recursion on the right sub-tree; merge into tmp[2n..].
    let mut z1 = tmp[n..2 * n].to_vec();
    {
        let t1c = t1.to_vec();
        let (za, zb) = z1.split_at_mut(hn);
        super::fft::poly_split_fft(za, zb, &t1c, logn);
    }
    {
        // Right sub-tree materialization (half-degree: hn words each).
        let mut r_g00 = g11[..hn].to_vec();
        let mut r_g01 = g11[hn..n].to_vec();
        let mut r_g11 = g01[hn..n].to_vec();
        let mut r_tmp = vec![0u64; 3 * hn];
        let (za, zb) = z1.split_at_mut(hn);
        ffsampling_dyntree(
            spc,
            za,
            zb,
            &mut r_g00,
            &mut r_g01,
            &mut r_g11,
            orig_logn,
            logn - 1,
            &mut r_tmp,
        );
    }
    {
        let z1c = z1.to_vec();
        super::fft::poly_merge_fft(&mut tmp[2 * n..3 * n], &z1c[..hn], &z1c[hn..n], logn);
    }

    // tb0 = t0 + (t1 - z1) * l10 (l10 in tmp, merged z1 in tmp[2n..3n]).
    {
        let t1c = t1.to_vec();
        z1.copy_from_slice(&t1c);
        let z1m = tmp[2 * n..3 * n].to_vec();
        super::fft::poly_sub(&mut z1, &z1m, logn);
        t1.copy_from_slice(&tmp[2 * n..3 * n]);
        let z1c = z1.to_vec();
        super::fft::poly_mul_fft(&mut tmp[..n], &z1c, logn);
        super::fft::poly_add(t0, &tmp[..n], logn);
    }

    // Left recursion on the split tb0 and the left sub-tree.
    let mut z0 = tmp[..n].to_vec();
    {
        let t0c = t0.to_vec();
        let (za, zb) = z0.split_at_mut(hn);
        super::fft::poly_split_fft(za, zb, &t0c, logn);
    }
    {
        let mut l_g00 = g00[..hn].to_vec();
        let mut l_g01 = g00[hn..n].to_vec();
        let mut l_g11 = g01[..hn].to_vec();
        let (za, zb) = z0.split_at_mut(hn);
        let mut ztmp = vec![0u64; 3 * hn];
        ffsampling_dyntree(
            spc,
            za,
            zb,
            &mut l_g00,
            &mut l_g01,
            &mut l_g11,
            orig_logn,
            logn - 1,
            &mut ztmp,
        );
    }
    {
        let z0c = z0.to_vec();
        super::fft::poly_merge_fft(t0, &z0c[..hn], &z0c[hn..n], logn);
    }
}

/// Reference `do_sign_dyn` + `sign_dyn` with the rejection loop. Every
/// attempt seeds a fresh ChaCha20 sampler from `rng` (56 bytes, exactly
/// like the reference), builds the target from the hash point `hm`, draws
/// (t0, t1) by FFT sampling over the on-the-fly Gram LDL tree, and accepts
/// the first (s1, s2) = (hm − ⌊t0⌉, −⌊t1⌉) whose squared norm passes
/// `is_short_half` (‖(s1, s2)‖² ≤ beta², beta from the spec). Only s2 is
/// written to `sig`; the verifier recomputes s2·h − c ≡ −s1.
#[allow(clippy::too_many_arguments)]
pub fn sign_dyn(
    sig: &mut [i16],
    rng: &mut super::common::InnerShake256,
    f: &[i8],
    g: &[i8],
    big_f: &[i8],
    big_g: &[i8],
    hm: &[u16],
    logn: u32,
) {
    let n = 1usize << logn;

    loop {
        let mut spc = SamplerCtx {
            sigma_min: FPR_SIGMA_MIN[logn as usize],
            p: Prng::init(rng),
        };

        // Lattice basis B = [[g, -f], [G, -F]] in FFT domain.
        let mut b00 = vec![0u64; n];
        let mut b01 = vec![0u64; n];
        let mut b10 = vec![0u64; n];
        let mut b11 = vec![0u64; n];
        smallints_to_fpr(&mut b01, f);
        smallints_to_fpr(&mut b00, g);
        smallints_to_fpr(&mut b11, big_f);
        smallints_to_fpr(&mut b10, big_g);
        super::fft::fft(&mut b01, logn);
        super::fft::fft(&mut b00, logn);
        super::fft::fft(&mut b11, logn);
        super::fft::fft(&mut b10, logn);
        super::fft::poly_neg(&mut b01, logn);
        super::fft::poly_neg(&mut b11, logn);

        // Gram matrix (upper triangle). The original b01 (-f in FFT) must
        // survive the Gram overwrite: like the reference, it is saved into
        // t0 and used for the target vector below.
        let mut t0 = vec![0u64; n];
        let mut t1 = vec![0u64; n];
        t0.copy_from_slice(&b01);
        super::fft::poly_mulselfadj_fft(&mut t0, logn);
        t1.copy_from_slice(&b00);
        super::fft::poly_muladj_fft(&mut t1, &b10, logn);
        super::fft::poly_mulselfadj_fft(&mut b00, logn);
        super::fft::poly_add(&mut b00, &t0, logn);
        t0.copy_from_slice(&b01);
        super::fft::poly_muladj_fft(&mut b01, &b11, logn);
        super::fft::poly_add(&mut b01, &t1, logn);
        super::fft::poly_mulselfadj_fft(&mut b10, logn);
        t1.copy_from_slice(&b11);
        super::fft::poly_mulselfadj_fft(&mut t1, logn);
        super::fft::poly_add(&mut b10, &t1, logn);
        // b01 now holds g01; the original b01 lives on in t0.
        let b01_orig = t0.clone();

        // Target vector [hm, 0], then the basis application.
        for u in 0..n {
            t0[u] = fpr_of(hm[u] as i64);
        }
        super::fft::fft(&mut t0, logn);
        let ni = FPR_INVERSE_OF_Q;
        t1.copy_from_slice(&t0);
        super::fft::poly_mul_fft(&mut t1, &b01_orig, logn);
        super::fft::poly_mulconst(&mut t1, fpr_neg(ni), logn);
        super::fft::poly_mul_fft(&mut t0, &b11, logn);
        super::fft::poly_mulconst(&mut t0, ni, logn);

        // Sampling (dyntree over the Gram matrix).
        {
            let mut g00 = b00.clone();
            let mut g01 = b01.clone();
            let mut g11 = b10.clone();
            let mut tmp = vec![0u64; n * 4];
            ffsampling_dyntree(
                &mut spc, &mut t0, &mut t1, &mut g00, &mut g01, &mut g11, logn, logn, &mut tmp,
            );
        }

        // Lattice point: (s1, s2) = (t − y)·B. The basis B was overwritten
        // by the Gram matrix above, so — exactly like the reference — it is
        // recomputed from f, g, F, G now.
        let mut b00 = vec![0u64; n];
        let mut b01 = vec![0u64; n];
        let mut b10 = vec![0u64; n];
        let mut b11 = vec![0u64; n];
        smallints_to_fpr(&mut b01, f);
        smallints_to_fpr(&mut b00, g);
        smallints_to_fpr(&mut b11, big_f);
        smallints_to_fpr(&mut b10, big_g);
        super::fft::fft(&mut b01, logn);
        super::fft::fft(&mut b00, logn);
        super::fft::fft(&mut b11, logn);
        super::fft::fft(&mut b10, logn);
        super::fft::poly_neg(&mut b01, logn);
        super::fft::poly_neg(&mut b11, logn);

        let mut tx = vec![0u64; n];
        let mut ty = vec![0u64; n];
        tx.copy_from_slice(&t0);
        ty.copy_from_slice(&t1);
        super::fft::poly_mul_fft(&mut tx, &b00, logn);
        super::fft::poly_mul_fft(&mut ty, &b10, logn);
        super::fft::poly_add(&mut tx, &ty, logn);
        ty.copy_from_slice(&t0);
        super::fft::poly_mul_fft(&mut ty, &b01, logn);
        t0.copy_from_slice(&tx);
        super::fft::poly_mul_fft(&mut t1, &b11, logn);
        super::fft::poly_add(&mut t1, &ty, logn);
        super::fft::ifft(&mut t0, logn);
        super::fft::ifft(&mut t1, logn);

        // s1 = hm − round(t0); norm test decides acceptance.
        let mut s1tmp = vec![0i16; n];
        let mut sqn: u32 = 0;
        let mut ng: u32 = 0;
        for u in 0..n {
            let z = hm[u] as i32 - fpr_rint(t0[u]) as i32;
            sqn = sqn.wrapping_add((z * z) as u32);
            ng |= sqn;
            s1tmp[u] = z as i16;
        }
        sqn |= (ng >> 31).wrapping_neg();

        let mut s2tmp = vec![0i16; n];
        for u in 0..n {
            s2tmp[u] = -(fpr_rint(t1[u]) as i16);
        }
        if is_short_half(sqn, &s2tmp, logn) {
            sig.copy_from_slice(&s2tmp);
            return;
        }
    }
}
