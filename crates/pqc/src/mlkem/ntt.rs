//! The FIPS 203 number-theoretic transform, byte-exact with the
//! specification.
//!
//! `q = 3329` has 2-adicity 7 < 8, so `X^256 + 1` does not split into linear
//! factors: the transform has seven butterfly layers and lands in 128 pairs
//! of coefficients, where the i-th pair lives in `Y^2 − ζ^(2·brv7(i)+1)`
//! (multiplication needs the spec's `BaseCaseMultiply`). This is why the
//! generic [`algebra::ntt`] engine cannot serve ML-KEM and the scheme carries
//! its own transform, exactly like [`crate::mldsa::ntt`] does for FIPS 204.
//!
//! Conventions (FIPS 203, §4.3):
//! - forward: Cooley–Tukey butterflies with `Zetas[i] = ζ^brv7(i)`,
//!   consumed layer-by-layer exactly like the spec pseudocode;
//! - the last layer (len = 2) splits into the `Y^2 − γ` pairs, so the
//!   inverse transform scales by `128⁻¹`, not `256⁻¹`;
//! - `Â` entries from `ExpandA` are stored as raw `SampleNTT` values, which
//!   are NTT-domain coefficients under precisely this convention.
//!
//! All arithmetic is modular over `u64` representatives in `[0, q)`.

use super::params::{N, Q, T_ZETA};
use algebra::crypto::xof::Xof;

const Q_U64: u64 = Q;

#[inline]
pub(crate) fn mul_mod(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % Q_U64 as u128) as u64
}

/// `base^exp mod q` by square-and-multiply (const-evaluable; the exponents
/// used at table build time are compile-time constants).
const fn pow_mod(mut base: u64, mut exp: u64) -> u64 {
    let mut acc: u64 = 1;
    base %= Q_U64;
    while exp > 0 {
        if exp & 1 == 1 {
            acc = ((acc as u128 * base as u128) % Q_U64 as u128) as u64;
        }
        base = ((base as u128 * base as u128) % Q_U64 as u128) as u64;
        exp >>= 1;
    }
    acc
}

/// 7-bit bit-reversal (FIPS 203 `Brv7`: the deepest layer of the transform
/// tree has 128 nodes, so twiddle indices are 7-bit reversed).
const fn bit_rev7(i: usize) -> u64 {
    let mut rev = 0u64;
    let mut val = i as u64;
    let mut bits = 7;
    while bits > 0 {
        rev = (rev << 1) | (val & 1);
        val >>= 1;
        bits -= 1;
    }
    rev
}

/// Forward twiddles: `ZETAS[i] = ζ^brv7(i)` for `i ∈ [0, 128)`.
const ZETAS: [u64; 128] = {
    let mut table = [0u64; 128];
    let mut i = 0;
    while i < 128 {
        table[i] = pow_mod(T_ZETA, bit_rev7(i));
        i += 1;
    }
    table
};

/// Twiddles for `MultiplyNTTs`: `MUL_ZETAS[i] = ζ^(2·brv7(i)+1)` — the
/// constant of the quadratic factor `Y^2 − MUL_ZETAS[i]` hosting pair `i`.
const MUL_ZETAS: [u64; 128] = {
    let mut table = [0u64; 128];
    let mut i = 0;
    while i < 128 {
        table[i] = pow_mod(T_ZETA, 2 * bit_rev7(i) + 1);
        i += 1;
    }
    table
};

/// `128⁻¹ mod q` (the inverse NTT of FIPS 203 has seven layers).
const HALF_N_INV: u64 = pow_mod((N / 2) as u64, Q - 2);

/// FIPS 203 NTT (forward): coefficients in `[0, q)` → NTT-domain values in
/// seven butterfly layers; the output is 128 pairs in the spec's layout.
pub fn ntt(a: &mut [u64; N]) {
    let mut i = 1usize;
    let mut len = N / 2;
    while len >= 2 {
        let mut start = 0;
        while start < N {
            let zeta = ZETAS[i];
            i += 1;
            for j in start..start + len {
                let t = mul_mod(zeta, a[j + len]);
                a[j + len] = (a[j] + Q_U64 - t) % Q_U64;
                a[j] = (a[j] + t) % Q_U64;
            }
            start += 2 * len;
        }
        len >>= 1;
    }
}

/// FIPS 203 inverse NTT (Algorithm 10): it consumes the SAME plain `Zetas`
/// table (`ζ^brv7(i)`, `i` starting at 127 and descending) — NOT inverted
/// twiddles; the descending traversal is what supplies the twiddle inverses.
/// The result is finally scaled by `128⁻¹ = 3303`, not `256⁻¹` (seven
/// layers, see below).
pub fn intt(a: &mut [u64; N]) {
    let mut i = 127usize;
    let mut len = 2;
    while len <= N / 2 {
        let mut start = 0;
        while start < N {
            let zeta = ZETAS[i];
            i -= 1;
            for j in start..start + len {
                let t = a[j];
                let u = a[j + len];
                a[j] = (t + u) % Q_U64;
                // Second update is zeta·(f[j+len] − t) = zeta·(u − t):
                // u MINUS t, not t − u. A flipped sign here still passes a
                // casual read of Algorithm 10 yet silently breaks
                // byte-exactness against the ACVP vectors.
                let du = (u + Q_U64 - t) % Q_U64;
                a[j + len] = mul_mod(du, zeta);
            }
            start += 2 * len;
        }
        len <<= 1;
    }
    // Seven layers ⇒ the last one already split into 128 quadratic pairs,
    // so the inverse scales by 128⁻¹ = 3303 mod q (NOT 256⁻¹).
    for c in a.iter_mut() {
        *c = mul_mod(*c, HALF_N_INV);
    }
}

/// FIPS 203 `MultiplyNTTs` — pointwise product in the NTT domain. Pair `i`
/// multiplies modulo `Y^2 − MUL_ZETAS[i]` (spec `BaseCaseMultiply`).
pub fn mul_ntts(a: &[u64; N], b: &[u64; N]) -> [u64; N] {
    let mut c = [0u64; N];
    for i in 0..N / 2 {
        let (a0, a1) = (a[2 * i], a[2 * i + 1]);
        let (b0, b1) = (b[2 * i], b[2 * i + 1]);
        c[2 * i] = (mul_mod(a0, b0) + mul_mod(mul_mod(a1, b1), MUL_ZETAS[i])) % Q_U64;
        c[2 * i + 1] = (mul_mod(a0, b1) + mul_mod(a1, b0)) % Q_U64;
    }
    c
}

/// NTT-domain inner-product step: `acc += a ⊗ b` in `T_q`. Unlike ML-DSA's
/// linear-factor layout, each of the 128 pairs multiplies modulo
/// `Y^2 − MUL_ZETAS[i]` (spec `BaseCaseMultiply`), so this is *not* a plain
/// coefficient-wise product.
pub fn pointwise_mul_add(acc: &mut [u64; N], a: &[u64; N], b: &[u64; N]) {
    for i in 0..N / 2 {
        let (a0, a1) = (a[2 * i], a[2 * i + 1]);
        let (b0, b1) = (b[2 * i], b[2 * i + 1]);
        acc[2 * i] =
            (acc[2 * i] + mul_mod(a0, b0) + mul_mod(mul_mod(a1, b1), MUL_ZETAS[i])) % Q_U64;
        acc[2 * i + 1] = (acc[2 * i + 1] + mul_mod(a0, b1) + mul_mod(a1, b0)) % Q_U64;
    }
}

/// FIPS 203 `SampleNTT`: 256 uniform coefficients in `[0, q)` from 12-bit
/// little-endian draws with rejection (`d ≥ q` is discarded).
fn sample_ntt<X: Xof>(rho: &[u8; 32], col: u8, row: u8) -> [u64; N] {
    let mut xof = X::new(&[]);
    xof.absorb(rho);
    xof.absorb(&[col, row]);
    let mut out = [0u64; N];
    let mut pos = 0;
    while pos < N {
        let mut buf = [0u8; 3];
        xof.squeeze(&mut buf);
        // Algorithm 7 reads a contiguous 12-bit little-endian stream, three
        // bytes per two candidates: d1 = C[0] + 256·(C[1] mod 16),
        // d2 = ⌊C[1]/16⌋ + 16·C[2]. A candidate with d ≥ q is rejected.
        let d1 = buf[0] as u64 + 256 * (buf[1] as u64 & 0x0F);
        let d2 = (buf[1] >> 4) as u64 + 16 * buf[2] as u64;
        if d1 < Q {
            out[pos] = d1;
            pos += 1;
        }
        if pos < N && d2 < Q {
            out[pos] = d2;
            pos += 1;
        }
    }
    out
}

/// FIPS 203 `ExpandA(ρ)`: builds the `K×K` matrix `Â` directly in the NTT
/// domain. Entry `(row, col)` is `SampleNTT(XOF(ρ ‖ bytes(col) ‖ bytes(row)))`
/// — the column index is absorbed first, per the spec.
///
/// Like ML-DSA's `ExpandA`, the `K²` streams are deliberately *not*
/// parallelized: each is a few microseconds of SHAKE, so per-stream task
/// dispatch costs more than it saves.
pub(crate) fn expand_a<X: Xof, const K: usize>(rho: &[u8; 32]) -> [[[u64; N]; K]; K] {
    let mut out = [[[0u64; N]; K]; K];
    for (r, row) in out.iter_mut().enumerate() {
        for (c, entry) in row.iter_mut().enumerate() {
            *entry = sample_ntt::<X>(rho, c as u8, r as u8);
        }
    }
    out
}

/// Maps centered coefficient representatives (any `i64`) into `[0, q)` and
/// applies the forward NTT.
pub fn ntt_coeffs(coeffs: &[i64; N]) -> [u64; N] {
    let mut out = [0u64; N];
    for (dst, &src) in out.iter_mut().zip(coeffs.iter()) {
        *dst = src.rem_euclid(Q as i64) as u64;
    }
    ntt(&mut out);
    out
}

/// Applies the inverse NTT, yielding coefficient representatives in
/// `[0, q)`.
pub fn intt_coeffs(values: &[u64; N]) -> [i64; N] {
    let mut out = *values;
    intt(&mut out);
    out.map(|v| v as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_coeffs(seed: u64) -> [i64; N] {
        let mut state = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
        std::array::from_fn(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state % (2 * Q)) as i64 - Q as i64
        })
    }

    #[test]
    fn zeta_has_order_256() {
        // q − 1 = 2^7·26, so the 2-adicity is 7: ζ must have order exactly
        // 256 (ζ^128 = −1) — which is why the transform has seven layers
        // and the last one splits into quadratic factors.
        assert_eq!(pow_mod(T_ZETA, (N / 2) as u64), Q_U64 - 1);
        assert_ne!(pow_mod(T_ZETA, (N / 4) as u64), Q_U64 - 1);
        assert_eq!(pow_mod(T_ZETA, N as u64), 1);
        assert_eq!(HALF_N_INV, 3303, "128⁻¹ mod 3329");
    }

    #[test]
    fn mul_zetas_are_distinct_odd_powers() {
        // The 128 constants must be exactly the odd powers ζ^1, ζ^3, …, ζ^255
        // (the roots of X^256 + 1), each once — otherwise pairs would not
        // cover the ring.
        let mut seen = [false; 128];
        for &g in MUL_ZETAS.iter() {
            let mut e = 0u64;
            let mut base = 1u64;
            loop {
                if base == g {
                    break;
                }
                base = mul_mod(base, T_ZETA);
                e += 1;
                assert!(e < 256);
            }
            assert!(e % 2 == 1, "MUL_ZETAS entry {g} is not an odd power");
            assert!(!seen[(e / 2) as usize], "odd power ζ^{e} duplicated");
            seen[(e / 2) as usize] = true;
        }
    }

    #[test]
    fn roundtrip_and_range() {
        for seed in 0..8u64 {
            let f = sample_coeffs(seed);
            let hat = ntt_coeffs(&f);
            assert!(hat.iter().all(|&v| v < Q));
            let back = intt_coeffs(&hat);
            assert_eq!(
                back,
                f.map(|c| c.rem_euclid(Q as i64)),
                "intt∘ntt must be identity"
            );
        }
    }

    #[test]
    fn homomorphism_and_negacyclic_product() {
        for seed in 0..4u64 {
            let f = sample_coeffs(seed);
            let g = sample_coeffs(seed + 100);
            let f_hat = ntt_coeffs(&f);
            let g_hat = ntt_coeffs(&g);
            // Negacyclic product via MultiplyNTTs must equal schoolbook
            // f·g mod (x^256 + 1).
            let prod_hat = mul_ntts(&f_hat, &g_hat);
            let prod = intt_coeffs(&prod_hat);
            let mut want = [0i64; N];
            for i in 0..N {
                for j in 0..N {
                    let v = f[i] * g[j];
                    if i + j < N {
                        want[i + j] += v;
                    } else {
                        want[i + j - N] -= v;
                    }
                }
            }
            assert_eq!(prod, want.map(|c| c.rem_euclid(Q as i64)));
        }
    }
}
