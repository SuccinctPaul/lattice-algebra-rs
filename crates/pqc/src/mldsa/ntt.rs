//! The FIPS 204 number-theoretic transform, byte-exact with the
//! specification and the pq-crystals reference implementation.
//!
//! The base [`algebra::ntt`] engine is a general-purpose transform: it picks
//! *some* primitive 2N-th root of unity and emits evaluation points in
//! natural order. That is mathematically valid for any scheme that samples
//! `Â` directly in the NTT domain, but it is *not* the FIPS 204 convention:
//! the standard fixes `ζ = 1753` and orders the evaluation points as
//! `ζ^(2·brv8(i)+1)` (bit-reversed odd powers), and the official KAT/ACVP
//! vectors are only reproducible under that exact convention.
//!
//! This module implements the standard's transform on plain `[0, q)`
//! representatives (no Montgomery form — the reference's `2^32` table factor
//! cancels in its butterflies, so the transforms are mathematically
//! identical):
//!
//! - forward: Cooley–Tukey butterflies with `ZETAS[k] = ζ^brv8(k)`,
//!   consumed block-by-block exactly like the reference;
//! - inverse: the same network run backwards with inverted twiddles,
//!   scaled by `N⁻¹`;
//! - `Â` entries from `ExpandA` are stored as raw `RejNTTPoly` values,
//!   which are NTT-domain coefficients under precisely this convention.
//!
//! All arithmetic is branch-free modular arithmetic over `u64`.

use super::params::{N, Q};
use super::ZqD;
use algebra::crypto::sampling::{sample_uniform_coeff, BitStream};
use algebra::crypto::xof::Xof;
use algebra::ring::Ring;

/// Primitive 2N-th root of unity mod `q` (FIPS 204, §3.7): `ζ^256 ≡ −1`.
const ZETA: u64 = 1753;

const Q_U64: u64 = Q as u64;

#[inline]
pub(crate) fn mul_mod(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % Q_U64 as u128) as u64
}

/// NTT-domain inner-product step: `acc[j] += a[j]·b[j] (mod q)`.
pub fn pointwise_mul_add(acc: &mut [u64; N], a: &[u64; N], b: &[u64; N]) {
    for j in 0..N {
        acc[j] = (acc[j] + mul_mod(a[j], b[j])) % Q_U64;
    }
}

/// FIPS 204 `ExpandA(ρ)`: builds the `K×L` matrix `Â` directly in the NTT
/// domain. Entry `(r, s)` is `RejNTTPoly(XOF(ρ ‖ s ‖ r))` with single-byte
/// indices (column `s` absorbed before row `r`); coefficients are drawn
/// with masked rejection (`CoeffFromThreeBytes`, 23-bit mask, reject ≥ q).
pub(crate) fn expand_a<X: Xof, const K: usize, const L: usize>(
    rho: &[u8; 32],
) -> [[[u64; N]; L]; K] {
    let mut out = [[[0u64; N]; L]; K];
    for (r, row) in out.iter_mut().enumerate() {
        for (s, entry) in row.iter_mut().enumerate() {
            let mut xof = X::new(&[]);
            xof.absorb(rho);
            xof.absorb(&[s as u8, r as u8]);
            let mut stream = BitStream::new(&mut xof);
            for c in entry.iter_mut() {
                *c = sample_uniform_coeff::<ZqD>(&mut stream).to_u128() as u64;
            }
        }
    }
    out
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

/// 8-bit bit-reversal (FIPS 204 `BitRev8`).
const fn bit_rev8(i: usize) -> usize {
    i.reverse_bits() >> (usize::BITS - 8)
}

/// Forward twiddles: `ZETAS[k] = ζ^brv8(k)` for `k ∈ [0, 256)`.
///
/// `ZETAS[0]` is unused (the reference table keeps a placeholder there).
const ZETAS: [u64; N] = {
    let mut table = [0u64; N];
    let mut k = 0;
    while k < N {
        table[k] = pow_mod(ZETA, bit_rev8(k) as u64);
        k += 1;
    }
    table
};

/// Inverse twiddles: `ZETAS_INV[k] = ζ^(−brv8(k))`.
const ZETAS_INV: [u64; N] = {
    let mut table = [0u64; N];
    let mut k = 0;
    while k < N {
        table[k] = pow_mod(ZETAS[k], Q as u64 - 2);
        k += 1;
    }
    table
};

/// `N⁻¹ mod q`.
const N_INV: u64 = pow_mod(N as u64, Q as u64 - 2);

/// FIPS 204 NTT (forward): coefficients in `[0, q)` → evaluation-domain
/// values `f̂[i] = f(ζ^(2·brv8(i)+1))`, exactly the reference layout.
pub fn ntt(a: &mut [u64; N]) {
    let mut k = 0usize;
    let mut len = N / 2;
    while len >= 1 {
        let mut start = 0;
        while start < N {
            k += 1;
            let zeta = ZETAS[k];
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

/// FIPS 204 inverse NTT: evaluation-domain values → coefficients in
/// `[0, q)`.
pub fn intt(a: &mut [u64; N]) {
    let mut len = 1;
    while len < N {
        let mut start = 0;
        while start < N {
            // Block index k mirrors the forward pass: with `len = 2^t`,
            // forward blocks are numbered `2^(7−t) + start/(2·len)`.
            let k = (N + start) / (2 * len);
            let zeta = ZETAS_INV[k];
            for j in start..start + len {
                let t = a[j];
                let u = a[j + len];
                a[j] = (t + u) % Q_U64;
                let du = (t + Q_U64 - u) % Q_U64;
                a[j + len] = mul_mod(du, zeta);
            }
            start += 2 * len;
        }
        len <<= 1;
    }
    for c in a.iter_mut() {
        *c = mul_mod(*c, N_INV);
    }
}

/// Maps centered coefficient representatives (any `i64`) into `[0, q)` and
/// applies the forward NTT.
pub fn ntt_coeffs(coeffs: &[i64; N]) -> [u64; N] {
    let mut out = [0u64; N];
    for (dst, &src) in out.iter_mut().zip(coeffs.iter()) {
        *dst = src.rem_euclid(Q) as u64;
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
    use crate::mldsa::params::Q;

    fn sample_coeffs(seed: u64) -> [i64; N] {
        let mut state = seed.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(1);
        std::array::from_fn(|_| {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            (state % (2 * Q as u64)) as i64 - Q
        })
    }

    #[test]
    fn roundtrip_and_range() {
        for seed in 0..8u64 {
            let f = sample_coeffs(seed);
            let hat = ntt_coeffs(&f);
            assert!(hat.iter().all(|&v| v < Q as u64));
            let back = intt_coeffs(&hat);
            assert_eq!(
                back,
                f.map(|c| c.rem_euclid(Q)),
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
            // Linearity: ntt(f + g) == ntt(f) + ntt(g) (domain-wise mod q).
            let sum: [i64; N] = std::array::from_fn(|i| (f[i] + g[i]).rem_euclid(Q));
            let sum_hat = ntt_coeffs(&sum);
            let f_plus_g_hat: Vec<u64> = f_hat
                .iter()
                .zip(&g_hat)
                .map(|(&a, &b)| (a + b) % Q_U64)
                .collect();
            assert_eq!(sum_hat, f_plus_g_hat.as_slice());
            // Negacyclic product via pointwise multiply.
            let prod_hat: Vec<u64> = f_hat
                .iter()
                .zip(&g_hat)
                .map(|(&a, &b)| mul_mod(a, b))
                .collect();
            let mut buf = [0u64; N];
            buf.copy_from_slice(&prod_hat);
            let prod = intt_coeffs(&buf);
            // Schoolbook f·g mod (x^N + 1).
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
            assert_eq!(prod, want.map(|c| c.rem_euclid(Q)));
        }
    }

    #[test]
    fn evaluation_points_match_fips204_order() {
        // f̂[i] must equal f(ζ^(2·brv8(i)+1)).
        let f = sample_coeffs(7);
        let hat = ntt_coeffs(&f);
        for i in (0..N).step_by(31) {
            let x = pow_mod(ZETA, (2 * bit_rev8(i) + 1) as u64);
            let mut eval = 0u64;
            for &c in f.iter().rev() {
                eval = (mul_mod(eval, x) + c.rem_euclid(Q) as u64) % Q_U64;
            }
            assert_eq!(hat[i], eval, "evaluation point mismatch at slot {i}");
        }
    }

    #[test]
    fn zeta_is_primitive_2n_th_root() {
        assert_eq!(pow_mod(ZETA, N as u64), Q_U64 - 1);
        assert_ne!(pow_mod(ZETA, (N / 2) as u64), Q_U64 - 1);
    }
}
