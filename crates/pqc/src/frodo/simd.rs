//! FrodoKEM matrix-arithmetic kernels: 16-lane SIMD paths with scalar
//! fallbacks.
//!
//! The lane paths (`simd-frodo` feature) run on the
//! [`algebra::simd`](algebra::simd) wrapping 16-bit kernels — exact for the
//! power-of-two moduli FrodoKEM uses (`q = 2^15` or `2^16`): the masked
//! result only depends on the low `logq ≤ 16` bits, and addition and
//! multiplication mod 2^16 commute with truncation regardless of summation
//! order. With the feature off, the same functions are pure scalar loops, so
//! constrained targets compile FrodoKEM with no lane code at all.

/// Wrapping 16-bit dot product `Σ a[i]·b[i] (mod 2^16)` — the FrodoKEM
/// inner-product step.
pub(super) fn dot16(a: &[u16], b: &[u16]) -> u16 {
    #[cfg(feature = "simd-frodo")]
    return algebra::simd::wrapping_dot_u16(a, b);
    #[cfg(not(feature = "simd-frodo"))]
    {
        let mut sum = 0u16;
        for (&x, &y) in a.iter().zip(b.iter()) {
            sum = sum.wrapping_add(x.wrapping_mul(y));
        }
        sum
    }
}

/// Wrapping 16-bit axpy: `row[i] += scalar·a[i] (mod 2^16)`; exactness as
/// [`dot16`](self::dot16).
pub(super) fn axpy16(row: &mut [u16], a: &[u16], scalar: u16) {
    #[cfg(feature = "simd-frodo")]
    return algebra::simd::wrapping_axpy_u16(row, a, scalar);
    #[cfg(not(feature = "simd-frodo"))]
    {
        for (px, &x) in row.iter_mut().zip(a.iter()) {
            *px = px.wrapping_add(scalar.wrapping_mul(x));
        }
    }
}
