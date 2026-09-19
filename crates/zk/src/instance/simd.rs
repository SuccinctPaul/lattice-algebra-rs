//! Z2-ring lane kernels (`simd` feature).
//!
//! The Z2 ring `Z_{2^32}[X]/(X^64+1)` multiplies with pure wrapping `u32`
//! arithmetic — products, sums and negation are all exact mod 2^32 — so the
//! schoolbook negacyclic product factors into contiguous
//! `algebra::simd::wrapping_dot_u32` windows over 8×32-bit
//! lanes. All lane-specific code lives here; protocol code calls `z2_mul`
//! unconditionally and the scalar fallback (the generic `PolyRing`
//! product) compiles when the feature is off. Both paths are exact integer
//! arithmetic and bit-identical; the test module asserts agreement against
//! the ring operator, and the protocol-level end-to-end tests pin the wire
//! format.

use crate::instance::ring::Z2Ring;
#[cfg(feature = "simd")]
use crate::instance::ring::D;

/// Negacyclic product `a·b` in `Z_{2^32}[X]/(X^64+1)`.
///
/// The lane path rewrites the two schoolbook diagonals of each output
/// coefficient as contiguous dots (exact: reordering sums is lossless mod
/// 2^32), giving the lane multiplier ~4 contiguous `u32` multiplies per
/// coefficient against the generic per-term scatter loop.
#[inline]
pub(crate) fn z2_mul(a: &Z2Ring, b: &Z2Ring) -> Z2Ring {
    #[cfg(feature = "simd")]
    {
        z2_mul_lanes(a, b)
    }

    #[cfg(not(feature = "simd"))]
    {
        a.clone() * b
    }
}

/// Lane path for [`z2_mul`].
///
/// With the reversed coefficient vector `rb[k] = b[D−1−k]`, the two
/// schoolbook diagonals of `c[i]` become contiguous windows:
///
/// ```text
/// c[i] = Σ_{j≤i} a[j]·b[i−j]  −  Σ_{j>i} a[j]·b[D+i−j]
///      = dot(a[0..=i], rb[D−1−i..]) − dot(a[i+1..], rb[..D−1−i])
/// ```
#[cfg(feature = "simd")]
fn z2_mul_lanes(a: &Z2Ring, b: &Z2Ring) -> Z2Ring {
    use crate::foundation::encoding::{ring_from_u32, ring_to_u32};
    use algebra::simd::wrapping_dot_u32;

    let ac = ring_to_u32(a);
    let bc = ring_to_u32(b);
    let mut rb = [0u32; D];
    for (dst, src) in rb.iter_mut().zip(bc.iter().rev()) {
        *dst = *src;
    }

    let mut out = [0u32; D];
    for i in 0..D {
        let plus = wrapping_dot_u32(&ac[..=i], &rb[D - 1 - i..]);
        let minus = wrapping_dot_u32(&ac[i + 1..], &rb[..D - 1 - i]);
        out[i] = plus.wrapping_sub(minus);
    }
    ring_from_u32(&out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::encoding::ring_from_u32;
    use crate::instance::ring::D;

    /// Deterministic xorshift so failures are reproducible.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            let mut s = self.0;
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            self.0 = s;
            s
        }
    }

    fn ring_from_seed(seed: u64) -> Z2Ring {
        let mut rng = Rng(seed);
        let coeffs: [u32; D] = core::array::from_fn(|_| rng.next() as u32);
        ring_from_u32(&coeffs)
    }

    #[test]
    fn z2_mul_matches_ring_operator() {
        // The lane path is exact integer arithmetic, so it must agree with
        // the generic ring product coefficient-for-coefficient — including
        // the extreme coefficients.
        let mut rng = Rng(0x9E37_79B9);
        let edge = [
            ring_from_u32(&{
                let mut c = [0u32; D];
                c[0] = u32::MAX;
                c
            }),
            ring_from_u32(&{
                let mut c = [0u32; D];
                c[D - 1] = 1;
                c
            }),
            ring_from_u32(&[0xFFFF_FFFF; D]),
        ];
        for i in 0..64 {
            let a = ring_from_seed(rng.next());
            let b = ring_from_seed(rng.next());
            assert_eq!(z2_mul(&a, &b), a.clone() * b, "pair {i}");
            for e in &edge {
                assert_eq!(z2_mul(e, &a), e.clone() * a.clone(), "edge {i}");
                assert_eq!(z2_mul(&a, e), a.clone() * e.clone(), "edge rev {i}");
            }
        }
    }
}
