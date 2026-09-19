//! The Z2 ring instance: `R = Z_{2^32}[X]/(X^64+1)` (L5 instance domain).
//!
//! With `q = 2^32` the modular reduction is a shift and `is_ntt_friendly`
//! is false, so ring multiplication takes the schoolbook negacyclic path —
//! correct and cheap at dimension 64 (4096 u32 multiplies per product).
//!
//! Key expansion uses **raw 32-bit coefficients** (four squeezed bytes per
//! coefficient, no rejection): every 32-bit value is a valid coefficient of
//! this ring. The expansion lives in [`crate::foundation::sampling`], the
//! coefficient wire conversion in [`crate::foundation::encoding`]. The R1CS
//! instance layer over this ring lives in [`crate::instance::r1cs`].

use crate::foundation::encoding::{ring_from_u32, ring_to_u32};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;
use alloc::{vec, vec::Vec};

/// The Z2 ring: `Z_{2^32}[X]/(X^64+1)`.
pub type Z2Ring = PolyRing<Zq<4294967296>, 64>;
/// Coefficient type of the Z2 ring (`q = 2^32`).
pub type Z2Coeff = Zq<4294967296>;

/// Number of coefficients of a ring element.
/// Ring dimension of the Z2 polynomial ring `Z_{2^32}[X]/(X^D + 1)`.
pub const D: usize = 64;

/// Infinity norm of a ring vector (max over all coefficients of all
/// elements, centered representatives).
pub fn infinity_norm(v: &[Z2Ring]) -> u64 {
    v.iter()
        .flat_map(|r| r.coefficients())
        .map(|c| c.abs_infinity())
        .max()
        .unwrap_or(0)
}

/// Multiplies a ring element by the constant `2^k` (`k < 32`).
///
/// A constant whose only non-zero coefficient sits at position 0 scales
/// each coefficient independently, so this is a linear coefficient shift —
/// exact in `Z_{2^32}` (overflow drops, matching the wrapping ring) — and
/// avoids the quadratic schoolbook product entirely.
///
/// # Panics
/// If `k >= 32`.
pub fn scale_pow2(v: &Z2Ring, k: u32) -> Z2Ring {
    assert!(k < 32, "scale_pow2 requires k < 32");
    let shifted: Vec<u32> = crate::foundation::encoding::ring_to_u32(v)
        .iter()
        .map(|&c| c << k)
        .collect();
    crate::foundation::encoding::ring_from_u32(shifted.as_slice().try_into().expect("D coeffs"))
}

/// The constant ring element `2^k` (scalar shifts in the ring domain).
///
/// # Panics
/// If `k >= 32` (the constant no longer fits a coefficient).
pub fn pow2_const(k: u32) -> Z2Ring {
    assert!(k < 32, "pow2_const requires k < 32");
    let mut coeffs = [0u32; D];
    coeffs[0] = 1u32 << k;
    ring_from_u32(&coeffs)
}

/// LaZer-style integer lift: splits every coefficient of `x` into
/// `(lo, hi)` with `x = lo + 2^k·hi` exactly (coefficient-wise). The lift
/// turns the modular statement `A·s ≡ t (mod 2^k)` into the exact
/// ring equation `A·s + 2^k·v = t` with `v` short — adding the hidden
/// carry vector `v` to the witness instead of proving arithmetic mod a
/// non-ring modulus.
///
/// # Panics
/// If `k` is 0 or ≥ 32.
pub fn split_mod_2k(x: &[Z2Ring], k: u32) -> (Vec<Z2Ring>, Vec<Z2Ring>) {
    assert!((1..32).contains(&k), "split_mod_2k needs 1 ≤ k < 32");
    let mask = (1u32 << k) - 1;
    let mut los = Vec::with_capacity(x.len());
    let mut his = Vec::with_capacity(x.len());
    for r in x {
        let cs = ring_to_u32(r);
        let mut lo = [0u32; D];
        let mut hi = [0u32; D];
        for j in 0..D {
            lo[j] = cs[j] & mask;
            hi[j] = cs[j] >> k;
        }
        los.push(ring_from_u32(&lo));
        his.push(ring_from_u32(&hi));
    }
    (los, his)
}

/// Homomorphic 2-adic modulus switch: reduces every coefficient modulo
/// `Q` (a power of two). The reduction is a ring homomorphism
/// `Z_{2^32}[X]/(X^D+1) → Z_Q[X]/(X^D+1)`, so
/// `ms(a·b) == ms(a)·ms(b)` and `ms(A·w) == ms(A)·ms(w)` — the switching
/// step the Alpine/Shadow line builds on (a commitment can be re-stated
/// over a smaller ring without re-opening the witness).
pub fn modswitch_ring<const Q: u64, const N: usize>(x: &[Z2Ring]) -> Vec<PolyRing<Zq<Q>, N>> {
    assert!(
        Q.is_power_of_two() && Q <= (1 << 32),
        "Q must be 2^k ≤ 2^32"
    );
    let mask = (Q as u32)
        .wrapping_sub(1)
        .max(if Q == 1 { 0 } else { u32::MAX });
    let _ = mask;
    x.iter()
        .map(|r| {
            PolyRing::from_coefficients(
                ring_to_u32(r)
                    .iter()
                    .map(|c| {
                        let reduced = if Q == 1 << 32 { *c } else { c & (Q as u32 - 1) };
                        Zq::<Q>::from(u64::from(reduced))
                    })
                    .collect(),
            )
        })
        .collect()
}

/// Ring inverse via Newton iteration: `x_{n+1} = x_n·(2 − a·x_n)`.
///
/// `a` is a unit of `Z_{2^32}[X]/(X^64+1)` iff its coefficient sum is odd
/// (the reduction mod 2 is `F_2[X]/(X+1)^64`, a local ring whose units are
/// the elements with `X = 1` evaluation equal to 1).
pub fn ring_inv_newton(a: &Z2Ring) -> Option<Z2Ring> {
    let parity: u64 = a
        .coefficients()
        .iter()
        .map(|c| (c.to_u128() & 1) as u64)
        .sum::<u64>()
        & 1;
    if parity == 0 {
        return None;
    }
    let two = Z2Ring::from_coefficients(vec![Z2Coeff::new(2)]);
    let mut x = Z2Ring::from_coefficients(vec![Z2Coeff::new(1)]);
    for _ in 0..8 {
        // x = x·(2 − a·x)
        let ax = a.clone() * x.clone();
        let t = two.clone() - ax;
        x = x.clone() * t;
    }
    // verify
    let check = a.clone() * x.clone();
    (ring_to_u32(&check)[0] == 1 && ring_to_u32(&check)[1..].iter().all(|&v| v == 0)).then_some(x)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ring_arithmetic_basics() {
        // (X^63)·(X) = X^64 ≡ −1 (mod X^64+1), q = 2^32 → −1 = 2^32−1
        let mut c = [0u32; D];
        c[63] = 1;
        let x63: Z2Ring = ring_from_u32(&c);
        let mut c1 = [0u32; D];
        c1[1] = 1;
        let x: Z2Ring = ring_from_u32(&c1);
        let prod = x63 * x;
        let coeffs = ring_to_u32(&prod);
        assert_eq!(coeffs[0], u32::MAX);
        assert!(coeffs[1..].iter().all(|&v| v == 0));
    }

    #[test]
    fn inv_odd_roundtrip() {
        fn inv_odd(a: u32) -> u32 {
            let mut x = 1u32;
            for _ in 0..5 {
                x = x.wrapping_mul(2u32.wrapping_sub(a.wrapping_mul(x)));
            }
            x
        }
        for a in [1u32, 3, 5, 0xDEAD_BEEF, 0xFFFF_FFFF] {
            assert_eq!(a.wrapping_mul(inv_odd(a)), 1, "a = {a}");
        }
    }

    #[test]
    fn scale_pow2_matches_constant_product() {
        let mut rng_state = 0x5EED_1234u64;
        let mut coeffs = [0u32; D];
        for c in &mut coeffs {
            rng_state ^= rng_state << 13;
            rng_state ^= rng_state >> 7;
            rng_state ^= rng_state << 17;
            *c = rng_state as u32;
        }
        let v = ring_from_u32(&coeffs);
        for k in [0u32, 1, 8, 16, 24, 31] {
            assert_eq!(
                scale_pow2(&v, k),
                pow2_const(k) * v.clone(),
                "scale by 2^{k}"
            );
        }
        // Overflow drops (exact mod 2^32): scaling 2^31 by 2 → 0.
        let two31 = ring_from_u32(&{
            let mut c = [0u32; D];
            c[3] = 1 << 31;
            c
        });
        assert!(ring_to_u32(&scale_pow2(&two31, 1)).iter().all(|&c| c == 0));
    }

    #[test]
    fn split_and_modswitch_are_exact() {
        use crate::foundation::encoding::ring_from_u32;
        let mut x = [0u32; D];
        x[0] = 0x1234_5678;
        x[3] = 0xFFFF_FFFF;
        x[63] = 7;
        let r = vec![ring_from_u32(&x)];

        // lift: lo + 2^k·hi == x
        let (lo, hi) = split_mod_2k(&r, 12);
        let rebuilt = pow2_const(12) * hi[0].clone() + lo[0].clone();
        assert_eq!(ring_to_u32(&rebuilt), x);
        // lo holds exactly the low 12 bits
        assert_eq!(ring_to_u32(&lo[0])[0], 0x678);
        assert_eq!(ring_to_u32(&hi[0])[0], 0x12345);

        // modswitch: homomorphic reduction to Z_{2^16}
        let a = ring_from_u32(&{
            let mut c = [0u32; D];
            c[0] = 0x0001_0002;
            c[1] = 0xFFFF_0000;
            c
        });
        let b = ring_from_u32(&{
            let mut c = [0u32; D];
            c[0] = 0x0000_0003;
            c
        });
        let prod = a.clone() * b.clone();
        let ms = |r: &Z2Ring| modswitch_ring::<65536, D>(core::slice::from_ref(r)).remove(0);
        let lhs = ms(&prod);
        let rhs = ms(&a) * ms(&b);
        assert_eq!(lhs.coefficients(), rhs.coefficients());
    }

    #[test]
    fn pow2_const_and_infinity_norm() {
        let four = pow2_const(2);
        assert_eq!(ring_to_u32(&four)[0], 4);
        assert!(ring_to_u32(&four)[1..].iter().all(|&v| v == 0));
        let v = vec![
            ring_from_u32(&{
                let mut c = [0u32; D];
                c[0] = 5;
                c
            }),
            ring_from_u32(&{
                let mut c = [0u32; D];
                c[3] = 0xFFFF_FFFF; // −1 centered
                c
            }),
        ];
        assert_eq!(infinity_norm(&v), 5);
        assert_eq!(infinity_norm(&[]), 0);
    }
}
