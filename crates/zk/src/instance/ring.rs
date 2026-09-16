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
