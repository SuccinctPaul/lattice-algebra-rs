//! σ-automorphism packing (Z7): commit to `d = 256` scalar coefficients per
//! ring element instead of one, removing the factor-`d` overhead the
//! unpacked PCS pays.
//!
//! The load-bearing identity is the constant-term pairing through the
//! coefficient-reversal automorphism `σ: X ↦ X^{−1}` of
//! `R_q = Z_q[X]/(X^d + 1)`. Since `X^{−1} = −X^{d−1}` and the two signs
//! cancel, `X^{−k} = −X^{d−k}` for every `k ≥ 1`, so `σ` is the reversal
//! with a global minus, `σ(g)_0 = g_0`, `σ(g)_{d−k} = −g_k`, and the wrap
//! sign of `X^d = −1` in the product cancels the automorphism's sign:
//!
//! ```text
//! const( g · σ(h) ) = Σ_k g_k·h_k        (plain scalar inner product)
//! ```
//!
//! With the power vector `p = (1, x, x², …, x^{d−1})` the pairing
//! evaluates: `const( F · σ(p) ) = Σ_k F_k·x^k`, so a scalar-coefficient
//! polynomial `f` of degree `< N·d`, packed into `N` ring elements `Fⱼ`
//! (d consecutive coefficients each), evaluates at a scalar point `x`
//! from ring data alone:
//!
//! ```text
//! f(x) = Σⱼ x^{j·d} · const( Fⱼ · σ(p) )
//! ```
//!
//! and the same two-layer Ajtai commitment and √N-split proof carry `d`×
//! more scalar coefficients. This module provides the packing primitives;
//! the packed evaluation-claim binding (replacing eqs. 2/3's ring products
//! by the σ-pairing in the Greyhound verifier) is the remaining
//! integration step of the packing line.

use crate::foundation::encoding::{ring_from_u32, ring_to_u32};
use crate::pcs::{RingElt, Z1Coeff, DIM};
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::{vec, vec::Vec};

/// The coefficient-reversal automorphism `σ: X ↦ X^{−1}`:
/// `σ(g)_0 = g_0`, `σ(g)_{d−k} = −g_k` (mod `q`).
pub fn sigma_automorphism(g: &RingElt) -> RingElt {
    let src = ring_to_u32::<Z1Coeff, DIM>(g);
    let mut out = [0u32; DIM];
    out[0] = src[0];
    for k in 1..DIM {
        out[DIM - k] = if src[k] == 0 {
            0
        } else {
            (Z1Coeff::MODULUS - u64::from(src[k])) as u32
        };
    }
    ring_from_u32::<Z1Coeff, DIM>(&out)
}

/// The σ-pairing `const(g·σ(h)) = Σ_k g_k·h_k` — the scalar inner product
/// via one ring product's constant term (see the module docs).
pub fn sigma_pairing(g: &RingElt, h: &RingElt) -> Z1Coeff {
    let prod = g.clone() * sigma_automorphism(h);
    Z1Coeff::from(u64::from(ring_to_u32::<Z1Coeff, DIM>(&prod)[0]))
}

/// Packs scalar coefficients into ring elements (`DIM` per element): `Fⱼ`
/// holds `f[j·d .. (j+1)·d]` in ascending order.
///
/// # Panics
/// If `f.len()` is zero or not a multiple of [`DIM`].
pub fn pack_scalars(f: &[Z1Coeff]) -> Vec<RingElt> {
    assert!(
        !f.is_empty() && f.len() % DIM == 0,
        "packed length must be a multiple of d"
    );
    f.chunks(DIM)
        .map(|chunk| crate::pcs::RingElt::from_coefficients(chunk.to_vec()))
        .collect()
}

/// Unpacks [`pack_scalars`] output back to the scalar coefficients.
///
/// # Panics
/// If `packed.len()` is zero.
pub fn unpack_scalars(packed: &[RingElt]) -> Vec<Z1Coeff> {
    assert!(!packed.is_empty(), "cannot unpack an empty packing");
    let mut out = Vec::with_capacity(packed.len() * DIM);
    for elt in packed {
        out.extend(
            ring_to_u32::<Z1Coeff, DIM>(elt)
                .iter()
                .map(|&c| Z1Coeff::from(u64::from(c))),
        );
    }
    out
}

/// Evaluates the packed scalar-coefficient polynomial at the scalar point
/// `x`: `f(x) = Σⱼ x^{j·d}·const(Fⱼ·σ(p))` with `p = (1, x, …, x^{d−1})`.
pub fn packed_eval(packed: &[RingElt], x: Z1Coeff) -> Z1Coeff {
    let mut p_coeffs = vec![Z1Coeff::ZERO; DIM];
    let mut cur = Z1Coeff::ONE;
    for c in p_coeffs.iter_mut() {
        *c = cur;
        cur *= x;
    }
    let p = crate::pcs::RingElt::from_coefficients(p_coeffs);

    let mut acc = Z1Coeff::ZERO;
    let mut block_weight = Z1Coeff::ONE;
    let mut xd = x.square() * x.square(); // x^4; squared up to x^256 below
    for _ in 0..6 {
        xd = xd.square();
    }
    for elt in packed {
        acc += block_weight * sigma_pairing(elt, &p);
        block_weight *= xd;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;

    /// Deterministic scalar coefficients covering the full range mix.
    fn test_scalars(len: usize) -> Vec<Z1Coeff> {
        (0..len)
            .map(|i| from_centered::<Z1Coeff>(((i as i64 * 37 + 11) % 97) - 48))
            .collect()
    }

    #[test]
    fn sigma_pairing_matches_scalar_inner_product() {
        // const(g·σ(h)) == Σ_k g_k·h_k (the plain inner product — the
        // automorphism's minus and the X^d = −1 wrap sign cancel)
        let g = pack_scalars(&test_scalars(DIM)).remove(0);
        let h = pack_scalars(&test_scalars(DIM + DIM)).remove(0);
        let gs = ring_to_u32::<Z1Coeff, DIM>(&g);
        let hs = ring_to_u32::<Z1Coeff, DIM>(&h);
        let mut expected = Z1Coeff::ZERO;
        for k in 0..DIM {
            expected += Z1Coeff::from(u64::from(gs[k])) * Z1Coeff::from(u64::from(hs[k]));
        }
        assert_eq!(sigma_pairing(&g, &h), expected);
    }

    #[test]
    fn sigma_is_an_involution_and_multiplicative() {
        let g = pack_scalars(&test_scalars(DIM)).remove(0);
        // σ∘σ = id
        assert_eq!(sigma_automorphism(&sigma_automorphism(&g)), g);
        // σ is a ring homomorphism: σ(g·h) == σ(g)·σ(h)
        let h = pack_scalars(&test_scalars(2 * DIM)).remove(0);
        assert_eq!(
            sigma_automorphism(&(g.clone() * h.clone())),
            sigma_automorphism(&g) * sigma_automorphism(&h)
        );
    }

    #[test]
    fn packing_roundtrips() {
        let f = test_scalars(4 * DIM);
        let packed = pack_scalars(&f);
        assert_eq!(packed.len(), 4);
        assert_eq!(unpack_scalars(&packed), f);
    }

    #[test]
    fn packed_eval_matches_horner() {
        // the packed evaluation must equal the plain scalar Horner fold
        let f = test_scalars(8 * DIM); // degree < 2048
        let packed = pack_scalars(&f);
        let x = from_centered::<Z1Coeff>(4242);

        let y_packed = packed_eval(&packed, x);
        let mut horner = Z1Coeff::ZERO;
        for c in f.iter().rev() {
            horner = horner * x + *c;
        }
        assert_eq!(y_packed, horner);
    }
}
