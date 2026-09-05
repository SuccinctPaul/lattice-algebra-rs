//! LaBRADOR-style Z2 instance over the power-of-two ring
//! `R = Z_{2^32}[X]/(X^64+1)` (L5, Z2).
//!
//! With `q = 2^32` the modular reduction is a shift and `is_ntt_friendly`
//! is false, so ring multiplication takes the schoolbook negacyclic path —
//! correct and cheap at dimension 64 (4096 u32 multiplies per product).
//!
//! Key expansion uses **raw 32-bit coefficients** (four squeezed bytes per
//! coefficient, no rejection): every 32-bit value is a valid coefficient of
//! this ring.

use crate::crypto::xof::{Shake128Xof, Xof};
use crate::ring::poly_ring::PolyRing;
use crate::ring::traits::MatrixElement;
use crate::ring::zq::Zq;
use crate::ring::PolynomialQuotientRing;
use crate::ring::Ring;

/// The Z2 ring: `Z_{2^32}[X]/(X^64+1)`.
pub type Z2Ring = PolyRing<Zq<4294967296>, 64>;
/// Coefficient type of the Z2 ring (`q = 2^32`).
pub type Z2Coeff = Zq<4294967296>;

/// Number of coefficients of a ring element.
pub const D: usize = 64;

/// Builds a ring element from raw 32-bit coefficients.
pub fn ring_from_u32(coeffs: &[u32; D]) -> Z2Ring {
    PolyRing::from_coefficients(coeffs.iter().map(|&c| Z2Coeff::new(c as u64)).collect())
}

/// Raw 32-bit coefficients of a ring element (ascending powers).
pub fn ring_to_u32(r: &Z2Ring) -> [u32; D] {
    let mut out = [0u32; D];
    for (dst, src) in out.iter_mut().zip(r.coefficients()) {
        *dst = src.to_u128() as u32;
    }
    out
}

/// Derives a uniform ring element from a seed (raw 32-bit coefficients —
/// no rejection needed on the power-of-two modulus).
pub fn ring_from_seed(xof: &mut Shake128Xof) -> Z2Ring {
    let mut coeffs = [0u32; D];
    let mut buf = [0u8; 4];
    for c in &mut coeffs {
        xof.squeeze(&mut buf);
        *c = u32::from_le_bytes(buf);
    }
    ring_from_u32(&coeffs)
}

/// Derives a uniform `R^{rows×cols}` matrix from a seed.
pub fn matrix_from_seed(seed: &[u8; 32], rows: usize, cols: usize) -> Vec<Vec<Z2Ring>> {
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(seed);
    (0..rows)
        .map(|_| (0..cols).map(|_| ring_from_seed(&mut xof)).collect())
        .collect()
}

/// Sparse ring row: `(variable index, coefficient)` pairs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SparseRow {
    pub terms: Vec<(usize, Z2Ring)>,
}

/// Toy R1CS instance over `R`: squaring gates
/// `(A_k·z) ∘ (A_k·z) = U_k · z_{sel_k}`.
///
/// Any R1CS reduces to squaring gates (introduce one auxiliary variable per
/// product, `B = I`), so this reduced form is representative. "≈10^4
/// constraints" means 10^4 ring rows — each one a 64-lane batch of scalar
/// constraints.
#[derive(Debug, Clone)]
pub struct ToyR1cs {
    /// Rows of `A` (each with a few non-zero ring entries).
    pub a: Vec<SparseRow>,
    /// Selected variable per gate (`B = I`).
    pub sel: Vec<usize>,
    /// Public outputs `U_k`.
    pub u: Vec<Z2Ring>,
    /// Number of witness variables.
    pub num_vars: usize,
}

impl ToyR1cs {
    /// Checks the full relation `∀k: (A_k·z)² = U_k · z_{sel_k}`.
    pub fn is_satisfied(&self, z: &[Z2Ring]) -> bool {
        if z.len() != self.num_vars {
            return false;
        }
        for (k, row) in self.a.iter().enumerate() {
            let mut acc = Z2Ring::zero();
            for (j, coeff) in &row.terms {
                acc += coeff.clone() * z[*j].clone();
            }
            let sq = acc.clone() * acc.clone();
            let rhs = self.u[k].clone() * z[self.sel[k]].clone();
            if sq.coefficients() != rhs.coefficients() {
                return false;
            }
        }
        true
    }
}

/// Generates a toy instance with `num_constraints` squaring gates and a
/// satisfying (random, odd-coefficient) witness. Witness values are 32-bit
/// and odd so the gate outputs are consistently derivable.
pub fn gen_toy_instance(
    seed: &[u8; 32],
    num_constraints: usize,
    num_vars: usize,
) -> (ToyR1cs, Vec<Z2Ring>) {
    assert!(num_vars >= 2);
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(seed);

    // random unit witness: elements ≡ 1 (mod 2) — odd constant term, all
    // other coefficients even — so `a − 1 ∈ 2R` and Newton's iteration for
    // the ring inverse converges (needed to derive the gate outputs U_k).
    let mut witness = Vec::with_capacity(num_vars);
    for _ in 0..num_vars {
        let mut coeffs = [0u32; D];
        let mut buf = [0u8; 4];
        xof.squeeze(&mut buf);
        coeffs[0] = u32::from_le_bytes(buf) | 1; // odd constant term
        for c in &mut coeffs[1..] {
            xof.squeeze(&mut buf);
            *c = u32::from_le_bytes(buf) & 0xFFFF_FFFE; // even
        }
        witness.push(ring_from_u32(&coeffs));
    }

    let mut a = Vec::with_capacity(num_constraints);
    let mut sel = Vec::with_capacity(num_constraints);
    let mut u = Vec::with_capacity(num_constraints);
    for k in 0..num_constraints {
        // 3 non-zero ring entries per row (sparse R1CS)
        let mut terms = Vec::with_capacity(3);
        for t in 0..3 {
            let var = (k * 7 + t * 13) % num_vars;
            let coeff = ring_from_seed(&mut xof);
            terms.push((var, coeff));
        }
        let sel_var = (k * 5 + 1) % num_vars;
        // Compute U_k = (A_k·z)² · z_sel^{-1}: invertible because both the
        // accumulator (odd×odd sums... force oddness by construction below)
        // — instead of general inversion we solve for U by multiplying the
        // accumulator by the odd-part inverse computed via Newton iteration
        // on odd 32-bit values.
        let mut acc = Z2Ring::zero();
        for (j, coeff) in &terms {
            acc += coeff.clone() * witness[*j].clone();
        }
        let sq = acc.clone() * acc.clone();
        let inv = ring_inv_newton(&witness[sel_var]).expect("selected variable must be a unit");
        let u_k = sq.clone() * inv.clone();
        a.push(SparseRow { terms });
        sel.push(sel_var);
        u.push(u_k);
    }

    (
        ToyR1cs {
            a,
            sel,
            u,
            num_vars,
        },
        witness,
    )
}

/// Ring inverse via Newton iteration: `x_{n+1} = x_n·(2 − a·x_n)`.
///
/// `a` is a unit of `Z_{2^32}[X]/(X^64+1)` iff its coefficient sum is odd
/// (the reduction mod 2 is `F_2[X]/(X+1)^64`, a local ring whose units are
/// the elements with `X = 1` evaluation equal to 1).
fn ring_inv_newton(a: &Z2Ring) -> Option<Z2Ring> {
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
        let x63 = ring_from_u32(&c);
        let mut c1 = [0u32; D];
        c1[1] = 1;
        let x = ring_from_u32(&c1);
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
    #[ignore]
    fn gate_debug_sequential() {
        let (r1cs, z) = gen_toy_instance(b"dbg00000000000000000000000000000", 8, 4);
        for k in 0..r1cs.a.len() {
            let mut acc = Z2Ring::zero();
            for (j, coeff) in &r1cs.a[k].terms {
                acc += coeff.clone() * z[*j].clone();
            }
            let sq = acc.clone() * acc.clone();
            let rhs = r1cs.u[k].clone() * z[r1cs.sel[k]].clone();
            println!(
                "gate {k}: sq={:?} rhs={:?} match={}",
                &ring_to_u32(&sq)[..2],
                &ring_to_u32(&rhs)[..2],
                ring_to_u32(&sq) == ring_to_u32(&rhs)
            );
        }
        println!("satisfied: {}", r1cs.is_satisfied(&z));
    }

    #[test]
    fn toy_instance_is_satisfied_by_generated_witness() {
        let (r1cs, z) = gen_toy_instance(b"toy00000000000000000000000000000", 64, 8);
        assert!(r1cs.is_satisfied(&z));
        // tampering breaks satisfaction
        let mut z_bad = z.clone();
        z_bad[0] = z_bad[0].clone() + Z2Ring::one();
        assert!(!r1cs.is_satisfied(&z_bad));
    }
}
