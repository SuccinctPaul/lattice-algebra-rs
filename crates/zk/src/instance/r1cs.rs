//! Toy R1CS instance over the Z2 ring (L5 instance domain).
//!
//! A [`ToyR1cs`] is a system of **squaring gates**
//! `(A_k·z) ∘ (A_k·z) = U_k · z_{sel_k}`: any R1CS reduces to squaring gates
//! (introduce one auxiliary variable per product, `B = I`), so this reduced
//! form is representative. "≈10^4 constraints" means 10^4 ring rows — each
//! one a 64-lane batch of scalar constraints.
//!
//! The gate-mapping helpers are the shared traversal used by the opening,
//! folding and shortness protocols (sequential, or parallel across threads
//! when the `parallel` feature is on and the instance is large enough).

use crate::foundation::encoding::ring_from_u32;
use crate::foundation::sampling::uniform_poly;
use crate::instance::ring::{ring_inv_newton, Z2Coeff, Z2Ring, D};
use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::ring::MatrixElement;
use algebra::ring::PolynomialQuotientRing;

/// Gate-count threshold above which the `parallel` feature engages. Below
/// it, per-task dispatch overhead outweighs the per-gate ring work.
#[cfg(feature = "parallel")]
const PARALLEL_GATE_THRESHOLD: usize = 256;

/// Maps `f` over the gates of `r1cs` (sequential, or parallel across
/// threads when the `parallel` feature is on and the instance is large
/// enough to amortize the dispatch).
pub(crate) fn map_over_gates<T, F>(r1cs: &ToyR1cs, f: F) -> Vec<T>
where
    T: Send,
    F: Fn(usize, &SparseRow) -> T + Sync,
{
    #[cfg(feature = "parallel")]
    {
        if r1cs.a.len() >= PARALLEL_GATE_THRESHOLD {
            use rayon::prelude::*;
            return (0..r1cs.a.len())
                .into_par_iter()
                .map(|k| f(k, &r1cs.a[k]))
                .collect();
        }
    }
    (0..r1cs.a.len()).map(|k| f(k, &r1cs.a[k])).collect()
}

/// All-gates predicate with the same thresholding as [`map_over_gates`]
/// (short-circuits on the first failing gate).
pub(crate) fn all_over_gates<P>(r1cs: &ToyR1cs, pred: P) -> bool
where
    P: Fn(usize, &SparseRow) -> bool + Sync,
{
    #[cfg(feature = "parallel")]
    {
        if r1cs.a.len() >= PARALLEL_GATE_THRESHOLD {
            use rayon::prelude::*;
            return (0..r1cs.a.len())
                .into_par_iter()
                .all(|k| pred(k, &r1cs.a[k]));
        }
    }
    (0..r1cs.a.len()).all(|k| pred(k, &r1cs.a[k]))
}

/// A sparse row of a toy-R1CS constraint: `(column, coefficient)` terms.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SparseRow {
    /// The non-zero `(column index, coefficient)` terms.
    pub terms: Vec<(usize, Z2Ring)>,
}

/// Toy R1CS instance over `R`: squaring gates
/// `(A_k·z) ∘ (A_k·z) = U_k · z_{sel_k}`.
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
    ///
    /// With the `parallel` feature the gates are checked across threads for
    /// large instances (short-circuiting on the first failure).
    pub fn is_satisfied(&self, z: &[Z2Ring]) -> bool {
        if z.len() != self.num_vars {
            return false;
        }
        all_over_gates(self, |k, row| {
            let mut acc = Z2Ring::zero();
            for (j, coeff) in &row.terms {
                acc += coeff.clone() * z[*j].clone();
            }
            let sq = acc.clone() * acc.clone();
            let rhs = self.u[k].clone() * z[self.sel[k]].clone();
            sq.coefficients() == rhs.coefficients()
        })
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
    let mut stream = BitStream::new(&mut xof);

    // random unit witness: elements ≡ 1 (mod 2) — odd constant term, all
    // other coefficients even — so `a − 1 ∈ 2R` and Newton's iteration for
    // the ring inverse converges (needed to derive the gate outputs U_k).
    let mut witness = Vec::with_capacity(num_vars);
    for _ in 0..num_vars {
        let mut coeffs = [0u32; D];
        let mut buf = [0u8; 4];
        stream.read_bytes(&mut buf);
        coeffs[0] = u32::from_le_bytes(buf) | 1; // odd constant term
        for c in &mut coeffs[1..] {
            stream.read_bytes(&mut buf);
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
            let coeff = uniform_poly::<Z2Coeff, _, D>(&mut stream);
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

#[cfg(test)]
mod tests {
    use super::*;

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
                &crate::foundation::encoding::ring_to_u32(&sq)[..2],
                &crate::foundation::encoding::ring_to_u32(&rhs)[..2],
                crate::foundation::encoding::ring_to_u32(&sq)
                    == crate::foundation::encoding::ring_to_u32(&rhs)
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
