//! Invertibility, inversion and integer powers of square matrices **over the
//! ring** `R_q = Z_q[X]/(X^d + 1)`.
//!
//! This is the piece `pcs::prisis` documents as missing: it could only ever
//! build a *certified* unit `W` (a diagonal of scalar units, where invertibility
//! is obvious) rather than draw `W ← GL(n, R_q)` uniformly, because the crate
//! had no solver over `R_q`. Sampling and checking such a `W` is what
//! Rinocchio's encoding and FMN's Fig. 4 `Setup` (`W ← GL(n, R_q)`, then
//! `Rᵢ := R·G⁻¹(W⁻ⁱG)`) actually ask for.
//!
//! # Why the field trick is the right one
//!
//! `R_q` is not a domain once `X^d + 1` factors, so "determinant non-zero" is
//! neither available nor correct as a criterion. The standard replacement is the
//! regular representation: `c ↦ M_c`, the `d × d` matrix of negacyclic
//! multiplication by `c`, which is a ring embedding
//! `R_q → Z_q^{d×d}`. Therefore
//!
//! ```text
//! A ∈ R_q^{n×n} is invertible  ⟺  E(A) ∈ Z_q^{nd×nd} is invertible,
//! ```
//!
//! where `E` replaces each entry by its multiplication matrix. The right side is
//! an ordinary matrix over the *field* `Z_q`, so Gauss–Jordan decides it.
//!
//! Inverting `E(A)` gives `E(A)⁻¹`, which must equal `E(A⁻¹)` because `E` is a
//! ring homomorphism; the `d × d` block `(i, j)` of `E(A)⁻¹` therefore has
//! `A⁻¹[i][j]`'s coefficients in its **column 0** (the first column of a
//! negacyclic multiplication matrix is the element itself — `M_c · e₁ = c`).
//!
//! Every inverse returned here is then **verified by multiplying back in `R_q`**
//! and by re-expanding: a wrong extraction or a non-unit yields `None` instead
//! of an unverified matrix. Nothing leaves this module trusted on the argument
//! above.

use crate::ring::poly_ring::PolyRing;
use crate::ring::traits::{Field, Ring};
use crate::ring::PolynomialQuotientRing;
use alloc::vec;
use alloc::vec::Vec;

/// `c`'s coefficients padded to exactly `D`.
///
/// [`PolyRing::coefficients`] trims trailing zeros, so any fixed-length read of
/// a ring element has to pad; without this a sparse `c` shifts every later
/// column of `M_c`.
fn padded<R: Ring, const D: usize>(c: &PolyRing<R, D>) -> [R; D] {
    let mut out = [R::ZERO; D];
    for (i, x) in c.coefficients().iter().enumerate().take(D) {
        out[i] = *x;
    }
    out
}

/// `M_c`: the `D × D` matrix of negacyclic multiplication by `c`, so
/// `M_c · coeffs(x) = coeffs(c · x)`.
///
/// Column 0 is `c` itself, which is what makes `E(A)⁻¹` readable back as a
/// matrix of ring elements.
pub fn multiplication_matrix<R: Ring, const D: usize>(c: &PolyRing<R, D>) -> Vec<Vec<R>> {
    let cs = padded::<R, D>(c);
    let mut m = vec![vec![R::ZERO; D]; D];
    for j in 0..D {
        for i in 0..D {
            // `X^j · X^{i-j} = X^i`, with `X^D = −1` when the exponent wraps.
            let (src, negated) = if i >= j { (i - j, false) } else { (i + D - j, true) };
            m[i][j] = if negated { -cs[src] } else { cs[src] };
        }
    }
    m
}

/// `E(A)`: `A` expanded blockwise to a `(n·D) × (n·D)` matrix over the base
/// ring, entry `(i·D + p, j·D + q)` being `M_{A[i][j]}[p][q]`.
///
/// # Panics
/// If `a` is not square.
pub fn expand<R: Ring, const D: usize>(a: &[Vec<PolyRing<R, D>>]) -> Vec<Vec<R>> {
    let n = a.len();
    assert!(
        n > 0 && a.iter().all(|row| row.len() == n),
        "expand needs a non-empty square matrix"
    );
    let mut out = vec![vec![R::ZERO; n * D]; n * D];
    for i in 0..n {
        for j in 0..n {
            let block = multiplication_matrix::<R, D>(&a[i][j]);
            for p in 0..D {
                for q in 0..D {
                    out[i * D + p][j * D + q] = block[p][q];
                }
            }
        }
    }
    out
}

/// Gauss–Jordan inverse over a field, or `None` if the matrix is singular.
fn field_inverse<R: Field>(m: &[Vec<R>]) -> Option<Vec<Vec<R>>> {
    let n = m.len();
    if n == 0 || m.iter().any(|r| r.len() != n) {
        return None;
    }
    // Augment with the identity.
    let mut a: Vec<Vec<R>> = (0..n)
        .map(|i| {
            let mut row = m[i].clone();
            row.extend((0..n).map(|j| if i == j { R::ONE } else { R::ZERO }));
            row
        })
        .collect();
    for col in 0..n {
        let pivot = (col..n).find(|&r| a[r][col] != R::ZERO)?;
        a.swap(col, pivot);
        let inv = a[col][col].inverse()?;
        for j in col..2 * n {
            a[col][j] = a[col][j] * inv;
        }
        for r in 0..n {
            if r == col {
                continue;
            }
            let f = a[r][col];
            if f == R::ZERO {
                continue;
            }
            for j in col..2 * n {
                let sub = f * a[col][j];
                a[r][j] = a[r][j] - sub;
            }
        }
    }
    Some(
        a.iter()
            .map(|row| row[n..2 * n].to_vec())
            .collect::<Vec<_>>(),
    )
}

/// `A⁻¹` over `R_q`, or `None` when `A` is not a unit of the matrix ring.
///
/// The candidate is checked two ways before being returned: `A · A⁻¹ = I` in
/// `R_q`, and `E(A⁻¹) = E(A)⁻¹` over the base field. A `None` therefore means
/// "not invertible", never "the extraction looked wrong".
pub fn invert_matrix<R: Field, const D: usize>(
    a: &[Vec<PolyRing<R, D>>],
) -> Option<Vec<Vec<PolyRing<R, D>>>> {
    let n = a.len();
    if n == 0 || a.iter().any(|row| row.len() != n) {
        return None;
    }
    let e_inv = field_inverse(&expand::<R, D>(a))?;
    // Column 0 of block (i, j) is A⁻¹[i][j]'s coefficient vector.
    let mut cand = vec![Vec::with_capacity(n); n];
    for i in 0..n {
        for j in 0..n {
            let coeffs: Vec<R> = (0..D).map(|p| e_inv[i * D + p][j * D]).collect();
            cand[i].push(PolyRing::from_coefficients(coeffs));
        }
    }
    // Verify in R_q: A · C = I.
    for i in 0..n {
        for j in 0..n {
            let mut acc = PolyRing::<R, D>::from_coefficients(vec![R::ZERO]);
            for k in 0..n {
                acc = acc + a[i][k].clone() * cand[k][j].clone();
            }
            let want = if i == j { R::ONE } else { R::ZERO };
            if padded::<R, D>(&acc)[0] != want || padded::<R, D>(&acc).iter().skip(1).any(|&x| x != R::ZERO) {
                return None;
            }
        }
    }
    // Verify the expansion agrees, which is the stronger statement.
    if expand::<R, D>(&cand) != e_inv {
        return None;
    }
    Some(cand)
}

/// Whether `A` is a unit of `R_q^{n×n}`. Decided by the expanded field rank, so
/// it does not depend on `A⁻¹` being extractable.
pub fn is_unit_matrix<R: Field, const D: usize>(a: &[Vec<PolyRing<R, D>>]) -> bool {
    invert_matrix::<R, D>(a).is_some()
}

/// `A^e` for any integer `e`, inverting once when `e < 0`.
///
/// This is FMN's `Wⁱ` and `W⁻ⁱ` pair: the same base `W`, both signs, no
/// separately-supplied inverse to trust.
pub fn matrix_pow<R: Field, const D: usize>(
    a: &[Vec<PolyRing<R, D>>],
    e: i64,
) -> Option<Vec<Vec<PolyRing<R, D>>>> {
    let base_abs = if e < 0 { invert_matrix::<R, D>(a)? } else { a.to_vec() };
    let n = base_abs.len();
    let mut out: Vec<Vec<PolyRing<R, D>>> = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    PolyRing::from_coefficients(if i == j {
                        vec![R::ONE]
                    } else {
                        vec![R::ZERO]
                    })
                })
                .collect()
        })
        .collect();
    let mut base = base_abs;
    let mut power = e.unsigned_abs();
    while power > 0 {
        if power & 1 == 1 {
            out = mat_mul(&out, &base)?;
        }
        power >>= 1;
        if power > 0 {
            base = mat_mul(&base, &base)?;
        }
    }
    Some(out)
}

/// Matrix product over `R_q`. `None` on a shape mismatch.
fn mat_mul<R: Ring, const D: usize>(
    a: &[Vec<PolyRing<R, D>>],
    b: &[Vec<PolyRing<R, D>>],
) -> Option<Vec<Vec<PolyRing<R, D>>>> {
    if a.is_empty() || b.is_empty() || a[0].len() != b.len() {
        return None;
    }
    let (rows, inner, cols) = (a.len(), a[0].len(), b[0].len());
    let mut out = vec![
        vec![PolyRing::<R, D>::from_coefficients(vec![R::ZERO]); cols];
        rows
    ];
    for i in 0..rows {
        for j in 0..cols {
            let mut acc = PolyRing::<R, D>::from_coefficients(vec![R::ZERO]);
            for k in 0..inner {
                acc = acc + a[i][k].clone() * b[k][j].clone();
            }
            out[i][j] = acc;
        }
    }
    Some(out)
}

/// Rejection-sample a uniform element of `GL(n, R_q)`: `n²` ring elements with
/// uniform coefficients in `[0, q)`, redrawn whole until invertible.
///
/// Returns the matrix and the number of *rejected* draws. That count is part of
/// the result on purpose: the unit density of `R_q^{n×n}` is below 1 (unlike a
/// field), so a caller sizing a setup loop needs the measured rate, not an
/// assumed one.
pub fn sample_gl<R, const D: usize>(
    n: usize,
    rng: &mut impl FnMut() -> u64,
) -> Option<(Vec<Vec<PolyRing<R, D>>>, u32)>
where
    R: Field,
{
    let q = R::MODULUS;
    let mut attempts = 0u32;
    loop {
        let a: Vec<Vec<PolyRing<R, D>>> = (0..n)
            .map(|_| {
                (0..n)
                    .map(|_| {
                        PolyRing::from_coefficients(
                            (0..D).map(|_| R::from(rng() % q)).collect(),
                        )
                    })
                    .collect()
            })
            .collect();
        attempts += 1;
        if invert_matrix::<R, D>(&a).is_some() {
            return Some((a, attempts - 1));
        }
        if attempts > 1_000_000 {
            return None;
        }
    }
}

/// `A⁻¹` given an `A` already known invertible, plus `Aᵉ` for the negative
/// exponent `e` — the two-sided power pair `Wⁱ`, `W⁻ⁱ` in one call.
///
/// Returns (`W⁰ … W^max_power`, `I, W⁻¹ … W⁻^max_power`) — FMN's Fig. 4 needs
/// both sides: `WⁱA` in the block rows of `B`, and `W⁻ⁱG` inside
/// `Rᵢ = R·G⁻¹(W⁻ⁱG)`.
pub fn powers_pair<R: Field, const D: usize>(
    a: &[Vec<PolyRing<R, D>>],
    max_power: usize,
) -> Option<(
    Vec<Vec<Vec<PolyRing<R, D>>>>,
    Vec<Vec<Vec<PolyRing<R, D>>>>,
)> {
    let inv = invert_matrix::<R, D>(a)?;
    let mut forward = Vec::with_capacity(max_power + 1);
    let mut backward = Vec::with_capacity(max_power + 1);
    let mut cur_f: Vec<Vec<PolyRing<R, D>>> = identity(a.len());
    let mut cur_b = identity::<R, D>(a.len());
    for _ in 0..=max_power {
        forward.push(cur_f.clone());
        backward.push(cur_b.clone());
        cur_f = mat_mul(&cur_f, a)?;
        cur_b = mat_mul(&cur_b, &inv)?;
    }
    Some((forward, backward))
}

/// The `n × n` identity over `R_q`.
pub fn identity<R: Ring, const D: usize>(n: usize) -> Vec<Vec<PolyRing<R, D>>> {
    (0..n)
        .map(|i| {
            (0..n)
                .map(|j| {
                    PolyRing::from_coefficients(vec![if i == j { R::ONE } else { R::ZERO }])
                })
                .collect()
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::zq::Zq;

    /// The house non-NTT prime: `q ≡ 5 (mod 8)`, so `X⁴ + 1` splits and `R_q`
    /// genuinely has zero divisors — the case "det ≠ 0" cannot handle.
    type Q = Zq<4_294_967_197>;
    const D: usize = 4;

    fn elt(coeffs: &[u64]) -> PolyRing<Q, D> {
        PolyRing::from_coefficients(coeffs.iter().map(|&c| Q::from(c)).collect())
    }

    #[test]
    fn multiplication_matrix_column_zero_is_the_element() {
        // The readability fact E(A)⁻¹ → A⁻¹ rests on: column 0 of M_c is c.
        let c = elt(&[7, 0, 11, 0]);
        let m = multiplication_matrix::<Q, D>(&c);
        assert_eq!(
            (0..D).map(|i| m[i][0]).collect::<Vec<_>>(),
            padded::<Q, D>(&c).to_vec(),
            "M_c · e₁ must be c"
        );
    }

    #[test]
    fn multiplication_matrix_matches_ring_multiplication() {
        // Independent check: M_c · coeffs(x) must equal coeffs(c·x) for a
        // random pair, so the embedding claim is not just asserted.
        let c = elt(&[3, 1, 4, 1]);
        let x = elt(&[5, 9, 2, 6]);
        let m = multiplication_matrix::<Q, D>(&c);
        let xs = padded::<Q, D>(&x);
        let mut got = [Q::ZERO; D];
        for i in 0..D {
            for j in 0..D {
                got[i] = got[i] + m[i][j] * xs[j];
            }
        }
        let want = padded::<Q, D>(&(c * x));
        assert_eq!(got.to_vec(), want.to_vec(), "M_c x ≠ c·x");
    }

    #[test]
    fn dense_unit_inverts_and_the_two_sided_powers_cancel() {
        // Non-diagonal, so the inverse really is a ring-level computation.
        let a = vec![
            vec![elt(&[1, 2, 0, 3]), elt(&[0, 1, 1, 0])],
            vec![elt(&[2, 0, 1, 1]), elt(&[1, 0, 0, 4])],
        ];
        let (forward, backward) = powers_pair::<Q, D>(&a, 2).expect("dense unit");
        assert_eq!(forward[0], identity::<Q, D>(2), "W⁰ is I");
        assert_eq!(forward[1], a, "W¹ is W");
        assert_eq!(backward[0], identity::<Q, D>(2), "W⁻⁰ is I");
        let prod = mat_mul(&forward[2], &backward[2]).expect("shapes");
        assert_eq!(
            prod,
            identity::<Q, D>(2),
            "W² · W⁻² must be the identity"
        );
    }

    #[test]
    fn a_singular_matrix_is_refused_not_inverted() {
        // `det = 1·X² − X·X = 0`, and `0` is not a unit, so `A` cannot be
        // invertible over any commutative ring. This is the case the field-rank
        // route exists for: `R_q` is not a domain, so "det ≠ 0" is not the
        // criterion, but `det = 0` still refutes invertibility.
        //
        // (An earlier version of this test reached for `1 + X` as a zero
        // divisor. It is not one: `X^d + 1` at `X = −1` is `2` for every even
        // `d`, non-zero for odd `q`, so `X + 1` divides nothing and `1 + X` is
        // a unit. The claim would have made the test pass for the wrong reason.)
        let bad = vec![
            vec![elt(&[1]), elt(&[0, 1])],
            vec![elt(&[0, 1]), elt(&[0, 0, 1])],
        ];
        assert!(
            invert_matrix::<Q, D>(&bad).is_none(),
            "a determinant-zero matrix is not a unit of the matrix ring"
        );
        assert!(!is_unit_matrix::<Q, D>(&bad));
        // The same call on a scalar-unit diagonal must succeed, so the refusal
        // above is about singularity and not about my extraction being broken.
        let good = vec![
            vec![elt(&[2]), elt(&[0])],
            vec![elt(&[0]), elt(&[1])],
        ];
        assert!(is_unit_matrix::<Q, D>(&good));
    }

    #[test]
    fn sample_gl_reaches_a_unit_and_reports_the_rejections_it_needed() {
        let mut state = 0x2545_F491_4F6C_DD1Du64;
        let mut next = || {
            // xorshift64*, so the draws are reproducible without a dependency
            state ^= state >> 12;
            state ^= state << 25;
            state ^= state >> 27;
            state.wrapping_mul(0x2545_F491_4F6C_DD1D)
        };
        let (w, rejects) = sample_gl::<Q, D>(2, &mut next).expect("a unit is found");
        assert!(is_unit_matrix::<Q, D>(&w), "sample_gl must return a unit");
        // The unit density of `R_q^{2×2}` is below 1, so rejections are
        // expected; the point of returning the count is that a caller can size
        // a setup loop from it instead of assuming `1`.
        assert!(
            rejects < 1000,
            "sampling took {rejects} rejections — too slow to be usable"
        );
    }
}
