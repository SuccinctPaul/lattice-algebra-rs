//! Reducing ring equations to field identities (eprint 2026/1983 §3.6, §7.3,
//! Appendix B.1).
//!
//! Akita's fold equations live in cyclotomic rings `R_{q,d} = Z_q[X]/(X^d + 1)`,
//! but sum-check runs over a field, and substituting `X = alpha` does **not**
//! respect a modular equality. The paper's two fixes are both implemented here,
//! on plain coefficient slices so a single batch can mix native dimensions
//! (`d_A`, `d_B`, `d_D`, `d_car`, the compression dimensions) exactly as
//! Lemma 3.9 and Remark 3.10 allow:
//!
//! * **quotient lift** (Lemma 3.8): `M w = h` in `R_{q,d}` iff
//!   `M~ w~ = h~ + (X^d + 1) r` in `Z_q[X]` with `r` unique and `deg r <= d - 2`.
//!   The witness supplies `r`, so the price is `d - 1` extra digit planes per row
//!   carried into the next recursive witness (Eq. 109). Soundness: `2 d_max - 1`
//!   bad `alpha` (Lemma 3.9).
//! * **quotient-free transpose convolution** (Lemma 7.1, Theorem 7.2): fold the
//!   reduction into the *verifier's weights* through the residue kernel
//!   `kappa^{(d)}_{A,alpha}(j) = (A(X) X^j mod (X^d + 1))(alpha)`, so the check
//!   is `sum_j w_j kappa(j) = Y(alpha)` and no private polynomial exists. Price:
//!   the kernel per row. Gain: `d_max - 1` bad `alpha` instead of `2 d_max - 1`,
//!   no quotient interval in the successor witness, and — Theorem 7.2's last
//!   sentence — *"No step divides by `alpha^{d_r} + 1`"*, so `alpha` values that
//!   are roots of the modulus need no rejection at all.
//!
//! # The kernel is linear-time, and that is a checked property
//!
//! Consecutive basis monomials differ by one multiplication by `X`, so
//! `kappa(j + 1) = alpha * kappa(j) - (alpha^d + 1) * a_{d-1-j}` (Lemma B.1).
//! The tests pin the recurrence against the `O(d^2)` expansion of Eq. (153) and
//! the transposed kernel of Eq. (287) against Eq. (288)'s exchange of summation
//! order, because a wrong wraparound sign passes every algebraic test that only
//! uses one side of the transpose.

use algebra::ring::Ring;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Which route a fold uses to turn its ring rows into field equations
/// (§5.1's `RingCheck` configuration field).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RingCheck {
    /// Private quotient per row (Lemma 3.8); quotient digits join the successor
    /// witness (Eq. 109).
    QuotientLift,
    /// Reduction folded into the public weights (Lemma 7.1); no quotient
    /// witness at all.
    QuotientFree,
}

/// The number of `alpha` values that can hide a false row, per route:
/// `d_max - 1` quotient-free (Theorem 7.2), `2 d_max - 1` quotient-lift
/// (Lemma 3.9). Dividing by `|E|` gives the per-reduction soundness error the
/// schedule charges.
pub const fn root_bound(route: RingCheck, d_max: usize) -> usize {
    match route {
        RingCheck::QuotientFree => d_max - 1,
        RingCheck::QuotientLift => 2 * d_max - 1,
    }
}

/// Why a row could not be reduced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReduceError {
    /// The ring equation itself fails: no quotient exists, because the residue
    /// of the left side modulo `X^d + 1` is not the target.
    RowDoesNotHold {
        /// The first coefficient where the residue and the target differ.
        coefficient: usize,
    },
    /// A slice was not `d` coefficients long.
    WrongLength {
        /// Length supplied.
        got: usize,
        /// Length the native dimension requires.
        expected: usize,
    },
}

impl fmt::Display for ReduceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReduceError::RowDoesNotHold { coefficient } => {
                write!(
                    f,
                    "row residue differs from the target at coefficient {coefficient}"
                )
            }
            ReduceError::WrongLength { got, expected } => {
                write!(
                    f,
                    "{got} coefficients against a native dimension of {expected}"
                )
            }
        }
    }
}

/// `sum_j coeffs[j] * alpha^j` — evaluation of the canonical degree-`< d`
/// representative (Eq. 53's `w_x(alpha)` contraction against the power ladder).
pub fn eval_poly<R: Ring>(coeffs: &[R], alpha: R) -> R {
    let mut acc = R::ZERO;
    let mut power = R::ONE;
    for c in coeffs {
        acc += power * *c;
        power *= alpha;
    }
    acc
}

/// The shared power ladder `{alpha^{2^j}}_{j < bits}` (Lemma 3.9 part 3: "all
/// truncated weights are prefixes of one tensor", so one ladder serves every
/// native dimension in the batch).
///
/// # Panics
/// If `bits` exceeds 64 (the ladder length is a schedule constant).
pub fn power_ladder<R: Ring>(alpha: R, bits: usize) -> Vec<R> {
    assert!(bits <= 64, "ladder length must fit a u64 exponent");
    let mut out = Vec::with_capacity(bits);
    let mut cur = alpha;
    for _ in 0..bits {
        out.push(cur);
        cur = cur.square();
    }
    out
}

/// The `(1, alpha, ..., alpha^{d-1})` weight vector Eq. (53) contracts a
/// witness ring element with.
pub fn alpha_powers<R: Ring>(alpha: R, d: usize) -> Vec<R> {
    let mut out = Vec::with_capacity(d);
    let mut power = R::ONE;
    for _ in 0..d {
        out.push(power);
        power *= alpha;
    }
    out
}

/// Negacyclic product modulo `X^d + 1` (Eq. 146's `⊛_d`).
///
/// # Panics
/// If either operand is not exactly `d` coefficients long.
pub fn nega_mul<R: Ring>(a: &[R], b: &[R], d: usize) -> Vec<R> {
    assert_eq!(a.len(), d, "operand length must match the dimension");
    assert_eq!(b.len(), d, "operand length must match the dimension");
    let mut out = vec![R::ZERO; d];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            if i + j < d {
                out[i + j] += x * y;
            } else {
                out[i + j - d] -= x * y;
            }
        }
    }
    out
}

/// The unreduced convolution of two degree-`< d` representatives: length
/// `2d - 1`, the object Lemma 3.8's identity is stated in.
///
/// # Panics
/// If the operands have different lengths.
pub fn unreduced_mul<R: Ring>(a: &[R], b: &[R]) -> Vec<R> {
    assert_eq!(a.len(), b.len(), "both operands share the native dimension");
    let d = a.len();
    let mut out = vec![R::ZERO; 2 * d - 1];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

/// The unique quotient of Lemma 3.8: given the polynomial residual
/// `p = sum_c A_c W_c - Y` in `Z_q[X]` of degree at most `2d - 2`, returns `r`
/// with `p = (X^d + 1) r` — or
/// [`ReduceError::RowDoesNotHold`] when the ring equation is false, since then no
/// such `r` exists.
///
/// Division is by top-down synthetic steps against the *monic* modulus, so no
/// coefficient inverse is taken: the route stays exact at every `alpha`, and the
/// returned quotient has degree at most `d - 2` by construction (Lemma 3.8's
/// stated bound, asserted below).
///
/// # Panics
/// If `p` is shorter than `d` or longer than `2d - 1`.
pub fn quotient<R: Ring>(p: &[R], d: usize) -> Result<Vec<R>, ReduceError> {
    assert!(
        p.len() >= d && p.len() <= 2 * d - 1,
        "residual degree must be within [d-1, 2d-2]"
    );
    let mut work = p.to_vec();
    let mut q = vec![R::ZERO; d - 1];
    for deg in (d..work.len()).rev() {
        let c = work[deg];
        if c != R::ZERO {
            q[deg - d] += c;
            work[deg - d] -= c;
        }
        work[deg] = R::ZERO;
    }
    if let Some(i) = work.iter().position(|&c| c != R::ZERO) {
        return Err(ReduceError::RowDoesNotHold { coefficient: i });
    }
    debug_assert_eq!(q.len(), quotient_len(d), "deg r <= d - 2");
    Ok(q)
}
/// `quotient`'s degree statement: the returned vector is `d - 1` long, i.e.
/// `deg r <= d - 2`, exactly Lemma 3.8's bound.
pub const fn quotient_len(d: usize) -> usize {
    d - 1
}

/// The row form of Lemma 3.8: `A W = Y` in `R_{q,d}` iff the residual admits a
/// quotient. Returns the quotient, or the error naming the differing
/// coefficient.
///
/// # Errors
/// [`ReduceError::RowDoesNotHold`] if the ring equation is false,
/// [`ReduceError::WrongLength`] if an operand is not `d` long.
pub fn row_quotient<R: Ring>(a: &[R], w: &[R], y: &[R], d: usize) -> Result<Vec<R>, ReduceError> {
    if a.len() != d || w.len() != d || y.len() != d {
        return Err(ReduceError::WrongLength {
            got: a.len().min(w.len()).min(y.len()),
            expected: d,
        });
    }
    let full = unreduced_mul(a, w);
    let residual: Vec<R> = (0..full.len())
        .map(|i| if i < d { full[i] - y[i] } else { full[i] })
        .collect();
    quotient(&residual, d)
}

/// The residue kernel `kappa^{(d)}_{A,alpha}(j)` of Eq. (152)-(153), computed by
/// the `O(d)` wraparound recurrence of Lemma B.1.
///
/// This is the *public weight of the witness coefficient `w_j`* in the
/// quotient-free check: Lemma 7.1 says `sum_j w_j kappa(j)` is exactly
/// `(A W mod (X^d + 1))(alpha)`.
///
/// # Panics
/// If `a.len() != d`.
pub fn residue_kernel<R: Ring>(a: &[R], alpha: R, d: usize) -> Vec<R> {
    assert_eq!(a.len(), d, "the multiplier must be d coefficients long");
    // kappa(0) = A(alpha); kappa(j+1) = alpha*kappa(j) - (alpha^d + 1)a_{d-1-j}
    let a_alpha = eval_poly(a, alpha);
    let alpha_d_plus_one = alpha.pow(d as u64) + R::ONE;
    let mut out = Vec::with_capacity(d);
    let mut cur = a_alpha;
    for j in 0..d {
        out.push(cur);
        if j < d - 1 {
            cur = alpha * cur - alpha_d_plus_one * a[d - 1 - j];
        }
    }
    out
}

/// The quadratic reference form of Eq. (153), kept so the fast kernel is checked
/// against the definition rather than against itself.
pub fn residue_kernel_reference<R: Ring>(a: &[R], alpha: R, d: usize) -> Vec<R> {
    let powers = alpha_powers(alpha, 2 * d);
    (0..d)
        .map(|j| {
            let mut acc = R::ZERO;
            for (k, &ak) in a.iter().enumerate().take(d) {
                if k + j < d {
                    acc += ak * powers[k + j];
                } else {
                    acc -= ak * powers[k + j - d];
                }
            }
            acc
        })
        .collect()
}

/// The *transposed* residue kernel of Eq. (287): given an exact equality
/// sequence `e_j` over a row's native coefficient positions, `kappa^T(k)` is the
/// weight the verifier puts on the public multiplier's coefficient `a_k`.
///
/// Eq. (288) makes `sum_j e_j kappa_{A,alpha}(j) = sum_k a_k kappa^T_{e,alpha}(k)`,
/// which is what lets a verifier read a row off the *setup* coefficients instead
/// of the witness ones (Appendix B.4's offloaded weight).
///
/// # Panics
/// If `e.len() != d`.
pub fn transposed_kernel<R: Ring>(e: &[R], alpha: R, d: usize) -> Vec<R> {
    assert_eq!(e.len(), d, "the equality sequence must be d long");
    // (289): kappa^T(0) = sum_j e_j alpha^j, then the same recurrence (290).
    let alpha_d_plus_one = alpha.pow(d as u64) + R::ONE;
    let mut out = Vec::with_capacity(d);
    let mut cur = eval_poly(e, alpha);
    for k in 0..d {
        out.push(cur);
        if k < d - 1 {
            cur = alpha * cur - alpha_d_plus_one * e[d - 1 - k];
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    /// The paper's Table 5 modulus: prime, `5 mod 8`, `X^d + 1` irreducible-ish
    /// (two factors), so no NTT of degree >= 4 exists.
    type Q32 = Zq<4_294_967_197>;
    /// A small field, so a root count can be taken by enumeration.
    type F17 = Zq<17>;

    fn rand_coeffs<R: Ring>(d: usize, seed: &mut u64) -> Vec<R> {
        (0..d)
            .map(|_| {
                *seed = seed
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                R::from((*seed >> 33) % R::MODULUS)
            })
            .collect()
    }

    #[test]
    fn negacyclic_product_wraps_with_a_minus_sign() {
        // X^{d-1} * X = -1 is the whole difference between cyclic and
        // negacyclic; a missing sign would silently break every row.
        let d = 8usize;
        let mut a = vec![Q32::ZERO; d];
        a[d - 1] = Q32::ONE;
        let mut b = vec![Q32::ZERO; d];
        b[1] = Q32::ONE;
        let prod = nega_mul(&a, &b, d);
        assert_eq!(prod[0], -Q32::ONE);
        assert!(prod[1..].iter().all(|v| *v == Q32::ZERO));
        // and the unreduced product keeps the high term for the lift
        let full = unreduced_mul(&a, &b);
        assert_eq!(full[d], Q32::ONE);
        assert_eq!(full.len(), 2 * d - 1);
    }

    #[test]
    fn residue_kernel_recurrence_equals_the_expansion() {
        // Lemma B.1 vs Eq. (153), the O(d) path against the O(d^2) definition.
        let mut seed = 11u64;
        for d in [2usize, 4, 8, 16] {
            for _ in 0..5 {
                let a: Vec<Q32> = rand_coeffs(d, &mut seed);
                let alpha: Q32 = rand_coeffs(1, &mut seed)[0];
                assert_eq!(
                    residue_kernel(&a, alpha, d),
                    residue_kernel_reference(&a, alpha, d),
                    "d = {d}"
                );
            }
        }
    }

    #[test]
    fn transpose_convolution_identity_holds_for_every_point() {
        // Lemma 7.1: (A W mod (X^d+1))(alpha) == sum_j w_j kappa(j).
        let mut seed = 5u64;
        let d = 8usize;
        for _ in 0..10 {
            let a: Vec<Q32> = rand_coeffs(d, &mut seed);
            let w: Vec<Q32> = rand_coeffs(d, &mut seed);
            let alpha: Q32 = rand_coeffs(1, &mut seed)[0];
            let reduced = nega_mul(&a, &w, d);
            let lhs = eval_poly(&reduced, alpha);
            let k = residue_kernel(&a, alpha, d);
            let rhs: Q32 = (0..d).map(|j| w[j] * k[j]).fold(Q32::ZERO, |x, y| x + y);
            assert_eq!(lhs, rhs);
        }
    }

    #[test]
    fn transposed_kernel_exchanges_the_summation_order() {
        // Eq. (288) and the recurrence (289)/(290).
        let mut seed = 9u64;
        for d in [2usize, 4, 8] {
            for _ in 0..6 {
                let a: Vec<F17> = rand_coeffs(d, &mut seed);
                let e: Vec<F17> = rand_coeffs(d, &mut seed);
                let alpha: F17 = rand_coeffs(1, &mut seed)[0];
                let k = residue_kernel(&a, alpha, d);
                let lhs: F17 = (0..d).map(|j| e[j] * k[j]).fold(F17::ZERO, |x, y| x + y);
                let kt = transposed_kernel(&e, alpha, d);
                let rhs: F17 = (0..d)
                    .map(|kk| a[kk] * kt[kk])
                    .fold(F17::ZERO, |x, y| x + y);
                assert_eq!(lhs, rhs, "d = {d}");
                // and the transposed kernel against its own definition
                let direct: Vec<F17> = (0..d)
                    .map(|kk| {
                        (0..d)
                            .map(|j| {
                                let wrap = ((kk + j) / d) % 2 == 1;
                                let term = e[j] * alpha.pow((kk + j) as u64 % d as u64);
                                if wrap {
                                    -term
                                } else {
                                    term
                                }
                            })
                            .fold(F17::ZERO, |x, y| x + y)
                    })
                    .collect();
                assert_eq!(kt, direct);
            }
        }
    }

    #[test]
    fn quotient_lift_is_exact_for_a_true_row_and_refuses_a_false_one() {
        // Lemma 3.8 both ways.
        let mut seed = 3u64;
        let d = 8usize;
        for _ in 0..20 {
            let a: Vec<Q32> = rand_coeffs(d, &mut seed);
            let w: Vec<Q32> = rand_coeffs(d, &mut seed);
            let y = nega_mul(&a, &w, d);
            let q = row_quotient(&a, &w, &y, d).expect("a true row always lifts");
            assert_eq!(q.len(), quotient_len(d), "deg r <= d - 2");
            // A~W~ = Y~ + (X^d + 1) r
            let mut lhs = unreduced_mul(&a, &w);
            for i in 0..d {
                lhs[i] -= y[i];
            }
            for i in 0..q.len() {
                lhs[i + d] -= q[i];
                lhs[i] -= q[i];
            }
            assert!(
                lhs.iter().all(|v| *v == Q32::ZERO),
                "the lift is an identity"
            );
            // every alpha satisfies the evaluated identity (Eq. 51)
            for t in 0..6u64 {
                let alpha = Q32::from(t + 2);
                let k = alpha.pow(d as u64) + Q32::ONE;
                let eval = eval_poly(&a, alpha) * eval_poly(&w, alpha)
                    - eval_poly(&y, alpha)
                    - k * eval_poly(&q, alpha);
                assert_eq!(eval, Q32::ZERO, "Eq. (51) at alpha = {t} + 2");
            }
            // one coefficient off: no quotient exists at all
            let mut bad = y.clone();
            bad[3] += Q32::ONE;
            assert_eq!(
                row_quotient(&a, &w, &bad, d),
                Err(ReduceError::RowDoesNotHold { coefficient: 3 })
            );
        }
    }

    #[test]
    fn a_false_row_can_be_hidden_by_at_most_the_stated_number_of_points() {
        // The empirical content of Theorem 7.2's `d_max - 1` and Lemma 3.9's
        // `2 d_max - 1`: enumerate the small field and count.
        let d = 4usize;
        let mut seed = 17u64;
        let all: Vec<F17> = (0..17).map(F17::from).collect();
        for _ in 0..40 {
            let a: Vec<F17> = rand_coeffs(d, &mut seed);
            let w: Vec<F17> = rand_coeffs(d, &mut seed);
            let mut y = nega_mul(&a, &w, d);
            y[0] += F17::ONE; // false row
            let qf_roots = all
                .iter()
                .filter(|&&alpha| {
                    let k = residue_kernel(&a, alpha, d);
                    let lhs: F17 = (0..d).map(|j| w[j] * k[j]).fold(F17::ZERO, |x, z| x + z);
                    lhs == eval_poly(&y, alpha)
                })
                .count();
            assert!(
                qf_roots <= root_bound(RingCheck::QuotientFree, d),
                "quotient-free hid a false row at {qf_roots} > {} points",
                root_bound(RingCheck::QuotientFree, d)
            );
            // quotient-lift: the prover supplies its best quotient, then the
            // evaluated identity can still hold at up to 2d-1 points
            let bad_residual = {
                let mut full = unreduced_mul(&a, &w);
                for i in 0..d {
                    full[i] -= y[i];
                }
                full
            };
            let forced = quotient(&bad_residual, d)
                .err()
                .map(|e| match e {
                    ReduceError::RowDoesNotHold { .. } => true,
                    ReduceError::WrongLength { .. } => false,
                })
                .unwrap_or(false);
            assert!(forced, "a false row must admit no quotient");
            // with the quotient a *true* row would have, the polynomial residual
            // has degree <= 2d-2, so at most 2d-1 roots
            let q = {
                let mut full = unreduced_mul(&a, &w);
                let true_y = nega_mul(&a, &w, d);
                for i in 0..d {
                    full[i] -= true_y[i];
                }
                quotient(&full, d).expect("true row")
            };
            let ql_roots = all
                .iter()
                .filter(|&&alpha| {
                    eval_poly(&a, alpha) * eval_poly(&w, alpha)
                        - eval_poly(&y, alpha)
                        - (alpha.pow(d as u64) + F17::ONE) * eval_poly(&q, alpha)
                        == F17::ZERO
                })
                .count();
            assert!(
                ql_roots <= root_bound(RingCheck::QuotientLift, d),
                "quotient-lift hid a false row at {ql_roots} > {} points",
                root_bound(RingCheck::QuotientLift, d)
            );
        }
    }

    #[test]
    fn quotient_free_never_divides_by_the_modulus_factor() {
        // Theorem 7.2: "Points that are roots of one of the cyclotomic moduli
        // therefore require no rejection". alpha with alpha^d = -1 must still
        // give a correct check.
        let d = 2usize;
        let alpha = F17::from(4u64); // 4^2 = 16 = -1 mod 17
        assert_eq!(alpha.pow(2) + F17::ONE, F17::ZERO, "fixture: alpha^d = -1");
        let a = [F17::from(3u64), F17::from(5u64)];
        let w = [F17::from(7u64), F17::from(11u64)];
        let y = nega_mul(&a, &w, d);
        let k = residue_kernel(&a, alpha, d);
        let lhs: F17 = (0..d).map(|j| w[j] * k[j]).fold(F17::ZERO, |x, z| x + z);
        assert_eq!(lhs, eval_poly(&y, alpha), "check survives alpha^d + 1 = 0");
        // the quotient-lift route degenerates here: its modulus factor vanishes
        let q = row_quotient(&a, &w, &y, d).expect("true row");
        assert_eq!(
            eval_poly(&a, alpha) * eval_poly(&w, alpha) - eval_poly(&y, alpha),
            F17::ZERO,
            "the alpha^d+1 term drops out at such a point"
        );
        assert_eq!(
            eval_poly(&q, alpha) * (alpha.pow(d as u64) + F17::ONE),
            F17::ZERO
        );
    }

    #[test]
    fn the_alpha_tensor_is_the_partial_evaluation_of_eq_52() {
        // Eq. (53): "evaluate at X = alpha" is the partial evaluation of the
        // witness against the rank-one weight e_alpha(y) = prod_j (1 +
        // y_j (alpha^{2^j} - 1)), leaving the coordinate variables free.
        let alpha = Q32::from(7u64);
        let d = 4usize; // log2 d = 2 coefficient variables
        let ladder = power_ladder(alpha, 2);
        let mut seed = 21u64;
        let w: Vec<Q32> = rand_coeffs(d, &mut seed);
        let mut acc = Q32::ZERO;
        for y in 0..d {
            let mut weight = Q32::ONE;
            for j in 0..2 {
                let bit = (y >> j) & 1;
                weight *= Q32::ONE + Q32::from(bit as u64) * (ladder[j] - Q32::ONE);
            }
            assert_eq!(weight, alpha.pow(y as u64), "tensor entry {y}");
            acc += w[y] * weight;
        }
        assert_eq!(acc, eval_poly(&w, alpha));
        // and the ladder really is the shared prefix (Lemma 3.9 part 3)
        assert_eq!(ladder[0], alpha);
        assert_eq!(ladder[1], alpha.square());
    }

    #[test]
    fn shape_errors_name_the_offending_length() {
        let d = 4usize;
        let a = vec![Q32::ONE; d];
        let w = vec![Q32::ONE; d - 1];
        assert_eq!(
            row_quotient(&a, &w, &a, d),
            Err(ReduceError::WrongLength {
                got: 3,
                expected: 4
            })
        );
        assert_eq!(quotient_len(4), 3);
        assert_eq!(root_bound(RingCheck::QuotientFree, 8), 7);
        assert_eq!(root_bound(RingCheck::QuotientLift, 8), 15);
    }
}
