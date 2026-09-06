//! Constant-time primitives (L4).
//!
//! Branch-free building blocks for code that touches secret-dependent
//! data. The constructions are the standard integer-mask idioms
//! (arithmetic right shifts, wrapping arithmetic, multiplicative masks)
//! that compile to branchless instruction sequences; every primitive is
//! exhaustively differential-tested against its scalar `if/else` form.
//!
//! ## Scope of the CT claim
//!
//! These primitives harden the secret-*value* paths of the schemes in this
//! workspace: norm gates, rounding/hint logic, sampler value mappings and
//! wire encodings. Two residual behaviors are *not* eliminated and are
//! documented on the Security Status page rather than hidden:
//!
//! 1. **Rejection-sampling loop counts.** FIPS 204 derives secrets through
//!    XOF rejection streams (`RejBounded`, `RejNTTPoly`, `SampleInBall`);
//!    the number of stream bytes consumed is inherently data-dependent.
//!    It depends only on the XOF output, never on a secret-indexed table
//!    lookup or a secret-valued branch inside the loop body.
//! 2. **Hint compaction.** `HintBitPack` writes hint positions through a
//!    running index that depends on the hint bits; the final hint vector
//!    is public (it is part of the signature), and the reference
//!    implementation has the same shape.

/// Full-width mask for a boolean: `!0u64` when `true`, `0` when `false`.
#[inline]
#[must_use]
pub fn mask64(cond: bool) -> u64 {
    (cond as u64).wrapping_neg()
}

/// Signed mask for a boolean: `-1i64` when `true`, `0` when `false`.
#[inline]
#[must_use]
pub fn maski64(cond: bool) -> i64 {
    (cond as i64).wrapping_neg()
}

/// Branch-free select: `a` when `cond`, else `b`.
#[inline]
#[must_use]
pub fn select(cond: bool, a: i64, b: i64) -> i64 {
    b ^ ((a ^ b) & maski64(cond))
}

/// Branch-free select over `u64`.
#[inline]
#[must_use]
pub fn select_u64(cond: bool, a: u64, b: u64) -> u64 {
    b ^ ((a ^ b) & mask64(cond))
}

/// Branch-free signed comparison `a < b` (`i64` inputs cannot overflow
/// `i128` subtraction).
#[inline]
#[must_use]
pub fn lt(a: i64, b: i64) -> bool {
    ((a as i128 - b as i128) >> 127) & 1 == 1
}

/// Branch-free unsigned comparison `a < b`.
#[inline]
#[must_use]
pub fn lt_u64(a: u64, b: u64) -> bool {
    a < b
}

/// Branch-free equality on `u64`.
#[inline]
#[must_use]
pub fn eq_u64(a: u64, b: u64) -> bool {
    let x = a ^ b;
    // `x | -x` has its sign bit set for every x != 0 and is 0 for x == 0.
    ((x | x.wrapping_neg()) >> 63) & 1 == 0
}

/// Branch-free absolute value.
#[inline]
#[must_use]
pub fn abs(x: i64) -> i64 {
    let sign = x >> 63;
    (x ^ sign).wrapping_sub(sign)
}

/// Branch-free `|x|_∞` over centered representatives, i.e.
/// `max |x_i|` without early exits or data-dependent branches.
#[must_use]
pub fn infinity_norm(coeffs: &[i64]) -> u64 {
    let mut m = 0u64;
    for &c in coeffs {
        let a = abs(c) as u64;
        m = select_u64(a > m, a, m);
    }
    m
}

/// Branch-free conditional accumulate: `acc += x` when `cond`.
///
/// Useful for replacing `if secret_data { count += 1 }` counting loops.
#[inline]
pub fn add_if(acc: &mut usize, cond: bool, x: usize) {
    *acc += (mask64(cond) & x as u64) as usize;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn select_matches_scalar() {
        for x in [-8i64, -1, 0, 1, 7, i64::MIN, i64::MAX] {
            for y in [-9i64, -2, 0, 3, 42, i64::MIN, i64::MAX] {
                for cond in [true, false] {
                    assert_eq!(select(cond, x, y), if cond { x } else { y });
                }
            }
        }
        for x in [0u64, 1, u64::MAX] {
            for y in [0u64, 5, u64::MAX] {
                for cond in [true, false] {
                    assert_eq!(select_u64(cond, x, y), if cond { x } else { y });
                }
            }
        }
    }

    #[test]
    fn comparisons_and_masks_match_scalar() {
        for a in [0i64, 1, -1, i64::MIN, i64::MAX, 123_456] {
            for b in [0i64, 1, -1, i64::MIN, i64::MAX, -123_456] {
                assert_eq!(lt(a, b), a < b, "lt({a}, {b})");
            }
        }
        for a in [0u64, 1, u64::MAX, 7] {
            for b in [0u64, 2, u64::MAX, 7] {
                assert_eq!(lt_u64(a, b), a < b);
                assert_eq!(eq_u64(a, b), a == b);
            }
        }
        for cond in [true, false] {
            assert_eq!(mask64(cond), if cond { u64::MAX } else { 0 });
            assert_eq!(maski64(cond), if cond { -1 } else { 0 });
        }
    }

    #[test]
    fn abs_matches_scalar() {
        for x in [0i64, 1, -1, 42, -42, i64::MAX, i64::MIN] {
            let want = if x == i64::MIN {
                i64::MIN.unsigned_abs() as i64
            } else {
                x.abs()
            };
            assert_eq!(abs(x), want, "abs({x})");
        }
    }

    #[test]
    fn infinity_norm_matches_scalar() {
        let cases: Vec<Vec<i64>> = vec![
            vec![],
            vec![0],
            vec![-5, 3, 2],
            vec![i64::MIN, 7],
            vec![1, i64::MAX],
            (0..64).map(|i| (i * 37 % 13) as i64 - 6).collect(),
        ];
        for coeffs in cases {
            let want = coeffs.iter().map(|&c| c.unsigned_abs()).max().unwrap_or(0);
            assert_eq!(infinity_norm(&coeffs), want);
        }
    }

    #[test]
    fn add_if_matches_branch() {
        let mut a = 5usize;
        add_if(&mut a, true, 3);
        assert_eq!(a, 8);
        add_if(&mut a, false, 3);
        assert_eq!(a, 8);
    }
}
