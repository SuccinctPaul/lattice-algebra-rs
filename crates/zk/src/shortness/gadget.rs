//! Gadget split + approximate linear check with provable slack (L5).
//!
//! The slack-based flavor of shortness: decompose coefficients into high
//! digits plus a centered low residual (`v = high·2^drop + low`, with `low`
//! re-centered into `(−2^{drop−1}, 2^{drop−1}]` and the remainder tracked as
//! slack), then accept openings that match the committed value only up to
//! the **provable slack** [`slack_bound`]. This is the machinery the full
//! LaBRADOR recursion (Z2/Z3) layers into a complete shortness proof; the
//! exact-balanced flavor used by the projection argument and LatticeFold
//! decomposition lives in [`crate::shortness::balanced`].

use crate::foundation::encoding::ring_to_u32;
use crate::instance::ring::{Z2Ring, D};

/// Gadget split: `v = high·2^drop + low`, with `low` re-centered into
/// `(−2^{drop−1}, 2^{drop−1}]` and the remainder tracked as slack.
/// Returns `(high, low_centered, slack)` with `|slack| ≤ 2^{drop−1}`.
pub fn gadget_split(v: u32, drop: u32) -> (u32, i64, i64) {
    debug_assert!((1..32).contains(&drop));
    let high = v >> drop;
    let low = v & ((1u32 << drop) - 1);
    let low_i = i64::from(low);
    let half = 1i64 << (drop - 1);
    let centered = if low_i > half {
        low_i - (1i64 << drop)
    } else {
        low_i
    };
    let slack = low_i - centered;
    (high, centered, slack)
}

/// Rebuilds a value from its gadget split (exact when slack is included).
pub fn gadget_join(high: u32, drop: u32, low_centered: i64, slack: i64) -> u32 {
    let low = (low_centered + slack).rem_euclid(1i64 << drop) as u32;
    (high << drop) | low
}

/// provable slack of an approximate linear opening: `N·D·2^{drop−1}`
/// (operator-norm bound of `A` acting on a coefficient-bounded residual).
pub fn slack_bound(n_rows: usize, drop: u32) -> i64 {
    i64::from(n_rows as u32 * (1u32 << (drop - 1)))
}

/// Approximate linear check: does `lhs ≈ 2^drop·(A·high) + A·low_centered`
/// hold within the provable slack? `lhs` and `rhs` are `N`-vectors of ring
/// elements (the committed and reconstructed values).
pub fn approx_linear_check(lhs: &[Z2Ring], reconstructed: &[Z2Ring], drop: u32) -> bool {
    let bound = slack_bound(lhs.len() * D, drop) as u64;
    for (l, r) in lhs.iter().zip(reconstructed.iter()) {
        let lc = ring_to_u32(l);
        let rc = ring_to_u32(r);
        for (a, b) in lc.iter().zip(&rc) {
            let diff = i64::from(*a) - i64::from(*b);
            // centered difference on the power-of-two modulus
            let diff = diff.rem_euclid(1i64 << 32);
            let diff = if diff > (1i64 << 31) {
                diff - (1i64 << 32)
            } else {
                diff
            };
            if diff.unsigned_abs() > bound {
                return false;
            }
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::encoding::ring_from_u32;

    fn make_probe(v: u32) -> [u32; D] {
        let mut c = [0u32; D];
        c[0] = v;
        c
    }

    #[test]
    fn gadget_split_is_exact_and_bounded() {
        for drop in [4u32, 12, 16] {
            for v in [0u32, 1, 0x7FFF_FFFF, 0xFFFF_FFFF, 123_456_789] {
                let (hi, lo, slack) = gadget_split(v, drop);
                assert_eq!(gadget_join(hi, drop, lo, slack), v);
                assert!(slack.abs() <= 1i64 << drop, "slack {slack} out of range");
                assert!(lo.abs() <= 1i64 << (drop - 1));
            }
        }
    }

    #[test]
    fn approx_check_accepts_exact_and_bounded_slack() {
        // exact reconstruction accepted
        let v = [0x1234_5678u32, 0xFFFF_FFFF, 42];
        let mut lhs = Vec::new();
        let mut recon = Vec::new();
        for &x in &v {
            let (hi, lo, slack) = gadget_split(x, 12);
            lhs.push(ring_from_u32(&make_probe(x)));
            let rebuilt = gadget_join(hi, 12, lo, slack);
            recon.push(ring_from_u32(&make_probe(rebuilt)));
        }
        assert!(approx_linear_check(&lhs, &recon, 12));
        // a deviation beyond the slack bound must be rejected
        let mut bad = recon.clone();
        bad[2] = ring_from_u32(&make_probe(42 + 1_000_000));
        assert!(!approx_linear_check(&lhs, &bad, 12));
    }
}
