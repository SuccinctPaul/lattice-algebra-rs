//! Per-coefficient rounding semantics shared by ML-DSA and lattice ZK
//! shortness proofs (L3), defined exactly per FIPS 204 Algorithms 35–38.
//!
//! All inputs/outputs use centered representatives in `(−q/2, q/2]`, and all
//! functions are branch-free (mask/select idioms from [`crate::crypto::ct`])
//! so they are safe on secret-dependent data.

use crate::crypto::ct;

/// `mod± alpha`: the unique `r` with `r ≡ v (mod alpha)` and
/// `r ∈ (−⌈alpha/2⌉, ⌊alpha/2⌋]`. Branch-free.
#[must_use]
pub fn mod_pm(v: i64, alpha: i64) -> i64 {
    let r = v.rem_euclid(alpha);
    r - (ct::maski64(r > alpha / 2) & alpha)
}

/// Splits `a ∈ [0, q)` into `(a1, a0)` with `a = a1·2^d + a0 (mod q)` and
/// `a0 ∈ (−2^{d−1}, 2^{d−1}]` (FIPS 204 `Power2Round`). Branch-free.
///
/// Used to split the commitment `t` into `t1` (high, packed at
/// `bitlen(q−1) − d` bits) and `t0` (low).
#[must_use]
pub fn power2round(a: i64, d: u32) -> (i64, i64) {
    let r0 = mod_pm(a, 1i64 << d);
    let a1 = (a - r0) >> d;
    (a1, r0)
}

/// Splits `a ∈ [0, q)` into `(a1, a0)` where `a0 = a mod± 2γ2` and
/// `a1 = (a − a0) / (2γ2)`, with the `q−1` boundary special case
/// (FIPS 204 `Decompose`). Branch-free.
///
/// `HighBits(a)` is `a1`; `LowBits(a)` is `a0`.
#[must_use]
pub fn decompose(a: i64, gamma2: i64, q: i64) -> (i64, i64) {
    let a = a.rem_euclid(q);
    let a0 = mod_pm(a, 2 * gamma2);
    let mut a1 = (a - a0) / (2 * gamma2);
    // Boundary case a − a0 == q−1: a1 ← 0, a0 ← a0 − 1, selected by mask.
    let edge = ct::maski64(a - a0 == q - 1);
    a1 = ct::select(a - a0 == q - 1, 0, a1);
    let a0 = a0 - (edge & 1);
    (a1, a0)
}

/// `HighBits_γ2(a)` (FIPS 204): the first component of [`decompose`].
#[must_use]
pub fn high_bits(a: i64, gamma2: i64, q: i64) -> i64 {
    decompose(a, gamma2, q).0
}

/// `LowBits_γ2(a)` (FIPS 204): the second component of [`decompose`].
#[must_use]
pub fn low_bits(a: i64, gamma2: i64, q: i64) -> i64 {
    decompose(a, gamma2, q).1
}

/// FIPS 204 `MakeHint(z, r)`: whether adding `z` to `r` changes the coarse
/// part, i.e. `HighBits(r) ≠ HighBits(r + z)`.
#[must_use]
pub fn make_hint(z: i64, r: i64, gamma2: i64, q: i64) -> bool {
    let r1 = high_bits(r, gamma2, q);
    let v1 = high_bits(r + z, gamma2, q);
    r1 != v1
}

/// FIPS 204 `UseHint(h, a)`: reconstruct the coarse part of `r + z` given
/// only `a = r + z` and the hint bit. Branch-free.
#[must_use]
pub fn use_hint(a: i64, hint: bool, gamma2: i64, q: i64) -> i64 {
    let m = (q - 1) / (2 * gamma2);
    let (r1, r0) = decompose(a, gamma2, q);
    let delta = ct::select(r0 > 0, 1, m - 1);
    ct::select(hint, (r1 + delta) % m, r1)
}

#[cfg(test)]
mod tests {
    use super::*;

    const Q: i64 = 8_380_417;
    const GAMMA2_44: i64 = 95_232; // (q−1)/88
    const GAMMA2_65: i64 = 261_888; // (q−1)/32

    #[test]
    fn power2round_recombines() {
        for a in [0i64, 1, Q - 1, Q / 2, 123_456, 8_000_000] {
            let (r1, r0) = power2round(a, 13);
            assert_eq!((r1 << 13) + r0, a);
            assert!((-4096..=4096).contains(&r0), "r0={r0} not centered");
        }
    }

    #[test]
    fn decompose_recombines_mod_q() {
        for gamma2 in [GAMMA2_44, GAMMA2_65] {
            let max1 = (Q - 1) / (2 * gamma2);
            for a in [
                0i64,
                1,
                Q - 1,
                Q / 2,
                123_456,
                8_000_000,
                300_000,
                q_minus(1),
            ] {
                let (r1, r0) = decompose(a, gamma2, Q);
                assert_eq!((r1 * 2 * gamma2 + r0).rem_euclid(Q), a);
                assert!(r0 > -gamma2 && r0 <= gamma2, "r0={r0} out of (−γ2, γ2]");
                assert!((0..max1).contains(&r1), "r1={r1} out of [0, m)");
            }
        }
    }

    fn q_minus(x: i64) -> i64 {
        Q - x
    }

    #[test]
    fn use_hint_recovers_high_bits_of_r_from_r_plus_z() {
        // The FIPS property: with h = MakeHint(z, r), UseHint(h, r + z)
        // equals HighBits(r), for any r and any z that is "small enough"
        // (‖z‖∞ ≤ γ2, which holds for the signing-time ‖c·s2‖∞ check).
        for gamma2 in [GAMMA2_44, GAMMA2_65] {
            for r in [0i64, 1, Q - 1, 123_456, 4190208, 8_000_000] {
                for z in [-gamma2, -100, -1, 0, 1, 100, gamma2 - 1, gamma2] {
                    let h = make_hint(z, r, gamma2, Q);
                    let recovered = use_hint(r + z, h, gamma2, Q);
                    assert_eq!(
                        recovered,
                        high_bits(r, gamma2, Q),
                        "hint roundtrip failed: γ2={gamma2} r={r} z={z}"
                    );
                }
            }
        }
    }

    #[test]
    fn use_hint_matches_c_reference_on_sweep() {
        // Differential check against the CRYSTALS-Dilithium reference
        // rounding.c formulas (transcribed to i64 arithmetic).
        let c_decompose = |a: i64, gamma2: i64| -> (i64, i64) {
            let mut a1 = (a + 127) >> 7;
            if gamma2 * 32 == Q - 1 {
                a1 = (a1 * 1025 + (1 << 21)) >> 22;
                a1 &= 15;
            } else {
                a1 = (a1 * 11275 + (1 << 23)) >> 24;
                a1 ^= ((43 - a1) >> 31) & a1;
            }
            let mut a0 = a - a1 * 2 * gamma2;
            a0 -= (((Q - 1) / 2 - a0) >> 31) & Q;
            (a1, a0)
        };
        for gamma2 in [GAMMA2_44, GAMMA2_65] {
            for a in 0..2_000_000i64 {
                let (r1, r0) = decompose(a, gamma2, Q);
                let (c1, c0) = c_decompose(a, gamma2);
                assert_eq!((r1, r0), (c1, c0), "decompose diverges at a={a}");
            }
        }
    }

    #[test]
    fn make_hint_boundaries() {
        let g = GAMMA2_65;
        // z = 0 never changes the coarse part.
        assert!(!make_hint(0, 123_456, g, Q));
        // Cells are centered: cell i spans (2i·γ2 − γ2, 2i·γ2 + γ2], so the
        // boundary sits at odd multiples of γ2.
        assert!(make_hint(2, g - 1, g, Q));
        assert!(!make_hint(1, g - 1, g, Q));
    }
}

#[cfg(test)]
mod probe {
    use super::*;
    const Q: i64 = 8_380_417;
    const G: i64 = 261_888;

    #[test]
    fn probe_hint_direction() {
        // property A: UseHint(MakeHint(z, r), r) == HighBits(r + z)
        // property B: UseHint(MakeHint(z, r), r + z) == HighBits(r)
        let mut a_ok = 0;
        let mut b_ok = 0;
        let mut total = 0;
        for r in [
            0i64,
            100_000,
            523_776,
            1_000_000,
            4_190_208,
            8_000_000,
            Q - 1,
        ] {
            for z in [-261_888i64, -100_000, -1, 1, 100_000, 261_887] {
                let h = make_hint(z, r, G, Q);
                let a = use_hint(r, h, G, Q) == high_bits(r + z, G, Q);
                let b = use_hint(r + z, h, G, Q) == high_bits(r, G, Q);
                a_ok += a as usize;
                b_ok += b as usize;
                total += 1;
            }
        }
        println!("property A (UseHint(h,r)==HighBits(r+z)): {a_ok}/{total}");
        println!("property B (UseHint(h,r+z)==HighBits(r)): {b_ok}/{total}");
    }
}
