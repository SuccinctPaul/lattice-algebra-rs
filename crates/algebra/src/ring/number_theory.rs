//! Number-theoretic helpers on the scalar-ring layer (L0).
//!
//! These are pure utilities with no intra-crate dependencies, so both the NTT
//! engine (L1) and the sampling layer (L4) can build on them without violating
//! the layering rules (see docs: L0 depends on nothing).

use crate::ring::Ring;
// Only the `#[cfg(test)]` children use this, so the plain lib build reports it
// unused; deleting it breaks `cargo test`.
#[allow(unused_imports)]
use alloc::{vec, vec::Vec};

/// Deterministic Miller-Rabin primality test for `u64`.
///
/// Uses the witness set {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}, which is
/// proven to be deterministic for all `n < 2^64`. Written as a `const fn` so
/// moduli can declare `Ring::IS_PRIME` as an associated constant.
pub const fn is_prime_u64(n: u64) -> bool {
    const WITNESSES: [u64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];

    if n < 2 {
        return false;
    }
    // Trial division by the witnesses themselves.
    let mut i = 0;
    while i < WITNESSES.len() {
        if n % WITNESSES[i] == 0 {
            return n == WITNESSES[i];
        }
        i += 1;
    }

    // Write n - 1 = d * 2^s with d odd.
    let mut d = n - 1;
    let mut s = 0u64;
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }

    let mut i = 0;
    while i < WITNESSES.len() {
        let a = WITNESSES[i];
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 {
            i += 1;
            continue;
        }
        let mut composite = true;
        let mut r = 1;
        while r < s {
            x = mulmod(x, x, n);
            if x == n - 1 {
                composite = false;
                break;
            }
            r += 1;
        }
        if composite {
            return false;
        }
        i += 1;
    }
    true
}

/// `a * b mod m` without 64-bit overflow (const-compatible).
#[inline]
pub const fn mulmod(a: u64, b: u64, m: u64) -> u64 {
    (((a as u128) * (b as u128)) % (m as u128)) as u64
}

/// `base^exp mod m` by square-and-multiply (const-compatible).
#[inline]
pub const fn powmod(mut base: u64, mut exp: u64, m: u64) -> u64 {
    let mut result: u64 = 1 % m;
    base %= m;
    while exp > 0 {
        if exp & 1 == 1 {
            result = mulmod(result, base, m);
        }
        base = mulmod(base, base, m);
        exp >>= 1;
    }
    result
}

/// Distinct prime factors of `n`, ascending (multiplicities collapsed).
pub fn prime_factors(mut n: u64) -> Vec<u64> {
    let mut factors = Vec::new();

    if n % 2 == 0 {
        factors.push(2);
        while n % 2 == 0 {
            n /= 2;
        }
    }

    let mut i = 3u64;
    while i * i <= n {
        if n % i == 0 {
            factors.push(i);
            while n % i == 0 {
                n /= i;
            }
        }
        i += 2;
    }

    if n > 1 {
        factors.push(n);
    }

    factors
}

/// Finds a primitive root (generator of the multiplicative group `Z_q*`)
/// for a prime modulus `q = R::MODULUS`.
///
/// # Panics
/// - If `R::MODULUS` is not prime (per `Ring::IS_PRIME`)
/// - If no generator is found (cannot happen for prime `q`)
pub fn primitive_root<R: Ring>() -> R {
    assert!(
        R::IS_PRIME,
        "primitive_root requires a prime modulus, got {}",
        R::MODULUS
    );
    let q = R::MODULUS;
    let phi = q - 1;
    let factors = prime_factors(phi);

    // Try candidates starting from 2. A generator g satisfies
    // g^((q-1)/p) != 1 for every prime factor p of q-1.
    for g in 2..q {
        let candidate = R::from(g);
        let mut is_generator = true;

        for &factor in &factors {
            let exp = phi / factor;
            if candidate.pow(exp) == R::ONE {
                is_generator = false;
                break;
            }
        }

        if is_generator {
            return candidate;
        }
    }

    unreachable!("every prime field has a primitive root");
}

/// Finds a primitive `n`-th root of unity in `R`, i.e. `w` with
/// `w^n == 1` and `w^k != 1` for all `0 < k < n`.
///
/// Requires `n` to divide `q - 1` (guaranteed for NTT-friendly setups).
pub fn find_primitive_root<R: Ring>(n: usize) -> R {
    let q = R::MODULUS;
    let n = n as u64;

    assert!(n > 0, "root order must be positive");
    assert!(
        (q - 1) % n == 0,
        "n={n} must divide q-1={} for a primitive {n}-th root of unity to exist",
        q - 1
    );

    let g = primitive_root::<R>();
    // w = g^((q-1)/n) is a primitive n-th root of unity.
    let exponent = (q - 1) / n;
    g.pow(exponent)
}

/// Greatest common divisor of two `u64`s (Euclid).
pub const fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

/// The multiplicative order of `a` modulo `n`, or `None` when `a` is not
/// invertible mod `n`.
///
/// The loop is capped at `n` steps; every caller here uses `n = 2d` with `d`
/// a power of two, so the order is at most `n` by Lagrange.
pub fn order_mod(a: u64, n: u64) -> Option<u64> {
    if n < 2 {
        return None;
    }
    let a = a % n;
    if gcd_u64(a, n) != 1 {
        return None;
    }
    let mut cur = a;
    let mut k = 1u64;
    while cur != 1 {
        cur = mulmod(cur, a, n);
        k += 1;
        if k > n {
            return None;
        }
    }
    Some(k)
}

/// How `X^d + 1` factors over the prime field `F_q`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Splitting {
    /// Degree of each irreducible factor (all are equal in this family).
    pub factor_degree: u64,
    /// Number of irreducible factors, `d / factor_degree`.
    pub factor_count: u64,
}

impl Splitting {
    /// Whether `X^d + 1` splits into linear factors — the NTT-friendly case,
    /// where `F_q` holds a primitive `2d`-th root of unity.
    pub const fn is_split_completely(&self) -> bool {
        self.factor_degree == 1
    }

    /// Whether `X^d + 1` splits into exactly two factors of degree `d / 2`,
    /// the shape LaBRADOR's Theorem 5.1 states its MSIS reduction over.
    pub const fn is_two_half_degrees(&self, d: u64) -> bool {
        self.factor_count == 2 && self.factor_degree == d / 2
    }
}

/// Factors `X^d + 1` over `F_q` for `d = 2^e` (`e >= 1`) and odd prime `q`.
///
/// For `d` a power of two, `X^d + 1 = Phi_{2d}(X)` is the `2d`-th cyclotomic
/// polynomial, and `Phi_m(X)` over `F_q` (with `q` coprime to `m`) factors
/// into `phi(m) / ord_m(q)` irreducibles each of degree `ord_m(q)`. Here
/// `m = 2d` and `phi(2d) = d`, so the whole picture is set by the
/// multiplicative order of `q` mod `2d`:
///
/// ```text
/// q ==  1 mod 2d    ->  d linear factors        (complete splitting, NTT)
/// q ==  3 or 5 mod 8 ->  2 factors of degree d/2 (LaBRADOR's stated regime)
/// ```
///
/// Returns `None` outside the lemma's hypotheses (`d` not a power of two
/// below `2^63`, or `q` not an odd prime).
pub fn x_pow_d_plus_1_splitting(q: u64, d: u64) -> Option<Splitting> {
    if d < 2 || d & (d - 1) != 0 {
        return None;
    }
    if q <= 2 || !is_prime_u64(q) {
        return None;
    }
    let degree = order_mod(q, 2 * d)?;
    Some(Splitting {
        factor_degree: degree,
        factor_count: d / degree,
    })
}

/// Searches downward from `2^bits` for a prime `q` making `X^d + 1` split
/// into factors of exactly `want_degree`.
///
/// Ring selection is a security-relevant choice, not packaging: the crate's
/// Z1 prime `8380417` is `1 mod 8`, so `X^256 + 1` splits *completely* —
/// which is why the NTT works, and also why schemes stated over the
/// two-factor regime (LaBRADOR) cannot inherit it unchanged. Capped search;
/// returns `None` rather than spinning.
#[must_use]
pub fn find_prime_for_splitting(d: u64, want_degree: u64, bits: u32) -> Option<u64> {
    if bits == 0 || bits > 62 {
        return None;
    }
    let mut q = (1u64 << bits) - 1;
    if q % 2 == 0 {
        q -= 1;
    }
    for _ in 0..200_000 {
        if q < 3 {
            return None;
        }
        if is_prime_u64(q) {
            if let Some(split) = x_pow_d_plus_1_splitting(q, d) {
                if split.factor_degree == want_degree {
                    return Some(q);
                }
            }
        }
        q -= 2;
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::zq::Zq;

    #[test]
    fn test_is_prime_u64() {
        assert!(!is_prime_u64(0));
        assert!(!is_prime_u64(1));
        assert!(is_prime_u64(2));
        assert!(is_prime_u64(3));
        assert!(!is_prime_u64(4));
        assert!(is_prime_u64(17));
        assert!(!is_prime_u64(2u64.pow(32)));
        assert!(is_prime_u64(3329));
        assert!(is_prime_u64(7681));
        assert!(is_prime_u64(12289));
        assert!(is_prime_u64(8380417));
        assert!(is_prime_u64(2147483647)); // 2^31 - 1 (Mersenne)
        assert!(is_prime_u64(u64::MAX - 58)); // largest known-prime 64-bit test value in this repo
        assert!(!is_prime_u64(u64::MAX));
    }

    #[test]
    fn test_prime_factors() {
        let empty: Vec<u64> = Vec::new();
        assert_eq!(prime_factors(1), empty);
        assert_eq!(prime_factors(16), vec![2]);
        assert_eq!(prime_factors(15), vec![3, 5]);
        assert_eq!(prime_factors(96), vec![2, 3]);
        assert_eq!(prime_factors(3328), vec![2, 13]); // 3329 - 1
        assert_eq!(prime_factors(8380416), vec![2, 3, 11, 31]); // 8380417 - 1 = 2^13 * 1023
    }

    #[test]
    fn test_primitive_root() {
        type Zq17 = Zq<17>;
        let g = primitive_root::<Zq17>();
        assert_eq!(g.pow(16), Zq17::ONE);
        for k in 1..16u64 {
            assert_ne!(g.pow(k), Zq17::ONE, "g^{k} should not be 1");
        }
    }

    #[test]
    fn test_find_primitive_root() {
        type Zq17 = Zq<17>;
        let omega = find_primitive_root::<Zq17>(8);
        assert_eq!(omega.pow(8), Zq17::ONE);
        assert_ne!(omega.pow(4), Zq17::ONE);
        assert_ne!(omega.pow(2), Zq17::ONE);
    }

    #[test]
    fn test_order_mod() {
        assert_eq!(order_mod(2, 7), Some(3)); // 2^3 = 8 = 1 mod 7
        assert_eq!(order_mod(3, 7), Some(6));
        assert_eq!(order_mod(3, 8), Some(2)); // 3^2 = 9 = 1 mod 8
        assert_eq!(order_mod(2, 8), None, "2 is not invertible mod 8");
        assert_eq!(order_mod(4, 8), None, "4 is not invertible mod 8");
    }

    #[test]
    fn x_pow_d_plus_1_splits_completely_when_q_is_one_mod_2d() {
        // The crate's Z1 prime: q - 1 = 2^13 * 3 * 11 * 31, so it is 1 mod
        // 512 = 2*256 and X^256 + 1 splits into linear factors. That is what
        // makes our NTT work - and what LaBRADOR's reduction cannot assume.
        const Z1: u64 = 8_380_417;
        let split = x_pow_d_plus_1_splitting(Z1, 256).expect("q prime, d a power of two");
        assert!(split.is_split_completely());
        assert_eq!(split.factor_count, 256);
        assert_eq!(Z1 % 8, 1);
    }

    #[test]
    fn x_pow_d_plus_1_gives_two_half_degree_factors_for_q_three_or_five_mod_eight() {
        for q in [5u64, 13, 29, 37] {
            assert!(is_prime_u64(q));
            for d in [8u64, 64, 256] {
                let split = x_pow_d_plus_1_splitting(q, d).expect("valid inputs");
                assert!(
                    split.is_two_half_degrees(d),
                    "q = {q} (mod 8 = {}) must give 2 factors of degree {}: {split:?}",
                    q % 8,
                    d / 2
                );
            }
        }
    }

    #[test]
    fn splitting_formula_matches_direct_root_counting() {
        // Independent check for the complete-splitting case: degree-1 factors
        // mean X^d + 1 has exactly d roots in F_q.
        for (q, d) in [(17u64, 8usize), (97u64, 8usize), (257u64, 8usize)] {
            let split = x_pow_d_plus_1_splitting(q, d as u64).expect("valid");
            let roots = (0..q as i64)
                .filter(|&a| (powmod(a.unsigned_abs(), d as u64, q) + 1) % q == 0)
                .count();
            if split.is_split_completely() {
                assert_eq!(
                    roots, d,
                    "q = {q}, d = {d}: linear factors must all be roots"
                );
            } else {
                assert_eq!(roots, 0, "q = {q}, d = {d}: no linear factor, so no root");
            }
        }
    }

    #[test]
    fn finds_primes_for_either_splitting_regime() {
        let two_factor = find_prime_for_splitting(64, 32, 16).expect("a 16-bit q with degree 32");
        assert!(is_prime_u64(two_factor));
        assert!(x_pow_d_plus_1_splitting(two_factor, 64)
            .unwrap()
            .is_two_half_degrees(64));

        let complete = find_prime_for_splitting(64, 1, 16);
        // degree 1 needs q == 1 mod 128, which the 16-bit range does contain
        let complete = complete.expect("a 16-bit q splitting X^64 + 1 completely");
        assert!(x_pow_d_plus_1_splitting(complete, 64)
            .unwrap()
            .is_split_completely());
    }

    #[test]
    fn rejects_inputs_outside_the_lemma() {
        assert_eq!(x_pow_d_plus_1_splitting(8_380_417, 63), None, "d not 2^e");
        assert_eq!(x_pow_d_plus_1_splitting(9, 64), None, "q not prime");
        assert_eq!(x_pow_d_plus_1_splitting(2, 64), None, "q must be odd");
    }
}
