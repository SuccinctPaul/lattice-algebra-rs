//! Number-theoretic helpers on the scalar-ring layer (L0).
//!
//! These are pure utilities with no intra-crate dependencies, so both the NTT
//! engine (L1) and the sampling layer (L4) can build on them without violating
//! the layering rules (see docs: L0 depends on nothing).

use crate::ring::Ring;

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
        assert_eq!(prime_factors(8380416), vec![2, 997]); // 8380417 - 1
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
}
