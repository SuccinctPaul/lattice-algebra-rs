//! NTT Parameters and Helper Functions
//!
//! This module provides utilities for NTT parameter validation and computation,
//! including primitive root finding and NTT-friendly prime checking.

use crate::ring::Ring;

/// NTT Parameters for a specific ring and dimension
#[derive(Debug, Clone)]
pub struct NttParams<R: Ring, const N: usize> {
    /// Primitive 2N-th root of unity (for negacyclic NTT)
    pub psi: R,
    /// Inverse of psi
    pub psi_inv: R,
    /// N-th root of unity (ω = ψ²)
    pub omega: R,
    /// Inverse of omega
    pub omega_inv: R,
    /// Inverse of N in the ring
    pub n_inv: R,
}

impl<R: Ring, const N: usize> NttParams<R, N> {
    /// Creates NTT parameters for the given ring
    ///
    /// # Panics
    /// - If N is not a power of 2
    /// - If the modulus is not NTT-friendly for dimension N
    pub fn new() -> Self {
        assert!(N.is_power_of_two(), "N must be a power of 2");
        assert!(
            is_ntt_friendly::<R>(N),
            "Modulus {} is not NTT-friendly for N={}. Required: q ≡ 1 (mod 2N)",
            R::MODULUS,
            N
        );

        // Find primitive 2N-th root of unity (ψ)
        let psi = find_primitive_root::<R>(2 * N);
        let psi_inv = psi.pow(R::MODULUS - 2); // Fermat's little theorem

        // ω = ψ² is the N-th root of unity
        let omega = psi.square();
        let omega_inv = omega.pow(R::MODULUS - 2);

        // Compute N^(-1) mod q
        let n_inv = R::from(N as u64).pow(R::MODULUS - 2);

        Self {
            psi,
            psi_inv,
            omega,
            omega_inv,
            n_inv,
        }
    }
}

impl<R: Ring, const N: usize> Default for NttParams<R, N> {
    fn default() -> Self {
        Self::new()
    }
}

/// Checks if the modulus q is NTT-friendly for the given dimension N.
///
/// A prime q is NTT-friendly for dimension N if:
/// - q ≡ 1 (mod 2N) for negacyclic NTT (x^N + 1)
/// - This ensures the existence of a primitive 2N-th root of unity
///
/// # Arguments
/// * `n` - The NTT dimension (must be a power of 2)
///
/// # Returns
/// `true` if the modulus supports NTT of dimension N
pub fn is_ntt_friendly<R: Ring>(n: usize) -> bool {
    let q = R::MODULUS;
    let two_n = 2 * n as u64;

    // Check q ≡ 1 (mod 2N)
    q % two_n == 1
}

/// Finds a primitive n-th root of unity in the ring R.
///
/// A primitive n-th root of unity ω satisfies:
/// - ω^n ≡ 1 (mod q)
/// - ω^k ≢ 1 (mod q) for all 0 < k < n
///
/// # Algorithm
/// 1. Find a generator g of Z_q* (primitive root modulo q)
/// 2. Compute ω = g^((q-1)/n)
///
/// # Panics
/// - If n does not divide (q-1)
/// - If no primitive root is found
pub fn find_primitive_root<R: Ring>(n: usize) -> R {
    let q = R::MODULUS;
    let n = n as u64;

    assert!(
        (q - 1) % n == 0,
        "n={} must divide q-1={} for primitive root to exist",
        n,
        q - 1
    );

    // Find a generator of Z_q* (primitive root modulo q)
    let g = primitive_root::<R>();

    // ω = g^((q-1)/n) is a primitive n-th root of unity
    let exponent = (q - 1) / n;
    g.pow(exponent)
}

/// Finds a primitive root (generator) of the multiplicative group Z_q*.
///
/// A primitive root g modulo q is an integer such that its powers generate
/// all non-zero elements of Z_q.
///
/// # Algorithm
/// For each candidate g from 2 to q-1:
/// 1. Compute g^((q-1)/p) for each prime factor p of q-1
/// 2. If all results are ≠ 1, then g is a primitive root
///
/// # Panics
/// If no primitive root is found (should not happen for prime q)
pub fn primitive_root<R: Ring>() -> R {
    let q = R::MODULUS;
    let phi = q - 1; // φ(q) = q - 1 for prime q

    // Get prime factors of q-1
    let factors = prime_factors(phi);

    // Try candidates starting from 2
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

    panic!("No primitive root found for modulus {}", q);
}

/// Computes the prime factorization of n.
///
/// Returns a vector of distinct prime factors (not multiplicities).
fn prime_factors(mut n: u64) -> Vec<u64> {
    let mut factors = Vec::new();

    // Check for factor 2
    if n % 2 == 0 {
        factors.push(2);
        while n % 2 == 0 {
            n /= 2;
        }
    }

    // Check for odd factors
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

    // If n is still > 1, it's a prime factor
    if n > 1 {
        factors.push(n);
    }

    factors
}

/// Computes the bit-reversal of an index for in-place NTT.
///
/// # Arguments
/// * `i` - The index to reverse
/// * `log_n` - log2(N), the number of bits
///
/// # Returns
/// The bit-reversed index
#[inline]
pub fn bit_reverse(i: usize, log_n: u32) -> usize {
    i.reverse_bits() >> (usize::BITS - log_n)
}

/// Performs in-place bit-reversal permutation on a slice.
///
/// This is required for the Cooley-Tukey DIT algorithm.
pub fn bit_reverse_permutation<T: Clone>(data: &mut [T]) {
    let n = data.len();
    assert!(n.is_power_of_two(), "Length must be a power of 2");

    let log_n = n.trailing_zeros();

    for i in 0..n {
        let j = bit_reverse(i, log_n);
        if i < j {
            data.swap(i, j);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::zq::Zq;

    // Test with Kyber's modulus: q = 3329
    type Zq3329 = Zq<3329>;

    // Test with a small prime: q = 17
    type Zq17 = Zq<17>;

    // Test with q = 97 (97 = 1 + 96 = 1 + 32*3, supports N=32)
    type Zq97 = Zq<97>;

    #[test]
    fn test_is_ntt_friendly() {
        // q = 3329 = 1 + 3328 = 1 + 13 * 256 = 1 + 13 * 2^8
        // For negacyclic NTT of dimension N, we need q ≡ 1 (mod 2N)
        // 3329 % 512 = 257 ≠ 1, so 3329 does NOT support N=256 directly
        // (Kyber uses incomplete NTT / special technique)
        assert!(!is_ntt_friendly::<Zq3329>(256)); // 2*256 = 512, 3329 % 512 = 257 ≠ 1
        assert!(is_ntt_friendly::<Zq3329>(128)); // 2*128 = 256, 3329 % 256 = 1 ✓

        // q = 17 = 1 + 16 = 1 + 2^4
        // Supports N = 8 (since 17 ≡ 1 (mod 16))
        assert!(is_ntt_friendly::<Zq17>(8));
        assert!(is_ntt_friendly::<Zq17>(4));
        assert!(is_ntt_friendly::<Zq17>(2));
        assert!(!is_ntt_friendly::<Zq17>(16)); // 2*16 = 32, 17 % 32 != 1
    }

    #[test]
    fn test_primitive_root() {
        // For q = 17, primitive root should satisfy:
        // g^1 ≠ 1, g^2 ≠ 1, ..., g^15 ≠ 1, g^16 = 1
        let g = primitive_root::<Zq17>();

        // Verify g^16 = 1
        assert_eq!(g.pow(16), Zq17::ONE);

        // Verify g^k ≠ 1 for k < 16
        for k in 1..16u64 {
            assert_ne!(g.pow(k), Zq17::ONE, "g^{} should not be 1", k);
        }
    }

    #[test]
    fn test_find_primitive_root() {
        // Find 8-th root of unity for q = 17
        // ω^8 = 1 and ω^4 ≠ 1
        let omega = find_primitive_root::<Zq17>(8);

        assert_eq!(omega.pow(8), Zq17::ONE, "ω^8 should be 1");
        assert_ne!(omega.pow(4), Zq17::ONE, "ω^4 should not be 1");
        assert_ne!(omega.pow(2), Zq17::ONE, "ω^2 should not be 1");
    }

    #[test]
    fn test_bit_reverse() {
        // For N = 8 (log_n = 3):
        // 0 (000) -> 0 (000)
        // 1 (001) -> 4 (100)
        // 2 (010) -> 2 (010)
        // 3 (011) -> 6 (110)
        // 4 (100) -> 1 (001)
        // 5 (101) -> 5 (101)
        // 6 (110) -> 3 (011)
        // 7 (111) -> 7 (111)
        assert_eq!(bit_reverse(0, 3), 0);
        assert_eq!(bit_reverse(1, 3), 4);
        assert_eq!(bit_reverse(2, 3), 2);
        assert_eq!(bit_reverse(3, 3), 6);
        assert_eq!(bit_reverse(4, 3), 1);
        assert_eq!(bit_reverse(5, 3), 5);
        assert_eq!(bit_reverse(6, 3), 3);
        assert_eq!(bit_reverse(7, 3), 7);
    }

    #[test]
    fn test_bit_reverse_permutation() {
        let mut data = vec![0, 1, 2, 3, 4, 5, 6, 7];
        bit_reverse_permutation(&mut data);
        assert_eq!(data, vec![0, 4, 2, 6, 1, 5, 3, 7]);
    }

    #[test]
    fn test_prime_factors() {
        assert_eq!(prime_factors(16), vec![2]); // 2^4
        assert_eq!(prime_factors(15), vec![3, 5]); // 3 * 5
        assert_eq!(prime_factors(96), vec![2, 3]); // 2^5 * 3
        assert_eq!(prime_factors(3328), vec![2, 13]); // 3329 - 1 = 2^8 * 13
    }

    #[test]
    fn test_ntt_params() {
        // Test with q = 17, N = 8
        let params = NttParams::<Zq17, 8>::new();

        // ψ is primitive 16-th root of unity
        assert_eq!(params.psi.pow(16), Zq17::ONE);
        assert_ne!(params.psi.pow(8), Zq17::ONE);

        // ω = ψ² is primitive 8-th root of unity
        assert_eq!(params.omega.pow(8), Zq17::ONE);
        assert_ne!(params.omega.pow(4), Zq17::ONE);

        // Verify inverses
        assert_eq!(params.psi * params.psi_inv, Zq17::ONE);
        assert_eq!(params.omega * params.omega_inv, Zq17::ONE);
        assert_eq!(params.n_inv * Zq17::from(8), Zq17::ONE);
    }
}
