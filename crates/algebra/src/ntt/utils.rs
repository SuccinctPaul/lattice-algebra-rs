//! Utility functions for NTT operations.

/// Computes a^exp mod m using binary exponentiation.
///
/// Time complexity: O(log exp)
///
/// # Arguments
/// * `base` - The base
/// * `exp` - The exponent
/// * `modulus` - The modulus
///
/// # Returns
/// base^exp mod modulus
#[inline]
pub fn mod_exp(base: u64, mut exp: u64, modulus: u64) -> u64 {
    if modulus == 1 {
        return 0;
    }
    let mut result: u128 = 1;
    let mut base = (base % modulus) as u128;
    let modulus = modulus as u128;

    while exp > 0 {
        if exp & 1 == 1 {
            result = (result * base) % modulus;
        }
        exp >>= 1;
        base = (base * base) % modulus;
    }
    result as u64
}

/// Computes the modular multiplicative inverse using extended Euclidean algorithm.
///
/// # Arguments
/// * `a` - The value to invert
/// * `modulus` - The modulus
///
/// # Returns
/// Some(a^(-1) mod modulus) if gcd(a, modulus) = 1, None otherwise
pub fn mod_inverse(a: u64, modulus: u64) -> Option<u64> {
    let (mut old_r, mut r) = (modulus as i128, a as i128);
    let (mut old_t, mut t) = (0i128, 1i128);

    while r != 0 {
        let quotient = old_r / r;
        (old_r, r) = (r, old_r - quotient * r);
        (old_t, t) = (t, old_t - quotient * t);
    }

    if old_r > 1 {
        return None; // a and modulus are not coprime
    }

    if old_t < 0 {
        old_t += modulus as i128;
    }

    Some(old_t as u64)
}

/// Checks if q is an NTT-friendly prime for degree n (cyclic NTT).
///
/// For cyclic NTT, we need q ≡ 1 (mod n), meaning n-th roots of unity exist.
///
/// # Arguments
/// * `q` - The modulus
/// * `n` - The polynomial degree (must be power of 2)
///
/// # Returns
/// true if q is NTT-friendly for cyclic convolution of degree n
pub fn is_ntt_friendly_prime(q: u64, n: usize) -> bool {
    // Check n is power of 2
    if n == 0 || (n & (n - 1)) != 0 {
        return false;
    }

    // Check q ≡ 1 (mod n) for cyclic NTT
    (q - 1) % (n as u64) == 0
}

/// Checks if q supports negacyclic NTT for degree n (for x^n + 1).
///
/// For negacyclic NTT, we need q ≡ 1 (mod 2n), meaning 2n-th roots of unity exist.
///
/// # Arguments
/// * `q` - The modulus
/// * `n` - The polynomial degree (must be power of 2)
///
/// # Returns
/// true if q supports negacyclic NTT for degree n
pub fn is_negacyclic_ntt_friendly(q: u64, n: usize) -> bool {
    // Check n is power of 2
    if n == 0 || (n & (n - 1)) != 0 {
        return false;
    }

    // Check q ≡ 1 (mod 2n) for negacyclic NTT
    let two_n = 2 * n as u64;
    (q - 1) % two_n == 0
}

/// Finds a primitive n-th root of unity modulo q for cyclic NTT.
///
/// A primitive n-th root of unity ω satisfies:
/// - ω^n ≡ 1 (mod q)
/// - ω^k ≢ 1 (mod q) for 0 < k < n
///
/// # Arguments
/// * `q` - The modulus (must be prime with q ≡ 1 (mod n))
/// * `n` - The order of the root
///
/// # Returns
/// Some(ω) if found, None otherwise
pub fn find_primitive_root(q: u64, n: usize) -> Option<u64> {
    if !is_ntt_friendly_prime(q, n) {
        return None;
    }

    // First find a generator of Z_q^*
    // Then compute g^((q-1)/n) to get an n-th root of unity
    for g in 2..q {
        if is_primitive_root(g, q) {
            let exp = (q - 1) / (n as u64);
            let omega = mod_exp(g, exp, q);

            // Verify: omega^n = 1 and omega^(n/2) != 1 (if n is even)
            if mod_exp(omega, n as u64, q) == 1 {
                if n > 1 {
                    // Check it's primitive (omega^(n/2) != 1 for even n)
                    if n % 2 == 0 && mod_exp(omega, (n / 2) as u64, q) == 1 {
                        continue;
                    }
                }
                return Some(omega);
            }
        }
    }

    None
}

/// Finds a primitive 2n-th root of unity for negacyclic NTT.
///
/// A primitive 2n-th root of unity ψ satisfies:
/// - ψ^(2n) ≡ 1 (mod q)
/// - ψ^n ≡ -1 (mod q)
///
/// # Arguments
/// * `q` - The modulus (must be prime with q ≡ 1 (mod 2n))
/// * `n` - The polynomial degree
///
/// # Returns
/// Some(ψ) if found, None otherwise
pub fn find_primitive_2n_root(q: u64, n: usize) -> Option<u64> {
    if !is_negacyclic_ntt_friendly(q, n) {
        return None;
    }

    let two_n = 2 * n as u64;

    // Find a generator of Z_q^*
    for g in 2..q {
        if is_primitive_root(g, q) {
            let exp = (q - 1) / two_n;
            let psi = mod_exp(g, exp, q);

            // Verify: psi^n = -1 (mod q)
            if mod_exp(psi, n as u64, q) == q - 1 {
                return Some(psi);
            }
        }
    }

    None
}

/// Checks if g is a primitive root (generator) modulo q.
///
/// g is a primitive root if ord(g) = q-1 (for prime q).
fn is_primitive_root(g: u64, q: u64) -> bool {
    if g == 0 || g >= q {
        return false;
    }

    let phi = q - 1; // Euler's totient for prime q

    // Check g^(phi/p) ≠ 1 for all prime factors p of phi
    let factors = prime_factors(phi);

    for &p in &factors {
        let exp = phi / p;
        if mod_exp(g, exp, q) == 1 {
            return false;
        }
    }

    true
}

/// Returns the prime factors of n.
fn prime_factors(mut n: u64) -> Vec<u64> {
    let mut factors = Vec::new();

    // Check for 2
    if n % 2 == 0 {
        factors.push(2);
        while n % 2 == 0 {
            n /= 2;
        }
    }

    // Check odd numbers
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

/// Computes the bit-reversal permutation of index i for log_n bits.
///
/// # Arguments
/// * `i` - The index to reverse
/// * `log_n` - Number of bits (log2 of N)
///
/// # Returns
/// The bit-reversed index
#[inline]
pub fn bit_reverse(i: usize, log_n: usize) -> usize {
    i.reverse_bits() >> (usize::BITS as usize - log_n)
}

/// Applies bit-reversal permutation to an array in-place.
///
/// # Arguments
/// * `a` - The array to permute
/// * `log_n` - log2(a.len())
pub fn bit_reverse_copy<T: Copy>(a: &mut [T], log_n: usize) {
    let n = a.len();
    for i in 0..n {
        let j = bit_reverse(i, log_n);
        if i < j {
            a.swap(i, j);
        }
    }
}

/// Montgomery reduction parameter R = 2^32 for 32-bit operations.
/// This is useful for optimizing modular multiplication.
#[allow(dead_code)]
pub const MONTGOMERY_R: u64 = 1u64 << 32;

/// Computes the Montgomery constant -q^(-1) mod R for Montgomery reduction.
#[allow(dead_code)]
pub fn compute_montgomery_constant(q: u64) -> u64 {
    // We need -q^(-1) mod 2^32
    let r = MONTGOMERY_R;
    let q_inv = mod_inverse(q % r, r).unwrap();
    r - q_inv
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mod_exp() {
        assert_eq!(mod_exp(2, 10, 1000), 24); // 2^10 = 1024 mod 1000 = 24
        assert_eq!(mod_exp(3, 4, 17), 13); // 3^4 = 81 mod 17 = 13
        assert_eq!(mod_exp(2, 0, 17), 1);
        assert_eq!(mod_exp(0, 5, 17), 0);
    }

    #[test]
    fn test_mod_inverse() {
        assert_eq!(mod_inverse(3, 17), Some(6)); // 3 * 6 = 18 ≡ 1 (mod 17)
        assert_eq!(mod_inverse(2, 17), Some(9)); // 2 * 9 = 18 ≡ 1 (mod 17)
        assert_eq!(mod_inverse(0, 17), None);
        assert_eq!(mod_inverse(4, 8), None); // gcd(4, 8) = 4 ≠ 1
    }

    #[test]
    fn test_is_ntt_friendly_prime() {
        // For cyclic NTT, we need q ≡ 1 (mod n)

        // Kyber: q = 3329, n = 256
        // 3329 - 1 = 3328 = 256 * 13, so 3328 % 256 = 0 ✓
        assert!(is_ntt_friendly_prime(3329, 256));

        // q = 17, n = 8
        // 17 - 1 = 16, 16 % 8 = 0 ✓
        assert!(is_ntt_friendly_prime(17, 8));

        // q = 17, n = 16
        // 16 % 16 = 0 ✓
        assert!(is_ntt_friendly_prime(17, 16));

        // q = 17, n = 4
        // 16 % 4 = 0 ✓
        assert!(is_ntt_friendly_prime(17, 4));

        // q = 13, n = 8
        // 12 % 8 = 4 ≠ 0 ✗
        assert!(!is_ntt_friendly_prime(13, 8));
    }

    #[test]
    fn test_is_negacyclic_ntt_friendly() {
        // For negacyclic NTT, we need q ≡ 1 (mod 2n)

        // q = 17, n = 8: 16 % 16 = 0 ✓
        assert!(is_negacyclic_ntt_friendly(17, 8));

        // q = 17, n = 4: 16 % 8 = 0 ✓
        assert!(is_negacyclic_ntt_friendly(17, 4));

        // Kyber: q = 3329, n = 256: 3328 % 512 = 256 ≠ 0 ✗
        // Kyber doesn't support full negacyclic NTT, uses special structure
        assert!(!is_negacyclic_ntt_friendly(3329, 256));

        // q = 7681, n = 256: 7680 % 512 = 0 ✓
        assert!(is_negacyclic_ntt_friendly(7681, 256));
    }

    #[test]
    fn test_find_primitive_root() {
        // For q = 17, n = 8 (cyclic NTT)
        let omega = find_primitive_root(17, 8).unwrap();
        // omega^8 should be 1 (mod 17)
        assert_eq!(mod_exp(omega, 8, 17), 1);
        // omega^4 should NOT be 1 (primitive)
        assert_ne!(mod_exp(omega, 4, 17), 1);
    }

    #[test]
    fn test_find_primitive_2n_root() {
        // For q = 17, n = 8 (negacyclic NTT)
        let psi = find_primitive_2n_root(17, 8).unwrap();
        // psi^8 should be -1 (mod 17), i.e., 16
        assert_eq!(mod_exp(psi, 8, 17), 16);
        // psi^16 should be 1
        assert_eq!(mod_exp(psi, 16, 17), 1);
    }

    #[test]
    fn test_bit_reverse() {
        // For n = 8 (log_n = 3)
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
    fn test_bit_reverse_copy() {
        let mut arr = [0, 1, 2, 3, 4, 5, 6, 7];
        bit_reverse_copy(&mut arr, 3);
        assert_eq!(arr, [0, 4, 2, 6, 1, 5, 3, 7]);
    }

    #[test]
    fn test_kyber_parameters() {
        // Verify Kyber parameters
        let q: u64 = 3329;
        let n: usize = 256;

        // 3329 - 1 = 3328 = 256 * 13
        // So q ≡ 1 (mod 256), supports 256-point cyclic NTT
        assert!(is_ntt_friendly_prime(q, n));

        // Find 256-th root of unity for cyclic NTT
        let omega = find_primitive_root(q, n).unwrap();
        println!("Kyber 256-th root of unity: {}", omega);

        // ω^256 should be 1 (mod 3329)
        assert_eq!(mod_exp(omega, 256, q), 1);
        // ω^128 should NOT be 1 (primitive)
        assert_ne!(mod_exp(omega, 128, q), 1);
    }

    #[test]
    fn test_small_prime_7681() {
        // q = 7681 = 1 + 30 * 256 = 1 + 15 * 512
        // Supports both cyclic (n=256) and negacyclic (n=256) NTT
        let q: u64 = 7681;
        let n: usize = 256;

        assert!(is_ntt_friendly_prime(q, n));
        assert!(is_negacyclic_ntt_friendly(q, n));

        // Find 2n-th root for negacyclic
        let psi = find_primitive_2n_root(q, n).unwrap();
        assert_eq!(mod_exp(psi, 256, q), q - 1); // psi^n = -1
        assert_eq!(mod_exp(psi, 512, q), 1); // psi^(2n) = 1
    }
}
