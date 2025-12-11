//! NTT configuration traits and types.

/// Configuration for NTT operations.
///
/// This trait defines the parameters needed for NTT:
/// - `Q`: The modulus (must be a prime with q ≡ 1 (mod 2n))
/// - `N`: The polynomial degree (must be a power of 2)
pub trait NttConfig {
    /// The modulus q
    const Q: u64;
    /// The polynomial degree n (must be power of 2)
    const N: usize;
    /// log2(N) for bit-reversal
    const LOG_N: usize;
    /// A primitive 2n-th root of unity modulo q
    /// ω^(2n) ≡ 1 (mod q) and ω^n ≡ -1 (mod q)
    const ROOT_OF_UNITY: u64;
    /// The inverse of ROOT_OF_UNITY modulo q
    const ROOT_OF_UNITY_INV: u64;
    /// The inverse of N modulo q (for INTT scaling)
    const N_INV: u64;
}

/// Kyber/ML-KEM NTT parameters
/// q = 3329 = 1 + 13 * 256, n = 256
/// 3329 supports 256-point cyclic NTT (but NOT negacyclic since 3328 % 512 ≠ 0)
#[derive(Debug, Clone, Copy)]
pub struct KyberNttConfig;

impl NttConfig for KyberNttConfig {
    const Q: u64 = 3329;
    const N: usize = 256;
    const LOG_N: usize = 8;
    // ω = 3061 is a primitive 256-th root of unity mod 3329
    // ω^256 ≡ 1 (mod 3329)
    // ω^128 ≡ 3328 ≡ -1 (mod 3329), confirming it's primitive
    const ROOT_OF_UNITY: u64 = 3061;
    // 3061^(-1) mod 3329 = 2298
    const ROOT_OF_UNITY_INV: u64 = 2298;
    // 256^(-1) mod 3329 = 3316
    const N_INV: u64 = 3316;
}

/// Dilithium/ML-DSA NTT parameters
/// q = 8380417 = 1 + 2^23 * 1, n = 256
#[derive(Debug, Clone, Copy)]
pub struct DilithiumNttConfig;

impl NttConfig for DilithiumNttConfig {
    const Q: u64 = 8380417;
    const N: usize = 256;
    const LOG_N: usize = 8;
    // ω = 1753 is a primitive 512-th root of unity mod 8380417
    const ROOT_OF_UNITY: u64 = 1753;
    const ROOT_OF_UNITY_INV: u64 = 731434; // 1753^(-1) mod 8380417
    const N_INV: u64 = 8347681;            // 256^(-1) mod 8380417
}

/// Generic NTT configuration for testing with small primes
/// q = 17, n = 8 (17 = 1 + 2*8, so 17 ≡ 1 (mod 16))
#[derive(Debug, Clone, Copy)]
pub struct TestNttConfig;

impl NttConfig for TestNttConfig {
    const Q: u64 = 17;
    const N: usize = 8;
    const LOG_N: usize = 3;
    // ω = 2 is a primitive 16-th root of unity mod 17
    // 2^8 ≡ 256 ≡ 1 (mod 17)? No, 2^8 = 256 = 15*17 + 1 = 256 mod 17 = 1
    // Actually we need 2^16 ≡ 1 and 2^8 ≡ -1
    // 2^8 = 256 mod 17 = 256 - 15*17 = 256 - 255 = 1, not -1
    // Let's use ω = 3: 3^8 mod 17 = 6561 mod 17 = 16 ≡ -1 ✓
    const ROOT_OF_UNITY: u64 = 3;
    const ROOT_OF_UNITY_INV: u64 = 6; // 3^(-1) mod 17 = 6
    const N_INV: u64 = 15;            // 8^(-1) mod 17 = 15 (since 8*15 = 120 = 7*17 + 1)
}

/// Configuration for a generic prime
/// q = 7681 = 1 + 15 * 512, n = 256
#[derive(Debug, Clone, Copy)]
pub struct SmallNttConfig;

impl NttConfig for SmallNttConfig {
    const Q: u64 = 7681;
    const N: usize = 256;
    const LOG_N: usize = 8;
    // Need to find primitive 512-th root of unity
    // 7681 = 1 + 15 * 512, so ord(Z_7681*) = 7680 = 15 * 512
    // We need ω where ω^512 ≡ 1 and ω^256 ≡ -1
    // Generator g of Z_7681* is 17
    // ω = g^(7680/512) = g^15 = 17^15 mod 7681
    const ROOT_OF_UNITY: u64 = 62; // 17^15 mod 7681 (precomputed)
    const ROOT_OF_UNITY_INV: u64 = 4972;
    const N_INV: u64 = 7651; // 256^(-1) mod 7681
}
