//! ML-KEM parameter sets (FIPS 203, Table 2).
//!
//! The scheme is generic over this trait; concrete parameter sets are
//! zero-sized types (`MlKem512`, `MlKem768`, `MlKem1024`) so the selected
//! parameter set appears in the type of every key.

/// Modulus shared by all ML-KEM parameter sets: `q = 3329 = 2^8·13 + 1`.
pub const Q: u64 = 3_329;
/// Ring dimension shared by all ML-KEM parameter sets.
pub const N: usize = 256;
/// Twiddle constant (FIPS 203, §4.3): `ζ = 17` has order 256 —
/// `ζ^128 ≡ −1 (mod q)` — which is why the transform has seven layers.
pub const T_ZETA: u64 = 17;

/// Per-parameter-set constants (FIPS 203, Table 2).
pub trait MlKemParams: 'static {
    /// Number of rows/columns of `Â` (module rank).
    const K: usize;
    /// Noise rate of the secret (and of `y` in encryption).
    const ETA1: usize;
    /// Noise rate of the encryption error `e1, e2`.
    const ETA2: usize;
    /// Compression factor of `u` (ciphertext part 1).
    const DU: usize;
    /// Compression factor of `v` (ciphertext part 2).
    const DV: usize;

    /// Encapsulation-key length in bytes (`384k + 32`).
    const EK_BYTES: usize = 384 * Self::K + 32;
    /// Decapsulation-key length in bytes (`768k + 96`, FIPS 203 augmented format).
    const DK_BYTES: usize = 768 * Self::K + 96;
    /// Ciphertext length in bytes (`32·du·k + 32·dv`).
    const CT_BYTES: usize = 32 * Self::K * Self::DU + 32 * Self::DV;
}

/// ML-KEM-512 (NIST security category 1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MlKem512;

impl MlKemParams for MlKem512 {
    const K: usize = 2;
    const ETA1: usize = 3;
    const ETA2: usize = 2;
    const DU: usize = 10;
    const DV: usize = 4;
}

/// ML-KEM-768 (NIST security category 3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MlKem768;

impl MlKemParams for MlKem768 {
    const K: usize = 3;
    const ETA1: usize = 2;
    const ETA2: usize = 2;
    const DU: usize = 10;
    const DV: usize = 4;
}

/// ML-KEM-1024 (NIST security category 5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MlKem1024;

impl MlKemParams for MlKem1024 {
    const K: usize = 4;
    const ETA1: usize = 2;
    const ETA2: usize = 2;
    const DU: usize = 11;
    const DV: usize = 5;
}
