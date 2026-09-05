//! ML-DSA parameter sets (FIPS 204, Table 1).
//!
//! The scheme is generic over this trait; concrete parameter sets are
//! zero-sized types (`MlDsa44`, `MlDsa65`, `MlDsa87`) so the selected
//! parameter set appears in the type of every key.

/// Global constants shared by all ML-DSA parameter sets.
pub const Q: i64 = 8_380_417; // 2^23 − 2^13 + 1
pub const N: usize = 256; // ring dimension
pub const D: u32 = 13; // dropped bits of t

/// Per-parameter-set constants (FIPS 204, Table 1).
pub trait MlDsaParams: 'static {
    /// Number of rows of Â.
    const K: usize;
    /// Number of columns of Â.
    const L: usize;
    /// Private-key range bound (s1, s2 ∈ [−η, η]).
    const ETA: u32;
    /// Number of ±1 coefficients of the challenge c.
    const TAU: u32;
    /// Range of the mask y (a power of two): 2^17 or 2^19.
    const GAMMA1: i64;
    /// Low-order rounding range: (q−1)/88 or (q−1)/32.
    const GAMMA2: i64;
    /// Maximum number of hint bits.
    const OMEGA: usize;
    /// Length of the commitment hash c̃ in bytes (λ/4).
    const C_TILDE_BYTES: usize;
}

/// ML-DSA-44 (NIST security category 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MlDsa44;

impl MlDsaParams for MlDsa44 {
    const K: usize = 4;
    const L: usize = 4;
    const ETA: u32 = 2;
    const TAU: u32 = 39;
    const GAMMA1: i64 = 1 << 17;
    const GAMMA2: i64 = (Q - 1) / 88; // 95232
    const OMEGA: usize = 80;
    const C_TILDE_BYTES: usize = 32;
}

/// ML-DSA-65 (NIST security category 3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MlDsa65;

impl MlDsaParams for MlDsa65 {
    const K: usize = 6;
    const L: usize = 5;
    const ETA: u32 = 4;
    const TAU: u32 = 49;
    const GAMMA1: i64 = 1 << 19;
    const GAMMA2: i64 = (Q - 1) / 32; // 261888
    const OMEGA: usize = 55;
    const C_TILDE_BYTES: usize = 48;
}

/// ML-DSA-87 (NIST security category 5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MlDsa87;

impl MlDsaParams for MlDsa87 {
    const K: usize = 8;
    const L: usize = 7;
    const ETA: u32 = 2;
    const TAU: u32 = 60;
    const GAMMA1: i64 = 1 << 19;
    const GAMMA2: i64 = (Q - 1) / 32; // 261888
    const OMEGA: usize = 75;
    const C_TILDE_BYTES: usize = 64;
}
