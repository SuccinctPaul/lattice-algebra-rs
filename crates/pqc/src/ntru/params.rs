//! NTRU parameter sets (round-3 specification, 2020-10-16, Table 3).
//!
//! The scheme is generic over this trait; concrete parameter sets are
//! zero-sized types. Two families exist: `HPS` (product-form secrets with
//! fixed-weight `g`/`m`) and `HRSS` (sampled via `sample_iid_plus`, with
//! `g = 3·(x−1)·g'` and free ternary `m`).

/// Per-parameter-set constants (round-3 spec, Table 3 / reference `params.h`).
pub trait NtruParams: 'static {
    /// Ring dimension `n` (prime, with 2 a generator of (Z/n)*).
    const N: usize;
    /// `log2(q)`: 11 / 12 / 13.
    const LOGQ: u32;
    /// `true` for the HPS family (ntruhps…), `false` for HRSS (ntruhrss701).
    const HPS: bool;

    /// Fixed Hamming weight of `g`/`m` (HPS): `q/8 − 2`.
    const WEIGHT: usize = (1 << Self::LOGQ) / 8 - 2;

    /// Bytes consumed to sample `(f, g)`: HPS draws `(n−1)` iid bytes
    /// plus `ceil(30·(n−1)/8)` for the fixed-type poly; HRSS draws
    /// `2·(n−1)` iid bytes.
    const SAMPLE_FG_BYTES: usize = Self::N
        - 1
        + if Self::HPS {
            (30 * (Self::N - 1)).div_ceil(8)
        } else {
            Self::N - 1
        };
    /// Bytes consumed to sample `(r, m)` (same shape as `(f, g)`).
    const SAMPLE_RM_BYTES: usize = Self::SAMPLE_FG_BYTES;
    /// Packed ternary polynomial size: `ceil((n−1)/5)`.
    const PACK_TRINARY_BYTES: usize = (Self::N - 1).div_ceil(5);
    /// Public-key / ciphertext length: `ceil(logq·(n−1)/8)`.
    const PUBLICKEY_BYTES: usize = (Self::LOGQ as usize * (Self::N - 1)).div_ceil(8);
    /// Secret key: `f ‖ f⁻¹ ‖ f⁻¹h ‖ PRF key`.
    const SECRETKEY_BYTES: usize =
        2 * Self::PACK_TRINARY_BYTES + Self::PUBLICKEY_BYTES + 32;
}

/// ntruhps2048677 (NIST security category 1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NtruHps2048677;
impl NtruParams for NtruHps2048677 {
    const N: usize = 677;
    const LOGQ: u32 = 11;
    const HPS: bool = true;
}

/// ntruhps2048821 (NIST security category 3, 2048-noise variant).
///
/// The round-3 submission ships no official KAT vectors for this set (its
/// KAT directory covers 2048677/4096821/hrss701); it shares the exact code
/// path of the KAT-verified sets and is exercised by round-trip tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NtruHps2048821;
impl NtruParams for NtruHps2048821 {
    const N: usize = 821;
    const LOGQ: u32 = 11;
    const HPS: bool = true;
}

/// ntruhps4096821 (NIST security category 3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NtruHps4096821;
impl NtruParams for NtruHps4096821 {
    const N: usize = 821;
    const LOGQ: u32 = 12;
    const HPS: bool = true;
}

/// ntruhps40961229 (NIST security category 5).
///
/// Like ntruhps2048821, no official KAT vectors ship for this set; covered
/// by round-trip tests.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NtruHps40961229;
impl NtruParams for NtruHps40961229 {
    const N: usize = 1229;
    const LOGQ: u32 = 12;
    const HPS: bool = true;
}

/// ntruhrss701 (NIST security category 1, HRSS family).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NtruHrss701;
impl NtruParams for NtruHrss701 {
    const N: usize = 701;
    const LOGQ: u32 = 13;
    const HPS: bool = false;
}
