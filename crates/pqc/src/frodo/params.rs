//! FrodoKEM parameter sets (round-3 specification, 2020-09-30, Table 2).
//!
//! The scheme is generic over this trait; concrete parameter sets are
//! zero-sized types. Each FrodoKEM size comes in the two variants defined
//! by the submission for generating the public matrix `A` — AES128 (the
//! default, `Frodo640` / `Frodo976` / `Frodo1344`) and SHAKE128 (the
//! alternative for platforms without AES, `Frodo640Shake` / …).

/// Per-parameter-set constants (round-3 spec, Table 2 / reference `api.h`).
pub trait FrodoParams: 'static {
    /// Ring/matrix dimension `n` (the LWE secret has `n·n̄` entries).
    const N: usize;
    /// Matrix dimension `n̄` (always 8).
    const NBAR: usize;
    /// `log2(q)`: 15 for FrodoKEM-640, 16 for -976/-1344.
    const LOGQ: u32;
    /// Bits extracted per key-encode coefficient (2 / 3 / 4).
    const EXTRACTED_BITS: u32;
    /// Discrete-Gaussian-style CDF table of the error distribution
    /// (spec Table 3: 13 / 7 / 11 entries for χ of σ ≈ 2.4 / 1.5 / 1.2).
    const CDF: &'static [u16];
    /// Shared-secret length in bytes (16 / 24 / 32).
    const SS_BYTES: usize;
    /// Matrix-`A` generation mode: `false` = AES128 (submission default),
    /// `true` = SHAKE128.
    const SHAKE_A: bool;
    /// The submission's per-set XOF for all KEM hashing and noise
    /// sampling: SHAKE128 for FrodoKEM-640, SHAKE256 for -976/-1344
    /// (`#define shake …` in the reference).
    const SHAKE256: bool;

    /// `μ` length in bytes: `EXTRACTED_BITS·n̄²/8` (16 / 24 / 32).
    const MU_BYTES: usize = Self::EXTRACTED_BITS as usize * Self::NBAR * Self::NBAR / 8;
    /// Encoded public-key length: `16 + LOGQ·N·N̄/8`.
    const EK_BYTES: usize = 16 + Self::LOGQ as usize * Self::N * Self::NBAR / 8;
    /// Encoded secret-key length:
    /// `SS + EK + 2·N·N̄ + SS` (the `s`, `pk`, raw `S` matrix and `pkh`).
    const DK_BYTES: usize =
        Self::SS_BYTES + Self::EK_BYTES + 2 * Self::N * Self::NBAR + Self::SS_BYTES;
    /// Ciphertext length: `LOGQ·(N·N̄ + N̄²)/8`.
    const CT_BYTES: usize =
        Self::LOGQ as usize * (Self::N * Self::NBAR + Self::NBAR * Self::NBAR) / 8;
}

/// FrodoKEM-640 (NIST security category 1), matrix `A` via AES128.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Frodo640;
impl FrodoParams for Frodo640 {
    const N: usize = 640;
    const NBAR: usize = 8;
    const LOGQ: u32 = 15;
    const EXTRACTED_BITS: u32 = 2;
    const CDF: &'static [u16] = &[
        4643, 13363, 20579, 25843, 29227, 31145, 32103, 32525, 32689, 32745, 32762, 32766, 32767,
    ];
    const SS_BYTES: usize = 16;
    const SHAKE_A: bool = false;
    const SHAKE256: bool = false;
}

/// FrodoKEM-976 (NIST security category 3), matrix `A` via AES128.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Frodo976;
impl FrodoParams for Frodo976 {
    const N: usize = 976;
    const NBAR: usize = 8;
    const LOGQ: u32 = 16;
    const EXTRACTED_BITS: u32 = 3;
    const CDF: &'static [u16] = &[
        5638, 15915, 23689, 28571, 31116, 32217, 32613, 32731, 32760, 32766, 32767,
    ];
    const SS_BYTES: usize = 24;
    const SHAKE_A: bool = false;
    const SHAKE256: bool = true;
}

/// FrodoKEM-1344 (NIST security category 5), matrix `A` via AES128.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Frodo1344;
impl FrodoParams for Frodo1344 {
    const N: usize = 1344;
    const NBAR: usize = 8;
    const LOGQ: u32 = 16;
    const EXTRACTED_BITS: u32 = 4;
    const CDF: &'static [u16] = &[9142, 23462, 30338, 32361, 32725, 32765, 32767];
    const SS_BYTES: usize = 32;
    const SHAKE_A: bool = false;
    const SHAKE256: bool = true;
}

/// FrodoKEM-640 with the SHAKE128 matrix-`A` generation (submission
/// variant for platforms without AES; identical parameters).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Frodo640Shake;
impl FrodoParams for Frodo640Shake {
    const N: usize = 640;
    const NBAR: usize = 8;
    const LOGQ: u32 = 15;
    const EXTRACTED_BITS: u32 = 2;
    const CDF: &'static [u16] = &[
        4643, 13363, 20579, 25843, 29227, 31145, 32103, 32525, 32689, 32745, 32762, 32766, 32767,
    ];
    const SS_BYTES: usize = 16;
    const SHAKE_A: bool = true;
    const SHAKE256: bool = false;
}

/// FrodoKEM-976 with the SHAKE128 matrix-`A` generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Frodo976Shake;
impl FrodoParams for Frodo976Shake {
    const N: usize = 976;
    const NBAR: usize = 8;
    const LOGQ: u32 = 16;
    const EXTRACTED_BITS: u32 = 3;
    const CDF: &'static [u16] = &[
        5638, 15915, 23689, 28571, 31116, 32217, 32613, 32731, 32760, 32766, 32767,
    ];
    const SS_BYTES: usize = 24;
    const SHAKE_A: bool = true;
    const SHAKE256: bool = true;
}

/// FrodoKEM-1344 with the SHAKE128 matrix-`A` generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Frodo1344Shake;
impl FrodoParams for Frodo1344Shake {
    const N: usize = 1344;
    const NBAR: usize = 8;
    const LOGQ: u32 = 16;
    const EXTRACTED_BITS: u32 = 4;
    const CDF: &'static [u16] = &[9142, 23462, 30338, 32361, 32725, 32765, 32767];
    const SS_BYTES: usize = 32;
    const SHAKE_A: bool = true;
    const SHAKE256: bool = true;
}
