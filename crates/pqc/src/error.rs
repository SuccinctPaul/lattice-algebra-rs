//! Typed errors for scheme APIs (L6).
//!
//! Scheme entry points validate their runtime-sized inputs and report
//! problems as [`InvalidInput`] instead of panicking: a caller-passed slice
//! of the wrong length is an API misuse, not a crash. Compile-time-sized
//! inputs (`&[u8; 32]` seeds, fixed key types) rule out the same errors by
//! construction. Decapsulation never fails at all — malformed or
//! manipulable ciphertexts fold into the implicit-rejection path by design.

use core::fmt;

/// Malformed caller input or a failed randomized key generation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InvalidInput {
    /// A byte-slice parameter had the wrong length.
    InvalidLength {
        /// Required length in bytes.
        expected: usize,
        /// Supplied length in bytes.
        got: usize,
    },
    /// Randomized key generation failed — the sampled polynomial is not
    /// invertible (Streamlined NTRU Prime's `R3_recip`; probability ≈ 1/q).
    /// Resample with fresh randomness, as the reference does.
    KeygenRetry,
}

impl InvalidInput {
    /// `Ok(())` when `got == expected`, otherwise [`Self::InvalidLength`].
    pub(crate) fn check_len(expected: usize, got: usize) -> SchemeResult<()> {
        if expected == got {
            Ok(())
        } else {
            Err(Self::InvalidLength { expected, got })
        }
    }
}

impl fmt::Display for InvalidInput {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLength { expected, got } => {
                write!(f, "invalid input length: expected {expected} bytes, got {got}")
            }
            Self::KeygenRetry => {
                write!(f, "keygen randomness unusable (non-invertible sample); retry with fresh randomness")
            }
        }
    }
}

impl std::error::Error for InvalidInput {}

/// Convenience alias for scheme results over [`InvalidInput`].
pub type SchemeResult<T> = core::result::Result<T, InvalidInput>;
