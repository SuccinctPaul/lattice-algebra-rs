//! Commitment domain: lattice commitments (L5).
//!
//! - [`key`]: the single Ajtai commitment-key implementation over the Z2
//!   ring — every Z2-ring protocol (opening, sumcheck/IPA, shortness,
//!   folding) commits through this one type;
//! - [`ajtai`]: the Z1 Ajtai/SIS instance on the ML-DSA ring with the
//!   `LatticeCommitment` trait and the Σ-protocol parameter types.

pub mod ajtai;
pub mod key;
