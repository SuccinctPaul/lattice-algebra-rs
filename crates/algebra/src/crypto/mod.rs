//! Cryptographic infrastructure (L4): XOFs, samplers, Fiat–Shamir
//! transcripts and wire-format bit packing.
//!
//! Everything here is deterministic and XOF-driven; see [`sampling`] and
//! [`xof`] for the design rationale.

pub mod sampling;
pub mod transcript;
pub mod xof;

pub mod bits;
