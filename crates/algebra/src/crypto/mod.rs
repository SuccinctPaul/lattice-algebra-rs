//! Cryptographic infrastructure (L4): XOFs, samplers, Fiat–Shamir
//! transcripts, wire-format bit packing and constant-time primitives.
//!
//! Everything here is deterministic and XOF-driven; see [`sampling`] and
//! [`xof`] for the design rationale. [`ct`] holds the branch-free idioms
//! used on secret-dependent data (see its scope notes).

pub mod ct;
pub mod sampling;
pub mod transcript;
pub mod xof;

pub mod bits;
