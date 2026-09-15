#![allow(clippy::module_inception)]
#![deny(missing_docs)]
//! Lattice-based zero-knowledge proof building blocks on the [`algebra`]
//! foundation.
//!
//! The crate splits into a shared-utility layer and the protocol layer:
//!
//! # Utilities (protocol-agnostic, shared by all proofs)
//!
//! - [`sampling`]: protocol-level samplers — uniform expansion, centered
//!   bounded / CBD masks, sparse in-ball challenges and the soundness-
//!   critical non-unit linear challenges, all XOF-driven and generic over
//!   the coefficient ring.
//! - [`fs`]: Fiat–Shamir derivation — transcript absorption of ring vectors
//!   and domain-separated seed re-expansion.
//! - [`encoding`]: the canonical ring ↔ little-endian wire encoding shared
//!   by transcripts and proof serialization.
//!
//! # Protocols ([`protocols`])
//!
//! - [`protocols::commitment`]: Ajtai/SIS lattice commitments.
//! - [`protocols::sigma`]: Lyubashevsky-style approximate-knowledge
//!   Sigma-protocol with Fiat-Shamir NIZK (Z1).
//! - [`protocols::z2_ring`] + [`protocols::z2`]: batch opening over
//!   `Z_{2^32}[X]/(X^64+1)` (Z2).
//! - [`protocols::sumcheck`]: multilinear ring-sumcheck (Z3).
//! - [`protocols::ipa`]: gadget-based inner-product argument with approximate
//!   opening (Z3).
//! - [`protocols::fold`]: Nova-style folding / IVC layer (Z4).
//!
//! [`algebra`]: algebra

pub mod encoding;
pub mod fs;
pub mod protocols;
pub mod sampling;
