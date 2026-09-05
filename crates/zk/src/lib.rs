#![allow(clippy::module_inception)]
//! Lattice-based zero-knowledge proof building blocks on the [`algebra`]
//! foundation.
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
//! [`algebra`]: https://docs.rs/lattice-algebra

pub mod protocols;
