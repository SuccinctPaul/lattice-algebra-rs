#![no_std]
#![allow(clippy::module_inception)]
#![deny(missing_docs)]
//! Lattice-based zero-knowledge proof building blocks on the [`algebra`]
//! foundation, organized by **domain**: each directory is one domain, and
//! the layering is strict —
//!
//! The crate is `#![no_std]` and links `alloc`.
//!
//! ```text
//! foundation ──▶ instance ──▶ commitment ──▶ sigma / opening / pcs / sumcheck / shortness / folding
//! (utils)       (rings,       (Ajtai keys)   (protocol domains; they may compose with
//!                R1CS)                        each other but only downward in this list)
//! ```
//!
//! # Domains
//!
//! - [`foundation`]: protocol-agnostic utilities — ring-shaped samplers,
//!   Fiat–Shamir derivation, canonical wire encoding.
//! - [`instance`]: the concrete algebra — the `Z_{2^32}[X]/(X^64+1)` ring
//!   and the toy-R1CS instance layer.
//! - [`commitment`]: Ajtai/SIS commitments — the shared Z2-ring key type
//!   and the Z1 instance with the `LatticeCommitment` trait.
//! - [`sigma`]: Lyubashevsky-style approximate-knowledge Sigma-protocol
//!   with Fiat–Shamir NIZK (Z1).
//! - [`opening`]: LaBRADOR-style batched opening over the Z2 ring (Z2).
//! - [`pcs`]: Greyhound-style polynomial commitment over the Z1 ring —
//!   commit to `f`, open at a point with a proof of `y = f(x)` (Z7);
//!   `pcs::batched` proves `k` claims at one shared point with a single
//!   HyperBall-weighted folded opening.
//! - [`sumcheck`]: multilinear ring-sumcheck + gadget-IPA (Z3);
//!   `sumcheck::batch` merges multiple assertions into one Π_batch-shaped
//!   round structure and `sumcheck::range` carries digit-range / Booleanity
//!   claims via vanishing polynomials.
//! - [`shortness`]: projection / norm-bound arguments — digit-balanced and
//!   gadget-slack flavors (Z5).
//! - [`folding`]: Nova-style folding (Z4) and LatticeFold-style
//!   decomposition folding (Z5).
//!
//! Milestone labels (Z1–Z5) are roadmap tags and live in module docs and
//! the README, not in module names. A primitive-level survey of the scheme
//! landscape maps each domain to the literature
//! (`crates/zk/docs/survey-lattice-zksnarks.md`).
//!
//! [`algebra`]: algebra

extern crate alloc;
// Tests link std so they can keep using `Instant`, `eprintln!` and the
// thread RNG; the library proper never sees it.
#[cfg(test)]
extern crate std;

pub mod commitment;
pub mod folding;
pub mod foundation;
pub mod instance;
pub mod opening;
pub mod pcs;
pub mod shortness;
pub mod sigma;
pub mod sumcheck;
