#![allow(clippy::module_inception)]
//! L0-L4 algebraic foundation for lattice-based cryptography.
//!
//! This crate is the shared substrate that the `lattice-pqc` (NIST PQC
//! schemes) and `lattice-zk` (zkSNARK building blocks) crates build on:
//!
//! - [`ring`]: scalar rings (`Zq`), negacyclic polynomial rings (`PolyRing`),
//!   capability traits (`Ring`, `Field`, `TwoAdicRing`, `CenteredRing`),
//!   modular reduction and compile-time-evaluable number theory.
//! - [`poly`]: univariate polynomials and sparse challenge polynomials.
//! - [`ntt`]: Cooley-Tukey / Gentleman-Sande NTT plus the
//!   [`ntt::NttDomain`] representation for polynomial rings.
//! - [`module`]: module-lattice vectors/matrices `R_q^K`, `R_q^{K x L}`,
//!   seed expansion and FIPS-exact rounding helpers.
//! - [`crypto`]: streaming SHAKE XOF, transcripts, reference-exact samplers,
//!   bit/serialization helpers and constant-time primitives.
//! - [`security`]: Core-SVP concrete-security estimation calibrated against
//!   the published Dilithium/ML-DSA analysis.
//! - [`matrix`]: generic matrices/vectors of ring elements.
//! - [`utils`]: small shared bit/byte conversion helpers (little-endian bit
//!   order, bit normalization).

pub mod crypto;
pub mod matrix;
pub mod module;
pub mod ntt;
pub mod poly;
pub mod ring;
pub mod security;
pub mod utils;
