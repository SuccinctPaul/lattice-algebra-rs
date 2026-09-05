#![allow(clippy::module_inception)]
//! L0-L4 algebraic foundation for lattice-based cryptography.
//!
//! This crate is the shared substrate the [`pqc`](https://docs.rs/lattice-pqc)
//! and [`zk`](https://docs.rs/lattice-zk) crates build on:
//!
//! - [`ring`]: scalar rings (`Zq`), negacyclic polynomial rings (`PolyRing`),
//!   capability traits (`Ring`, `Field`, `TwoAdicRing`, `CenteredRing`),
//!   Barrett reduction and const-time number theory.
//! - [`poly`]: univariate polynomials and sparse challenge polynomials.
//! - [`ntt`]: Cooley-Tukey / Gentleman-Sande NTT plus the [`NttDomain`]
//!   representation for polynomial rings.
//! - [`module`]: module-lattice vectors/matrices `R_q^K`, `R_q^{K x L}`,
//!   seed expansion and FIPS-exact rounding helpers.
//! - [`crypto`]: streaming SHAKE XOF, transcripts, reference-exact samplers
//!   and bit/serialization helpers.
//! - [`matrix`]: generic matrices/vectors of ring elements.

pub mod crypto;
pub mod matrix;
pub mod module;
pub mod ntt;
pub mod poly;
pub mod ring;
pub mod utils;
