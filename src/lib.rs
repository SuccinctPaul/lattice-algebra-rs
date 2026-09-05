#![allow(clippy::module_inception)]
//! Unified facade over the lattice cryptography workspace.
//!
//! The workspace is split into three crates sharing one algebraic foundation:
//!
//! - [`algebra`] (crate `lattice-algebra`): L0-L4 foundation — scalar and
//!   polynomial rings, NTT, module lattices, XOF/sampling crypto.
//! - [`pqc`] (crate `lattice-pqc`): NIST PQC schemes (ML-DSA today).
//! - [`zk`] (crate `lattice-zk`): lattice zkSNARK building blocks.
//!
//! This facade re-exports every module under its historical path, so code
//! and docs written against the original single crate keep compiling:
//!
//! ```
//! use lattice_algebra_rs::module::ModuleVector;
//! use lattice_algebra_rs::mldsa::{MlDsa65, MlDsaParams};
//! use lattice_algebra_rs::protocols::commitment::CommitmentKey;
//! ```

pub use algebra;
pub use algebra::{crypto, matrix, module, ntt, poly, ring, utils};
pub use pqc;
pub use pqc::mldsa;
pub use zk;
pub use zk::protocols;
