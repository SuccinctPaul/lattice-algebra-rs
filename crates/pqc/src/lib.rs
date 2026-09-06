#![allow(clippy::module_inception)]
//! Post-quantum cryptography schemes built on the `algebra` foundation
//! (crate `lattice-algebra`).
//!
//! - [`mldsa`]: ML-DSA (FIPS 204) digital signatures — keygen, deterministic
//!   and randomized signing, verification, for all three parameter sets.
//!
//! ML-KEM (FIPS 203) and FN-DSA / Falcon (FIPS 206) are planned; see the
//! roadmap in the repository docs.

pub mod mldsa;
