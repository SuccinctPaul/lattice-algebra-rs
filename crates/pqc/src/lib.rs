#![allow(clippy::module_inception)]
//! Post-quantum cryptography schemes built on the `algebra` foundation
//! (crate `lattice-algebra`).
//!
//! - [`mlkem`]: ML-KEM (FIPS 203) key encapsulation — keygen, encapsulation
//!   and decapsulation (implicit rejection) for all three parameter sets.
//! - [`mldsa`]: ML-DSA (FIPS 204) digital signatures — keygen, deterministic
//!   and randomized signing, verification, for all three parameter sets.
//!
//! FN-DSA / Falcon (FIPS 206) is planned; see the roadmap in the repository
//! docs.

pub mod mldsa;
pub mod mlkem;
