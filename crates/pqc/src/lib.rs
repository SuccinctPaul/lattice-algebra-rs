#![allow(clippy::module_inception)]
//! Post-quantum cryptography schemes built on the `algebra` foundation
//! (crate `lattice-algebra`).
//!
//! - [`falcon`]: Falcon (round-3 spec; the future FN-DSA / FIPS 206) —
//!   keygen, sign and verify for Falcon-512 and Falcon-1024.
//! - [`mlkem`]: ML-KEM (FIPS 203) key encapsulation — keygen, encapsulation
//!   and decapsulation (implicit rejection) for all three parameter sets.
//! - [`mldsa`]: ML-DSA (FIPS 204) digital signatures — keygen, deterministic
//!   and randomized signing, verification, for all three parameter sets.

pub mod falcon;
pub mod mldsa;
pub mod mlkem;
