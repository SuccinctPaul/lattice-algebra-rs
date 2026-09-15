#![allow(clippy::module_inception)]
#![deny(missing_docs)]
//! Post-quantum cryptography schemes built on the `algebra` foundation
//! (crate `lattice-algebra`).
//!
//! - [`falcon`]: Falcon (round-3 spec; the future FN-DSA / FIPS 206) —
//!   keygen, sign and verify for Falcon-512 and Falcon-1024.
//! - [`frodo`]: FrodoKEM (round-3 LWE-based KEM candidate) — keygen,
//!   encapsulation and decapsulation for 640/976/1344 in both the AES128
//!   and SHAKE128 matrix-`A` variants.
//! - [`mlkem`]: ML-KEM (FIPS 203) key encapsulation — keygen, encapsulation
//!   and decapsulation (implicit rejection) for all three parameter sets.
//! - [`ntru`]: NTRU (round-3 lattice KEM candidate) — keygen, encapsulation
//!   and decapsulation (implicit rejection) for the hps2048677, hps2048821,
//!   hps4096821, hps40961229 and hrss701 parameter sets.
//! - [`sntrup`]: Streamlined NTRU Prime (round-3 lattice KEM candidate;
//!   the sntrup761 deployed in OpenSSH) — keygen, encapsulation and
//!   decapsulation (implicit rejection) for p = 653/761/857/953/1013/1277.
//! - [`mldsa`]: ML-DSA (FIPS 204) digital signatures — keygen, deterministic
//!   and randomized signing, verification, for all three parameter sets.

pub mod falcon;
pub mod frodo;
pub mod mldsa;
pub mod mlkem;
pub mod ntru;
pub mod sntrup;
