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
//! - [`error`]: the typed error surface shared by the scheme APIs.
//!
//! # API conventions
//!
//! - Randomness is always an explicit parameter (deterministic, KAT-driven
//!   design); no function draws from an ambient RNG.
//! - Runtime-sized inputs are validated and reported as
//!   [`InvalidInput`]; compile-time-sized inputs
//!   (`&[u8; 32]` seeds) rule the same errors out at type level.
//!   `from_bytes` constructors return `Option`; decapsulation never fails
//!   (implicit rejection).
//! - Each scheme names keys as its specification does: ML-KEM speaks of
//!   encapsulation/decapsulation keys, the round-3 submissions of
//!   public/secret keys. Per-set module names follow the same rule:
//!   `mlkem_512`/`mldsa_44` for the hyphenated FIPS names, `falcon512`/
//!   `frodo640`/`ntruhps2048677`/`sntrup761` for the concatenated
//!   submission names.

pub mod error;
pub mod falcon;
pub mod frodo;
pub mod mldsa;
pub mod mlkem;
pub mod ntru;
pub mod sntrup;

pub use error::{InvalidInput, SchemeResult};
