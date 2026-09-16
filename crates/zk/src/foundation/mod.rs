//! Foundation domain: protocol-agnostic utilities shared by every proof
//! module (L5 utilities).
//!
//! - [`sampling`]: protocol-level samplers, generic over the ring;
//! - [`fs`]: Fiat–Shamir derivation (transcript absorption + seed
//!   re-expansion);
//! - [`encoding`]: the canonical ring ↔ little-endian wire encoding.

pub mod encoding;
pub mod fs;
pub mod sampling;
