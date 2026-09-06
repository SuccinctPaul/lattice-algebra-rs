//! Scalar-ring layer (L0): the const-generic ring [`zq::Zq`], the capability
//! traits that gate its methods ([`traits`]), and the number theory
//! ([`number_theory`]) shared by the NTT engine and the samplers.

pub mod number_theory;
pub mod poly_ring;

pub(crate) mod reduction;
mod sample;
pub mod traits;
pub mod zq;

pub use traits::*;
#[cfg(test)]
mod axiom_tests;
// Test-only alias; referenced by the axiom and codec tests below.
#[cfg(test)]
pub type Zq17 = self::zq::Zq<17>;
