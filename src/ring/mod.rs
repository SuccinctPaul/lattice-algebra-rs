pub mod poly_ring;

pub(crate) mod reduction;
mod sample;
mod traits;
pub mod zq;
/// export the trait
pub use traits::*;
#[cfg(test)]
// Generally, it's used for test purpose.
pub type Zq17 = self::zq::Zq<17>;
