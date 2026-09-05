pub mod barrett;

#[allow(unused)]
/// Trait for modular arithmetic with optional Barrett reduction.
pub trait ModularArithmetic<const MODULUS: u64> {
    /// Modular addition
    fn mod_add(a: u64, b: u64) -> u64;
    /// Modular subtraction
    fn mod_sub(a: u64, b: u64) -> u64;
    /// Modular multiplication (default: Barrett reduction if enabled)
    fn mod_mul(a: u64, b: u64) -> u64;
    /// Barrett reduction for a value (a < MODULUS^2)
    fn barrett_reduce(x: u128) -> u64;
}
