use crate::ring::reduction::ModularArithmetic;
use crate::ring::zq::Zq;

/// Barrett reduction constants for a given modulus.
pub struct Barrett<const MODULUS: u64> {
    pub mu: u128, // floor(2^128 / MODULUS)
}

impl<const MODULUS: u64> Barrett<MODULUS> {
    pub const fn new() -> Self {
        // 2^128 = u128::MAX + 1
        Self {
            mu: (u128::MAX as u128) + 1 / (MODULUS as u128),
        }
    }
    /// Barrett reduction: returns x mod MODULUS for x < MODULUS^2
    #[inline(always)]
    pub fn reduce(&self, x: u128) -> u64 {
        // Correct shift for Barrett reduction is 64 bits, not 128
        let q = ((x as u128).wrapping_mul(self.mu)) >> 64;
        let r = x - q * (MODULUS as u128);
        if r >= MODULUS as u128 {
            (r - MODULUS as u128) as u64
        } else {
            r as u64
        }
    }
}

impl<const MODULUS: u64> ModularArithmetic<MODULUS> for Zq<MODULUS> {
    #[inline(always)]
    fn mod_add(a: u64, b: u64) -> u64 {
        let sum = a.wrapping_add(b);
        if sum >= MODULUS { sum - MODULUS } else { sum }
    }
    #[inline(always)]
    fn mod_sub(a: u64, b: u64) -> u64 {
        if a >= b { a - b } else { MODULUS - (b - a) }
    }
    #[inline(always)]
    fn mod_mul(a: u64, b: u64) -> u64 {
        // Use Barrett reduction for large MODULUS
        if MODULUS > (1u64 << 32) {
            let barrett = Barrett::<MODULUS>::new();
            barrett.reduce((a as u128) * (b as u128))
        } else {
            ((a as u128 * b as u128) % (MODULUS as u128)) as u64
        }
    }
    #[inline(always)]
    fn barrett_reduce(x: u128) -> u64 {
        let barrett = Barrett::<MODULUS>::new();
        barrett.reduce(x)
    }
}
