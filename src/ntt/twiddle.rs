//! Twiddle Factors for NTT
//!
//! This module provides precomputed twiddle factors (powers of roots of unity)
//! for efficient NTT computation.

use crate::ntt::params::{bit_reverse, NttParams};
use crate::ring::Ring;

/// Precomputed twiddle factors for NTT operations.
///
/// Twiddle factors are powers of roots of unity used in the butterfly operations.
/// Precomputing them avoids repeated exponentiation during NTT.
#[derive(Debug, Clone)]
pub struct TwiddleFactors<R: Ring, const N: usize> {
    /// Powers of ψ for forward NTT (bit-reversed order)
    /// psi_powers[i] = ψ^(bit_reverse(i))
    pub psi_powers: Vec<R>,

    /// Powers of ψ^(-1) for inverse NTT (bit-reversed order)
    pub psi_inv_powers: Vec<R>,

    /// Powers of ω for standard cyclic NTT (bit-reversed order)
    pub omega_powers: Vec<R>,

    /// Powers of ω^(-1) for standard cyclic INTT (bit-reversed order)
    pub omega_inv_powers: Vec<R>,

    /// Inverse of N for scaling after INTT
    pub n_inv: R,
}

impl<R: Ring, const N: usize> TwiddleFactors<R, N> {
    /// Creates precomputed twiddle factors for NTT of dimension N.
    ///
    /// # Panics
    /// - If N is not a power of 2
    /// - If the modulus is not NTT-friendly
    pub fn new() -> Self {
        let params = NttParams::<R, N>::new();
        Self::from_params(&params)
    }

    /// Creates twiddle factors from existing NTT parameters.
    pub fn from_params(params: &NttParams<R, N>) -> Self {
        // Compute powers of ψ in bit-reversed order for negacyclic NTT
        let psi_powers = Self::compute_powers_bit_reversed(params.psi, N);
        let psi_inv_powers = Self::compute_powers_bit_reversed(params.psi_inv, N);

        // Compute powers of ω for standard NTT
        let omega_powers = Self::compute_powers_bit_reversed(params.omega, N);
        let omega_inv_powers = Self::compute_powers_bit_reversed(params.omega_inv, N);

        Self {
            psi_powers,
            psi_inv_powers,
            omega_powers,
            omega_inv_powers,
            n_inv: params.n_inv,
        }
    }

    /// Computes powers of a root in bit-reversed order.
    ///
    /// Returns [root^0, root^(br(1)), root^(br(2)), ..., root^(br(N-1))]
    /// where br(i) is the bit-reversal of i.
    fn compute_powers_bit_reversed(root: R, n: usize) -> Vec<R> {
        let log_n = n.trailing_zeros();
        let mut powers = vec![R::ONE; n];

        // Compute powers in natural order first
        let mut power = R::ONE;
        for i in 0..n {
            let j = bit_reverse(i, log_n);
            powers[j] = power;
            power *= root;
        }

        powers
    }

    /// Computes twiddle factors for a specific stage of Cooley-Tukey NTT.
    ///
    /// For stage s (butterfly size 2^(s+1)), returns the twiddle factors
    /// needed for all butterflies in that stage.
    pub fn stage_twiddles_ct(&self, stage: usize) -> Vec<R> {
        let m = 1 << (stage + 1); // Butterfly size
        let half_m = m / 2;
        let step = N / m;

        let mut twiddles: Vec<_> = (0..half_m).map(|j| self.omega_powers[j * step]).collect();
        twiddles[0] = R::ONE;
        twiddles
    }

    /// Computes twiddle factors for a specific stage of Gentleman-Sande INTT.
    pub fn stage_twiddles_gs(&self, stage: usize) -> Vec<R> {
        let m = 1 << (stage + 1);
        let half_m = m / 2;
        let step = N / m;

        let mut twiddles: Vec<_> = (0..half_m)
            .map(|j| self.omega_inv_powers[j * step])
            .collect();
        twiddles[0] = R::ONE;
        twiddles
    }
}

impl<R: Ring, const N: usize> Default for TwiddleFactors<R, N> {
    fn default() -> Self {
        Self::new()
    }
}

/// Precomputed twiddle factors specifically optimized for negacyclic NTT.
///
/// For polynomial multiplication in Z_q[x]/(x^n + 1), we use negacyclic NTT
/// which incorporates powers of ψ (primitive 2n-th root of unity).
#[derive(Debug, Clone)]
pub struct NegacyclicTwiddles<R: Ring, const N: usize> {
    /// Powers of ψ for pre-processing: [ψ^0, ψ^1, ..., ψ^(N-1)]
    pub psi_powers: Vec<R>,

    /// Powers of ψ^(-1) for post-processing
    pub psi_inv_powers: Vec<R>,
}

impl<R: Ring, const N: usize> NegacyclicTwiddles<R, N> {
    /// Creates precomputed twiddle factors for negacyclic NTT.
    pub fn new() -> Self {
        let params = NttParams::<R, N>::new();

        // Compute sequential powers of ψ
        let psi_powers = Self::compute_sequential_powers(params.psi, N);
        let psi_inv_powers = Self::compute_sequential_powers(params.psi_inv, N);

        Self {
            psi_powers,
            psi_inv_powers,
        }
    }

    /// Computes sequential powers: [root^0, root^1, ..., root^(n-1)]
    fn compute_sequential_powers(root: R, n: usize) -> Vec<R> {
        let mut powers = vec![R::ONE; n];
        let mut power = R::ONE;
        for p in &mut powers {
            *p = power;
            power *= root;
        }
        powers
    }
}

impl<R: Ring, const N: usize> Default for NegacyclicTwiddles<R, N> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::zq::Zq;

    type Zq17 = Zq<17>;

    #[test]
    fn test_twiddle_factors_creation() {
        let twiddles = TwiddleFactors::<Zq17, 8>::new();

        // Should have N twiddle factors
        assert_eq!(twiddles.psi_powers.len(), 8);
        assert_eq!(twiddles.omega_powers.len(), 8);

        // First element should be 1
        assert_eq!(twiddles.psi_powers[0], Zq17::ONE);
        assert_eq!(twiddles.omega_powers[0], Zq17::ONE);
    }

    #[test]
    fn test_negacyclic_twiddles() {
        let twiddles = NegacyclicTwiddles::<Zq17, 8>::new();

        // Should have N twiddle factors
        assert_eq!(twiddles.psi_powers.len(), 8);
        assert_eq!(twiddles.psi_inv_powers.len(), 8);
    }

    #[test]
    fn test_psi_powers() {
        let params = NttParams::<Zq17, 8>::new();
        let twiddles = NegacyclicTwiddles::<Zq17, 8>::new();

        // Verify ψ^i * ψ^(-i) = 1
        for i in 0..8 {
            let product = twiddles.psi_powers[i] * twiddles.psi_inv_powers[i];
            assert_eq!(product, Zq17::ONE, "ψ^{} * ψ^(-{}) should be 1", i, i);
        }

        // Verify ψ^N = -1 (since ψ is primitive 2N-th root)
        let psi_n = params.psi.pow(8);
        assert_eq!(psi_n, -Zq17::ONE, "ψ^N should be -1");
    }
}
