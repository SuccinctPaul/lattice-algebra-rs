//! Core NTT Operations
//!
//! This module implements the Number Theoretic Transform (NTT) algorithms:
//! - Cooley-Tukey radix-2 DIT (Decimation-In-Time) for forward NTT
//! - Gentleman-Sande radix-2 DIF (Decimation-In-Frequency) for inverse NTT
//! - Negacyclic NTT for polynomial rings Z_q[x]/(x^n + 1)

use crate::ntt::params::{bit_reverse_permutation, NttParams};
use crate::ntt::twiddle::NegacyclicTwiddles;
use crate::ring::Ring;

/// NTT Operator for performing forward and inverse NTT transformations.
///
/// This struct encapsulates precomputed parameters and twiddle factors
/// for efficient NTT operations.
///
/// # Type Parameters
/// - `R`: The ring type (must implement `Ring` trait)
/// - `N`: The NTT dimension (must be a power of 2)
///
/// # Example
/// ```ignore
/// use lattice_algebra_rs::ntt::NttOperator;
/// use lattice_algebra_rs::ring::zq::Zq;
///
/// type Zq17 = Zq<17>;
/// let ntt = NttOperator::<Zq17, 8>::new();
///
/// let mut a = vec![Zq17::new(1), Zq17::new(2), Zq17::new(3), Zq17::new(4),
///                  Zq17::new(5), Zq17::new(6), Zq17::new(7), Zq17::new(8)];
/// ntt.forward(&mut a);
/// ntt.inverse(&mut a);
/// ```
#[derive(Debug, Clone)]
pub struct NttOperator<R: Ring, const N: usize> {
    /// NTT parameters
    params: NttParams<R, N>,
    /// Precomputed twiddle factors for negacyclic NTT
    twiddles: NegacyclicTwiddles<R, N>,
    /// log2(N)
    log_n: usize,
}

impl<R: Ring, const N: usize> NttOperator<R, N> {
    /// Creates a new NTT operator with precomputed parameters.
    ///
    /// # Panics
    /// - If N is not a power of 2
    /// - If the modulus is not NTT-friendly for dimension N
    pub fn new() -> Self {
        assert!(N.is_power_of_two(), "N must be a power of 2");

        let params = NttParams::<R, N>::new();
        let twiddles = NegacyclicTwiddles::<R, N>::new();
        let log_n = N.trailing_zeros() as usize;

        Self {
            params,
            twiddles,
            log_n,
        }
    }

    /// Returns the NTT dimension.
    #[inline]
    pub fn dimension(&self) -> usize {
        N
    }

    /// Returns the primitive 2N-th root of unity (ψ).
    #[inline]
    pub fn psi(&self) -> R {
        self.params.psi
    }

    /// Returns the N-th root of unity (ω = ψ²).
    #[inline]
    pub fn omega(&self) -> R {
        self.params.omega
    }

    // ========================================================================
    // Standard (Cyclic) NTT
    // ========================================================================

    /// Performs forward NTT using Cooley-Tukey radix-2 DIT algorithm.
    ///
    /// Transforms a polynomial from coefficient domain to NTT domain.
    ///
    /// # Arguments
    /// * `a` - Mutable slice of N ring elements (modified in-place)
    ///
    /// # Algorithm (Cooley-Tukey DIT)
    /// ```text
    /// Input: a[0..N] in natural order
    /// Output: â[0..N] in bit-reversed order
    ///
    /// for s = 0 to log2(N) - 1:
    ///     m = 2^(s+1)
    ///     ω_m = ω^(N/m)
    ///     for k = 0 to N-1 by m:
    ///         w = 1
    ///         for j = 0 to m/2 - 1:
    ///             t = w * a[k + j + m/2]
    ///             u = a[k + j]
    ///             a[k + j] = u + t
    ///             a[k + j + m/2] = u - t
    ///             w = w * ω_m
    /// ```
    pub fn forward(&self, a: &mut [R]) {
        assert_eq!(a.len(), N, "Input length must be N");

        // Bit-reversal permutation
        bit_reverse_permutation(a);

        // Cooley-Tukey butterflies
        for s in 0..self.log_n {
            let m = 1 << (s + 1); // Butterfly size
            let half_m = m / 2;

            // Get twiddle factors for this stage
            let omega_m = self.params.omega.pow((N as u64) / (m as u64));

            for k in (0..N).step_by(m) {
                let mut w = R::ONE;
                for j in 0..half_m {
                    let t = w * a[k + j + half_m];
                    let u = a[k + j];
                    a[k + j] = u + t;
                    a[k + j + half_m] = u - t;
                    w *= omega_m;
                }
            }
        }
    }

    /// Performs inverse NTT using Gentleman-Sande radix-2 DIF algorithm.
    ///
    /// Transforms a polynomial from NTT domain back to coefficient domain.
    ///
    /// # Arguments
    /// * `a` - Mutable slice of N ring elements (modified in-place)
    ///
    /// # Algorithm (Gentleman-Sande DIF)
    /// ```text
    /// Input: â[0..N] in bit-reversed order
    /// Output: a[0..N] in natural order
    ///
    /// for s = log2(N) - 1 down to 0:
    ///     m = 2^(s+1)
    ///     ω_m^(-1) = ω^(-N/m)
    ///     for k = 0 to N-1 by m:
    ///         w = 1
    ///         for j = 0 to m/2 - 1:
    ///             t = a[k + j]
    ///             u = a[k + j + m/2]
    ///             a[k + j] = t + u
    ///             a[k + j + m/2] = (t - u) * w
    ///             w = w * ω_m^(-1)
    /// ```
    pub fn inverse(&self, a: &mut [R]) {
        assert_eq!(a.len(), N, "Input length must be N");

        // Gentleman-Sande butterflies (reverse order of stages)
        for s in (0..self.log_n).rev() {
            let m = 1 << (s + 1);
            let half_m = m / 2;

            let omega_m_inv = self.params.omega_inv.pow((N as u64) / (m as u64));

            for k in (0..N).step_by(m) {
                let mut w = R::ONE;
                for j in 0..half_m {
                    let t = a[k + j];
                    let u = a[k + j + half_m];
                    a[k + j] = t + u;
                    a[k + j + half_m] = (t - u) * w;
                    w *= omega_m_inv;
                }
            }
        }

        // Bit-reversal permutation
        bit_reverse_permutation(a);

        // Scale by N^(-1)
        for elem in a.iter_mut() {
            *elem *= self.params.n_inv;
        }
    }

    // ========================================================================
    // Negacyclic NTT (for x^N + 1)
    // ========================================================================

    /// Performs forward negacyclic NTT for polynomial ring Z_q[x]/(x^N + 1).
    ///
    /// The negacyclic NTT computes:
    /// â[i] = Σ_{j=0}^{N-1} a[j] · ψ^j · ω^{ij}
    ///
    /// where ψ is a primitive 2N-th root of unity and ω = ψ² is a primitive
    /// N-th root of unity.
    ///
    /// # Arguments
    /// * `a` - Mutable slice of N ring elements (modified in-place)
    pub fn forward_negacyclic(&self, a: &mut [R]) {
        assert_eq!(a.len(), N, "Input length must be N");

        // Pre-multiply by powers of ψ
        for (i, elem) in a.iter_mut().enumerate() {
            *elem *= self.twiddles.psi_powers[i];
        }

        // Standard forward NTT
        self.forward(a);
    }

    /// Performs inverse negacyclic NTT for polynomial ring Z_q[x]/(x^N + 1).
    ///
    /// # Arguments
    /// * `a` - Mutable slice of N ring elements (modified in-place)
    pub fn inverse_negacyclic(&self, a: &mut [R]) {
        assert_eq!(a.len(), N, "Input length must be N");

        // Standard inverse NTT
        self.inverse(a);

        // Post-multiply by powers of ψ^(-1)
        for (i, elem) in a.iter_mut().enumerate() {
            *elem *= self.twiddles.psi_inv_powers[i];
        }
    }

    // ========================================================================
    // Polynomial Multiplication using NTT
    // ========================================================================

    /// Multiplies two polynomials using NTT.
    ///
    /// Computes c(x) = a(x) · b(x) in time O(N log N).
    ///
    /// # Arguments
    /// * `a` - First polynomial coefficients [a_0, a_1, ..., a_{N-1}]
    /// * `b` - Second polynomial coefficients [b_0, b_1, ..., b_{N-1}]
    ///
    /// # Returns
    /// Product polynomial coefficients [c_0, c_1, ..., c_{N-1}]
    ///
    /// # Note
    /// For standard (cyclic) convolution. For polynomial rings Z_q[x]/(x^N + 1),
    /// use `multiply_negacyclic` instead.
    pub fn multiply(&self, a: &[R], b: &[R]) -> Vec<R> {
        assert_eq!(a.len(), N, "First polynomial length must be N");
        assert_eq!(b.len(), N, "Second polynomial length must be N");

        let mut a_ntt = a.to_vec();
        let mut b_ntt = b.to_vec();

        // Forward NTT
        self.forward(&mut a_ntt);
        self.forward(&mut b_ntt);

        // Pointwise multiplication in NTT domain
        let mut c_ntt: Vec<R> = a_ntt
            .iter()
            .zip(b_ntt.iter())
            .map(|(&x, &y)| x * y)
            .collect();

        // Inverse NTT
        self.inverse(&mut c_ntt);

        c_ntt
    }

    /// Multiplies two polynomials in Z_q[x]/(x^N + 1) using negacyclic NTT.
    ///
    /// This computes the negacyclic convolution:
    /// c(x) = a(x) · b(x) mod (x^N + 1)
    ///
    /// # Arguments
    /// * `a` - First polynomial coefficients [a_0, a_1, ..., a_{N-1}]
    /// * `b` - Second polynomial coefficients [b_0, b_1, ..., b_{N-1}]
    ///
    /// # Returns
    /// Product polynomial coefficients [c_0, c_1, ..., c_{N-1}] where
    /// c(x) ≡ a(x) · b(x) (mod x^N + 1)
    pub fn multiply_negacyclic(&self, a: &[R], b: &[R]) -> Vec<R> {
        assert_eq!(a.len(), N, "First polynomial length must be N");
        assert_eq!(b.len(), N, "Second polynomial length must be N");

        let mut a_ntt = a.to_vec();
        let mut b_ntt = b.to_vec();

        // Forward negacyclic NTT
        self.forward_negacyclic(&mut a_ntt);
        self.forward_negacyclic(&mut b_ntt);

        // Pointwise multiplication in NTT domain
        let mut c_ntt: Vec<R> = a_ntt
            .iter()
            .zip(b_ntt.iter())
            .map(|(&x, &y)| x * y)
            .collect();

        // Inverse negacyclic NTT
        self.inverse_negacyclic(&mut c_ntt);

        c_ntt
    }

    /// Computes pointwise multiplication of two polynomials in NTT domain.
    ///
    /// Both inputs must already be in NTT representation.
    #[inline]
    pub fn pointwise_mul(&self, a_ntt: &[R], b_ntt: &[R]) -> Vec<R> {
        assert_eq!(a_ntt.len(), N);
        assert_eq!(b_ntt.len(), N);

        a_ntt
            .iter()
            .zip(b_ntt.iter())
            .map(|(&x, &y)| x * y)
            .collect()
    }

    /// Computes pointwise multiplication and stores result in-place.
    #[inline]
    pub fn pointwise_mul_assign(&self, a_ntt: &mut [R], b_ntt: &[R]) {
        assert_eq!(a_ntt.len(), N);
        assert_eq!(b_ntt.len(), N);

        for (a, &b) in a_ntt.iter_mut().zip(b_ntt.iter()) {
            *a *= b;
        }
    }
}

impl<R: Ring, const N: usize> Default for NttOperator<R, N> {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Optimized NTT with precomputed per-stage twiddles
// ============================================================================

/// Optimized NTT operator with fully precomputed per-stage twiddle factors.
///
/// This version avoids computing powers of ω during the transform by
/// precomputing all required twiddle factors.
#[derive(Debug, Clone)]
pub struct NttOperatorOptimized<R: Ring, const N: usize> {
    /// Forward twiddle factors for each stage
    /// forward_twiddles[s][j] = ω^(j * N / 2^(s+1))
    forward_twiddles: Vec<Vec<R>>,

    /// Inverse twiddle factors for each stage
    inverse_twiddles: Vec<Vec<R>>,

    /// Powers of ψ for negacyclic pre-processing
    psi_powers: Vec<R>,

    /// Powers of ψ^(-1) for negacyclic post-processing
    psi_inv_powers: Vec<R>,

    /// N^(-1) for scaling
    n_inv: R,

    /// log2(N)
    log_n: usize,
}

impl<R: Ring, const N: usize> NttOperatorOptimized<R, N> {
    /// Creates an optimized NTT operator with fully precomputed twiddle factors.
    pub fn new() -> Self {
        let params = NttParams::<R, N>::new();
        let log_n = N.trailing_zeros() as usize;

        // Precompute forward twiddles for each stage
        let mut forward_twiddles = Vec::with_capacity(log_n);
        for s in 0..log_n {
            let m = 1 << (s + 1);
            let half_m = m / 2;
            let omega_m = params.omega.pow((N as u64) / (m as u64));

            let mut stage = Vec::with_capacity(half_m);
            let mut w = R::ONE;
            for _ in 0..half_m {
                stage.push(w);
                w *= omega_m;
            }
            forward_twiddles.push(stage);
        }

        // Precompute inverse twiddles for each stage
        let mut inverse_twiddles = Vec::with_capacity(log_n);
        for s in (0..log_n).rev() {
            let m = 1 << (s + 1);
            let half_m = m / 2;
            let omega_m_inv = params.omega_inv.pow((N as u64) / (m as u64));

            let mut stage = Vec::with_capacity(half_m);
            let mut w = R::ONE;
            for _ in 0..half_m {
                stage.push(w);
                w *= omega_m_inv;
            }
            inverse_twiddles.push(stage);
        }

        // Precompute ψ powers
        let mut psi_powers = Vec::with_capacity(N);
        let mut psi_inv_powers = Vec::with_capacity(N);
        let mut psi_pow = R::ONE;
        let mut psi_inv_pow = R::ONE;
        for _ in 0..N {
            psi_powers.push(psi_pow);
            psi_inv_powers.push(psi_inv_pow);
            psi_pow *= params.psi;
            psi_inv_pow *= params.psi_inv;
        }

        Self {
            forward_twiddles,
            inverse_twiddles,
            psi_powers,
            psi_inv_powers,
            n_inv: params.n_inv,
            log_n,
        }
    }

    /// Forward NTT with precomputed twiddles.
    pub fn forward(&self, a: &mut [R]) {
        assert_eq!(a.len(), N);
        bit_reverse_permutation(a);

        for s in 0..self.log_n {
            let m = 1 << (s + 1);
            let half_m = m / 2;

            for k in (0..N).step_by(m) {
                for j in 0..half_m {
                    let w = self.forward_twiddles[s][j];
                    let t = w * a[k + j + half_m];
                    let u = a[k + j];
                    a[k + j] = u + t;
                    a[k + j + half_m] = u - t;
                }
            }
        }
    }

    /// Inverse NTT with precomputed twiddles.
    pub fn inverse(&self, a: &mut [R]) {
        assert_eq!(a.len(), N);

        for (stage_idx, s) in (0..self.log_n).rev().enumerate() {
            let m = 1 << (s + 1);
            let half_m = m / 2;

            for k in (0..N).step_by(m) {
                for j in 0..half_m {
                    let w = self.inverse_twiddles[stage_idx][j];
                    let t = a[k + j];
                    let u = a[k + j + half_m];
                    a[k + j] = t + u;
                    a[k + j + half_m] = (t - u) * w;
                }
            }
        }

        bit_reverse_permutation(a);

        for elem in a.iter_mut() {
            *elem *= self.n_inv;
        }
    }

    /// Forward negacyclic NTT.
    pub fn forward_negacyclic(&self, a: &mut [R]) {
        assert_eq!(a.len(), N);
        for (i, elem) in a.iter_mut().enumerate() {
            *elem *= self.psi_powers[i];
        }
        self.forward(a);
    }

    /// Inverse negacyclic NTT.
    pub fn inverse_negacyclic(&self, a: &mut [R]) {
        assert_eq!(a.len(), N);
        self.inverse(a);
        for (i, elem) in a.iter_mut().enumerate() {
            *elem *= self.psi_inv_powers[i];
        }
    }

    /// Negacyclic polynomial multiplication.
    pub fn multiply_negacyclic(&self, a: &[R], b: &[R]) -> Vec<R> {
        let mut a_ntt = a.to_vec();
        let mut b_ntt = b.to_vec();

        self.forward_negacyclic(&mut a_ntt);
        self.forward_negacyclic(&mut b_ntt);

        let mut c_ntt: Vec<R> = a_ntt
            .iter()
            .zip(b_ntt.iter())
            .map(|(&x, &y)| x * y)
            .collect();

        self.inverse_negacyclic(&mut c_ntt);
        c_ntt
    }
}

impl<R: Ring, const N: usize> Default for NttOperatorOptimized<R, N> {
    fn default() -> Self {
        Self::new()
    }
}
