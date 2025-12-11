//! Core NTT implementation using Cooley-Tukey and Gentleman-Sande algorithms.
//!
//! # Algorithm Overview
//!
//! ## Forward NTT (Cooley-Tukey, DIT - Decimation in Time)
//! ```text
//! Input: coefficients a[0..n-1] in standard order
//! Output: NTT(a) in bit-reversed order
//!
//! for m in [2, 4, 8, ..., n]:
//!     ωm = ω^(n/m)  // m-th root of unity
//!     for k in [0, m, 2m, ..., n-m]:
//!         ω = 1
//!         for j in [0, 1, ..., m/2-1]:
//!             t = ω * a[k + j + m/2]
//!             u = a[k + j]
//!             a[k + j] = u + t
//!             a[k + j + m/2] = u - t
//!             ω = ω * ωm
//! ```
//!
//! ## Inverse NTT (Gentleman-Sande, DIF - Decimation in Frequency)
//! ```text
//! Input: NTT(a) in bit-reversed order
//! Output: coefficients a[0..n-1] in standard order
//!
//! for m in [n, n/2, ..., 2]:
//!     ωm = ω^(-n/m)  // m-th root of unity inverse
//!     for k in [0, m, 2m, ..., n-m]:
//!         ω = 1
//!         for j in [0, 1, ..., m/2-1]:
//!             t = a[k + j]
//!             u = a[k + j + m/2]
//!             a[k + j] = t + u
//!             a[k + j + m/2] = ω * (t - u)
//!             ω = ω * ωm
//! Scale by n^(-1)
//! ```

use super::traits::NttConfig;
use super::utils::{bit_reverse_copy, mod_exp, mod_inverse};

/// Precomputed NTT table containing twiddle factors.
///
/// Twiddle factors are powers of the root of unity used in butterfly operations.
/// Precomputing them avoids repeated modular exponentiation during NTT.
#[derive(Debug, Clone)]
pub struct NttTable {
    /// The modulus q
    pub q: u64,
    /// Polynomial degree n
    pub n: usize,
    /// log2(n)
    pub log_n: usize,
    /// Twiddle factors for forward NTT
    /// For Cooley-Tukey: powers of ω (n-th root of unity)
    pub zetas: Vec<u64>,
    /// Twiddle factors for inverse NTT
    pub zetas_inv: Vec<u64>,
    /// n^(-1) mod q for final scaling
    pub n_inv: u64,
    /// The n-th root of unity
    pub omega: u64,
    /// The inverse of omega
    pub omega_inv: u64,
}

impl NttTable {
    /// Creates a new NTT table from an NttConfig.
    pub fn new<C: NttConfig>() -> Self {
        let q = C::Q;
        let n = C::N;
        let log_n = C::LOG_N;
        let omega = C::ROOT_OF_UNITY;
        let omega_inv = C::ROOT_OF_UNITY_INV;
        let n_inv = C::N_INV;

        // Compute zetas: powers of ω for each layer
        // Standard Cooley-Tukey needs ω^0, ω^1, ..., ω^{n-1}
        let mut zetas = vec![0u64; n];
        let mut zetas_inv = vec![0u64; n];

        for i in 0..n {
            zetas[i] = mod_exp(omega, i as u64, q);
            zetas_inv[i] = mod_exp(omega_inv, i as u64, q);
        }

        Self {
            q,
            n,
            log_n,
            zetas,
            zetas_inv,
            n_inv,
            omega,
            omega_inv,
        }
    }

    /// Creates a new NTT table with custom parameters.
    ///
    /// # Arguments
    /// * `q` - The modulus
    /// * `n` - Polynomial degree (must be power of 2)
    /// * `omega` - Primitive n-th root of unity (ω^n ≡ 1 mod q)
    pub fn with_params(q: u64, n: usize, omega: u64) -> Option<Self> {
        if n == 0 || (n & (n - 1)) != 0 {
            return None; // n must be power of 2
        }

        // Verify omega is an n-th root of unity
        if mod_exp(omega, n as u64, q) != 1 {
            return None;
        }

        let log_n = n.trailing_zeros() as usize;

        // Compute omega inverse
        let omega_inv = mod_inverse(omega, q)?;
        let n_inv = mod_inverse(n as u64, q)?;

        // Compute zetas: ω^0, ω^1, ..., ω^{n-1}
        let mut zetas = vec![0u64; n];
        let mut zetas_inv = vec![0u64; n];

        for i in 0..n {
            zetas[i] = mod_exp(omega, i as u64, q);
            zetas_inv[i] = mod_exp(omega_inv, i as u64, q);
        }

        Some(Self {
            q,
            n,
            log_n,
            zetas,
            zetas_inv,
            n_inv,
            omega,
            omega_inv,
        })
    }
}

/// Bit-reverse helper function
fn bit_reverse(i: usize, log_n: usize) -> usize {
    i.reverse_bits() >> (usize::BITS as usize - log_n)
}

/// NTT operator with precomputed tables for efficient polynomial operations.
#[derive(Debug, Clone)]
pub struct NttOperator {
    table: NttTable,
}

impl NttOperator {
    /// Creates a new NTT operator from an NttConfig.
    pub fn new<C: NttConfig>() -> Self {
        Self {
            table: NttTable::new::<C>(),
        }
    }

    /// Creates a new NTT operator with custom parameters.
    pub fn with_params(q: u64, n: usize, root: u64) -> Option<Self> {
        Some(Self {
            table: NttTable::with_params(q, n, root)?,
        })
    }

    /// Returns the modulus q.
    #[inline]
    pub fn q(&self) -> u64 {
        self.table.q
    }

    /// Returns the polynomial degree n.
    #[inline]
    pub fn n(&self) -> usize {
        self.table.n
    }

    /// Modular addition: (a + b) mod q
    #[inline]
    fn mod_add(&self, a: u64, b: u64) -> u64 {
        let sum = a + b;
        if sum >= self.table.q {
            sum - self.table.q
        } else {
            sum
        }
    }

    /// Modular subtraction: (a - b) mod q
    #[inline]
    fn mod_sub(&self, a: u64, b: u64) -> u64 {
        if a >= b {
            a - b
        } else {
            self.table.q - (b - a)
        }
    }

    /// Modular multiplication: (a * b) mod q
    #[inline]
    fn mod_mul(&self, a: u64, b: u64) -> u64 {
        ((a as u128 * b as u128) % self.table.q as u128) as u64
    }

    /// Forward NTT using Cooley-Tukey (DIT) algorithm.
    ///
    /// Computes the NTT of the input polynomial in-place.
    /// Uses standard Cooley-Tukey with bit-reversal permutation.
    ///
    /// # Arguments
    /// * `a` - The coefficient array (must have length n)
    pub fn forward(&self, a: &mut [u64]) {
        let n = self.table.n;
        assert_eq!(a.len(), n, "Input length must be {}", n);

        // Bit-reverse the input
        bit_reverse_copy(a, self.table.log_n);

        // Cooley-Tukey iterative NTT
        let mut len = 2;
        while len <= n {
            // ω_len = ω^{n/len} is a primitive len-th root of unity
            let step = n / len;

            for start in (0..n).step_by(len) {
                let mut w = 1u64; // ω^0 = 1
                for j in 0..len / 2 {
                    let u = a[start + j];
                    let v = self.mod_mul(a[start + j + len / 2], w);

                    a[start + j] = self.mod_add(u, v);
                    a[start + j + len / 2] = self.mod_sub(u, v);

                    // w *= ω^step = ω_len
                    w = self.mod_mul(w, self.table.zetas[step]);
                }
            }
            len *= 2;
        }
    }

    /// Inverse NTT using Cooley-Tukey with inverse roots.
    ///
    /// Computes the inverse NTT of the input in-place.
    ///
    /// # Arguments
    /// * `a` - The NTT coefficient array (must have length n)
    pub fn inverse(&self, a: &mut [u64]) {
        let n = self.table.n;
        assert_eq!(a.len(), n, "Input length must be {}", n);

        // Bit-reverse the input
        bit_reverse_copy(a, self.table.log_n);

        // Cooley-Tukey with inverse roots
        let mut len = 2;
        while len <= n {
            let step = n / len;

            for start in (0..n).step_by(len) {
                let mut w = 1u64;
                for j in 0..len / 2 {
                    let u = a[start + j];
                    let v = self.mod_mul(a[start + j + len / 2], w);

                    a[start + j] = self.mod_add(u, v);
                    a[start + j + len / 2] = self.mod_sub(u, v);

                    w = self.mod_mul(w, self.table.zetas_inv[step]);
                }
            }
            len *= 2;
        }

        // Scale by n^(-1)
        for x in a.iter_mut() {
            *x = self.mod_mul(*x, self.table.n_inv);
        }
    }

    /// Forward Negacyclic NTT for polynomial ring Z_q[x]/(x^n + 1).
    ///
    /// Requires a 2n-th root of unity ψ such that ψ^n = -1 (mod q).
    /// This transforms the negacyclic convolution into pointwise multiplication.
    ///
    /// # Arguments
    /// * `a` - The coefficient array (must have length n)
    /// * `psi` - Primitive 2n-th root of unity (ψ^n ≡ -1 mod q)
    pub fn forward_negacyclic_with_psi(&self, a: &mut [u64], psi: u64) {
        let n = self.table.n;
        assert_eq!(a.len(), n, "Input length must be {}", n);

        // Pre-multiply: a[i] *= ψ^i
        let mut psi_power = 1u64;
        for i in 0..n {
            a[i] = self.mod_mul(a[i], psi_power);
            psi_power = self.mod_mul(psi_power, psi);
        }

        // Standard NTT (uses ω = ψ^2 as n-th root of unity)
        self.forward(a);
    }

    /// Inverse Negacyclic NTT for polynomial ring Z_q[x]/(x^n + 1).
    ///
    /// # Arguments
    /// * `a` - The NTT coefficient array (must have length n)
    /// * `psi_inv` - Inverse of the 2n-th root of unity
    pub fn inverse_negacyclic_with_psi(&self, a: &mut [u64], psi_inv: u64) {
        let n = self.table.n;

        // Standard inverse NTT
        self.inverse(a);

        // Post-multiply: a[i] *= ψ^{-i}
        let mut psi_inv_power = 1u64;
        for i in 0..n {
            a[i] = self.mod_mul(a[i], psi_inv_power);
            psi_inv_power = self.mod_mul(psi_inv_power, psi_inv);
        }
    }

    /// Pointwise multiplication in NTT domain.
    ///
    /// After NTT, polynomial multiplication becomes pointwise multiplication.
    ///
    /// # Arguments
    /// * `a` - First NTT polynomial (modified in-place to contain result)
    /// * `b` - Second NTT polynomial
    pub fn pointwise_mul(&self, a: &mut [u64], b: &[u64]) {
        assert_eq!(a.len(), b.len());
        for i in 0..a.len() {
            a[i] = self.mod_mul(a[i], b[i]);
        }
    }

    /// Polynomial multiplication using NTT.
    ///
    /// Computes a * b mod (x^n + 1) using negacyclic NTT.
    ///
    /// # Arguments
    /// * `a` - First polynomial coefficients
    /// * `b` - Second polynomial coefficients
    ///
    /// # Returns
    /// Product polynomial coefficients
    pub fn multiply(&self, a: &[u64], b: &[u64]) -> Vec<u64> {
        let n = self.table.n;
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);

        // Copy and transform
        let mut a_ntt = a.to_vec();
        let mut b_ntt = b.to_vec();

        self.forward(&mut a_ntt);
        self.forward(&mut b_ntt);

        // Pointwise multiply
        self.pointwise_mul(&mut a_ntt, &b_ntt);

        // Inverse NTT
        self.inverse(&mut a_ntt);

        a_ntt
    }

    /// Polynomial multiplication modulo (x^n + 1) using negacyclic NTT.
    ///
    /// Requires that q ≡ 1 (mod 2n) so that a 2n-th root of unity exists.
    ///
    /// # Arguments
    /// * `a` - First polynomial coefficients
    /// * `b` - Second polynomial coefficients
    /// * `psi` - Primitive 2n-th root of unity
    ///
    /// # Returns
    /// Product polynomial coefficients modulo (x^n + 1)
    pub fn multiply_negacyclic(&self, a: &[u64], b: &[u64], psi: u64) -> Vec<u64> {
        let n = self.table.n;
        assert_eq!(a.len(), n);
        assert_eq!(b.len(), n);

        let psi_inv = mod_inverse(psi, self.table.q).expect("psi must be invertible");

        let mut a_ntt = a.to_vec();
        let mut b_ntt = b.to_vec();

        self.forward_negacyclic_with_psi(&mut a_ntt, psi);
        self.forward_negacyclic_with_psi(&mut b_ntt, psi);

        self.pointwise_mul(&mut a_ntt, &b_ntt);

        self.inverse_negacyclic_with_psi(&mut a_ntt, psi_inv);

        a_ntt
    }
}

