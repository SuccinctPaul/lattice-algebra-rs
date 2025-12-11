//! Number Theoretic Transform (NTT) Module
//!
//! This module provides efficient polynomial multiplication over finite fields
//! using the Number Theoretic Transform, which is the finite field analog of FFT.
//!
//! # Overview
//!
//! NTT is essential for lattice-based cryptography because it enables O(n log n)
//! polynomial multiplication in the ring Z_q[x]/(x^n + 1).
//!
//! # Features
//!
//! - Cooley-Tukey radix-2 DIT (Decimation-In-Time) NTT
//! - Gentleman-Sande radix-2 DIF (Decimation-In-Frequency) INTT
//! - Negacyclic NTT for polynomial rings Z_q[x]/(x^n + 1)
//! - Precomputed twiddle factors for performance
//! - Support for any NTT-friendly prime modulus
//!
//! # Example
//!
//! ```ignore
//! use lattice_algebra_rs::ntt::NttOperator;
//! use lattice_algebra_rs::ring::zq::Zq;
//!
//! // Kyber-like parameters: q = 3329, n = 256
//! type Zq3329 = Zq<3329>;
//! let ntt = NttOperator::<Zq3329, 256>::new();
//!
//! let mut a = vec![Zq3329::new(1); 256];
//! ntt.forward(&mut a);  // Transform to NTT domain
//! ntt.inverse(&mut a);  // Transform back
//! ```

mod ntt_core;
mod params;
mod twiddle;

pub use ntt_core::NttOperator;
pub use params::{is_ntt_friendly, primitive_root, NttParams};
pub use twiddle::TwiddleFactors;

#[cfg(test)]
mod tests;
