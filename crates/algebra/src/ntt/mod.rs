//! Number Theoretic Transform (NTT) Module
//!
//! This module provides efficient polynomial multiplication over finite fields
//! using the Number Theoretic Transform, which is the finite field analog of FFT.
//!
//! # Overview
//!
//! NTT is essential for lattice-based cryptography because it enables O(n log n)
//! polynomial multiplication in the ring ``Z_q[x]/(x^n + 1)``.
//!
//! # Features
//!
//! - Cooley-Tukey radix-2 DIT (Decimation-In-Time) NTT
//! - Gentleman-Sande radix-2 DIF (Decimation-In-Frequency) INTT
//! - Negacyclic NTT for polynomial rings `Z_q[x]/(x^n + 1)`
//! - Precomputed twiddle factors for performance
//! - Support for any NTT-friendly prime modulus
//!
//! # Example
//!
//! ```rust
//! use algebra::ntt::NttOperator;
//! use algebra::ring::zq::Zq;
//!
//! // Dilithium parameters: q = 8380417, n = 256 (q ≡ 1 mod 2n)
//! type ZqD = Zq<8380417>;
//! let ntt = NttOperator::<ZqD, 256>::new();
//!
//! let mut a = vec![ZqD::new(1); 256];
//! let before = a.clone();
//! ntt.forward(&mut a); // Transform to the NTT domain
//! ntt.inverse(&mut a); // Transform back: forward ∘ inverse = id
//! assert_eq!(a, before);
//! ```
//!
//! Note that `Zq<3329>` (ML-KEM) is *not* eligible for this generic
//! negacyclic NTT at `n = 256`: its 2-adicity is 7 < 9, because FIPS 203
//! instead specifies an incomplete, layered NTT. Gate dimension choices
//! with [`is_ntt_friendly`].

mod ntt_core;
mod ntt_domain;
mod params;
mod twiddle;

pub use ntt_core::{NttOperator, NttOperatorOptimized};
pub use ntt_domain::NttDomain;
pub use params::{find_primitive_root, is_ntt_friendly, prime_factors, primitive_root, NttParams};
pub use twiddle::TwiddleFactors;

#[cfg(test)]
mod tests;
