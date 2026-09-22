//! Polynomial commitment scheme (Z7): a Greyhound-style PCS over the Z1
//! ring — commit to a polynomial `f`, later open it at an evaluation point
//! `x` with a proof for `y = f(x)`.
//!
//! This is the first *committed* evaluation in the crate: the sumcheck
//! domain (Z3) runs over an explicitly public table, so nothing there
//! commits to the evaluated object. The scheme follows Nguyen–Seiler,
//! *Greyhound: Fast Polynomial Commitments from Lattices* (CRYPTO 2024,
//! eprint 2024/1293): a two-layer Ajtai commitment (`commitment` domain)
//! with the √N split evaluation protocol. What is **not** implemented yet
//! is the LaBRADOR recursion that compresses the O(√N) core proof down to
//! polylog(N) — the proof here stays at the core size.
//!
//! ```text
//! f ∈ R^{N}  (N = m·r ring-element coefficients, f = Σᵢ X^{im}·fᵢ)
//!   sᵢ = G_m⁻¹(fᵢ)   binary digits          ‖sᵢ‖∞ = 1
//!   tᵢ = A·sᵢ        inner Ajtai
//!   û  = B·(G_n⁻¹(t₁) ∥ … ∥ G_n⁻¹(t_r))    outer Ajtai — the commitment
//! ```
//!
//! Layering: `commitment → pcs` (the scheme is a direct consumer of the
//! Ajtai keys, parallel to `opening`).
//!
//! # Instance parameters
//!
//! All committed coefficients are ring elements of
//! `R_q = Z_q[X]/(X^256 + 1)` with the Z1 prime `q = 8380417`; the toy
//! dimensions below keep tests and examples interactive. They must be
//! re-sized (and validated with the Core-SVP estimator, see
//! `algebra::security`) before any security claim.
//!
//! [`packing`] carries the σ-automorphism identity
//! `const(g·σ(h)) = Σ g_k·h_k` (`σ: X ↦ X^{−1}`) with the scalar packing
//! helpers — the factor-`d` removal for scalar-coefficient polynomials.
//! [`mle`] carries the tall-key linear-commitment mode with exact
//! arbitrary-weight-claim verification (the transparent read-out the
//! cross-point batching composes against).

pub mod batched;
pub mod gadget;
pub mod greyhound;
pub mod mle;
pub mod packing;

pub use batched::{open_batch, verify_batch, BatchedOpeningProof, L1_PER_POLY, MAX_BATCH};
pub use greyhound::{
    commit, commit_packed, open, open_packed, verify, verify_packed, GreyhoundKey, OpeningProof,
    PcsError, PolyCommitment,
};
pub use mle::{certify_l2, claim, commit_mle, witness_of, MleCommitment, MleError, MleKey};

/// Ring degree `d` of one committed coefficient (the Z1 cyclotomic).
pub const DIM: usize = 256;

/// Gadget digits per scalar coefficient: `⌈log₂ q⌉` for `q = 8380417`.
pub const DELTA: usize = 23;

/// Ajtai output width (the paper's `n`): rows of the keys A, B and D.
pub const N_ROWS: usize = 4;

/// Column height `m`: ring-element coefficients per block `fᵢ`.
pub const M_COLS: usize = 8;

/// Number of blocks `r` (the √ decomposition: `m ≈ r ≈ √N`).
pub const R_COLS: usize = 8;

/// Committed polynomial length in ring-element coefficients: `N = m·r`.
pub const N_DEG: usize = M_COLS * R_COLS;

/// Verifier response bound: `‖z‖∞ ≤ r·d` for `z = Σ cᵢ·sᵢ` with ternary
/// `cᵢ` (each product contributes at most `min(‖c‖₁·‖s‖∞, …) ≤ d`).
pub const B_Z: u64 = R_COLS as u64 * DIM as u64;

/// Scalar coefficient ring of [`RingElt`] (the ML-DSA prime, same ring as
/// the `commitment`/`sigma` domains).
pub type Z1Coeff = crate::commitment::ajtai::Z1Ring;

/// One committed coefficient of `f`: an element of
/// `R_q = Z_q[X]/(X^256 + 1)`.
pub type RingElt = algebra::ring::poly_ring::PolyRing<Z1Coeff, DIM>;
