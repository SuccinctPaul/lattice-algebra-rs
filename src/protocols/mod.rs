//! Protocol components (L5): commitments, Σ-protocols and sumcheck/inner
//! product arguments built on the module-lattice layer, serving the lattice
//! zkSNARK roadmap.
//!
//! Implemented:
//! - [`commitment`] (Z1): Ajtai/SIS commitments `C = A·s` with short `s`
//!   (binding from Module-SIS);
//! - [`sigma`] (Z1): Lyubashevsky-style approximate-knowledge Σ-protocol,
//!   FS-NIZK with a public relaxed-knowledge extractor;
//! - [`z2_ring`] / [`z2`] (Z2): the `Z_{2^32}[X]/(X^64+1)` instance,
//!   batched-opening R1CS proofs and gadget decomposition;
//! - [`sumcheck`] (Z3): multilinear sumcheck over any commutative ring;
//! - [`ipa`] (Z3): gadget-IPA — inner-product arguments on Ajtai-committed
//!   vectors with an approximate (slack-bounded) opening mode.
//!
//! Zero-knowledge status: Z1's rejection-sampled protocol is honest-verifier
//! zero-knowledge (HVZK); Z2/Z3 proofs-of-knowledge are transparent (like
//! LaBRADOR); full ZK via blinding is deferred to Z4.

pub mod commitment;
pub mod fold;
pub mod ipa;
pub mod sigma;
pub mod sumcheck;
pub mod z2;
pub mod z2_ring;
