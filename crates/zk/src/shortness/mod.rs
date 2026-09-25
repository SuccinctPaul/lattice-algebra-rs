//! Shortness domain: norm-bound / approximate-shortness arguments (L5).
//!
//! - [`balanced`]: the digit-based projection argument — exact balanced
//!   `2^γ` splits with digit gates and an exact commitment link;
//! - [`gadget`]: the slack-based flavor (gadget split + approximate linear
//!   check with a provable slack bound), used by batched openings;
//! - [`projection`]: the `l2` flavor — GHL-style Johnson–Lindenstrauss
//!   projection with an explicit certified-bound gap (LaBRADOR's
//!   shortness layer, simplified ±1-entry variant).
//! - [`fold`]: pairwise commitment folding with JL shortness
//!   certification — the base step of the amortized-compression route
//!   (rows 19/24);
//! - [`self_ip`]: the self-inner-product argument — Serval's divide-and-conquer
//!   proof that `ct(⟨s,σ(s)⟩)` equals a claimed integer, producing exactly the
//!   quantity [`exact_l2`] then gates;
//! - [`exact_l2`]: the slack-free **exact integer** squared-Euclidean gate
//!   (Akita §6.2), which is a different instrument from the JL argument
//!   above and does not use it;
//! - [`tensor_fold`]: the shared split-and-fold engine — tensor-structured
//!   public weights, the linear / bilinear-round recursions, Theorem-shaped
//!   norm growth and an invertible challenge pool — generic over the scalar
//!   ring and the ring degree;
//! - [`committed_norm`]: the composed argument — the four constraint families
//!   above folded by one challenge sequence over a
//!   [`crate::pcs::leveled::LeveledAjtai`] commitment.

pub mod balanced;
pub mod committed_norm;
pub mod exact_l2;
pub mod fold;
pub mod gadget;
pub mod projection;
pub mod self_ip;
pub mod tensor_fold;
