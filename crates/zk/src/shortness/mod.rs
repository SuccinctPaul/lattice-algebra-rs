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

pub mod balanced;
pub mod fold;
pub mod gadget;
pub mod projection;
