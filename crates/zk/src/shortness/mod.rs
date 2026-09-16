//! Shortness domain: norm-bound / approximate-shortness arguments (L5).
//!
//! - [`balanced`]: the digit-based projection argument — exact balanced
//!   `2^γ` splits with digit gates and an exact commitment link;
//! - [`gadget`]: the slack-based flavor (gadget split + approximate linear
//!   check with a provable slack bound), used by batched openings.

pub mod balanced;
pub mod gadget;
