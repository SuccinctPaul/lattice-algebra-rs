//! Folding domain: fold two committed instances into one (L5).
//!
//! Two complementary lines, sharing the instance and commitment domains:
//!
//! - [`nova`]: Nova-style relaxed-R1CS folding (homomorphic commitment
//!   updates, cross-term absorption, IVC chains);
//! - [`latticefold`]: LatticeFold-style folding — small-norm fold challenge,
//!   exact balanced b-bit batch decomposition, splitting query.

pub mod latticefold;
pub mod nova;
