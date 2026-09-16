//! Instance domain: the concrete algebra the protocols run over (L5).
//!
//! Protocol modules never hand-roll a ring — they name the instance here:
//!
//! - [`ring`]: the `Z_{2^32}[X]/(X^64+1)` ring, its helpers and the shared
//!   ring-vector norms / power-of-two constants;
//! - [`r1cs`]: the toy R1CS layer (squaring gates) with the parallel gate
//!   traversal used by the opening/folding protocols.

pub mod r1cs;
pub mod ring;
