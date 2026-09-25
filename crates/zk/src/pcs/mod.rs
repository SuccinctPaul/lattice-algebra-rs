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
//! [`api`] is the scheme-facing abstraction — [`Pcs`] for point openings,
//! [`BatchPcs`] for shared-point batches, [`WeightPcs`] for arbitrary
//! weight tables — that a scheme under `examples/` assembles against so the
//! crate keeps `src` = capabilities and example = scheme.
//! [`packing`] carries the σ-automorphism identity
//! `const(g·σ(h)) = Σ g_k·h_k` (`σ: X ↦ X^{−1}`) with the scalar packing
//! helpers — the factor-`d` removal for scalar-coefficient polynomials.
//! [`mle`] carries the tall-key linear-commitment mode: exact verification of
//! **arbitrary** weight-table claims `y = ⟨w, F⟩` (power tables, `eq`
//! tensors, range-check functionals), a Σ opening per claim, and
//! [`batch_verify`] folding `k` such claims into one opening. This is the
//! cross-point/cross-table shape the √N split cannot express, so the
//! sumcheck line composes against it.

pub mod api;
pub mod batched;
pub mod binary_r1cs;
pub mod digit_pack;
pub mod dotproduct;
pub mod fold_geom;
pub mod gadget;
pub mod greyhound;
pub mod jl_compose;
pub mod key;
pub mod leveled;
pub mod masking;
pub mod mixed;
pub mod mle;
pub mod monomial_pok;
pub mod nested;
pub mod norm_route;
pub mod packing;
pub mod powers_srs;
pub mod prisis;
pub mod projection;
pub mod ring_reduce;
pub mod rotation;
pub mod slap_tree;
pub mod setup_stream;
pub mod switching;
pub mod trapdoor;
pub mod tree_commit;
pub mod tree_eval;
pub mod tree_fin;
pub mod tree_fold;

pub use api::{
    BatchOpening, BatchPcs, PackedGreyhound, Pcs, WeightPcs, WeightPcsExt,
};
pub use batched::{open_batch, verify_batch, BatchedOpeningProof, L1_PER_POLY, MAX_BATCH};
pub use dotproduct::{
    aggregation_count, prove_core, verify_core, verify_core_report, AggregatedCoeffs,
    ChallengeError, ChallengeSpace, CoreChallenger, CoreError, CoreMessage, CoreParams, CoreSetup,
    CtFn, Decomposition, DigitError, NormBounds, Projection, QuadFn, Relation, RelationError,
    PROJECTION_ROWS,
};
pub use greyhound::{
    commit, commit_packed, open, open_packed, verify, verify_packed, GreyhoundKey, OpeningProof,
    PcsError, PolyCommitment,
};
pub use jl_compose::{
    extractor_slack_sq, identity_mat, kron, projection_gate_ok, tuned_ternary, SquaredRatioWindow,
    StructuredProjection, SINGLE_STAGE, TWO_STAGE,
};
pub use key::{apply_blockwise, KeyShapeError, RingMatrixKey};
pub use mixed::{BlockMat, MixedError};
pub use mle::{
    batch_verify, certify_l2, claim, combined_claim, commit_mle, open_claims, open_mle_proof,
    verify_mle_proof, witness_of, MleCommitment, MleError, MleKey, MleOpenProof, WeightClaim,
    MASK_BOUND,
};
pub use nested::{NestedError, NestedGadget, TensorGadget};
pub use projection::{
    const_term, from_coeffs, gamma_stack, sigma_matrix, sigma_pairing_vec, to_coeffs, FieldMat,
    FieldShapeError,
};
pub use rotation::{
    evaluation_vector, expand_matrix, fold_matrix, fold_row, identity_field_mat,
    multiplication_matrix, one_poly, powers, rot, zip_entries, RowTensor, TensorShapeError,
};

pub use trapdoor::{
    bound_of_matrix, check_gadget_capacity, gadget_apply, gadget_matrix, identity_matrix, matmul,
    preimage_ok, preimage_random_with_trapdoor, preimage_with_trapdoor, scalar_elt, short_matrix,
    trapdoor_relation, TrapError, TrapdoorKey, UnitMatrix,
};

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
