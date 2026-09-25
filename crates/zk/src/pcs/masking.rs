//! Sublinear masking for **hiding** openings (Z7: evaluation hiding).
//!
//! A linear-commitment PCS proves claims `y = ⟨w, F⟩` against a commitment.
//! Proving them *in the open* leaks the per-claim values: nothing in
//! [`crate::pcs::mle`] or [`crate::pcs::greyhound`] stops a verifier who holds
//! the transcript from reading the claimed functional off the messages. This
//! module is that missing capability — it turns a batch of linear claims into
//! a transcript that is **simulatable without the witness**, at a masking cost
//! that is sublinear in the committed size.
//!
//! The construction is the one Hwang–Lee–Seo–Song give for Jindo (*Jindo:
//! Practical Lattice-Based Polynomial Commitments for Client-Side Proving*,
//! eprint 2026/044, §2.4 and §4.3, Figs. 5–7). Two masks, for two leaks:
//!
//! 1. **Uniform value masks** (§2.4 "Splitting with Augmented Subpolynomial",
//!    Fig. 5). The input is split into `m0` sub-polynomials of `N/m0`
//!    coefficients and each committed block is *augmented by one row* of
//!    `n0·n1 = N/(m0·m1)` uniformly random ring elements — the `ĝᵢ` of Fig. 3's
//!    `EcdToMat`. The prover publishes `y_g = Σᵢ g(x)·v₀` **before** the
//!    verifier's scalar `x* ← F×` exists, then sends the masked claims
//!    `ŷ*ᵢ = ŷᵢ + x*·(ĝᵢᵀŵ₀)`. Since `ĝᵢ` is uniform over the whole ring and
//!    `ŵ₀,₀ = 1`, the induced mask `ĝᵢŵ₀` is uniform, so every `ŷ*ᵢ` is
//!    uniform **whatever the claim was**: exact statistical hiding of the
//!    opened values with no hardness assumption, for `m0·n0·n1 = N/m1` mask
//!    elements in total.
//! 2. **A rejection-sampled Gaussian mask** (§2.4 "Aggregation with Rejection
//!    Sampling", Fig. 6). Aggregating the `m0` claims by `α` leaves the
//!    aggregate witness `Σᵢ α·F̂*ᵢ` a function of the input, hence not
//!    simulatable. The prover adds a masking block drawn from the discrete
//!    Gaussian `D_σ` and runs Lyubashevsky's `Rej` (Fig. 1) on the pair; by
//!    Lemma 2 of [LNP22] the accepted aggregate is within `2⁻¹²/M` of `D_σ` —
//!    statistically independent of every input block — provided
//!    `σ = 14·T/ln M` for `T` the aggregate's norm bound, which is exactly
//!    what [`sigma_for`] and [`aggregate_norm_bound`] compute (Theorem 5).
//!
//! # Why "sublinear"
//!
//! [`MaskShape`] carries the budget: value masks cost `N/m1` elements, the
//! masking commitment `N/m0 + N/(m0·m1)` — both `o(N)`. At the cube-root
//! balance `m0 = m1 = n0 = N^{1/3}` the overhead is `O(N^{2/3})` (§2.4 and
//! Theorem 8).
//!
//! # Seam: what this layer asks of the base PCS
//!
//! Nothing but *linear claims*. The layer never commits, never opens and never
//! picks a key shape: it consumes committed vectors `Fᵢ = (fᵢ ∥ gᵢ)` through
//! the [`crate::pcs::WeightPcs`] shape — `y = ⟨w, F⟩` for any table `w`, which
//! [`crate::pcs::mle::MleKey`] implements — and returns the
//! augmented weight tables ([`augmented_weight`]), the masked claims
//! ([`masked_claims`]), the verifier's closing equation ([`split_check`]), the
//! Gaussian aggregate ([`GaussianBlock`], [`aggregate_blocks`],
//! [`rejection_accept`]) and the witness-free simulation ([`simulate_split`]).
//! [`crate::pcs::mle`] is the backend the `examples/jindo.rs` assembly uses,
//! because it is the repo's only mode admitting **non-factored** weight tables
//! — which is what an augmented quadratic form flattens to.
//!
//! That choice has one cost, and it is not this layer's: `mle`'s tall key makes
//! the commitment *transparent*, so the layer delivers Hybrid Argument 0 of
//! Theorem 7 (the accepting **transcript** is statistically close to a
//! simulation) but not Hybrid Argument 1 (the **commitment** is hiding under
//! MLWE). A base whose commitment carries the masking term `B·r` —
//! `greyhound`'s Ajtai mode, or a CELPC-style `Com*` — supplies that half
//! unchanged (Theorem 2); the only shape change is that its Gaussian block must
//! also cover the `µ + ν` randomness rows, which is what
//! [`GaussianBlock::with_randomness`] is for and what adds the
//! `σ·√(2(µ+ν)d)` term to Theorem 5's `B`.
//!
//! # Genericity
//!
//! Every item is generic in the scalar ring `R` and the ring degree `D`, so the
//! layer runs over the crate's Z1 instance, over the non-NTT-friendly
//! `Z_{2³²−99}[X]/(X⁶⁴+1)` (see `split_check_closes_over_a_non_ntt_ring`), and
//! over the degenerate `D = 1` case where `R_{X^γ−b} = Z_p` and Fig. 2's `Ecd`
//! is the identity — which is the paper's own §2 presentation.

use crate::foundation::fs::seed_stream;
use crate::foundation::sampling::from_centered;
use algebra::crypto::sampling::{sample_uniform_coeff, BitStream, DiscreteGaussian};
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::{vec, vec::Vec};
use core::fmt;

/// Domain label for the uniform value-mask expansion.
const VALUE_MASK_DOMAIN: &[u8] = b"lattice-algebra/Z7/masking-value";

/// Domain label for the simulated (witness-free) split transcript.
const SIMULATE_DOMAIN: &[u8] = b"lattice-algebra/Z7/masking-simulate";

/// Domain label for the masking block's committed Gaussian part.
const GAUSS_DOMAIN: &[u8] = b"lattice-algebra/Z7/masking-gauss";

/// Domain label for the masking block's Gaussian randomness rows.
const GAUSS_R_DOMAIN: &[u8] = b"lattice-algebra/Z7/masking-gauss-r";

/// Domain label for the coin that drives [`rejection_accept`].
const REJ_COIN_DOMAIN: &[u8] = b"lattice-algebra/Z7/masking-rej";

/// Fixed-point scale of the rejection threshold (`2³²`).
const SCALE: u128 = 1u128 << 32;

/// Widest `σ` whose cumulative table is built (`24·σ + 1` `u128` entries).
pub const MAX_SIGMA: i64 = 1 << 16;

/// Why a masking step refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MaskError {
    /// A split dimension was zero.
    ZeroDimension,
    /// A vector had a length other than the one the shape requires.
    Ragged {
        /// Length supplied.
        got: usize,
        /// Length the shape requires.
        expected: usize,
    },
    /// The two operands of a form had different lengths.
    LengthMismatch {
        /// First length.
        left: usize,
        /// Second length.
        right: usize,
    },
    /// The claimed unit `x*` is not invertible.
    NotAUnit,
    /// A Gaussian width was not positive.
    BadWidth,
    /// A histogram carried no samples, so no distance is defined.
    EmptySample,
    /// `σ` is too wide for the `O(σ)` cumulative table of [`DiscreteGaussian`].
    SigmaTooWide {
        /// Requested width.
        sigma: i64,
    },
    /// A norm exceeded what `i128` accumulation can hold.
    Overflow,
}

impl fmt::Display for MaskError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ZeroDimension => write!(f, "a split dimension is zero"),
            Self::Ragged { got, expected } => {
                write!(f, "block of {got} elements against {expected}")
            }
            Self::LengthMismatch { left, right } => {
                write!(f, "form over {left} weights and {right} values")
            }
            Self::NotAUnit => write!(f, "the masking challenge x* is not invertible"),
            Self::BadWidth => write!(f, "width must be positive"),
            Self::EmptySample => write!(f, "histogram carries no samples"),
            Self::SigmaTooWide { sigma } => {
                write!(f, "sigma = {sigma} exceeds the samplable CDT range")
            }
            Self::Overflow => write!(f, "norm accumulation overflowed i128"),
        }
    }
}

/// The split shape `(m0, m1, n0, n1)` of Fig. 3's `Setup`.
///
/// `N = m0·m1·n0·n1` committed coefficients, read as the tensor `(i, j, k, ℓ)`:
/// `i` indexes the batch (one commitment per block), `j` the rows of a block's
/// matrix, `k` its columns and `ℓ` the encoding slot (`n1 = γ`, which is `1` in
/// the scalar-field case). The augmented block of Fig. 3's `EcdToMat` is
/// `(m1 + 1) × n0` — the extra row is the mask.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MaskShape {
    /// Blocks `m0` (the batch dimension).
    pub m0: usize,
    /// Rows per block `m1` (the mask adds one).
    pub m1: usize,
    /// Columns per block `n0`.
    pub n0: usize,
    /// Encoding slots per entry `n1 = γ`.
    pub n1: usize,
}

impl MaskShape {
    /// Builds the shape, rejecting a zero dimension.
    ///
    /// # Errors
    /// [`MaskError::ZeroDimension`] if any of `m0, m1, n0, n1` is zero.
    pub fn new(m0: usize, m1: usize, n0: usize, n1: usize) -> Result<Self, MaskError> {
        if m0 == 0 || m1 == 0 || n0 == 0 || n1 == 0 {
            return Err(MaskError::ZeroDimension);
        }
        Ok(Self { m0, m1, n0, n1 })
    }

    /// Committed coefficients `N = m0·m1·n0·n1`.
    pub fn coeffs(&self) -> usize {
        self.m0 * self.block_len()
    }

    /// Coefficients of one sub-polynomial `fᵢ`: `m1·n0·n1 = N/m0`.
    pub fn block_len(&self) -> usize {
        self.m1 * self.n0 * self.n1
    }

    /// Mask entries per block `n0·n1` — the single extra row of `F̂*ᵢ`.
    pub fn mask_len(&self) -> usize {
        self.n0 * self.n1
    }

    /// Committed entries per augmented block: `(m1 + 1)·n0·n1`.
    pub fn aug_len(&self) -> usize {
        self.block_len() + self.mask_len()
    }

    /// Total value-mask entries `m0·n0·n1 = N/m1` (mechanism 1 of the
    /// module docs): the mask the *opened values* are hidden by.
    pub fn value_masks(&self) -> usize {
        self.m0 * self.mask_len()
    }

    /// Entries of the masking block `F̂*_{m0}` of Fig. 6 line 1 — the
    /// `O(N/m0)` masking-commitment overhead of §2.4.
    pub fn masking_block_len(&self) -> usize {
        self.aug_len()
    }

    /// Whether both masks cost strictly less than the `N`-element witness.
    pub fn is_sublinear(&self) -> bool {
        let n = self.coeffs();
        self.value_masks() < n && self.masking_block_len() < n
    }
}

/// The zero of `R_q[X]/(X^D + 1)`.
fn zero<R: Ring, const D: usize>() -> PolyRing<R, D> {
    PolyRing::from_coefficients(vec![R::ZERO; D])
}

/// The one of `R_q[X]/(X^D + 1)`.
fn one<R: Ring, const D: usize>() -> PolyRing<R, D> {
    PolyRing::from_coefficients(vec![R::ONE])
}

/// `Σᵢ aᵢ·bᵢ` over the ring, with a typed length check.
///
/// This is the layer's only algebraic primitive: every claim of Fig. 5 —
/// `ŷᵢ = v₁ᵀF̂ᵢ₀`, `gᵢ(x) = ĝᵢᵀŵ₀`, `y = Σᵢ v₀ᵢŷᵢ` — is one instance of it.
///
/// # Errors
/// [`MaskError::LengthMismatch`] unless the two slices are equally long.
pub fn linear_form<R: Ring, const D: usize>(
    weights: &[PolyRing<R, D>],
    values: &[PolyRing<R, D>],
) -> Result<PolyRing<R, D>, MaskError> {
    if weights.len() != values.len() {
        return Err(MaskError::LengthMismatch {
            left: weights.len(),
            right: values.len(),
        });
    }
    let mut acc = zero::<R, D>();
    for (w, v) in weights.iter().zip(values.iter()) {
        acc += w.clone() * v.clone();
    }
    Ok(acc)
}

/// The invertible masking challenge `x* ∈ F×` of Fig. 5 line 5, stored with its
/// inverse.
///
/// Invertibility is load-bearing twice: the mask `x*·(ĝᵀŵ₀)` is uniform only
/// for invertible `x*`, and the soundness loss is `1/|F×|` (Schwartz–Zippel on
/// the linear polynomial `X* ↦ y + X*·y_g − Σᵢ⟨Dcd(ŷ*ᵢ), w₁⟩v₀ᵢ`). Carrying the
/// inverse explicitly keeps the layer generic over rings, which have no
/// ring-level inversion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnitChallenge<R: Ring, const D: usize> {
    value: PolyRing<R, D>,
    inv: PolyRing<R, D>,
}

impl<R: Ring, const D: usize> UnitChallenge<R, D> {
    /// Accepts `x*` only when `x*·inv == 1`, so a zero-divisor challenge (which
    /// exists as soon as `D > 1`) is a typed rejection rather than a silent
    /// loss of hiding.
    ///
    /// # Errors
    /// [`MaskError::NotAUnit`] when the product is not the ring's one.
    pub fn new(value: PolyRing<R, D>, inv: PolyRing<R, D>) -> Result<Self, MaskError> {
        if value.clone() * inv.clone() != one::<R, D>() {
            return Err(MaskError::NotAUnit);
        }
        Ok(Self { value, inv })
    }

    /// `x*` itself.
    pub fn value(&self) -> &PolyRing<R, D> {
        &self.value
    }

    /// `x*⁻¹`.
    pub fn inv(&self) -> &PolyRing<R, D> {
        &self.inv
    }
}

/// `len` uniform ring elements from a domain-separated seed.
fn uniform_ring_vec<R: Ring, const D: usize>(
    domain: &[u8],
    seed: &[u8; 32],
    len: usize,
) -> Vec<PolyRing<R, D>> {
    let mut xof = seed_stream::<Shake256Xof>(domain, seed);
    let mut stream = BitStream::new(&mut xof);
    (0..len)
        .map(|_| {
            PolyRing::from_coefficients(
                (0..D)
                    .map(|_| sample_uniform_coeff::<R>(&mut stream))
                    .collect(),
            )
        })
        .collect()
}

/// `len` ring elements `1, b, b², …, b^{len−1}`.
///
/// This is the weight table of Fig. 3's univariate reading (`X̃^i = X^i`): the
/// claim `y = ⟨w, F⟩` with `w = power_table(x, N)` *is* `y = f(x)`, and the
/// block factors `v₀ᵢ = X̃^{m1·n·i}` are the entries at stride `m1·n0·n1`. The
/// multilinear reading replaces it with an `eq` tensor
/// ([`crate::sumcheck::eq_tensor`]) and the layer does not care which.
///
/// [`crate::pcs::greyhound`] keeps the same construction private; it is
/// repeated here because the masking layer's shape arithmetic needs it at
/// three different lengths (`m1·n0·n1`, `n0·n1`, and the batch factors).
pub fn power_table<R: Ring, const D: usize>(
    base: &PolyRing<R, D>,
    len: usize,
) -> Vec<PolyRing<R, D>> {
    let mut out = Vec::with_capacity(len);
    let mut acc = one::<R, D>();
    for _ in 0..len {
        out.push(acc.clone());
        acc *= base.clone();
    }
    out
}

/// The uniform value masks `(ĝ₀, …, ĝ_{m0−1})` of §2.4.
///
/// Each block gets `n0·n1` entries drawn **uniformly over the ring**, not from
/// a bounded set: `ĝᵢᵀŵ₀` is uniform because `ĝᵢ` is, and a bounded mask leaves
/// a measurable fingerprint of the claim (the `bounded_mask_*` test pins that
/// difference down).
///
/// Deterministic in `seed`, so a test can replay one exact mask table.
pub fn sample_masks<R: Ring, const D: usize>(
    shape: &MaskShape,
    seed: &[u8; 32],
) -> Vec<Vec<PolyRing<R, D>>> {
    uniform_ring_vec::<R, D>(VALUE_MASK_DOMAIN, seed, shape.value_masks())
        .chunks(shape.mask_len())
        .map(<[PolyRing<R, D>]>::to_vec)
        .collect()
}

/// Fig. 5 line 6: `v̂*₁ := (v̂₁, Ecd(x*))` — the claim weight table with the
/// mask row's weights appended.
///
/// `claim` holds the `m1·n0·n1` weights of the sub-polynomial rows and
/// `mask_weight` the `n0·n1` weights of the mask row (`ŵ₀`); the appended block
/// is `x*·mask_weight`, because the augmented row of `f* = f + X*·g` is scaled
/// by `X*`.
///
/// # Errors
/// [`MaskError::Ragged`] unless `claim` has `m1·n0·n1` and `mask_weight`
/// `n0·n1` entries.
pub fn augmented_weight<R: Ring, const D: usize>(
    shape: &MaskShape,
    claim: &[PolyRing<R, D>],
    mask_weight: &[PolyRing<R, D>],
    xstar: &PolyRing<R, D>,
) -> Result<Vec<PolyRing<R, D>>, MaskError> {
    if claim.len() != shape.block_len() || mask_weight.len() != shape.mask_len() {
        return Err(MaskError::Ragged {
            got: claim.len() + mask_weight.len(),
            expected: shape.aug_len(),
        });
    }
    let mut out = Vec::with_capacity(shape.aug_len());
    out.extend_from_slice(claim);
    out.extend(mask_weight.iter().map(|w| w.clone() * xstar.clone()));
    Ok(out)
}

/// Fig. 5 line 9: the masked claims `ŷ* := ŷᵢ + x*·(ĝᵢᵀŵ₀)`.
///
/// `ys` are the unmasked claim values `ŷᵢ` and `mus` the masks' own values
/// `ĝᵢᵀŵ₀`, one entry per block.
///
/// # Errors
/// [`MaskError::LengthMismatch`] unless `ys` and `mus` are equally long.
pub fn masked_claims<R: Ring, const D: usize>(
    ys: &[PolyRing<R, D>],
    mus: &[PolyRing<R, D>],
    xstar: &PolyRing<R, D>,
) -> Result<Vec<PolyRing<R, D>>, MaskError> {
    if ys.len() != mus.len() {
        return Err(MaskError::LengthMismatch {
            left: ys.len(),
            right: mus.len(),
        });
    }
    Ok(ys
        .iter()
        .zip(mus.iter())
        .map(|(y, mu)| y.clone() + xstar.clone() * mu.clone())
        .collect())
}

/// Fig. 5 line 4: `y_g := Σᵢ gᵢ(x)·v₀ᵢ (mod p)` — the mask's own evaluation,
/// sent *before* `x*` exists.
///
/// # Errors
/// [`MaskError::LengthMismatch`] unless `mus` and `v0` are equally long.
pub fn mask_evaluation<R: Ring, const D: usize>(
    v0: &[PolyRing<R, D>],
    mus: &[PolyRing<R, D>],
) -> Result<PolyRing<R, D>, MaskError> {
    linear_form(v0, mus)
}

/// Fig. 5 line 11: the verifier's closing equation, as the pair
/// `(y + x*·y_g, Σᵢ ⟨Dcd(ŷ*ᵢ), w₁⟩·v₀ᵢ)`.
///
/// The right-hand side is the block-weighted sum of the masked claims, so the
/// verifier accepts exactly when the pair is equal. Setting `x* = 0` (no mask)
/// leaves the left side at `y` while the right side still carries the `ŷᵢ`,
/// which is the equation a mask-free prover has to satisfy.
///
/// # Errors
/// [`MaskError::LengthMismatch`] unless `v0` and `ystars` are equally long.
pub fn split_check<R: Ring, const D: usize>(
    y: &PolyRing<R, D>,
    y_g: &PolyRing<R, D>,
    xstar: &PolyRing<R, D>,
    ystars: &[PolyRing<R, D>],
    v0: &[PolyRing<R, D>],
) -> Result<(PolyRing<R, D>, PolyRing<R, D>), MaskError> {
    Ok((
        y.clone() + xstar.clone() * y_g.clone(),
        linear_form(v0, ystars)?,
    ))
}

/// `⌈√n⌉` over `u64`, integer only (`core` exposes no `sqrt`).
fn isqrt_ceil(n: u64) -> u64 {
    let r = (n as u128).isqrt() as u64;
    if u128::from(r) * u128::from(r) < u128::from(n) {
        r + 1
    } else {
        r
    }
}

/// Theorem 5's bound `T = m0·√n0·B_C·B` on the L2 norm of the aggregate
/// `Σᵢ αᵢ·[F̂*; Rᵢ]`, which [`sigma_for`] must dominate.
///
/// Each of the `m0` blocks contributes `n0` columns of norm `≤ B`, each scaled
/// by a challenge with `‖α‖₁ ≤ B_C`, so one block has norm `≤ √n0·B_C·B` and
/// the triangle inequality over `m0` blocks gives `T`. `√n0` rounds **up** so
/// the bound stays valid for a non-square `n0`.
///
/// Returns `None` on `i64` overflow — `σ = 14·T/ln M` past that is not
/// samplable here anyway, so the caller must shrink the instance.
pub fn aggregate_norm_bound(m0: usize, n0: usize, b_c: i64, b: i64) -> Option<i64> {
    let root = i64::try_from(isqrt_ceil(n0 as u64)).ok()?;
    (m0 as i64)
        .checked_mul(root)?
        .checked_mul(b_c)?
        .checked_mul(b)
}

/// Lemma 2 / Theorem 5's Gaussian width `σ = 14·T/ln M`, rounded up.
///
/// `log_m` is `ln M`, so [`rejection_accept`]'s probability is at least
/// `(1 − 2⁻¹²⁸)/M`. Rounding up keeps `σ ≥ 14·T/ln M` — the lemma's hypothesis
/// — at the price of accepting marginally more often than `1/M`.
///
/// # Errors
/// [`MaskError::BadWidth`] if `t_bound` or `log_m` is not positive, and
/// [`MaskError::Overflow`] past `i64`.
pub fn sigma_for(t_bound: i64, log_m: i64) -> Result<i64, MaskError> {
    if t_bound <= 0 || log_m <= 0 {
        return Err(MaskError::BadWidth);
    }
    let num = i128::from(t_bound)
        .checked_mul(14)
        .ok_or(MaskError::Overflow)?;
    let sigma = (num + i128::from(log_m) - 1) / i128::from(log_m);
    i64::try_from(sigma).map_err(|_| MaskError::Overflow)
}

/// The masking block of Fig. 6 line 1:
/// `[F̂*_{m0}; R_{m0}] ← D_σ^{(m1+µ+ν+1)·n0·d}`.
///
/// The paper's Gaussian covers the `(m1+1)·n0` committed entries **and** the
/// `µ + ν` randomness rows per column. The `mle` backend has no randomness rows
/// (its tall key over-determines the witness instead), so
/// [`GaussianBlock::committed`] samples only the committed part; a base whose
/// commitment carries `B·r` adds the rows with [`Self::with_randomness`], and
/// Theorem 5's `B` then gains its `σ·√(2(µ+ν)d)` term.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GaussianBlock<R: Ring, const D: usize> {
    /// The committed part `F̂*_{m0}`.
    pub committed: Vec<PolyRing<R, D>>,
    /// The randomness part `R_{m0}` — empty for a base that does not mask with
    /// `B·r`.
    pub randomness: Vec<PolyRing<R, D>>,
    /// The width every entry was drawn at.
    pub sigma: i64,
}

impl<R: Ring + CenteredRing, const D: usize> GaussianBlock<R, D> {
    /// Samples `(m1+1)·n0` committed ring elements from `D_σ`.
    ///
    /// # Errors
    /// [`MaskError::BadWidth`] for a non-positive width, [`MaskError::SigmaTooWide`]
    /// past the table budget, [`MaskError::Overflow`] past `i128`.
    pub fn committed(shape: &MaskShape, sigma: i64, seed: &[u8; 32]) -> Result<Self, MaskError> {
        Ok(Self {
            committed: coeffs_to_ring(&gaussian_coeffs_from(
                GAUSS_DOMAIN,
                shape.aug_len() * D,
                sigma,
                seed,
            )?),
            randomness: Vec::new(),
            sigma,
        })
    }

    /// Extends the block with `rows` randomness ring elements per column
    /// (independent draws at the same `σ`, own domain label), for a hiding base
    /// commitment.
    ///
    /// # Errors
    /// As [`Self::committed`].
    pub fn with_randomness(
        shape: &MaskShape,
        sigma: i64,
        rows: usize,
        seed: &[u8; 32],
    ) -> Result<Self, MaskError> {
        Ok(Self {
            committed: Self::committed(shape, sigma, seed)?.committed,
            randomness: coeffs_to_ring(&gaussian_coeffs_from(
                GAUSS_R_DOMAIN,
                rows * shape.n0 * D,
                sigma,
                seed,
            )?),
            sigma,
        })
    }

    /// The block as centered integer coefficients — the `z` argument of
    /// [`rejection_accept`] once the `α`-combination has been added in.
    pub fn as_coeffs(&self) -> Vec<i64> {
        let mut out = ring_to_coeffs(&self.committed);
        out.extend(ring_to_coeffs(&self.randomness));
        out
    }
}

/// `len` independent draws from the discrete Gaussian `D_σ` over `Z`, from a
/// caller-supplied domain label.
fn gaussian_coeffs_from(
    domain: &[u8],
    len: usize,
    sigma: i64,
    seed: &[u8; 32],
) -> Result<Vec<i64>, MaskError> {
    if sigma <= 0 {
        return Err(MaskError::BadWidth);
    }
    if sigma > MAX_SIGMA {
        return Err(MaskError::SigmaTooWide { sigma });
    }
    let mut xof = seed_stream::<Shake256Xof>(domain, seed);
    let mut stream = BitStream::new(&mut xof);
    Ok(DiscreteGaussian::new(sigma as f64).sample_many(&mut stream, len))
}

/// `len` independent draws from the discrete Gaussian `D_σ` over `Z`.
///
/// Sampled by cumulative-table inversion ([`DiscreteGaussian`]), truncated at
/// `12σ`. The paper's §5.1 note that a rounded Gaussian is within `O(σ⁻²)` of
/// the discrete one is an *implementation* optimization; this repo takes the
/// discrete side of that trade, so no statistical distance is introduced here.
///
/// # Errors
/// [`MaskError::BadWidth`] for `sigma ≤ 0`, [`MaskError::SigmaTooWide`] past
/// the table budget.
pub fn gaussian_coeffs(len: usize, sigma: i64, seed: &[u8; 32]) -> Result<Vec<i64>, MaskError> {
    gaussian_coeffs_from(GAUSS_DOMAIN, len, sigma, seed)
}

/// Fig. 1's `Rej(z, v, σ)`, returning whether the sample is **accepted**
/// (`b = 0` in the paper's numbering — the prover aborts when it is not).
///
/// With `M = exp(log_m)` the test is
/// ```text
/// accept  ⟺  u ≤ (1/M)·exp((−2⟨z,v⟩ + ‖v‖²)/(2σ²))
/// ```
/// for a uniform `u ∈ [0,1)`, where `z` is the **already masked** aggregate
/// (`v + mask`) and `v` the aggregate that needs hiding — the convention Fig. 6
/// line 14 uses. The exponential is evaluated in `2³²` fixed point by
/// [`exp_neg_fixed`], so no floating point and no `libm` dependency enters the
/// protocol path; a threshold above `1` (which happens when `‖v‖` falls far
/// below its bound `T`) accepts, matching the `min(1, ·)` that makes `Rej` a
/// probability.
///
/// # Errors
/// [`MaskError::LengthMismatch`] unless `z` and `v` are equally long,
/// [`MaskError::BadWidth`] for a non-positive `sigma`/`log_m`, and
/// [`MaskError::Overflow`] if a norm exceeds `i128`.
pub fn rejection_accept(
    z: &[i64],
    v: &[i64],
    sigma: i64,
    log_m: i64,
    draw: u32,
) -> Result<bool, MaskError> {
    if z.len() != v.len() {
        return Err(MaskError::LengthMismatch {
            left: z.len(),
            right: v.len(),
        });
    }
    if sigma <= 0 || log_m <= 0 {
        return Err(MaskError::BadWidth);
    }
    let sigma = i128::from(sigma);
    let two_sigma_sq = 2 * sigma * sigma;
    // A = ‖v‖² − 2⟨z,v⟩: the numerator of the exponent.
    let mut a: i128 = 0;
    for (zi, vi) in z.iter().zip(v.iter()) {
        let (zi, vi) = (i128::from(*zi), i128::from(*vi));
        let term = vi
            .checked_mul(vi)
            .and_then(|sq| sq.checked_sub(2 * zi.checked_mul(vi)?))
            .ok_or(MaskError::Overflow)?;
        a = a.checked_add(term).ok_or(MaskError::Overflow)?;
    }
    // accept ⟺ u ≤ exp((A − 2σ²·ln M)/(2σ²)); a non-positive numerator means
    // the threshold is ≥ 1 and the sample always accepts.
    let num = two_sigma_sq
        .checked_mul(i128::from(log_m))
        .and_then(|t| t.checked_sub(a))
        .ok_or(MaskError::Overflow)?;
    if num <= 0 {
        return Ok(true);
    }
    Ok(u128::from(draw) <= exp_neg_fixed(num as u128, two_sigma_sq as u128))
}

/// `round(2³²·exp(−num/den))` for `num, den ≥ 0`, saturating.
///
/// The argument is reduced by `2⁸` so the Taylor series in `x/256` converges
/// well inside 16 terms, and the result is squared back up eight times. The
/// saturation is exact where it matters: `exp(−30)·2³² < 1`, so `num ≥ 30·den`
/// returns `0` and the caller rejects.
fn exp_neg_fixed(num: u128, den: u128) -> u128 {
    if num == 0 {
        return SCALE;
    }
    if den == 0 || num >= 30 * den {
        return 0;
    }
    let d = den * 256;
    let mut term = SCALE;
    let mut total = SCALE;
    let mut subtract = true;
    for k in 1..16u128 {
        let dk = d.saturating_mul(k);
        let next = (term * num + dk / 2) / dk;
        if next == 0 {
            break;
        }
        total = if subtract { total - next } else { total + next };
        subtract = !subtract;
        term = next;
    }
    let mut v = total;
    for _ in 0..8 {
        v = (v * v + (1u128 << 31)) >> 32;
    }
    v
}

/// A uniform `u32` rejection coin for attempt `attempt` of seed `seed`.
pub fn rejection_coin(seed: &[u8; 32], attempt: u32) -> u32 {
    let mut xof = seed_stream::<Shake256Xof>(REJ_COIN_DOMAIN, seed);
    xof.absorb(&attempt.to_le_bytes());
    let mut buf = [0u8; 4];
    xof.squeeze(&mut buf);
    u32::from_le_bytes(buf)
}

/// Fig. 6 lines 8/9: `X := Σᵢ α·Xᵢ + X_{m0}` for one kind of block.
///
/// Used for the commitment `û`, the claim value `ŷ*` and the witness `F̂*`, `R`,
/// `t̂` alike: `blocks` holds the `m0` inputs and `mask` the Gaussian entry from
/// line 1.
///
/// # Errors
/// [`MaskError::LengthMismatch`] unless `alphas` and `blocks` are equally long.
pub fn linear_combination<R: Ring, const D: usize>(
    alphas: &[PolyRing<R, D>],
    blocks: &[PolyRing<R, D>],
    mask: &PolyRing<R, D>,
) -> Result<PolyRing<R, D>, MaskError> {
    if alphas.len() != blocks.len() {
        return Err(MaskError::LengthMismatch {
            left: alphas.len(),
            right: blocks.len(),
        });
    }
    let mut acc = mask.clone();
    for (a, b) in alphas.iter().zip(blocks.iter()) {
        acc += a.clone() * b.clone();
    }
    Ok(acc)
}

/// Fig. 6 lines 10/12/13 for a whole vector block: `X := Σᵢ αᵢ·Xᵢ + X_{m0}`
/// coordinate-wise.
///
/// # Errors
/// [`MaskError::Ragged`] if `mask` or any block is not `len` long, and
/// [`MaskError::LengthMismatch`] unless `alphas` and `blocks` match.
pub fn aggregate_blocks<R: Ring, const D: usize>(
    alphas: &[PolyRing<R, D>],
    blocks: &[Vec<PolyRing<R, D>>],
    mask: &[PolyRing<R, D>],
    len: usize,
) -> Result<Vec<PolyRing<R, D>>, MaskError> {
    if alphas.len() != blocks.len() {
        return Err(MaskError::LengthMismatch {
            left: alphas.len(),
            right: blocks.len(),
        });
    }
    if mask.len() != len {
        return Err(MaskError::Ragged {
            got: mask.len(),
            expected: len,
        });
    }
    let mut out = mask.to_vec();
    for (alpha, block) in alphas.iter().zip(blocks.iter()) {
        if block.len() != len {
            return Err(MaskError::Ragged {
                got: block.len(),
                expected: len,
            });
        }
        for (acc, x) in out.iter_mut().zip(block.iter()) {
            *acc += alpha.clone() * x.clone();
        }
    }
    Ok(out)
}

/// The ΠSplit messages a verifier holds when ΠAgg starts (Fig. 5 lines 4–9).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SplitTranscript<R: Ring, const D: usize> {
    /// The invertible scalar challenge of line 5.
    pub xstar: PolyRing<R, D>,
    /// The mask evaluation of line 4.
    pub y_g: PolyRing<R, D>,
    /// The masked claims `ŷ*ᵢ` of line 9, one per block.
    pub masked_claims: Vec<PolyRing<R, D>>,
}

/// Appendix B.10's simulator `S1`, restricted to ΠSplit's messages.
///
/// It writes a transcript **without the witness**: `x*` and the `ŷ*ᵢ` are
/// uniform and `y_g` is *derived* from them by inverting the verifier's
/// equation,
/// ```text
/// y_g = x*⁻¹ · (Σᵢ v₀·ŷ* − y)
/// ```
/// which is line 1 of `S1`. This is the object the hiding statement is tested
/// against: a transcript satisfying every check that was never produced from
/// `f`.
///
/// # Errors
/// [`MaskError::LengthMismatch`] if `v0` is empty of claims — never for a valid
/// shape — propagating [`linear_form`]'s check.
pub fn simulate_split<R: Ring, const D: usize>(
    y: &PolyRing<R, D>,
    v0: &[PolyRing<R, D>],
    xstar: &UnitChallenge<R, D>,
    seed: &[u8; 32],
) -> Result<SplitTranscript<R, D>, MaskError> {
    let ystars = uniform_ring_vec::<R, D>(SIMULATE_DOMAIN, seed, v0.len());
    let sum = linear_form(v0, &ystars)?;
    Ok(SplitTranscript {
        xstar: xstar.value().clone(),
        y_g: xstar.inv().clone() * (sum - y.clone()),
        masked_claims: ystars,
    })
}

/// Counts how `values` fall into `bins` equal-width buckets over
/// `[-half, half]` of the centered representative.
///
/// The measurement half of the hiding tests and of the example trace; the
/// counts feed [`statistical_distance`]. Values outside the window land in an
/// end bucket, which can only *understate* a distance — so a measured `0` is
/// still a sound conclusion.
pub fn bucket_counts<R: CenteredRing>(values: &[R], bins: usize, half: i64) -> Vec<u64> {
    let mut counts = vec![0u64; bins];
    if bins == 0 || half <= 0 {
        return counts;
    }
    let span = 2 * i128::from(half);
    for v in values {
        let shifted = (i128::from(v.centered()) + i128::from(half)).clamp(0, span);
        let idx = usize::try_from(shifted * bins as i128 / span)
            .unwrap_or(0)
            .min(bins - 1);
        counts[idx] += 1;
    }
    counts
}

/// `½·Σₖ |pₐ(k) − p_b(k)|` between two histograms of equal bucket count.
///
/// `0` when the two samples are indistinguishable through this statistic, `1`
/// when their supports are disjoint — Definition 10's statistical distance as a
/// measurable quantity.
///
/// # Errors
/// [`MaskError::LengthMismatch`] unless the histograms are equally long, and
/// [`MaskError::EmptySample`] when either holds no samples (the distance
/// between two undefined distributions is not reported as `0`).
pub fn statistical_distance(a: &[u64], b: &[u64]) -> Result<f64, MaskError> {
    if a.len() != b.len() {
        return Err(MaskError::LengthMismatch {
            left: a.len(),
            right: b.len(),
        });
    }
    let sa: u64 = a.iter().sum();
    let sb: u64 = b.iter().sum();
    if a.is_empty() || sa == 0 || sb == 0 {
        return Err(MaskError::EmptySample);
    }
    let mut acc = 0.0f64;
    for (x, y) in a.iter().zip(b.iter()) {
        acc += (*x as f64 / sa as f64 - *y as f64 / sb as f64).abs();
    }
    Ok(acc / 2.0)
}

/// Centered integer coefficients → `Vec<PolyRing<R, D>>`, `D` per element.
fn coeffs_to_ring<R: Ring, const D: usize>(coeffs: &[i64]) -> Vec<PolyRing<R, D>> {
    coeffs
        .chunks(D)
        .map(|chunk| {
            let mut padded = chunk.to_vec();
            padded.resize(D, 0);
            PolyRing::from_coefficients(padded.iter().map(|c| from_centered::<R>(*c)).collect())
        })
        .collect()
}

/// `Vec<PolyRing<R, D>>` → centered integer coefficients, padded to `D` per
/// element ([`PolyRing::coefficients`] trims trailing zeros).
fn ring_to_coeffs<R: Ring + CenteredRing, const D: usize>(elts: &[PolyRing<R, D>]) -> Vec<i64> {
    let mut out = Vec::with_capacity(elts.len() * D);
    for e in elts {
        let cs = e.coefficients();
        out.extend(cs.iter().map(|c| c.centered()));
        // `coefficients()` trims trailing zeros, so every element is padded
        // back to exactly `D` slots before the next block starts.
        out.resize(out.len() + D - cs.len(), 0);
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::pcs::{Z1Coeff, MASK_BOUND};
    use algebra::crypto::sampling::sample_rej_bounded;
    use algebra::ring::zq::Zq;

    /// The house non-NTT instance: `2³² − 99` is prime and `≡ 5 (mod 8)`, so
    /// `q − 1` has 2-adicity 2 and no NTT of degree `≥ 4` exists.
    type Q5 = Zq<4294967197>;
    /// A field small enough to enumerate exhaustively, for the exact tests.
    type Tiny = Zq<5>;

    const D: usize = 8;

    /// The constant ring element carrying `v` (centered representative).
    fn elt<R: Ring, const N: usize>(v: i64) -> PolyRing<R, N> {
        PolyRing::from_coefficients(vec![from_centered::<R>(v)])
    }

    fn shape() -> MaskShape {
        MaskShape::new(3, 4, 3, 1).expect("non-zero shape")
    }

    /// The claim weight table `v̂₁` (shared prefix powers), the mask weight
    /// table `ŵ₀` (its first `n0·n1` entries) and the batch factors `v₀ᵢ`, all
    /// at the point `x`.
    fn tables<R: Ring, const N: usize>(
        s: &MaskShape,
        x: i64,
    ) -> (
        Vec<PolyRing<R, N>>,
        Vec<PolyRing<R, N>>,
        Vec<PolyRing<R, N>>,
    ) {
        let base = elt::<R, N>(x);
        let claim = power_table::<R, N>(&base, s.block_len());
        let mask_weight = claim[..s.mask_len()].to_vec();
        let v0_full = power_table::<R, N>(&base, s.m0 * s.block_len());
        let v0 = (0..s.m0)
            .map(|i| v0_full[i * s.block_len()].clone())
            .collect();
        (claim, mask_weight, v0)
    }

    #[test]
    fn shape_budget_is_sublinear_and_matches_the_paper() {
        let s = shape();
        assert_eq!(s.coeffs(), 36);
        assert_eq!(s.block_len(), 12);
        assert_eq!(s.mask_len(), 3);
        assert_eq!(s.aug_len(), 15);
        // value masks: m0·n0·n1 = N/m1
        assert_eq!(s.value_masks(), 9);
        assert_eq!(s.value_masks(), s.coeffs() / s.m1);
        // masking commitment: (m1+1)·n0·n1 = N/m0 + N/(m0·m1)
        assert_eq!(s.masking_block_len(), 15);
        assert_eq!(
            s.masking_block_len(),
            s.coeffs() / s.m0 + s.coeffs() / (s.m0 * s.m1)
        );
        assert!(s.is_sublinear());
        // The cube-root balance of §1.1: m0 = m1 = n0 = N^{1/3} leaves exactly
        // an N^{2/3} masking overhead, which is the paper's headline claim.
        let c = MaskShape::new(27, 27, 27, 1).expect("cube-root shape");
        assert_eq!(c.coeffs(), 19683);
        assert_eq!(c.value_masks(), 729);
        assert_eq!(c.value_masks(), c.coeffs() / 27);
        assert_eq!(MaskShape::new(0, 1, 1, 1), Err(MaskError::ZeroDimension));
    }

    #[test]
    fn augmented_weight_satisfies_the_paper_identity() {
        // ⟨w*, (f ∥ g)⟩ == ⟨w, f⟩ + x*·⟨u, g⟩ — the flattened form of
        // ŷ*ᵢ = v̂*₁ᵀF*ᵢŵ₀ = ŷᵢ + x*·ĝᵢᵀŵ₀ (Fig. 5 line 9).
        let s = shape();
        let (w, u, _) = tables::<Z1Coeff, D>(&s, 7);
        let f: Vec<_> = (0..s.block_len())
            .map(|i| elt::<Z1Coeff, D>(i as i64 - 3))
            .collect();
        let g: Vec<_> = (0..s.mask_len())
            .map(|i| elt::<Z1Coeff, D>(2 * i as i64 + 1))
            .collect();
        let xs = elt::<Z1Coeff, D>(11);
        let ws = augmented_weight(&s, &w, &u, &xs).expect("sized");
        assert_eq!(ws.len(), s.aug_len());
        let mut aug = Vec::with_capacity(s.aug_len());
        aug.extend(f.iter().cloned());
        aug.extend(g.iter().cloned());
        let lhs = linear_form(&ws, &aug).expect("form");
        let y = linear_form(&w, &f).expect("y");
        let mu = linear_form(&u, &g).expect("mu");
        assert_eq!(lhs, y + xs.clone() * mu, "the appended row must read at x*");
        assert_eq!(
            augmented_weight(&s, &w[..4], &u, &xs),
            Err(MaskError::Ragged {
                got: 7,
                expected: 15
            }),
            "a short claim table is a typed rejection, not a silent pad"
        );
    }

    #[test]
    fn split_check_closes_the_evaluation_relation() {
        // Σᵢ v₀·ŷ* == f(x) + x*·g(x) with y = f(x) and y_g = g(x). The index
        // arithmetic (verified in python before coding) is that the block
        // weights are the SHARED prefix powers and the block factor is
        // v₀ᵢ = x^{m1·n0·n1·i}.
        let s = shape();
        let (w, u, v0) = tables::<Z1Coeff, D>(&s, 7);
        let blocks: Vec<Vec<_>> = (0..s.m0)
            .map(|i| {
                (0..s.block_len())
                    .map(|t| elt::<Z1Coeff, D>(((i * 7 + t * 3) % 9) as i64 - 4))
                    .collect()
            })
            .collect();
        let masks = sample_masks::<Z1Coeff, D>(&s, &[4u8; 32]);
        assert_eq!(masks.len(), s.m0);
        let ys: Vec<_> = blocks
            .iter()
            .map(|b| linear_form(&w, b).expect("y"))
            .collect();
        let mus: Vec<_> = masks
            .iter()
            .map(|g| linear_form(&u, g).expect("mu"))
            .collect();
        let xs = elt::<Z1Coeff, D>(11);
        let y_stars = masked_claims(&ys, &mus, &xs).expect("masked");
        let y_g = mask_evaluation(&v0, &mus).expect("y_g");
        let y = linear_form(&v0, &ys).expect("y");
        let (lhs, rhs) = split_check(&y, &y_g, &xs, &y_stars, &v0).expect("check");
        assert_eq!(lhs, rhs, "an honest masked transcript must close");

        // Not vacuous: with the mask switched off (x* = 0) the same messages do
        // not close, and one perturbed ŷ* breaks the equation too.
        let (l0, r0) = split_check(&y, &y_g, &elt::<Z1Coeff, D>(0), &y_stars, &v0).expect("check");
        assert_ne!(l0, r0, "a zero mask must not close line 11");
        let mut tampered = y_stars.clone();
        tampered[1] = tampered[1].clone() + elt::<Z1Coeff, D>(1);
        let (tl, tr) = split_check(&y, &y_g, &xs, &tampered, &v0).expect("check");
        assert_ne!(tl, tr, "one perturbed ŷ* must trip line 11");

        // And y really is the power-table evaluation of the whole polynomial.
        let mut flat = Vec::with_capacity(s.coeffs());
        for b in blocks.iter() {
            flat.extend(b.iter().cloned());
        }
        let powers = power_table::<Z1Coeff, D>(&elt::<Z1Coeff, D>(7), s.coeffs());
        let direct = linear_form(&powers, &flat).expect("direct");
        assert_eq!(y, direct, "Σᵢ v₀·⟨w,fᵢ⟩ must be the power-table evaluation");
    }

    #[test]
    fn split_check_closes_over_a_non_ntt_ring() {
        // The same algebra over Z_{2^32-99}[X]/(X^64+1): 2-adicity 2 means no
        // NTT exists, and elements are genuine polynomials whose products mix
        // coefficients — a wrong negacyclic reduction breaks the closure.
        let s = MaskShape::new(2, 3, 2, 4).expect("shape");
        let block = s.block_len();
        let base = {
            let mut c = vec![Q5::ZERO; 64];
            c[0] = Q5::from(3);
            c[63] = Q5::from(1);
            PolyRing::from_coefficients(c)
        };
        let w = power_table::<Q5, 64>(&base, block);
        let u = w[..s.mask_len()].to_vec();
        let v0_full = power_table::<Q5, 64>(&base, s.m0 * block);
        let v0: Vec<_> = (0..s.m0).map(|i| v0_full[i * block].clone()).collect();
        let f: Vec<Vec<_>> = (0..s.m0)
            .map(|i| {
                (0..block)
                    .map(|t| {
                        let mut c = vec![Q5::ZERO; 64];
                        c[(t + i) % 64] = Q5::from((t + 1) as u64);
                        c[(2 * t + 7) % 64] = Q5::from((i + 1) as u64);
                        PolyRing::from_coefficients(c)
                    })
                    .collect()
            })
            .collect();
        let g = sample_masks::<Q5, 64>(&s, &[9u8; 32]);
        assert_eq!(g[0].len(), s.mask_len());
        let xs = {
            let mut c = vec![Q5::ZERO; 64];
            c[0] = Q5::from(11);
            PolyRing::from_coefficients(c)
        };
        let ys: Vec<_> = f.iter().map(|b| linear_form(&w, b).expect("y")).collect();
        let mus: Vec<_> = g.iter().map(|b| linear_form(&u, b).expect("mu")).collect();
        let y_stars = masked_claims(&ys, &mus, &xs).expect("masked");
        let y_g = mask_evaluation(&v0, &mus).expect("y_g");
        let y = linear_form(&v0, &ys).expect("y");
        let (lhs, rhs) = split_check(&y, &y_g, &xs, &y_stars, &v0).expect("check");
        assert_eq!(lhs, rhs, "the relation must close over the non-NTT ring");
        assert_ne!(ys, y_stars, "masking must change the claim values");
        assert_ne!(mus[0], mus[1], "the masks must be block-independent");
    }

    #[test]
    fn a_uniform_mask_hides_the_claim_exactly() {
        // Enumerate the WHOLE mask space over F_5 (n0·n1 = 2 ⇒ 25 masks) and
        // compare the marginal of the masked value for two different claims.
        // The paper's claim is exact: ŷ* = y + x*·⟨u,g⟩ is uniform whenever u
        // has an invertible entry (here u₀ = 1, the paper's "w_{0,0} = 1"), so
        // the two marginals coincide and the distance is 0 — while the two
        // unmasked claims are point masses at distance 1.
        let u: Vec<PolyRing<Tiny, 1>> = vec![elt::<Tiny, 1>(1), elt::<Tiny, 1>(2)];
        let xs = elt::<Tiny, 1>(3);
        let (y0, y1) = (elt::<Tiny, 1>(0), elt::<Tiny, 1>(4));
        let mut hist0 = vec![0u64; 5];
        let mut hist1 = vec![0u64; 5];
        let mut point0 = vec![0u64; 5];
        let mut point1 = vec![0u64; 5];
        for g0 in 0..5u64 {
            for g1 in 0..5u64 {
                let g = vec![
                    PolyRing::from_coefficients(vec![Tiny::from(g0)]),
                    PolyRing::from_coefficients(vec![Tiny::from(g1)]),
                ];
                let mu = linear_form(&u, &g).expect("mu");
                let s0 = masked_claims(&[y0.clone()], &[mu.clone()], &xs).expect("mask")[0].clone();
                let s1 = masked_claims(&[y1.clone()], &[mu], &xs).expect("mask")[0].clone();
                hist0[s0.coefficients()[0].to_u128() as usize] += 1;
                hist1[s1.coefficients()[0].to_u128() as usize] += 1;
            }
        }
        point0[y0.coefficients()[0].to_u128() as usize] = 25;
        point1[y1.coefficients()[0].to_u128() as usize] = 25;
        assert_eq!(
            hist0,
            vec![5u64; 5],
            "a uniform mask must spread each claim evenly over the field"
        );
        assert_eq!(
            statistical_distance(&hist0, &hist1).expect("dist"),
            0.0,
            "two different committed polynomials opened at one point must give
             identical marginals"
        );
        assert_eq!(statistical_distance(&point0, &point1).expect("dist"), 1.0);
    }

    #[test]
    fn a_bounded_mask_leaves_the_claims_distinguishable() {
        // The negative control on the test above, on the same field and the
        // same enumeration: a mask drawn from a bounded set — the `MASK_BOUND`
        // shape `mle`'s Σ-mask uses — does not spread the claim evenly, so two
        // claims sit at non-zero distance. This is why §2.4 samples ĝᵢ uniformly
        // over R rather than from a small noise distribution.
        let u: Vec<PolyRing<Tiny, 1>> = vec![elt::<Tiny, 1>(1), elt::<Tiny, 1>(2)];
        let xs = elt::<Tiny, 1>(3);
        let mut hist0 = vec![0u64; 5];
        let mut hist1 = vec![0u64; 5];
        for g0 in -1i64..=1 {
            for g1 in -1i64..=1 {
                let g = vec![elt::<Tiny, 1>(g0), elt::<Tiny, 1>(g1)];
                let mu = linear_form(&u, &g).expect("mu");
                let s0 = masked_claims(&[elt::<Tiny, 1>(0)], &[mu.clone()], &xs).expect("mask")[0]
                    .clone();
                let s1 = masked_claims(&[elt::<Tiny, 1>(4)], &[mu], &xs).expect("mask")[0].clone();
                hist0[s0.coefficients()[0].to_u128() as usize] += 1;
                hist1[s1.coefficients()[0].to_u128() as usize] += 1;
            }
        }
        let d = statistical_distance(&hist0, &hist1).expect("dist");
        assert!(
            (d - 1.0 / 9.0).abs() < 1e-12,
            "a bounded mask must sit the two claims at distance 1/9, got {d}"
        );
        // and the bounded sampler really is bounded, which is the whole point
        let mut xof = Shake256Xof::new(b"bounded-control");
        let mut stream = BitStream::new(&mut xof);
        for _ in 0..200 {
            let m = sample_rej_bounded::<Z1Coeff>(&mut stream, MASK_BOUND);
            assert!(
                m.abs() <= i64::from(MASK_BOUND),
                "bounded mask escaped {MASK_BOUND}"
            );
        }
    }

    #[test]
    fn exp_neg_fixed_matches_known_values() {
        // 2^32·exp(-x) at the analytic values (computed in python before
        // coding): a wrong reduction or a miscounted squaring shifts these by
        // orders of magnitude, so the assertion is sensitive.
        let cases: [(u128, u128, u128); 5] = [
            (0, 1, 4_294_967_296), // exp(0)
            (1, 2, 2_605_029_347), // exp(-0.5)
            (1, 1, 1_580_030_169), // exp(-1)
            (3, 1, 213_833_830),   // exp(-3)·2^32 = 213 833 830.4
            (10, 1, 194_991),      // exp(-10)
        ];
        for (num, den, want) in cases {
            let got = exp_neg_fixed(num, den);
            let slack = (want / 100_000).max(20);
            assert!(
                got + slack >= want && got.saturating_sub(want) <= slack,
                "exp(-{num}/{den}): got {got}, want {want}"
            );
        }
        assert_eq!(exp_neg_fixed(31, 1), 0, "exp(-31)·2^32 < 1 saturates to 0");
        assert_eq!(exp_neg_fixed(0, 0), SCALE, "the zero exponent is 1");
    }

    #[test]
    fn rejection_sampling_needs_the_lemmas_sigma() {
        // Lemma 2: at σ = 14T/ln M the accepted aggregate is within 2^-128/M of
        // D_σ — which means both that it is accepted with probability ≥ 1/M and
        // that it carries no trace of v. Shrink σ below the lemma's value and
        // both guarantees fail measurably. This is the "mask size the paper's
        // lemma requires" test.
        let ell = 4usize;
        let t = 40i64;
        let log_m = 1i64; // M = e ⇒ accept ≥ (1 − 2^-128)/e ≈ 0.368
        let good = sigma_for(t, log_m).expect("sigma");
        assert_eq!(good, 14 * t, "σ = 14T/ln M at ln M = 1");
        assert_eq!(
            sigma_for(t, 3).expect("sigma"),
            (14 * t + 2) / 3,
            "σ rounds up, keeping σ ≥ 14T/ln M"
        );
        assert_eq!(
            aggregate_norm_bound(2, 3, 3, 13).expect("bound"),
            2 * 2 * 3 * 13,
            "T = m0·⌈√n0⌉·B_C·B"
        );
        assert_eq!(
            aggregate_norm_bound(1, 4, 1, 5).expect("square n0"),
            10,
            "an exact square must not round up"
        );
        assert_eq!(sigma_for(0, 1), Err(MaskError::BadWidth));

        let v = [20i64; 4];
        assert_eq!(
            v.iter().map(|x| x * x).sum::<i64>(),
            t * t,
            "the control instance must sit exactly at the bound T"
        );
        let trials = 3000usize;
        let mut biases = Vec::new();
        for sigma in [good, t / 2] {
            let mask = gaussian_coeffs(ell * trials, sigma, &[5u8; 32]).expect("gauss");
            let mut accepted = 0usize;
            let mut positive = 0usize;
            let mut sum = 0i128;
            let mut sumsq = 0i128;
            for (i, chunk) in mask.chunks(ell).enumerate() {
                let z: Vec<i64> = chunk.iter().zip(v.iter()).map(|(m, vv)| m + vv).collect();
                let draw = rejection_coin(&[6u8; 32], i as u32);
                if rejection_accept(&z, &v, sigma, log_m, draw).expect("rej") {
                    accepted += 1;
                    if z[0] > 0 {
                        positive += 1;
                    }
                    sum += i128::from(z[0]);
                    sumsq += i128::from(z[0]) * i128::from(z[0]);
                }
            }
            let rate = accepted as f64 / trials as f64;
            let mean = sum as f64 / accepted as f64;
            let var = sumsq as f64 / accepted as f64 - mean * mean;
            let bias = (positive as f64 / accepted as f64 - 0.5).abs();
            biases.push(bias);
            if sigma == good {
                assert!(rate > 0.30, "lemma σ must accept ≈1/M = 0.368, got {rate}");
                assert!(bias < 0.05, "v's sign leaked into the accepted z: {bias}");
                assert!(
                    (var / (sigma * sigma) as f64 - 1.0).abs() < 0.15,
                    "the accepted aggregate is not D_σ: variance {var} against σ² = {}",
                    sigma * sigma
                );
            } else {
                assert!(
                    rate < 0.30,
                    "a σ below the lemma's must break the (1−2^-128)/M bound, got {rate}"
                );
                assert!(bias > 0.08, "a too-small σ must leak v (bias {bias})");
            }
        }
        assert_eq!(biases.len(), 2, "both σ regimes measured");
        assert!(
            biases[0] < biases[1],
            "the lemma's σ must hide v better than the shrunken one"
        );
    }

    #[test]
    fn simulated_split_transcript_passes_the_verifier_check() {
        // B.10's S1 writes a valid transcript with no witness at all: were the
        // derived y_g wrong, line 11 would fail.
        let s = shape();
        let (_, _, v0) = tables::<Z1Coeff, D>(&s, 7);
        let y = elt::<Z1Coeff, D>(12345);
        let inv = Z1Coeff::from(7).inverse().expect("7 is a unit");
        let xs = UnitChallenge::<Z1Coeff, D>::new(
            elt::<Z1Coeff, D>(7),
            elt::<Z1Coeff, D>(inv.to_u128() as i64),
        )
        .expect("unit");
        let sim = simulate_split(&y, &v0, &xs, &[3u8; 32]).expect("simulate");
        assert_eq!(sim.masked_claims.len(), s.m0);
        let (lhs, rhs) =
            split_check(&y, &sim.y_g, &sim.xstar, &sim.masked_claims, &v0).expect("check");
        assert_eq!(lhs, rhs, "the simulation must satisfy line 11");
        // a second seed gives a different transcript: the simulation is
        // randomized, not one fixed string
        let other = simulate_split(&y, &v0, &xs, &[4u8; 32]).expect("simulate 2");
        assert_ne!(sim.masked_claims, other.masked_claims);
        assert_ne!(sim.y_g, other.y_g);
    }

    #[test]
    fn unit_challenge_rejects_a_non_unit() {
        // Over a ring with zero divisors a "challenge" that is not invertible
        // silently destroys the hiding, so the layer refuses it.
        let a = PolyRing::from_coefficients(vec![Z1Coeff::from(3), Z1Coeff::ZERO]);
        let b = PolyRing::from_coefficients(vec![Z1Coeff::from(2), Z1Coeff::ZERO]);
        assert_eq!(
            UnitChallenge::<Z1Coeff, 2>::new(a, b),
            Err(MaskError::NotAUnit)
        );
        let inv = Z1Coeff::from(5).inverse().expect("5 is a unit");
        assert!(UnitChallenge::<Z1Coeff, 2>::new(
            PolyRing::from_coefficients(vec![Z1Coeff::from(5)]),
            PolyRing::from_coefficients(vec![inv])
        )
        .is_ok());
    }

    #[test]
    fn linear_combination_and_aggregate_fold_like_fig_6() {
        let alphas: Vec<_> = (0..3).map(|i| elt::<Z1Coeff, D>(i + 1)).collect();
        let vals: Vec<_> = (0..3).map(|i| elt::<Z1Coeff, D>(10 * i)).collect();
        let got = linear_combination(&alphas, &vals, &elt::<Z1Coeff, D>(7)).expect("fold");
        // 1·0 + 2·10 + 3·20 + 7 = 87
        assert_eq!(got, elt::<Z1Coeff, D>(87));
        let blocks: Vec<Vec<_>> = (0..3)
            .map(|i| (0..4).map(|t| elt::<Z1Coeff, D>(i + t)).collect())
            .collect();
        let mask = vec![elt::<Z1Coeff, D>(1); 4];
        let agg = aggregate_blocks(&alphas, &blocks, &mask, 4).expect("aggregate");
        for t in 0..4i64 {
            let want: i64 = (0..3).map(|i| (i + 1) * (i + t)).sum::<i64>() + 1;
            assert_eq!(agg[t as usize], elt::<Z1Coeff, D>(want), "coordinate {t}");
        }
        assert_eq!(
            aggregate_blocks(&alphas, &blocks, &mask[..3], 4),
            Err(MaskError::Ragged {
                got: 3,
                expected: 4
            })
        );
        assert_eq!(
            linear_form(&alphas, &vals[..2]),
            Err(MaskError::LengthMismatch { left: 3, right: 2 })
        );
        assert_eq!(
            rejection_accept(&[1, 2], &[1], 5, 1, 0),
            Err(MaskError::LengthMismatch { left: 2, right: 1 })
        );
        assert_eq!(
            rejection_accept(&[1], &[1], 0, 1, 0),
            Err(MaskError::BadWidth)
        );
    }

    #[test]
    fn the_value_mask_sampler_is_uniform_over_the_field() {
        // A sampler that quietly fell back to a bounded set would break the
        // exact hiding above, so pin the drawn distribution down too.
        let n = 5000usize;
        let s = MaskShape::new(1, 1, n, 1).expect("wide shape");
        let g = sample_masks::<Tiny, 1>(&s, &[2u8; 32]);
        assert_eq!(g.len(), 1);
        let flat: Vec<Tiny> = g[0].iter().map(|e| e.coefficients()[0]).collect();
        let mut counts = vec![0u64; 5];
        for v in flat.iter() {
            counts[v.to_u128() as usize] += 1;
        }
        for c in counts.iter() {
            assert!(
                *c > (n as u64) / 5 - 200 && *c < (n as u64) / 5 + 200,
                "the uniform mask sampler is skewed: {counts:?}"
            );
        }
        // bucket_counts must put each of -2..2 in its own bucket
        let spread: Vec<Z1Coeff> = (-2..=2)
            .flat_map(|v| std::iter::repeat_n(from_centered::<Z1Coeff>(v), 10))
            .collect();
        assert_eq!(bucket_counts(&spread, 5, 3), vec![10u64; 5]);
        // and out-of-window values pile into an end bucket rather than panicking
        let outside = vec![
            from_centered::<Z1Coeff>(100),
            from_centered::<Z1Coeff>(-100),
        ];
        let edges = bucket_counts(&outside, 4, 10);
        assert_eq!(edges[0] + edges[3], 2, "both extremes land on an edge");
        assert_eq!(edges[1] + edges[2], 0);
    }

    #[test]
    fn gaussian_block_covers_the_papers_shape() {
        let s = MaskShape::new(2, 3, 2, 2).expect("shape");
        let sigma = sigma_for(10, 1).expect("sigma");
        let plain = GaussianBlock::<Z1Coeff, D>::committed(&s, sigma, &[1u8; 32]).expect("sampled");
        assert_eq!(plain.committed.len(), s.aug_len());
        assert!(plain.randomness.is_empty());
        assert_eq!(plain.as_coeffs().len(), s.aug_len() * D);
        // µ + ν = 3 randomness rows per column, for a hiding base commitment
        let wide =
            GaussianBlock::<Z1Coeff, D>::with_randomness(&s, sigma, 3, &[1u8; 32]).expect("wide");
        assert_eq!(wide.randomness.len(), 3 * s.n0);
        assert_eq!(wide.as_coeffs().len(), (s.aug_len() + 3 * s.n0) * D);
        assert_eq!(wide.committed, plain.committed, "same seed, same block");
        assert_ne!(wide.randomness[0], plain.committed[0], "own domain label");
        assert!(
            wide.as_coeffs().iter().all(|c| c.abs() <= 12 * sigma),
            "the CDT is truncated at 12σ"
        );
        assert_eq!(gaussian_coeffs(1, 0, &[0u8; 32]), Err(MaskError::BadWidth));
        assert_eq!(
            gaussian_coeffs(1, MAX_SIGMA + 1, &[0u8; 32]),
            Err(MaskError::SigmaTooWide {
                sigma: MAX_SIGMA + 1
            })
        );
    }

    #[test]
    fn statistical_distance_is_the_usual_one() {
        assert_eq!(statistical_distance(&[5, 5], &[5, 5]).expect("d"), 0.0);
        assert_eq!(statistical_distance(&[10, 0], &[0, 10]).expect("d"), 1.0);
        assert!(
            (statistical_distance(&[10, 0], &[5, 5]).expect("d") - 0.5).abs() < 1e-12,
            "half the L1 mass difference"
        );
        assert_eq!(
            statistical_distance(&[1, 2], &[1]),
            Err(MaskError::LengthMismatch { left: 2, right: 1 })
        );
        assert_eq!(
            statistical_distance(&[0, 0], &[1, 1]),
            Err(MaskError::EmptySample)
        );
    }
}
