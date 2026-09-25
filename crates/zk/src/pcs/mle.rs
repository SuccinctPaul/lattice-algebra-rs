//! MLE/eq-weight opening mode (Z7, row 25 foundation): commit to a
//! scalar-coefficient vector once, later prove **arbitrary linear
//! evaluation claims** `y = ⟨w, F⟩` — power tables (point evaluations at
//! any `x`), eq tensors (multilinear evaluations), and range-check
//! functionals all instantiate.
//!
//! # Architecture (transparent by design)
//!
//! Unlike the √N-split Greyhound mode (whose weight tables must factor as
//! the outer product `aⱼ·bᵢ` — see [`crate::pcs::batched`] for why
//! arbitrary tables do not), this mode supports **non-factored** weight
//! tables with exact verification, at a documented cost:
//!
//! - the commitment key `A ∈ Z_q^{2L×L}` is **tall** (twice as many rows
//!   as columns), so `A·F = c` over-determines `F`: the system has the
//!   unique solution `F = A⁺·c` (full column rank w.h.p. for a random
//!   matrix over the prime field) — the claim verification is **exact**;
//! - the flip side: the commitment is **transparent (not hiding)** — the
//!   witness is recoverable by linear elimination, so this mode is the
//!   *claim-verification interface* the batching line composes against,
//!   not a hiding commitment. Hiding stays with the Greyhound mode.
//!
//! # Weighted claims
//!
//! For a weight table `w ∈ Z_q^L` (power table `w_j = xʲ`, eq tensor
//! `eq(r, ·)`, a range-check functional, …), the claim `y = ⟨w, F⟩` is
//! verified exactly against the recovered witness. Batches of claims
//! compose: `Σᵢ λᵢ·yᵢ == ⟨Σᵢ λᵢ·wᵢ, F⟩` for verifier-chosen `λ`.
//! # The compressed line: two levels and a Theseus-shaped response
//!
//! [`MleLevels`] adds the shape a *levelled* commitment has and the plain Σ
//! line does not: an inner commitment `tₖ = A·(column k)` compressed to
//! `t̂ₖ = ⌊tₖ/B_t⌉`, and an outer commitment `û = ⌊(D t̂)/B_u⌉` under a *second*
//! key `D` of the same family. The compression is not cosmetic — it is what
//! makes a response shortness gate sayable. On the tall key alone the
//! commitment of a witness is `A·F`, whose entries are field-sized, so any
//! bound that admits an honest transcript admits every vector of the same
//! length: the gate would be decoration. Compressing to `⌊·/B_t⌉` puts an
//! honest stack entry at `≈ q/(2B_t)` while a non-compressed one stays at
//! `≈ q/2`, and that gap is exactly what a verifier can enforce — which is
//! why Jindo's own outer bound is written `B_o = … + (q/B_t)√(μn₀d)`
//! (Theorem 5, p. 11) rather than in terms of the witness.
//!
//! [`MleQuadProof`] is the prover side of Fig. 7 of the same paper
//! (eprint 2026/044, p. 11): the inner triple `(f̂*, r, h)` with
//! `f̂* := F̂*c`, `r := Rc` and the residual `h` the *verifier* forms at line 5,
//! plus the outer pair `(s, t̂)` with `s := D t̂ − B_u û` from line 6, and the
//! first-message `zᵀ := v̂*₁ᵀ F̂*` of line 1.
//! [`MleLevels::quad_report`] gates the figure's four verifier lines as named
//! checks — [`QuadCheck::InnerNorm`] (7), [`QuadCheck::OuterNorm`] (8),
//! [`QuadCheck::Linearity`] (9, `v̂*₁ᵀf̂* = zᵀc`) and
//! [`QuadCheck::Evaluation`] (10, `zᵀŵ₀ = ŷ*`) — and returns the whole failing
//! set, because the four lines read different messages and a transcript can
//! break any one of them alone.
//!
//! [`QuadParams`] derives the thresholds from the instance instead of
//! accepting a constant: Theorem 3's base pair (p. 10), Theorem 5's
//! aggregation relaxation (p. 11) and Theorem 6's contraction (p. 12), with
//! the paper's `B`-on-both-sides notation resolved as a one-step relaxation
//! for the reason documented on the type.
//!
//! # The three matrices and the two moduli of Fig. 3's `Setup` (p. 8)
//!
//! `A ∈ R_q^{µ×(m₁+1)}`, `B := [B′ | I_µ] ∈ R_q^{µ×(µ+ν)}` and
//! `D ←$ R_{q_o}^{κ×µn₀}`: [`MleLevels`] holds all three, over **two** moduli —
//! [`Q_INNER`] for the inner level and [`Q_O`] for the outer one, each with its
//! own ring ([`InnerCoeff`] and [`OuterCoeff`]). Both shapes are load-bearing:
//!
//! * `B = [B′ | I_µ]` is what Theorem 2's hiding (proved at B.5, p. 18) is
//!   stated over. `tₖ = Af̂*ₖ + Brₖ` with `rₖ ← χ^{µ+ν}` reads `Af̂*ₖ + B′r̃ₖ + r̂ₖ`:
//!   the `B′` columns are the MLWE matrix, the split-off `r̂ₖ` its **error** term,
//!   and the pair is what makes `Brₖ` indistinguishable from uniform. Drop the
//!   identity block and the commitment degenerates to an error-free sample;
//!   drop `B′` and the noise alone (`‖r̂‖∞ ≤ B_χ ≪ B_t`) survives no rounding.
//!   [`MaskBlock::mask_hiding`] measures exactly that trade, and
//!   [`MleLevels::preimage_freedom`] counts the short preimages the shape
//!   leaves — zero for a tall injective key, positive here.
//! * `q_o ≠ q` is what makes the stack shift of Fig. 7 line 8 a *two-sided*
//!   escape: `t̂` must be re-shifted by a multiple of both moduli to keep the
//!   residues of lines 5 and 6 intact, so `lcm(q, q_o) = q·q_o` is the smallest
//!   integer that leaves both gates no choice but the norm.
//! * Because the *message* is no longer determined by the commitment,
//!   `quad_prove` takes the randomness rows as an **input** rather than reading
//!   them out of a recovered witness, and the [`MleKey::solve`] read-out stays
//!   what it always was: the plain Σ line's transparency, not this line's.
//!
//! [`OuterKey`] is where the second modulus is a *type* parameter rather than a
//! comment: the same `FlatKey<Q>` machinery serves both levels, so a scheme that
//! wants another `q_o` instantiates [`Q_O`] once and gets a distinct key, a
//! distinct reduction in line 6 and a distinct `MSIS_{q_o,κ,2B_αB_o}` in
//! [`QuadParams::outer_msis_headroom`].

use crate::foundation::sampling::from_centered;
use crate::pcs::masking;
use crate::pcs::{Z1Coeff, DELTA};
use crate::shortness::exact_l2;
use crate::shortness::projection::JLProjection;
use algebra::crypto::sampling::{sample_rej_bounded, sample_uniform_coeff, BitStream};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::traits::CenteredRing;
use algebra::ring::zq::Zq;
use algebra::ring::Ring;
use alloc::{vec, vec::Vec};

/// Domain label for the tall commitment-key expansion.
const KEY_DOMAIN: &[u8] = b"lattice-algebra/Z7/mle-key";

/// Domain label for the rectangular keys of Fig. 3's `Setup` (`A`, `B′`, `D`).
const FLAT_DOMAIN: &[u8] = b"lattice-algebra/Z7/mle-flat-key";

/// FS domain label shared by the prover and the verifier of the Σ opening.
/// Both sides derive the challenge through [`opening_challenge`], so the
/// transcript shape cannot drift apart.
const OPEN_DOMAIN: &[u8] = b"lattice-algebra/Z7/mle-open";

/// Converts a slice of scalars to LE bytes for transcript absorption.
fn scalar_bytes_le(v: &[Z1Coeff]) -> Vec<u8> {
    v.iter()
        .flat_map(|c| (c.to_u128() as u32).to_le_bytes())
        .collect()
}

/// The bounded-mask constant: `‖mask‖∞ ≤ 2^9`.
pub const MASK_BOUND: u32 = 1 << 9;

/// The Fiat–Shamir challenge of the Σ opening, bound to every public value
/// the verifier holds: the key seed, the commitment, the weight table, the
/// claimed value, and the first message.
fn opening_challenge(
    key: &MleKey,
    c: &MleCommitment,
    w: &[Z1Coeff],
    y: Z1Coeff,
    d: &[Z1Coeff],
) -> Z1Coeff {
    let mut tr = Transcript::<Shake256Xof>::new(OPEN_DOMAIN);
    tr.absorb(b"key", key.seed());
    tr.absorb(b"c", &scalar_bytes_le(&c.c));
    tr.absorb(b"w", &scalar_bytes_le(w));
    tr.absorb(b"y", &scalar_bytes_le(core::slice::from_ref(&y)));
    tr.absorb(b"d", &scalar_bytes_le(d));
    let seed = tr.challenge_bytes(8);
    let mut raw = [0u8; 8];
    raw.copy_from_slice(&seed[..8]);
    // Reduce into the scalar field; the transcript seed is uniform, so this
    // is a uniform field element up to a 2^-40 bias.
    Z1Coeff::from(u64::from_le_bytes(raw) % Z1Coeff::MODULUS)
}

/// A tall scalar commitment key `A ∈ Z_q^{2L×L}` (row-major, entries
/// rejection-sampled from a SHAKE-256 expansion of the seed over the Z1
/// prime).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MleKey {
    seed: [u8; 32],
    len: usize,
    entries: Vec<Z1Coeff>,
}

impl MleKey {
    /// Derives the key from a seed. Deterministic; `len` is the committed
    /// scalar-vector length.
    ///
    /// Entries are uniform on `[0, q)` from one SHAKE-256 stream over the
    /// full 32-byte seed (rejection-sampled so no modulus bias is
    /// introduced).
    pub fn setup(seed: &[u8; 32], len: usize) -> Self {
        assert!(len > 0, "committed length must be positive");
        let mut xof = Shake256Xof::new(KEY_DOMAIN);
        xof.absorb(seed);
        let mut stream = BitStream::new(&mut xof);
        let mut entries = Vec::with_capacity(2 * len * len);
        for _ in 0..2 * len * len {
            // Rejection sample at `ceil(log2 q)` bits: `q` is not a power of
            // two, so any shorter read would skew the leading residues, and
            // a 32-bit read would reject ~512 draws per accepted entry.
            let mut v = stream.read_bits(DELTA as u32) as u64;
            while v >= Z1Coeff::MODULUS {
                v = stream.read_bits(DELTA as u32) as u64;
            }
            entries.push(Z1Coeff::from(v));
        }
        MleKey {
            seed: *seed,
            len,
            entries,
        }
    }

    /// The binding master seed (Fiat–Shamir input).
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The committed length `L`.
    pub fn len(&self) -> usize {
        self.len
    }

    /// Whether the committed length is zero.
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// `A·v` — the commitment map (`2·len` scalars out).
    ///
    /// # Panics
    /// If `v.len() != len`.
    pub fn apply(&self, v: &[Z1Coeff]) -> Vec<Z1Coeff> {
        assert_eq!(v.len(), self.len, "mle map length mismatch");
        let mut out = vec![Z1Coeff::ZERO; 2 * self.len];
        for (i, row) in self.entries.chunks(self.len).enumerate() {
            let mut acc = Z1Coeff::ZERO;
            for (a, v_j) in row.iter().zip(v.iter()) {
                acc += *a * *v_j;
            }
            out[i] = acc;
        }
        out
    }

    /// Solves `A·x = c` for the unique witness (Gaussian elimination over
    /// the prime field). `None` if the system is inconsistent.
    pub fn solve(&self, c: &[Z1Coeff]) -> Option<Vec<Z1Coeff>> {
        if c.len() != 2 * self.len {
            return None;
        }
        let cols = self.len;
        let rows = 2 * self.len;
        let mut aug: Vec<Vec<Z1Coeff>> = (0..rows)
            .map(|i| {
                let mut row = self.entries[i * cols..(i + 1) * cols].to_vec();
                row.push(c[i]);
                row
            })
            .collect();
        let mut pivot_row = 0usize;
        #[allow(clippy::explicit_counter_loop)]
        for col in 0..cols {
            let pivot = (pivot_row..rows).find(|&r| aug[r][col] != Z1Coeff::ZERO)?;
            aug.swap(pivot_row, pivot);
            let inv = aug[pivot_row][col].inverse().expect("nonzero pivot");
            for v in aug[pivot_row].iter_mut() {
                *v *= inv;
            }
            let pivot_vals = aug[pivot_row].clone();
            for (r, row) in aug.iter_mut().enumerate() {
                if r != pivot_row && row[col] != Z1Coeff::ZERO {
                    let factor = row[col];
                    for (dst, pv) in row.iter_mut().zip(pivot_vals.iter()) {
                        *dst -= factor * pv;
                    }
                }
            }
            pivot_row += 1;
        }
        Some((0..cols).map(|i| aug[i][cols]).collect())
    }
}

/// The MLE commitment: `c = A·F` (`2·len` scalars).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MleCommitment {
    /// `A·F` — `2·len` scalars.
    pub c: Vec<Z1Coeff>,
}

/// Typed rejection for the MLE mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MleError {
    /// A vector had a length other than the canonical instance length.
    WrongLength,
    /// The system was inconsistent (the commitment is not binding for the
    /// supplied claim data).
    Inconsistent,
    /// A link equation failed (the claimed value doesn't match).
    LinkCheckFailed,
    /// A norm gate could not be decided — an accumulation left the integer
    /// window, or a compression factor did not fit the field's representative.
    /// Refusal, never a pass: see [`crate::shortness::exact_l2`]'s same rule.
    NormUndecidable,
}

/// Commits to the scalar vector `F` (length `len`).
pub fn commit_mle(key: &MleKey, f: &[Z1Coeff]) -> Result<MleCommitment, MleError> {
    if f.len() != key.len() {
        return Err(MleError::WrongLength);
    }
    Ok(MleCommitment { c: key.apply(f) })
}

/// The weighted evaluation `y = ⟨w, F⟩` of the committed witness.
pub fn claim(key: &MleKey, c: &MleCommitment, w: &[Z1Coeff]) -> Result<Z1Coeff, MleError> {
    let f = key.solve(&c.c).ok_or(MleError::Inconsistent)?;
    let mut y = Z1Coeff::ZERO;
    for (w_j, f_j) in w.iter().zip(f.iter()) {
        y += *w_j * *f_j;
    }
    Ok(y)
}

/// Recovers the committed witness (the transparent mode's read-out).
pub fn witness_of(key: &MleKey, c: &MleCommitment) -> Option<Vec<Z1Coeff>> {
    key.solve(&c.c)
}

/// The Σ opening: proves `⟨w, F⟩ = y` against the commitment `c = A·F`.
///
/// Protocol: bounded mask, challenge `X` from the transcript, response
/// `z = mask + X·F`. Checks: `A·z == d + X·c` (overdetermined link) and
/// `⟨w, z⟩ == t + X·y` (weighted claim, exact over the prime field).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MleOpenProof {
    /// `A·mask` — the mask commitment (first message).
    pub d: Vec<Z1Coeff>,
    /// `z = mask + X·F` — the masked response.
    pub z: Vec<Z1Coeff>,
    /// `⟨w, mask⟩` — the mask's weighted value.
    pub t: Z1Coeff,
}

/// Prover: bounded mask, challenge from transcript, response `z`.
pub fn open_mle_proof(
    key: &MleKey,
    f: &[Z1Coeff],
    w: &[Z1Coeff],
    mask_seed: &[u8; 32],
) -> Result<MleOpenProof, MleError> {
    if f.len() != key.len() || w.len() != f.len() {
        return Err(MleError::WrongLength);
    }
    // The public statement, recomputed from the witness so the challenge
    // binds exactly what the verifier will hold.
    let c = MleCommitment { c: key.apply(f) };
    let mut y = Z1Coeff::ZERO;
    for (w_j, f_j) in w.iter().zip(f.iter()) {
        y += *w_j * *f_j;
    }

    // Bounded mask, **centered** in [-MASK_BOUND, MASK_BOUND]: taking only
    // the absolute value would make the mask non-symmetric and stop it from
    // masking the witness.
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(b"mle-mask");
    xof.absorb(mask_seed);
    let mut stream = BitStream::new(&mut xof);
    let mask: Vec<Z1Coeff> = (0..key.len())
        .map(|_| from_centered::<Z1Coeff>(sample_rej_bounded::<Z1Coeff>(&mut stream, MASK_BOUND)))
        .collect();
    let d = key.apply(&mask);

    let x = opening_challenge(key, &c, w, y, &d);

    // response: z = mask + X·F
    let z: Vec<Z1Coeff> = mask
        .iter()
        .zip(f.iter())
        .map(|(m, f_j)| *m + x * *f_j)
        .collect();

    // t = ⟨w, mask⟩
    let mut t = Z1Coeff::ZERO;
    for (w_j, m_j) in w.iter().zip(mask.iter()) {
        t += *w_j * *m_j;
    }

    Ok(MleOpenProof { d, z, t })
}

/// Verifier: checks the overdetermined link and the weighted claim.
///
/// Check 1: `A·z == d + X·c` — the response is consistent with the
/// commitment (overdetermined: 2L constraints on L unknowns).
/// Check 2: `⟨w, z⟩ == t + X·y` — the weighted claim.
pub fn verify_mle_proof(
    key: &MleKey,
    c: &MleCommitment,
    w: &[Z1Coeff],
    claimed_y: Z1Coeff,
    proof: &MleOpenProof,
) -> Result<(), MleError> {
    if w.len() != key.len() || proof.d.len() != 2 * key.len() || proof.z.len() != key.len() {
        return Err(MleError::WrongLength);
    }
    // derive the same challenge — one shared path with the prover
    let x = opening_challenge(key, c, w, claimed_y, &proof.d);

    // check 1: link
    let az = key.apply(&proof.z);
    for (i, az_i) in az.iter().enumerate() {
        let rhs = proof.d[i] + c.c[i] * x;
        if *az_i != rhs {
            return Err(MleError::LinkCheckFailed);
        }
    }

    // check 2: weighted claim
    let mut lhs = Z1Coeff::ZERO;
    for (w_j, z_j) in w.iter().zip(proof.z.iter()) {
        lhs += *w_j * *z_j;
    }
    let rhs = proof.t + x * claimed_y;
    if lhs != rhs {
        return Err(MleError::LinkCheckFailed);
    }
    Ok(())
}

/// The JL shortness certificate for a claimed-bounded witness: the
/// committed witness's `l2` norm is certified against
/// `⌈√(128/30)·B⌉` (see [`crate::shortness::projection`]).
///
/// The `l2` test on the projected image is the whole certificate; there is
/// no extra coordinate-wise gate, since an arbitrary `l∞` prefilter would
/// only reject honest witnesses without strengthening the bound.
pub fn certify_l2(proj: &JLProjection, witness: &[Z1Coeff], claimed_bound: u64) -> bool {
    if claimed_bound == 0 {
        return false;
    }
    let flat: Vec<i64> = witness.iter().map(|v| v.centered()).collect();
    let response = proj.project(&flat);
    let k = proj.rows() as u128;
    let b = u128::from(claimed_bound);
    let square: u128 = response
        .iter()
        .map(|v| {
            let a = u128::from(v.unsigned_abs());
            a * a
        })
        .sum();
    square <= k * b * b
}

/// One public claim against a single commitment: a weight table and the
/// value asserted for it.
#[derive(Debug, Clone, Copy)]
pub struct WeightClaim<'a> {
    /// The weight table `wᵢ`.
    pub weight: &'a [Z1Coeff],
    /// The asserted value `yᵢ = ⟨wᵢ, F⟩`.
    pub value: Z1Coeff,
}

/// FS domain label for the multi-claim combination.
const BATCH_DOMAIN: &[u8] = b"lattice-algebra/Z7/mle-batch";

/// Reduces `k` weight-table claims to the single claim
/// `(Σ γⁱ·wᵢ, Σ γⁱ·yᵢ)` the opening proves.
///
/// The combining challenge `γ` is a Fiat–Shamir output over the **public**
/// statement `(key, c, {wᵢ}, {yᵢ})`, so it is fixed before the prover acts
/// and cannot be chosen to make a false combination true. A claim set with
/// any false entry then forces a false combined claim, at the price of one
/// Schwartz–Zippel factor over the `γ` draw — the same accounting
/// [`crate::sumcheck::batch`] documents for its γ-power weights.
pub fn combined_claim(
    key: &MleKey,
    com: &MleCommitment,
    claims: &[WeightClaim<'_>],
) -> Result<(Vec<Z1Coeff>, Z1Coeff), MleError> {
    if claims.is_empty() {
        return Err(MleError::WrongLength);
    }
    let len = key.len();
    for claim in claims {
        if claim.weight.len() != len {
            return Err(MleError::WrongLength);
        }
    }
    let mut tr = Transcript::<Shake256Xof>::new(BATCH_DOMAIN);
    tr.absorb(b"key", key.seed());
    tr.absorb(b"c", &scalar_bytes_le(&com.c));
    for claim in claims {
        tr.absorb(b"w", &scalar_bytes_le(claim.weight));
        tr.absorb(b"y", &scalar_bytes_le(core::slice::from_ref(&claim.value)));
    }
    let seed = tr.challenge_bytes(8);
    let mut raw = [0u8; 8];
    raw.copy_from_slice(&seed[..8]);
    let gamma = Z1Coeff::from(u64::from_le_bytes(raw) % Z1Coeff::MODULUS);

    let mut combined = vec![Z1Coeff::ZERO; len];
    let mut value = Z1Coeff::ZERO;
    let mut weight_gamma = Z1Coeff::ONE;
    for claim in claims {
        for (acc, w) in combined.iter_mut().zip(claim.weight.iter()) {
            *acc += weight_gamma * *w;
        }
        value += weight_gamma * claim.value;
        weight_gamma *= gamma;
    }
    Ok((combined, value))
}

/// Proves all `claims` against the commitment to `f` with **one** opening.
pub fn open_claims(
    key: &MleKey,
    f: &[Z1Coeff],
    claims: &[WeightClaim<'_>],
    mask_seed: &[u8; 32],
) -> Result<MleOpenProof, MleError> {
    let com = commit_mle(key, f)?;
    let (combined, _) = combined_claim(key, &com, claims)?;
    open_mle_proof(key, f, &combined, mask_seed)
}

/// Verifier: folds the claimed tables by the transcript-derived `γ`, then
/// checks the single opening against the combined claim.
pub fn batch_verify(
    key: &MleKey,
    com: &MleCommitment,
    claims: &[WeightClaim<'_>],
    proof: &MleOpenProof,
) -> Result<(), MleError> {
    let (combined, value) = combined_claim(key, com, claims)?;
    verify_mle_proof(key, com, &combined, value, proof)
}

// ---------------------------------------------------------------------------
// The compressed line: a *two-level* commitment and the Theseus-shaped Σ
// response over it (Jindo eprint 2026/044, Fig. 3 pp. 8–9 and Fig. 7 p. 11).
// ---------------------------------------------------------------------------

/// `⌊a/b⌉` — the nearest integer to `a/b`, ties rounding up, for the rounding
/// steps of Jindo Fig. 3's `Com*` (p. 9): `t̂ₖ = ⌊tₖ/B_t⌉` and
/// `û = ⌊(D t̂)/B_u⌉`.
///
/// The input `a` is expected to be the **centered** representative of a
/// residue, which is what makes the *output* short: with `a ∈ (−q/2, q/2]` and
/// `b ≥ 1` the result is bounded by `q/b + 1`. That bound is the whole reason
/// the gates of Fig. 7 lines 7–8 can say anything at all — B.6 (p. 18) gets
/// `‖t̂‖∞ ≤ q/B_t` and `‖s‖∞ ≤ B_u` "by the rounding definitions", and
/// Theorem 5's `B_o = m₀B_C B_o + B_u√(κd) + (q/B_t)√(μn₀d)` (p. 11) is the sum
/// of exactly those two terms plus the aggregation slack. With `b = 1` nothing
/// is compressed, `q/b = q`, and the outer gate turns vacuous: this helper is
/// where the choice of `B_t` earns its keep.
#[must_use]
pub fn round_div(a: i64, b: u64) -> i64 {
    let b = i64::try_from(b).unwrap_or(i64::MAX);
    debug_assert!(b > 0, "a compression factor of zero is not rounding");
    let q = a.div_euclid(b);
    let r = a.rem_euclid(b);
    // `0 ≤ r < b`, so `r ≥ b − r` is the tie-going-up rule `2r ≥ b` written
    // without a multiply that could overflow.
    if r >= b - r {
        q + 1
    } else {
        q
    }
}

/// Lifts integer coordinates into the scalar field through the centered
/// representative (§3.1, p. 6: "`Z ∩ (−q/2, q/2]` as a representative set").
fn ints_to_field(v: &[i64]) -> Vec<Z1Coeff> {
    v.iter().map(|&x| from_centered::<Z1Coeff>(x)).collect()
}

/// Lifts a field vector to its centered integer representatives.
fn ints_of(v: &[Z1Coeff]) -> Vec<i64> {
    v.iter().map(Z1Coeff::centered).collect()
}

/// The inner modulus `q` of Fig. 3's `Setup` (p. 8) — the one the levelled
/// commitments `tₖ` and the residual `h` of Fig. 7 line 5 live in.
pub const Q_INNER: u64 = Z1Coeff::MODULUS;

/// The coefficients of the inner level: `Z_q`.
pub type InnerCoeff = Zq<Q_INNER>;

/// The outer modulus `q_o` of Fig. 3's `Setup` (p. 8) — a *second*, smaller
/// prime, listed among `q, q_o, B_t, B_u ∈ Z_{>0}` and carrying `D` (p. 8),
/// `u = D t̂ (mod q_o)` and `s := D t̂ − B_u α û (mod q_o)` (Fig. 3 `Open*` step
/// 3, p. 9), and named by Theorem 1's `MSIS_{q_o,κ,2B_αB_o}` (p. 10).
///
/// # How the value was picked, and what the instance needs from it
///
/// §5.1 (p. 12) asks for `2d ∣ q_o − 1` beside `2d ∣ q − 1` so both levels
/// support an NTT; here `d = 1` and the toy takes `q_o ≡ 1 (mod 4096)` anyway,
/// which is what `q = 8380417 = 2046·4096 + 1` itself satisfies. Beyond that
/// the figure imposes an ordering, and it is the one the paper explains at
/// p. 9: Jindo compresses `tₖ` to `t̂ₖ = ⌊tₖ/B_t⌉` *before* committing again,
/// "since each entry of `t̂ₖ` is now bounded by roughly `q/B_t`, which permits a
/// smaller `q_o` while the column dimension of `D` remains `µn₀`". So:
///
/// * `q_o < q` — the whole point of the level. `4206593 = 1027·4096 + 1` is
///   about `q/2`, which is what this *toy* can use; see
///   [`QuadParams::outer_msis_headroom`] for the measurement of how much of
///   that headroom `B_o` eats.
/// * `q_o > B_u` by a wide margin, or `û = ⌊u/B_u⌉` compresses to one bit and
///   line 6 stops being a commitment.
/// * `q_o` prime, so `Z_{q_o}` is a field and the rejection sampler below is
///   unbiased.
///
/// The last condition is what makes this a *reportable* finding rather than a
/// free parameter: the sampler reads `⌈log₂ q_o⌉` bits per entry, and the
/// module's own `DELTA = 23` (the bit length of `q`) is the ceiling a
/// `u32`-encodable prime can have here and still be drawn by the fixed-width
/// path. `4206593` needs 23 bits, so the instance is *exactly* at that ceiling
/// — a `q_o` above `2²³` would need the byte-wise [`sample_uniform_coeff`]
/// path [`OuterKey`] uses, and a `q_o` above `2³²` would stop fitting the
/// `u32` encoding the transcript absorbs. Both are asserted below rather than
/// assumed.
pub const Q_O: u64 = 4_206_593;

/// The coefficients of the outer level: `Z_{q_o}`, a ring *distinct* from
/// [`InnerCoeff`] (`q_o ≠ q`, and neither divides the other).
pub type OuterCoeff = Zq<Q_O>;

/// The inner ring is a field: `solve`, the challenge sets and the centered
/// representative all assume inverses exist.
const _: () = assert!(InnerCoeff::IS_PRIME, "q must be prime");
/// Same for the outer level — `D` is sampled uniformly mod `q_o` by rejection,
/// which is unbiased only over a field.
const _: () = assert!(OuterCoeff::IS_PRIME, "q_o must be prime");
const _: () = assert!(Q_O < Q_INNER, "q_o is the *smaller* modulus (p. 9)");
const _: () = assert!(Q_O > 2 * crate::pcs::mle::MIN_BUDGET, "q_o must be odd");
/// The transcript encodes residues as `u32`, so a modulus above `2³²` would be
/// silently truncated. This is the `u32`-encodability the instance needs.
const _: () = assert!(Q_O < (1 << 32), "q_o must be u32-encodable");
const _: () = assert!(Q_O < (1 << 53), "rounding residuals are added in i64");

/// A lower bound on `q_o/2` that any instance this module serves must clear, so
/// the const assertion above can state the *shape* of the requirement without
/// hard-coding one scheme's `B_o`. See
/// [`QuadParams::outer_msis_headroom`] for the measured value.
pub const MIN_BUDGET: u64 = 1 << 18;

/// A uniform `rows × cols` matrix over `Z_Q`, expanded from a seed by
/// rejection sampling — the shape every matrix of Fig. 3's `Setup` (p. 8) has.
///
/// [`MleKey`] cannot stand in for it: it is *tall by construction*
/// (`2L × L`, full column rank), and that is precisely the property Theorem 2
/// has to give up. A commitment `tₖ = A·(column k)` under a tall `A` determines
/// its message (`A::solve` reads it back), which is transparency, not hiding.
/// Fig. 3's `A ∈ R_q^{µ×(m₁+1)}` has `µ` rows and `m₁+1` columns with
/// `m₁+1+µ+ν > µ` input coordinates once `B = [B′|I_µ]` is appended, so the
/// combined map has a kernel and the message is *not* determined — see
/// [`MleLevels::preimage_freedom`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FlatKey<const Q: u64> {
    rows: usize,
    cols: usize,
    entries: Vec<Zq<Q>>,
}

impl<const Q: u64> FlatKey<Q> {
    /// Derives a `rows × cols` key from a seed, domain-separated by `tag` so
    /// two keys of the same shape and the same seed are still independent.
    ///
    /// Entries are uniform on `[0, Q)`, drawn by [`sample_uniform_coeff`]'s
    /// byte-wise rejection (correct for any `Q ≤ u64::MAX`, so the outer level
    /// is not limited to the inner level's `DELTA`).
    ///
    /// # Panics
    /// If either dimension is zero.
    pub fn new(tag: &[u8], seed: &[u8; 32], rows: usize, cols: usize) -> Self {
        assert!(rows > 0 && cols > 0, "a key with a zero side has no rows");
        let mut xof = Shake256Xof::new(FLAT_DOMAIN);
        xof.absorb(tag);
        xof.absorb(seed);
        xof.absorb(&(rows as u64).to_le_bytes());
        xof.absorb(&(cols as u64).to_le_bytes());
        let mut stream = BitStream::new(&mut xof);
        let entries = (0..rows * cols)
            .map(|_| sample_uniform_coeff::<Zq<Q>>(&mut stream))
            .collect();
        Self { rows, cols, entries }
    }

    /// `µ` (or `κ`, for the outer key): the output dimension.
    pub fn rows(&self) -> usize {
        self.rows
    }

    /// The input dimension: `m₁+1` for `A`, `ν` for `B′`, `µn₀` for `D`.
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// `M·v`.
    ///
    /// # Panics
    /// If `v.len() != cols`.
    pub fn apply(&self, v: &[Zq<Q>]) -> Vec<Zq<Q>> {
        assert_eq!(v.len(), self.cols, "flat key application length");
        let mut out = vec![Zq::<Q>::ZERO; self.rows];
        for (i, row) in self.entries.chunks(self.cols).enumerate() {
            let mut acc = Zq::<Q>::ZERO;
            for (a, v_j) in row.iter().zip(v.iter()) {
                acc += *a * *v_j;
            }
            out[i] = acc;
        }
        out
    }

    /// Column `j` of the matrix, gathered from the row-major storage.
    ///
    /// # Panics
    /// If `j ≥ cols`.
    pub fn column(&self, j: usize) -> Vec<Zq<Q>> {
        assert!(j < self.cols, "column {j} outside {}", self.cols);
        self.entries
            .chunks(self.cols)
            .map(|row| row[j])
            .collect()
    }

    /// The entry at row `i`, column `j`.
    ///
    /// # Panics
    /// If either index is out of range.
    pub fn entry(&self, i: usize, j: usize) -> Zq<Q> {
        assert!(i < self.rows && j < self.cols, "flat key index");
        self.entries[i * self.cols + j]
    }

    /// `rank` of the matrix over `Z_Q` (`Q` prime), by Gaussian elimination.
    #[must_use]
    pub fn rank(&self) -> usize {
        let mut aug: Vec<Vec<Zq<Q>>> = self
            .entries
            .chunks(self.cols)
            .map(|row| row.to_vec())
            .collect();
        let mut pivot_row = 0usize;
        for col in 0..self.cols {
            if pivot_row >= self.rows {
                break;
            }
            let Some(p) = (pivot_row..self.rows).find(|&r| aug[r][col] != Zq::<Q>::ZERO) else {
                continue;
            };
            aug.swap(pivot_row, p);
            let inv = aug[pivot_row][col]
                .inverse()
                .expect("a prime field inverts every non-zero pivot");
            for v in aug[pivot_row].iter_mut() {
                *v *= inv;
            }
            let piv = aug[pivot_row].clone();
            for (r, row) in aug.iter_mut().enumerate() {
                if r != pivot_row && row[col] != Zq::<Q>::ZERO {
                    let f = row[col];
                    for (dst, pv) in row.iter_mut().zip(piv.iter()) {
                        *dst -= f * *pv;
                    }
                }
            }
            pivot_row += 1;
        }
        pivot_row
    }
}

/// The inner level's key `A ∈ R_q^{µ×(m₁+1)}` (Fig. 3 `Setup`, p. 8).
pub type InnerKey = FlatKey<Q_INNER>;

/// The outer level's key `D ←$ R_{q_o}^{κ×µn₀}` — the *same* machinery over the
/// **second** modulus, which is what makes `q_o` a parameter of the instance
/// rather than a comment.
pub type OuterKey = FlatKey<Q_O>;

/// Fig. 3's `B := [B′ | I_µ] ∈ R_q^{µ×(µ+ν)}` (p. 8), the masking block of
/// Theorem 2's hiding proof (B.5, p. 18).
///
/// The split it forces on the randomness is the point: with
/// `rₖ ∈ R^{µ+ν}` the product is
///
/// ```text
/// B·rₖ  =  B′·r̃ₖ  +  r̂ₖ          r̃ₖ ∈ R^ν  the first ν entries
///                                   r̂ₖ ∈ R^µ  the last µ entries
/// ```
///
/// i.e. an MLWE sample with matrix `B′`, `ν` secrets and **error `r̂ₖ`**. B.5
/// reads it exactly that way ("under the hardness of MLWE_{q,ν,χ}, the term
/// `Brₖ` is computationally indistinguishable from a uniformly random element
/// of `R_q^µ`"), and `ν` — not `µ+ν` — is the MLWE dimension Theorem 2 names.
/// The identity block is what supplies the error: without it `B′r̃ₖ` is an
/// *error-free* sample, a different distribution with a far smaller support for
/// a small `χ`; with `ν = 0` there is no `B′` at all and `tₖ = Af̂*ₖ + r̂ₖ`
/// differs from the message by an entrywise `≤ B_χ` bump, which the compression
/// `⌊·/B_t⌉` erases outright. [`Self::mask_hiding`] measures both degenerations
/// against the uniform side of B.5's statement.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MaskBlock {
    mu: usize,
    nu: usize,
    b_prime: InnerKey,
}

impl MaskBlock {
    /// Derives `B′ ←$ R_q^{µ×ν}` from a seed; `I_µ` needs no seed.
    ///
    /// `nu = 0` is legal and means the degenerate `B = [I_µ]`, so that the
    /// measurement below can *show* what the `B′` block buys instead of
    /// asserting it. (The storage keeps one column either way — `FlatKey`
    /// refuses a zero side — and [`Self::apply`] never reads it at `ν = 0`.)
    ///
    /// # Panics
    /// If `mu == 0`.
    pub fn new(seed: &[u8; 32], mu: usize, nu: usize) -> Self {
        assert!(mu > 0, "B has µ rows");
        let b_prime = FlatKey::new(b"mle-b-prime", seed, mu, if nu == 0 { 1 } else { nu });
        Self { mu, nu, b_prime }
    }

    /// `µ`, the identity block's size and the commitment's height.
    #[must_use]
    pub fn mu(&self) -> usize {
        self.mu
    }

    /// `ν`, the MLWE dimension of Theorem 2's `MLWE_{q,ν,χ}`.
    #[must_use]
    pub fn nu(&self) -> usize {
        self.nu
    }

    /// `µ + ν`, the width of every `rₖ` (Fig. 3 `Com*` step 2 samples
    /// `R = [r₀|…|r_{n₀−1}] ←$ χ^{(µ+ν)×n₀}`, p. 9).
    #[must_use]
    pub fn width(&self) -> usize {
        self.mu + self.nu
    }

    /// `B·r` for `r ∈ R^{µ+ν}`: the `B′` part on the first `ν` entries, the
    /// identity on the last `µ`.
    ///
    /// # Panics
    /// If `r.len() != µ + ν`.
    pub fn apply(&self, r: &[InnerCoeff]) -> Vec<InnerCoeff> {
        assert_eq!(r.len(), self.width(), "B takes µ+ν entries");
        let mut out = if self.nu > 0 {
            self.b_prime.apply(&r[..self.nu])
        } else {
            vec![InnerCoeff::ZERO; self.mu]
        };
        for (o, e) in out.iter_mut().zip(&r[self.nu..]) {
            *o += *e;
        }
        out
    }

    /// B.5's hiding term, measured rather than assumed.
    ///
    /// `trials` draws of `r ← χ^{µ+ν}` (χ the entrywise-`b_chi` centered ball —
    /// the same `χ` Theorem 3's `‖r‖₁ ≤ B_χ` speaks of, p. 10), each turned into
    /// `⌊(B·r)/b_t⌉`: the *rounded* value the commitment actually publishes,
    /// because it is the rounding that can erase a mask. The histogram is
    /// bucketed over the rounded window by the shared [`crate::pcs::masking`]
    /// counters and compared against the same rounding of a uniform element of
    /// `R_q^µ` — B.5's left- and right-hand side.
    ///
    /// A small distance is *sufficient* for the statement and never necessary
    /// (MLWE is a computational hypothesis, so no histogram can certify it),
    /// but it is what separates the three shapes: at `ν = 0` the mask is
    /// `≪ B_t` wide, i.e. absent after rounding, and the measured distance is
    /// `≈ 1`.
    #[must_use]
    pub fn mask_hiding(
        &self,
        b_chi: u64,
        b_t: u64,
        trials: usize,
        bins: usize,
        seed: &[u8; 32],
    ) -> MaskHiding {
        let window = (i128::from(Q_INNER) / 2 / i128::from(b_t.max(1))) as i64;
        let mut xof = Shake256Xof::new(b"mle-mask-hiding");
        xof.absorb(seed);
        xof.absorb(&(self.nu as u64).to_le_bytes());
        xof.absorb(&b_chi.to_le_bytes());
        let mut stream = BitStream::new(&mut xof);
        let width = self.width();
        let mut masked: Vec<InnerCoeff> = Vec::with_capacity(trials * self.mu);
        let mut reference: Vec<InnerCoeff> = Vec::with_capacity(trials);
        let mut zero_noise = 0usize;
        for _ in 0..trials {
            let r: Vec<InnerCoeff> = (0..width)
                .map(|_| {
                    from_centered::<InnerCoeff>(sample_rej_bounded::<InnerCoeff>(
                        &mut stream,
                        u32::try_from(b_chi).unwrap_or(u32::MAX),
                    ))
                })
                .collect();
            let rounded: Vec<i64> = self
                .apply(&r)
                .iter()
                .map(|c| round_div(c.centered(), b_t))
                .collect();
            // `B·r = 0` is the event under which the published stack *is*
            // `⌊Af̂*ₖ/B_t⌉`: the message, uncompressed.
            if rounded.iter().all(|&x| x == 0) {
                zero_noise += 1;
            }
            masked.extend(rounded.iter().map(|&x| from_centered::<InnerCoeff>(x)));
            reference.push(from_centered::<InnerCoeff>(round_div(
                sample_uniform_coeff::<InnerCoeff>(&mut stream).centered(),
                b_t,
            )));
        }
        let mine = masking::bucket_counts(&masked, bins, window);
        let theirs = masking::bucket_counts(&reference, bins, window);
        let sd_vs_uniform = masking::statistical_distance(&mine, &theirs).unwrap_or(1.0);
        let mut sorted = masked.clone();
        sorted.sort_unstable();
        sorted.dedup();
        MaskHiding {
            nu: self.nu,
            trials,
            bins,
            sd_vs_uniform,
            distinct: sorted.len(),
            zero_noise,
        }
    }
}

/// What [`MaskBlock::mask_hiding`] measured, kept as a type so a scheme prints
/// the numbers instead of recomputing them.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct MaskHiding {
    /// The `ν` the block was built at.
    pub nu: usize,
    /// Draws pooled into the histogram.
    pub trials: usize,
    /// Buckets each histogram used.
    pub bins: usize,
    /// `½·Σ|p − p_uniform|` over the rounded window: B.5's distance, measured.
    pub sd_vs_uniform: f64,
    /// Distinct rounded values the mask took — its *statistical* support.
    pub distinct: usize,
    /// Draws with `B·r = 0`, the event that hands the verifier `⌊Af̂*ₖ/B_t⌉`.
    pub zero_noise: usize,
}

/// The two commitment levels of Jindo Fig. 3's `Setup` (p. 8) and `Com*`'s
/// steps 3–4 (p. 9), on the paper's own shapes.
///
/// ```text
/// tₖ  = A·f̂*ₖ + B·rₖ  (mod q)      A ∈ R_q^{µ×(m₁+1)},  B = [B′ | I_µ]
/// t̂ₖ  = ⌊tₖ/B_t⌉ ,   t̂ = t̂₀‖…‖t̂_{n₀−1} ∈ R^{µn₀}
/// û   = ⌊(D t̂)/B_u⌉  ∈ R^κ          D ∈ R_{q_o}^{κ×µn₀}
/// ```
///
/// with `s := D t̂ − B_u û (mod q_o)` the outer rounding residual (Fig. 7 line 6,
/// the only line whose arithmetic changes when `q_o ≠ q`) and
/// `h := A f̂* + B r − B_t Ťc (mod q)` the inner one (line 5). Both are
/// *verifier-side* quantities — Fig. 7 prints lines 5 and 6 in the verifier's
/// column — which is why [`MleQuadProof`] carries only what the prover sends.
///
/// # What this base reproduces, exactly
///
/// * The paper's `A` is one matrix applied to *each* of the `n₀` columns, and so
///   is [`InnerKey`] here, column by column. Committing a contracted column and
///   contracting commitments are therefore the same linear map, which is what
///   makes `h` a pure rounding residual rather than a shape artefact — and it is
///   why the *per-column* stack is needed at all: a key that mixed the `n₀`
///   columns could not express `Ťc`.
/// * `B = [B′ | I_µ]` is [`MaskBlock`]: a *separate* matrix whose identity block
///   supplies the MLWE error term B.5 (p. 18) hides with. The consequence for
///   this type is structural, not cosmetic — `[A | B]` is
///   `µ × (m₁+1+µ+ν)`, wider than tall, so the levelled commitment does not
///   determine its message and [`MleLevels::preimage_freedom`] is positive. That
///   is why [`MleLevels::quad_prove`] is *given* the augmented matrix instead of
///   solving for one, and why the `û` the gates read has to travel with the
///   instance. The plain Σ line keeps its own, transparent [`MleKey`].
/// * `q_o` is [`Q_O`]: a second prime with a second ring ([`OuterCoeff`]), so
///   line 6 reduces where line 5 does not, and a stack entry can only slip past
///   both gates by a multiple of `q·q_o`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MleLevels {
    /// `A`: `µ` rows, `m₁+1` columns, applied per matrix column.
    a: InnerKey,
    /// `B = [B′ | I_µ]`.
    mask: MaskBlock,
    /// `D`: `κ` rows, `µ·n₀` columns, over `Z_{q_o}`.
    outer: OuterKey,
    /// `n₀`, the columns of the augmented matrix — and the length of the
    /// challenge `c` of Fig. 7 line 2.
    cols: usize,
    /// `B_t`, the inner compression factor.
    b_t: u64,
    /// `B_u`, the outer compression factor.
    b_u: u64,
    /// How many leading rows of `f̂*` the gates measure, and the same number the
    /// bounds count. `m₁ + 1` (every row of `F̂*`) is the paper's reading; a base
    /// carrying an unshortenable row — the value mask of `examples/jindo.rs`,
    /// uniform over `Z_p` with `p = q` — sets it to the rows it can bound
    /// instead, and both sides move together.
    counted_rows: usize,
}

impl MleLevels {
    /// Builds the three matrices of Fig. 3's `Setup` from their own seeds.
    ///
    /// `shape` is the instance's `(µ, ν, m₁+1, n₀, counted_rows, B_t, B_u)`; a
    /// `counted_rows` above `m₁+1` is refused, because the gates would then
    /// measure rows `F̂*` does not have.
    ///
    /// # Panics
    /// As [`Shape::validate`].
    #[must_use]
    pub fn new(seed_a: &[u8; 32], seed_b: &[u8; 32], seed_d: &[u8; 32], shape: &Shape) -> Self {
        shape.validate();
        Self {
            a: FlatKey::new(b"mle-a", seed_a, shape.mu, shape.aug_rows),
            mask: MaskBlock::new(seed_b, shape.mu, shape.nu),
            outer: FlatKey::new(
                b"mle-d",
                seed_d,
                2 * shape.mu * shape.cols,
                shape.mu * shape.cols,
            ),
            cols: shape.cols,
            b_t: shape.b_t,
            b_u: shape.b_u,
            counted_rows: shape.counted_rows,
        }
    }

    /// `µ`, the entries one column commitment `tₖ` carries.
    #[must_use]
    pub fn mu(&self) -> usize {
        self.a.rows()
    }

    /// `ν`, the MLWE dimension of `B = [B′ | I_µ]` — the `ν` of Theorem 2's
    /// `MLWE_{q,ν,χ}`.
    #[must_use]
    pub fn nu(&self) -> usize {
        self.mask.nu()
    }

    /// `κ`, the entries of one outer commitment `û`.
    #[must_use]
    pub fn kappa(&self) -> usize {
        self.outer.rows()
    }

    /// `µ + ν`, the randomness rows per column (Fig. 3 `Com*` step 2, p. 9).
    #[must_use]
    pub fn rand_rows(&self) -> usize {
        self.mask.width()
    }

    /// `µ·n₀`, the length of the stack `t̂` (Fig. 3 `Com*` step 3, p. 9).
    #[must_use]
    pub fn stack_len(&self) -> usize {
        self.mu() * self.cols
    }

    /// Entries of one committed augmented matrix: `rows·n₀`, laid out row-major
    /// with row stride `n₀`.
    #[must_use]
    pub fn aug_len(&self) -> usize {
        self.rows() * self.cols
    }

    /// The inner key `A`.
    #[must_use]
    pub fn inner_key(&self) -> &InnerKey {
        &self.a
    }

    /// The masking block `B = [B′ | I_µ]`.
    #[must_use]
    pub fn mask_block(&self) -> &MaskBlock {
        &self.mask
    }

    /// The outer key `D`, over `Z_{q_o}`.
    #[must_use]
    pub fn outer_key(&self) -> &OuterKey {
        &self.outer
    }

    /// `B_t`.
    #[must_use]
    pub fn b_t(&self) -> u64 {
        self.b_t
    }

    /// `B_u`.
    #[must_use]
    pub fn b_u(&self) -> u64 {
        self.b_u
    }

    /// Entries of one column of the augmented matrix: `m₁+1` committed rows and
    /// `µ+ν` randomness rows.
    #[must_use]
    pub fn rows(&self) -> usize {
        self.aug_rows() + self.rand_rows()
    }

    /// `n₀`, the columns of the augmented matrix.
    #[must_use]
    pub fn cols(&self) -> usize {
        self.cols
    }

    /// The rows of `f̂*` the gates measure.
    #[must_use]
    pub fn counted_rows(&self) -> usize {
        self.counted_rows
    }

    /// `m₁ + 1`, the rows of `F̂*` — and so of `f̂*` (the mask row included).
    #[must_use]
    pub fn aug_rows(&self) -> usize {
        self.a.cols()
    }

    /// `m₁+1+µ+ν − rank([A | B′ | I_µ])`: the dimension of the set of augmented
    /// columns that share one levelled commitment.
    ///
    /// This is the *structural* half of Theorem 2, and the reason the paper
    /// writes `B = [B′ | I_µ]` (p. 8) rather than sampling one wide `A`. A base
    /// whose key is tall and full-column-rank — the [`MleKey`] of the Σ line, and
    /// every reading in which the randomness rows are just more columns of `A` —
    /// scores `0` here: the commitment *is* the message, invertible by
    /// [`MleKey::solve`], and no choice of `χ` hides anything. A positive value
    /// says the levelled commitment leaves `[f̂*; r]` free, which is the
    /// precondition B.5 (p. 18) turns into hiding with MLWE.
    #[must_use]
    pub fn preimage_freedom(&self) -> usize {
        let nu = self.mask.nu();
        let cols = self.aug_rows() + nu + self.mu();
        let mut joined: Vec<Vec<InnerCoeff>> = (0..self.mu())
            .map(|i| {
                let mut row = Vec::with_capacity(cols);
                for j in 0..self.aug_rows() {
                    row.push(self.a.entry(i, j));
                }
                for j in 0..nu {
                    row.push(self.mask.b_prime.entry(i, j));
                }
                for j in 0..self.mu() {
                    row.push(if j == i {
                        InnerCoeff::ONE
                    } else {
                        InnerCoeff::ZERO
                    });
                }
                row
            })
            .collect();
        let mut pivot_row = 0usize;
        for col in 0..cols {
            if pivot_row >= self.mu() {
                break;
            }
            let Some(p) = (pivot_row..self.mu()).find(|&r| joined[r][col] != InnerCoeff::ZERO)
            else {
                continue;
            };
            joined.swap(pivot_row, p);
            let inv = joined[pivot_row][col]
                .inverse()
                .expect("a prime field inverts every non-zero pivot");
            for v in joined[pivot_row].iter_mut() {
                *v *= inv;
            }
            let piv = joined[pivot_row].clone();
            for (r, row) in joined.iter_mut().enumerate() {
                if r != pivot_row && row[col] != InnerCoeff::ZERO {
                    let f = row[col];
                    for (dst, pv) in row.iter_mut().zip(piv.iter()) {
                        *dst -= f * *pv;
                    }
                }
            }
            pivot_row += 1;
        }
        cols - pivot_row
    }

    /// Column `k` of a flat augmented matrix: the `m₁+1` committed rows with the
    /// `µ+ν` randomness rows underneath.
    ///
    /// # Panics
    /// If `aug` is not [`Self::aug_len`] long or `k ≥ n₀`.
    #[must_use]
    pub fn column(&self, aug: &[Z1Coeff], k: usize) -> Vec<Z1Coeff> {
        assert_eq!(aug.len(), self.aug_len(), "augmented matrix length");
        assert!(k < self.cols, "column {k} outside n0 = {}", self.cols);
        (0..self.rows())
            .map(|row| aug[row * self.cols + k])
            .collect()
    }

    /// The split Fig. 3's two matrices impose on one column of the augmented
    /// matrix: `f̂*ₖ` (the `m₁+1` rows `A` takes) and `rₖ` (the `µ+ν` rows `B`
    /// takes).
    #[must_use]
    pub fn column_pair(&self, aug: &[Z1Coeff], k: usize) -> (Vec<Z1Coeff>, Vec<Z1Coeff>) {
        let col = self.column(aug, k);
        let split = self.aug_rows();
        (col[..split].to_vec(), col[split..].to_vec())
    }

    /// Fig. 3 `Com*` step 3's left-hand side: `tₖ = A f̂*ₖ + B rₖ (mod q)`.
    ///
    /// # Panics
    /// If `f` is not `m₁+1` or `r` not `µ+ν` long.
    #[must_use]
    pub fn inner_apply(&self, f: &[Z1Coeff], r: &[Z1Coeff]) -> Vec<Z1Coeff> {
        assert_eq!(f.len(), self.aug_rows(), "A takes the m₁+1 rows");
        assert_eq!(r.len(), self.rand_rows(), "B takes the µ+ν rows");
        let a_f = self.a.apply(f);
        let b_r = self.mask.apply(r);
        a_f.iter().zip(b_r.iter()).map(|(x, y)| *x + *y).collect()
    }

    /// Fig. 3 `Com*` step 3 (p. 9): the rounded inner commitment stack
    /// `t̂ = t̂₀‖…‖t̂_{n₀−1}` of a committed augmented matrix.
    #[must_use]
    pub fn stack(&self, aug: &[Z1Coeff]) -> Vec<i64> {
        let mut out = Vec::with_capacity(self.stack_len());
        for k in 0..self.cols {
            let (f, r) = self.column_pair(aug, k);
            let t = self.inner_apply(&f, &r);
            out.extend(t.iter().map(|c| round_div(c.centered(), self.b_t)));
        }
        out
    }

    /// Fig. 3 `Com*` step 4 (p. 9): the outer commitment `û = ⌊(D t̂)/B_u⌉` of a
    /// stack, with `u = D t̂` reduced in the **outer** ring first — the step that
    /// makes `q_o` do work rather than appear.
    #[must_use]
    pub fn outer_commit(&self, stack: &[i64]) -> Vec<i64> {
        assert_eq!(stack.len(), self.stack_len(), "stack length");
        let u = self.outer.apply(&ints_to_outer(stack));
        // `u ∈ [0, q_o)` is the representative the figure rounds, so `û` lands in
        // `[0, q_o/B_u]` and `s` is a rounding error, not a field element.
        u.iter()
            .map(|c| round_div(c.to_u128() as i64, self.b_u))
            .collect()
    }

    /// Fig. 7 line 1's `zᵀ := v̂*₁ᵀ F̂*`: the `n₀`-vector the prover sends
    /// *before* the challenge, with `zₖ = Σⱼ v̂*₁[ⱼ]·F̂*[ⱼ][k]`.
    ///
    /// `v1` is `v̂*₁` of Fig. 4 (p. 10) — the `m₁+1` row weights
    /// `(Ecd(v₁,₀), …, Ecd(v₁,m₁₋₁), Ecd(x*))` of the quadratic form. Note what
    /// this does *not* need: no witness recovery, because the prover holds `F̂*`.
    /// That is the difference from the Σ line, and the reason
    /// [`Self::preimage_freedom`] has to be positive for lines 9–10 to say
    /// anything a verifier could not compute for itself.
    ///
    /// # Errors
    /// [`MleError::WrongLength`] if `v1` is not `m₁+1` long or `aug` is not
    /// [`Self::aug_len`] long.
    pub fn quad_z(&self, aug: &[Z1Coeff], v1: &[Z1Coeff]) -> Result<Vec<Z1Coeff>, MleError> {
        if v1.len() != self.aug_rows() || aug.len() != self.aug_len() {
            return Err(MleError::WrongLength);
        }
        let mut z = vec![Z1Coeff::ZERO; self.cols];
        for (j, v) in v1.iter().enumerate() {
            for (zk, cell) in z.iter_mut().zip(&aug[j * self.cols..(j + 1) * self.cols]) {
                *zk += *v * *cell;
            }
        }
        Ok(z)
    }

    /// Fig. 6 lines 12–13 (p. 11): the aggregate `Σᵢ λᵢ·xᵢ + x_mask` of stacks
    /// or of outer commitments.
    ///
    /// Both are *integer* combinations, because the paper aggregates the already
    /// rounded values (`t̂ := Σαᵢt̂ᵢ + t̂_{m₀}`, `û := Σαᵢûᵢ + û_{m₀}`) — which is
    /// why `‖û‖` is not `⌊(D t̂)/B_u⌉` exactly and the difference is the
    /// `m₀B_C B_o` term of Theorem 5 rather than a bug.
    ///
    /// Returns `None` if the parts are ragged or a term leaves `i128`.
    pub fn integer_combination(
        weights: &[i64],
        parts: &[&[i64]],
        mask: &[i64],
    ) -> Option<Vec<i64>> {
        if weights.len() != parts.len() || parts.iter().any(|p| p.len() != mask.len()) {
            return None;
        }
        let mut out = Vec::with_capacity(mask.len());
        for i in 0..mask.len() {
            let mut acc: i128 = i128::from(mask[i]);
            for (w, p) in weights.iter().zip(parts.iter()) {
                acc = acc.checked_add(i128::from(*w).checked_mul(i128::from(p[i]))?)?;
            }
            out.push(i64::try_from(acc).ok()?);
        }
        Some(out)
    }

    /// Fig. 7 lines 3 and 4: the contracted response `(f̂*, r)` of a committed
    /// augmented matrix under the challenge `c`, *without* the stack.
    ///
    /// A scheme that aggregates several blocks sends the stack of Fig. 6
    /// line 13 (`t̂ := Σᵢ αᵢt̂ᵢ + t̂_{m₀}`), which rounding makes different from
    /// the stack of the aggregated matrix, so it builds its response from this
    /// and supplies `t̂` itself ([`MleQuadProof`], [`Self::integer_combination`]).
    ///
    /// # Errors
    /// [`MleError::WrongLength`] if `c` is not `n₀` long or `aug` is not
    /// [`Self::aug_len`] long.
    pub fn quad_contract(
        &self,
        aug: &[Z1Coeff],
        c: &[Z1Coeff],
    ) -> Result<(Vec<Z1Coeff>, Vec<Z1Coeff>), MleError> {
        if c.len() != self.cols || aug.len() != self.aug_len() {
            return Err(MleError::WrongLength);
        }
        let mut comb = vec![Z1Coeff::ZERO; self.rows()];
        for k in 0..self.cols {
            for row in 0..self.rows() {
                comb[row] += c[k] * aug[row * self.cols + k];
            }
        }
        let split = self.aug_rows();
        Ok((comb[..split].to_vec(), comb[split..].to_vec()))
    }

    /// Fig. 7's `Quad.P` in one call: lines 1, 3 and 4.
    ///
    /// Line 1 sends `(t̂, z)` with `zᵀ := v̂*₁ᵀ F̂*`; lines 3–4 send
    /// `f̂* := F̂*c` and `r := Rc` after the challenge of line 2. The `t̂` of an
    /// aggregated transcript is the integer combination of Fig. 6 line 13, which
    /// the caller overwrites on the returned proof
    /// ([`Self::integer_combination`]).
    ///
    /// # Errors
    /// [`MleError::WrongLength`] for a wrong `aug`, `c` or `v1`.
    pub fn quad_prove(
        &self,
        aug: &[Z1Coeff],
        c: &[Z1Coeff],
        v1: &[Z1Coeff],
    ) -> Result<MleQuadProof, MleError> {
        let (f_star, r) = self.quad_contract(aug, c)?;
        Ok(MleQuadProof {
            t_hat: self.stack(aug),
            z: self.quad_z(aug, v1)?,
            f_star,
            r,
        })
    }

    /// Fig. 7 lines 5, 6, 9 and 10: everything the verifier *computes*, plus the
    /// two sums lines 7–8 compare.
    ///
    /// `claim` carries the public instance data (`û`, `v̂*₁`, `ŵ₀`, `ŷ*`), `c` the
    /// challenge of line 2 and `proof` the prover's four messages.
    ///
    /// # Errors
    /// [`MleError::WrongLength`] for a component of the wrong shape, and
    /// [`MleError::NormUndecidable`] when a squared norm cannot be accumulated.
    pub fn quad_measure(
        &self,
        claim: &QuadClaim<'_>,
        c: &[Z1Coeff],
        proof: &MleQuadProof,
    ) -> Result<QuadResiduals, MleError> {
        claim.validate(self, c, proof)?;
        let b_t = i64::try_from(self.b_t).map_err(|_| MleError::NormUndecidable)?;
        let b_u = i64::try_from(self.b_u).map_err(|_| MleError::NormUndecidable)?;
        // line 5: h := A f̂* + B r − B_t·Ťc  (mod q), with Ťc the challenge
        // contraction of the *sent* stack.
        let a_comb = self.inner_apply(&proof.f_star, &proof.r);
        let mu = self.mu();
        let mut t_c = vec![Z1Coeff::ZERO; mu];
        for (k, ck) in c.iter().enumerate() {
            for (acc, t) in t_c.iter_mut().zip(&proof.t_hat[k * mu..(k + 1) * mu]) {
                *acc += *ck * from_centered::<Z1Coeff>(*t);
            }
        }
        let b_t_f = from_centered::<Z1Coeff>(b_t);
        let h: Vec<i64> = (0..mu)
            .map(|i| (a_comb[i] - b_t_f * t_c[i]).centered())
            .collect();
        // line 6: s := D t̂ − B_u·û  (mod q_o). The reduction happens in the
        // *outer* ring: this is the line `q_o ≠ q` changes, and the reason `û`
        // travels as an integer vector rather than as residues of the inner one.
        let d_stack = self.outer.apply(&ints_to_outer(&proof.t_hat));
        let q_o = i128::from(Q_O);
        let s: Vec<i64> = d_stack
            .iter()
            .enumerate()
            .map(|(i, u)| {
                let scaled = (i128::from(claim.outer[i]) * i128::from(b_u)).rem_euclid(q_o);
                (*u - OuterCoeff::new(scaled as u64)).centered()
            })
            .collect();
        // line 9: v̂*₁ᵀ f̂*  ?=  zᵀc.
        let linearity_lhs = dot(&proof.f_star, claim.v1);
        let linearity_rhs = dot(&proof.z, c);
        // line 10: zᵀŵ₀  ?=  ŷ* (mod X_γ − b), which in §2's scalar reading
        // (p. 5, γ = 1) is an equality of field elements.
        let evaluation_lhs = dot(&proof.z, claim.w0);
        // the gated parts, lifted once so the sums and the report agree.
        let counted = self.counted_rows;
        let f_part = ints_of(&proof.f_star[..counted]);
        let f_full = ints_of(&proof.f_star);
        let r_part = ints_of(&proof.r);
        let inner_sum = summed_norms(&[&f_part, &r_part, &h])?;
        let inner_sum_full = summed_norms(&[&f_full, &r_part, &h])?;
        let outer_sum = summed_norms(&[&s, &proof.t_hat])?;
        Ok(QuadResiduals {
            h,
            s,
            inner_sum,
            inner_sum_full,
            outer_sum,
            linearity_lhs,
            linearity_rhs,
            evaluation_lhs,
            y_star: claim.y_star,
        })
    }

    /// Fig. 7 lines 7–10: the two response gates and the two link checks,
    /// reported as a *set* — every line the transcript trips, never only the
    /// first.
    ///
    /// `claim` holds the instance the figure verifies against, `c` the challenge
    /// of line 2, `proof` the prover's messages and `bounds` the `(B, B_o)` this
    /// instance's parameters imply, from [`QuadParams::gates`].
    ///
    /// The four lines are independent *by construction*, and B.9 (p. 20) uses
    /// them that way: line 7 reads the inner triple, line 8 the outer pair, and
    /// lines 9–10 split the single message `z` between the committed matrix
    /// (`v̂*₁ᵀf̂* = zᵀc`) and the claimed value (`zᵀŵ₀ = ŷ*`). B.9 subtracts two
    /// transcripts that share `(t̂, z)` and differ only in `c`, which turns line 9
    /// into `v̂*₁ᵀf̂*ₖ = cₖzₖ` *per column*, and then needs line 10 to turn those
    /// column values into `ŷ*`. Neither line implies the other: a verifier that
    /// ran only line 9 would accept a `z` that opens the committed matrix
    /// correctly for its own challenge while mis-stating the evaluation, and one
    /// that ran only line 10 would accept a `z` that adds up to `ŷ*` without
    /// being the committed matrix's contraction at all.
    ///
    /// # Errors
    /// As [`Self::quad_measure`].
    pub fn quad_report(
        &self,
        claim: &QuadClaim<'_>,
        c: &[Z1Coeff],
        proof: &MleQuadProof,
        bounds: &QuadBounds,
    ) -> Result<Vec<QuadCheck>, MleError> {
        let m = self.quad_measure(claim, c, proof)?;
        let mut bad = Vec::new();
        if m.inner_sum > bounds.b {
            bad.push(QuadCheck::InnerNorm);
        }
        if m.outer_sum > bounds.b_o {
            bad.push(QuadCheck::OuterNorm);
        }
        if m.linearity_lhs != m.linearity_rhs {
            bad.push(QuadCheck::Linearity);
        }
        if m.evaluation_lhs != m.y_star {
            bad.push(QuadCheck::Evaluation);
        }
        Ok(bad)
    }
}

/// The instance-side data one Fig. 7 verification reads besides the prover's
/// messages: the reduced instance `x* = (û, x*, ŷ*)` of Fig. 6's footer (p. 11)
/// together with the two weight tables of Fig. 4 (p. 10) that split `ŷ*` between
/// lines 9 and 10.
///
/// The split is the content of the two lines. `ŷ* = v̂*₁ᵀ F̂* ŵ₀` is one scalar
/// equation, but ΠQuad never sees `F̂*`; giving the prover the *row* contraction
/// `zᵀ := v̂*₁ᵀ F̂*` (line 1) turns it into two checks on one short message — line
/// 9 pins `z` to `F̂*` through the challenge, line 10 pins it to the claim. A
/// verifier holding only the flattened weight table `v̂*₁ ⊗ ŵ₀` (which is what the
/// Σ line uses) can run neither.
#[derive(Debug, Clone, Copy)]
pub struct QuadClaim<'a> {
    /// `û`: the outer aggregate commitment line 6 reduces against, `κ` entries.
    pub outer: &'a [i64],
    /// `v̂*₁`: the `m₁+1` row weights — the row side of Fig. 4's
    /// `ŷ* = v̂*₁ᵀ F̂* ŵ₀`, and the only thing line 9 reads from the instance.
    pub v1: &'a [Z1Coeff],
    /// `ŵ₀`: the `n₀` column weights, line 10's side of the same split.
    pub w0: &'a [Z1Coeff],
    /// `ŷ*`: the claimed value of the reduced instance.
    pub y_star: Z1Coeff,
}

impl QuadClaim<'_> {
    /// The shape check `quad_measure` and `quad_report` share: a component of
    /// the wrong length is a refusal, never a pass.
    ///
    /// # Errors
    /// [`MleError::WrongLength`] if any component disagrees with `lv`.
    fn validate(
        &self,
        lv: &MleLevels,
        c: &[Z1Coeff],
        proof: &MleQuadProof,
    ) -> Result<(), MleError> {
        if c.len() != lv.cols
            || proof.t_hat.len() != lv.stack_len()
            || proof.z.len() != lv.cols
            || proof.f_star.len() != lv.aug_rows()
            || proof.r.len() != lv.rand_rows()
            || self.outer.len() != lv.kappa()
            || self.v1.len() != lv.aug_rows()
            || self.w0.len() != lv.cols
        {
            return Err(MleError::WrongLength);
        }
        Ok(())
    }
}

/// The shape of one [`MleLevels`]: Fig. 3's `Setup` line (p. 8) read as fields.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Shape {
    /// `µ`: the entries of one column commitment `tₖ`, i.e. the row count of
    /// both `A` and `B`.
    pub mu: usize,
    /// `ν`: the columns of `B′`, so `B = [B′ | I_µ] ∈ R_q^{µ×(µ+ν)}` and
    /// Theorem 2's hypothesis is `MLWE_{q,ν,χ}`.
    pub nu: usize,
    /// `m₁ + 1`: the rows of `F̂*` — `m₁` sub-polynomial rows and the value-mask
    /// row of `EcdToMat` (p. 9).
    pub aug_rows: usize,
    /// `n₀`: the columns of `F̂*`, and the width of Fig. 7 line 2's challenge.
    pub cols: usize,
    /// The rows of `f̂*` the gates measure. See [`MleLevels::counted_rows`].
    pub counted_rows: usize,
    /// `B_t`.
    pub b_t: u64,
    /// `B_u`.
    pub b_u: u64,
}

impl Shape {
    /// The shape of a scheme with `m1` sub-polynomial rows per block and every
    /// row of `F̂*` short enough to gate.
    #[must_use]
    pub const fn new(mu: usize, nu: usize, m1: usize, cols: usize, b_t: u64, b_u: u64) -> Self {
        Self {
            mu,
            nu,
            aug_rows: m1 + 1,
            cols,
            counted_rows: m1 + 1,
            b_t,
            b_u,
        }
    }

    /// The rows one column of the augmented matrix carries: `m₁+1` committed
    /// plus `µ+ν` randomness.
    #[must_use]
    pub const fn rows(&self) -> usize {
        self.aug_rows + self.mu + self.nu
    }

    /// Refuses the shapes the gates cannot express.
    ///
    /// # Panics
    /// If a dimension is zero, `counted_rows > m₁+1`, or a compression factor is
    /// zero (a zero factor makes [`round_div`] undefined and the matching gate
    /// vacuous).
    pub fn validate(&self) {
        assert!(
            self.mu > 0 && self.cols > 0 && self.aug_rows > 0,
            "bad level shape: µ {}, ν {}, rows {}, n₀ {}",
            self.mu,
            self.nu,
            self.aug_rows,
            self.cols
        );
        assert!(
            self.counted_rows <= self.aug_rows,
            "the gates cannot measure more rows than F̂* has: rows {}, counted {}",
            self.aug_rows,
            self.counted_rows
        );
        assert!(
            self.b_t > 0 && self.b_u > 0,
            "a compression factor of zero is not rounding"
        );
    }
}

/// `Σᵢ aᵢbᵢ` over the scalar field — the shape lines 9 and 10 are written in.
fn dot(a: &[Z1Coeff], b: &[Z1Coeff]) -> Z1Coeff {
    a.iter().zip(b).fold(Z1Coeff::ZERO, |acc, (x, y)| acc + *x * *y)
}

/// Lifts integer coordinates into the **outer** field through the centered
/// representative: the stack `t̂` is an integer vector, `D` lives mod `q_o`.
fn ints_to_outer(v: &[i64]) -> Vec<OuterCoeff> {
    v.iter().map(|&x| from_centered::<OuterCoeff>(x)).collect()
}

/// The ceiling-`ℓ2` sum of several parts — the left-hand side of Fig. 7 lines
/// 7–8, via the shared [`exact_l2`] accumulator.
fn summed_norms(parts: &[&[i64]]) -> Result<u128, MleError> {
    let mut sum: u128 = 0;
    for part in parts {
        let squared =
            exact_l2::squared_norm_of_ints(part).map_err(|_| MleError::NormUndecidable)?;
        sum = sum
            .checked_add(exact_l2::isqrt_ceil(squared))
            .ok_or(MleError::NormUndecidable)?;
    }
    Ok(sum)
}

/// What the verifier forms at Fig. 7 lines 5–6 and 9–10, plus the sums lines
/// 7–8 gate. Exposed so a caller can *report* how much slack a transcript uses,
/// and which exempt row eats it, instead of only whether the run passed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuadResiduals {
    /// Line 5: the inner residual `h = A f̂* + B r − B_t Ťc`, centered, `µ`
    /// entries, in `Z_q`.
    pub h: Vec<i64>,
    /// Line 6: the outer residual `s = D t̂ − B_u û`, centered, `κ` entries, in
    /// `Z_{q_o}` — the one number in the protocol that only exists because the
    /// outer level has its own modulus.
    pub s: Vec<i64>,
    /// `⌈‖f̂*_{counted}‖₂⌉ + ⌈‖r‖₂⌉ + ⌈‖h‖₂⌉`, the quantity line 7 bounds by `B`.
    pub inner_sum: u128,
    /// The same sum with **every** row of `F̂*` measured, the exempt ones
    /// included. A base that exempts a row ([`MleLevels::counted_rows`]) can
    /// only say `inner_sum ≤ B`; this field says how much of `B` the exemption
    /// was worth, which is the number a reader needs before trusting the gate.
    pub inner_sum_full: u128,
    /// `⌈‖s‖₂⌉ + ⌈‖t̂‖₂⌉`, the quantity line 8 bounds by `B_o`.
    pub outer_sum: u128,
    /// Line 9's left-hand side, `v̂*₁ᵀ f̂*`.
    pub linearity_lhs: Z1Coeff,
    /// Line 9's right-hand side, `zᵀc`.
    pub linearity_rhs: Z1Coeff,
    /// Line 10's left-hand side, `zᵀŵ₀`.
    pub evaluation_lhs: Z1Coeff,
    /// Line 10's right-hand side: the `ŷ*` the reduced instance claims.
    pub y_star: Z1Coeff,
}

/// The response of Jindo Fig. 7's `Quad.P` (p. 11): the four messages the
/// prover sends, and nothing the verifier can compute for itself.
///
/// Lines 5 and 6 sit in the figure's *verifier* column, so `h` and `s` are
/// derived ([`MleLevels::quad_measure`]) rather than transmitted — sending them
/// would let a prover hand the gate its own input. `z` is the opposite case: it
/// is line 1's message, sent **before** the challenge of line 2, which is what
/// makes lines 9–10 bind at all. B.9 (p. 20) rewinds a prover that fixed `z` to
/// re-draw only `cₖ`, so a `z` that is not in the transcript before the
/// challenge would let a prover satisfy line 9 and line 10 with two linear
/// conditions on `n₀ ≥ 3` unknowns and no witness at all.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MleQuadProof {
    /// Line 1: the rounded inner commitment stack `t̂ ∈ R^{µn₀}`.
    pub t_hat: Vec<i64>,
    /// Line 1: `zᵀ := v̂*₁ᵀ F̂*`, the `n₀` row-contractions the two link lines
    /// split between them ([`MleLevels::quad_z`]).
    pub z: Vec<Z1Coeff>,
    /// Line 3: `f̂* := F̂*c` — every row of the augmented sub-polynomial matrix,
    /// the last of them the value mask's.
    pub f_star: Vec<Z1Coeff>,
    /// Line 4: `r := Rc` — the contracted commitment randomness, `µ+ν` entries.
    pub r: Vec<Z1Coeff>,
}

/// Which of Jindo Fig. 7's verifier lines (p. 11) a transcript tripped.
///
/// The four lines are independent *by construction*. Line 7 reads the prover's
/// inner response (`f̂*`, `r`, and the inner residual `h` formed from them and
/// the sent stack), line 8 the outer pair (`s`, `t̂`), and lines 9–10 the single
/// first message `z` from two directions: line 9 against the contracted matrix
/// (`v̂*₁ᵀf̂* = zᵀc`), line 10 against the claimed value (`zᵀŵ₀ = ŷ*`). A
/// transcript can fail any one of them alone — which is what makes them four
/// conditions rather than one — and the paper's own arguments use them apart:
/// Theorem 1 (p. 10) needs `MSIS_{q,µ,2B_αB_C B}` for line 7 and
/// `MSIS_{q_o,κ,2B_αB_o}` for line 8, while B.9 (p. 20) extracts per-column
/// values from line 9 and only then closes the relation with line 10.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[non_exhaustive]
pub enum QuadCheck {
    /// `‖f̂*‖₂ + ‖r‖₂ + ‖h‖₂ ≤ B`.
    InnerNorm,
    /// `‖s‖₂ + ‖t̂‖₂ ≤ B_o`.
    OuterNorm,
    /// `v̂*₁ᵀ f̂* = zᵀc`.
    Linearity,
    /// `zᵀŵ₀ = ŷ* (mod X_γ − b)`.
    Evaluation,
}

impl QuadCheck {
    /// The line's name, in the ASCII form a tamper battery attributes failures
    /// by (combining diacritics drop out of a plain terminal).
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::InnerNorm => "Fig.7 L7   |f*| + |r| + |h| <= B",
            Self::OuterNorm => "Fig.7 L8   |s| + |t_hat| <= B_o",
            Self::Linearity => "Fig.7 L9   v1.f* == z.c",
            Self::Evaluation => "Fig.7 L10  z.w0 == y* (mod X^g-b)",
        }
    }
}

impl core::fmt::Display for QuadCheck {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.name())
    }
}

/// The two response bounds of one instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuadBounds {
    /// `B`, the line 7 bound on the inner triple.
    pub b: u128,
    /// `B_o`, the line 8 bound on the outer pair.
    pub b_o: u128,
}

/// The parameters Jindo's Theorems 3, 5 and 6 read (eprint 2026/044,
/// pp. 10–12) to produce `(B, B_o)`, so a gate's threshold is a computation
/// over the instance rather than a tuned constant.
///
/// # The recursion the paper leaves ambiguous — and the reading taken here
///
/// Theorem 5 (p. 11) prints its own output bound with `B` on **both** sides:
///
/// ```text
/// B   = m0·B_C·B + σ(√(2(m1+1)d) + √(2(μ+ν)d)) + B_t√(μd)
/// B_o = m0·B_C·B_o + B_u√(κd) + (q/B_t)√(μn0 d)
/// ```
///
/// and the same shape recurs in Theorem 6's `B = n0·B_C·B` and `B_o = B_o`
/// (p. 12) and in Corollary 1 (p. 12). Reading any of them as a fixed point
/// `B := (σ(…) + B_t√(μd))/(1 − m0·B_C)` is impossible for any instance worth
/// running: `m0·B_C > 1` makes the denominator negative, so the "solution" is
/// negative while the gate it feeds is a norm bound. B.8 (p. 19) decides what
/// was meant. It derives the display from an honest aggregate
/// `f̂*_k = Σᵢ αᵢf̂*_{i,k} + f̂*_{m0,k}` whose `α`-summed part is bounded by
/// `m0·B_C` times **the input relation's** bound and whose fresh term is a tail
/// of the new Gaussian — so the left-hand `B` is the *output* and the
/// right-hand `B` the *input* of one relaxation `B_out = f(B_in)`.
/// [`QuadParams::theorem5`] and [`QuadParams::theorem6`] therefore take the
/// input bound as an explicit argument, and [`QuadParams::theorem3`] supplies
/// the base value an honest `Com*` opening already satisfies (p. 10, and B.6
/// p. 18 for the per-entry reasoning).
///
/// The second ambiguity is `σ`. Lemma 2 (p. 6) states `σ ≈ 14·T/ln M` — `T`
/// *multiplying* — and B.8 (p. 19) instantiates it at `T = m0√n0·B_C·B`, so
/// Theorem 5's first bullet is a product, not a quotient. A wider `B` therefore
/// demands a *wider* `σ`; [`Self::sigma_required`] computes it, and the
/// instance reports its sampling width against that value instead of quietly
/// using a smaller one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct QuadParams {
    /// `m0`, the batch count of Fig. 3's `Setup` (p. 8).
    pub m0: usize,
    /// `n0`, the columns of `F̂*`.
    pub n0: usize,
    /// `µ + ν`: the commitment-randomness rows per column, i.e. the width of
    /// every `rₖ` that [`MaskBlock`] masks.
    pub rand_rows: usize,
    /// The rows of `F̂*` the bounds count. The paper's `m1 + 1` includes the
    /// value-mask row, whose shortness comes from Lemma 7's flattening
    /// (`‖â‖∞ ≤ b`, p. 8); a base without that guarantee passes `m1` and its
    /// gates measure the same `m1` rows ([`MleLevels::counted_rows`]), so
    /// neither side can quietly exceed the other.
    pub counted_rows: usize,
    /// `μ`, the entries of one column commitment `tₖ`.
    pub mu: usize,
    /// `κ`, the entries of one outer commitment `û`.
    pub kappa: usize,
    /// The ring degree `d`.
    pub d: usize,
    /// `b` of Lemma 7 (p. 8): the per-entry bound of a committed coefficient.
    pub b_entry: u64,
    /// `B_χ` of Theorem 3 (p. 10): the per-entry bound of `χ`, from which the
    /// input blocks' randomness rows are drawn.
    pub b_chi: u64,
    /// `B_C`: the `ℓ1` bound on every challenge (Theorems 5, 6).
    pub b_c: u64,
    /// `B_t`, the inner compression factor of Fig. 3's `Setup` (p. 8).
    pub b_t: u64,
    /// `B_u`, the outer compression factor.
    pub b_u: u64,
    /// `q`: the inner modulus, which `A`, `B` and the line 5 residual `h` are
    /// reduced under.
    pub q: u64,
    /// `q_o`: the *outer* modulus, which `D` and the line 6 residual `s` are
    /// reduced under (Fig. 3's `Setup` lists `q, q_o, B_t, B_u` side by side,
    /// p. 8). It enters no formula of Theorems 3, 5 or 6 — `B_o` bounds `s`
    /// through `B_u`, not through `q_o` — and appears only in Theorem 1's
    /// `MSIS_{q_o,κ,2B_αB_o}`, which [`Self::outer_msis_headroom`] measures.
    pub q_o: u64,
    /// The width the masking block was *actually* sampled at. Theorem 5's fresh
    /// terms are Lemma 1 tails `σ√(…)` of that sampling, so the gate must see
    /// the `σ` that drew the samples; [`Self::sigma_required`] is the value
    /// Lemma 2 wanted, and the two are reported apart on purpose.
    pub sigma: u128,
}

impl QuadParams {
    /// `√(k·d)`, rounded up so the bound stays valid for a non-square product.
    fn root(&self, k: u128) -> Option<u128> {
        k.checked_mul(self.d as u128).map(exact_l2::isqrt_ceil)
    }

    /// `⌈q/B_t⌉`, the per-entry bound of a rounded inner commitment (B.6,
    /// p. 18: `‖t̂‖∞ ≤ q/B_t` "by the rounding definition").
    fn q_over_b_t(&self) -> u128 {
        (u128::from(self.q) + u128::from(self.b_t) - 1) / u128::from(self.b_t)
    }

    /// Theorem 3 (p. 10) — the bounds an honestly generated `Com*` opening
    /// already satisfies, i.e. the *input* to the two relaxations below:
    ///
    /// ```text
    /// B   = b√((m1+1)d) + B_χ√((μ+ν)d) + B_t√(μd)
    /// B_o = (q/B_t)√(μn0 d) + B_u√(κd)
    /// ```
    ///
    /// with `(m1+1)` read as [`Self::counted_rows`].
    #[must_use]
    pub fn theorem3(&self) -> Option<QuadBounds> {
        let h_term = u128::from(self.b_t).checked_mul(self.root(self.mu as u128)?)?;
        let b = u128::from(self.b_entry)
            .checked_mul(self.root(self.counted_rows as u128)?)?
            .checked_add(
                u128::from(self.b_chi)
                    .checked_mul(self.root(self.rand_rows as u128)?)?
                    .checked_add(h_term)?,
            )?;
        Some(QuadBounds {
            b,
            b_o: self.fresh_outer()?,
        })
    }

    /// The `(q/B_t)√(μn₀d) + B_u√(κd)` a *fresh* masking block contributes: one
    /// copy in Theorem 3, one more at the end of Theorem 5's `B_o`.
    fn fresh_outer(&self) -> Option<u128> {
        self.q_over_b_t()
            .checked_mul(self.root(self.mu as u128 * self.n0 as u128)?)?
            .checked_add(u128::from(self.b_u).checked_mul(self.root(self.kappa as u128)?)?)
    }

    /// Theorem 5 (p. 11), ΠAgg's relaxation of an input bound:
    ///
    /// ```text
    /// B   = m0·B_C·B_in + σ(√(2·counted·d) + √(2(μ+ν)d)) + B_t√(μd)
    /// B_o = m0·B_C·B_o_in + B_u√(κd) + (q/B_t)√(μn0 d)
    /// ```
    #[must_use]
    pub fn theorem5(&self, input: &QuadBounds) -> Option<QuadBounds> {
        let m0bc = (self.m0 as u128).checked_mul(u128::from(self.b_c))?;
        let fresh = self
            .sigma
            .checked_mul(self.root(2 * self.counted_rows as u128)?)?
            .checked_add(
                self.sigma
                    .checked_mul(self.root(2 * self.rand_rows as u128)?)?,
            )?
            .checked_add(u128::from(self.b_t).checked_mul(self.root(self.mu as u128)?)?)?;
        Some(QuadBounds {
            b: m0bc.checked_mul(input.b)?.checked_add(fresh)?,
            b_o: m0bc
                .checked_mul(input.b_o)?
                .checked_add(self.fresh_outer()?)?,
        })
    }

    /// Theorem 6 (p. 12, derived at B.9 p. 20) — ΠQuad's relaxation: contracting
    /// `n₀` columns by challenges of `ℓ1` norm `≤ B_C` multiplies the inner
    /// bound by `n₀·B_C` and leaves the outer one alone (`B = n₀·B_C·B`,
    /// `B_o = B_o`). These are the values a Fig. 7 transcript is gated against.
    #[must_use]
    pub fn theorem6(&self, input: &QuadBounds) -> Option<QuadBounds> {
        Some(QuadBounds {
            b: (self.n0 as u128)
                .checked_mul(u128::from(self.b_c))?
                .checked_mul(input.b)?,
            b_o: input.b_o,
        })
    }

    /// The whole chain — Theorem 3 on each input block, Theorem 5 across the
    /// aggregation, Theorem 6 across the contraction: the `(B, B_o)` of
    /// [`MleLevels::quad_report`].
    #[must_use]
    pub fn gates(&self) -> Option<QuadBounds> {
        self.theorem6(&self.theorem5(&self.theorem3()?)?)
    }

    /// Theorem 5's rejection-sampling width `σ = ⌈14·m0·√n0·B_C·B_in / ln M⌉`
    /// (p. 11), i.e. Lemma 2's `σ ≈ 14·T/ln M` (p. 6) at B.8's
    /// `T = m0√n0·B_C·B` (p. 19).
    ///
    /// Note the direction: `σ` grows *with* `B_in`. A sampling width below this
    /// value does not weaken a gate — the gate bounds the samples that were
    /// actually drawn — it breaks the *rejection-sampling* hypothesis of
    /// Theorem 5, and so the simulatability of `(F̂*, R)`. That is worth
    /// reporting, which is why it is a separate number rather than an
    /// assumption baked into [`Self::theorem5`].
    #[must_use]
    pub fn sigma_required(&self, b_in: u128, log_m: u128) -> Option<u128> {
        if log_m == 0 {
            return None;
        }
        let t = (self.m0 as u128)
            .checked_mul(exact_l2::isqrt_ceil(self.n0 as u128))?
            .checked_mul(u128::from(self.b_c))?
            .checked_mul(b_in)?;
        14u128.checked_mul(t).map(|num| (num + log_m - 1) / log_m)
    }

    /// The signed headroom of the **outer** modulus against Theorem 1's outer
    /// hypothesis `MSIS_{q_o,κ,2·B_α·B_o}` (p. 10):
    ///
    /// ```text
    /// q_o/2 − 2·B_α·B_o
    /// ```
    ///
    /// An `ℓ2` target of `2·B_α·B_o` lets a single coordinate of the solution
    /// vector be that large, and once it reaches `q_o/2` the target no longer
    /// confines a coordinate to a proper subrange of `Z_{q_o}`: the assumption is
    /// then stated at a bound the modulus cannot express. This is a *measurement*
    /// of that margin, not a proof step — `q_o` enters none of Theorems 3, 5 or
    /// 6's formulas, only their `B_o` feeds this one — and a negative value is
    /// reported as such rather than absorbed by shrinking the gate.
    ///
    /// Returns `None` when the arithmetic leaves `i128`, which for an `i128`
    /// accumulator means a bound past `2¹²²`: undecidable, not zero.
    #[must_use]
    pub fn outer_msis_headroom(&self, b_alpha: u128, b_o: u128) -> Option<i128> {
        let target = b_alpha.checked_mul(b_o)?.checked_mul(2)?;
        let half = i128::try_from(u128::from(self.q_o) / 2).ok()?;
        let target = i128::try_from(target).ok()?;
        half.checked_sub(target)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const L: usize = 16;

    fn key() -> MleKey {
        MleKey::setup(&[3u8; 32], L)
    }

    fn witness() -> Vec<Z1Coeff> {
        (0..L)
            .map(|i| from_centered::<Z1Coeff>(i as i64 - 4))
            .collect()
    }

    fn weights() -> Vec<Z1Coeff> {
        (0..L).map(|i| Z1Coeff::from(i as u64 + 1)).collect()
    }

    #[test]
    fn key_expansion_is_deterministic_and_seed_bound() {
        assert_eq!(MleKey::setup(&[1u8; 32], L), MleKey::setup(&[1u8; 32], L));
        assert_ne!(MleKey::setup(&[1u8; 32], L), MleKey::setup(&[2u8; 32], L));
    }

    #[test]
    fn honest_sigma_opening_verifies() {
        let k = key();
        let (f, w) = (witness(), weights());
        let com = commit_mle(&k, &f).expect("commit");
        let y = claim(&k, &com, &w).expect("claim");
        let proof = open_mle_proof(&k, &f, &w, &[9u8; 32]).expect("open");
        verify_mle_proof(&k, &com, &w, y, &proof).expect("honest opening must verify");
    }

    #[test]
    fn opening_is_randomized_by_the_mask_seed() {
        let k = key();
        let (f, w) = (witness(), weights());
        let a = open_mle_proof(&k, &f, &w, &[1u8; 32]).expect("open");
        let b = open_mle_proof(&k, &f, &w, &[1u8; 32]).expect("open");
        let c = open_mle_proof(&k, &f, &w, &[2u8; 32]).expect("open");
        assert_eq!(a, b, "the same mask seed must give the same proof");
        assert_ne!(a.d, c.d, "a different mask seed must redraw the mask");
    }

    #[test]
    fn tampered_response_is_rejected() {
        let k = key();
        let (f, w) = (witness(), weights());
        let com = commit_mle(&k, &f).expect("commit");
        let y = claim(&k, &com, &w).expect("claim");
        let mut proof = open_mle_proof(&k, &f, &w, &[9u8; 32]).expect("open");
        proof.z[0] += Z1Coeff::ONE;
        assert!(
            verify_mle_proof(&k, &com, &w, y, &proof).is_err(),
            "a perturbed response must break the overdetermined link"
        );
    }

    #[test]
    fn false_claim_is_rejected() {
        let k = key();
        let (f, w) = (witness(), weights());
        let com = commit_mle(&k, &f).expect("commit");
        let y = claim(&k, &com, &w).expect("claim");
        let proof = open_mle_proof(&k, &f, &w, &[9u8; 32]).expect("open");
        assert!(verify_mle_proof(&k, &com, &w, y + Z1Coeff::ONE, &proof).is_err());
    }

    #[test]
    fn proof_does_not_transfer_to_another_weight_table() {
        let k = key();
        let (f, w) = (witness(), weights());
        let com = commit_mle(&k, &f).expect("commit");
        let y = claim(&k, &com, &w).expect("claim");
        let proof = open_mle_proof(&k, &f, &w, &[9u8; 32]).expect("open");
        verify_mle_proof(&k, &com, &w, y, &proof).expect("the bound table verifies");
        let mut other = weights();
        other[3] += Z1Coeff::ONE;
        let other_y = claim(&k, &com, &other).expect("claim");
        assert!(
            verify_mle_proof(&k, &com, &other, other_y, &proof).is_err(),
            "the opening is bound to one weight table, not any table"
        );
    }

    #[test]
    fn certify_l2_separates_short_from_long() {
        let proj = JLProjection::from_seed(&[5u8; 32], 64, L);
        let short: Vec<Z1Coeff> = (0..L).map(|_| from_centered::<Z1Coeff>(1)).collect();
        let long: Vec<Z1Coeff> = (0..L).map(|_| from_centered::<Z1Coeff>(1000)).collect();
        assert!(certify_l2(&proj, &short, 8), "a short witness certifies");
        assert!(
            !certify_l2(&proj, &long, 8),
            "the same bound must reject a 1000x longer witness"
        );
        assert!(!certify_l2(&proj, &short, 0), "a zero bound is vacuous");
    }

    #[test]
    fn batch_claims_open_with_one_proof() {
        let k = key();
        let f = witness();
        let com = commit_mle(&k, &f).expect("commit");
        let w0 = weights();
        let mut w1 = weights();
        for (i, c) in w1.iter_mut().enumerate() {
            *c = Z1Coeff::from(i as u64 + 3);
        }
        let claims = [
            WeightClaim {
                weight: &w0,
                value: claim(&k, &com, &w0).expect("claim"),
            },
            WeightClaim {
                weight: &w1,
                value: claim(&k, &com, &w1).expect("claim"),
            },
        ];
        let proof = open_claims(&k, &f, &claims, &[3u8; 32]).expect("open");
        batch_verify(&k, &com, &claims, &proof).expect("honest batch verifies");
    }

    #[test]
    fn one_false_claim_in_the_batch_is_rejected() {
        let k = key();
        let f = witness();
        let com = commit_mle(&k, &f).expect("commit");
        let w0 = weights();
        let mut w1 = weights();
        for (i, c) in w1.iter_mut().enumerate() {
            *c = Z1Coeff::from(i as u64 + 3);
        }
        let claims = [
            WeightClaim {
                weight: &w0,
                value: claim(&k, &com, &w0).expect("claim"),
            },
            WeightClaim {
                // the *second* claim is off by one
                weight: &w1,
                value: claim(&k, &com, &w1).expect("claim") + Z1Coeff::ONE,
            },
        ];
        let proof = open_claims(&k, &f, &claims, &[3u8; 32]).expect("open");
        assert!(
            batch_verify(&k, &com, &claims, &proof).is_err(),
            "γ binds the whole claim set, so one false entry breaks the combined claim"
        );
    }

    #[test]
    fn combination_is_bound_to_the_commitment_and_claim_order() {
        let k = key();
        let f = witness();
        let com = commit_mle(&k, &f).expect("commit");
        let w0 = weights();
        let mut w1 = weights();
        for (i, c) in w1.iter_mut().enumerate() {
            *c = Z1Coeff::from(i as u64 + 3);
        }
        let y0 = claim(&k, &com, &w0).expect("claim");
        let y1 = claim(&k, &com, &w1).expect("claim");
        let forward = [
            WeightClaim {
                weight: &w0,
                value: y0,
            },
            WeightClaim {
                weight: &w1,
                value: y1,
            },
        ];
        let swapped = [
            WeightClaim {
                weight: &w0,
                value: y1,
            },
            WeightClaim {
                weight: &w1,
                value: y0,
            },
        ];
        let (wf, _) = combined_claim(&k, &com, &forward).expect("combine");
        let (ws, _) = combined_claim(&k, &com, &swapped).expect("combine");
        assert_ne!(
            wf, ws,
            "relabeling which value goes with which table must change the combination"
        );
    }

    // -----------------------------------------------------------------------
    // The compressed line: Fig. 3's two levels and Fig. 7's response gates.
    // -----------------------------------------------------------------------

    /// The toy's Fig. 3 shapes: `F̂*` has 2 sub-polynomial rows and the 1
    /// value-mask row (`AUG_ROWS = m₁+1 = 3`), `µ = 4`, `ν = 2`, so `R` carries
    /// `µ+ν = 6` randomness rows per column (Fig. 3 `Com*` step 2) and one column
    /// of the augmented matrix has `3 + 6 = 9` entries.
    const AUG_ROWS: usize = 3;
    const COLS: usize = 3;
    const MU: usize = 4;
    const NU: usize = 2;
    const RAND_ROWS: usize = MU + NU;
    const ROWS: usize = AUG_ROWS + RAND_ROWS;
    const KAPPA: usize = 2 * MU * COLS;
    /// The inner compression factor: `q/B_t ≈ 2045`, so a stack entry is at
    /// most `≈ 1023`.
    const B_T: u64 = 4096;
    const B_U: u64 = 8;
    const B_CHI: u64 = 1;
    const B_E: u64 = 2;

    fn shape() -> Shape {
        Shape {
            mu: MU,
            nu: NU,
            aug_rows: AUG_ROWS,
            cols: COLS,
            // Every row of `F̂*` is short here, so nothing is exempt: the
            // exemption path is `counted_rows < aug_rows`, exercised below.
            counted_rows: AUG_ROWS,
            b_t: B_T,
            b_u: B_U,
        }
    }

    fn levels() -> MleLevels {
        MleLevels::new(&[7u8; 32], &[8u8; 32], &[9u8; 32], &shape())
    }

    /// An honest `Com*` augmented matrix: short in every row.
    fn aug() -> Vec<Z1Coeff> {
        (0..ROWS * COLS)
            .map(|i| {
                let row = i / COLS;
                let v = match row {
                    0 | 1 => (i as i64 % 5) - 2,
                    2 => 1,
                    _ => -1,
                };
                from_centered::<Z1Coeff>(v)
            })
            .collect()
    }

    /// Fig. 7 line 2's challenge set: `{c : ‖c‖₁ ≤ B_C}` scalar entries.
    fn challenge(seed: u8) -> Vec<Z1Coeff> {
        (0..COLS)
            .map(|k| from_centered::<Z1Coeff>(((seed + k as u8) % 5) as i64 - 2))
            .collect()
    }

    /// `v̂*₁` of Fig. 4 (p. 10): the `m₁+1` row weights of the quadratic form.
    fn v1() -> Vec<Z1Coeff> {
        (0..AUG_ROWS)
            .map(|j| from_centered::<Z1Coeff>(j as i64 + 1))
            .collect()
    }

    /// `ŵ₀` of Fig. 4: the `n₀` column weights, the powers of a `d = 1`
    /// evaluation point.
    fn w0() -> Vec<Z1Coeff> {
        (0..COLS)
            .map(|k| from_centered::<Z1Coeff>(5i64.pow(k as u32)))
            .collect()
    }

    /// Fig. 4's claim `ŷ* = v̂*₁ᵀ F̂* ŵ₀` of a committed matrix, computed the way
    /// the *prover* computes it (through its own `z` of line 1) so that line 10
    /// is an honest transcript's tautology and any failure of it is the
    /// protocol's, not the fixture's.
    fn y_star_of(lv: &MleLevels, aug: &[Z1Coeff]) -> Z1Coeff {
        let z = lv.quad_z(aug, &v1()).expect("the fixture has F̂*'s shape");
        dot(&z, &w0())
    }

    fn params(sigma: u128) -> QuadParams {
        QuadParams {
            m0: 2,
            n0: COLS,
            rand_rows: RAND_ROWS,
            counted_rows: AUG_ROWS,
            mu: MU,
            kappa: KAPPA,
            d: 1,
            b_entry: B_E,
            b_chi: B_CHI,
            b_c: 2,
            b_t: B_T,
            b_u: B_U,
            q: Q_INNER,
            q_o: Q_O,
            sigma,
        }
    }

    /// A transcript of the whole line: commit, derive the outer aggregate the
    /// way Fig. 6 line 8 does, run `Quad.P`, and hold the four verifier lines'
    /// thresholds and instance data.
    #[allow(clippy::type_complexity)]
    fn transcript() -> (
        MleLevels,
        Vec<Z1Coeff>,
        Vec<Z1Coeff>,
        MleQuadProof,
        Vec<i64>,
        QuadBounds,
        Vec<Z1Coeff>,
        Vec<Z1Coeff>,
        Z1Coeff,
    ) {
        let lv = levels();
        let a = aug();
        let stack = lv.stack(&a);
        // One masking block plus one input block, aggregated by α = 1: the
        // outer commitment the instance holds is then the sum of the two, and
        // the stack the prover sends is the sum of the two stacks.
        let outer = lv.outer_commit(&stack);
        let bounds = params(300).gates().expect("toy bounds fit u128");
        let c = challenge(1);
        let (v1, w0) = (v1(), w0());
        let y_star = y_star_of(&lv, &a);
        let mut proof = lv.quad_prove(&a, &c, &v1).expect("prove");
        // Fig. 6 line 13 aggregates stacks by rounding first; with one block and
        // α = 1 the aggregate is the stack itself, so the sent one stands.
        proof.t_hat = stack;
        (lv, a, c, proof, outer, bounds, v1, w0, y_star)
    }

    /// The instance side of one Fig. 7 verification.
    fn claim_of<'a>(outer: &'a [i64], v1: &'a [Z1Coeff], w0: &'a [Z1Coeff], y: Z1Coeff) -> QuadClaim<'a>
    {
        QuadClaim {
            outer,
            v1,
            w0,
            y_star: y,
        }
    }

    #[test]
    fn rounding_is_nearest_and_bounded_by_the_quotient() {
        assert_eq!(round_div(0, 4), 0);
        assert_eq!(round_div(1, 4), 0);
        assert_eq!(round_div(3, 4), 1);
        assert_eq!(round_div(2, 4), 1, "ties go up");
        assert_eq!(round_div(-2, 4), 0, "−0.5 ties up, not away from zero");
        assert_eq!(round_div(-3, 4), -1);
        assert_eq!(
            round_div(8_380_416, 1),
            8_380_416,
            "B_t = 1 is not rounding"
        );
        for a in [-4_190_208i64, -1, 0, 1, 4_190_208, 8_380_416] {
            for b in [1u64, 2, 7, 4096] {
                let r = round_div(a, b);
                // |⌊a/b⌉| ≤ ⌈|a|/b⌉: the residual stays inside the quotient.
                let budget = (i128::from(a.abs()) + i128::from(b) - 1) / i128::from(b);
                assert!(
                    i128::from(r.abs()) <= budget,
                    "round_div({a},{b}) = {r} escaped ⌈|a|/b⌉ = {budget}"
                );
            }
        }
    }

    #[test]
    fn the_honest_quad_response_passes_every_line_with_slack() {
        let (lv, _, c, proof, outer, bounds, v1, w0, y) = transcript();
        let claim = claim_of(&outer, &v1, &w0, y);
        let m = lv.quad_measure(&claim, &c, &proof).expect("measure");
        assert_eq!(
            lv.quad_report(&claim, &c, &proof, &bounds).expect("report"),
            Vec::new(),
            "an honest transcript must trip no line (B = {}, B_o = {})",
            bounds.b,
            bounds.b_o
        );
        // h is the *rounding* residual, so B_t bounds it entrywise (B.6, p. 18:
        // ‖h‖∞ ≤ B_t). A residual of that size is the honesty evidence: a wrong
        // f̂* would show up here as a field-sized value.
        assert!(
            m.h.iter()
                .all(|&x| x.abs() <= (lv.b_t() * COLS as u64 * 2) as i64),
            "h escaped the rounding bound: {:?}",
            m.h
        );
        assert!(m.s.iter().all(|&x| x.abs() <= B_U as i64));
        assert!(m.inner_sum * 3 < bounds.b, "the toy slack is vanishing");
        assert!(m.outer_sum * 3 < bounds.b_o, "the toy slack is vanishing");
        // Lines 9 and 10 hold as *equalities*, and both sides are carried so a
        // scheme can report the values rather than only the verdict.
        assert_eq!(m.linearity_lhs, m.linearity_rhs, "line 9");
        assert_eq!(m.evaluation_lhs, m.y_star, "line 10");
        // The two link lines are the *same* claim read two ways: composing them
        // reproduces Fig. 4's `ŷ* = v̂*₁ᵀ F̂* ŵ₀` on the contracted response.
        let mut back = Z1Coeff::ZERO;
        for (ci, zi) in c.iter().zip(&proof.z) {
            back += *ci * *zi;
        }
        assert_eq!(back, m.linearity_lhs);
    }

    /// The acceptance bar the crate holds every scheme to: conditions the paper
    /// prints separately must fail separately.
    #[test]
    fn l7_and_l8_fail_apart() {
        let (lv, a, c, proof, outer, bounds, v1, w0, y) = transcript();
        let claim = claim_of(&outer, &v1, &w0, y);
        // Only line 7 plus line 9: a longer f̂* under an otherwise untouched
        // response. Line 5 then makes `h` field-sized — that is line 7 — and
        // line 9 sees the same lie from the other side, because `v̂*₁ᵀf̂*` moved
        // while `zᵀc` did not. Line 8 stays green: line 6 does not read `f̂*` at
        // all, which is the independence the pair is supposed to have.
        let mut inner_only = proof.clone();
        inner_only.f_star[0] += from_centered::<Z1Coeff>(1_000_000);
        assert_eq!(
            lv.quad_report(&claim, &c, &inner_only, &bounds)
                .expect("report"),
            vec![QuadCheck::InnerNorm, QuadCheck::Linearity],
            "a long inner response trips line 7, and line 9 sees the same lie"
        );
        // Only line 8: a stack entry shifted by `q·q_o` — the least positive
        // integer that leaves *both* residues alone, `h`'s mod `q` and `s`'s mod
        // `q_o`. With one modulus the shift was `q`; with two it has to clear
        // both, which is exactly what `q_o ≠ q` costs a prover.
        let mut outer_only = proof.clone();
        outer_only.t_hat[3] += i64::try_from(Q_O).unwrap() * i64::try_from(Q_INNER).unwrap();
        let before = lv.quad_measure(&claim, &c, &proof).expect("measure");
        let after = lv
            .quad_measure(&claim, &c, &outer_only)
            .expect("measure");
        assert_eq!(before.h, after.h, "the shift changed the inner residue");
        assert_eq!(before.s, after.s, "the shift changed the outer residue");
        assert_eq!(
            lv.quad_report(&claim, &c, &outer_only, &bounds)
                .expect("report"),
            vec![QuadCheck::OuterNorm],
            "a non-short stack must trip line 8 alone"
        );
        assert_eq!(a.len(), lv.aug_len());
    }

    /// Lines 9 and 10 read the *same* message `z` against two different things,
    /// and a `z` moved inside one functional's kernel fails the other alone.
    /// This is the pair B.9 (p. 20) uses apart: line 9 survives the rewind that
    /// extracts `v̂*₁ᵀf̂*ₖ = cₖzₖ`, line 10 is what turns those values into `ŷ*`.
    #[test]
    fn l9_and_l10_fail_apart() {
        let (lv, _, c, proof, outer, bounds, v1, w0, y) = transcript();
        let claim = claim_of(&outer, &v1, &w0, y);
        assert!(lv
            .quad_report(&claim, &c, &proof, &bounds)
            .expect("green")
            .is_empty());
        // Only line 9: shift `z` along `(ŵ₀₁, −ŵ₀₀, 0)`, which is orthogonal to
        // `ŵ₀` (so `zᵀŵ₀ = ŷ*` still holds) and generically not to `c` (so
        // `zᵀc ≠ v̂*₁ᵀf̂*`). The prover's `z` is then right about the claim and
        // wrong about the challenge contraction — exactly what line 9 exists for.
        let nine = {
            let mut p = proof.clone();
            p.z[0] += w0[1];
            p.z[1] -= w0[0];
            p
        };
        assert_ne!(nine.z, proof.z, "the shift must be non-trivial");
        assert_eq!(
            lv.quad_report(&claim, &c, &nine, &bounds).expect("report"),
            vec![QuadCheck::Linearity],
            "a z that still evaluates to ŷ* must trip line 9 alone"
        );
        // Only line 10: shift `z` along `(c₁, −c₀, 0)`, orthogonal to `c` (so
        // line 9's equation is untouched) and not to `ŵ₀` — a `z` consistent with
        // the committed matrix that simply mis-states the evaluation.
        let ten = {
            let mut p = proof.clone();
            p.z[0] += c[1];
            p.z[1] -= c[0];
            p
        };
        assert_ne!(ten.z, proof.z, "this transcript's c must not be zero");
        assert_eq!(
            lv.quad_report(&claim, &c, &ten, &bounds).expect("report"),
            vec![QuadCheck::Evaluation],
            "a z that still opens the committed matrix must trip line 10 alone"
        );
    }

    /// A `z` that is wrong in both directions trips both lines, and the report
    /// says so — the whole-failing-set convention, never a short circuit.
    #[test]
    fn a_double_lie_trips_both_link_lines_at_once() {
        let (lv, _, c, proof, outer, bounds, v1, w0, y) = transcript();
        let claim = claim_of(&outer, &v1, &w0, y);
        let mut both = proof.clone();
        both.z[2] += from_centered::<Z1Coeff>(7);
        let report = lv.quad_report(&claim, &c, &both, &bounds).expect("report");
        assert_eq!(
            report,
            vec![QuadCheck::Linearity, QuadCheck::Evaluation],
            "one bogus coordinate must be named by both lines that read it"
        );
        // And the response gates stay green: lines 7–8 do not read `z`, which is
        // why a verifier that ran only them would accept this transcript.
        let m = lv.quad_measure(&claim, &c, &both).expect("measure");
        assert!(m.inner_sum <= bounds.b && m.outer_sum <= bounds.b_o);
    }

    /// `q_o ≠ q` is not decoration: the outer commitment is reduced mod `q_o`,
    /// and line 6's residual is only a rounding error against *that* value.
    #[test]
    fn the_outer_level_lives_in_its_own_ring() {
        assert_ne!(Q_O, Q_INNER, "the protocol has a distinct outer modulus");
        assert!(Q_O < Q_INNER, "and it is the smaller one (p. 9)");
        let lv = levels();
        let a = aug();
        let outer = lv.outer_commit(&lv.stack(&a));
        // `û = ⌊(D t̂)/B_u⌉` with `D t̂ (mod q_o)`, so every entry is in
        // `[0, q_o/B_u]`. Under the collapsed reading (`q_o = q`) the same 3κ
        // entries would spread over `[0, q/B_u]`, i.e. a mean `q/q_o ≈ 2×`
        // larger: the range check below is what distinguishes the two.
        let cap = (Q_O / B_U) as i64;
        assert!(
            outer.iter().all(|&x| (0..=cap).contains(&x)),
            "û escaped [0, q_o/B_u]: {:?}",
            outer
        );
        let mean = outer.iter().sum::<i64>() / i64::try_from(outer.len()).unwrap();
        assert!(
            mean < cap,
            "û's mean {mean} sits where a mod-q reduction would put it (cap {cap})"
        );
        // Line 6 then reads back as the rounding error it is.
        let (lv2, _, c, proof, outer2, _, v1, w0, y) = transcript();
        assert_eq!(lv2.kappa(), outer2.len());
        let m = lv2
            .quad_measure(&claim_of(&outer2, &v1, &w0, y), &c, &proof)
            .expect("measure");
        assert!(
            m.s.iter().all(|&x| x.abs() as u64 <= B_U),
            "s is not a rounding error: {:?}",
            m.s
        );
        assert_eq!(lv.outer_key().rows(), lv.kappa());
        assert_eq!(lv.outer_key().cols(), lv.stack_len());
    }

    /// Theorem 2's shape requirement, measured: `B = [B′ | I_µ]` is what stops
    /// the levelled commitment from naming its own message.
    #[test]
    fn the_identity_block_leaves_the_message_free() {
        let lv = levels();
        assert_eq!(lv.mu(), MU);
        assert_eq!(lv.nu(), NU);
        assert_eq!(lv.rand_rows(), MU + NU, "R has µ+ν rows per column");
        // `[A | B′ | I_µ]` has rank exactly µ — the identity block alone reaches
        // it — so the kernel dimension is `m₁+1+ν`, and it is positive: the
        // commitment does not determine the augmented column.
        assert_eq!(lv.preimage_freedom(), AUG_ROWS + NU);
        assert!(lv.preimage_freedom() > 0);
        // `B·r` really is `B′r̃ + r̂`: the first ν entries meet `B′`, the last µ
        // pass through the identity untouched.
        let r: Vec<Z1Coeff> = (0..lv.rand_rows())
            .map(|i| from_centered::<Z1Coeff>(i as i64 - 1))
            .collect();
        let direct = lv.mask_block().apply(&r);
        let expect: Vec<Z1Coeff> = (0..MU)
            .map(|e| {
                let mut acc = r[NU + e];
                for (j, rj) in r[..NU].iter().enumerate() {
                    acc += lv.mask_block().b_prime.entry(e, j) * *rj;
                }
                acc
            })
            .collect();
        assert_eq!(direct, expect, "B·r must be B′r̃ + the identity part");
        assert_eq!(direct.len(), MU);
        // The identity part alone: with `r̃ = 0`, `B·r = r̂` verbatim — which is
        // precisely what [`MaskBlock::mask_hiding`] then shows the compression
        // destroying.
        let bare: Vec<Z1Coeff> = (0..lv.rand_rows())
            .map(|i| from_centered::<Z1Coeff>(if i >= NU { i as i64 - 9 } else { 0 }))
            .collect();
        assert_eq!(
            lv.mask_block().apply(&bare),
            bare[NU..],
            "with no B′ secret the mask is the identity"
        );
    }

    /// B.5 (p. 18) as a measurement: the rounded mask `⌊(B r)/B_t⌉` against the
    /// same rounding of a uniform `R_q^µ`. At `ν = 0` there is no `B′`, the mask
    /// is `≤ B_χ` entrywise, the compression erases it, and every draw collapses
    /// to `0` — which is `⌊Af̂*ₖ/B_t⌉`: the message, uncompressed.
    #[test]
    fn the_mask_flattens_the_rounded_commitment_and_nu_zero_does_not() {
        let seed = [0x2du8; 32];
        let bare = MaskBlock::new(&seed, MU, 0).mask_hiding(B_CHI, B_T, 200, 16, &seed);
        assert!(
            bare.sd_vs_uniform > 0.8,
            "with no B′ block the rounded commitment is the message (SD = {})",
            bare.sd_vs_uniform
        );
        assert_eq!(
            bare.zero_noise, bare.trials,
            "every ν = 0 draw rounds the mask to zero"
        );
        let masked = MaskBlock::new(&seed, MU, NU).mask_hiding(B_CHI, B_T, 200, 16, &seed);
        assert!(
            masked.sd_vs_uniform < bare.sd_vs_uniform / 2.0,
            "B′ must flatten the histogram: {} vs {}",
            masked.sd_vs_uniform,
            bare.sd_vs_uniform
        );
        assert!(
            masked.zero_noise > 0 && masked.zero_noise * 5 < masked.trials,
            "the residual `B·r = 0` event is the leakage the measurement can see: {:?}",
            (masked.zero_noise, masked.trials)
        );
        assert!(masked.distinct > bare.distinct);
    }

    /// `counted_rows < m₁+1` exempts a row from line 7. The exemption is only
    /// honest while its *cost* is measured: `inner_sum_full` reports the same
    /// transcript with the exempt rows in, and here it straddles the bound.
    #[test]
    fn an_exempt_row_is_a_measured_cost_not_a_hidden_one() {
        let shape = Shape {
            counted_rows: AUG_ROWS - 1,
            ..shape()
        };
        let lv = MleLevels::new(&[7u8; 32], &[8u8; 32], &[9u8; 32], &shape);
        assert_eq!(lv.counted_rows(), AUG_ROWS - 1);
        assert_eq!(lv.aug_rows(), AUG_ROWS);
        // A committed matrix whose value-mask row is *not* short — the `p = q`
        // reading's uniform mask, which no bound can admit.
        let mut a = aug();
        for (i, cell) in a.iter_mut().enumerate() {
            if i / COLS == AUG_ROWS - 1 {
                *cell = from_centered::<Z1Coeff>(300_000 + i as i64);
            }
        }
        let c = challenge(4);
        let stack = lv.stack(&a);
        let outer = lv.outer_commit(&stack);
        let (v1, w0) = (v1(), w0());
        let y = y_star_of(&lv, &a);
        let proof = lv.quad_prove(&a, &c, &v1).expect("prove");
        let claim = claim_of(&outer, &v1, &w0, y);
        let bounds = params(300).gates().expect("bounds");
        let m = lv.quad_measure(&claim, &c, &proof).expect("measure");
        assert!(
            m.inner_sum <= bounds.b,
            "the exempted transcript must still pass line 7: {} > {}",
            m.inner_sum,
            bounds.b
        );
        assert!(
            m.inner_sum_full > bounds.b,
            "and the exemption must be what saved it: full {} vs B {}",
            m.inner_sum_full,
            bounds.b
        );
        assert!(m.inner_sum_full > m.inner_sum, "the cost is positive");
        // Same matrix, no exemption: the gate now says what it measured.
        let strict = levels();
        let s2 = strict.stack(&a);
        let o2 = strict.outer_commit(&s2);
        let p2 = strict.quad_prove(&a, &c, &v1).expect("prove");
        let report = strict
            .quad_report(&claim_of(&o2, &v1, &w0, y), &c, &p2, &bounds)
            .expect("report");
        assert_eq!(report, vec![QuadCheck::InnerNorm]);
    }

    /// A stack that skipped the compression is *not* a rounding error any more,
    /// so both response gates fail together — and the report names both instead
    /// of stopping at the first. The reading is B.6's (p. 18): `‖t̂‖∞ ≤ q/B_t`
    /// holds "by the rounding definition", so removing the rounding removes the
    /// bound. Lines 9 and 10 stay green: they read `z`, `f̂*` and `c`, none of
    /// which this tamper touches.
    #[test]
    fn skipping_the_compression_is_the_l8_failure_it_claims_to_be() {
        let lv = levels();
        let a = aug();
        let bounds = params(300).gates().expect("bounds");
        let outer = lv.outer_commit(&lv.stack(&a));
        let c = challenge(2);
        let (v1, w0) = (v1(), w0());
        let y = y_star_of(&lv, &a);
        let claim = claim_of(&outer, &v1, &w0, y);
        let honest = lv.quad_prove(&a, &c, &v1).expect("prove");
        // The uncompressed stack: `B_t = 1` leaves every entry a full residue.
        let raw: Vec<i64> = (0..lv.cols())
            .flat_map(|k| {
                let (f, r) = lv.column_pair(&a, k);
                lv.inner_apply(&f, &r)
                    .iter()
                    .map(Z1Coeff::centered)
                    .collect::<Vec<i64>>()
            })
            .collect();
        assert!(
            raw.iter().any(|&x| x.abs() > i64::try_from(B_T).unwrap()),
            "with no compression the stack stays field-sized"
        );
        let uncompressed = MleQuadProof {
            t_hat: raw,
            ..honest.clone()
        };
        assert_eq!(
            lv.quad_report(&claim, &c, &uncompressed, &bounds)
                .expect("report"),
            // Exactly the two *gates*: the tamper touches `t̂` alone, and lines
            // 9–10 read `z`, `f̂*`, `c` and the instance, none of which moved.
            vec![QuadCheck::InnerNorm, QuadCheck::OuterNorm],
            "an uncompressed stack breaks both gates, and the set shows it"
        );
        assert!(lv
            .quad_report(&claim, &c, &honest, &bounds)
            .expect("report")
            .is_empty());
    }

    #[test]
    fn the_bounds_are_the_paper_formulas_and_strictly_grow_the_input() {
        let p = params(300);
        let base = p.theorem3().expect("thm 3");
        // Theorem 3 (p. 10): B = b√((m₁+1)d) + B_χ√((μ+ν)d) + B_t√(μd), read
        // against the crate's own ceiling roots, written out longhand here so a
        // refactor of the helper cannot quietly change what the gate compares.
        let r = |k: u128| exact_l2::isqrt_ceil(k);
        assert_eq!(
            base.b,
            u128::from(B_E) * r(AUG_ROWS as u128)
                + u128::from(B_CHI) * r(RAND_ROWS as u128)
                + u128::from(B_T) * r(MU as u128)
        );
        assert_eq!(
            base.b_o,
            (u128::from(p.q) + u128::from(B_T) - 1) / u128::from(B_T) * r((MU * COLS) as u128)
                + u128::from(B_U) * r(KAPPA as u128)
        );
        let agg = p.theorem5(&base).expect("thm 5");
        assert_eq!(
            agg.b,
            2 * 2 * base.b
                + 300 * (r(2 * AUG_ROWS as u128) + r(2 * RAND_ROWS as u128))
                + u128::from(B_T) * r(MU as u128)
        );
        assert_eq!(agg.b_o, 4 * base.b_o + base.b_o);
        let quad = p.theorem6(&agg).expect("thm 6");
        assert_eq!(quad.b, 3 * 2 * agg.b, "B = n₀·B_C·B (p. 12)");
        assert_eq!(quad.b_o, agg.b_o, "B_o = B_o (p. 12)");
        assert_eq!(quad, p.gates().expect("chain"));
        // The one-step reading: each relaxation is strictly above its input,
        // which is what a fixed-point reading (`B = m₀B_C·B + …`, m₀B_C = 4 > 1)
        // could never produce — it would demand a negative B.
        assert!(base.b < agg.b && agg.b < quad.b);
        assert!(base.b_o < agg.b_o);
    }

    /// Theorem 1's outer hypothesis is `MSIS_{q_o,κ,2B_αB_o}`: the modulus has
    /// to be able to *express* the bound the assumption is stated at. The
    /// headroom is signed, so a toy that runs out of modulus says so.
    #[test]
    fn the_outer_modulus_has_to_be_able_to_say_the_bound() {
        let p = params(300);
        let gates = p.gates().expect("chain");
        // B_α = 1 is the honest reading (Theorem 3, p. 10: both relaxation
        // factors are 1 for an honestly generated opening).
        let room = p.outer_msis_headroom(1, gates.b_o).expect("fits");
        assert!(
            room > 0,
            "q_o/2 must exceed Theorem 1's target 2·B_α·B_o: {}",
            room
        );
        assert_eq!(
            room,
            i128::try_from(u128::from(Q_O) / 2)
                .unwrap()
                .checked_sub(i128::try_from(2 * gates.b_o).unwrap())
                .unwrap()
        );
        // A bound past half the modulus is reported as a negative headroom, not
        // as silence.
        assert!(p.outer_msis_headroom(1, u128::from(Q_O)).is_some());
        assert!(p.outer_msis_headroom(1, u128::from(Q_O)) < Some(0));
        assert_eq!(p.outer_msis_headroom(1, u128::MAX), None);
    }

    #[test]
    fn sigma_grows_with_the_bound_it_has_to_dominate() {
        let p = params(300);
        let base = p.theorem3().expect("thm 3");
        let want = p.sigma_required(base.b, 1).expect("sigma");
        assert_eq!(want, 14 * 2 * exact_l2::isqrt_ceil(3) * 2 * base.b);
        // Lemma 2's shape: a wider input bound needs a *wider* σ, and doubling
        // B doubles it.
        assert_eq!(
            p.sigma_required(base.b * 2, 1).expect("sigma"),
            want * 2,
            "σ = 14·m₀√n₀·B_C·B/ln M is a product, not a quotient"
        );
        assert_eq!(p.sigma_required(base.b, 0), None, "ln M = 0 is not a thing");
        // The instance's sampling width below that value is a rejection-rate
        // statement, not a gate statement — but it must be *visible*.
        assert!(
            p.sigma < want,
            "the fixture is meant to show σ below the required width"
        );
        assert!(
            params(want).theorem5(&base).expect("wider").b
                > p.theorem5(&base).expect("narrower").b
        );
    }

    #[test]
    fn ragged_or_unshortened_components_refuse_instead_of_passing() {
        let (lv, a, c, proof, outer, bounds, v1, w0, y) = transcript();
        let claim = claim_of(&outer, &v1, &w0, y);
        assert_eq!(
            lv.quad_prove(&a[..a.len() - 1], &c, &v1),
            Err(MleError::WrongLength)
        );
        assert_eq!(lv.quad_z(&a[..a.len() - 1], &v1), Err(MleError::WrongLength));
        assert_eq!(lv.quad_z(&a, &v1[..v1.len() - 1]), Err(MleError::WrongLength));
        let short = MleQuadProof {
            t_hat: proof.t_hat[..proof.t_hat.len() - 1].to_vec(),
            ..proof.clone()
        };
        assert_eq!(
            lv.quad_report(&claim, &c, &short, &bounds),
            Err(MleError::WrongLength)
        );
        // `z` has `n₀` entries — one per column, one per line-9 coordinate.
        assert_eq!(
            lv.quad_report(&claim, &c, &MleQuadProof { z: proof.z[..1].to_vec(), ..proof.clone() }, &bounds),
            Err(MleError::WrongLength)
        );
        // `û` is read mod `q_o`, so it has exactly `κ` entries.
        let short_outer = outer[..outer.len() - 2].to_vec();
        assert_eq!(
            lv.quad_report(&claim_of(&short_outer, &v1, &w0, y), &c, &proof, &bounds),
            Err(MleError::WrongLength)
        );
        assert_eq!(
            lv.quad_report(&claim_of(&outer, &v1, &w0[..w0.len() - 1], y), &c, &proof, &bounds),
            Err(MleError::WrongLength)
        );
        assert_eq!(
            lv.quad_report(&claim, &c[..1], &proof, &bounds),
            Err(MleError::WrongLength)
        );
        // A component the shape check accepts but the *gates* do not: an
        // absurdly tight bound must fail the lines, not error out.
        let tight = QuadBounds { b: 1, b_o: 1 };
        assert_eq!(
            lv.quad_report(&claim, &c, &proof, &tight).expect("report"),
            vec![QuadCheck::InnerNorm, QuadCheck::OuterNorm],
            "lines 9 and 10 are equations, not bounds: they stay green"
        );
    }

    #[test]
    fn the_integer_aggregate_is_what_fig_six_line_thirteen_computes() {
        let lv = levels();
        let a = aug();
        let stack = lv.stack(&a);
        assert_eq!(stack.len(), lv.stack_len());
        let other: Vec<i64> = stack.iter().map(|x| x + 1).collect();
        let mask: Vec<i64> = stack.iter().map(|x| x - 2).collect();
        let agg =
            MleLevels::integer_combination(&[3, -4], &[&stack, &other], &mask).expect("aggregate");
        for i in 0..stack.len() {
            assert_eq!(agg[i], 3 * stack[i] - 4 * other[i] + mask[i]);
        }
        // ragged parts and an out-of-range accumulator are refused
        assert!(MleLevels::integer_combination(&[3], &[&stack, &other], &mask).is_none());
        assert!(
            MleLevels::integer_combination(&[3, 4], &[&stack, &mask[..1].to_vec()], &mask)
                .is_none()
        );
        let huge = vec![i64::MAX; stack.len()];
        assert!(MleLevels::integer_combination(&[4, 4], &[&huge, &huge], &mask).is_none());
    }

    #[test]
    fn the_two_gates_share_one_norm_path_with_the_ring_gate() {
        // The sums the gates compare must be exactly what `exact_l2` computes
        // for the same lifted parts, so a second ℓ2 path cannot drift.
        let (lv, _, c, proof, outer, _, v1, w0, y) = transcript();
        let claim = claim_of(&outer, &v1, &w0, y);
        let m = lv.quad_measure(&claim, &c, &proof).expect("measure");
        let counted = lv.counted_rows();
        let f = ints_of(&proof.f_star[..counted]);
        let all = ints_of(&proof.f_star);
        let r = ints_of(&proof.r);
        let parts: &[&[i64]] = &[&f, &r, &m.h];
        assert_eq!(
            m.inner_sum,
            exact_l2::norm_sum_gate(parts, u128::MAX).expect("no bound")
        );
        let parts: &[&[i64]] = &[&all, &r, &m.h];
        assert_eq!(
            m.inner_sum_full,
            exact_l2::norm_sum_gate(parts, u128::MAX).expect("no bound")
        );
        let parts: &[&[i64]] = &[&m.s, &proof.t_hat];
        assert_eq!(
            m.outer_sum,
            exact_l2::norm_sum_gate(parts, u128::MAX).expect("no bound")
        );
    }
}
