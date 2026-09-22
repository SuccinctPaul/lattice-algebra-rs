//! Batched openings (Z7): prove `k` evaluation claims
//! `(uⱼ, x) ↦ yⱼ` — `k` independently committed polynomials opened at **one
//! common point** — with a single folded-opening vector.
//!
//! This is the PCS form of the LaBRADOR amortized opening (survey §1.1:
//! "r inner-product constraints proved at once via a small-norm linear
//! combination"): every claim whose proof would re-reveal an `m·δ`-element
//! folded opening `zⱼ = Σᵢ cᵢ⁽ʲ⁾·sᵢ⁽ʲ⁾` instead folds all of them into one
//! `z` under HyperBall weights, the same amortization the 2025–2026
//! successors build on (Akita's batched openings, SALSAA's
//! sumcheck-aided opening, Greyhound's shared-point batch mode). The
//! saving is `(k−1)·m·δ` ring elements; the combination weights are drawn
//! from the LaBRADOR *HyperBall* distribution (`‖β‖∞ ≤ 1`,
//! `‖β‖₁ ≤ [`L1_PER_POLY`]·k`) so the norm accounting stays provable:
//! `‖z‖∞ ≤ ‖β‖₁·maxⱼ‖zⱼ‖∞`.
//!
//! The shared point is load-bearing, not convenience: the second link
//! equation is linear in the digits *through* `a(x)ᵀ·G_m(z)`, and only a
//! common `a(x)` turns the per-claim equations into one equation in the
//! combined `z` without `βⱼβₗ` cross terms (`G_m(z) = Σⱼ βⱼ·G_m(zⱼ)` is
//! absorbed by the shared `a(x)`).
//!
//! # Why cross-point batching is not a local change
//!
//! The √N split exists because power weight tables **factor** as the
//! outer product `aⱼ·bᵢ = x^{j}·x^{im}`. Claims at `k` different points
//! carry `k` different power tables, and their γ-combination is a
//! per-position scaled table `Σᵢ γⁱ·xᵢ^{j}·Fᵢ[j]` that (a) does not
//! factor, so the √N-split opening equations no longer apply, and (b) as
//! a per-position rescaling of the witness, breaks the Ajtai commitment
//! linearity that would otherwise let the verifier recompute the combined
//! commitment from the `cᵢ` (`commit(Σ scaled Fᵢ) ≠ Σ scaled commit(Fᵢ)`).
//! The sumcheck-line reduction ends in an MLE claim
//! `Σ_g eq(r,g)·F[g]` whose weight table does not factor either, and the
//! only verifier-checkable bridge to the power-mode proof re-introduces a
//! non-unit-challenge annihilator slack (the row 19/24 blocker). The sound
//! routes and their quantified architectural cost: an MLE-native
//! (eq-weight) opening mode requires a **tall** commitment key
//! (`rows ≥ 2·cols` over the flattened digit witness ≈ 3000 ring-element
//! rows ⇒ multi-megabyte commitments) so the response link overdetermines
//! `z` and the claim check is non-vacuous; or the full LaBRADOR
//! amortized-openings machinery. Both are tracked as the cross-point
//! milestone (survey row 25).
//!
//! ```text
//! shared point x, per claim j:
//!     yⱼ = fⱼ(x),  wⱼ = a(x)ᵀ·Fⱼ,  vⱼ = D·ŵⱼ              (first messages)
//!     c⁽ʲ⁾ ← H(key, uⱼ, x, yⱼ, vⱼ)                        (per-claim challenges)
//!     zⱼ = Σᵢ cᵢ⁽ʲ⁾·sᵢ⁽ʲ⁾
//! batch step:
//!     β ← HyperBall(k)  from H(key, {uⱼ}, x, {yⱼ}, {vⱼ})
//!     z = Σⱼ βⱼ·zⱼ
//! proof = ({vⱼ}, {ŵⱼ}, z, {t̂ⱼ})
//! ```
//!
//! Verifier checks (gates first, then links):
//!
//! ```text
//! per claim j:   D·ŵⱼ == vⱼ,   wⱼᵀ·b(x) == yⱼ,   B·t̂ⱼ == uⱼ
//! batched:       Σⱼ βⱼ·(c⁽ʲ⁾ᵀ·wⱼ) == a(x)ᵀ·G_m(z)
//!                A·z == Σⱼ βⱼ·Σᵢ cᵢ⁽ʲ⁾·G_n(t̂ᵢ⁽ʲ⁾)
//! gates:         ŵⱼ, t̂ⱼ binary;   ‖z‖∞ ≤ β₁·k·r·d
//! ```
//!
//! The two batched equations are exactly the per-claim equations scaled by
//! `βⱼ` and summed — the `βⱼ` weights are Fiat–Shamir outputs bound to all
//! first messages, so claims cannot be mixed across batches. Extraction
//! keeps the single-protocol shape (a second accepting batch yields a
//! short kernel vector against the concatenated block-diagonal witness),
//! with the response bound inflated by the HyperBall budget. That bound
//! degrades linearly in `k`, so [`MAX_BATCH`] caps the toy instance;
//! re-derive the instance (and re-check with the Core-SVP estimator)
//! before raising it.
//!
//! # Example
//!
//! ```rust
//! use algebra::ring::PolynomialQuotientRing;
//! use zk::foundation::sampling::from_centered;
//! use zk::pcs::{self, batched, greyhound};
//!
//! let key = greyhound::GreyhoundKey::setup(&[7u8; 32]);
//! let polys: Vec<Vec<pcs::RingElt>> = (0..3)
//!     .map(|p| {
//!         (0..pcs::N_DEG)
//!             .map(|i| {
//!                 let coeffs: Vec<_> = (0..pcs::DIM)
//!                     .map(|j| {
//!                         from_centered::<pcs::Z1Coeff>(
//!                             ((p as i64 * 11 + i as i64 * 3 + j as i64) % 9) - 4,
//!                         )
//!                     })
//!                     .collect();
//!                 algebra::ring::poly_ring::PolyRing::from_coefficients(coeffs)
//!             })
//!             .collect()
//!     })
//!     .collect();
//! let coms: Vec<_> = polys.iter().map(|f| greyhound::commit(&key, f).unwrap()).collect();
//! let x = batched::eval_point(5);
//! let refs: Vec<&[pcs::RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
//!
//! let (ys, proof) = batched::open_batch(&key, &refs, &x).expect("lengths ok");
//! assert!(batched::verify_batch(&key, &coms, &x, &ys, &proof).is_ok());
//! // one folded opening instead of three:
//! assert!(proof.to_bytes().len() < 3 * greyhound::OpeningProof::encoded_len());
//! ```

use crate::foundation::encoding::{le_bytes_to_u32s, ring_from_u32, ring_to_u32, u32s_to_le_bytes};
use crate::foundation::fs::absorb_rings;
use crate::foundation::sampling::hyperball_vec;
use crate::pcs::gadget::{recombine_digits, recombine_digits_mod};
use crate::pcs::greyhound::{
    challenges, derive_witness, dot, ntt_op, pow_table, ring_zero, vec_inf_norm, Committed,
    GreyhoundKey, PcsError, PolyCommitment,
};
use crate::pcs::{RingElt, Z1Coeff, B_Z, DELTA, DIM, M_COLS, N_DEG, N_ROWS, R_COLS};
use algebra::crypto::sampling::BitStream;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::{vec, vec::Vec};

/// Transcript domain for the batched evaluation protocol (the per-claim
/// challenges keep the single-protocol domain; only the combination step
/// is derived here).
const FS_DOMAIN_BATCH: &[u8] = b"lattice-algebra/Z7/greyhound-pcs-batch";

/// XOF label under which the HyperBall weights are re-expanded from the
/// batch transcript seed.
const CHALLENGE_LABEL: &[u8] = b"B";

/// Largest batch the toy instance's norm accounting supports: the
/// response bound `L1_PER_POLY·k·r·d` must stay a comfortable fraction of
/// `q` (see the module soundness notes).
pub const MAX_BATCH: usize = 8;

/// Hyperball l1 budget per claim: `E[‖βⱼ‖₁] = 2·d/3 ≈ 171` for ternary
/// coefficients, so `256` accepts with overwhelming probability while
/// inflating the response bound by only 1.5× per claim.
pub const L1_PER_POLY: u64 = 256;

/// The batched opening proof: per-claim first messages and inner-commitment
/// digits, and the **single** combined folded opening `z = Σⱼ βⱼ·zⱼ`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchedOpeningProof {
    /// `vⱼ = D·ŵⱼ` — row-combination commitments (first messages).
    pub v: Vec<Vec<RingElt>>,
    /// `ŵⱼ = G_r⁻¹(wⱼ)` — binary digits of the row combinations.
    pub w_hat: Vec<Vec<RingElt>>,
    /// `z = Σⱼ βⱼ·zⱼ` — the one folded opening for the whole batch.
    pub z: Vec<RingElt>,
    /// `t̂ⱼ` — binary digits of the inner commitments (block major).
    pub t_hat: Vec<Vec<RingElt>>,
}

/// Ring elements revealed per claim (`v`, `ŵ`, `t̂`).
const PER_CLAIM_ELTS: usize = N_ROWS + R_COLS * DELTA + R_COLS * N_ROWS * DELTA;

impl BatchedOpeningProof {
    /// Serialized size in bytes for a batch of `k` claims (all vectors are
    /// fixed length per claim; only `z` is batch-global).
    pub fn encoded_len(k: usize) -> usize {
        (k * PER_CLAIM_ELTS + M_COLS * DELTA) * DIM * 4
    }

    /// Number of claims this proof covers.
    pub fn len(&self) -> usize {
        self.v.len()
    }

    /// Always `false` for proofs produced by [`open_batch`] (empty batches
    /// are rejected at the API boundary).
    pub fn is_empty(&self) -> bool {
        self.v.is_empty()
    }

    /// Canonical wire encoding: per-claim fields in claim order (each in
    /// declaration order), then the batch-global `z`.
    ///
    /// # Panics
    /// If the proof vectors have non-canonical lengths (never the case for
    /// proofs produced by [`open_batch`]).
    pub fn to_bytes(&self) -> Vec<u8> {
        let k = self.len();
        let mut out = Vec::with_capacity(Self::encoded_len(k));
        for j in 0..k {
            for field in [&self.v[j], &self.w_hat[j], &self.t_hat[j]] {
                for elt in field.iter() {
                    out.extend_from_slice(&u32s_to_le_bytes(&ring_to_u32::<Z1Coeff, DIM>(elt)));
                }
            }
        }
        for elt in self.z.iter() {
            out.extend_from_slice(&u32s_to_le_bytes(&ring_to_u32::<Z1Coeff, DIM>(elt)));
        }
        out
    }

    /// Parses [`to_bytes`] output; `None` on any length or encoding error
    /// (the batch size is recovered from the byte length and must be a
    /// canonical shape).
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        let elt_bytes = DIM * 4;
        let total_elts = bytes.len().checked_sub(M_COLS * DELTA * elt_bytes)? / elt_bytes;
        if total_elts % PER_CLAIM_ELTS != 0 {
            return None;
        }
        let k = total_elts / PER_CLAIM_ELTS;
        if k == 0 || bytes.len() != Self::encoded_len(k) {
            return None;
        }
        let mut cursor = bytes;
        let mut v = Vec::with_capacity(k);
        let mut w_hat = Vec::with_capacity(k);
        let mut t_hat = Vec::with_capacity(k);
        for _ in 0..k {
            v.push(take_elts(&mut cursor, N_ROWS)?);
            w_hat.push(take_elts(&mut cursor, R_COLS * DELTA)?);
            t_hat.push(take_elts(&mut cursor, R_COLS * N_ROWS * DELTA)?);
        }
        let z = take_elts(&mut cursor, M_COLS * DELTA)?;
        Some(BatchedOpeningProof { v, w_hat, z, t_hat })
    }
}

/// Parses `count` consecutive ring elements off the front of `cursor`.
fn take_elts(cursor: &mut &[u8], count: usize) -> Option<Vec<RingElt>> {
    let chunk = DIM * 4;
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        if cursor.len() < chunk {
            return None;
        }
        let (head, tail) = cursor.split_at(chunk);
        let coeffs = le_bytes_to_u32s(head)?;
        if coeffs.len() != DIM {
            return None;
        }
        out.push(ring_from_u32::<Z1Coeff, DIM>(
            coeffs[..DIM].try_into().ok()?,
        ));
        *cursor = tail;
    }
    Some(out)
}

/// The verifier response bound for a batch of `k` claims:
/// `‖z‖∞ ≤ ‖β‖₁·maxⱼ‖zⱼ‖∞ ≤ (L1_PER_POLY·k)·(r·d)`.
pub fn batch_z_bound(k: usize) -> u64 {
    L1_PER_POLY * k as u64 * B_Z
}

/// A convenient nonzero evaluation point for examples and tests: the ring
/// element with constant coefficient `v`.
///
/// # Panics
/// If `v` does not fit the scalar modulus (never for protocol values).
pub fn eval_point(v: u64) -> RingElt {
    let mut coeffs = vec![Z1Coeff::ZERO; DIM];
    coeffs[0] = Z1Coeff::from(v.rem_euclid(Z1Coeff::MODULUS));
    PolyRing::from_coefficients(coeffs)
}

/// Evaluates `k` polynomials at the **common point** `x` and proves all
/// `k` claims with one combined folded opening.
///
/// # Errors
/// - [`PcsError::WrongLength`] if `fs` is empty or any polynomial is not
///   [`N_DEG`] long;
/// - [`PcsError::BatchTooLarge`] if `fs.len() > [`MAX_BATCH`]`.
pub fn open_batch(
    key: &GreyhoundKey,
    fs: &[&[RingElt]],
    x: &RingElt,
) -> Result<(Vec<RingElt>, BatchedOpeningProof), PcsError> {
    let k = fs.len();
    if k == 0 {
        return Err(PcsError::WrongLength);
    }
    if k > MAX_BATCH {
        return Err(PcsError::BatchTooLarge);
    }
    for f in fs {
        if f.len() != N_DEG {
            return Err(PcsError::WrongLength);
        }
    }

    let wit: Vec<Committed> = fs
        .iter()
        .map(|f| derive_witness(key, f))
        .collect::<Result<_, _>>()?;

    // Shared split factorization of the point; per-claim evaluation rows
    // and first messages.
    let powers = pow_table(x, N_DEG);
    let a_pow = &powers[..M_COLS];
    let b_pow: Vec<RingElt> = (0..R_COLS).map(|i| powers[i * M_COLS].clone()).collect();
    let mut ys = Vec::with_capacity(k);
    let mut v = Vec::with_capacity(k);
    let mut w_hat = Vec::with_capacity(k);
    let mut zs = Vec::with_capacity(k);
    for f in fs.iter() {
        let w: Vec<RingElt> = (0..R_COLS)
            .map(|i| dot(&f[i * M_COLS..(i + 1) * M_COLS], a_pow))
            .collect();
        ys.push(dot(&w, &b_pow));

        let wh = crate::pcs::gadget::decompose_digits(&w);
        v.push(key.d.commit(&wh, &ntt_op()));
        w_hat.push(wh);
    }

    // Per-claim challenges and folded openings (block-wise accumulation
    // over the column-digit layout, exactly as in the single protocol).
    for (j, wj) in wit.iter().enumerate() {
        let c = challenges(key, &wj.u, x, &ys[j], &v[j]);
        let mut z: Vec<RingElt> = wj.s[..M_COLS * DELTA]
            .iter()
            .map(|s_l| s_l.clone() * &c[0])
            .collect();
        for (c_i, s_i) in c.iter().zip(wj.s.chunks(M_COLS * DELTA)).skip(1) {
            for (z_l, s_l) in z.iter_mut().zip(s_i) {
                *z_l = z_l.clone() + s_l.clone() * c_i;
            }
        }
        zs.push(z);
    }

    // Batch step: HyperBall weights bound to every first message, then the
    // single combined folded opening.
    let beta = batch_challenges(
        key,
        &wit.iter().map(|w| w.u.as_slice()).collect::<Vec<_>>(),
        x,
        &ys,
        &v,
    );
    let mut z: Vec<RingElt> = zs[0].iter().map(|z_l| z_l.clone() * &beta[0]).collect();
    for (b_j, z_j) in beta.iter().zip(zs.iter()).skip(1) {
        for (z_l, z_jl) in z.iter_mut().zip(z_j) {
            *z_l = z_l.clone() + z_jl.clone() * b_j;
        }
    }

    Ok((
        ys,
        BatchedOpeningProof {
            v,
            w_hat,
            z,
            t_hat: wit.iter().map(|w| w.t_hat.clone()).collect(),
        },
    ))
}

/// Verifies `k` evaluation claims `(uⱼ, x) ↦ yⱼ` against the batched
/// proof: norm gates first (they bound the aMSIS extraction instance),
/// then the per-claim links and the two batched equations.
///
/// # Errors
/// - [`PcsError::WrongLength`] on non-canonical lengths or an empty batch;
/// - [`PcsError::BatchTooLarge`] if the claim count exceeds [`MAX_BATCH`];
/// - [`PcsError::NormViolation`] if any norm gate fails;
/// - [`PcsError::LinkCheckFailed`] if any link equation fails.
pub fn verify_batch(
    key: &GreyhoundKey,
    coms: &[PolyCommitment],
    x: &RingElt,
    ys: &[RingElt],
    proof: &BatchedOpeningProof,
) -> Result<(), PcsError> {
    let k = coms.len();
    if k != ys.len() || k != proof.len() {
        return Err(PcsError::WrongLength);
    }
    if k > MAX_BATCH {
        return Err(PcsError::BatchTooLarge);
    }
    if k == 0 {
        return Err(PcsError::WrongLength);
    }
    for ((v_j, wh_j), th_j) in proof.v.iter().zip(&proof.w_hat).zip(&proof.t_hat) {
        if v_j.len() != N_ROWS
            || wh_j.len() != R_COLS * DELTA
            || th_j.len() != R_COLS * N_ROWS * DELTA
        {
            return Err(PcsError::WrongLength);
        }
    }
    if proof.z.len() != M_COLS * DELTA {
        return Err(PcsError::WrongLength);
    }

    // Gates first: binary digits everywhere and the HyperBall-inflated
    // response bound (the aMSIS extraction budget).
    for (wh_j, th_j) in proof.w_hat.iter().zip(&proof.t_hat) {
        if vec_inf_norm(wh_j) > 1 || vec_inf_norm(th_j) > 1 {
            return Err(PcsError::NormViolation);
        }
    }
    if vec_inf_norm(&proof.z) > batch_z_bound(k) {
        return Err(PcsError::NormViolation);
    }

    // Shared split factorization of the point; per-claim challenges.
    let powers = pow_table(x, N_DEG);
    let a_pow = &powers[..M_COLS];
    let b_pow: Vec<RingElt> = (0..R_COLS).map(|i| powers[i * M_COLS].clone()).collect();
    let cs: Vec<Vec<RingElt>> = (0..k)
        .map(|j| challenges(key, &coms[j].u, x, &ys[j], &proof.v[j]))
        .collect();
    let beta = batch_challenges(
        key,
        &coms.iter().map(|c| c.u.as_slice()).collect::<Vec<_>>(),
        x,
        ys,
        &proof.v,
    );

    // Per-claim links: row-combination commitment, second half of the
    // evaluation, and the outer commitment.
    for j in 0..k {
        if key.d.commit(&proof.w_hat[j], &ntt_op()) != proof.v[j] {
            return Err(PcsError::LinkCheckFailed);
        }
        let w = recombine_digits(&proof.w_hat[j]);
        if dot(&w, &b_pow) != ys[j] {
            return Err(PcsError::LinkCheckFailed);
        }
        if key.b.commit(&proof.t_hat[j], &ntt_op()) != coms[j].u {
            return Err(PcsError::LinkCheckFailed);
        }
    }

    // Batched equation 1: Σⱼ βⱼ·(cⱼᵀ·wⱼ) == a(x)ᵀ·G_m(z) — the shared
    // `a(x)` is what makes the per-claim equations merge without cross
    // terms.
    let g_z = recombine_digits_mod(&proof.z);
    let mut lhs = ring_zero();
    for j in 0..k {
        let w = recombine_digits(&proof.w_hat[j]);
        lhs += dot(&cs[j], &w) * &beta[j];
    }
    if lhs != dot(a_pow, &g_z) {
        return Err(PcsError::LinkCheckFailed);
    }

    // Batched equation 2: A·z == Σⱼ βⱼ·Σᵢ cᵢ⁽ʲ⁾·G_n(t̂ᵢ⁽ʲ⁾).
    let az = key.a.commit(&proof.z, &ntt_op());
    for (az_k, az_elt) in az.iter().enumerate() {
        let mut rhs = ring_zero();
        for j in 0..k {
            for (c_i, block) in cs[j].iter().zip(proof.t_hat[j].chunks(N_ROWS * DELTA)) {
                let t_i = recombine_digits(block);
                rhs += t_i[az_k].clone() * c_i * &beta[j];
            }
        }
        if az_elt != &rhs {
            return Err(PcsError::LinkCheckFailed);
        }
    }
    Ok(())
}

/// Fiat–Shamir HyperBall weights for the batch step: binds (key, every
/// `uⱼ`, the shared `x`, every `yⱼ`, every `vⱼ`) and derives `k` ring
/// elements from the restricted ball `‖β‖∞ ≤ 1`, `‖β‖₁ ≤ L1_PER_POLY·k` —
/// the norm budget the folded-opening gate and the soundness accounting
/// both read.
///
/// # Panics
/// If the rejection loop exhausts (statistically unreachable for the
/// documented budget; `256` per claim is 1.5× the ternary expectation).
fn batch_challenges(
    key: &GreyhoundKey,
    us: &[&[RingElt]],
    x: &RingElt,
    ys: &[RingElt],
    vs: &[Vec<RingElt>],
) -> Vec<RingElt> {
    let mut tr = Transcript::<Shake256Xof>::new(FS_DOMAIN_BATCH);
    tr.absorb(b"key", key.seed());
    for j in 0..us.len() {
        absorb_rings(&mut tr, b"u", us[j]);
        absorb_rings(&mut tr, b"y", core::slice::from_ref(&ys[j]));
        absorb_rings(&mut tr, b"v", &vs[j]);
    }
    absorb_rings(&mut tr, b"x", core::slice::from_ref(x));
    let seed = tr.challenge_bytes(64);
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(CHALLENGE_LABEL);
    xof.absorb(&seed);
    let mut stream = BitStream::new(&mut xof);
    let k = us.len();
    hyperball_vec::<Z1Coeff, Shake256Xof, DIM>(&mut stream, k, 1, L1_PER_POLY * k as u64, 1 << 20)
        .expect("hyperball batch challenge must sample for the documented budget")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use crate::pcs::greyhound;
    use algebra::ring::traits::CenteredRing;

    /// Deterministic test polynomial with small coefficients.
    fn test_poly(seed: u64) -> Vec<RingElt> {
        (0..N_DEG)
            .map(|i| {
                let coeffs: Vec<_> = (0..DIM)
                    .map(|j| {
                        from_centered::<Z1Coeff>(
                            ((seed as i64 * 7 + i as i64 * 3 + j as i64) % 9) - 4,
                        )
                    })
                    .collect();
                PolyRing::from_coefficients(coeffs)
            })
            .collect()
    }

    /// Test evaluation point with a small nonconstant part.
    fn test_x(v: u64) -> RingElt {
        let mut coeffs = vec![Z1Coeff::ZERO; DIM];
        coeffs[0] = Z1Coeff::from(v);
        coeffs[1] = Z1Coeff::from(v / 2 + 1);
        PolyRing::from_coefficients(coeffs)
    }

    #[test]
    fn honest_batch_verifies_and_matches_single_opens() {
        let key = GreyhoundKey::setup(&[1u8; 32]);
        let polys: Vec<Vec<RingElt>> = (0..4).map(|p| test_poly(p + 3)).collect();
        let refs: Vec<&[RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
        let x = test_x(11);
        let coms: Vec<PolyCommitment> = polys
            .iter()
            .map(|f| greyhound::commit(&key, f).unwrap())
            .collect();

        let (ys, proof) = open_batch(&key, &refs, &x).expect("lengths ok");
        assert_eq!(ys.len(), 4);
        assert!(verify_batch(&key, &coms, &x, &ys, &proof).is_ok());

        // each batched claim equals the single-protocol evaluation
        for j in 0..4 {
            let (y_single, _) = greyhound::open(&key, &polys[j], &x).unwrap();
            assert_eq!(ys[j], y_single);
        }

        // determinism
        let (ys2, proof2) = open_batch(&key, &refs, &x).unwrap();
        assert_eq!(ys, ys2);
        assert_eq!(proof, proof2);
    }

    #[test]
    fn single_claim_batch_behaves_like_a_small_batch() {
        let key = GreyhoundKey::setup(&[2u8; 32]);
        let f = test_poly(9);
        let x = test_x(33);
        let com = greyhound::commit(&key, &f).unwrap();
        let (ys, proof) = open_batch(&key, &[&f], &x).unwrap();
        assert_eq!(ys.len(), 1);
        assert!(verify_batch(&key, core::slice::from_ref(&com), &x, &ys, &proof).is_ok());
    }

    #[test]
    fn wrong_lengths_and_oversized_batches_are_typed_rejections() {
        let key = GreyhoundKey::setup(&[3u8; 32]);
        let f = test_poly(1);
        let x = eval_point(2);

        // empty batch
        assert_eq!(open_batch(&key, &[], &x), Err(PcsError::WrongLength));
        // non-canonical polynomial length
        assert_eq!(
            open_batch(&key, &[&f[..N_DEG - 1]], &x),
            Err(PcsError::WrongLength)
        );
        // oversized batch: rejected before any witness derivation
        let big: Vec<&[RingElt]> = (0..MAX_BATCH + 1).map(|_| f.as_slice()).collect();
        assert_eq!(open_batch(&key, &big, &x), Err(PcsError::BatchTooLarge));

        // malformed proof vectors
        let com = greyhound::commit(&key, &f).unwrap();
        let (ys, mut proof) = open_batch(&key, &[&f, &f], &x).unwrap();
        proof.z.pop();
        assert_eq!(
            verify_batch(&key, &[com.clone(), com.clone()], &x, &ys, &proof),
            Err(PcsError::WrongLength)
        );
        // claim-count mismatch
        let (ys, proof) = open_batch(&key, &[&f, &f], &x).unwrap();
        assert_eq!(
            verify_batch(&key, core::slice::from_ref(&com), &x, &ys, &proof),
            Err(PcsError::WrongLength)
        );
    }

    #[test]
    fn tampered_claims_and_proofs_are_rejected() {
        let key = GreyhoundKey::setup(&[4u8; 32]);
        let polys: Vec<Vec<RingElt>> = (0..3).map(|p| test_poly(p + 5)).collect();
        let refs: Vec<&[RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
        let x = test_x(21);
        let coms: Vec<PolyCommitment> = polys
            .iter()
            .map(|f| greyhound::commit(&key, f).unwrap())
            .collect();
        let (ys, proof) = open_batch(&key, &refs, &x).unwrap();

        // wrong claimed evaluation for claim 1 ⇒ per-claim check 2 fails
        let mut bad_ys = ys.clone();
        bad_ys[1] = bad_ys[1].clone()
            + PolyRing::from_coefficients({
                let mut c = vec![Z1Coeff::ZERO; DIM];
                c[0] = Z1Coeff::ONE;
                c
            });
        assert_eq!(
            verify_batch(&key, &coms, &x, &bad_ys, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // claims shuffled across commitments ⇒ the per-claim links fail
        let mut shuffled = ys.clone();
        shuffled.reverse();
        assert_eq!(
            verify_batch(&key, &coms, &x, &shuffled, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // a different shared point ⇒ checks 2/3 fail for every claim
        assert_eq!(
            verify_batch(&key, &coms, &test_x(22), &ys, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered row-combination commitment for claim 2 ⇒ check 1 fails
        let mut bad = proof.clone();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad.v[2][1]);
        coeffs[11] ^= 1;
        bad.v[2][1] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify_batch(&key, &coms, &x, &ys, &bad),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered combined folded opening ⇒ batched equation 1 fails
        let mut bad = proof.clone();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad.z[5]);
        coeffs[3] ^= 1;
        bad.z[5] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify_batch(&key, &coms, &x, &ys, &bad),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered inner-commitment digits for claim 0 ⇒ batched equation 2
        // or the outer link fails
        let mut bad = proof.clone();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad.t_hat[0][100]);
        coeffs[9] ^= 1;
        bad.t_hat[0][100] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify_batch(&key, &coms, &x, &ys, &bad),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered commitment for claim 1 ⇒ outer link fails
        let mut bad_coms = coms.clone();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad_coms[1].u[0]);
        coeffs[7] ^= 1;
        bad_coms[1].u[0] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify_batch(&key, &bad_coms, &x, &ys, &proof),
            Err(PcsError::LinkCheckFailed)
        );
    }

    #[test]
    fn norm_gates_fire_before_links() {
        let key = GreyhoundKey::setup(&[5u8; 32]);
        let polys: Vec<Vec<RingElt>> = (0..2).map(|p| test_poly(p + 7)).collect();
        let refs: Vec<&[RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
        let x = test_x(51);
        let coms: Vec<PolyCommitment> = polys
            .iter()
            .map(|f| greyhound::commit(&key, f).unwrap())
            .collect();
        let (ys, mut proof) = open_batch(&key, &refs, &x).unwrap();

        // inflate the combined folded opening beyond the HyperBall budget
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&proof.z[0]);
        coeffs[0] = (batch_z_bound(2) + 1) as u32; // > ‖β‖₁·k·r·d
        proof.z[0] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert!(vec_inf_norm(&proof.z) > batch_z_bound(2));
        assert_eq!(
            verify_batch(&key, &coms, &x, &ys, &proof),
            Err(PcsError::NormViolation)
        );

        // non-binary row-combination digits
        let (_, mut proof) = open_batch(&key, &refs, &x).unwrap();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&proof.w_hat[1][0]);
        coeffs[0] = 5;
        proof.w_hat[1][0] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify_batch(&key, &coms, &x, &ys, &proof),
            Err(PcsError::NormViolation)
        );
    }

    #[test]
    fn foreign_key_rejects_honest_batch() {
        let key = GreyhoundKey::setup(&[6u8; 32]);
        let other = GreyhoundKey::setup(&[7u8; 32]);
        let polys: Vec<Vec<RingElt>> = (0..2).map(|p| test_poly(p + 9)).collect();
        let refs: Vec<&[RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
        let x = test_x(61);
        let coms: Vec<PolyCommitment> = polys
            .iter()
            .map(|f| greyhound::commit(&key, f).unwrap())
            .collect();
        let (ys, proof) = open_batch(&key, &refs, &x).unwrap();
        assert_eq!(
            verify_batch(&other, &coms, &x, &ys, &proof),
            Err(PcsError::LinkCheckFailed)
        );
    }

    #[test]
    fn wire_format_roundtrips_and_beats_k_single_proofs() {
        let key = GreyhoundKey::setup(&[8u8; 32]);
        let polys: Vec<Vec<RingElt>> = (0..4).map(|p| test_poly(p + 11)).collect();
        let refs: Vec<&[RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
        let x = test_x(71);
        let (_ys, proof) = open_batch(&key, &refs, &x).unwrap();

        assert_eq!(
            BatchedOpeningProof::encoded_len(4),
            (4 * PER_CLAIM_ELTS + M_COLS * DELTA) * DIM * 4
        );
        let bytes = proof.to_bytes();
        assert_eq!(bytes.len(), BatchedOpeningProof::encoded_len(4));
        assert_eq!(
            BatchedOpeningProof::from_bytes(&bytes).as_ref(),
            Some(&proof)
        );
        assert_eq!(
            BatchedOpeningProof::from_bytes(&bytes[..bytes.len() - 4]),
            None
        );
        let mut junk = bytes.clone();
        junk.push(0);
        assert_eq!(BatchedOpeningProof::from_bytes(&junk), None);
        // zero-claim and non-canonical shapes are rejected
        assert_eq!(
            BatchedOpeningProof::from_bytes(&bytes[..M_COLS * DELTA * DIM * 4]),
            None
        );

        // the whole point of batching: strictly smaller than k single proofs
        assert_eq!(
            greyhound::OpeningProof::encoded_len(),
            (PER_CLAIM_ELTS + M_COLS * DELTA) * DIM * 4
        );
        let saving = (4 - 1) * M_COLS * DELTA * DIM * 4;
        assert_eq!(
            4 * greyhound::OpeningProof::encoded_len() - bytes.len(),
            saving
        );
    }

    #[test]
    fn batch_challenges_are_small_normed_and_statement_bound() {
        let key = GreyhoundKey::setup(&[9u8; 32]);
        let u0 = vec![test_x(1), test_x(2), test_x(3), test_x(4)];
        let us = vec![u0.as_slice(), u0.as_slice()];
        let x = test_x(5);
        let ys = vec![test_x(7), test_x(8)];
        let vs = vec![u0.clone(), u0.clone()];
        let beta = batch_challenges(&key, &us, &x, &ys, &vs);
        assert_eq!(beta.len(), 2);
        let l1: u64 = beta
            .iter()
            .map(|b| {
                ring_to_u32::<Z1Coeff, DIM>(b)
                    .iter()
                    .map(|&c| Z1Coeff::from(u64::from(c)).abs_infinity())
                    .sum::<u64>()
            })
            .sum();
        assert!(l1 <= L1_PER_POLY * 2, "hyperball budget must hold");
        // every bound value shifts the derivation
        let shifted = batch_challenges(&key, &us, &x, &[test_x(9), test_x(8)], &vs);
        assert_ne!(beta, shifted);
    }
}
