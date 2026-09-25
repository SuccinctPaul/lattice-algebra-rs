//! Greyhound-style polynomial commitment (Z7): commit to
//! `f ∈ R_q[X]`, open at a point with a proof of `y = f(x)`.
//!
//! Core construction of Nguyen–Seiler, *Greyhound: Fast Polynomial
//! Commitments from Lattices* (CRYPTO 2024, eprint 2024/1293): the
//! two-layer Ajtai commitment over the √N split, and the five-equation
//! evaluation protocol. The LaBRADOR recursion that compresses the core
//! O(√N) proof to polylog(N) is *not* layered on here; the proof size
//! stays at the core size (the σ-automorphism packing that removes the
//! factor-`d` size overhead is deferred with it).
//!
//! # Commitment
//!
//! ```text
//! f = Σ_{i<r} X^{im}·fᵢ,  fᵢ = (f[i·m], …, f[i·m + m−1])   (ring elements)
//! sᵢ = G_m⁻¹(fᵢ)                    binary digits,  ‖sᵢ‖∞ = 1
//! tᵢ = A·sᵢ                         inner Ajtai (per column)
//! û  = B·(G_n⁻¹(t₁) ∥ … ∥ G_n⁻¹(t_r))  outer Ajtai — the commitment u
//! ```
//!
//! The outer layer *is* the batching of the r sub-commitments (there is no
//! Merkle layer as in Brakedown/Ligero): the commitment `u ∈ R_q^n` has O(1)
//! ring elements, independent of N.
//!
//! # Evaluation protocol (FS-compiled)
//!
//! With `a(x) = (1, x, …, x^{m−1})` and `b(x) = (1, x^m, …, x^{m(r−1)})` the
//! evaluation factors as `f(x) = a(x)ᵀ·F·b(x)`. Prover:
//!
//! ```text
//! w  = a(x)ᵀ·F                      row combination (r ring elements)
//! ŵ  = G_r⁻¹(w),  v = D·ŵ           commitment to w, sent before the challenge
//! c  ← small ternary challenges     derived from H(key, u, x, y, v)
//! z  = Σᵢ cᵢ·sᵢ                     folded opening
//! proof = (v, ŵ, z, t̂₁ ∥ … ∥ t̂_r)   O(√N) ring elements
//! ```
//!
//! Verifier checks:
//!
//! ```text
//! 1. D·ŵ            == v                          (row-combination commitment)
//! 2. w := G_r(ŵ);     wᵀ·b(x)       == y          (second half of the evaluation)
//! 3. cᵀ·w            == a(x)ᵀ·G_m(z)               (w consistent with folded opening)
//! 4. A·z             == Σᵢ cᵢ·(G_n(t̂ᵢ))            (batched inner opening)
//! 5. B·(t̂₁ ∥ … ∥ t̂_r) == u                         (sub-commitments match u)
//! 6. ‖ŵ‖∞, ‖t̂‖∞ ≤ 1, ‖z‖∞ ≤ r·d                    (norm gates — load-bearing!)
//! ```
//!
//! Check 6 is integral to soundness, not a hygiene measure: knowledge
//! extraction reduces a second opening to a short kernel vector and needs
//! the *approximate* Module-SIS instance with the gated norms as the bound.
//! A verifier that drops the gates accepts transcripts outside the aMSIS
//! bound.
//!
//! # Security notes
//!
//! - **Binding** of `u` (and `v`) is Module-SIS; **knowledge soundness** of
//!   the evaluation is aMSIS with slack, exactly like LaBRADOR.
//! - **Not zero-knowledge**: transcripts are a deterministic function of
//!   the witness (no masking, matching the paper's proof-of-knowledge
//!   status).
//! - Challenges are ternary ring elements. Over the prime ring, the
//!   difference `cᵢ − cⱼ` of distinct draws is invertible except with
//!   negligible probability (the standard resultant heuristic also used by
//!   LaBRADOR/Greyhound), which is what the extractor needs. The
//!   collision/knowledge error is `|C|^{-r}`-dominated and negligible for
//!   the 3^{d·r} challenge space.
//! - The instance constants in [`crate::pcs`] are **toy**: re-derive `(q,
//!   n, lengths, bounds)` against the Core-SVP estimator
//!   (`algebra::security`) before any deployment claim.
//!
//! # Example
//!
//! ```rust
//! use algebra::ring::PolynomialQuotientRing;
//! use zk::foundation::sampling::from_centered;
//! use zk::pcs::{self, greyhound};
//!
//! let key = greyhound::GreyhoundKey::setup(&[7u8; 32]);
//! let f: Vec<_> = (0..pcs::N_DEG)
//!     .map(|i| {
//!         let coeffs: Vec<_> = (0..pcs::DIM)
//!             .map(|j| from_centered::<pcs::Z1Coeff>(((i as i64 * 3 + j as i64) % 9) - 4))
//!             .collect();
//!         pcs::RingElt::from_coefficients(coeffs)
//!     })
//!     .collect();
//! let com = greyhound::commit(&key, &f).expect("length ok");
//! let x = greyhound::eval_point(12345);
//! let (y, proof) = greyhound::open(&key, &f, &x).expect("length ok");
//! assert_eq!(greyhound::OpeningProof::encoded_len(), 1_134_592);
//! assert!(greyhound::verify(&key, &com, &x, &y, &proof).is_ok());
//! ```

use crate::foundation::encoding::{le_bytes_to_u32s, ring_from_u32, ring_to_u32, u32s_to_le_bytes};
use crate::foundation::fs::absorb_rings;
use crate::foundation::sampling::centered_bounded_poly;
use crate::pcs::gadget;
use crate::pcs::packing;
use crate::pcs::{RingElt, Z1Coeff, B_Z, DELTA, DIM, M_COLS, N_DEG, N_ROWS, R_COLS};
use algebra::crypto::sampling::BitStream;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::module::sample_coeffs_from_xof;
use algebra::ntt::{NttDomain, NttOperatorOptimized};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::{vec, vec::Vec};

/// Transcript domain for the evaluation protocol.
const FS_DOMAIN: &[u8] = b"lattice-algebra/Z7/greyhound-pcs";

/// Key derivation domain separator for the three Ajtai keys.
const KEY_DOMAIN: &[u8] = b"lattice-algebra/Z7/greyhound-key";

/// The public polynomial commitment: `u = B·(t̂₁ ∥ … ∥ t̂_r) ∈ R_q^n`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PolyCommitment {
    /// The Ajtai commitment vector (one [`RingElt`] per Ajtai row).
    pub u: Vec<RingElt>,
}

/// The O(√N) core evaluation proof: row-combination commitment `v`, its
/// gadget digits `ŵ`, the folded opening `z`, and the re-decomposed inner
/// commitments `t̂`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpeningProof {
    /// `v = D·ŵ` — commitment to the row combination (first message).
    pub v: Vec<RingElt>,
    /// `ŵ = G_r⁻¹(w)` — binary digits of the row combination.
    pub w_hat: Vec<RingElt>,
    /// `z = Σᵢ cᵢ·sᵢ` — gadget digits of the folded opening.
    pub z: Vec<RingElt>,
    /// `t̂₁ ∥ … ∥ t̂_r` — binary digits of the inner commitments (block
    /// major: block `i` occupies `[i·n·δ, (i+1)·n·δ)`).
    pub t_hat: Vec<RingElt>,
}

impl OpeningProof {
    /// Serialized size in bytes (all vectors are fixed length).
    pub const fn encoded_len() -> usize {
        (N_ROWS + R_COLS * DELTA + M_COLS * DELTA + R_COLS * N_ROWS * DELTA) * DIM * 4
    }

    /// Canonical wire encoding: every field in declaration order, each ring
    /// element as `DIM` little-endian `u32` coefficients.
    ///
    /// # Panics
    /// If the proof vectors have non-canonical lengths (never the case for
    /// proofs produced by [`open`]).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(Self::encoded_len());
        for field in [&self.v, &self.w_hat, &self.z, &self.t_hat] {
            for elt in field.iter() {
                out.extend_from_slice(&u32s_to_le_bytes(&ring_to_u32::<Z1Coeff, DIM>(elt)));
            }
        }
        out
    }

    /// Parses [`to_bytes`] output; `None` on any length or encoding error.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != Self::encoded_len() {
            return None;
        }
        let mut cursor = bytes;
        let v = take_elts(&mut cursor, N_ROWS)?;
        let w_hat = take_elts(&mut cursor, R_COLS * DELTA)?;
        let z = take_elts(&mut cursor, M_COLS * DELTA)?;
        let t_hat = take_elts(&mut cursor, R_COLS * N_ROWS * DELTA)?;
        Some(OpeningProof { v, w_hat, z, t_hat })
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

/// Heap-backed Ajtai key `M ∈ R_q^{rows×cols}` kept in the NTT domain.
///
/// This mirrors [`crate::commitment::ajtai::CommitmentKey`] but stores the
/// matrix in a `Vec`: the commitment module's inline `[[NttDomain; L]; K]`
/// layout is the right shape for Σ-protocol keys (a few dozen entries),
/// while a PCS key holds `O(r·n·δ)` entries — megabytes that must not live
/// on the stack. Entry derivation is the same ExpandA stream per matrix
/// entry with **two-byte** indices (the single-byte encoding saturates
/// past 256 columns), prefixed by the key label for domain separation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AjtaiKeyHeap {
    rows: usize,
    cols: usize,
    /// Row-major NTT-domain entries (`rows × cols`).
    entries: Vec<NttDomain<Z1Coeff, DIM>>,
}

impl AjtaiKeyHeap {
    /// ExpandA: entry `(i, j)` from `XOF(KEY_DOMAIN ‖ label ‖ seed ‖ j ‖ i)`.
    pub(crate) fn setup(label: &[u8], seed: &[u8; 32], rows: usize, cols: usize) -> Self {
        let mut entries = Vec::with_capacity(rows * cols);
        for j in 0..cols {
            for i in 0..rows {
                let mut xof = Shake256Xof::new(&[]);
                xof.absorb(KEY_DOMAIN);
                xof.absorb(label);
                xof.absorb(seed);
                xof.absorb(&(j as u32).to_le_bytes());
                xof.absorb(&(i as u32).to_le_bytes());
                entries.push(NttDomain::from_values(sample_coeffs_from_xof::<
                    Shake256Xof,
                    Z1Coeff,
                    DIM,
                >(xof)));
            }
        }
        AjtaiKeyHeap {
            rows,
            cols,
            entries,
        }
    }

    /// `M·v` entirely in the NTT domain (`rows·cols` pointwise products and
    /// `rows` inverse transforms).
    ///
    /// # Panics
    /// If `v.len() != cols` (internal invariant; every caller passes
    /// canonical instance lengths).
    pub(crate) fn commit(
        &self,
        v: &[RingElt],
        op: &NttOperatorOptimized<Z1Coeff, DIM>,
    ) -> Vec<RingElt> {
        assert_eq!(v.len(), self.cols, "Ajtai mat-vec length mismatch");
        (0..self.rows)
            .map(|i| {
                let mut acc: Option<NttDomain<Z1Coeff, DIM>> = None;
                for (j, elt) in v.iter().enumerate() {
                    let prod = self.entries[i * self.cols + j].mul(&elt.to_ntt(op));
                    acc = Some(match acc {
                        Some(s) => s.add(&prod),
                        None => prod,
                    });
                }
                PolyRing::from_ntt(acc.unwrap_or_else(NttDomain::zero), op)
            })
            .collect()
    }
}

/// The three Ajtai keys of the scheme, derived from one master seed:
///
/// - `a ∈ R_q^{n×mδ}` — inner commitment key (applied per column);
/// - `b ∈ R_q^{n×rnδ}` — outer commitment key (batches the inner ones);
/// - `d ∈ R_q^{n×rδ}` — row-combination commitment key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GreyhoundKey {
    seed: [u8; 32],
    pub(crate) a: AjtaiKeyHeap,
    pub(crate) b: AjtaiKeyHeap,
    pub(crate) d: AjtaiKeyHeap,
}

impl GreyhoundKey {
    /// Derives A/B/D from the master seed with domain-separated labels.
    pub fn setup(seed: &[u8; 32]) -> Self {
        GreyhoundKey {
            seed: *seed,
            a: AjtaiKeyHeap::setup(b"A", seed, N_ROWS, M_COLS * DELTA),
            b: AjtaiKeyHeap::setup(b"B", seed, N_ROWS, R_COLS * N_ROWS * DELTA),
            d: AjtaiKeyHeap::setup(b"D", seed, N_ROWS, R_COLS * DELTA),
        }
    }

    /// The binding master seed (Fiat–Shamir input).
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }
}

/// A fresh NTT operator for the committed ring (twiddle setup per call).
pub(crate) fn ntt_op() -> NttOperatorOptimized<Z1Coeff, DIM> {
    NttOperatorOptimized::new()
}

/// Commits to `f` (length must be [`N_DEG`] ring-element coefficients).
///
/// `f` is indexed `f[i·m + j]` (block `i`, in-block power `j`), i.e.
/// `f = Σᵢ X^{im}·fᵢ`. Coefficients are arbitrary ring elements — no norm
/// restriction: the gadget digits are always binary.
///
/// # Errors
/// [`PcsError::WrongLength`] if `f.len() != N_DEG`.
pub fn commit(key: &GreyhoundKey, f: &[RingElt]) -> Result<PolyCommitment, PcsError> {
    let wit = derive_witness(key, f)?;
    Ok(PolyCommitment { u: wit.u })
}

/// Evaluates and proves: returns `y = f(x)` and the O(√N) opening proof.
///
/// # Errors
/// [`PcsError::WrongLength`] if `f.len() != N_DEG`.
pub fn open(
    key: &GreyhoundKey,
    f: &[RingElt],
    x: &RingElt,
) -> Result<(RingElt, OpeningProof), PcsError> {
    let wit = derive_witness(key, f)?;

    // Evaluation by the split factorization: y = Σᵢ bᵢ·wᵢ.
    let powers = pow_table(x, N_DEG);
    let a_pow = &powers[..M_COLS];
    let b_pow: Vec<RingElt> = (0..R_COLS).map(|i| powers[i * M_COLS].clone()).collect();
    let w: Vec<RingElt> = (0..R_COLS)
        .map(|i| dot(&f[i * M_COLS..(i + 1) * M_COLS], a_pow))
        .collect();
    let y = dot(&w, &b_pow);

    let w_hat = gadget::decompose_digits(&w);
    let v = key.d.commit(&w_hat, &ntt_op());

    let challenges = challenges(key, &wit.u, x, &y, &v);
    // z = Σᵢ cᵢ·sᵢ, accumulated block-wise over the column-digit layout.
    let mut z: Vec<RingElt> = wit.s[..M_COLS * DELTA]
        .iter()
        .map(|s_l| s_l.clone() * &challenges[0])
        .collect();
    for (c_i, s_i) in challenges.iter().zip(wit.s.chunks(M_COLS * DELTA)).skip(1) {
        for (z_l, s_l) in z.iter_mut().zip(s_i) {
            *z_l = z_l.clone() + s_l.clone() * c_i;
        }
    }
    Ok((
        y,
        OpeningProof {
            v,
            w_hat,
            z,
            t_hat: wit.t_hat,
        },
    ))
}

/// Verifies the evaluation claim `(u, x) ↦ y` against the proof, running
/// the five link equations plus the norm gates (checks 1–6 of the module
/// docs, gates first).
///
/// # Errors
/// - [`PcsError::WrongLength`] on non-canonical commitment/proof lengths;
/// - [`PcsError::NormViolation`] if any norm gate fails;
/// - [`PcsError::LinkCheckFailed`] if any link equation fails.
pub fn verify(
    key: &GreyhoundKey,
    com: &PolyCommitment,
    x: &RingElt,
    y: &RingElt,
    proof: &OpeningProof,
) -> Result<(), PcsError> {
    if com.u.len() != N_ROWS
        || proof.v.len() != N_ROWS
        || proof.w_hat.len() != R_COLS * DELTA
        || proof.z.len() != M_COLS * DELTA
        || proof.t_hat.len() != R_COLS * N_ROWS * DELTA
    {
        return Err(PcsError::WrongLength);
    }
    // Check 6: norm gates — must run before the links (aMSIS bound).
    if vec_inf_norm(&proof.w_hat) > 1 || vec_inf_norm(&proof.t_hat) > 1 {
        return Err(PcsError::NormViolation);
    }
    if vec_inf_norm(&proof.z) > B_Z {
        return Err(PcsError::NormViolation);
    }

    let powers = pow_table(x, N_DEG);
    let a_pow = &powers[..M_COLS];
    let b_pow: Vec<RingElt> = (0..R_COLS).map(|i| powers[i * M_COLS].clone()).collect();
    let challenges = challenges(key, &com.u, x, y, &proof.v);

    // Check 1: D·ŵ == v.
    if key.d.commit(&proof.w_hat, &ntt_op()) != proof.v {
        return Err(PcsError::LinkCheckFailed);
    }

    // Check 2: w = G_r(ŵ); wᵀ·b(x) == y.
    let w = gadget::recombine_digits(&proof.w_hat);
    if dot(&w, &b_pow) != *y {
        return Err(PcsError::LinkCheckFailed);
    }

    // Check 3: cᵀ·w == a(x)ᵀ·G_m(z) — z is short but not binary, so its
    // recombination goes through the modular gadget path.
    let g_z = gadget::recombine_digits_mod(&proof.z);
    if dot(&challenges, &w) != dot(a_pow, &g_z) {
        return Err(PcsError::LinkCheckFailed);
    }

    // Check 4: A·z == Σᵢ cᵢ·(G_n(t̂ᵢ)).
    let az = key.a.commit(&proof.z, &ntt_op());
    for (k, az_k) in az.iter().enumerate() {
        let mut rhs = ring_zero();
        for (c_i, block) in challenges.iter().zip(proof.t_hat.chunks(N_ROWS * DELTA)) {
            let t_i = gadget::recombine_digits(block);
            rhs += t_i[k].clone() * c_i;
        }
        if az_k != &rhs {
            return Err(PcsError::LinkCheckFailed);
        }
    }

    // Check 5: B·(t̂₁ ∥ … ∥ t̂_r) == u.
    if key.b.commit(&proof.t_hat, &ntt_op()) != com.u {
        return Err(PcsError::LinkCheckFailed);
    }
    Ok(())
}

/// The constant ring element carrying `v` as its constant coefficient
/// (scalar weights of the packed statement embedded in the ring).
fn const_elt(v: Z1Coeff) -> RingElt {
    let mut coeffs = vec![Z1Coeff::ZERO; DIM];
    coeffs[0] = v;
    PolyRing::from_coefficients(coeffs)
}

/// The scalar powers `[1, b, b², …, b^{n−1}]`.
fn scalar_pows(b: Z1Coeff, n: usize) -> Vec<Z1Coeff> {
    let mut out = Vec::with_capacity(n);
    let mut cur = Z1Coeff::ONE;
    for _ in 0..n {
        out.push(cur);
        cur *= b;
    }
    out
}

/// The power vector `p = (1, x, x², …, x^{d−1})` as a ring element — the
/// pairing operand of the packed evaluation.
fn power_elt(x: Z1Coeff) -> RingElt {
    let coeffs = scalar_pows(x, DIM);
    PolyRing::from_coefficients(coeffs)
}

/// **Packed commitment**: commits to the scalar-coefficient polynomial
/// `f` (length [`N_DEG`]·[`DIM`]) by packing `d = 256` consecutive
/// coefficients into each ring element and running the usual two-layer
/// Ajtai pipeline ([`commit`]). The commitment is identical in shape; the
/// factor-`d` gain shows up in what a proof can carry: `N_DEG` ring
/// elements now stand for `N_DEG·256` scalar coefficients.
///
/// # Errors
/// [`PcsError::WrongLength`] if `f.len() != N_DEG·DIM`.
pub fn commit_packed(key: &GreyhoundKey, f: &[Z1Coeff]) -> Result<PolyCommitment, PcsError> {
    if f.len() != N_DEG * DIM {
        return Err(PcsError::WrongLength);
    }
    commit(key, &packing::pack_scalars(f))
}

/// **Packed opening**: evaluates the scalar-coefficient polynomial at the
/// scalar point `x` and proves the claim `y = f(x)`.
///
/// The √N-split structure is reused verbatim; the only change is the
/// statement's weight vectors, which become **scalars**: with
/// `ξ = x^d`, `a_j = ξ^j (j < m)` and `b_i = ξ^{i·m} (i < r)`,
///
/// ```text
/// w = Σ_j a_j·F[·,j]        (scalar-weighted row combination, ring elements)
/// y = Σ_i b_i·const(w_i·σ(p)),   p = (1, x, …, x^{d−1})   (σ-pairing)
/// ```
///
/// where `const(w_i·σ(p))` reads off `w_i`'s evaluation at `x` from one
/// ring product. The proof binds `y` through this pairing (packed check 2)
/// while checks 1/3/4/5/6 carry over unchanged — with scalar `a_j` the
/// eq-3 identity `cᵀ·w == aᵀ·G_m(z)` still holds by commutativity.
///
/// # Errors
/// [`PcsError::WrongLength`] if `f.len() != N_DEG·DIM`.
pub fn open_packed(
    key: &GreyhoundKey,
    f: &[Z1Coeff],
    x: Z1Coeff,
) -> Result<(Z1Coeff, OpeningProof), PcsError> {
    if f.len() != N_DEG * DIM {
        return Err(PcsError::WrongLength);
    }
    let packed = packing::pack_scalars(f);
    let wit = derive_witness(key, &packed)?;

    // scalar weight vectors: a_j = ξ^j, b_i = ξ^{i·m} with ξ = x^d
    let xi = x.pow(DIM as u64);
    let a_s = scalar_pows(xi, M_COLS);
    let b_s = scalar_pows(xi.pow(M_COLS as u64), R_COLS);
    let a_const: Vec<RingElt> = a_s.iter().map(|&a| const_elt(a)).collect();

    // w_i = Σ_j a_j·F[i·m+j] (scalar-weighted; constants commute)
    let w: Vec<RingElt> = (0..R_COLS)
        .map(|i| dot(&a_const, &packed[i * M_COLS..(i + 1) * M_COLS]))
        .collect();

    // the claimed scalar evaluation via the σ-pairing on w
    let p = power_elt(x);
    let mut y = Z1Coeff::ZERO;
    for (b_i, w_i) in b_s.iter().zip(&w) {
        y += *b_i * packing::sigma_pairing(w_i, &p);
    }

    let w_hat = gadget::decompose_digits(&w);
    let v = key.d.commit(&w_hat, &ntt_op());

    let challenges = challenges(key, &wit.u, &const_elt(x), &const_elt(y), &v);
    let mut z: Vec<RingElt> = wit.s[..M_COLS * DELTA]
        .iter()
        .map(|s_l| s_l.clone() * &challenges[0])
        .collect();
    for (c_i, s_i) in challenges.iter().zip(wit.s.chunks(M_COLS * DELTA)).skip(1) {
        for (z_l, s_l) in z.iter_mut().zip(s_i) {
            *z_l = z_l.clone() + s_l.clone() * c_i;
        }
    }
    Ok((
        y,
        OpeningProof {
            v,
            w_hat,
            z,
            t_hat: wit.t_hat,
        },
    ))
}

/// **Packed verification**: checks the scalar claim `y = f(x)` against the
/// commitment and the proof. The five link equations of [`verify`] run with
/// the scalar weight vectors, and check 2 binds the claim through the
/// σ-pairing:
///
/// ```text
/// Σ_i b_i·const(w_i·σ(p)) == y      (b_i = ξ^{i·m},  ξ = x^d)
/// ```
///
/// Norm gates unchanged (`‖ŵ‖∞, ‖t̂‖∞ ≤ 1`, `‖z‖∞ ≤ r·d`).
///
/// # Errors
/// Typed rejections as for [`verify`].
pub fn verify_packed(
    key: &GreyhoundKey,
    com: &PolyCommitment,
    x: Z1Coeff,
    y: Z1Coeff,
    proof: &OpeningProof,
) -> Result<(), PcsError> {
    if com.u.len() != N_ROWS
        || proof.v.len() != N_ROWS
        || proof.w_hat.len() != R_COLS * DELTA
        || proof.z.len() != M_COLS * DELTA
        || proof.t_hat.len() != R_COLS * N_ROWS * DELTA
    {
        return Err(PcsError::WrongLength);
    }
    if vec_inf_norm(&proof.w_hat) > 1 || vec_inf_norm(&proof.t_hat) > 1 {
        return Err(PcsError::NormViolation);
    }
    if vec_inf_norm(&proof.z) > B_Z {
        return Err(PcsError::NormViolation);
    }

    let xi = x.pow(DIM as u64);
    let a_s = scalar_pows(xi, M_COLS);
    let b_s = scalar_pows(xi.pow(M_COLS as u64), R_COLS);
    let a_const: Vec<RingElt> = a_s.iter().map(|&a| const_elt(a)).collect();
    let p = power_elt(x);
    let challenges = challenges(key, &com.u, &const_elt(x), &const_elt(y), &proof.v);

    // Check 1: D·ŵ == v.
    if key.d.commit(&proof.w_hat, &ntt_op()) != proof.v {
        return Err(PcsError::LinkCheckFailed);
    }

    // Check 2 (packed): Σ_i b_i·const(w_i·σ(p)) == y, w = G_r(ŵ).
    let w = gadget::recombine_digits(&proof.w_hat);
    let mut y_check = Z1Coeff::ZERO;
    for (b_i, w_i) in b_s.iter().zip(&w) {
        y_check += *b_i * packing::sigma_pairing(w_i, &p);
    }
    if y_check != y {
        return Err(PcsError::LinkCheckFailed);
    }

    // Check 3: cᵀ·w == aᵀ·G_m(z) (scalar a_j embedded as constants —
    // the identity holds by commutativity, as in the ring protocol).
    let g_z = gadget::recombine_digits_mod(&proof.z);
    if dot(&challenges, &w) != dot(&a_const, &g_z) {
        return Err(PcsError::LinkCheckFailed);
    }

    // Check 4: A·z == Σᵢ cᵢ·(G_n(t̂ᵢ)).
    let az = key.a.commit(&proof.z, &ntt_op());
    for (k, az_k) in az.iter().enumerate() {
        let mut rhs = ring_zero();
        for (c_i, block) in challenges.iter().zip(proof.t_hat.chunks(N_ROWS * DELTA)) {
            let t_i = gadget::recombine_digits(block);
            rhs += t_i[k].clone() * c_i;
        }
        if az_k != &rhs {
            return Err(PcsError::LinkCheckFailed);
        }
    }

    // Check 5: B·(t̂₁ ∥ … ∥ t̂_r) == u.
    if key.b.commit(&proof.t_hat, &ntt_op()) != com.u {
        return Err(PcsError::LinkCheckFailed);
    }
    Ok(())
}

/// A convenient nonzero evaluation point `x` for examples and tests: the
/// ring element with constant coefficient `v`.
///
/// # Panics
/// If `v` does not fit the scalar modulus (never for protocol values).
pub fn eval_point(v: u64) -> RingElt {
    let mut coeffs = vec![Z1Coeff::ZERO; DIM];
    coeffs[0] = Z1Coeff::from(v.rem_euclid(Z1Coeff::MODULUS));
    PolyRing::from_coefficients(coeffs)
}

/// Witness side of the commitment: digits `s` (block per column), the
/// decomposed inner commitments `t_hat`, and the commitment `u`.
pub(crate) struct Committed {
    pub(crate) s: Vec<RingElt>,
    pub(crate) t_hat: Vec<RingElt>,
    pub(crate) u: Vec<RingElt>,
}

/// Runs the two-layer commitment pipeline: per-column digit split, inner
/// Ajtai commitments, outer digit split and outer Ajtai commitment.
pub(crate) fn derive_witness(key: &GreyhoundKey, f: &[RingElt]) -> Result<Committed, PcsError> {
    if f.len() != N_DEG {
        return Err(PcsError::WrongLength);
    }
    // Block layout of decompose (value-major: out[j·δ + k]) matches the
    // column layout s[i·mδ + j·δ + k] exactly.
    let s = gadget::decompose_digits(f);
    let op = ntt_op();
    let mut t_hat = Vec::with_capacity(R_COLS * N_ROWS * DELTA);
    for col in s.chunks(M_COLS * DELTA) {
        for row in key.a.commit(col, &op) {
            t_hat.extend(gadget::decompose_digits(core::slice::from_ref(&row)));
        }
    }
    let u = key.b.commit(&t_hat, &op);
    Ok(Committed { s, t_hat, u })
}

/// Fiat–Shamir challenges: binds (key, u, x, y, v) and derives `r` ternary
/// ring elements (the small challenge set; see the module security notes).
pub(crate) fn challenges(
    key: &GreyhoundKey,
    u: &[RingElt],
    x: &RingElt,
    y: &RingElt,
    v: &[RingElt],
) -> Vec<RingElt> {
    let mut tr = Transcript::<Shake256Xof>::new(FS_DOMAIN);
    tr.absorb(b"key", key.seed());
    absorb_rings(&mut tr, b"u", u);
    absorb_rings(&mut tr, b"x", core::slice::from_ref(x));
    absorb_rings(&mut tr, b"y", core::slice::from_ref(y));
    absorb_rings(&mut tr, b"v", v);
    let seed = tr.challenge_bytes(64);
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(b"C");
    xof.absorb(&seed);
    let mut stream = BitStream::new(&mut xof);
    (0..R_COLS)
        .map(|_| centered_bounded_poly::<Z1Coeff, Shake256Xof, DIM>(&mut stream, 1))
        .collect()
}

/// The powers `[1, x, x², …, x^{n−1}]` (sequential negacyclic products).
pub(crate) fn pow_table(x: &RingElt, n: usize) -> Vec<RingElt> {
    let mut out = Vec::with_capacity(n);
    let mut cur = ring_one();
    for _ in 0..n {
        out.push(cur.clone());
        cur = cur * x;
    }
    out
}

/// Ring dot product `Σ aᵢ·bᵢ` (zero-padded, equal lengths assumed).
pub(crate) fn dot(a: &[RingElt], b: &[RingElt]) -> RingElt {
    let mut acc = ring_zero();
    for (x, y) in a.iter().zip(b.iter()) {
        acc += x.clone() * y;
    }
    acc
}

/// The zero ring element.
pub(crate) fn ring_zero() -> RingElt {
    PolyRing::from_coefficients(vec![Z1Coeff::ZERO; DIM])
}

/// The multiplicative identity ring element.
fn ring_one() -> RingElt {
    let mut coeffs = vec![Z1Coeff::ZERO; DIM];
    coeffs[0] = Z1Coeff::ONE;
    PolyRing::from_coefficients(coeffs)
}

/// Infinity norm over a ring-element vector: the maximum `|·|_∞` over all
/// scalar coefficients (centered representatives).
pub(crate) fn vec_inf_norm(elts: &[RingElt]) -> u64 {
    elts.iter()
        .flat_map(ring_to_u32::<Z1Coeff, DIM>)
        .map(|c| Z1Coeff::from(u64::from(c)).abs_infinity())
        .max()
        .unwrap_or(0)
}

/// Typed rejection for the PCS (no panics on adversarial input).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PcsError {
    /// A vector had a length other than the canonical instance length.
    WrongLength,
    /// A norm gate failed (digits must be binary; `‖z‖∞ ≤ r·d`).
    NormViolation,
    /// One of the five link equations failed.
    LinkCheckFailed,
    /// A batched opening exceeded the instance's batch-size cap.
    BatchTooLarge,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;

    /// Deterministic scalar coefficient vector of full packed length
    /// (`N_DEG·DIM`), coefficients in `[−48, 48]`.
    fn test_scalars(seed: u64) -> Vec<Z1Coeff> {
        (0..N_DEG * DIM)
            .map(|i| from_centered::<Z1Coeff>(((seed as i64 * 37 + i as i64 * 11) % 97) - 48))
            .collect()
    }

    #[test]
    fn packed_honest_roundtrip_and_claim_binding() {
        let key = GreyhoundKey::setup(&[21u8; 32]);
        let f = test_scalars(1);
        let com = commit_packed(&key, &f).expect("length ok");
        assert_eq!(com.u.len(), N_ROWS);

        for seed in [3u64, 9, 77] {
            let x = from_centered::<Z1Coeff>((seed as i64 * 411) % 1000 - 500);
            let (y, proof) = open_packed(&key, &f, x).expect("length ok");

            // the claimed scalar matches the packing module's evaluation…
            assert_eq!(y, packing::packed_eval(&packing::pack_scalars(&f), x));

            // …and the verifier accepts it through the σ-pairing binding
            assert!(verify_packed(&key, &com, x, y, &proof).is_ok());
        }

        // determinism
        let x = from_centered::<Z1Coeff>(999);
        let (y1, p1) = open_packed(&key, &f, x).unwrap();
        let (y2, p2) = open_packed(&key, &f, x).unwrap();
        assert_eq!(y1, y2);
        assert_eq!(p1, p2);
    }

    #[test]
    fn packed_claim_matches_scalar_horner() {
        // the packed proof's claim is the plain scalar Horner evaluation of
        // the 16384-coefficient polynomial (independent computation path)
        let key = GreyhoundKey::setup(&[22u8; 32]);
        let f = test_scalars(2);
        let x = from_centered::<Z1Coeff>(3777);
        let (y, _proof) = open_packed(&key, &f, x).unwrap();
        let mut horner = Z1Coeff::ZERO;
        for c in f.iter().rev() {
            horner = horner * x + *c;
        }
        assert_eq!(y, horner);
    }

    #[test]
    fn packed_wrong_claims_and_tampering_rejected() {
        let key = GreyhoundKey::setup(&[23u8; 32]);
        let f = test_scalars(3);
        let com = commit_packed(&key, &f).expect("length ok");
        let x = from_centered::<Z1Coeff>(555);
        let (y, proof) = open_packed(&key, &f, x).unwrap();

        // wrong claimed evaluation ⇒ the packed check 2 fails
        let bad_y = y + Z1Coeff::from(1);
        assert_eq!(
            verify_packed(&key, &com, x, bad_y, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // wrong evaluation point ⇒ the packed check 2 fails
        assert_eq!(
            verify_packed(&key, &com, x + Z1Coeff::from(1), y, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // a different polynomial's claim under this commitment fails
        let mut f_other = f.clone();
        f_other[7] += Z1Coeff::from(5);
        let (y_other, _p) = open_packed(&key, &f_other, x).unwrap();
        assert_eq!(
            verify_packed(&key, &com, x, y_other, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered row-combination digits ⇒ checks 1/2 fail
        let mut bad = proof.clone();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad.w_hat[2]);
        coeffs[4] ^= 1;
        bad.w_hat[2] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify_packed(&key, &com, x, y, &bad),
            Err(PcsError::LinkCheckFailed)
        );

        // wrong length input is a typed rejection
        assert_eq!(
            commit_packed(&key, &f[..f.len() - 1]),
            Err(PcsError::WrongLength)
        );
    }

    #[test]
    fn packed_and_ring_modes_are_distinct_claims() {
        // the same commitment object, different statement shapes: the
        // packed proof must not verify under the ring-mode verifier and
        // vice versa (the claims bind different evaluation semantics)
        let key = GreyhoundKey::setup(&[24u8; 32]);
        let f_ring = test_poly(6);
        let com = commit(&key, &f_ring).unwrap();
        let x_elt = eval_point(31);
        let (_y, proof) = open(&key, &f_ring, &x_elt).unwrap();
        let x_scalar = from_centered::<Z1Coeff>(31);
        let y_scalar = from_centered::<Z1Coeff>(12);
        assert!(verify_packed(&key, &com, x_scalar, y_scalar, &proof).is_err());
    }

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
    fn honest_roundtrip_verifies_at_multiple_points() {
        let key = GreyhoundKey::setup(&[1u8; 32]);
        let f = test_poly(3);
        let com = commit(&key, &f).expect("length ok");
        assert_eq!(com.u.len(), N_ROWS);

        for seed in [11u64, 22, 33] {
            let x = test_x(seed);
            let (y, proof) = open(&key, &f, &x).expect("length ok");
            assert!(verify(&key, &com, &x, &y, &proof).is_ok());
        }

        // determinism: same (f, x) give identical proofs
        let x = test_x(44);
        let (y1, p1) = open(&key, &f, &x).unwrap();
        let (y2, p2) = open(&key, &f, &x).unwrap();
        assert_eq!(y1, y2);
        assert_eq!(p1, p2);
    }

    #[test]
    fn evaluation_matches_horner() {
        // y from the split factorization must equal a plain Horner fold
        // Σⱼ fⱼ·xʲ over the same ring.
        let key = GreyhoundKey::setup(&[2u8; 32]);
        let f = test_poly(5);
        let x = test_x(77);
        let (y, _proof) = open(&key, &f, &x).unwrap();
        let mut horner = ring_zero();
        for f_j in f.iter().rev() {
            horner = horner * &x + f_j;
        }
        assert_eq!(y, horner);
    }

    #[test]
    fn commitments_discriminate_polynomials() {
        let key = GreyhoundKey::setup(&[3u8; 32]);
        let c1 = commit(&key, &test_poly(1)).unwrap();
        let c2 = commit(&key, &test_poly(2)).unwrap();
        assert_ne!(c1.u, c2.u, "a collision would be an MSIS solution");
        // deterministic re-commitment
        assert_eq!(c1, commit(&key, &test_poly(1)).unwrap());
    }

    #[test]
    fn wrong_lengths_are_typed_rejections() {
        let key = GreyhoundKey::setup(&[4u8; 32]);
        let f = test_poly(1);
        assert_eq!(commit(&key, &f[..N_DEG - 1]), Err(PcsError::WrongLength));
        assert!(matches!(
            open(&key, &f[..N_DEG - 1], &eval_point(1)),
            Err(PcsError::WrongLength)
        ));

        // malformed proof vectors
        let com = commit(&key, &f).unwrap();
        let x = eval_point(9);
        let (y, mut proof) = open(&key, &f, &x).unwrap();
        proof.z.pop();
        assert_eq!(
            verify(&key, &com, &x, &y, &proof),
            Err(PcsError::WrongLength)
        );
    }

    #[test]
    fn tampered_claims_and_proofs_are_rejected() {
        let key = GreyhoundKey::setup(&[5u8; 32]);
        let f = test_poly(6);
        let com = commit(&key, &f).unwrap();
        let x = test_x(88);
        let (y, proof) = open(&key, &f, &x).unwrap();

        // wrong claimed evaluation ⇒ check 2 fails
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&y);
        coeffs[0] ^= 1;
        let bad_y = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify(&key, &com, &x, &bad_y, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // wrong evaluation point ⇒ checks 2/3 fail
        assert_eq!(
            verify(&key, &com, &test_x(89), &y, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered commitment ⇒ check 5 fails
        let mut bad_com = com.clone();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad_com.u[0]);
        coeffs[7] ^= 1;
        bad_com.u[0] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify(&key, &bad_com, &x, &y, &proof),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered row-combination commitment ⇒ check 1 fails
        let mut bad = proof.clone();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad.v[1]);
        coeffs[11] ^= 1;
        bad.v[1] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify(&key, &com, &x, &y, &bad),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered folded opening ⇒ checks 3/4 fail
        let mut bad = proof.clone();
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad.z[5]);
        coeffs[3] ^= 1;
        bad.z[5] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify(&key, &com, &x, &y, &bad),
            Err(PcsError::LinkCheckFailed)
        );

        // tampered inner-commitment digits ⇒ checks 4/5 fail
        let mut bad = proof;
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&bad.t_hat[100]);
        coeffs[9] ^= 1;
        bad.t_hat[100] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify(&key, &com, &x, &y, &bad),
            Err(PcsError::LinkCheckFailed)
        );
    }

    #[test]
    fn norm_gates_fire_before_links() {
        // A proof whose folded opening violates the response bound must be
        // rejected as NormViolation even though the links would also fail —
        // the gates bound the aMSIS extraction instance and run first.
        let key = GreyhoundKey::setup(&[6u8; 32]);
        let f = test_poly(7);
        let com = commit(&key, &f).unwrap();
        let x = eval_point(13);
        let (y, mut proof) = open(&key, &f, &x).unwrap();

        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&proof.z[0]);
        coeffs[0] = 1_000_000; // ≫ B_Z = r·d
        proof.z[0] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert!(vec_inf_norm(&proof.z) > B_Z);
        assert_eq!(
            verify(&key, &com, &x, &y, &proof),
            Err(PcsError::NormViolation)
        );

        // same for non-binary digits of the row combination
        let mut proof = open(&key, &f, &x).unwrap().1;
        let mut coeffs = ring_to_u32::<Z1Coeff, DIM>(&proof.w_hat[0]);
        coeffs[0] = 5; // ŵ must be binary
        proof.w_hat[0] = ring_from_u32::<Z1Coeff, DIM>(&coeffs);
        assert_eq!(
            verify(&key, &com, &x, &y, &proof),
            Err(PcsError::NormViolation)
        );
    }

    #[test]
    fn foreign_key_rejects_honest_proof() {
        let key = GreyhoundKey::setup(&[7u8; 32]);
        let other = GreyhoundKey::setup(&[8u8; 32]);
        let f = test_poly(9);
        let com = commit(&key, &f).unwrap();
        let x = eval_point(21);
        let (y, proof) = open(&key, &f, &x).unwrap();
        assert_eq!(
            verify(&other, &com, &x, &y, &proof),
            Err(PcsError::LinkCheckFailed)
        );
    }

    #[test]
    fn wire_format_roundtrips_exactly() {
        let key = GreyhoundKey::setup(&[10u8; 32]);
        let f = test_poly(11);
        let x = eval_point(31);
        let (_y, proof) = open(&key, &f, &x).unwrap();

        assert_eq!(
            OpeningProof::encoded_len(),
            (N_ROWS + R_COLS * DELTA + M_COLS * DELTA + R_COLS * N_ROWS * DELTA) * DIM * 4
        );
        let bytes = proof.to_bytes();
        assert_eq!(bytes.len(), OpeningProof::encoded_len());
        assert_eq!(OpeningProof::from_bytes(&bytes).as_ref(), Some(&proof));
        // truncation and trailing junk are rejected
        assert_eq!(OpeningProof::from_bytes(&bytes[..bytes.len() - 4]), None);
        let mut junk = bytes.clone();
        junk.push(0);
        assert_eq!(OpeningProof::from_bytes(&junk), None);
    }

    #[test]
    fn challenges_are_small_and_domain_bound() {
        // the derived challenge vector must be ternary and must change with
        // every bound value (statement binding of the Fiat–Shamir step)
        let key = GreyhoundKey::setup(&[12u8; 32]);
        let u = vec![test_x(1), test_x(2), test_x(3), test_x(4)];
        let base = challenges(&key, &u, &eval_point(5), &eval_point(6), &u);
        assert_eq!(base.len(), R_COLS);
        for c in &base {
            assert!(vec_inf_norm(core::slice::from_ref(c)) <= 1, "ternary");
        }
        let shifted = challenges(&key, &u, &eval_point(7), &eval_point(6), &u);
        assert_ne!(base, shifted);
    }
}
