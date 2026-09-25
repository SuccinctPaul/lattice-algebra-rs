//! Lattice trapdoor generation and short-preimage sampling (gap G2).
//!
//! The capability the crate did not have: publish an Ajtai matrix `A` together
//! with a *short* matrix `B` obeying the SIS relation `A·B = G mod q` for the
//! gadget `G`, and turn any target into a short preimage under `A`. SLAP's tree
//! parent (Albrecht–Fenzi–Lapiha–Nguyen, eprint 2023/1469 Fig. 4) and the
//! PowerBASIS commitment (Fenzi–Moghaddas–Nguyen, eprint 2023/846 Fig. 4) are
//! the only schemes in `docs/survey-lattice-pcs.md` §1 that need it: a parent
//! must satisfy two commitment equations against **one** shared child value,
//! which is a joint short-preimage problem rather than a hash.
//!
//! # The construction, and the text that licenses it
//!
//! **TrapGen** is Micciancio–Peikert `GenTrap` (EUROCRYPT 2012 / eprint
//! 2011/501, §5.2 Algorithm 1): take `Ā` uniform, a short `R`, and apply the
//! unimodular `T = [[I, −R], [0, I]]` to the semi-random `A' = [Ā | G]`:
//!
//! ```text
//! A  = A'·T⁻¹ = [Ā | G − Ā·R]        (published)
//! B  = T·[0; I] = [R; I_w]           A·B = G       (the trapdoor)
//! ```
//!
//! MP12 Def. 5.2 is the definition this module's relation check enforces: "A
//! `G`-trapdoor for `A` is a matrix `R` such that `A [R; I] = HG` for some
//! invertible `H`", here with the tag `H = I`. The Gaussian-free choice of `R`
//! is MP12's own statistical instantiation: "let `D = P^(m̄×w)` where `P` is the
//! distribution over `Z` that outputs 0 with probability 1/2, and ±1 each with
//! probability 1/4" — coin flips, no Gaussian oracle.
//!
//! **SamplePre** is the algebraic skeleton of MP12's `SampleD` (Algorithm 3),
//! `x ← p + [R;I]·z` with `z` a gadget preimage of the residual, specialised by
//! replacing its two Gaussian oracles with exact substitutes: `p = 0` and the
//! binary digit map `G⁻¹`, or a bounded-uniform `p` and the same digit map:
//!
//! ```text
//! x = p + B · G⁻¹(u − A·p)     ⇒   A·x = A·p + G·G⁻¹(u − A·p) = u
//! ```
//!
//! `p = 0` is the deterministic preimage SLAP's Appendix C prescribes verbatim:
//! "The instantiations that we are concerned with in this section are not
//! concerned with zero-knowledge. Thus, we can replace the `SamplePre`
//! procedure in the commit phase to make us of simpler deterministic sampling.
//! More formally, given a matrix `B` and a corresponding trapdoor `T`, one can
//! compute a preimage of a target vector `t` as `v := T·G⁻¹(t)`. It can then be
//! easily verified that `B·v = B·T·G⁻¹(t) = G·G⁻¹(t) = t`."
//!
//! **What is not claimed.** MP12's `SampleD` proves its output is
//! `negl(n)`-close to the discrete Gaussian `D_{Λ_u^⊥(A), r√Σ}`. That needs the
//! Gaussian perturbation and the gadget coset sampler of MP12 §4.1; here the
//! output is *exactly* a solution of `A·x = u` and *provably short* (see
//! [`TrapdoorKey::certified_bound`]), and with `p ≠ 0` it is genuinely random
//! (two draws differ — tested), but no distribution claim is made. Anything
//! that consumes Gaussian *quality* — SLAP §5.4 / FMN §5.6 zero-knowledge
//! simulation, and the `σ ≥ δ‖R‖ω(√log)` conditions of SLAP Lem. 2.14 — cannot
//! use this sampler, and the two assemblies say so where they stop.
//!
//! # Generality, and the known walls
//!
//! Generic over the scalar ring `R`, ring degree `D` and gadget
//! (`BASE`, `DIGITS`), so the non-NTT instance the schemes actually need
//! (`q = 2³² − 99 ≡ 5 (mod 8)`, where SLAP Rem. 2.11 wants `X^N+1` to split
//! into *two* fields, i.e. `ord_{2N}(q) = N/2`) works exactly like the
//! NTT-friendly `Z1`. `BASE^DIGITS > q` is required for `G·G⁻¹ = id` to be
//! exact ([`check_gadget_capacity`], mirroring the guard inside
//! [`crate::pcs::gadget::split`]).
//!
//! Layering: a trapdoor is a commitment-key object, but it is *defined* against
//! the gadget, and `gadget` lives in the `pcs` domain, one rung above
//! `commitment`. This module is therefore the bottom rung of `pcs`, and the
//! scheme assemblies reach it from there.

use crate::foundation::encoding::ring_to_u32;
use crate::foundation::sampling::from_centered;
use crate::pcs::gadget::{digit_half_width, join, split};
use crate::pcs::key::{KeyShapeError, RingMatrixKey};
use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{Field, PolynomialQuotientRing, Ring};
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// One ring element of `R_q = Z_q[X]/(X^D + 1)`.
pub type Elt<R, const D: usize> = PolyRing<R, D>;

/// Domain separator for the uniform half, distinct from the Greyhound key
/// domain so a reused seed cannot make two schemes share a matrix.
const TRAPDOM: &[u8] = b"lattice-algebra/G2/trapgen-uniform";
/// Domain separator for the short trapdoor block.
const SHORTDOM: &[u8] = b"lattice-algebra/G2/trapgen-short";
/// Domain separator for a preimage perturbation.
const PERTDOM: &[u8] = b"lattice-algebra/G2/perturb";

/// Why a trapdoor operation refused.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum TrapError {
    /// A vector or matrix axis had the wrong length.
    WrongShape {
        /// Length supplied.
        got: usize,
        /// Length the operation requires.
        expected: usize,
    },
    /// A claimed inverse is not an inverse, or a claimed unit is not one.
    NotAUnit,
    /// Two matrices are not composable.
    NotComposable {
        /// Column count of the left factor.
        left_cols: usize,
        /// Row count of the right factor.
        right_rows: usize,
    },
    /// `BASE^DIGITS <= q`: `G⁻¹` would wrap instead of being exact.
    GadgetTooNarrow {
        /// Both sides of the failed inequality.
        detail: String,
    },
}

impl fmt::Display for TrapError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TrapError::WrongShape { got, expected } => {
                write!(f, "shape {got} where {expected} is required")
            }
            TrapError::NotAUnit => write!(f, "the claimed inverse is not an inverse"),
            TrapError::NotComposable {
                left_cols,
                right_rows,
            } => write!(
                f,
                "cannot apply a ×{left_cols} matrix to a {right_rows}×· matrix"
            ),
            TrapError::GadgetTooNarrow { detail } => {
                write!(f, "gadget cannot represent the modulus: {detail}")
            }
        }
    }
}

/// The zero of `R_q[X]/(X^D + 1)`.
fn zero<R: Ring, const D: usize>() -> Elt<R, D> {
    PolyRing::from_coefficients(vec![R::ZERO; D])
}

/// Lifts a `KeyShapeError` into the module's own refusal.
const fn shape_err(e: KeyShapeError) -> TrapError {
    TrapError::WrongShape {
        got: e.got,
        expected: e.expected,
    }
}

/// `BASE^DIGITS`, saturating at `u128::MAX`.
const fn capacity<const BASE: u64, const DIGITS: usize>() -> u128 {
    let mut acc: u128 = 1;
    let mut k = 0;
    while k < DIGITS {
        acc = match acc.checked_mul(BASE as u128) {
            Some(v) => v,
            None => return u128::MAX,
        };
        k += 1;
    }
    acc
}

/// Rejects a gadget that cannot hold a canonical representative.
///
/// Without `BASE^DIGITS > q` the digit map wraps, so `G·G⁻¹(u) = u` fails and
/// every "preimage" produced from it solves a different equation.
///
/// # Errors
/// [`TrapError::GadgetTooNarrow`], naming both sides.
pub fn check_gadget_capacity<R: Ring, const BASE: u64, const DIGITS: usize>(
) -> Result<(), TrapError> {
    let cap = capacity::<BASE, DIGITS>();
    if cap > u128::from(R::MODULUS) {
        Ok(())
    } else {
        Err(TrapError::GadgetTooNarrow {
            detail: format!("BASE^{DIGITS} = {cap} <= q = {}", R::MODULUS),
        })
    }
}

/// `BASE^k mod q` as a ring element, by modular doubling-free iteration
/// (multiplying `u64`s would overflow for `BASE^k` past 2⁶⁴).
fn pow_base<R: Ring, const BASE: u64, const DIGITS: usize>(k: usize) -> R {
    let base = BASE % R::MODULUS;
    let mut acc = 1u128;
    for _ in 0..k {
        acc = (acc * u128::from(base)) % u128::from(R::MODULUS);
    }
    R::from(acc as u64)
}

/// The gadget matrix `G_n = Iₙ ⊗ [1, BASE, …, BASE^{DIGITS−1}] ∈ R_q^{n×nδ}`,
/// materialised independently of [`split`]/[`join`].
///
/// Tests compare against this object exactly because it *is* the second path: a
/// wrong digit layout still round-trips through `join ∘ split`, but it does not
/// reproduce `G_n`.
pub fn gadget_matrix<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    n: usize,
) -> RingMatrixKey<R, D> {
    let cols = n * DIGITS;
    let mut entries = vec![zero::<R, D>(); n * cols];
    for j in 0..n {
        for k in 0..DIGITS {
            entries[j * cols + j * DIGITS + k] = scalar_elt::<R, D>(pow_base::<R, BASE, DIGITS>(k));
        }
    }
    RingMatrixKey::from_entries(n, cols, entries)
}

/// The ring element with constant coefficient `c` and the rest zero.
pub fn scalar_elt<R: Ring, const D: usize>(c: R) -> Elt<R, D> {
    let mut coeff = [R::ZERO; D];
    coeff[0] = c;
    PolyRing::from_coefficients(coeff.to_vec())
}

/// The `n × n` identity over `R_q`.
pub fn identity_matrix<R: Ring, const D: usize>(n: usize) -> RingMatrixKey<R, D> {
    let mut entries = vec![zero::<R, D>(); n * n];
    for i in 0..n {
        entries[i * n + i] = scalar_elt::<R, D>(R::ONE);
    }
    RingMatrixKey::from_entries(n, n, entries)
}

/// The `rows × cols` zero matrix.
pub fn zero_matrix<R: Ring, const D: usize>(rows: usize, cols: usize) -> RingMatrixKey<R, D> {
    RingMatrixKey::from_entries(rows, cols, vec![zero::<R, D>(); rows * cols])
}

/// Column `j` of a matrix, zero-padded past the row count.
pub fn column<R: Ring, const D: usize>(m: &RingMatrixKey<R, D>, j: usize) -> Vec<Elt<R, D>> {
    (0..m.rows())
        .map(|i| m.get(i, j).cloned().unwrap_or_else(zero::<R, D>))
        .collect()
}

/// `A·B` over `R_q`: apply `A` to each column of `B`.
///
/// # Errors
/// [`TrapError::NotComposable`] naming both inner dimensions.
pub fn matmul<R: Ring, const D: usize>(
    a: &RingMatrixKey<R, D>,
    b: &RingMatrixKey<R, D>,
) -> Result<RingMatrixKey<R, D>, TrapError> {
    if a.cols() != b.rows() {
        return Err(TrapError::NotComposable {
            left_cols: a.cols(),
            right_rows: b.rows(),
        });
    }
    let mut entries = vec![zero::<R, D>(); a.rows() * b.cols()];
    for j in 0..b.cols() {
        let col = a.matvec(&column(b, j)).map_err(shape_err)?;
        for (i, v) in col.into_iter().enumerate() {
            entries[i * b.cols() + j] = v;
        }
    }
    Ok(RingMatrixKey::from_entries(a.rows(), b.cols(), entries))
}

/// `[A | B | …]`: equal row counts, summed column counts.
///
/// # Errors
/// [`TrapError::WrongShape`] naming the offending row count.
pub fn hstack<R: Ring, const D: usize>(
    parts: &[&RingMatrixKey<R, D>],
) -> Result<RingMatrixKey<R, D>, TrapError> {
    let rows = parts.first().map_or(0, |p| p.rows());
    if let Some(bad) = parts.iter().find(|p| p.rows() != rows) {
        return Err(TrapError::WrongShape {
            got: bad.rows(),
            expected: rows,
        });
    }
    let cols: usize = parts.iter().map(|p| p.cols()).sum();
    let mut entries = Vec::with_capacity(rows * cols);
    for i in 0..rows {
        for p in parts {
            entries.extend_from_slice(p.row(i));
        }
    }
    Ok(RingMatrixKey::from_entries(rows, cols, entries))
}

/// `[A ; B ; …]`: equal column counts, summed row counts.
///
/// # Errors
/// [`TrapError::WrongShape`] naming the offending column count.
pub fn vstack<R: Ring, const D: usize>(
    parts: &[&RingMatrixKey<R, D>],
) -> Result<RingMatrixKey<R, D>, TrapError> {
    let cols = parts.first().map_or(0, |p| p.cols());
    if let Some(bad) = parts.iter().find(|p| p.cols() != cols) {
        return Err(TrapError::WrongShape {
            got: bad.cols(),
            expected: cols,
        });
    }
    let rows: usize = parts.iter().map(|p| p.rows()).sum();
    let mut entries = Vec::with_capacity(rows * cols);
    for p in parts {
        for i in 0..p.rows() {
            entries.extend_from_slice(p.row(i));
        }
    }
    Ok(RingMatrixKey::from_entries(rows, cols, entries))
}

/// `diag(P₀, …, P_{k−1})`: the block shape SLAP's and FMN's `R̃` have — one `Rᵢ`
/// per block row, zeros elsewhere — so the padding is part of the object.
pub fn block_diag<R: Ring, const D: usize>(parts: &[&RingMatrixKey<R, D>]) -> RingMatrixKey<R, D> {
    let rows: usize = parts.iter().map(|p| p.rows()).sum();
    let cols: usize = parts.iter().map(|p| p.cols()).sum();
    let mut entries = vec![zero::<R, D>(); rows * cols];
    let mut r0 = 0;
    let mut c0 = 0;
    for p in parts {
        for i in 0..p.rows() {
            for j in 0..p.cols() {
                entries[(r0 + i) * cols + (c0 + j)] =
                    p.get(i, j).cloned().unwrap_or_else(zero::<R, D>);
            }
        }
        r0 += p.rows();
        c0 += p.cols();
    }
    RingMatrixKey::from_entries(rows, cols, entries)
}

/// Element-wise sum.
///
/// # Panics
/// If the lengths differ (a protocol shape bug, not a hostile input).
pub fn add_vec<R: Ring, const D: usize>(a: &[Elt<R, D>], b: &[Elt<R, D>]) -> Vec<Elt<R, D>> {
    assert_eq!(a.len(), b.len(), "vector addition needs equal lengths");
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| x.clone() + y.clone())
        .collect()
}

/// Element-wise difference `a − b`.
///
/// # Panics
/// If the lengths differ.
pub fn sub_vec<R: Ring, const D: usize>(a: &[Elt<R, D>], b: &[Elt<R, D>]) -> Vec<Elt<R, D>> {
    assert_eq!(a.len(), b.len(), "vector subtraction needs equal lengths");
    a.iter()
        .zip(b.iter())
        .map(|(x, y)| x.clone() - y.clone())
        .collect()
}

/// Negates every entry.
pub fn neg_vec<R: Ring, const D: usize>(a: &[Elt<R, D>]) -> Vec<Elt<R, D>> {
    a.iter().cloned().map(core::ops::Neg::neg).collect()
}

/// Scales every entry by the ring element `c`.
pub fn scale_vec<R: Ring, const D: usize>(c: &Elt<R, D>, a: &[Elt<R, D>]) -> Vec<Elt<R, D>> {
    a.iter().map(|x| x.clone() * c.clone()).collect()
}

/// The gadget recomposition `G·z`, so a scheme can state `t = G·t̂` without
/// reaching into [`crate::pcs::gadget`].
pub fn gadget_apply<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    digits: &[Elt<R, D>],
) -> Vec<Elt<R, D>> {
    join::<R, D, BASE, DIGITS>(digits)
}

/// `G_h⁻¹` applied **column-wise to a matrix**: for `M ∈ R_q^{h×c}` it returns
/// the `(h·DIGITS)×c` digit matrix with `G_h · that = M`.
///
/// SLAP's Setup needs this on a matrix, not a vector — its `Rᵢ := R·G⁻¹(w⁻ⁱ·G)`
/// takes the gadget inverse of the whole matrix `w⁻ⁱ·G`.
///
/// # Errors
/// [`TrapError::GadgetTooNarrow`] if the digit capacity cannot hold `q`.
pub fn gadget_inverse_matrix<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    m: &RingMatrixKey<R, D>,
) -> Result<RingMatrixKey<R, D>, TrapError> {
    check_gadget_capacity::<R, BASE, DIGITS>()?;
    let cols = m.cols();
    let mut entries = vec![zero::<R, D>(); m.rows() * DIGITS * cols];
    for j in 0..cols {
        let digits = split::<R, D, BASE, DIGITS>(&column(m, j));
        for (i, e) in digits.iter().enumerate() {
            entries[i * cols + j] = e.clone();
        }
    }
    Ok(RingMatrixKey::from_entries(
        m.rows() * DIGITS,
        cols,
        entries,
    ))
}

/// One centered uniform integer in `[-bound, bound]`.
///
/// The bit width is the smallest `b` with `2^b ≥ 2·bound+1` and out-of-range
/// draws are rejected, so the distribution is exactly uniform — an unmasked
/// `mod` would bias the low values, and a biased trapdoor block is a biased
/// CRS.
fn centered_draw<X: Xof>(stream: &mut BitStream<'_, X>, bound: u32) -> i64 {
    let span = 2 * bound + 1;
    let bits = u32::BITS - (span - 1).leading_zeros();
    loop {
        let v = stream.read_bits(bits);
        if v < span {
            return i64::from(v) - i64::from(bound);
        }
    }
}

/// A `rows × cols` matrix with coefficient-wise centered uniform entries in
/// `[-bound, bound]`, from a domain-separated seed.
///
/// This is MP12's `D` for the statistical instantiation, applied
/// coefficient-wise: coin flips only, no Gaussian oracle.
pub fn short_matrix<R: Ring, const D: usize>(
    label: &[u8],
    seed: &[u8; 32],
    rows: usize,
    cols: usize,
    bound: u32,
) -> RingMatrixKey<R, D> {
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(SHORTDOM);
    xof.absorb(label);
    xof.absorb(seed);
    xof.absorb(&(rows as u32).to_le_bytes());
    xof.absorb(&(cols as u32).to_le_bytes());
    xof.absorb(&bound.to_le_bytes());
    let mut stream = BitStream::new(&mut xof);
    let mut entries = Vec::with_capacity(rows * cols);
    for _ in 0..rows * cols {
        let coeff: Vec<R> = (0..D)
            .map(|_| from_centered::<R>(centered_draw(&mut stream, bound)))
            .collect();
        entries.push(PolyRing::from_coefficients(coeff));
    }
    RingMatrixKey::from_entries(rows, cols, entries)
}

/// A `len`-vector with coefficient-wise centered uniform entries in
/// `[-bound, bound]` (the perturbation `p` of [`preimage_random`]).
pub fn short_vec<R: Ring, const D: usize>(
    label: &[u8],
    seed: &[u8; 32],
    len: usize,
    bound: u32,
) -> Vec<Elt<R, D>> {
    let m = short_matrix::<R, D>(label, seed, 1, len, bound);
    (0..len).map(|j| m.get(0, j).cloned().unwrap()).collect()
}

/// A matrix `W` with a **certified** inverse.
///
/// SLAP's `w ← R_q^×` and FMN's `W ← GL(n, R_q)` enter their constructions only
/// through `W^{-i}·G`, and the crate has no solver over `R_q` (no NTT is
/// assumed, and `X^D+1` need not split). So the capability takes the pair and
/// checks `W·W⁻¹ = Iₙ = W⁻¹·W` exactly: a wrong inverse is a typed refusal, not
/// a silently broken CRS.
///
/// [`UnitMatrix::scalar_units`] is the solver-free constructor — a diagonal of
/// nonzero scalar units, invertible coefficient-wise. That is a *subfamily* of
/// `GL(n, R_q)`, not a uniform draw, and the assemblies that use it say so.
#[derive(Clone, PartialEq, Eq)]
pub struct UnitMatrix<R: Ring, const D: usize> {
    value: RingMatrixKey<R, D>,
    inverse: RingMatrixKey<R, D>,
}

impl<R: Ring, const D: usize> fmt::Debug for UnitMatrix<R, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "UnitMatrix<{}×{}>", self.value.rows(), self.value.cols())
    }
}

impl<R: Ring, const D: usize> UnitMatrix<R, D> {
    /// Wraps a pair and verifies both products are the identity.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if either matrix is not square or the sizes
    /// differ; [`TrapError::NotAUnit`] if either product is not `Iₙ`.
    pub fn new(
        value: RingMatrixKey<R, D>,
        inverse: RingMatrixKey<R, D>,
    ) -> Result<Self, TrapError> {
        if value.rows() != value.cols() {
            return Err(TrapError::WrongShape {
                got: value.cols(),
                expected: value.rows(),
            });
        }
        if inverse.rows() != inverse.cols() {
            return Err(TrapError::WrongShape {
                got: inverse.cols(),
                expected: inverse.rows(),
            });
        }
        if value.rows() != inverse.rows() {
            return Err(TrapError::WrongShape {
                got: inverse.rows(),
                expected: value.rows(),
            });
        }
        let id = identity_matrix::<R, D>(value.rows());
        if matmul(&value, &inverse)? != id || matmul(&inverse, &value)? != id {
            return Err(TrapError::NotAUnit);
        }
        Ok(Self { value, inverse })
    }

    /// `diag(u₀, …, u_{k−1})` over a field, with the coefficient-wise inverses.
    ///
    /// A nonzero scalar of `Z_q` is a unit of `R_q` with the same inverse
    /// (lifted to a constant polynomial), so no ring-level inversion is needed.
    ///
    /// # Errors
    /// [`TrapError::NotAUnit`] if any entry is zero, or empty input.
    pub fn scalar_units(units: &[R]) -> Result<Self, TrapError>
    where
        R: Field,
    {
        if units.is_empty() {
            return Err(TrapError::WrongShape {
                got: 0,
                expected: 1,
            });
        }
        let mut vals = Vec::with_capacity(units.len());
        let mut invs = Vec::with_capacity(units.len());
        for u in units {
            let Some(i) = u.inverse() else {
                return Err(TrapError::NotAUnit);
            };
            vals.push(*u);
            invs.push(i);
        }
        let diag = |cs: &[R]| {
            let n = cs.len();
            let mut entries = vec![zero::<R, D>(); n * n];
            for i in 0..n {
                entries[i * n + i] = scalar_elt::<R, D>(cs[i]);
            }
            RingMatrixKey::from_entries(n, n, entries)
        };
        Self::new(diag(&vals), diag(&invs))
    }

    /// The matrix itself.
    pub fn value(&self) -> &RingMatrixKey<R, D> {
        &self.value
    }

    /// Its certified inverse.
    pub fn inverse(&self) -> &RingMatrixKey<R, D> {
        &self.inverse
    }

    /// Side length.
    pub fn size(&self) -> usize {
        self.value.rows()
    }

    /// `(W⁰, …, W^{count−1})` and `(I, W⁻¹, …, W^{-(count−1)})`.
    ///
    /// FMN's Setup needs both halves: `Wⁱ·A` builds the block rows of `B`, and
    /// `W^{-i}·G` builds the trapdoor blocks `Rᵢ`.
    pub fn powers(&self, count: usize) -> (Vec<RingMatrixKey<R, D>>, Vec<RingMatrixKey<R, D>>) {
        let n = self.size();
        let mut pos = Vec::with_capacity(count);
        let mut neg = Vec::with_capacity(count);
        let mut acc = identity_matrix::<R, D>(n);
        let mut acci = identity_matrix::<R, D>(n);
        for _ in 0..count {
            pos.push(acc.clone());
            neg.push(acci.clone());
            acc = matmul(&acc, &self.value).expect("square matrices compose");
            acci = matmul(&acci, &self.inverse).expect("square matrices compose");
        }
        (pos, neg)
    }

    /// `Wᵉ` as a new *certified* unit, for a scheme that re-powers the slot
    /// multiplier on the fly — FMN Fig. 6 step 2(d) sets `Wᵣ := W^k_{r−1}`, so
    /// the folded instance's `W⁻ⁱ·t` check runs against `W^{k·r}`.
    ///
    /// The pair is rebuilt by repeated multiplication and re-verified through
    /// [`UnitMatrix::new`], so an exponentiation that does not round-trip is a
    /// refusal rather than a silently broken relation.
    ///
    /// # Errors
    /// Propagates [`TrapError::NotAUnit`] if the rebuilt pair fails the check.
    pub fn powered(&self, e: usize) -> Result<Self, TrapError> {
        let n = self.size();
        let mut v = identity_matrix::<R, D>(n);
        let mut vi = identity_matrix::<R, D>(n);
        for _ in 0..e {
            v = matmul(&v, &self.value)?;
            vi = matmul(&self.inverse, &vi)?;
        }
        Self::new(v, vi)
    }
}

/// A TrapGen key pair: the published Ajtai matrix and its gadget trapdoor.
#[derive(Clone)]
pub struct TrapdoorKey<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> {
    pub_a: RingMatrixKey<R, D>,
    uniform: RingMatrixKey<R, D>,
    trap: RingMatrixKey<R, D>,
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> fmt::Debug
    for TrapdoorKey<R, D, BASE, DIGITS>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TrapdoorKey<A {}×{}, B {}×{}>",
            self.pub_a.rows(),
            self.pub_a.cols(),
            self.trap.rows(),
            self.trap.cols()
        )
    }
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>
    TrapdoorKey<R, D, BASE, DIGITS>
{
    /// MP12 `GenTrap`: `A = [Ā | G − Ā·R]` with `Ā` the uniform expansion of
    /// `(label, seed)` and `R` the short one, publishing `B = [R; I]`.
    ///
    /// `n` is the gadget height (the module rank) and `mbar` the width of the
    /// uniform half; the published matrix has `m = mbar + n·DIGITS` columns.
    ///
    /// # Panics
    /// If `n == 0`, `mbar == 0`, or the gadget is too narrow for `q`.
    pub fn generate(label: &[u8], seed: &[u8; 32], n: usize, mbar: usize) -> Self {
        assert!(
            n > 0 && mbar > 0,
            "a trapdoor key needs a non-degenerate shape"
        );
        check_gadget_capacity::<R, BASE, DIGITS>().expect("gadget must be wide enough for q");
        let t = n * DIGITS;
        let mut dom = Vec::with_capacity(TRAPDOM.len() + label.len());
        dom.extend_from_slice(TRAPDOM);
        dom.extend_from_slice(label);
        let uniform = RingMatrixKey::setup(&dom, seed, n, mbar);
        // bound = 1 ⇒ the {−1,0,1} block of MP12's worked instantiation.
        let r = short_matrix::<R, D>(label, seed, mbar, t, 1);
        let g = gadget_matrix::<R, D, BASE, DIGITS>(n);
        let ar = matmul(&uniform, &r).expect("shapes match by construction");
        let second = sub_matrix(&g, &ar);
        Self {
            pub_a: hstack(&[&uniform, &second]).expect("same row count"),
            uniform,
            trap: vstack(&[&r, &identity_matrix::<R, D>(t)]).expect("same column count"),
        }
    }

    /// The published parity-check matrix `A ∈ R_q^{n×m}`.
    pub fn public(&self) -> &RingMatrixKey<R, D> {
        &self.pub_a
    }

    /// The trapdoor `B = [R; I] ∈ R^{m×nδ}` with `A·B = G`.
    pub fn trapdoor(&self) -> &RingMatrixKey<R, D> {
        &self.trap
    }

    /// The uniform half `Ā` — the first `m − nδ` columns of `A`, exactly as
    /// sampled (MP12: `A` must *contain* the uniform block).
    pub fn uniform_half(&self) -> &RingMatrixKey<R, D> {
        &self.uniform
    }

    /// Height `n`.
    pub fn rows(&self) -> usize {
        self.pub_a.rows()
    }

    /// Gadget width `t = n·DIGITS` = the column count of `B`.
    pub fn gadget_width(&self) -> usize {
        self.trap.cols()
    }

    /// `G_n`, for a relation check.
    pub fn gadget(&self) -> RingMatrixKey<R, D> {
        gadget_matrix::<R, D, BASE, DIGITS>(self.rows())
    }

    /// The certified `‖·‖∞` bound on this key's preimages with a perturbation
    /// of that coefficient bound — see [`bound_of_matrix`].
    pub fn certified_bound(&self, perturbation: u32) -> u64 {
        bound_of_matrix::<R, D, BASE, DIGITS>(&self.trap, perturbation)
    }

    /// The deterministic short preimage `x = B·G⁻¹(u)` (SLAP App. C).
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] unless `u` has `n` entries.
    pub fn preimage(&self, target: &[Elt<R, D>]) -> Result<Vec<Elt<R, D>>, TrapError> {
        preimage_with_trapdoor::<R, D, BASE, DIGITS>(&self.pub_a, &self.trap, target)
    }

    /// A randomised short preimage: `x = p + B·G⁻¹(u − A·p)` with `p` uniform in
    /// `[-perturbation, perturbation]` per coefficient.
    ///
    /// # Errors
    /// As [`preimage`].
    pub fn preimage_random(
        &self,
        target: &[Elt<R, D>],
        seed: &[u8; 32],
        perturbation: u32,
    ) -> Result<Vec<Elt<R, D>>, TrapError> {
        preimage_random_with_trapdoor::<R, D, BASE, DIGITS>(
            &self.pub_a,
            &self.trap,
            target,
            b"key",
            seed,
            perturbation,
        )
    }
}

/// The deterministic gadget preimage `x = M·G⁻¹(u)` under **any** matrix `M`
/// satisfying `B·M = G_h` for the height-`h` gadget.
///
/// MP12's `[R; I]` shape is deliberately *not* used — only the relation — which
/// is what lets the derived trapdoors `R̃`/`T` of SLAP and FMN Fig. 4 feed the
/// same routine. That is also why the caller must keep `B`: this function does
/// not check the relation, [`trapdoor_relation`] does.
///
/// # Errors
/// [`TrapError::WrongShape`] if `u` is not `B.rows()` long;
/// [`TrapError::NotComposable`] if `M` is not `B.cols()` tall.
pub fn preimage_with_trapdoor<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    b: &RingMatrixKey<R, D>,
    trap: &RingMatrixKey<R, D>,
    target: &[Elt<R, D>],
) -> Result<Vec<Elt<R, D>>, TrapError> {
    if target.len() != b.rows() {
        return Err(TrapError::WrongShape {
            got: target.len(),
            expected: b.rows(),
        });
    }
    if trap.rows() != b.cols() {
        return Err(TrapError::NotComposable {
            left_cols: b.cols(),
            right_rows: trap.rows(),
        });
    }
    let digits = split::<R, D, BASE, DIGITS>(target);
    trap.matvec(&digits).map_err(shape_err)
}

/// The randomised preimage `x = p + M·G⁻¹(u − B·p)` (MP12 Alg. 3 with a bounded
/// perturbation in place of its Gaussian one).
///
/// # Errors
/// As [`preimage_with_trapdoor`].
pub fn preimage_random_with_trapdoor<
    R: Ring,
    const D: usize,
    const BASE: u64,
    const DIGITS: usize,
>(
    b: &RingMatrixKey<R, D>,
    trap: &RingMatrixKey<R, D>,
    target: &[Elt<R, D>],
    label: &[u8],
    seed: &[u8; 32],
    perturbation: u32,
) -> Result<Vec<Elt<R, D>>, TrapError> {
    let mut dom = Vec::with_capacity(PERTDOM.len() + label.len());
    dom.extend_from_slice(PERTDOM);
    dom.extend_from_slice(label);
    let p = short_vec::<R, D>(&dom, seed, trap.rows(), perturbation);
    let residual = sub_vec(target, &b.matvec(&p).map_err(shape_err)?);
    let x = preimage_with_trapdoor::<R, D, BASE, DIGITS>(b, trap, &residual)?;
    Ok(add_vec(&p, &x))
}

/// Checks the defining relation `B·M = G_h` of a gadget trapdoor.
///
/// # Errors
/// [`TrapError::NotComposable`] if the product is not defined.
pub fn trapdoor_relation<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    b: &RingMatrixKey<R, D>,
    trap: &RingMatrixKey<R, D>,
) -> Result<bool, TrapError> {
    Ok(matmul(b, trap)? == gadget_matrix::<R, D, BASE, DIGITS>(b.rows()))
}

/// Verifies `A·x = u` exactly (the check a verifier, or a test, runs).
///
/// # Errors
/// [`TrapError::WrongShape`] if `x` or `u` has the wrong length.
pub fn preimage_ok<R: Ring, const D: usize>(
    a: &RingMatrixKey<R, D>,
    target: &[Elt<R, D>],
    x: &[Elt<R, D>],
) -> Result<bool, TrapError> {
    if x.len() != a.cols() {
        return Err(TrapError::WrongShape {
            got: x.len(),
            expected: a.cols(),
        });
    }
    if target.len() != a.rows() {
        return Err(TrapError::WrongShape {
            got: target.len(),
            expected: a.rows(),
        });
    }
    Ok(a.matvec(x).map_err(shape_err)? == target)
}

/// The certified `‖·‖∞` bound for `M·G⁻¹(·)`: with digit magnitudes
/// `dz = ⌊BASE/2⌋` each digit plane has `‖·‖₁ ≤ D·dz`, so
///
/// ```text
/// ‖M·G⁻¹(v)‖∞ ≤ dz · (D · max_i Σ_j ‖M_ij‖∞ + 1)   (+ extra)
/// ```
///
/// The row sum is over the **actual** entries of `M`, so this is a statement
/// about this key rather than a worst case over the sampling distribution — a
/// norm gate `γ` can be derived from it instead of guessed.
pub fn bound_of_matrix<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    m: &RingMatrixKey<R, D>,
    extra: u32,
) -> u64 {
    let dz = digit_half_width(BASE);
    let mut worst: u64 = 0;
    for i in 0..m.rows() {
        let row: u64 = m
            .row(i)
            .iter()
            .map(|e| {
                ring_to_u32::<R, D>(e)
                    .iter()
                    .map(|&c| {
                        let x = u64::from(c);
                        x.min(R::MODULUS - x)
                    })
                    .sum::<u64>()
            })
            .sum();
        worst = worst.max(row);
    }
    u64::from(extra) + dz * (D as u64 * worst + 1)
}

/// The `‖·‖∞` of a vector of ring elements, in centered representatives.
///
/// Generic over [`Ring`] (not [`CenteredRing`]) so a scheme's norm gate does not
/// have to carry an extra bound: the centered magnitude of a residue `x` is
/// `min(x, q − x)`, which needs only the modulus.
pub fn vector_infinity_norm<R: Ring, const D: usize>(v: &[Elt<R, D>]) -> u64 {
    v.iter()
        .map(|e| {
            ring_to_u32::<R, D>(e)
                .iter()
                .map(|&c| {
                    let x = u64::from(c);
                    x.min(R::MODULUS - x)
                })
                .max()
                .unwrap_or(0)
        })
        .max()
        .unwrap_or(0)
}

/// Element-wise `a − b` of two equally-sized matrices.
///
/// # Panics
/// If the shapes differ.
fn sub_matrix<R: Ring, const D: usize>(
    a: &RingMatrixKey<R, D>,
    b: &RingMatrixKey<R, D>,
) -> RingMatrixKey<R, D> {
    assert_eq!(
        (a.rows(), a.cols()),
        (b.rows(), b.cols()),
        "matrix shapes differ"
    );
    let entries = (0..a.rows())
        .flat_map(|i| {
            a.row(i)
                .iter()
                .zip(b.row(i))
                .map(|(x, y)| x.clone() - y.clone())
                .collect::<Vec<_>>()
        })
        .collect();
    RingMatrixKey::from_entries(a.rows(), a.cols(), entries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    /// NTT-friendly house prime (`q − 1` divisible by 512).
    type Z1 = Zq<8380417>;
    /// The non-NTT instance: `2³² − 99`, prime, `≡ 5 (mod 8)`, which is what
    /// SLAP Rem. 2.11 / FMN Lem. 2.15 actually require.
    type Q5 = Zq<4294967197>;

    const BIN: u64 = 2;
    /// `⌈log₂ 8380417⌉ = 23`.
    const K23: usize = 23;
    /// `⌈log₂ (2³² − 99)⌉ = 32`.
    const K32: usize = 32;

    fn targets<const D: usize>(n: usize, tag: u64) -> Vec<Elt<Q5, D>> {
        (0..n)
            .map(|j| scalar_elt::<Q5, D>(Q5::from(tag * 991 + j as u64 * 7 + 3)))
            .collect()
    }

    #[test]
    fn trapgen_satisfies_the_sis_relation_exactly() {
        // A·B = G_n, compared against the materialised gadget (a second path),
        // on the non-NTT ring with d = 64 — the instance the schemes need.
        let td = TrapdoorKey::<Q5, 64, BIN, K32>::generate(b"rel", &[1u8; 32], 2, 3);
        assert!(
            trapdoor_relation::<Q5, 64, BIN, K32>(td.public(), td.trapdoor()).expect("composable"),
            "A·B must equal G_n exactly"
        );
        // and a trapdoor with one entry off must fail the same check: this is
        // the non-vacuity half — a check that always returned `true` would let
        // a broken R through, and the relation is what every preimage rests on.
        let t = td.gadget_width();
        let rows = td.trapdoor().rows();
        let mut entries = Vec::with_capacity(rows * t);
        for i in 0..rows {
            for j in 0..t {
                let e = td.trapdoor().get(i, j).cloned().unwrap();
                entries.push(if (i, j) == (0, 0) {
                    e + scalar_elt::<Q5, 64>(Q5::ONE)
                } else {
                    e
                });
            }
        }
        let bad = RingMatrixKey::from_entries(rows, t, entries);
        assert!(
            !trapdoor_relation::<Q5, 64, BIN, K32>(td.public(), &bad).unwrap(),
            "one flipped entry in B must break A·B = G"
        );
    }

    #[test]
    fn published_matrix_contains_the_uniform_half_and_the_derived_one() {
        // A silent transpose survives every relation test, so pin the layout:
        // left half == the uniform expansion, right half == G − Ā·R, both
        // recomputed independently here.
        let td = TrapdoorKey::<Q5, 8, BIN, K32>::generate(b"layout", &[2u8; 32], 2, 2);
        let (n, mbar) = (td.rows(), td.uniform_half().cols());
        let t = n * K32;
        assert_eq!(td.public().cols(), mbar + t, "m = mbar + n·DIGITS");
        for i in 0..n {
            for j in 0..mbar {
                assert_eq!(
                    td.public().get(i, j),
                    td.uniform_half().get(i, j),
                    "column {j} of row {i} must be the uniform entry"
                );
            }
        }
        let g = gadget_matrix::<Q5, 8, BIN, K32>(n);
        let r = {
            // recover R from the trapdoor's top block and redo G − ĀR
            let mut entries = Vec::new();
            for i in 0..mbar {
                for j in 0..t {
                    entries.push(td.trapdoor().get(i, j).cloned().unwrap());
                }
            }
            RingMatrixKey::from_entries(mbar, t, entries)
        };
        let second = sub_matrix(&g, &matmul(td.uniform_half(), &r).unwrap());
        for i in 0..n {
            for j in 0..t {
                assert_eq!(
                    td.public().get(i, mbar + j),
                    second.get(i, j),
                    "second block entry ({i},{j}) must be (G − ĀR)₍ᵢ,ⱼ₎"
                );
            }
        }
        // and the bottom block of B really is the identity (MP12's T)
        for i in 0..t {
            for j in 0..t {
                let want = if i == j { Q5::ONE } else { Q5::ZERO };
                assert_eq!(
                    td.trapdoor().get(mbar + i, j),
                    Some(&scalar_elt::<Q5, 8>(want)),
                    "B's lower block is I_t"
                );
            }
        }
    }

    #[test]
    fn both_samplers_solve_the_relation_and_stay_under_the_bound() {
        let td = TrapdoorKey::<Q5, 8, BIN, K32>::generate(b"samp", &[3u8; 32], 2, 2);
        let bound0 = td.certified_bound(0);
        let bound4 = td.certified_bound(4);
        assert!(
            bound0 < bound4,
            "the bound must charge for the perturbation"
        );
        for tag in 0..3u64 {
            let u = targets::<8>(2, tag);
            let x = td.preimage(&u).expect("right shape");
            assert!(
                preimage_ok(td.public(), &u, &x).expect("right shape"),
                "the deterministic preimage must satisfy A·x = u"
            );
            assert!(
                vector_infinity_norm(&x) <= bound0,
                "‖x‖∞ = {} must respect the certified bound {bound0}",
                vector_infinity_norm(&x)
            );
            let y = td.preimage_random(&u, &[9u8; 32], 4).expect("right shape");
            assert!(
                preimage_ok(td.public(), &u, &y).expect("right shape"),
                "the randomised preimage must satisfy A·x = u"
            );
            assert!(
                vector_infinity_norm(&y) <= bound4,
                "‖y‖∞ = {} must respect {bound4}",
                vector_infinity_norm(&y)
            );
        }
    }

    #[test]
    fn the_randomised_sampler_really_randomises() {
        // A "SamplePre" that returns one fixed answer per target would pass
        // every relation test, so assert the draws differ — and that the
        // deterministic one is exactly the p = 0 special case.
        let td = TrapdoorKey::<Q5, 8, BIN, K32>::generate(b"rnd", &[4u8; 32], 2, 2);
        let u = targets::<8>(2, 11);
        let a = td.preimage_random(&u, &[5u8; 32], 3).unwrap();
        let b = td.preimage_random(&u, &[6u8; 32], 3).unwrap();
        assert_ne!(
            a, b,
            "distinct perturbation seeds must give distinct preimages"
        );
        assert_ne!(
            a,
            td.preimage(&u).unwrap(),
            "a perturbation must move the answer"
        );
        assert_eq!(
            td.preimage_random(&u, &[7u8; 32], 0).unwrap(),
            td.preimage(&u).unwrap(),
            "perturbation 0 must reproduce the deterministic preimage"
        );
    }

    #[test]
    fn a_tampered_preimage_and_a_wrong_target_are_both_refused() {
        let td = TrapdoorKey::<Q5, 8, BIN, K32>::generate(b"tamper", &[5u8; 32], 2, 2);
        let u = targets::<8>(2, 21);
        let x = td.preimage(&u).unwrap();
        assert!(preimage_ok(td.public(), &u, &x).unwrap());
        let mut bad = x.clone();
        bad[0] = bad[0].clone() + scalar_elt::<Q5, 8>(Q5::ONE);
        assert!(
            !preimage_ok(td.public(), &u, &bad).unwrap(),
            "one coefficient flipped must break A·x = u"
        );
        let other = targets::<8>(2, 22);
        assert!(
            !preimage_ok(td.public(), &other, &x).unwrap(),
            "a preimage of u must not solve a different target"
        );
    }

    #[test]
    fn shapes_are_refused_not_panicked() {
        let td = TrapdoorKey::<Q5, 8, BIN, K32>::generate(b"shape", &[6u8; 32], 2, 2);
        let long = targets::<8>(3, 1);
        assert_eq!(
            td.preimage(&long),
            Err(TrapError::WrongShape {
                got: 3,
                expected: 2
            })
        );
        let u = targets::<8>(2, 1);
        let x = td.preimage(&u).unwrap();
        assert_eq!(
            preimage_ok(td.public(), &u, &x[..x.len() - 1]),
            Err(TrapError::WrongShape {
                got: x.len() - 1,
                expected: x.len()
            })
        );
        let bad = matmul(
            &short_matrix::<Q5, 8>(b"L", &[1u8; 32], 2, 3, 1),
            &short_matrix::<Q5, 8>(b"R", &[1u8; 32], 4, 2, 1),
        );
        assert_eq!(
            bad,
            Err(TrapError::NotComposable {
                left_cols: 3,
                right_rows: 4
            }),
            "a 2×3 by 4×2 product must name both inner dimensions"
        );
    }

    /// A vector as a one-column matrix, so the materialised gadget can be
    /// multiplied by it through the same path the schemes use.
    fn as_column<R: Ring, const D: usize>(v: &[Elt<R, D>]) -> RingMatrixKey<R, D> {
        RingMatrixKey::from_entries(v.len(), 1, v.to_vec())
    }

    #[test]
    fn gadget_matrix_and_the_digit_map_agree() {
        // G_n · G⁻¹(v) = v through the *materialised* G, not through `join`:
        // this is what pins the digit layout used by every relation above.
        let n = 3;
        let g = gadget_matrix::<Q5, 4, BIN, K32>(n);
        assert_eq!((g.rows(), g.cols()), (n, n * K32));
        let v = targets::<4>(n, 31);
        let digits = split::<Q5, 4, BIN, K32>(&v);
        assert_eq!(digits.len(), n * K32, "one plane per digit");
        assert_eq!(
            matmul(&g, &as_column(&digits)).unwrap(),
            as_column(&v),
            "the materialised G must recompose the split digits"
        );
        // and the explicit non-zero pattern: BASE^k on the block diagonal
        assert_eq!(
            *g.get(1, K32 + 2).unwrap(),
            scalar_elt::<Q5, 4>(Q5::from(4u64)),
            "entry (1, δ+2) must be BASE²"
        );
        assert_eq!(*g.get(0, K32).unwrap(), scalar_elt::<Q5, 4>(Q5::ZERO));
        // the last plane of the last row is the only entry there: pins the tail
        assert_eq!(
            *g.get(n - 1, n * K32 - 1).unwrap(),
            scalar_elt::<Q5, 4>(Q5::from(1u64 << (K32 - 1))),
            "the top digit of the last row is BASE^(DIGITS-1)"
        );
    }

    #[test]
    fn unit_matrix_refuses_a_non_inverse() {
        let w = UnitMatrix::<Q5, 8>::scalar_units(&[Q5::from(3u64), Q5::from(5u64)]).unwrap();
        assert_eq!(w.size(), 2);
        let (pos, neg) = w.powers(3);
        assert_eq!(pos[0], identity_matrix::<Q5, 8>(2));
        assert_eq!(
            matmul(&pos[2], &neg[2]).unwrap(),
            identity_matrix::<Q5, 8>(2)
        );
        // a deliberately wrong "inverse": the transpose of the value with one
        // diagonal entry replaced by 0
        let mut bad_entries = Vec::new();
        for i in 0..2 {
            for j in 0..2 {
                bad_entries.push(
                    w.inverse()
                        .get(i, j)
                        .cloned()
                        .map(|e| if i == 0 && j == 0 { e.clone() + e } else { e })
                        .unwrap(),
                );
            }
        }
        let bad = RingMatrixKey::from_entries(2, 2, bad_entries);
        assert_eq!(
            UnitMatrix::new(w.value().clone(), bad),
            Err(TrapError::NotAUnit),
            "2·W⁻¹ on the diagonal must be refused"
        );
        assert_eq!(
            UnitMatrix::<Q5, 8>::scalar_units(&[Q5::from(7u64), Q5::ZERO]),
            Err(TrapError::NotAUnit),
            "0 is not a unit"
        );
    }

    #[test]
    fn short_matrix_is_bounded_reproducible_and_label_bound() {
        let a = short_matrix::<Q5, 8>(b"x", &[1u8; 32], 4, 6, 1);
        let b = short_matrix::<Q5, 8>(b"x", &[1u8; 32], 4, 6, 1);
        let c = short_matrix::<Q5, 8>(b"y", &[1u8; 32], 4, 6, 1);
        assert_eq!(a, b, "same (label, seed) must reproduce");
        assert_ne!(a, c, "the label must domain-separate");
        let mut zeros = 0;
        let mut ones = 0;
        for e in (0..a.rows()).flat_map(|i| (0..a.cols()).map(move |j| (i, j))) {
            for c in ring_to_u32::<Q5, 8>(a.get(e.0, e.1).unwrap()).iter() {
                let x = u64::from(*c);
                let mag = x.min(Q5::MODULUS - x);
                assert!(mag <= 1, "a bound-1 draw must be ternary, got {mag}");
                zeros += (mag == 0) as u32;
                ones += (mag == 1) as u32;
            }
        }
        assert!(ones > 0 && zeros > 0, "the draw must use both outcomes");
    }

    #[test]
    fn stacks_and_block_diagonals_place_blocks_where_the_schemes_read_them() {
        let a = short_matrix::<Q5, 4>(b"a", &[1u8; 32], 2, 3, 1);
        let b = short_matrix::<Q5, 4>(b"b", &[2u8; 32], 2, 5, 1);
        let h = hstack(&[&a, &b]).unwrap();
        assert_eq!((h.rows(), h.cols()), (2, 8));
        assert_eq!(h.get(1, 4), b.get(1, 1), "b starts at column 3");
        let v = vstack(&[&a, &b]).expect_err("a 3-column and a 5-column block cannot stack");
        assert_eq!(
            v,
            TrapError::WrongShape {
                got: 5,
                expected: 3
            }
        );
        let d = block_diag(&[&a, &b]);
        assert_eq!((d.rows(), d.cols()), (4, 8));
        assert_eq!(
            d.get(3, 6),
            b.get(1, 3),
            "b's block sits at rows 2.., cols 3.."
        );
        assert_eq!(
            d.get(1, 4),
            Some(&zero::<Q5, 4>()),
            "the off-diagonal must be zero, not garbage"
        );
        assert_eq!(d.get(0, 0), a.get(0, 0));
    }

    #[test]
    fn works_on_the_ntt_friendly_ring_too() {
        // Same capability, Z1 instance: 2^23 > q, and the digits are exact.
        let td = TrapdoorKey::<Z1, 8, BIN, K23>::generate(b"z1", &[7u8; 32], 2, 2);
        assert!(trapdoor_relation::<Z1, 8, BIN, K23>(td.public(), td.trapdoor()).unwrap());
        let u: Vec<Elt<Z1, 8>> = (0..2)
            .map(|j| scalar_elt::<Z1, 8>(Z1::from(j as u64 + 40)))
            .collect();
        let x = td.preimage(&u).unwrap();
        assert!(preimage_ok(td.public(), &u, &x).unwrap());
        assert!(vector_infinity_norm(&x) <= td.certified_bound(0));
    }

    #[test]
    fn a_narrow_gadget_is_refused() {
        // 2^8 < q: `G⁻¹` would wrap, so TrapGen must refuse rather than publish
        // a key whose "preimages" solve the wrong equation.
        let r = std::panic::catch_unwind(|| {
            TrapdoorKey::<Q5, 8, BIN, 8>::generate(b"narrow", &[1u8; 32], 2, 2)
        });
        assert!(r.is_err(), "BASE^DIGITS <= q must be rejected");
    }

    #[test]
    fn base_diagonal_unit_matrix_is_not_uniform_but_is_exact() {
        // Documents the deviation: scalar_units gives a diagonal of units, whose
        // powers round-trip exactly. The schemes' own CRS draws W uniformly;
        // nothing here claims it does.
        let w = UnitMatrix::<Q5, 64>::scalar_units(&[Q5::from(1_234_567u64)]).unwrap();
        let (pos, neg) = w.powers(4);
        for i in 0..4 {
            assert_eq!(
                matmul(&pos[i], &neg[i]).unwrap(),
                identity_matrix::<Q5, 64>(1),
                "W^i·W^-i = I at i = {i}"
            );
        }
    }
}
