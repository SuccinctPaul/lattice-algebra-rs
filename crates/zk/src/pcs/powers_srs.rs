//! Structured **powers-of-a-unit** reference strings and the linear functional
//! commitments built on them (Z7).
//!
//! This is the capability layer that [`crate::pcs::mle`]'s tall Ajtai keys
//! cannot provide: an Ajtai key is a *random* matrix, so its commitments are
//! only usable for the vectors the key itself indexes. A **structured**
//! universal reference string instead publishes short preimages of the powers
//! `vⁱ` of one invertible ring element `v`, and that algebraic relation is what
//! lets a *derived* linear functional be committed to out of public values:
//!
//! ```text
//! ⟨a₀, u_{0,i}⟩ ≡ vⁱ mod q  (i ∈ Z(W) \ {0})     ⟨a₁, u_{1,i}⟩ ≡ vⁱ·t mod q  (i ∈ [W])
//! ```
//!
//! Because the targets are monomials evaluated at `v` (`g(v) = vⁱ` for the
//! Laurent monomial set `G₀ = [Xⁱ]_{i∈P}`), the commitment to *any* linear
//! functional `f` is `Σᵢ fᵢv⁻ⁱ` — which the verifier forms from `f` and `v`
//! alone, never from a key entry. That is the whole of the "preprocessing" and
//! "polylogarithmic verifier" story, and it is also what makes the SRS
//! *universal*: one setup covers every dimension `w ≤ W`.
//!
//! The scheme this layer assembles is Orbweaver (Fisch–Liu–Vesely, CRYPTO 2023,
//! eprint 2024/2026, rev. 2024-12 §4); the algorithms here are named after that
//! section's boxes — `Setup`, `Com`, `Open`, `PreVerify`, `Verify` — plus the
//! §4.1 extensions (proof aggregation, the inner-product argument, the halved
//! verifier) and the §4.2 integer shim. Assumption: **k-P-R-ISIS** (plain, for
//! evaluation binding) and its knowledge counterpart (for extractability),
//! §2.4.1–§2.4.2.
//!
//! # The SRS is *trusted setup*
//!
//! `Setup` runs `TrapGen`, which keeps a trapdoor. Whoever holds it can sample
//! a short preimage of **any** target, so they can open a committed vector to
//! any value they like. [`setup`] therefore returns the public SRS *and* the
//! trapdoor ([`SetupTrapdoor`]) separately, and the caller must destroy the
//! latter — [`SetupTrapdoor`] is the paper's toxic waste, not a prover secret.
//! `shared_and_distinct_a_both_prove` demonstrates the consequence of not
//! destroying it.
//!
//! # What `TrapGen` / `SampPre` are here (§2.3, §5.1)
//!
//! [`Trapdoor`] instantiates the two sampling algorithms with the
//! Micciancio–Pallemore shape §5.1 names — "trapdoor public RSIS vectors in
//! [MP12] are of the form `a = [â | g − râ]`" — with the gadget vector
//! `g = (1, B, …, B^{k−1})` from [`crate::pcs::gadget`] and a short trapdoor
//! `R`. A preimage of `y` is `u = (w + R·e, e)`, where `w` is a fresh short
//! randomizer and `e` is the exact digit decomposition of `y − ⟨â, w⟩`, so
//!
//! ```text
//! ⟨a, u⟩ = ⟨â, w + R·e⟩ + ⟨g − â·R, e⟩ = ⟨â, w⟩ + ⟨g, e⟩ = ⟨â, w⟩ + (y − ⟨â, w⟩) = y
//! ```
//!
//! holds *identically* ([`Trapdoor::samp_pre`], pinned by
//! `samp_pre_is_exact_and_short`), and `w` is what makes the output a
//! distribution rather than a point mass.
//!
//! Two documented deviations from the ideal §2.3 specification, both inherited
//! from that gadget form:
//!
//! - `a` is not information-theoretically uniform: with `ℓ = 2k` entries it is
//!   an RLWE sample — §5.1 says exactly this ("one can see the resulting `a` is
//!   an RLWE sample"), so indistinguishability rests on RLWE in addition to the
//!   leftover-hash condition `ℓ ≥ lhl(R_q, b)`;
//! - statistical closeness of [`Trapdoor::samp_pre`] to `SampD` conditioned on
//!   the target is *not* proved here. `w` supplies `k` ring elements' worth of
//!   `ρ`-bounded entropy per preimage, which is the mechanism, not the theorem.
//!
//! # `t` and the ring's splitting (Definition 2.15)
//!
//! The knowledge half needs `t ←$ T`, which the paper takes to be "all the
//! elements `t` such that exactly half of the elements in the NTT representation
//! of `t` are zero", and it is explicit that this "is only defined when `⟨q⟩` is
//! not a prime ideal in `R`". [`vanishing_element`] implements that set in the
//! coefficient domain — `t = ∏_{r∈S}(r − X)` over a half-size `S` of the roots
//! of `X^D + 1` — and refuses with [`SrsError::NotSplitCompletely`] on a ring
//! where `X^D + 1` has no linear factors, e.g. the `q ≡ 5 (mod 8)` instance
//! other lanes use. There the *binding* half of the scheme (the k-P-R-ISIS
//! window, `Open`, `PreVerify` and the opening equation) is still fully
//! available: [`Trapdoor`], [`laurent_product`] and [`pairing`] are generic over
//! any `(R, D)`, and `non_ntt_ring_binding_half_round_trips` exercises them on
//! `q = 2³² − 99`, `d = 64`.
//!
//! # Norm accounting (Table 1, Theorem 4.1)
//!
//! [`NormBounds::derive`] computes `δ_M`, `δ₁`, `δ₀` and `β*₀` from the declared
//! alphabet bounds and the ring expansion factor `γ_R ≤ D` (Theorem 2.2) — no
//! tuned gates. The paper states one `α` for both witness and functional; §4.3
//! needs them separate (a power-table functional has `‖f‖ ≤ α^{log w + 1}`), so
//! `derive` takes `alpha_x` and `alpha_f`, and the single-`α` scheme is
//! `derive(w, α, α, …)`.

use crate::foundation::fs::seed_stream;
use crate::foundation::sampling::{
    centered_bounded_poly, fixed_weight_signs, uniform_poly, uniform_vec_from_seed,
};
use crate::pcs::gadget::{digit_half_width, split};
use crate::pcs::mixed::{dot as ring_dot, BlockMat};
use crate::pcs::packing::sigma_of;
use crate::pcs::projection::{const_term, from_coeffs, to_coeffs};
use crate::shortness::exact_l2::max_magnitude;
use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::number_theory::{find_primitive_root, x_pow_d_plus_1_splitting};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::{CenteredRing, Field};
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Domain label for the trapdoor entries.
const TRAP_DOMAIN: &[u8] = b"lattice-algebra/Z7/powers-trap";
/// Domain label for the preimage randomizer.
const PREIMAGE_DOMAIN: &[u8] = b"lattice-algebra/Z7/powers-preimage";
/// Domain label for the `v ←$ R×_q` draw.
const UNIT_DOMAIN: &[u8] = b"lattice-algebra/Z7/powers-unit";
/// Domain label for the `t ←$ T` draw.
const T_DOMAIN: &[u8] = b"lattice-algebra/Z7/powers-t";

/// One element of `R_q = Z_R[X]/(X^D + 1)`.
type Elt<R, const D: usize> = PolyRing<R, D>;

/// The additive identity of `R_q`.
fn zero_elt<R: Ring, const D: usize>() -> Elt<R, D> {
    PolyRing::from_coefficients(vec![R::ZERO; D])
}

/// The constant ring element `c`.
fn const_elt<R: Ring, const D: usize>(c: R) -> Elt<R, D> {
    PolyRing::from_coefficients(vec![c])
}

/// The monomial `X^k`, with the negacyclic sign when `k ≥ D`.
fn monomial<R: Ring, const D: usize>(k: usize) -> Elt<R, D> {
    let mut coeffs = vec![R::ZERO; D];
    coeffs[k % D] = if (k / D) % 2 == 0 { R::ONE } else { -R::ONE };
    PolyRing::from_coefficients(coeffs)
}

/// The largest centered coefficient magnitude over a vector of ring elements:
/// the scheme's `‖·‖` (the paper writes `‖x` for the `ℓ` norm of the
/// coefficient vector and `‖π‖∞` for the same quantity on a preimage stack).
pub fn max_norm<R: CenteredRing, const D: usize>(elts: &[Elt<R, D>]) -> u64 {
    max_magnitude(&to_coeffs(elts))
}

/// Saturating `u128 → u64` for gate comparisons. A gate above `u64::MAX` is
/// above any measured norm, so saturating can only *accept* more, never reject
/// wrongly.
fn saturating_u64(v: u128) -> u64 {
    u64::try_from(v).unwrap_or(u64::MAX)
}

/// Why an SRS operation refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum SrsError {
    /// A vector had a length other than the one the SRS shape requires.
    WrongLength {
        /// Length supplied.
        got: usize,
        /// Length required.
        expected: usize,
    },
    /// An exponent fell outside the SRS window `Z(W) \ {0}`.
    ExponentOutOfRange {
        /// Exponent asked for.
        exponent: i32,
        /// Largest exponent the SRS covers.
        window: i32,
    },
    /// `PreVerify` aborted: the functional is outside the declared alphabet.
    FunctionalOutOfAlphabet {
        /// `‖f‖` as measured.
        norm: u64,
        /// The declared bound `α`.
        bound: u64,
    },
    /// A committed vector is outside the declared input alphabet.
    WitnessOutOfAlphabet {
        /// `‖x‖` as measured.
        norm: u64,
        /// The declared bound `α`.
        bound: u64,
    },
    /// `X^D + 1` does not split into linear factors mod `R::MODULUS`, so the
    /// set `T` of Definition 2.15 does not exist for this ring.
    NotSplitCompletely {
        /// Modulus examined.
        modulus: u64,
        /// Ring degree examined.
        degree: usize,
    },
    /// No invertible element was found within the attempt budget.
    NotAUnit,
    /// A dimension the scheme requires to be a power of two was not one.
    NotAPowerOfTwo(usize),
    /// The halved §5.1 check was asked of an SRS built with `a₁ ≠ a₀`.
    DistinctKeys,
    /// A dual commitment was asked of an SRS whose §4.1 inner-product window
    /// was never built.
    MissingDualWindow,
}

impl fmt::Display for SrsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SrsError::WrongLength { got, expected } => {
                write!(f, "vector of {got} elements against {expected}")
            }
            SrsError::ExponentOutOfRange { exponent, window } => {
                write!(f, "exponent {exponent} outside the SRS window ±{window}")
            }
            SrsError::FunctionalOutOfAlphabet { norm, bound } => {
                write!(f, "PreVerify aborts: ‖f‖ = {norm} exceeds α = {bound}")
            }
            SrsError::WitnessOutOfAlphabet { norm, bound } => {
                write!(f, "‖x‖ = {norm} exceeds the declared alphabet α = {bound}")
            }
            SrsError::NotSplitCompletely { modulus, degree } => write!(
                f,
                "X^{degree} + 1 does not split completely mod {modulus}, so T (Def 2.15) is unavailable"
            ),
            SrsError::NotAUnit => write!(f, "no unit of R_q found"),
            SrsError::NotAPowerOfTwo(n) => write!(f, "{n} is not a power of two"),
            SrsError::DistinctKeys => {
                write!(f, "the combined check needs a₁ = a₀ (see §5.1)")
            }
            SrsError::MissingDualWindow => {
                write!(f, "the SRS has no v^(-i)·t knowledge window (see §4.1's IPA)")
            }
        }
    }
}

/// One condition of the verification boxes, reported as a **set**.
///
/// Every check here evaluates all of its conditions and returns the ones that
/// failed, so a rejection can be attributed to the equations a tamper really
/// violates instead of to the first one it happened to reach.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Condition {
    /// `‖y‖∞ ≤ δ_M` (Verify's first line).
    ValueNorm,
    /// `‖π₁‖∞ ≤ δ₁` (Verify's first line).
    KnowledgeNorm,
    /// `‖π₀∞ ≤ δ₀` (Verify's first line).
    OpeningNorm,
    /// `⟨a₁, π₁⟩ ≡ c·t mod q` (Verify's second line).
    KnowledgeEquation,
    /// `⟨a₀, π₀⟩ ≡ vk_f·c − y mod q` (Verify's third line).
    OpeningEquation,
    /// The Setup invariant `⟨a₀, u_{0,i}⟩ = vⁱ ∧ ⟨a₁, u_{1,i}⟩ = vⁱ·t`.
    SrsPreimages,
    /// §4.1 aggregation: `⟨a₀, Σᵢhπ₀ᵢ⟩  Σᵢ h(vkᵢc − yᵢ) mod q`.
    AggregatedOpeningEquation,
    /// §4.1 inner-product argument: `⟨a₀, π₀⟩ ≡ c'·c − y mod q`.
    InnerProductEquation,
    /// §5.1's halved check `⟨a, vk_f·π₁ − t·π₀⟩ ≡ y·t mod q`.
    CombinedEquation,
}

impl fmt::Display for Condition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let name: &str = match self {
            Condition::ValueNorm => "‖y‖ ≤ δ_M",
            Condition::KnowledgeNorm => "‖π₁ ≤ δ₁",
            Condition::OpeningNorm => "‖π₀‖ ≤ δ₀",
            Condition::KnowledgeEquation => "⟨a₁,π₁⟩ = c·t",
            Condition::OpeningEquation => "⟨a₀,π₀⟩ = vk_f·c − y",
            Condition::SrsPreimages => "⟨a,u⟩ = vⁱ (SRS window)",
            Condition::AggregatedOpeningEquation => "⟨a₀,Σhπ₀⟩ = Σh(vk·c − y)",
            Condition::InnerProductEquation => "⟨a₀,π₀⟩ = c'·c − y",
            Condition::CombinedEquation => "⟨a,vk·π₁ − t·π₀⟩ = y·t",
        };
        f.write_str(name)
    }
}

/// A verification rejection: the conditions that did not hold.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rejection(pub Vec<Condition>);

impl fmt::Display for Rejection {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let names: Vec<String> = self.0.iter().map(ToString::to_string).collect();
        write!(f, "rejected: {}", names.join(", "))
    }
}

// ---------------------------------------------------------------------------
// §2.3  TrapGen / SampPre
// ---------------------------------------------------------------------------

/// A trapdoor R-SIS key `a = [â ‖ g − â·R] ∈ R_q^{2k}` with gadget vector
/// `g = (1, B, …, B^{k−1})` (§2.3, in the [MP12] form §5.1 names).
///
/// `k = DIGITS` is forced by the requirement that the base-`BASE` digit
/// decomposition be exact (`BASE^k > q`), so `a` holds `ℓ = 2·DIGITS` ring
/// elements — the paper's `ℓ = 2` choice in its `ℓ = log_b q⌉` notation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Trapdoor<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> {
    /// `â`: `DIGITS` uniform ring elements.
    a_hat: Vec<Elt<R, D>>,
    /// `R`: the trapdoor, `DIGITS × DIGITS` row-major, entries with coefficients
    /// in `[-rho, rho]`.
    trap: Vec<Elt<R, D>>,
    /// The public vector `a = [â ‖ g − â·R]`.
    a: Vec<Elt<R, D>>,
    /// Coefficient bound of the trapdoor entries.
    rho: u32,
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> Trapdoor<R, D, BASE, DIGITS> {
    /// `TrapGen(1^ℓ, q, R, β)`: expands the key from a seed.
    ///
    /// `rho` bounds the trapdoor entries; the preimage norm bound that yields
    /// is [`Self::preimage_norm_bound`].
    pub fn trap_gen(seed: &[u8; 32], label: &[u8], rho: u32) -> Self {
        let a_hat = uniform_vec_from_seed::<R, D>(label, seed, DIGITS);
        let mut xof = seed_stream::<Shake256Xof>(TRAP_DOMAIN, seed);
        xof.absorb(label);
        let mut stream = BitStream::new(&mut xof);
        let trap: Vec<Elt<R, D>> = (0..DIGITS * DIGITS)
            .map(|_| centered_bounded_poly::<R, _, D>(&mut stream, rho))
            .collect();
        let a = Self::expand_public(&a_hat, &trap);
        Self {
            a_hat,
            trap,
            a,
            rho,
        }
    }

    /// `a = [â ‖ g − â·R]`, with `g` built by repeated multiplication by the
    /// base so that no `BASE^DIGITS` value ever has to fit an integer.
    fn expand_public(a_hat: &[Elt<R, D>], trap: &[Elt<R, D>]) -> Vec<Elt<R, D>> {
        let mat = BlockMat::new(DIGITS, DIGITS, trap.to_vec()).expect("square by construction");
        // (â·R)_j = Σᵢ âᵢ·R_{i,j}: contract the trapdoor's *rows* against â.
        let a_r = mat
            .contract_rows(a_hat)
            .expect("â has DIGITS entries by construction");
        let base = const_elt::<R, D>(R::from(BASE));
        let mut gadget = const_elt::<R, D>(R::ONE);
        let mut right = Vec::with_capacity(DIGITS);
        for entry in a_r {
            right.push(gadget.clone() - entry);
            gadget *= base.clone();
        }
        let mut a = Vec::with_capacity(2 * DIGITS);
        a.extend_from_slice(a_hat);
        a.extend(right);
        a
    }

    /// The public R-SIS vector `a` (`2·DIGITS` ring elements).
    pub fn public_vector(&self) -> &[Elt<R, D>] {
        &self.a
    }

    /// `ℓ`, the number of ring elements in `a`.
    pub const fn ell(&self) -> usize {
        2 * DIGITS
    }

    /// The preimage norm bound this key achieves: `ρ + k·ρ·γ_R·⌊B/2⌋`, from
    /// `u = (w + R·e, e)` with `‖w‖ ≤ ρ`, `‖e‖ ≤ ⌊B/2⌋`, and `γ_R` the ring
    /// expansion factor (Definition 2.1; `γ_R ≤ D` for power-of-two cyclotomics
    /// by Theorem 2.2).
    pub fn preimage_norm_bound(&self, gamma_r: u64) -> u64 {
        let rho = u64::from(self.rho);
        let digits = u64::try_from(DIGITS).expect("DIGITS fits u64");
        let digit = digit_half_width(BASE).max(1);
        rho + digits * rho * gamma_r * digit
    }

    /// `SampPre(td, y, β)`: a short `u` with `⟨a, u⟩ ≡ y mod q`.
    ///
    /// `w ←$ [-ρ,ρ]^k` is the randomizer, `e` the exact digit decomposition of
    /// `y − ⟨â, w⟩`, and `u = (w + R·e, e)`.
    pub fn samp_pre(&self, target: &Elt<R, D>, seed: &[u8; 32], tag: u64) -> Vec<Elt<R, D>> {
        let mut xof = seed_stream::<Shake256Xof>(PREIMAGE_DOMAIN, seed);
        xof.absorb(&tag.to_le_bytes());
        let mut stream = BitStream::new(&mut xof);
        let w: Vec<Elt<R, D>> = (0..DIGITS)
            .map(|_| centered_bounded_poly::<R, _, D>(&mut stream, self.rho))
            .collect();
        let mut residual = target.clone();
        for (a_i, w_i) in self.a_hat.iter().zip(w.iter()) {
            residual -= a_i.clone() * w_i.clone();
        }
        let e = split::<R, D, BASE, DIGITS>(&[residual]);
        let mat = BlockMat::new(DIGITS, DIGITS, self.trap.clone()).expect("square by construction");
        let r_e = mat
            .contract_cols(&e)
            .expect("e has DIGITS entries by construction");
        let u_top: Vec<Elt<R, D>> = w.into_iter().zip(r_e).map(|(x, y)| x + y).collect();
        let mut u = Vec::with_capacity(2 * DIGITS);
        u.extend(u_top);
        u.extend(e);
        u
    }
}

// ---------------------------------------------------------------------------
// units of R_q, and the set T
// ---------------------------------------------------------------------------

/// Inverts an element of `R_q = Z_R[X]/(X^D + 1)` by Gauss–Jordan on the
/// `D × D` matrix of "multiply by `x`", solving `x·u = 1`.
///
/// `None` means `x` is a **zero divisor** (in particular `x = 0`). Over the
/// prime field this is the "is `x` a unit" test, and it is what makes the
/// paper's `v ←$ R×_q` requirement and `t`'s non-invertibility checkable rather
/// than assumed.
pub fn ring_inverse<R: Field, const D: usize>(x: &Elt<R, D>) -> Option<Elt<R, D>> {
    // Column `c` of the multiplication matrix is the coefficient vector of
    // `x·X^c`, so `M·u = e₀` reads `Σ_c u_c·[x·X^c]_r = [r = 0]` for every
    // coefficient position `r` — i.e. `x·U = 1`. Writing those vectors into
    // *rows* instead solves the transposed system, which agrees on which
    // elements are invertible but returns the wrong element whenever the matrix
    // is not symmetric: `ring_inverse_agrees_with_multiplication` is what
    // catches that.
    let mut mat: Vec<Vec<R>> = vec![vec![R::ZERO; D]; D];
    let columns: Vec<Vec<R>> = (0..D)
        .map(|c| to_coeffs::<R, D>(&[x.clone() * monomial::<R, D>(c)]))
        .collect();
    for (c, col) in columns.into_iter().enumerate() {
        for (row, value) in mat.iter_mut().zip(col) {
            row[c] = value;
        }
    }
    for (i, row) in mat.iter_mut().enumerate() {
        row.push(if i == 0 { R::ONE } else { R::ZERO });
    }
    for col in 0..D {
        let pivot = (col..D).find(|&r| mat[r][col] != R::ZERO)?;
        mat.swap(col, pivot);
        let inv = mat[col][col].inverse()?;
        for v in mat[col].iter_mut() {
            *v *= inv;
        }
        let pivot_row = mat[col].clone();
        for (r, row) in mat.iter_mut().enumerate() {
            if r == col || row[col] == R::ZERO {
                continue;
            }
            let factor = row[col];
            for (dst, pv) in row.iter_mut().zip(pivot_row.iter()) {
                *dst -= factor * *pv;
            }
        }
    }
    Some(PolyRing::from_coefficients(
        mat.iter().map(|row| row[D]).collect(),
    ))
}

/// Draws `v ←$ R×_q` with its inverse (§4's first `Setup` line, and Theorem 2.3's
/// guarantee that a uniform `v` is invertible with overwhelming probability once
/// `q` is large).
pub fn sample_unit<R: Ring + Field, const D: usize>(
    seed: &[u8; 32],
    label: &[u8],
    attempts: usize,
) -> Result<(Elt<R, D>, Elt<R, D>), SrsError> {
    for attempt in 0..attempts {
        let mut xof = seed_stream::<Shake256Xof>(UNIT_DOMAIN, seed);
        xof.absorb(label);
        xof.absorb(&(attempt as u64).to_le_bytes());
        let v = uniform_poly::<R, _, D>(&mut BitStream::new(&mut xof));
        if let Some(inv) = ring_inverse::<R, D>(&v) {
            return Ok((v, inv));
        }
    }
    Err(SrsError::NotAUnit)
}

/// The `D` roots of `X^D + 1` in `Z_R`, as `ω^{2k+1}` for a primitive `2D`-th
/// root `ω`.
///
/// These exist exactly when `X^D + 1` splits into linear factors, i.e. when
/// `R::MODULUS ≡ 1 (mod 2D)` — so [`vanishing_element`] is only defined then.
pub fn roots_of_negacyclic<R: Ring + Field, const D: usize>() -> Result<Vec<R>, SrsError> {
    let splitting = x_pow_d_plus_1_splitting(R::MODULUS, D as u64);
    if !splitting.is_some_and(|s| s.is_split_completely()) {
        return Err(SrsError::NotSplitCompletely {
            modulus: R::MODULUS,
            degree: D,
        });
    }
    let omega = find_primitive_root::<R>(2 * D);
    Ok((0..D).map(|k| omega.pow(2 * k as u64 + 1)).collect())
}

/// `t ←$ T` from Definition 2.15, in the coefficient domain: with the roots
/// `r₀…r_{D−1}` of `X^D + 1`, `t = ∏_{r∈S}(r − X)` for a half-size set `S`.
///
/// Then `t` vanishes on `S`, so exactly half of its evaluations (the paper's
/// "half the elements in the NTT representation") are zero and `|⟨t⟩| = q^{D/2}`
/// — restriction 1. Any `s' ≠ 0` with `s't ≡ 0` must vanish on the *other* half,
/// i.e. be a multiple of `∏_{r∉S}(X − r)`, which is what makes restriction 2 a
/// lattice problem rather than a `±1` trick. The support is returned so a caller
/// can form that annihilator.
pub fn vanishing_element_with_support<R: Ring + Field, const D: usize>(
    seed: &[u8; 32],
) -> Result<(Elt<R, D>, Vec<usize>), SrsError> {
    let roots = roots_of_negacyclic::<R, D>()?;
    let mut xof = seed_stream::<Shake256Xof>(T_DOMAIN, seed);
    // Exactly `D/2` of the `D` roots, uniformly: `fixed_weight_signs` is the
    // crate's fixed-Hamming-weight draw.
    let signs = fixed_weight_signs(&mut BitStream::new(&mut xof), (D / 2) as u32, D);
    let support: Vec<usize> = signs
        .iter()
        .enumerate()
        .filter(|(_, &s)| s != 0)
        .map(|(k, _)| k)
        .collect();
    let x = monomial::<R, D>(1);
    let mut t = const_elt::<R, D>(R::ONE);
    for &k in &support {
        t *= const_elt(roots[k]) - x.clone();
    }
    Ok((t, support))
}

/// [`vanishing_element_with_support`] without the support.
pub fn vanishing_element<R: Ring + Field, const D: usize>(
    seed: &[u8; 32],
) -> Result<Elt<R, D>, SrsError> {
    vanishing_element_with_support::<R, D>(seed).map(|(t, _)| t)
}

// ---------------------------------------------------------------------------
// Table 1 / Theorem 4.1: norm bounds
// ---------------------------------------------------------------------------

/// The scheme's derived norm gates (Table 1 and Theorem 4.1).
///
/// The gates are `u128`: `δ₀ = w²·α_x·α_f·β₀·γ_R²` overflows `u64` for exactly
/// the large instances the paper's size tables target.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NormBounds {
    /// Committed dimension `w`.
    pub w: u64,
    /// Alphabet bound on the witness entries.
    pub alpha_x: u64,
    /// Alphabet bound on the functional entries — `α` in the paper, where one
    /// bound covers both; §4.3's power tables need a larger one.
    pub alpha_f: u64,
    /// Preimage norm bound of the opening window (`β₀`).
    pub beta0: u64,
    /// Preimage norm bound of the knowledge window (`β₁`).
    pub beta1: u64,
    /// Ring expansion factor `γ_R` (Theorem 2.2: `≤ D`).
    pub gamma_r: u64,
    /// `δ_M = w·α_x·α_f·γ_R` — the bound on `y = ⟨f, x⟩`.
    pub delta_m: u128,
    /// `δ₁ = w·α_x·β₁·γ_R` — the bound on `π₁`.
    pub delta_1: u128,
    /// `δ₀ = w²·α_x·α_f·β₀·γ_R²` — the bound on `π₀`.
    pub delta_0: u128,
    /// `β*₀ = 2·w²·α_x·δ₁·β₀·γ_R²` — the norm for which R-SIS must stay hard to
    /// make the scheme `X*`-extractable (Theorem 4.2, at the extraction stretch
    /// `α* = δ₁`).
    pub beta_star_0: u128,
}

impl NormBounds {
    /// Table 1's formulas, evaluated in `u128`.
    ///
    /// `None` when a product exceeds `u128`: that parameter set is outside what
    /// this accounting can express, and saturating silently would turn a gate
    /// into a no-op.
    #[must_use]
    pub fn derive(
        w: u64,
        alpha_x: u64,
        alpha_f: u64,
        beta0: u64,
        beta1: u64,
        gamma_r: u64,
    ) -> Option<Self> {
        let w128 = u128::from(w);
        let ax = u128::from(alpha_x);
        let af = u128::from(alpha_f);
        let b0 = u128::from(beta0);
        let b1 = u128::from(beta1);
        let g = u128::from(gamma_r);
        let delta_m = (w128 * ax).checked_mul(af)?.checked_mul(g)?;
        let delta_1 = (w128 * ax).checked_mul(b1)?.checked_mul(g)?;
        let delta_0 = (w128 * w128 * ax)
            .checked_mul(af)?
            .checked_mul(b0)?
            .checked_mul(g * g)?;
        let beta_star_0 = (2u128 * w128 * w128 * ax)
            .checked_mul(delta_1)?
            .checked_mul(b0)?
            .checked_mul(g * g)?;
        Some(Self {
            w,
            alpha_x,
            alpha_f,
            beta0,
            beta1,
            gamma_r,
            delta_m,
            delta_1,
            delta_0,
            beta_star_0,
        })
    }

    /// §4.1's inner-product variant: the functional *is* another committed
    /// vector, so its norm bound is the extracted stretch `δ₁` rather than `α`.
    /// This bound's `beta_star_0` is the paper's
    /// `β*₀ = w²(α*)²β₀γ_R² = w⁴α²β₁²β₀γ_R⁴`.
    #[must_use]
    pub fn inner_product_variant(&self) -> Option<Self> {
        let stretch = u64::try_from(self.delta_1).ok()?;
        Self::derive(
            self.w,
            stretch,
            stretch,
            self.beta0,
            self.beta1,
            self.gamma_r,
        )
    }

    /// §4.1's aggregate gate on `Σᵢ hᵢπ₀ᵢ`: each challenge contributes its
    /// operator norm (`c` for a `c`-sparse `±1` set, Lemma 2.5) times its
    /// summand's own `δ₀`.
    #[must_use]
    pub fn aggregated_opening_bound(&self, count: usize, op_norm: u64) -> Option<u128> {
        let terms = u128::from(count as u64).checked_mul(u128::from(op_norm))?;
        self.delta_0.checked_mul(terms)
    }

    /// Whether every gate sits below `q/2`. Above that a check stops
    /// constraining anything: a coefficient can be shifted by `q` to hide any
    /// value, so the norm gate becomes decorative.
    #[must_use]
    pub fn gates_below_half_modulus(&self, modulus: u64) -> bool {
        let half = u128::from(modulus / 2);
        self.delta_m < half && self.delta_1 < half && self.delta_0 < half
    }
}

// ---------------------------------------------------------------------------
// §4  Setup / Com / Open / PreVerify / Verify
// ---------------------------------------------------------------------------

/// The structured universal SRS
/// `ck = (a₀, [u_{0,i}]_{i∈P}, a₁, t, [u_{1,i}]_{i∈[W]}, v)`.
///
/// `W` is the *maximum* dimension: the same `ck` serves every `w ≤ W` (§4.1
/// "Universal SRS"), which is what makes it universal rather than per-size.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PowersSrs<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> {
    a0: Vec<Elt<R, D>>,
    a1: Vec<Elt<R, D>>,
    v: Elt<R, D>,
    v_inv: Elt<R, D>,
    t: Elt<R, D>,
    w_max: usize,
    openings: Vec<Vec<Elt<R, D>>>,
    knowledge: Vec<Vec<Elt<R, D>>>,
    /// §4.1's inner-product extension: preimages of `v^{-i}·t`. Empty unless
    /// [`SetupTrapdoor::extend_for_inner_product`] ran.
    dual: Vec<Vec<Elt<R, D>>>,
    beta0: u64,
    beta1: u64,
}

/// The structured universal SRS as *data*: the CRS a verifier holds, before it
/// is validated. [`PowersSrs::from_parts`] checks it; a corrupted CRS is
/// modelled by editing these fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CrsParts<R: Ring, const D: usize> {
    /// `a₀`: the R-SIS vector the opening preimages are taken against.
    pub open_key: Vec<Elt<R, D>>,
    /// `a₁`: the R-SIS vector the knowledge preimages are taken against.
    pub know_key: Vec<Elt<R, D>>,
    /// `v`: the structured generator, required to lie in `R×_q`.
    pub v: Elt<R, D>,
    /// `t`: the knowledge assumption's element of `T`.
    pub t: Elt<R, D>,
    /// `[u_{0,i}]_{i∈Z(W)\{0}}`, ascending in `i`.
    pub openings: Vec<Vec<Elt<R, D>>>,
    /// `[u_{1,i}]_{i∈[W]}`.
    pub knowledge: Vec<Vec<Elt<R, D>>>,
    /// `[u_{1,-i}]_{i∈[W]}`, the §4.1 inner-product extension; empty when the
    /// setup did not run it.
    pub dual_knowledge: Vec<Vec<Elt<R, D>>>,
    /// `β₀`: the claimed preimage norm bound of the opening window.
    pub beta0: u64,
    /// `β₁`: the claimed preimage norm bound of the knowledge window.
    pub beta1: u64,
}

/// The trapdoors `Setup` used — the toxic waste. Holding one lets its owner
/// `samp_pre` a preimage of any target and forge openings at will.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SetupTrapdoor<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> {
    open: Trapdoor<R, D, BASE, DIGITS>,
    know: Trapdoor<R, D, BASE, DIGITS>,
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>
    SetupTrapdoor<R, D, BASE, DIGITS>
{
    /// The trapdoor behind `a₀`: with it, `⟨a₀, ·⟩ = anything` is easy.
    pub fn open_trapdoor(&self) -> &Trapdoor<R, D, BASE, DIGITS> {
        &self.open
    }

    /// The trapdoor behind `a₁`.
    pub fn knowledge_trapdoor(&self) -> &Trapdoor<R, D, BASE, DIGITS> {
        &self.know
    }

    /// Builds §4.1's inner-product window into `srs`: preimages of `v^{-i}·t`
    /// for `i ∈ [W]`, under the same `a₁`.
    ///
    /// The extension is forced by how the paper's two IPA equations read
    /// together — "verifies both knowledge proofs as in Verify, and then checks
    /// the opening proof satisfies ⟨a, π₀⟩ ≡ c′ · c − y mod q". With `Com`
    /// committing at `vⁱ`, `Open(ck, x', x)` evaluates
    /// `(Σᵢ xvⁱ)(Σ x'ⱼv⁻ʲ)`, so the `c′` of that equation is the commitment of
    /// `x'` at the *negative* powers — and its knowledge proof then needs
    /// preimages of `v^{-i}·t`, which §4's `Setup` box never samples (it lists
    /// only `u_{1,i} ← SampPre(td₁, vⁱ·t) ∀i ∈ [w]`). Without this window the
    /// pair of printed equations is not simultaneously satisfiable.
    ///
    /// # Errors
    /// [`SrsError::WrongLength`] if an existing window has a different
    /// dimension.
    pub fn extend_for_inner_product(
        &self,
        srs: &mut PowersSrs<R, D, BASE, DIGITS>,
        seed: &[u8; 32],
    ) -> Result<(), SrsError> {
        if !srs.dual.is_empty() && srs.dual.len() != srs.knowledge.len() {
            return Err(SrsError::WrongLength {
                got: srs.dual.len(),
                expected: srs.knowledge.len(),
            });
        }
        srs.dual.clear();
        for i in 0..srs.w_max() {
            let target = srs.power_inv(i + 1) * srs.t().clone();
            srs.dual
                .push(self.know.samp_pre(&target, seed, 2u64 << 32 | i as u64));
        }
        Ok(())
    }
}

/// The exponent window `P = Z(W) \ {0}` as a slot index, ascending:
/// `-(W-1), …, -1, 1, …, W-1`.
fn opening_slot(w_max: usize, exponent: i32) -> Option<usize> {
    let lo = -(w_max as i32 - 1);
    let hi = w_max as i32 - 1;
    if exponent == 0 || exponent < lo || exponent > hi {
        return None;
    }
    let idx = exponent - lo;
    Some(if exponent > 0 {
        (idx - 1) as usize
    } else {
        idx as usize
    })
}

/// `Setup(1^λ, 1^W)` (§4): the trusted structured universal SRS.
///
/// `rho` bounds the trapdoor entries. `shared_a` implements §5.1's "fix a single
/// public R-SIS vector `a` with respect to which preimages for `vⁱ` and `vⁱt`
/// are generated" (`a₁ = a₀`, which halves the verifier's work and enables
/// [`failing_combined`]); `false` keeps the two independent keys the §4 box
/// writes.
///
/// Returns the public SRS and the trapdoor that must then be destroyed.
pub fn setup<R: Ring + Field, const D: usize, const BASE: u64, const DIGITS: usize>(
    seed: &[u8; 32],
    w_max: usize,
    rho: u32,
    shared_a: bool,
) -> Result<
    (
        PowersSrs<R, D, BASE, DIGITS>,
        SetupTrapdoor<R, D, BASE, DIGITS>,
    ),
    SrsError,
> {
    assert!(w_max >= 1, "the SRS must cover at least dimension 1");
    let (v, v_inv) = sample_unit::<R, D>(seed, b"v", 64)?;
    let t = vanishing_element::<R, D>(seed)?;
    let open = Trapdoor::<R, D, BASE, DIGITS>::trap_gen(seed, b"orbweaver-a0", rho);
    let know = if shared_a {
        open.clone()
    } else {
        Trapdoor::<R, D, BASE, DIGITS>::trap_gen(seed, b"orbweaver-a1", rho)
    };
    // γ_R ≤ D for power-of-two cyclotomics (Theorem 2.2): the ring this module
    // is written against is exactly `Z[X]/(X^D + 1)` with `D` a power of two.
    let gamma_r = u64::try_from(D).expect("D fits u64");
    // vⁱ for i ∈ [1, W] and v⁻ⁱ for i ∈ [1, W−1] by two multiplication chains.
    let mut powers_up = vec![v.clone()];
    for _ in 1..w_max {
        let next = powers_up[powers_up.len() - 1].clone() * v.clone();
        powers_up.push(next);
    }
    let mut powers_down = vec![v_inv.clone()];
    for _ in 1..w_max {
        let next = powers_down[powers_down.len() - 1].clone() * v_inv.clone();
        powers_down.push(next);
    }
    let mut openings = Vec::with_capacity(2 * w_max.saturating_sub(1));
    for (slot, exponent) in (-(w_max as i32 - 1)..=w_max as i32 - 1)
        .filter(|&k| k != 0)
        .enumerate()
    {
        let target = if exponent > 0 {
            powers_up[(exponent - 1) as usize].clone()
        } else {
            powers_down[(-exponent - 1) as usize].clone()
        };
        openings.push(open.samp_pre(&target, seed, u64::try_from(slot).expect("slot")));
    }
    let mut knowledge = Vec::with_capacity(w_max);
    for (i, power) in powers_up.iter().enumerate() {
        let target = power.clone() * t.clone();
        knowledge.push(know.samp_pre(&target, seed, 1u64 << 32 | i as u64));
    }
    let srs = PowersSrs {
        a0: open.public_vector().to_vec(),
        a1: know.public_vector().to_vec(),
        v,
        v_inv,
        t,
        w_max,
        openings,
        knowledge,
        dual: Vec::new(),
        beta0: open.preimage_norm_bound(gamma_r),
        beta1: know.preimage_norm_bound(gamma_r),
    };
    Ok((srs, SetupTrapdoor { open, know }))
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> PowersSrs<R, D, BASE, DIGITS> {
    /// `a₀`: the R-SIS vector the opening preimages are taken against.
    pub fn a0(&self) -> &[Elt<R, D>] {
        &self.a0
    }

    /// `a₁`: the R-SIS vector the knowledge preimages are taken against.
    pub fn a1(&self) -> &[Elt<R, D>] {
        &self.a1
    }

    /// Whether §5.1's single-key instantiation was used (`a₁ = a₀`).
    pub fn shares_a(&self) -> bool {
        self.a0 == self.a1
    }

    /// The structured generator `v ∈ R×_q`.
    pub fn v(&self) -> &Elt<R, D> {
        &self.v
    }

    /// `v⁻¹ mod q`, which `PreVerify` needs for `vk_f = Σᵢ fv⁻ⁱ`.
    pub fn v_inv(&self) -> &Elt<R, D> {
        &self.v_inv
    }

    /// `t ←$ T`, the knowledge assumption's group element.
    pub fn t(&self) -> &Elt<R, D> {
        &self.t
    }

    /// The maximum supported dimension `W`.
    pub const fn w_max(&self) -> usize {
        self.w_max
    }

    /// `β₀` (Table 1): the norm bound the opening preimages are sampled under.
    pub const fn opening_norm_bound(&self) -> u64 {
        self.beta0
    }

    /// `β₁` (Table 1): the norm bound the knowledge preimages are sampled under.
    pub const fn knowledge_norm_bound(&self) -> u64 {
        self.beta1
    }

    /// The CRS as plain data (see [`CrsParts`]).
    #[must_use]
    pub fn to_parts(&self) -> CrsParts<R, D> {
        CrsParts {
            open_key: self.a0.clone(),
            know_key: self.a1.clone(),
            v: self.v.clone(),
            t: self.t.clone(),
            openings: self.openings.clone(),
            knowledge: self.knowledge.clone(),
            dual_knowledge: self.dual.clone(),
            beta0: self.beta0,
            beta1: self.beta1,
        }
    }

    /// Rebuilds an SRS from [`CrsParts`], checking the two structural
    /// requirements `Setup` imposes: `v ∈ R×_q` (§4's first line) and a
    /// well-shaped window (`|P| = 2W − 2` stacks of `ℓ` entries each).
    ///
    /// A verifier that downloaded the CRS, and a test modelling a corrupted
    /// one, both come through here.
    ///
    /// # Errors
    /// [`SrsError::NotAUnit`] if `v` is a zero divisor, and
    /// [`SrsError::WrongLength`] if the window is ragged.
    pub fn from_parts(parts: CrsParts<R, D>) -> Result<Self, SrsError>
    where
        R: Field,
    {
        let CrsParts {
            open_key,
            know_key,
            v,
            t,
            openings,
            knowledge,
            dual_knowledge,
            beta0,
            beta1,
        } = parts;
        let v_inv = ring_inverse::<R, D>(&v).ok_or(SrsError::NotAUnit)?;
        let w_max = knowledge.len();
        if w_max == 0 {
            return Err(SrsError::WrongLength {
                got: 0,
                expected: 1,
            });
        }
        // |P| = 2(W − 1): the exponents −(W−1), …, −1, 1, …, W−1.
        if openings.len() != 2 * w_max.saturating_sub(1) {
            return Err(SrsError::WrongLength {
                got: openings.len(),
                expected: 2 * w_max.saturating_sub(1),
            });
        }
        for stack in openings
            .iter()
            .chain(knowledge.iter())
            .chain(dual_knowledge.iter())
        {
            if stack.len() != open_key.len() || stack.len() != know_key.len() {
                return Err(SrsError::WrongLength {
                    got: stack.len(),
                    expected: open_key.len(),
                });
            }
        }
        Ok(Self {
            a0: open_key,
            a1: know_key,
            v,
            v_inv,
            t,
            w_max,
            openings,
            knowledge,
            dual: dual_knowledge,
            beta0,
            beta1,
        })
    }

    /// `u_{0,i}`, the short preimage of `vⁱ` for `i ∈ Z(W) \ {0}`.
    pub fn opening_preimage(&self, exponent: i32) -> Option<&[Elt<R, D>]> {
        opening_slot(self.w_max, exponent)
            .and_then(|slot| self.openings.get(slot))
            .map(Vec::as_slice)
    }

    /// `u_{1,i}`, the short preimage of `vⁱ·t` for `i ∈ [W]` (1-based).
    pub fn knowledge_preimage(&self, index: usize) -> Option<&[Elt<R, D>]> {
        if index == 0 {
            return None;
        }
        self.knowledge.get(index - 1).map(Vec::as_slice)
    }

    /// Whether §4.1's inner-product window is present.
    pub fn has_dual_window(&self) -> bool {
        !self.dual.is_empty()
    }

    /// `u_{1,-i}`, the short preimage of `v^{-i}·t` (§4.1's IPA window).
    pub fn dual_knowledge_preimage(&self, index: usize) -> Option<&[Elt<R, D>]> {
        if index == 0 {
            return None;
        }
        self.dual.get(index - 1).map(Vec::as_slice)
    }

    /// The exponents `P = Z(W) \ {0}` the opening window covers, ascending.
    pub fn exponents(&self) -> Vec<i32> {
        (-(self.w_max as i32 - 1)..=self.w_max as i32 - 1)
            .filter(|&k| k != 0)
            .collect()
    }

    /// The CRS size in ring elements: the `(2W − 2) + W = 3W − 2` preimage
    /// vectors plus the two public vectors, i.e. `3W·ℓ` — §5.2.1's "the
    /// Orbweaver CRS size is calculated as `3wℓn log β` bits, as it consists of
    /// `3w` vectors of ring elements".
    pub fn crs_ring_elements(&self) -> usize {
        (self.openings.len() + self.knowledge.len() + self.dual.len() + 2) * self.a0.len()
    }

    /// `v^k` for `k ≥ 1` by repeated multiplication.
    fn power(&self, k: usize) -> Elt<R, D> {
        let mut acc = self.v.clone();
        for _ in 1..k {
            acc *= self.v.clone();
        }
        acc
    }

    /// `v^{-k}` for `k ≥ 1`.
    fn power_inv(&self, k: usize) -> Elt<R, D> {
        let mut acc = self.v_inv.clone();
        for _ in 1..k {
            acc *= self.v_inv.clone();
        }
        acc
    }

    /// `Setup`'s invariant, read from the public side: every stored preimage
    /// maps to the power it claims. A *structured* SRS is only correct if this
    /// holds, and it is the equation a tampered window entry trips.
    #[must_use]
    pub fn failing_setup_invariant(&self) -> Vec<Condition> {
        let mut bad = Vec::new();
        for exponent in self.exponents() {
            let target = if exponent > 0 {
                self.power(exponent as usize)
            } else {
                self.power_inv((-exponent) as usize)
            };
            let ok = match self.opening_preimage(exponent) {
                Some(u) => pairing(&self.a0, u).is_ok_and(|got| got == target),
                None => false,
            };
            if !ok {
                bad.push(Condition::SrsPreimages);
            }
        }
        for (i, u) in self.knowledge.iter().enumerate() {
            let target = self.power(i + 1) * self.t.clone();
            if !pairing(&self.a1, u).is_ok_and(|got| got == target) {
                bad.push(Condition::SrsPreimages);
            }
        }
        for (i, u) in self.dual.iter().enumerate() {
            let target = self.power_inv(i + 1) * self.t.clone();
            if !pairing(&self.a1, u).is_ok_and(|got| got == target) {
                bad.push(Condition::SrsPreimages);
            }
        }
        bad
    }

    /// Whether [`Self::failing_setup_invariant`] is empty.
    #[must_use]
    pub fn well_formed(&self) -> bool {
        self.failing_setup_invariant().is_empty()
    }
}

/// The R-SIS pairing `⟨a, u⟩ = Σᵢ auᵢ` over `R_q` — the left side of both
/// verification equations, and of every derived check.
///
/// # Errors
/// [`SrsError::WrongLength`] unless the two vectors agree in length.
pub fn pairing<R: Ring, const D: usize>(
    a: &[Elt<R, D>],
    u: &[Elt<R, D>],
) -> Result<Elt<R, D>, SrsError> {
    if a.len() != u.len() {
        return Err(SrsError::WrongLength {
            got: u.len(),
            expected: a.len(),
        });
    }
    Ok(ring_dot(a, u))
}

/// `Com(ck, x) → (c, π₁)` (§4): the commitment and the knowledge proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Commitment<R: Ring, const D: usize> {
    /// `c = Σᵢ₁^w xvⁱ mod q`.
    pub c: Elt<R, D>,
    /// `π₁ = Σᵢ₌₁^w xᵢ·u_{1,i} mod q`.
    pub pi1: Vec<Elt<R, D>>,
}

/// `Open(ck, f, x) → π₀` (§4): the opening proof of a linear-functional claim.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Opening<R: Ring, const D: usize> {
    /// `π₀ = Σ_{i∈P} aᵢ·u_{0,i} mod q`.
    pub pi0: Vec<Elt<R, D>>,
}

/// `Com`: commits to `x ∈ X^w`.
///
/// `x` must lie in the declared alphabet (Definition 2.7's precondition;
/// [`check_alphabet`] is the guard). `Verify` does not re-check `x` because the
/// paper's `Verify` does not — extractability bounds the *extracted* witness
/// instead, at the stretch `α* = δ₁`.
///
/// # Errors
/// [`SrsError::WrongLength`] if `x` is empty or longer than `W`, or
/// [`SrsError::ExponentOutOfRange`] from the window lookup.
pub fn commit<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    x: &[Elt<R, D>],
) -> Result<Commitment<R, D>, SrsError> {
    if x.is_empty() || x.len() > srs.w_max() {
        return Err(SrsError::WrongLength {
            got: x.len(),
            expected: srs.w_max(),
        });
    }
    let mut c = zero_elt::<R, D>();
    let mut pi1 = vec![zero_elt::<R, D>(); srs.a1.len()];
    for (i, xi) in x.iter().enumerate() {
        c += srs.power(i + 1) * xi.clone();
        let u = srs
            .knowledge_preimage(i + 1)
            .ok_or(SrsError::ExponentOutOfRange {
                exponent: i as i32 + 1,
                window: srs.w_max() as i32,
            })?;
        if u.len() != pi1.len() {
            return Err(SrsError::WrongLength {
                got: u.len(),
                expected: pi1.len(),
            });
        }
        for (acc, uk) in pi1.iter_mut().zip(u.iter()) {
            *acc += xi.clone() * uk.clone();
        }
    }
    Ok(Commitment { c, pi1 })
}

/// The Laurent polynomial `x(v)·f(v) = (Σᵢ xᵢvⁱ)(Σⱼ fⱼv⁻ʲ) = Σₖ aₖvᵏ` that §4's
/// `Open` reads its coefficients from.
///
/// Slot `k + (w − 1)` holds `a_k`, so the window is `[−(w−1), w−1]` and
/// `a₀ = ⟨f, x⟩` is exactly the claimed value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LaurentPoly<R: Ring, const D: usize> {
    offset: i32,
    coeffs: Vec<Elt<R, D>>,
}

impl<R: Ring, const D: usize> LaurentPoly<R, D> {
    /// The `2w − 1` coefficients `a_{-w+1}, …, a_{w-1}`, `a_k = Σ_{i−j=k} xᵢfⱼ`.
    ///
    /// # Errors
    /// [`SrsError::WrongLength`] unless `x` and `f` are equally long and
    /// non-empty.
    pub fn product(x: &[Elt<R, D>], f: &[Elt<R, D>]) -> Result<Self, SrsError> {
        if x.len() != f.len() {
            return Err(SrsError::WrongLength {
                got: f.len(),
                expected: x.len(),
            });
        }
        if x.is_empty() {
            return Err(SrsError::WrongLength {
                got: 0,
                expected: 1,
            });
        }
        let w = x.len();
        let offset = (w - 1) as i32;
        let mut coeffs = vec![zero_elt::<R, D>(); 2 * w - 1];
        for (i, xi) in x.iter().enumerate() {
            for (j, fj) in f.iter().enumerate() {
                coeffs[offset as usize + i - j] += xi.clone() * fj.clone();
            }
        }
        Ok(Self { offset, coeffs })
    }

    /// `a_k`, or `None` outside the window.
    pub fn coefficient(&self, k: i32) -> Option<&Elt<R, D>> {
        let idx = k + self.offset;
        if idx < 0 || idx as usize >= self.coeffs.len() {
            return None;
        }
        Some(&self.coeffs[idx as usize])
    }

    /// `a₀ = ⟨f, x⟩` — the evaluation the opening is about.
    pub fn constant_term(&self) -> Elt<R, D> {
        self.coefficient(0)
            .cloned()
            .unwrap_or_else(zero_elt::<R, D>)
    }

    /// The dimension `w`, from the `2w − 1` stored coefficients.
    #[must_use]
    pub fn w(&self) -> usize {
        self.coeffs.len().div_ceil(2)
    }

    /// The window `P = Z(w) \ {0}`: every stored exponent except `0`, ascending.
    pub fn exponents(&self) -> Vec<i32> {
        (-self.offset..=self.offset).filter(|&k| k != 0).collect()
    }
}

/// The Laurent product `x(v)·f(v)` of §4's `Open` (see [`LaurentPoly`]).
///
/// # Errors
/// [`SrsError::WrongLength`] if `x` and `f` differ in length or are empty.
pub fn laurent_product<R: Ring, const D: usize>(
    x: &[Elt<R, D>],
    f: &[Elt<R, D>],
) -> Result<LaurentPoly<R, D>, SrsError> {
    LaurentPoly::product(x, f)
}

/// `Open`: the opening proof of `y = ⟨f, x⟩`.
///
/// # Errors
/// Propagates [`laurent_product`]'s, plus [`SrsError::WrongLength`] when
/// `w > W` and [`SrsError::ExponentOutOfRange`] from the window lookup.
pub fn open<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    f: &[Elt<R, D>],
    x: &[Elt<R, D>],
) -> Result<Opening<R, D>, SrsError> {
    let lp = laurent_product(x, f)?;
    if lp.w() > srs.w_max() {
        return Err(SrsError::WrongLength {
            got: lp.w(),
            expected: srs.w_max(),
        });
    }
    let mut pi0 = vec![zero_elt::<R, D>(); srs.a0.len()];
    for k in lp.exponents() {
        let u = srs
            .opening_preimage(k)
            .ok_or(SrsError::ExponentOutOfRange {
                exponent: k,
                window: srs.w_max() as i32 - 1,
            })?;
        if u.len() != pi0.len() {
            return Err(SrsError::WrongLength {
                got: u.len(),
                expected: pi0.len(),
            });
        }
        let ak = lp.coefficient(k).expect("in the window by construction");
        for (acc, uk) in pi0.iter_mut().zip(u.iter()) {
            *acc += ak.clone() * uk.clone();
        }
    }
    Ok(Opening { pi0 })
}

/// The functional key `Σᵢ fᵢv⁻ⁱ mod q` — the commitment to the linear functional
/// `f`, formed from public SRS data only.
///
/// # Errors
/// [`SrsError::WrongLength`] if `f` is empty or longer than `W`.
pub fn functional_key<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    f: &[Elt<R, D>],
) -> Result<Elt<R, D>, SrsError> {
    if f.is_empty() || f.len() > srs.w_max() {
        return Err(SrsError::WrongLength {
            got: f.len(),
            expected: srs.w_max(),
        });
    }
    let mut acc = zero_elt::<R, D>();
    let mut v_neg_i = srs.v_inv().clone();
    for fi in f {
        acc += fi.clone() * v_neg_i.clone();
        v_neg_i *= srs.v_inv().clone();
    }
    Ok(acc)
}

/// `PreVerify(ck, f) → vk_f` (§4): [`functional_key`] behind the box's abort
/// `if ‖f‖ > α`.
///
/// This is the structure-preserving step: the verifier forms a commitment to a
/// *new* linear functional in `w` ring multiplications, with no key entry beyond
/// `v`.
///
/// # Errors
/// [`SrsError::FunctionalOutOfAlphabet`] when `‖f‖ > α`, and
/// [`SrsError::WrongLength`] from [`functional_key`].
pub fn pre_verify<R: Ring + CenteredRing, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    f: &[Elt<R, D>],
    alpha_f: u64,
) -> Result<Elt<R, D>, SrsError> {
    check_alphabet(f, alpha_f, true)?;
    functional_key(srs, f)
}

/// The `O(log w)` univariate functional key (§4.3, and §1's "Polynomial
/// commitments for integers"): for the evaluation functional
/// `f = (1, z, …, z^{w−1})`,
///
/// ```text
/// Σ_{i=1..w} z^{i−1}·v^{-i}  =  v^{-w} · Π_{j=0}^{log₂ w − 1} (z^{2^j} + v^{2^j})
/// ```
///
/// so a verifier holding only the *point* `z` forms the key in `log w` ring
/// multiplications instead of `w`. Pinned against [`functional_key`] by
/// `power_key_matches_the_log_time_product`.
///
/// # Errors
/// [`SrsError::NotAPowerOfTwo`] if `w` is not a power of two, and
/// [`SrsError::WrongLength`] if `w > W`.
pub fn power_functional_key<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    z: &Elt<R, D>,
    w: usize,
) -> Result<Elt<R, D>, SrsError> {
    if !w.is_power_of_two() {
        return Err(SrsError::NotAPowerOfTwo(w));
    }
    if w > srs.w_max() {
        return Err(SrsError::WrongLength {
            got: w,
            expected: srs.w_max(),
        });
    }
    let mut product = const_elt::<R, D>(R::ONE);
    let mut z_pow = z.clone();
    let mut v_pow = srs.v().clone();
    for _ in 0..w.trailing_zeros() {
        product *= z_pow.clone() + v_pow.clone();
        z_pow = z_pow.clone() * z_pow;
        v_pow = v_pow.clone() * v_pow;
    }
    let mut v_inv_w = srs.v_inv().clone();
    for _ in 1..w {
        v_inv_w *= srs.v_inv().clone();
    }
    Ok(product * v_inv_w)
}

/// The weight vector of the multilinear evaluation at `point`:
/// `eq(b) = Πⱼ (bit ? zⱼ : 1 − zⱼ)`, in the order `i = Σⱼ bⱼ2ʲ + 1`.
///
/// This is the functional a multilinear PCS opens with, and the `y` side of
/// [`multilinear_functional_key`].
///
/// # Errors
/// [`SrsError::WrongLength`] if `2^ℓ > w_max`.
pub fn eq_tensor<R: Ring, const D: usize>(
    point: &[Elt<R, D>],
    w_max: usize,
) -> Result<Vec<Elt<R, D>>, SrsError> {
    let w = 1usize << point.len();
    if w > w_max {
        return Err(SrsError::WrongLength {
            got: w,
            expected: w_max,
        });
    }
    let one = const_elt::<R, D>(R::ONE);
    Ok((0..w)
        .map(|i| {
            let mut acc = one.clone();
            for (j, z) in point.iter().enumerate() {
                let factor = if (i >> j) & 1 == 1 {
                    z.clone()
                } else {
                    one.clone() - z.clone()
                };
                acc *= factor;
            }
            acc
        })
        .collect())
}

/// The `O(log w)` multilinear functional key — §4.3's "by replacing `z^{2i}`
/// with `zⁱ` for all `i` below we obtain the N-linear version":
///
/// ```text
/// Σ_{i=1..w} eq(z, i−1)·v^{-i}  =  v^{-1} · Πⱼ ((1 − zⱼ) + zⱼ·v^{-2^j})
/// ```
///
/// # Errors
/// Propagates [`eq_tensor`]'s.
pub fn multilinear_functional_key<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    point: &[Elt<R, D>],
) -> Result<Elt<R, D>, SrsError> {
    eq_tensor::<R, D>(point, srs.w_max())?;
    let one = const_elt::<R, D>(R::ONE);
    let mut product = one.clone();
    let mut v_neg_pow = srs.v_inv().clone();
    for z in point {
        product *= (one.clone() - z.clone()) + z.clone() * v_neg_pow.clone();
        v_neg_pow = v_neg_pow.clone() * v_neg_pow;
    }
    Ok(product * srs.v_inv())
}

/// Guards a vector against the declared alphabet bound `‖·‖ ≤ α`.
///
/// `functional` picks which variant is reported, so a caller cannot confuse
/// `PreVerify`'s abort with a bad witness.
///
/// # Errors
/// [`SrsError::FunctionalOutOfAlphabet`] or [`SrsError::WitnessOutOfAlphabet`].
pub fn check_alphabet<R: CenteredRing, const D: usize>(
    v: &[Elt<R, D>],
    alpha: u64,
    functional: bool,
) -> Result<(), SrsError> {
    let norm = max_norm(v);
    if norm > alpha {
        return Err(if functional {
            SrsError::FunctionalOutOfAlphabet { norm, bound: alpha }
        } else {
            SrsError::WitnessOutOfAlphabet { norm, bound: alpha }
        });
    }
    Ok(())
}

/// `Verify(vk_f, c, π₁, y, π₀)` (§4): all five conditions, none short-circuited.
///
/// Returns the conditions that **failed**; an empty vector is acceptance.
pub fn failing<R: Ring + CenteredRing, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    bounds: &NormBounds,
    vk_f: &Elt<R, D>,
    com: &Commitment<R, D>,
    y: &Elt<R, D>,
    opening: &Opening<R, D>,
) -> Vec<Condition> {
    let mut bad = Vec::new();
    if max_norm(core::slice::from_ref(y)) > saturating_u64(bounds.delta_m) {
        bad.push(Condition::ValueNorm);
    }
    if max_norm(&com.pi1) > saturating_u64(bounds.delta_1) {
        bad.push(Condition::KnowledgeNorm);
    }
    if max_norm(&opening.pi0) > saturating_u64(bounds.delta_0) {
        bad.push(Condition::OpeningNorm);
    }
    if !pairing(srs.a1(), &com.pi1).is_ok_and(|got| got == com.c.clone() * srs.t().clone()) {
        bad.push(Condition::KnowledgeEquation);
    }
    if !pairing(srs.a0(), &opening.pi0)
        .is_ok_and(|got| got == vk_f.clone() * com.c.clone() - y.clone())
    {
        bad.push(Condition::OpeningEquation);
    }
    bad
}

/// [`failing`] as an accept/reject decision.
///
/// # Errors
/// [`Rejection`] carries every condition that failed.
pub fn verify<R: Ring + CenteredRing, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    bounds: &NormBounds,
    vk_f: &Elt<R, D>,
    com: &Commitment<R, D>,
    y: &Elt<R, D>,
    opening: &Opening<R, D>,
) -> Result<(), Rejection> {
    let bad = failing(srs, bounds, vk_f, com, y, opening);
    if bad.is_empty() {
        Ok(())
    } else {
        Err(Rejection(bad))
    }
}

/// §5.1's halved verifier check, available when `Setup` fixed `a₁ = a₀`:
///
/// ```text
/// ⟨a, vk_f·π₁ − t·π₀⟩ ≡ y·t mod q
/// ```
///
/// — one pairing instead of two, "so the verifier runtime can be nearly halved".
/// It is implied by both §4 equations, and it implies their difference, so it is
/// the cheaper single test of the *same* relation.
///
/// # Errors
/// [`SrsError::DistinctKeys`] when the SRS was built with independent `a₀`, `a₁`
/// (the §4 box's shape), where this equation is not the scheme's check.
pub fn failing_combined<
    R: Ring + CenteredRing,
    const D: usize,
    const BASE: u64,
    const DIGITS: usize,
>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    bounds: &NormBounds,
    vk_f: &Elt<R, D>,
    com: &Commitment<R, D>,
    y: &Elt<R, D>,
    opening: &Opening<R, D>,
) -> Result<Vec<Condition>, SrsError> {
    if !srs.shares_a() {
        return Err(SrsError::DistinctKeys);
    }
    let mut bad = failing(srs, bounds, vk_f, com, y, opening);
    let folded: Vec<Elt<R, D>> = com
        .pi1
        .iter()
        .zip(opening.pi0.iter())
        .map(|(p1, p0)| vk_f.clone() * p1.clone() - srs.t().clone() * p0.clone())
        .collect();
    let ok = pairing(srs.a0(), &folded).is_ok_and(|got| got == y.clone() * srs.t().clone());
    if !ok {
        bad.push(Condition::CombinedEquation);
    }
    Ok(bad)
}

// ---------------------------------------------------------------------------
// §4.1  extensions
// ---------------------------------------------------------------------------

/// One `(commitment, functional key, claimed value, opening)` tuple for
/// [`aggregate`].
#[derive(Debug, Clone)]
pub struct Claim<'a, R: Ring, const D: usize> {
    /// `cᵢ`.
    pub commitment: &'a Elt<R, D>,
    /// `vk_{fᵢ}`.
    pub functional_key: &'a Elt<R, D>,
    /// `yᵢ`.
    pub value: &'a Elt<R, D>,
    /// `π₀ᵢ`.
    pub opening: &'a [Elt<R, D>],
}

/// §4.1 public proof aggregation: with short challenges `hᵢ`, `t` openings
/// collapse into `π₀ = Σᵢ hᵢπ₀ᵢ` against the folded right-hand side
/// `Σᵢ hᵢ(vkᵢc − yᵢ)`.
///
/// The aggregator holds no secret — this is the linear homomorphism of the
/// opening proofs, and it is exactly what the structured SRS buys: *derived*
/// linear-functional commitments from public data.
///
/// # Errors
/// [`SrsError::WrongLength`] unless there is one challenge per claim (at least
/// one) and every opening has `ℓ` entries.
pub fn aggregate<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    claims: &[Claim<'_, R, D>],
    challenges: &[Elt<R, D>],
) -> Result<(Elt<R, D>, Vec<Elt<R, D>>), SrsError> {
    if claims.is_empty() || claims.len() != challenges.len() {
        return Err(SrsError::WrongLength {
            got: challenges.len(),
            expected: claims.len(),
        });
    }
    let ell = srs.a0().len();
    let mut residual = zero_elt::<R, D>();
    let mut pi0 = vec![zero_elt::<R, D>(); ell];
    for (claim, h) in claims.iter().zip(challenges.iter()) {
        if claim.opening.len() != ell {
            return Err(SrsError::WrongLength {
                got: claim.opening.len(),
                expected: ell,
            });
        }
        residual += h.clone()
            * (claim.functional_key.clone() * claim.commitment.clone() - claim.value.clone());
        for (acc, uk) in pi0.iter_mut().zip(claim.opening.iter()) {
            *acc += h.clone() * uk.clone();
        }
    }
    Ok((residual, pi0))
}

/// The aggregated check: `⟨a₀, π₀⟩ ≡ residual`, plus the aggregate norm gate
/// `‖π₀‖ ≤ Σᵢ op(hᵢ)·δ₀` (Lemma 2.5 gives `op = c` for a `c`-sparse `±1`
/// challenge set).
///
/// # Errors
/// Propagates [`pairing`]'s.
pub fn failing_aggregated<
    R: Ring + CenteredRing,
    const D: usize,
    const BASE: u64,
    const DIGITS: usize,
>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    residual: &Elt<R, D>,
    pi0: &[Elt<R, D>],
    opening_bound: u128,
) -> Result<Vec<Condition>, SrsError> {
    let mut bad = Vec::new();
    if max_norm(pi0) > saturating_u64(opening_bound) {
        bad.push(Condition::OpeningNorm);
    }
    if pairing(srs.a0(), pi0)? != residual.clone() {
        bad.push(Condition::AggregatedOpeningEquation);
    }
    Ok(bad)
}

/// The dual commitment `c' = Σᵢ xv^{-i}` of §4.1's inner-product argument, with
/// its knowledge proof `π₁' = Σᵢ xᵢ·u_{1,-i}` against the window built by
/// [`SetupTrapdoor::extend_for_inner_product`], so `⟨a₁, π₁'⟩ ≡ c'·t mod q` holds
/// exactly as in `Verify`.
///
/// # Errors
/// [`SrsError::MissingDualWindow`] if the setup never ran the §4.1 extension;
/// otherwise those of [`commit`].
pub fn commit_dual<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    x: &[Elt<R, D>],
) -> Result<Commitment<R, D>, SrsError> {
    if !srs.has_dual_window() {
        return Err(SrsError::MissingDualWindow);
    }
    if x.is_empty() || x.len() > srs.w_max() {
        return Err(SrsError::WrongLength {
            got: x.len(),
            expected: srs.w_max(),
        });
    }
    let mut c = zero_elt::<R, D>();
    let mut pi1 = vec![zero_elt::<R, D>(); srs.a1.len()];
    for (i, xi) in x.iter().enumerate() {
        c += srs.power_inv(i + 1) * xi.clone();
        let u = srs
            .dual_knowledge_preimage(i + 1)
            .ok_or(SrsError::MissingDualWindow)?;
        if u.len() != pi1.len() {
            return Err(SrsError::WrongLength {
                got: u.len(),
                expected: pi1.len(),
            });
        }
        for (acc, uk) in pi1.iter_mut().zip(u.iter()) {
            *acc += xi.clone() * uk.clone();
        }
    }
    Ok(Commitment { c, pi1 })
}

/// §4.1's inner-product argument: `y = ⟨x, x'⟩` between two committed vectors,
/// proved by opening `x` with the *committed* functional `x'`. The verifier
/// checks both knowledge proofs, both norm gates, and
/// `⟨a₀, π₀⟩ ≡ c'·c − y mod q` — with `c'` the [`commit_dual`] commitment, the
/// only reading on which the paper's two printed equations hold at once.
///
/// # Errors
/// Propagates [`pairing`]'s.
pub fn failing_inner_product<
    R: Ring + CenteredRing,
    const D: usize,
    const BASE: u64,
    const DIGITS: usize,
>(
    srs: &PowersSrs<R, D, BASE, DIGITS>,
    bounds: &NormBounds,
    com: &Commitment<R, D>,
    com_prime: &Commitment<R, D>,
    y: &Elt<R, D>,
    opening: &Opening<R, D>,
) -> Result<Vec<Condition>, SrsError> {
    let mut bad = Vec::new();
    if max_norm(core::slice::from_ref(y)) > saturating_u64(bounds.delta_m) {
        bad.push(Condition::ValueNorm);
    }
    if max_norm(&opening.pi0) > saturating_u64(bounds.delta_0) {
        bad.push(Condition::OpeningNorm);
    }
    let knowledge_a = pairing(srs.a1(), &com.pi1)? == com.c.clone() * srs.t().clone();
    let knowledge_b = pairing(srs.a1(), &com_prime.pi1)? == com_prime.c.clone() * srs.t().clone();
    if !(knowledge_a && knowledge_b) {
        bad.push(Condition::KnowledgeEquation);
    }
    if pairing(srs.a0(), &opening.pi0)? != com_prime.c.clone() * com.c.clone() - y.clone() {
        bad.push(Condition::InnerProductEquation);
    }
    Ok(bad)
}

/// §4.2 "Linear functional commitments for integers": the coefficient embedding
/// of `x̂ ∈ Z^N` as `x ∈ R^{N/D}`.
///
/// # Errors
/// [`SrsError::WrongLength`] unless `N` is a non-empty multiple of `D`.
pub fn pack_integer_witness<R: Ring, const D: usize>(
    scalars: &[R],
) -> Result<Vec<Elt<R, D>>, SrsError> {
    if scalars.is_empty() || scalars.len() % D != 0 {
        return Err(SrsError::WrongLength {
            got: scalars.len(),
            expected: D,
        });
    }
    Ok(from_coeffs::<R, D>(scalars))
}

/// The functional side of the same shim, `f = [σ⁻¹(f'ᵢ)]`, so that
/// `⟨f̂, x⟩ ≡ ct(⟨f, x⟩) mod q` — the σ-pairing identity of
/// [`crate::pcs::packing`], with `σ⁻¹ = σ` because `σ` has order two.
///
/// # Errors
/// Propagates [`pack_integer_witness`]'s.
pub fn pack_integer_functional<R: Ring, const D: usize>(
    scalars: &[R],
) -> Result<Vec<Elt<R, D>>, SrsError> {
    Ok(pack_integer_witness::<R, D>(scalars)?
        .iter()
        .map(|e| sigma_of::<R, D>(e))
        .collect())
}

/// The integer claim read out of the ring claim: `ct(y)`. §4.2 — "only `ct(y)`
/// is in the instance over `Z`, while the non-constant coefficients of `y` are
/// instead part of the proof for the relation over `Z`".
pub fn integer_claim<R: Ring, const D: usize>(y: &Elt<R, D>) -> R {
    const_term::<R, D>(y)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use algebra::ring::zq::Zq;
    use alloc::vec;

    /// The crate's Z1 prime: `≡ 1 (mod 2·8)`, so `X^8 + 1` splits completely and
    /// `T` exists.
    type Z1 = Zq<8_380_417>;
    /// `2³² − 99`: prime, `≡ 5 (mod 8)`, so `X^64 + 1` has two degree-32
    /// factors — **no** NTT and no `T`, but the binding half must still work.
    type Q5 = Zq<4_294_967_197>;

    const D8: usize = 8;
    const BASE2: u64 = 2;
    /// `⌈log₂ 8380417⌉ = 23`, and `2²³ = 8388608 > q`, so the split is exact.
    const K23: usize = 23;
    const D64: usize = 64;
    const K32: usize = 32;

    /// `γ_R ≤ D` for power-of-two cyclotomics (Theorem 2.2).
    const GAMMA: u64 = D8 as u64;

    type Srs = PowersSrs<Z1, D8, BASE2, K23>;

    fn elt(seed: u64, i: usize) -> Elt<Z1, D8> {
        PolyRing::from_coefficients(
            (0..D8)
                .map(|k| from_centered::<Z1>(((seed as i64 * 7 + i as i64 * 3 + k as i64) % 5) - 2))
                .collect(),
        )
    }

    fn vector(seed: u64, w: usize) -> Vec<Elt<Z1, D8>> {
        (0..w).map(|i| elt(seed, i)).collect()
    }

    /// `base^k` by repeated ring multiplication (`PolyRing` carries no `pow`).
    fn ring_pow<R: Ring, const D: usize>(base: &Elt<R, D>, k: u64) -> Elt<R, D> {
        let mut acc = const_elt::<R, D>(R::ONE);
        for _ in 0..k {
            acc *= base.clone();
        }
        acc
    }

    fn srs() -> Srs {
        setup::<Z1, D8, BASE2, K23>(&[1u8; 32], 4, 1, true)
            .expect("the Z1 ring splits")
            .0
    }

    fn bounds(w: usize, alpha_x: u64, alpha_f: u64, beta: u64) -> NormBounds {
        NormBounds::derive(w as u64, alpha_x, alpha_f, beta, beta, GAMMA)
            .expect("derived bounds must fit u128")
    }

    /// The shared test bundle: an SRS for `W = 4`, a witness and a functional
    /// of dimension 4, and the gates derived from *their* measured norms.
    fn instance(seed: u64) -> (Srs, Vec<Elt<Z1, D8>>, Vec<Elt<Z1, D8>>, NormBounds) {
        let s = srs();
        let x = vector(seed, 4);
        let f = vector(seed + 1, 4);
        let b = bounds(4, max_norm(&x), max_norm(&f), s.opening_norm_bound());
        (s, x, f, b)
    }

    #[test]
    fn samp_pre_is_exact_and_short() {
        // The load-bearing algebraic step: ⟨a, u⟩ = target *identically*, for
        // every target, and the output really is short. A transposed trapdoor
        // or a swapped half would miss.
        let td = Trapdoor::<Z1, D8, BASE2, K23>::trap_gen(&[2u8; 32], b"t", 1);
        let beta = td.preimage_norm_bound(GAMMA);
        assert_eq!(td.public_vector().len(), 2 * K23, "ℓ = 2k");
        assert_eq!(td.ell(), 2 * K23);
        for i in 0..8u64 {
            let target = elt(i + 1, 3);
            let u = td.samp_pre(&target, &[3u8; 32], i);
            assert_eq!(
                pairing(td.public_vector(), &u).expect("shaped"),
                target,
                "preimage {i} must hit its target"
            );
            assert!(
                max_norm(&u) <= beta,
                "preimage norm {} exceeds the derived β {beta}",
                max_norm(&u)
            );
        }
    }

    #[test]
    fn samp_pre_is_randomized_by_its_tag() {
        // A deterministic preimage sampler would make the SRS a point mass,
        // which is not the distribution k-P-R-ISIS assumes over D_{g,a,v}.
        let td = Trapdoor::<Z1, D8, BASE2, K23>::trap_gen(&[2u8; 32], b"t", 1);
        let target = elt(9, 1);
        let a = td.samp_pre(&target, &[3u8; 32], 0);
        let b = td.samp_pre(&target, &[3u8; 32], 0);
        let c = td.samp_pre(&target, &[3u8; 32], 1);
        assert_eq!(a, b, "the same tag must reproduce the same preimage");
        assert_ne!(a, c, "a different tag must redraw the randomizer");
        assert_eq!(
            pairing(td.public_vector(), &c).expect("shaped"),
            target,
            "and the redrawn preimage must still hit the target"
        );
    }

    #[test]
    fn public_vector_is_the_documented_gadget_form() {
        // Pins the deviation: `a` is a function of `â` and `R` (an RLWE sample
        // per §5.1), so two labels differ while one label reproduces exactly —
        // and the gadget half really is `g − â·R`, entry by entry.
        let td = Trapdoor::<Z1, D8, BASE2, K23>::trap_gen(&[4u8; 32], b"x", 1);
        assert_eq!(
            td,
            Trapdoor::<Z1, D8, BASE2, K23>::trap_gen(&[4u8; 32], b"x", 1)
        );
        assert_ne!(
            td.public_vector(),
            Trapdoor::<Z1, D8, BASE2, K23>::trap_gen(&[4u8; 32], b"y", 1).public_vector()
        );
        let base = const_elt::<Z1, D8>(Z1::from(BASE2));
        let mut gadget = const_elt::<Z1, D8>(Z1::ONE);
        for j in 0..3usize {
            let mut a_r = zero_elt::<Z1, D8>();
            for i in 0..K23 {
                a_r += td.a_hat[i].clone() * td.trap[i * K23 + j].clone();
            }
            assert_eq!(
                td.public_vector()[K23 + j].clone() + a_r,
                gadget,
                "a[{}] + (â·R)_{} must be the gadget entry B^{}",
                K23 + j,
                j,
                j
            );
            gadget *= base.clone();
        }
    }

    #[test]
    fn srs_window_maps_to_powers_of_v() {
        // The structured-SRS invariant for *every* exponent in the window: this
        // is the equation the whole scheme rests on.
        let s = srs();
        assert!(s.well_formed(), "an honest SRS satisfies its own invariant");
        assert_eq!(s.openings.len(), 2 * s.w_max() - 2, "|P| = 2W−2");
        assert_eq!(s.knowledge.len(), s.w_max(), "|[W]| = W");
        assert_eq!(
            s.crs_ring_elements(),
            3 * s.w_max() * 2 * K23,
            "3W vectors of ℓ ring elements (§5.2.1)"
        );
        assert_ne!(
            s.opening_preimage(1).expect("in window"),
            s.opening_preimage(-1).expect("in window"),
            "positive and negative exponents are different targets"
        );
        assert!(s.opening_preimage(0).is_none(), "0 ∉ P (Def 2.11)");
        assert!(s.opening_preimage(4).is_none(), "±W is outside Z(W)");
    }

    #[test]
    fn tampered_srs_entry_breaks_the_setup_invariant() {
        let mut s = srs();
        let idx = opening_slot(s.w_max(), 2).expect("in window");
        s.openings[idx][0] = s.openings[idx][0].clone() + elt(1, 0);
        assert_eq!(
            s.failing_setup_invariant(),
            vec![Condition::SrsPreimages],
            "a tampered preimage must be caught by the invariant"
        );
        assert!(!s.well_formed());
    }

    #[test]
    fn corrupted_crs_is_caught_by_the_setup_invariant() {
        // The trusted-setup story, made checkable: the CRS is data, so a
        // verifier must be able to rebuild it from parts and reject a corrupted
        // window — and `from_parts` must also refuse a non-unit `v`.
        let s = srs();
        let round = PowersSrs::from_parts(s.to_parts()).expect("an honest CRS rebuilds");
        assert_eq!(round, s, "to_parts/from_parts is the identity");
        assert!(round.well_formed());

        let mut swapped = s.to_parts();
        swapped.openings.swap(0, 1);
        let swapped: Srs = PowersSrs::from_parts(swapped).expect("same shape");
        assert_eq!(
            swapped.failing_setup_invariant(),
            vec![Condition::SrsPreimages; 2],
            "two window entries now map to the wrong powers"
        );

        let mut zero_v = s.to_parts();
        zero_v.v = zero_elt::<Z1, D8>();
        let refused: Result<Srs, SrsError> = PowersSrs::from_parts(zero_v);
        assert_eq!(
            refused,
            Err(SrsError::NotAUnit),
            "Setup demands v ∈ R×_q, and a zero divisor must be refused"
        );
    }

    #[test]
    fn honest_proof_satisfies_every_condition() {
        let (s, x, f, b) = instance(3);
        let com = commit(&s, &x).expect("commit");
        let vk = pre_verify(&s, &f, max_norm(&f)).expect("PreVerify");
        let y = ring_dot(&f, &x);
        let opening = open(&s, &f, &x).expect("open");
        assert_eq!(
            failing(&s, &b, &vk, &com, &y, &opening),
            Vec::new(),
            "Theorem 4.1: correctness must hold under the derived gates"
        );
        assert!(
            b.gates_below_half_modulus(Z1::MODULUS),
            "a gate above q/2 would check nothing"
        );
        // The claimed value is the Laurent product's constant term (§4's Open).
        assert_eq!(laurent_product(&x, &f).expect("shaped").constant_term(), y);
        // And the §5.1 single-key form agrees.
        assert_eq!(
            failing_combined(&s, &b, &vk, &com, &y, &opening).expect("shared a"),
            Vec::new()
        );
    }

    #[test]
    fn each_tamper_trips_its_own_condition() {
        // Non-vacuity: if `failing` ignored one argument, that argument's
        // tamper would be accepted.
        let (s, x, f, b) = instance(3);
        let com = commit(&s, &x).expect("commit");
        let vk = pre_verify(&s, &f, max_norm(&f)).expect("PreVerify");
        let y = ring_dot(&f, &x);
        let opening = open(&s, &f, &x).expect("open");
        let one = const_elt::<Z1, D8>(Z1::ONE);

        assert_eq!(
            failing(&s, &b, &vk, &com, &(y.clone() + one.clone()), &opening),
            vec![Condition::OpeningEquation],
            "a false value must be caught by the opening equation"
        );
        let mut bad_pi0 = opening.clone();
        bad_pi0.pi0[0] = bad_pi0.pi0[0].clone() + one.clone();
        assert_eq!(
            failing(&s, &b, &vk, &com, &y, &bad_pi0),
            vec![Condition::OpeningEquation],
            "a tampered opening proof must be caught by the opening equation"
        );
        let mut bad_pi1 = com.clone();
        bad_pi1.pi1[0] = bad_pi1.pi1[0].clone() + one.clone();
        assert_eq!(
            failing(&s, &b, &vk, &bad_pi1, &y, &opening),
            vec![Condition::KnowledgeEquation],
            "a tampered knowledge proof must be caught by its own equation"
        );
        // `c` sits in both equations, so it must be attributed to both.
        let bad_c = Commitment {
            c: com.c.clone() + one.clone(),
            ..com.clone()
        };
        assert_eq!(
            failing(&s, &b, &vk, &bad_c, &y, &opening),
            vec![Condition::KnowledgeEquation, Condition::OpeningEquation]
        );
        // A functional with a wrong key trips the opening equation only.
        assert_eq!(
            failing(&s, &b, &(vk.clone() + one.clone()), &com, &y, &opening),
            vec![Condition::OpeningEquation]
        );
        // A value outside δ_M trips the norm gate *and* the equation.
        let huge = y.clone() + const_elt::<Z1, D8>(Z1::from(1u64 << 21));
        assert_eq!(
            failing(&s, &b, &vk, &com, &huge, &opening),
            vec![Condition::ValueNorm, Condition::OpeningEquation]
        );
        // A gate tightened below the honest proof must reject that proof, and
        // only on its own gate: the equations are untouched.
        let tight = NormBounds {
            delta_0: u128::from(max_norm(&opening.pi0)) - 1,
            ..b
        };
        assert_eq!(
            failing(&s, &tight, &vk, &com, &y, &opening),
            vec![Condition::OpeningNorm]
        );
        let tight1 = NormBounds {
            delta_1: u128::from(max_norm(&com.pi1)) - 1,
            ..b
        };
        assert_eq!(
            failing(&s, &tight1, &vk, &com, &y, &opening),
            vec![Condition::KnowledgeNorm]
        );
        assert!(verify(&s, &b, &vk, &com, &y, &opening).is_ok());
        assert_eq!(
            verify(&s, &b, &vk, &com, &(y + one), &opening)
                .expect_err("false claim")
                .0,
            vec![Condition::OpeningEquation]
        );
    }

    #[test]
    fn combined_check_agrees_with_the_pair_and_refuses_distinct_keys() {
        let (s, x, f, b) = instance(8);
        let com = commit(&s, &x).expect("commit");
        let vk = pre_verify(&s, &f, max_norm(&f)).expect("vk");
        let y = ring_dot(&f, &x);
        let opening = open(&s, &f, &x).expect("open");
        let one = const_elt::<Z1, D8>(Z1::ONE);
        assert_eq!(
            failing_combined(&s, &b, &vk, &com, &(y.clone() + one), &opening).expect("shared a"),
            vec![Condition::OpeningEquation, Condition::CombinedEquation],
            "§5.1's single pairing sees the same false claim"
        );
        let (distinct, _) = setup::<Z1, D8, BASE2, K23>(&[1u8; 32], 4, 1, false).expect("splits");
        assert!(!distinct.shares_a());
        assert_eq!(
            failing_combined(&distinct, &b, &vk, &com, &y, &opening),
            Err(SrsError::DistinctKeys)
        );
        // The §4 box still verifies under its own two keys.
        let com2 = commit(&distinct, &x).expect("commit under a1");
        let opening2 = open(&distinct, &f, &x).expect("open under a0");
        assert_eq!(
            failing(&distinct, &b, &vk, &com2, &y, &opening2),
            Vec::new(),
            "independent a₀/a₁ is the §4 box's shape and must also prove"
        );
    }

    #[test]
    fn pre_verify_enforces_the_functional_alphabet() {
        let (s, _, f, _) = instance(3);
        let alpha = max_norm(&f);
        assert!(pre_verify(&s, &f, alpha).is_ok());
        assert_eq!(
            pre_verify(&s, &f, alpha - 1),
            Err(SrsError::FunctionalOutOfAlphabet {
                norm: alpha,
                bound: alpha - 1
            }),
            "Verify's box says 'if ‖f‖ > α, abort' — the gate must be live"
        );
        assert_eq!(
            check_alphabet(&f, alpha - 1, false),
            Err(SrsError::WitnessOutOfAlphabet {
                norm: alpha,
                bound: alpha - 1
            }),
            "the witness variant must report a different condition"
        );
    }

    #[test]
    fn functional_key_is_the_sum_of_negative_powers() {
        // vk_f = Σ fᵢv⁻ⁱ recomputed independently: a shifted exponent or a
        // missing inverse in `functional_key` cannot pass this.
        let s = srs();
        let f = vector(6, 4);
        let mut expect = zero_elt::<Z1, D8>();
        for (i, fi) in f.iter().enumerate() {
            let mut v_neg_i = const_elt::<Z1, D8>(Z1::ONE);
            for _ in 0..i + 1 {
                v_neg_i *= s.v_inv().clone();
            }
            expect += fi.clone() * v_neg_i;
        }
        assert_eq!(functional_key(&s, &f).expect("shaped"), expect);
        // and it is *not* the positive-power sum
        let mut positive = zero_elt::<Z1, D8>();
        for (i, fi) in f.iter().enumerate() {
            positive += fi.clone() * ring_pow(s.v(), i as u64 + 1);
        }
        assert_ne!(functional_key(&s, &f).expect("shaped"), positive);
    }

    #[test]
    fn power_key_matches_the_log_time_product() {
        // §4.3's identity against the O(w) sum, for every power-of-two
        // dimension the SRS covers.
        let s = srs();
        for w in [1usize, 2, 4] {
            let z = elt(7 + w as u64, 2);
            let f: Vec<Elt<Z1, D8>> = (0..w).map(|i| ring_pow(&z, i as u64)).collect();
            assert_eq!(
                power_functional_key(&s, &z, w).expect("log-time key"),
                functional_key(&s, &f).expect("direct sum"),
                "w = {w}"
            );
        }
        assert_eq!(
            power_functional_key(&s, &elt(1, 1), 3),
            Err(SrsError::NotAPowerOfTwo(3))
        );
        assert_eq!(
            power_functional_key(&s, &elt(1, 1), 8),
            Err(SrsError::WrongLength {
                got: 8,
                expected: 4
            })
        );
    }

    #[test]
    fn multilinear_key_matches_the_eq_tensor_sum() {
        // The N-linear variant of the same trick (§4.3):
        // v⁻¹·Πⱼ((1−zⱼ) + zⱼv^{−2ʲ}) against Σᵢ eq(z, i−1)·v⁻ⁱ.
        let s = srs();
        for ell in [1usize, 2] {
            let point: Vec<Elt<Z1, D8>> = (0..ell).map(|j| elt(11 + j as u64, j)).collect();
            let f = eq_tensor::<Z1, D8>(&point, s.w_max()).expect("fits");
            assert_eq!(f.len(), 1 << ell);
            assert_eq!(
                multilinear_functional_key(&s, &point).expect("log-time ml key"),
                functional_key(&s, &f).expect("direct eq sum"),
                "ℓ = {ell} variables"
            );
        }
        assert_eq!(
            eq_tensor::<Z1, D8>(&vector(1, 3), 4),
            Err(SrsError::WrongLength {
                got: 8,
                expected: 4
            })
        );
    }

    #[test]
    fn universal_srs_serves_every_smaller_dimension() {
        // §4.1 "Universal SRS": one `ck` for all `w ≤ W`, protocol unmodified.
        let s = srs();
        for w in 1..=s.w_max() {
            let x = vector(20 + w as u64, w);
            let f = vector(31 + w as u64, w);
            let b = bounds(w, max_norm(&x), max_norm(&f), s.opening_norm_bound());
            assert!(
                b.gates_below_half_modulus(Z1::MODULUS),
                "w = {w}: gates must stay meaningful"
            );
            let com = commit(&s, &x).expect("commit");
            let vk = pre_verify(&s, &f, max_norm(&f)).expect("pre-verify");
            let y = ring_dot(&f, &x);
            let opening = open(&s, &f, &x).expect("open");
            assert_eq!(
                failing(&s, &b, &vk, &com, &y, &opening),
                Vec::new(),
                "w = {w}"
            );
        }
        assert_eq!(
            commit(&s, &vector(1, s.w_max() + 1)),
            Err(SrsError::WrongLength {
                got: 5,
                expected: 4
            }),
            "w > W is out of scope for this SRS"
        );
    }

    #[test]
    fn aggregation_folds_many_openings_into_one() {
        // §4.1 public proof aggregation.
        let s = srs();
        let beta = s.opening_norm_bound();
        let mut coms = Vec::new();
        let mut vks = Vec::new();
        let mut ys = Vec::new();
        let mut openings = Vec::new();
        for i in 0..3u64 {
            let x = vector(40 + i, 4);
            let f = vector(55 + i, 4);
            coms.push(commit(&s, &x).expect("commit"));
            vks.push(pre_verify(&s, &f, max_norm(&f)).expect("vk"));
            ys.push(ring_dot(&f, &x));
            openings.push(open(&s, &f, &x).expect("open"));
        }
        let claims: Vec<Claim<'_, Z1, D8>> = (0..3)
            .map(|i| Claim {
                commitment: &coms[i].c,
                functional_key: &vks[i],
                value: &ys[i],
                opening: &openings[i].pi0,
            })
            .collect();
        // Ternary challenges with two non-zero coefficients: the §2.1 set H,
        // whose operator norm is c = 2 (Lemma 2.5).
        let hs = vec![
            monomial::<Z1, D8>(0) + monomial::<Z1, D8>(3),
            -monomial::<Z1, D8>(1),
            monomial::<Z1, D8>(2) - monomial::<Z1, D8>(5),
        ];
        let bound = bounds(4, 2, 8, beta)
            .aggregated_opening_bound(claims.len(), 2)
            .expect("aggregate bound fits");
        let (residual, pi0) = aggregate(&s, &claims, &hs).expect("aggregate");
        assert_eq!(
            failing_aggregated(&s, &residual, &pi0, bound).expect("shaped"),
            Vec::new(),
            "the aggregate of honest openings must verify"
        );
        // Dropping one summand's contribution moves the residual only: the
        // folded equation must then fail, which is what makes aggregation sound.
        let mut wrong = residual.clone();
        wrong += hs[1].clone();
        assert_eq!(
            failing_aggregated(&s, &wrong, &pi0, bound).expect("shaped"),
            vec![Condition::AggregatedOpeningEquation]
        );
        assert_eq!(
            aggregate(&s, &claims, &hs[..2]),
            Err(SrsError::WrongLength {
                got: 2,
                expected: 3
            })
        );
    }

    #[test]
    fn inner_product_argument_verifies_and_binds() {
        // §4.1: `y = ⟨x, x'⟩` between two committed vectors, opened with the
        // committed functional `x'`.
        //
        // The functional has to be committed **dual**: the IPA pair
        // `⟨a, π₀⟩ = c′·c − y` is satisfiable only when `c′` sits at the
        // negative powers `v^{-i}`, which is what `extend_for_inner_product`
        // samples. `dual_window_is_what_makes_the_inner_product_equations_hold`
        // below pins the negative side — a plain `commit(&s, &xp)` fails here
        // with `InnerProductEquation`, which is exactly how this test used to
        // "fail" before that capability landed.
        let (mut s, waste) = setup::<Z1, D8, BASE2, K23>(&[1u8; 32], 4, 1, true).expect("splits");
        let x = vector(60, 4);
        let xp = vector(61, 4);
        waste
            .extend_for_inner_product(&mut s, &[3u8; 32])
            .expect("extend");
        assert!(s.has_dual_window());
        let beta = s.opening_norm_bound();
        let com = commit(&s, &x).expect("commit");
        let com_prime = commit_dual(&s, &xp).expect("dual commit");
        let y = ring_dot(&xp, &x);
        let opening = open(&s, &xp, &x).expect("open");
        let ip_bounds = bounds(4, max_norm(&x), max_norm(&xp), beta);
        assert_eq!(
            failing_inner_product(&s, &ip_bounds, &com, &com_prime, &y, &opening).expect("shaped"),
            Vec::new(),
            "the honest inner product must verify"
        );
        let one = const_elt::<Z1, D8>(Z1::ONE);
        assert_eq!(
            failing_inner_product(
                &s,
                &ip_bounds,
                &com,
                &com_prime,
                &(y.clone() + one.clone()),
                &opening
            )
            .expect("shaped"),
            vec![Condition::InnerProductEquation],
            "a false inner product must be rejected by its own equation"
        );
        let mut bad_pi1 = com_prime.clone();
        bad_pi1.pi1[0] = bad_pi1.pi1[0].clone() + one.clone();
        assert_eq!(
            failing_inner_product(&s, &ip_bounds, &com, &bad_pi1, &y, &opening).expect("shaped"),
            vec![Condition::KnowledgeEquation],
            "π₁ reaches the knowledge proof only, so this isolates that check"
        );
        // The stretch §4.1's remark demands: with the functional itself
        // extracted, β*₀ grows by the δ₁ factor.
        let plain = bounds(4, 2, 2, beta);
        let stretched = plain.inner_product_variant().expect("fits");
        assert_eq!(
            stretched.delta_0,
            plain.delta_0 * plain.delta_1 * plain.delta_1 / (2 * 2)
        );
        assert!(stretched.beta_star_0 > plain.beta_star_0);
    }

    #[test]
    fn dual_window_is_what_makes_the_inner_product_equations_hold() {
        // §4.1 prints two checks for the IPA — "verifies both knowledge proofs
        // as in Verify, and then checks the opening proof satisfies
        // ⟨a, π₀⟩ ≡ c′ · c − y". With `Com` at vⁱ that pair is satisfiable only
        // if c′ is the commitment of x′ at v^{-i}, which needs preimages of
        // v^{-i}·t that §4's Setup box never samples. This test pins both sides
        // of that: the extension makes the IPA verify, and an ordinary
        // commitment of x′ does *not*.
        let (mut s, waste) = setup::<Z1, D8, BASE2, K23>(&[2u8; 32], 4, 1, true).expect("splits");
        let x = vector(60, 4);
        let xp = vector(61, 4);
        let y = ring_dot(&xp, &x);
        let opening = open(&s, &xp, &x).expect("open");
        let b = bounds(4, max_norm(&x), max_norm(&xp), s.opening_norm_bound());
        let com = commit(&s, &x).expect("commit");

        assert!(!s.has_dual_window());
        assert_eq!(commit_dual(&s, &x), Err(SrsError::MissingDualWindow));
        // The plain commitment of x′ fails the IPA equations, so the dual
        // window is load-bearing rather than decoration. It fails the
        // inner-product equation *alone*: `commit` still produces a π₁ that
        // satisfies the knowledge proof for its own `c`, and `c` at the
        // positive powers is what breaks `⟨a₀, π₀⟩ = c′·c − y`. That isolation
        // is the stronger result — it says no valid-looking commitment can
        // stand in for the dual one, and that the two checks are independent
        // rather than one shadowing the other.
        let plain_prime = commit(&s, &xp).expect("commit");
        assert_eq!(
            failing_inner_product(&s, &b, &com, &plain_prime, &y, &opening).expect("shaped"),
            vec![Condition::InnerProductEquation]
        );

        let before = s.crs_ring_elements();
        waste
            .extend_for_inner_product(&mut s, &[3u8; 32])
            .expect("extend");
        assert_eq!(
            s.crs_ring_elements() - before,
            4 * 2 * K23,
            "the extension adds W preimages of ℓ ring elements"
        );
        assert!(
            s.well_formed(),
            "the extended window must satisfy the same Setup invariant: {:?}",
            s.failing_setup_invariant()
        );
        let dual_prime = commit_dual(&s, &xp).expect("dual commit");
        assert_eq!(
            pairing(s.a1(), &dual_prime.pi1).expect("shaped"),
            dual_prime.c.clone() * s.t().clone(),
            "⟨a₁,π₁′⟩ = c′·t with c′ at the negative powers"
        );
        assert_eq!(
            failing_inner_product(&s, &b, &com, &dual_prime, &y, &opening).expect("shaped"),
            Vec::new(),
            "the honest inner product must verify once the window exists"
        );
        // And a corrupted dual entry is caught by the invariant alone.
        let mut parts = s.to_parts();
        parts.dual_knowledge.swap(0, 3);
        let corrupted: Srs = PowersSrs::from_parts(parts).expect("same shape");
        assert_eq!(
            corrupted.failing_setup_invariant(),
            vec![Condition::SrsPreimages; 2],
            "swapped negative-power preimages must break S0"
        );
        let rebuilt: Srs = PowersSrs::from_parts(s.to_parts()).expect("rebuild");
        assert_eq!(
            rebuilt.dual, s.dual,
            "to_parts/from_parts must carry the extension"
        );
    }

    #[test]
    fn integer_shim_reads_the_scalar_inner_product() {
        // §4.2: ⟨f̂, x̂⟩ ≡ ct(⟨f, x⟩) with f = σ⁻¹(embed(f̂)).
        let scalars: Vec<Z1> = (0..D8 * 2)
            .map(|i| from_centered::<Z1>(((i as i64 * 13) % 7) - 3))
            .collect();
        let other: Vec<Z1> = (0..D8 * 2)
            .map(|i| from_centered::<Z1>(((i as i64 * 5 + 2) % 9) - 4))
            .collect();
        let x = pack_integer_witness::<Z1, D8>(&scalars).expect("packed");
        let f = pack_integer_functional::<Z1, D8>(&other).expect("packed");
        let mut expect = Z1::ZERO;
        for (a, b) in scalars.iter().zip(other.iter()) {
            expect += *a * *b;
        }
        assert_eq!(integer_claim(&ring_dot(&f, &x)), expect);
        assert_eq!(
            pack_integer_witness::<Z1, D8>(&scalars[..D8 * 2 - 1]),
            Err(SrsError::WrongLength {
                got: D8 * 2 - 1,
                expected: D8
            })
        );
    }

    #[test]
    fn vanishing_element_is_a_half_zero_divisor_only_when_the_ring_splits() {
        // Definition 2.15's two restrictions, checked on the split ring.
        let (t, support) = vanishing_element_with_support::<Z1, D8>(&[5u8; 32]).expect("splits");
        assert_eq!(support.len(), D8 / 2, "exactly half the roots");
        let roots = roots_of_negacyclic::<Z1, D8>().expect("splits");
        assert_eq!(roots.len(), D8);
        for (k, r) in roots.iter().enumerate() {
            let vanished = t.evaluate(r) == Z1::ZERO;
            assert_eq!(
                vanished,
                support.contains(&k),
                "root {k} (r = {r}) vanishing must match the support exactly"
            );
        }
        assert!(
            ring_inverse::<Z1, D8>(&t).is_none(),
            "a half-vanishing t is a zero divisor"
        );
        // The annihilator: multiples of ∏_{r∉S}(X − r) kill t, and none of them
        // is ±1-coefficient — which is restriction 2 in the only form a toy
        // dimension can express.
        let mut ann = const_elt::<Z1, D8>(Z1::ONE);
        for (k, r) in roots.iter().enumerate() {
            if !support.contains(&k) {
                ann *= monomial::<Z1, D8>(1) - const_elt::<Z1, D8>(*r);
            }
        }
        assert_eq!(t * ann.clone(), zero_elt::<Z1, D8>(), "t·ann = 0");
        assert!(
            max_norm(&[ann.clone()]) > 1,
            "the annihilator generator is not ±1-coefficient"
        );
        assert!(ring_inverse::<Z1, D8>(&ann).is_none());
    }

    #[test]
    fn ring_inverse_agrees_with_multiplication() {
        // A zero divisor must refuse, a unit must satisfy x·x⁻¹ = 1, and the
        // monomial case has a closed form: X·(−X^{D−1}) = −X^D = 1.
        let x = elt(12, 4);
        let inv = ring_inverse::<Z1, D8>(&x).expect("a random element is a unit");
        assert_eq!(x * inv, const_elt::<Z1, D8>(Z1::ONE));
        let zero = zero_elt::<Z1, D8>();
        assert_eq!(ring_inverse::<Z1, D8>(&zero), None);
        let t = vanishing_element::<Z1, D8>(&[5u8; 32]).expect("splits");
        assert_eq!(ring_inverse::<Z1, D8>(&t), None, "t is a zero divisor");
        let x_mono = monomial::<Z1, D8>(1);
        assert_eq!(
            ring_inverse::<Z1, D8>(&x_mono),
            Some(-monomial::<Z1, D8>(D8 - 1))
        );
    }

    #[test]
    fn non_ntt_ring_binding_half_round_trips() {
        // The requirement that this capability not lean on NTT-friendliness.
        // `q = 2³² − 99 ≡ 5 (mod 8)` gives `X^64 + 1` two degree-32 factors, so
        // `T` is unavailable (`vanishing_element` must refuse) while the whole
        // k-P-R-ISIS *binding* half — trapdoor, power window, `Open`,
        // `PreVerify` and the opening equation — runs unchanged.
        assert_eq!(
            (Q5::MODULUS - 1).trailing_zeros(),
            2,
            "2-adicity 2 ⇒ no NTT"
        );
        assert_eq!(
            vanishing_element::<Q5, D64>(&[1u8; 32]),
            Err(SrsError::NotSplitCompletely {
                modulus: Q5::MODULUS,
                degree: D64
            })
        );
        let td = Trapdoor::<Q5, D64, BASE2, K32>::trap_gen(&[7u8; 32], b"a0", 1);
        let (v, v_inv) = sample_unit::<Q5, D64>(&[7u8; 32], b"v", 8).expect("a unit exists");
        assert_eq!(v.clone() * v_inv.clone(), const_elt::<Q5, D64>(Q5::ONE));
        assert_eq!(
            td.preimage_norm_bound(D64 as u64),
            1 + K32 as u64 * 1 * D64 as u64 * 1
        );

        let w = 3usize;
        let mut window: Vec<(i32, Vec<Elt<Q5, D64>>)> = Vec::new();
        for exponent in -(w as i32 - 1)..=w as i32 - 1 {
            if exponent == 0 {
                continue;
            }
            let base = if exponent > 0 {
                v.clone()
            } else {
                v_inv.clone()
            };
            let mut target = base.clone();
            for _ in 1..exponent.unsigned_abs() {
                target *= base.clone();
            }
            // The tag is a domain-separation nonce, so it only has to be
            // distinct per exponent — but it is a `u64`, and `exponent as u64`
            // on a negative `i32` is 2^64 − k, which overflowed on the first
            // negative exponent. Shifting into the non-negative range keeps
            // +k and −k apart, which `.unsigned_abs()` would not.
            let tag = (exponent + w as i32) as u64 + 8;
            let u = td.samp_pre(&target, &[8u8; 32], tag);
            assert!(
                max_norm(&u) <= td.preimage_norm_bound(D64 as u64),
                "preimage {exponent} is short over a ring with no NTT"
            );
            assert_eq!(
                pairing(td.public_vector(), &u).expect("shaped"),
                target,
                "exponent {exponent} must be hit exactly"
            );
            window.push((exponent, u));
        }

        // The opening equation itself, with no `t` and no NTT.
        let x: Vec<Elt<Q5, D64>> = (0..w)
            .map(|i| {
                PolyRing::from_coefficients(
                    (0..D64)
                        .map(|k| from_centered::<Q5>(((i * 5 + k) % 5) as i64 - 2))
                        .collect(),
                )
            })
            .collect();
        let f: Vec<Elt<Q5, D64>> = (0..w)
            .map(|i| {
                PolyRing::from_coefficients(
                    (0..D64)
                        .map(|k| from_centered::<Q5>(((i * 3 + 2 * k) % 7) as i64 - 3))
                        .collect(),
                )
            })
            .collect();
        let lp = laurent_product(&x, &f).expect("shaped");
        let y = lp.constant_term();
        assert_eq!(y, ring_dot(&f, &x), "a₀ = ⟨f, x⟩ over the non-NTT ring");
        let mut c = zero_elt::<Q5, D64>();
        let mut vk = zero_elt::<Q5, D64>();
        let mut pi0 = vec![zero_elt::<Q5, D64>(); td.ell()];
        for (i, xi) in x.iter().enumerate() {
            c += xi.clone() * ring_pow(&v, (i + 1) as u64);
            vk += f[i].clone() * ring_pow(&v_inv, (i + 1) as u64);
        }
        for (exponent, u) in &window {
            let a = lp.coefficient(*exponent).expect("in window");
            for (acc, uk) in pi0.iter_mut().zip(u.iter()) {
                *acc += a.clone() * uk.clone();
            }
        }
        assert_eq!(
            pairing(td.public_vector(), &pi0).expect("shaped"),
            vk * c - y,
            "⟨a₀,π₀⟩ = vk_f·c − y must hold over a ring with no NTT"
        );
    }

    #[test]
    fn derived_gates_track_the_parameters_they_claim() {
        // Table 1's formulas, recomputed by hand: a silently changed factor
        // would make every gate assertion above vacuous.
        let b = NormBounds::derive(4, 3, 5, 7, 11, 8).expect("fits");
        assert_eq!(b.delta_m, 4 * 3 * 5 * 8);
        assert_eq!(b.delta_1, 4 * 3 * 11 * 8);
        assert_eq!(b.delta_0, 16 * 3 * 5 * 7 * 64);
        assert_eq!(b.beta_star_0, 2 * 16 * 3 * b.delta_1 * 7 * 64);
        assert!(b.gates_below_half_modulus(1u64 << 31));
        assert!(
            !b.gates_below_half_modulus(1000),
            "with q = 1000 the gates exceed q/2 and stop meaning anything"
        );
        // The single-α case is the paper's Table 1 row.
        let one = NormBounds::derive(4, 3, 3, 7, 7, 8).expect("fits");
        assert_eq!(one.delta_m, 4 * 9 * 8);
        assert_eq!(one.delta_0, 16 * 9 * 7 * 64);
        assert_eq!(one.delta_1, 4 * 3 * 7 * 8);
    }

    #[test]
    fn laurent_product_is_the_convolution_of_the_two_power_series() {
        let x = vector(2, 3);
        let f = vector(4, 3);
        let lp = laurent_product(&x, &f).expect("shaped");
        assert_eq!(lp.coeffs.len(), 2 * 3 - 1);
        assert_eq!(lp.w(), 3);
        assert_eq!(lp.exponents(), vec![-2, -1, 1, 2]);
        assert_eq!(lp.coefficient(3), None, "outside the window");
        for k in -2..=2 {
            let mut expect = zero_elt::<Z1, D8>();
            for i in 0..3usize {
                let j = i as i32 - k;
                if (0..3).contains(&j) {
                    expect += x[i].clone() * f[j as usize].clone();
                }
            }
            assert_eq!(lp.coefficient(k).expect("in window"), &expect, "a_{k}");
        }
        assert_eq!(lp.constant_term(), ring_dot(&x, &f));
        assert_eq!(
            laurent_product(&x, &vector(4, 2)),
            Err(SrsError::WrongLength {
                got: 2,
                expected: 3
            })
        );
        assert_eq!(
            laurent_product::<Z1, D8>(&[], &[]),
            Err(SrsError::WrongLength {
                got: 0,
                expected: 1
            })
        );
    }

    #[test]
    fn shared_and_distinct_a_both_prove_and_the_waste_forges() {
        // §5.1's two key choices, plus the trusted-setup caveat made concrete.
        for shared in [true, false] {
            let (s, waste) = setup::<Z1, D8, BASE2, K23>(&[9u8; 32], 4, 1, shared).expect("splits");
            assert_eq!(s.a0() == s.a1(), shared, "shared_a must be observable");
            assert!(s.well_formed());
            let x = vector(3, 4);
            let f = vector(4, 4);
            let b = bounds(4, max_norm(&x), max_norm(&f), s.opening_norm_bound());
            let com = commit(&s, &x).expect("commit");
            let vk = pre_verify(&s, &f, max_norm(&f)).expect("vk");
            let y = ring_dot(&f, &x);
            let opening = open(&s, &f, &x).expect("open");
            assert_eq!(failing(&s, &b, &vk, &com, &y, &opening), Vec::new());
            // With the trapdoor, a false claim opens just as well: this is why
            // the setup is *trusted* and `SetupTrapdoor` must be destroyed.
            let one = const_elt::<Z1, D8>(Z1::ONE);
            let forged_target = vk.clone() * com.c.clone() - (y.clone() + one.clone());
            let forged = waste
                .open_trapdoor()
                .samp_pre(&forged_target, &[0u8; 32], 7);
            assert_eq!(
                failing(
                    &s,
                    &b,
                    &vk,
                    &com,
                    &(y.clone() + one.clone()),
                    &Opening { pi0: forged }
                ),
                Vec::new(),
                "a trapdoor holder opens to anything — the trusted-setup caveat"
            );
            // The same holds on the knowledge side: a false commitment can be
            // given a valid π₁, which is why `Verify`'s E1 is a *knowledge*
            // guarantee rather than a binding one.
            let false_c = com.c.clone() + one.clone();
            let forged_pi1 = waste.knowledge_trapdoor().samp_pre(
                &(false_c.clone() * s.t().clone()),
                &[0u8; 32],
                8,
            );
            let forged_com = Commitment {
                c: false_c,
                pi1: forged_pi1,
            };
            assert_eq!(
                failing(&s, &b, &vk, &forged_com, &y, &opening),
                vec![Condition::OpeningEquation],
                "the forged π₁ must satisfy E1 while E2 still rejects the swap"
            );
        }
    }
}
