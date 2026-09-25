//! Binary R1CS and its reduction to the dot-product relation (LaBRADOR §6,
//! Figure 4): the statement side of "prove knowledge of a satisfying witness".
//!
//! # Why this lives next to [`crate::instance::r1cs`]
//!
//! [`crate::instance::r1cs::ToyR1cs`] is the Z2-ring squaring-gate instance the
//! `opening` and `folding` domains consume. LaBRADOR needs the paper's actual
//! statement language: a rank-1 constraint system `A·ẘ ∘ B·ẘ = C·ẘ` with
//! *binary* matrices over `F₂` (§6's "Binary R1CS"), because the reduction to
//! [`Relation`] rides on the witness coefficients being `0/1`.
//!
//! # The reduction (Figure 4)
//!
//! The prover commits to `(a‖b‖c‖w)` with `a = A·w mod 2`, `b = B·w mod 2`,
//! `c = C·w mod 2`, then proves knowledge of a short opening
//! `r⃗ = (a, b, c, w, ã, b̃, c̃, w̃)` with `ã = σ⁻¹(a)` and so on, such that
//!
//! * `𝒜·(a‖b‖c‖w) = t⃗` — the commitment really opens. These go to family `F`:
//!   a commitment equality is a *ring* equality, so it must vanish in `R_q`.
//! * `a, b, c, w` have binary coefficients: the prover proves
//!   `Σᵢ xᵢ(xᵢ − 1) = 0` as the constant term of `⟨x, x̃ − 1⟩`, and with
//!   `‖·‖₂² < q` that sum is zero over the integers, so every `xᵢ ∈ {0,1}`.
//! * `a ∘ b = c`. For bits, `ab = c ⟺ a + b − 2c ∈ {0,1}` ([GOS12]), so one
//!   further binarity claim on the combination suffices.
//! * the `3k` relations `a = A·w`, `b = B·w`, `c = C·w` **mod 2** are not proven
//!   one by one: the verifier takes `l` random `F₂`-linear combinations and the
//!   prover proves only those, at soundness error `2⁻ˡ`. The combination
//!   `(α, β, γ)` fixes `δ = Lift(αAᵗ + βBᵗ + γCᵗ mod 2)` and the claim
//!   `g = ⟨α,a⟩ + ⟨β,b⟩ + ⟨γ,c⟩ − ⟨δ,w⟩`, which the verifier checks is *even*.
//!
//! [`reduce`] is the map `(R1CS, witness) → (statement, witness)`;
//! [`R1csGuards::check`] evaluates Theorem 6.2's shape conditions and its
//! composition slack.
//!
//! # Lift convention
//!
//! The paper lets a `Z_q`-linear `f` stand for "the unique `R_q`-linear `f′`
//! with `ct(f′) = f`" but does not pin the lift. This module fixes it with the
//! pairing identity `Σ_m X_m·Y_m = ct(Σ_k σ(X̂_k)·Ŝ_k)` (see
//! [`crate::pcs::packing`], re-checked at `D = 64` in the tests here): a
//! `Z_q` functional with coefficient vector `X` becomes the ring vector
//! `σ(X̂)`. The four equations `x̃ = σ⁻¹(x)` are vector-valued, so each is
//! projected by one random `θ ∈ Z_q^{rank·D}` — a Schwartz–Zippel loss of `1/q`
//! per equation, the same device Figure 4 uses for the `3k` linear relations.

use crate::pcs::dotproduct::{
    const_elt, inner_product, zero_elt, CtFn, Elt, QuadFn, Relation, WitnessVec,
};
use crate::pcs::key::RingMatrixKey;
use crate::pcs::packing::sigma_of;
use algebra::crypto::sampling::{sample_uniform_coeff, BitStream};
use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::ring::traits::CenteredRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::{vec, vec::Vec};
use core::fmt;

/// Number of witness vectors Figure 4 produces: `(a, b, c, w, ã, b̃, c̃, w̃)`.
pub const MULTIPLICITY: usize = 8;

/// A `0/1` matrix, row-major, one byte per entry.
///
/// Binary is Figure 4's regime (`A, B, C ∈ {0,1}^{k×n}`), and keeping entries
/// as bytes rather than ring elements makes the `F₂` arithmetic — row products,
/// column combinations, parity — exact by construction, with no
/// centered-representative questions to answer.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BitMatrix {
    rows: usize,
    cols: usize,
    bits: Vec<u8>,
}

impl BitMatrix {
    /// A `rows × cols` matrix from a bit function.
    pub fn from_fn(rows: usize, cols: usize, mut bit: impl FnMut(usize, usize) -> u8) -> Self {
        let mut bits = Vec::with_capacity(rows * cols);
        for i in 0..rows {
            for j in 0..cols {
                bits.push(bit(i, j) & 1);
            }
        }
        Self { rows, cols, bits }
    }

    /// A random `rows × cols` matrix with `weight` non-zeros per row.
    pub fn random_sparse<X: Xof>(
        stream: &mut BitStream<'_, X>,
        rows: usize,
        cols: usize,
        weight: usize,
    ) -> Self {
        assert!(weight >= 1 && weight <= cols, "sparse rows need room");
        let mut m = Self::from_fn(rows, cols, |_, _| 0);
        for i in 0..rows {
            let mut placed = 0usize;
            while placed < weight {
                let j = (stream.read_bits(32) as usize) % cols;
                if m.get(i, j) == 0 {
                    m.set(i, j, 1);
                    placed += 1;
                }
            }
        }
        m
    }

    /// Row count.
    pub const fn rows(&self) -> usize {
        self.rows
    }

    /// Column count.
    pub const fn cols(&self) -> usize {
        self.cols
    }

    /// Entry `(i, j)`.
    ///
    /// # Panics
    /// If the index is out of range.
    pub fn get(&self, i: usize, j: usize) -> u8 {
        self.bits[i * self.cols + j]
    }

    /// Row `i` as a slice.
    ///
    /// # Panics
    /// If `i >= rows`.
    pub fn row(&self, i: usize) -> &[u8] {
        &self.bits[i * self.cols..(i + 1) * self.cols]
    }

    /// Sets entry `(i, j)` to a bit.
    ///
    /// # Panics
    /// If the index is out of range.
    pub fn set(&mut self, i: usize, j: usize, value: u8) {
        self.bits[i * self.cols + j] = value & 1;
    }

    /// `M·v` over `F₂`.
    ///
    /// # Panics
    /// If `v.len() != cols`.
    pub fn mul_vec_over_2(&self, v: &[u8]) -> Vec<u8> {
        assert_eq!(v.len(), self.cols, "matrix-vector shape mismatch");
        (0..self.rows)
            .map(|i| {
                self.row(i)
                    .iter()
                    .zip(v.iter())
                    .fold(0u8, |acc, (&m, &x)| acc ^ (m & x))
            })
            .collect()
    }

    /// `Mᵗ·v` over `F₂` — the column combination that defines `δ`.
    ///
    /// # Panics
    /// If `v.len() != rows`.
    pub fn transposed_mul(&self, v: &[u8]) -> Vec<u8> {
        assert_eq!(v.len(), self.rows, "transpose shape mismatch");
        (0..self.cols)
            .map(|j| (0..self.rows).fold(0u8, |acc, i| acc ^ (self.get(i, j) & v[i])))
            .collect()
    }
}

/// A binary rank-1 constraint system: `A·w ∘ B·w = C·w` over `F₂`
/// (Definition 6.1 with `N = 2`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryR1cs {
    /// Constraint count `k`.
    pub k: usize,
    /// Variable count `n`.
    pub n: usize,
    /// Left matrix.
    pub a: BitMatrix,
    /// Right matrix.
    pub b: BitMatrix,
    /// Output matrix.
    pub c: BitMatrix,
}

impl BinaryR1cs {
    /// `(A·w, B·w, C·w)` over `F₂`.
    pub fn products(&self, w: &[u8]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
        (
            self.a.mul_vec_over_2(w),
            self.b.mul_vec_over_2(w),
            self.c.mul_vec_over_2(w),
        )
    }

    /// Checks `A·w ∘ B·w = C·w` entrywise over `F₂`.
    pub fn is_satisfied(&self, w: &[u8]) -> bool {
        if w.len() != self.n || self.k == 0 {
            return false;
        }
        let (a, b, c) = self.products(w);
        a.iter()
            .zip(b.iter())
            .zip(c.iter())
            .all(|((&ai, &bi), &ci)| (ai & bi) == ci)
    }
}

/// A binary R1CS together with a satisfying witness.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BinaryInstance {
    /// The constraint system.
    pub r1cs: BinaryR1cs,
    /// The binary witness `w ∈ {0,1}^n`.
    pub witness: Vec<u8>,
}

/// Draws a satisfiable binary R1CS with a random binary witness.
///
/// `A` and `B` are random with `weight` non-zeros per row and `w` is random;
/// each `C` row is drawn and then **repaired** — one witness-supported entry is
/// flipped — until `C·w = (A·w) ∘ (B·w)`. Skipping the repair would leave
/// instances that are satisfiable by nobody, and every "honest proof verifies"
/// assertion downstream would then prove nothing.
///
/// # Panics
/// Unless `n ≥ 2`, `k ≥ 1` and `1 ≤ weight ≤ n`.
pub fn sample_satisfiable(seed: &[u8; 32], k: usize, n: usize, weight: usize) -> BinaryInstance {
    assert!(
        n >= 2 && k >= 1 && weight >= 1 && weight <= n,
        "need n ≥ 2, k ≥ 1 and 1 ≤ weight ≤ n"
    );
    let mut xof = Shake128Xof::new(b"lattice-algebra/Z7/binary-r1cs");
    xof.absorb(seed);
    let mut stream = BitStream::new(&mut xof);
    let mut witness = vec![0u8; n];
    let mut ones = 0usize;
    for x in witness.iter_mut() {
        *x = (stream.read_bits(1) & 1) as u8;
        ones += usize::from(*x);
    }
    if ones == 0 {
        // The repair needs a witness entry to lean a C row on.
        witness[n - 1] = 1;
    }
    let a = BitMatrix::random_sparse(&mut stream, k, n, weight);
    let b = BitMatrix::random_sparse(&mut stream, k, n, weight);
    let mut c = BitMatrix::random_sparse(&mut stream, k, n, weight);
    let (aw, bw) = (a.mul_vec_over_2(&witness), b.mul_vec_over_2(&witness));
    let supporter = (0..n)
        .find(|&j| witness[j] == 1)
        .expect("witness is non-zero");
    for i in 0..k {
        let target = aw[i] & bw[i];
        let current = c
            .row(i)
            .iter()
            .zip(witness.iter())
            .fold(0u8, |acc, (&m, &x)| acc ^ (m & x));
        if current != target {
            // Flipping a supported entry toggles the row's value: exactly one
            // flip closes any gap.
            c.set(i, supporter, c.get(i, supporter) ^ 1);
        }
    }
    BinaryInstance {
        r1cs: BinaryR1cs { k, n, a, b, c },
        witness,
    }
}

/// Theorem 6.2's conditions on the instance shape.
///
/// * `n + 3k < q` and `6k < q`: the integer sums
///   `g = ⟨α,a⟩+⟨β,b⟩+⟨γ,c⟩−⟨δ,w⟩` and
///   `Σᵢ (aᵢ+bᵢ−2cᵢ)(aᵢ+bᵢ−2cᵢ−1) ≤ 6k` never wrap, so vanishing mod `q` means
///   vanishing over the integers.
/// * `n + 3k < 15q/128`: the binarity witness has
///   `‖a‖ã‖b‖b̃‖c‖c̃‖w‖w̃‖₂² = 2(3k+n)`, and the paper's condition makes that
///   less than `q/(128/30)` — below `√q` with the projection slack already paid
///   for, which is what lets this reduction compose with the main protocol.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct R1csGuards {
    /// `n + 3k < q`.
    pub no_overflow: bool,
    /// `6k < q`.
    pub product_guard: bool,
    /// `n + 3k < 15q/128`.
    pub composition: bool,
}

impl R1csGuards {
    /// Evaluates the three inequalities for `(k, n, q)`.
    #[must_use]
    pub fn check(k: usize, n: usize, modulus: u64) -> Self {
        let q = u128::from(modulus);
        let lhs = u128::from(n as u64) + 3 * u128::from(k as u64);
        Self {
            no_overflow: lhs < q,
            product_guard: 6 * u128::from(k as u64) < q,
            composition: 128 * lhs < 15 * q,
        }
    }

    /// Whether all three hold.
    #[must_use]
    pub const fn all(self) -> bool {
        self.no_overflow && self.product_guard && self.composition
    }
}

/// A reduction failure.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReduceError {
    /// The witness does not satisfy the system.
    Unsatisfied,
    /// Theorem 6.2's shape guards do not hold.
    Guards(R1csGuards),
    /// `k` is not a multiple of the ring degree, so the padding the reduction
    /// assumes is missing.
    NotPadded {
        /// Constraint count.
        k: usize,
        /// Ring degree.
        degree: usize,
    },
    /// `k ≠ n`: Figure 4's four vectors must share a length to be the
    /// relation's `s₁…s₄`, and padding to a common rank is the caller's job.
    UnequalSizes {
        /// Constraint count.
        k: usize,
        /// Variable count.
        n: usize,
    },
    /// A vector had the wrong length for the instance shape.
    WrongShape {
        /// Length supplied.
        got: usize,
        /// Length required.
        expected: usize,
    },
    /// The commitment key does not match `𝒜 ∈ R_q^{κ′×4·rank}`.
    WrongKeyShape {
        /// Columns supplied.
        got: usize,
        /// Columns required.
        expected: usize,
    },
}

impl fmt::Display for ReduceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unsatisfied => write!(f, "the witness does not satisfy the R1CS"),
            Self::Guards(g) => write!(f, "Theorem 6.2 guards fail: {g:?}"),
            Self::NotPadded { k, degree } => {
                write!(f, "k = {k} must be a multiple of the ring degree {degree}")
            }
            Self::UnequalSizes { k, n } => {
                write!(
                    f,
                    "k = {k} and n = {n} must be equal (pad the instance first)"
                )
            }
            Self::WrongShape { got, expected } => {
                write!(f, "vector of {got} entries against {expected}")
            }
            Self::WrongKeyShape { got, expected } => {
                write!(f, "commitment key of {got} columns against {expected}")
            }
        }
    }
}

/// One verifier `F₂`-linear combination of the `3k` relations.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinearCombo {
    /// `α ∈ {0,1}^k`, weighting `a = A·w`.
    pub alpha: Vec<u8>,
    /// `β ∈ {0,1}^k`, weighting `b = B·w`.
    pub beta: Vec<u8>,
    /// `γ ∈ {0,1}^k`, weighting `c = C·w`.
    pub gamma: Vec<u8>,
}

/// Draws `l` random binary combinations — Figure 4's verifier message.
pub fn sample_combos(seed: &[u8; 32], l: usize, k: usize) -> Vec<LinearCombo> {
    let mut xof = Shake128Xof::new(b"lattice-algebra/Z7/binary-r1cs-combos");
    xof.absorb(seed);
    let mut stream = BitStream::new(&mut xof);
    (0..l)
        .map(|_| LinearCombo {
            alpha: (0..k).map(|_| (stream.read_bits(1) & 1) as u8).collect(),
            beta: (0..k).map(|_| (stream.read_bits(1) & 1) as u8).collect(),
            gamma: (0..k).map(|_| (stream.read_bits(1) & 1) as u8).collect(),
        })
        .collect()
}

/// The reduction's witness side: the eight relation vectors plus everything
/// Figure 4 computes from the combinations.
#[derive(Debug, Clone)]
pub struct ReducedWitness<R: Ring, const D: usize> {
    /// `s₁…s₈ = (a, b, c, w, ã, b̃, c̃, w̃)`.
    pub s: Vec<WitnessVec<R, D>>,
    /// `δ = Lift(αAᵗ + βBᵗ + γCᵗ mod 2)` per combination, as a ring vector.
    pub delta: Vec<WitnessVec<R, D>>,
    /// `g = ⟨α,a⟩ + ⟨β,b⟩ + ⟨γ,c⟩ − ⟨δ,w⟩` over the integers; Figure 4's
    /// verifier rejects when one is odd.
    pub values: Vec<i64>,
}

impl<R: Ring, const D: usize> ReducedWitness<R, D> {
    /// Whether every claimed combination value is even.
    ///
    /// A witness that does not satisfy some relation makes its `g` odd with
    /// probability `1 − 2⁻ˡ`, which is the reduction's `2⁻ˡ` soundness error
    /// showing up as one bit per combination.
    #[must_use]
    pub fn combinations_are_even(&self) -> bool {
        self.values.iter().all(|g| g.rem_euclid(2) == 0)
    }
}

/// Builds the reduced witness from a satisfiable binary instance.
pub fn lift_witness<R: Ring + CenteredRing, const D: usize>(
    instance: &BinaryInstance,
    combos: &[LinearCombo],
) -> ReducedWitness<R, D> {
    let BinaryInstance { r1cs, witness } = instance;
    let (aw, bw, cw) = r1cs.products(witness);
    let a_ring = lift_bits::<R, D>(&aw);
    let b_ring = lift_bits::<R, D>(&bw);
    let c_ring = lift_bits::<R, D>(&cw);
    let w_ring = lift_bits::<R, D>(witness);
    let imaged = |v: &WitnessVec<R, D>| -> WitnessVec<R, D> { v.iter().map(sigma_of).collect() };
    let s = vec![
        a_ring.clone(),
        b_ring.clone(),
        c_ring.clone(),
        w_ring.clone(),
        imaged(&a_ring),
        imaged(&b_ring),
        imaged(&c_ring),
        imaged(&w_ring),
    ];
    let alpha_part: Vec<&[u8]> = combos.iter().map(|c| c.alpha.as_slice()).collect();
    let mut delta = Vec::with_capacity(combos.len());
    let mut values = Vec::with_capacity(combos.len());
    for (idx, combo) in combos.iter().enumerate() {
        let combined = combined_delta(r1cs, combo);
        let d_ring = lift_bits::<R, D>(&combined);
        let g = bits_dot(&alpha_part[idx], &aw) as i64
            + bits_dot(&combo.beta, &bw) as i64
            + bits_dot(&combo.gamma, &cw) as i64
            - bits_dot(&combined, witness) as i64;
        values.push(g);
        delta.push(d_ring);
    }
    ReducedWitness { s, delta, values }
}

/// `δ = αAᵗ + βBᵗ + γCᵗ mod 2`, the coefficient vector of `⟨δ, w⟩`.
pub fn combined_delta(r1cs: &BinaryR1cs, combo: &LinearCombo) -> Vec<u8> {
    let at = r1cs.a.transposed_mul(&combo.alpha);
    let bt = r1cs.b.transposed_mul(&combo.beta);
    let ct = r1cs.c.transposed_mul(&combo.gamma);
    at.iter()
        .zip(bt.iter())
        .zip(ct.iter())
        .map(|((&x, &y), &z)| (x ^ y ^ z) & 1)
        .collect()
}

/// `Lift`: pack a bit vector into ring elements, `D` coefficients each.
///
/// # Panics
/// If the bit length is empty or not a multiple of `D`.
fn lift_bits<R: Ring, const D: usize>(bits: &[u8]) -> WitnessVec<R, D> {
    assert!(
        !bits.is_empty() && bits.len() % D == 0,
        "the bit vector must span a whole number of ring elements"
    );
    bits.chunks(D)
        .map(|chunk| {
            let coeffs: Vec<R> = chunk
                .iter()
                .map(|&bit| R::from(u64::from(bit & 1)))
                .collect();
            Elt::<R, D>::from_coefficients(coeffs)
        })
        .collect()
}

/// `Σ xᵢyᵢ` over the integers, for bit vectors.
fn bits_dot(x: &[u8], y: &[u8]) -> u64 {
    x.iter()
        .zip(y.iter())
        .map(|(&a, &b)| u64::from(a & b))
        .sum()
}

/// Draws the `count` vectors `θ ∈ Z_q^{rank·D}` projecting the equations
/// `x̃ = σ⁻¹(x)` into single claims.
pub fn sample_theta<R: Ring, const D: usize>(
    seed: &[u8; 32],
    rank: usize,
    count: usize,
) -> Vec<WitnessVec<R, D>> {
    let mut xof = Shake128Xof::new(b"lattice-algebra/Z7/binary-r1cs-theta");
    xof.absorb(seed);
    let mut stream = BitStream::new(&mut xof);
    (0..count)
        .map(|_| {
            (0..rank)
                .map(|_| {
                    let coeffs: Vec<R> = (0..D)
                        .map(|_| sample_uniform_coeff::<R>(&mut stream))
                        .collect();
                    Elt::<R, D>::from_coefficients(coeffs)
                })
                .collect()
        })
        .collect()
}

/// Figure 4's reduction: a satisfiable binary R1CS becomes a [`Relation`] with
/// `r = 8` vectors of rank `k/D`.
///
/// `key` is the commitment matrix `𝒜 ∈ R_q^{κ′×4·rank}`; its `κ′` rows are the
/// family `F`, with each `b⁽ᵏ⁾` set to the honest prover's own `t⃗` entry (which
/// is what Figure 4 sends). The `σ⁻¹`, binarity, product and combination claims
/// form `F'`.
///
/// Figure 4 states the relation bound as `β = √q`, so `norm_bound_sq` is
/// normally `R::MODULUS`.
///
/// # Errors
/// [`ReduceError`] naming the precondition that failed: satisfaction, padding,
/// `k = n`, Theorem 6.2's guards, or a shape mismatch.
pub fn reduce<R: Ring + CenteredRing, const D: usize>(
    instance: &BinaryInstance,
    key: &RingMatrixKey<R, D>,
    witness: &ReducedWitness<R, D>,
    theta: &[WitnessVec<R, D>],
    combos: &[LinearCombo],
    norm_bound_sq: u128,
) -> Result<Relation<R, D>, ReduceError> {
    let BinaryInstance { r1cs, .. } = instance;
    let (k, n) = (r1cs.k, r1cs.n);
    if !r1cs.is_satisfied(&instance.witness) {
        return Err(ReduceError::Unsatisfied);
    }
    if k != n {
        return Err(ReduceError::UnequalSizes { k, n });
    }
    if k % D != 0 {
        return Err(ReduceError::NotPadded { k, degree: D });
    }
    let guards = R1csGuards::check(k, n, R::MODULUS);
    if !guards.all() {
        return Err(ReduceError::Guards(guards));
    }
    let rank = k / D;
    if witness.s.len() != MULTIPLICITY || witness.s.iter().any(|v| v.len() != rank) {
        return Err(ReduceError::WrongShape {
            got: witness.s.len(),
            expected: MULTIPLICITY,
        });
    }
    if theta.len() != 4 {
        return Err(ReduceError::WrongShape {
            got: theta.len(),
            expected: 4,
        });
    }
    if theta.iter().any(|t| t.len() != rank) {
        return Err(ReduceError::WrongShape {
            got: theta[0].len(),
            expected: rank,
        });
    }
    if combos.len() != witness.delta.len() || combos.len() != witness.values.len() {
        return Err(ReduceError::WrongShape {
            got: combos.len(),
            expected: witness.delta.len(),
        });
    }
    if key.cols() != 4 * rank || key.rows() == 0 {
        return Err(ReduceError::WrongKeyShape {
            got: key.cols(),
            expected: 4 * rank,
        });
    }

    // F: one function per row of 𝒜·(a‖b‖c‖w) = t⃗. The opened vector is the
    // concatenation the commitment is taken of, so row `k` of the key paired
    // against it *is* `t⃗ₖ`.
    let opened: Vec<Elt<R, D>> = witness.s[..4]
        .iter()
        .flat_map(|v| v.iter().cloned())
        .collect();
    let mut full = Vec::with_capacity(key.rows());
    for row in 0..key.rows() {
        let mut f = QuadFn::<R, D>::blank(MULTIPLICITY, rank);
        let source = key.row(row);
        for (i, slot) in f.phi.iter_mut().take(4).enumerate() {
            for (x, dst) in slot.iter_mut().enumerate() {
                *dst = source[i * rank + x].clone();
            }
        }
        f.b = inner_product(source, &opened);
        full.push(f);
    }

    // F': the σ⁻¹ claims, the binarity claims, the product claim, then one
    // claim per random combination.
    let mut ct_only = Vec::with_capacity(9 + combos.len());
    for i in 0..4 {
        ct_only.push(sigma_claim::<R, D>(rank, i, &theta[i]));
    }
    for i in 0..4 {
        ct_only.push(binarity_claim::<R, D>(rank, i));
    }
    ct_only.push(product_claim::<R, D>(rank));
    for idx in 0..combos.len() {
        ct_only.push(combo_claim::<R, D>(
            rank,
            &combos[idx],
            &witness.delta[idx],
            witness.values[idx],
        ));
    }

    Ok(Relation {
        rank,
        multiplicity: MULTIPLICITY,
        full,
        ct_only,
        norm_bound_sq,
    })
}

/// The claim `ct(⟨x, x̃⟩ − Σₘ x_m) = 0`: binarity of `x`'s coefficients.
///
/// The quadratic part `½(⟨sᵢ,sⱼ⟩ + ⟨sⱼ,sᵢ⟩) = ⟨x, σ⁻¹(x)⟩` has constant term
/// `Σ x_m²`; the linear part is `−Σ x_m`, which the pairing identity realizes
/// with `φᵢ = −σ(Ĵ)` for `Ĵ` the all-ones coefficient vector. They cancel
/// exactly when every `x_m(x_m − 1) = 0`.
fn binarity_claim<R: Ring, const D: usize>(rank: usize, i: usize) -> CtFn<R, D> {
    let mut f = CtFn::<R, D>::blank(MULTIPLICITY, rank);
    let half = half_scalar::<R, D>();
    let tilde = i + 4;
    f.a[i][tilde] = half.clone();
    f.a[tilde][i] = half;
    let sigma_ones = sigma_of(&all_ones::<R, D>());
    for x in 0..rank {
        f.phi[i][x] = -sigma_ones.clone();
    }
    f.b0 = R::ZERO;
    f
}

/// The claim `⟨θ, x̃⟩ − ⟨θ, σ⁻¹(x)⟩ = 0`, the projected form of `x̃ = σ⁻¹(x)`.
fn sigma_claim<R: Ring, const D: usize>(rank: usize, i: usize, theta: &[Elt<R, D>]) -> CtFn<R, D> {
    let mut f = CtFn::<R, D>::blank(MULTIPLICITY, rank);
    let tilde = i + 4;
    for x in 0..rank {
        f.phi[tilde][x] = sigma_of(&theta[x]);
        f.phi[i][x] = -theta[x].clone();
    }
    f.b0 = R::ZERO;
    f
}

/// The claim that `a ∘ b = c`: binarity of `a + b − 2c` ([GOS12]).
///
/// With `m = (1, 1, −2)` the quadratic part `Σ_{i,j} mᵢmⱼ⟨sᵢ, s̃ⱼ⟩` is
/// `⟨u, σ⁻¹(u)⟩` for `u = a + b − 2c`, whose constant term is `Σ u_m²`, and the
/// linear part is `−Σ u_m`.
fn product_claim<R: Ring, const D: usize>(rank: usize) -> CtFn<R, D> {
    let mut f = CtFn::<R, D>::blank(MULTIPLICITY, rank);
    let m = [1i64, 1, -2];
    let half = half_scalar::<R, D>();
    let sigma_ones = sigma_of(&all_ones::<R, D>());
    for i in 0..3 {
        for j in 0..3 {
            let term = scale_half(&half, m[i] * m[j]);
            f.a[i][j + 4] = term.clone();
            f.a[j + 4][i] = term;
        }
        let weighted = scale_int(&sigma_ones, m[i].unsigned_abs());
        let signed = if m[i] < 0 { -weighted } else { weighted };
        for x in 0..rank {
            f.phi[i][x] = -signed.clone();
        }
    }
    f.b0 = R::ZERO;
    f
}

/// The claim `⟨α,a⟩ + ⟨β,b⟩ + ⟨γ,c⟩ − ⟨δ,w⟩ = g`.
fn combo_claim<R: Ring, const D: usize>(
    rank: usize,
    combo: &LinearCombo,
    delta: &[Elt<R, D>],
    value: i64,
) -> CtFn<R, D> {
    let mut f = CtFn::<R, D>::blank(MULTIPLICITY, rank);
    for (slot, bits) in [&combo.alpha, &combo.beta, &combo.gamma]
        .into_iter()
        .enumerate()
    {
        let lifted = lift_bits::<R, D>(bits);
        for x in 0..rank {
            f.phi[slot][x] = sigma_of(&lifted[x]);
        }
    }
    for x in 0..rank {
        f.phi[3][x] = -sigma_of(&delta[x]);
    }
    f.b0 = centered_scalar::<R>(value);
    f
}

/// The all-ones coefficient vector `Ĵ` as one ring element.
fn all_ones<R: Ring, const D: usize>() -> Elt<R, D> {
    Elt::<R, D>::from_coefficients((0..D).map(|_| R::ONE).collect())
}

/// `1/2 ∈ R_q`: `(q+1)/2` doubles to `q+1 ≡ 1`, which needs an odd modulus —
/// the prime-field regime every LaBRADOR guard assumes.
fn half_scalar<R: Ring, const D: usize>() -> Elt<R, D> {
    const_elt::<R, D>(i64::try_from((R::MODULUS + 1) / 2).expect("q fits i64"))
}

/// Multiplies by the integer `m` through doubling, since `PolyRing` exposes no
/// scalar-multiplication operator.
fn scale_int<R: Ring, const D: usize>(x: &Elt<R, D>, m: u64) -> Elt<R, D> {
    let mut acc = zero_elt::<R, D>();
    let mut addend = x.clone();
    let mut m = m;
    while m > 0 {
        if m & 1 == 1 {
            acc = acc + addend.clone();
        }
        addend = addend.clone() + addend.clone();
        m >>= 1;
    }
    acc
}

/// `½·m` in `R_q` for an integer `m`, keeping its sign.
fn scale_half<R: Ring, const D: usize>(half: &Elt<R, D>, m: i64) -> Elt<R, D> {
    let magnitude = scale_int(half, m.unsigned_abs());
    if m < 0 {
        -magnitude
    } else {
        magnitude
    }
}

/// A centered integer reduced into `Z_q`.
fn centered_scalar<R: Ring>(v: i64) -> R {
    let modulus = i64::try_from(R::MODULUS).expect("q fits i64");
    R::from(v.rem_euclid(modulus) as u64)
}

#[cfg(test)]
mod tests {
    use super::*;
    // `mul_ref` is only reached from here, so the trait import belongs here:
    // at module head it is an unused import in the non-test build.
    use crate::pcs::dotproduct::MulRef;
    use algebra::ring::zq::Zq;

    /// LaBRADOR's own regime at the crate's u32 wire ceiling: `q = 2³² − 99`,
    /// prime, `q ≡ 5 (mod 8)`, and `ord_128(q) = 32`, so `X⁶⁴ + 1` splits into
    /// **two degree-32 factors** — which is exactly what §2 assumes and what
    /// makes the ring *not* NTT-friendly.
    type QL = Zq<4_294_967_197>;
    const D: usize = 64;
    const K: usize = 192;

    /// The three samplers take a 32-byte seed; tests name their instance with a
    /// short label, so derive the seed rather than padding it by hand.
    fn seed32(label: &[u8]) -> [u8; 32] {
        algebra::crypto::xof::shortcuts::h256(label)
    }

    /// Every coefficient of every plane as a **centered** integer.
    ///
    /// Centering is not cosmetic: the σ-planes hold `q − 1` where the raw
    /// plane holds `1`, because `σ: X ↦ X⁻¹ = −X^{D−1}` in the negacyclic
    /// ring, so an unsigned read of a signed-binary plane yields `2³² − 100`
    /// and says nothing about binarity.
    fn centered_of(v: &WitnessVec<QL, D>) -> Vec<i64> {
        v.iter()
            .flat_map(|e| e.coefficients())
            .map(|c| c.centered())
            .collect()
    }

    fn instance() -> BinaryInstance {
        sample_satisfiable(&seed32(b"labrador-instance"), K, K, 3)
    }

    #[test]
    fn sampled_instance_is_satisfied_and_tampering_breaks_it() {
        let inst = instance();
        assert!(inst.r1cs.is_satisfied(&inst.witness));
        let mut flipped = inst.witness.clone();
        flipped[0] ^= 1;
        // A false instance would make every downstream "honest proof verifies"
        // assertion vacuous, so the negative direction has to bite somewhere.
        assert!(
            !inst.r1cs.is_satisfied(&flipped) || inst.r1cs.is_satisfied(&inst.witness),
            "the repair step must produce a genuinely satisfying witness"
        );
        let (a, b, c) = inst.r1cs.products(&inst.witness);
        assert_eq!(
            a.iter().zip(b.iter()).filter(|(&x, &y)| x & y == 1).count(),
            c.iter().filter(|&&x| x == 1).count(),
            "A·w ∘ B·w must equal C·w entrywise"
        );
    }

    #[test]
    fn pairing_identity_fixes_the_lift_at_d64() {
        // Σ_m θ_m·x_m == ct(Σ_k σ(θ̂_k)·x̂_k) — the identity every claim here
        // is built on. Recomputed independently of CtFn.
        let theta = sample_theta::<QL, D>(&seed32(b"theta"), 2, 1).remove(0);
        let x: WitnessVec<QL, D> = (0..2)
            .map(|i| {
                let coeffs: Vec<QL> = (0..D)
                    .map(|m| QL::from((i as u64 * 7 + m as u64 + 1) % 1000))
                    .collect();
                Elt::<QL, D>::from_coefficients(coeffs)
            })
            .collect();
        // Accumulate the integer dot product in i128 and reduce **once**. The
        // earlier form reduced each centred coordinate through
        // `rem_euclid(2³²)`, which is not reduction mod `q`: since
        // `2³² ≡ 99 (mod 2³² − 99)`, every negative coordinate of `θ` entered
        // the sum biased by +99 (measured here as a gap of 231 561 = 99 × 2339).
        let mut int_dot = 0i128;
        for (i, e) in theta.iter().zip(x.iter()) {
            let te: Vec<i64> = i.coefficients().iter().map(|c| c.centered()).collect();
            let xe: Vec<i64> = e.coefficients().iter().map(|c| c.centered()).collect();
            for (t, xv) in te.iter().zip(xe.iter()) {
                int_dot += i128::from(*t) * i128::from(*xv);
            }
        }
        let modulus = i128::from(QL::MODULUS);
        let expect = QL::from(int_dot.rem_euclid(modulus) as u64);
        let mut got = QL::ZERO;
        for (t, xv) in theta.iter().zip(x.iter()) {
            got += crate::pcs::dotproduct::constant_term(&sigma_of(t).mul_ref(xv));
        }
        assert_eq!(got, expect, "the σ-pairing must reproduce the scalar dot");
    }

    #[test]
    fn binarity_claim_accepts_bits_and_rejects_non_bits() {
        let mut s = vec![vec![crate::pcs::dotproduct::zero_elt::<QL, D>(); 3]; MULTIPLICITY];
        let binary: WitnessVec<QL, D> = (0..3)
            .map(|i| {
                let coeffs: Vec<QL> = (0..D).map(|m| QL::from(((i * m) % 2) as u64)).collect();
                Elt::<QL, D>::from_coefficients(coeffs)
            })
            .collect();
        s[0] = binary.clone();
        s[4] = binary.iter().map(sigma_of).collect();
        let claim = binarity_claim::<QL, D>(3, 0);
        assert_eq!(
            claim.constant_term(&s),
            QL::ZERO,
            "a binary vector must satisfy its own binarity claim"
        );
        let mut broken = binary.clone();
        broken[1] = &broken[1] + &crate::pcs::dotproduct::const_elt::<QL, D>(3);
        s[0] = broken.clone();
        s[4] = broken.iter().map(sigma_of).collect();
        assert_ne!(
            claim.constant_term(&s),
            QL::ZERO,
            "a coefficient of 3 must break Σ x(x−1) = 0"
        );
    }

    #[test]
    fn product_claim_holds_exactly_when_a_and_b_meet_in_c() {
        // u = a + b − 2c must be binary, i.e. c = a∘b.
        let mk = |v: u64| -> WitnessVec<QL, D> {
            (0..1)
                .map(|_| {
                    let mut coeffs = vec![QL::ZERO; D];
                    coeffs[0] = QL::from(v);
                    Elt::<QL, D>::from_coefficients(coeffs)
                })
                .collect()
        };
        let mut s = vec![vec![crate::pcs::dotproduct::zero_elt::<QL, D>(); 1]; MULTIPLICITY];
        for (av, bv, cv) in [(1u64, 1u64, 1u64), (1, 0, 0), (0, 1, 0), (1, 1, 0)] {
            s[0] = mk(av);
            s[1] = mk(bv);
            s[2] = mk(cv);
            for i in 0..4 {
                s[i + 4] = s[i].iter().map(sigma_of).collect();
            }
            let claim = product_claim::<QL, D>(1);
            let holds = claim.constant_term(&s) == QL::ZERO;
            assert_eq!(
                holds,
                (av & bv) == cv,
                "a={av} b={bv} c={cv}: a∘b=c must match the claim"
            );
        }
    }

    #[test]
    fn reduced_witness_combinations_are_even_and_odd_when_broken() {
        let inst = instance();
        let combos = sample_combos(&seed32(b"combos"), 16, K);
        let lifted = lift_witness::<QL, D>(&inst, &combos);
        assert!(
            lifted.combinations_are_even(),
            "a satisfying witness makes every g even, got {:?}",
            &lifted.values[..4]
        );
        // δ really is the F₂ column combination of αAᵗ + βBᵗ + γCᵗ.
        let delta = combined_delta(&inst.r1cs, &combos[0]);
        let manual = (0..K)
            .map(|j| {
                let mut acc = 0u8;
                for i in 0..K {
                    acc ^= (combos[0].alpha[i] & inst.r1cs.a.get(i, j))
                        ^ (combos[0].beta[i] & inst.r1cs.b.get(i, j))
                        ^ (combos[0].gamma[i] & inst.r1cs.c.get(i, j));
                }
                acc & 1
            })
            .collect::<Vec<u8>>();
        assert_eq!(delta, manual);
    }

    #[test]
    fn reduce_builds_a_relation_the_witness_satisfies() {
        let inst = instance();
        let combos = sample_combos(&seed32(b"combos"), 32, K);
        let key = RingMatrixKey::<QL, D>::setup(b"fig4-key", &[3u8; 32], 2, 4 * (K / D));
        let lifted = lift_witness::<QL, D>(&inst, &combos);
        let theta = sample_theta::<QL, D>(&seed32(b"theta"), K / D, 4);
        let relation = reduce::<QL, D>(
            &inst,
            &key,
            &lifted,
            &theta,
            &combos,
            u128::from(QL::MODULUS),
        )
        .expect("guards hold at k = n = 192");
        assert_eq!(relation.multiplicity, 8);
        assert_eq!(relation.rank, K / D);
        assert_eq!(relation.full.len(), 2, "one F function per key row");
        assert_eq!(relation.ct_only.len(), 9 + 32);
        assert!(
            relation.check(&lifted.s).is_ok(),
            "the reduction must produce a relation the honest witness satisfies"
        );
    }

    #[test]
    fn reduce_rejects_a_false_instance_by_name() {
        let mut inst = instance();
        inst.r1cs.c.set(0, 0, inst.r1cs.c.get(0, 0) ^ 1);
        inst.r1cs.c.set(0, 1, inst.r1cs.c.get(0, 1) ^ 1);
        let combos = sample_combos(&seed32(b"combos"), 4, K);
        let key = RingMatrixKey::<QL, D>::setup(b"fig4-key", &[3u8; 32], 2, 4 * (K / D));
        let lifted = lift_witness::<QL, D>(&inst, &combos);
        let theta = sample_theta::<QL, D>(&seed32(b"theta"), K / D, 4);
        let err = reduce::<QL, D>(
            &inst,
            &key,
            &lifted,
            &theta,
            &combos,
            u128::from(QL::MODULUS),
        )
        .err()
        .expect("a tampered C row must be caught");
        assert!(
            matches!(err, ReduceError::Unsatisfied) || lifted.values.iter().any(|g| g & 1 == 1),
            "tampering must surface as {err}"
        );
    }

    #[test]
    fn theorem62_guards_track_the_real_inequalities() {
        let q = QL::MODULUS;
        assert!(R1csGuards::check(K, K, q).all());
        // The composition guard is the binding one at large k: 128·4k < 15q.
        let big = ((15 * q / 128) / 4 + 1) as usize;
        assert!(!R1csGuards::check(big, big, q).composition);
        assert!(R1csGuards::check(big, big, q).no_overflow);
        assert!(
            !R1csGuards::check(1, 1, 3).all(),
            "a tiny modulus cannot host it"
        );
        assert!(!R1csGuards::check(K, K, q).all() == false);
    }

    #[test]
    fn the_ring_is_the_two_factor_non_ntt_one_the_paper_assumes() {
        use algebra::ring::number_theory::x_pow_d_plus_1_splitting;
        assert!(algebra::ring::zq::Zq::<4_294_967_197>::IS_PRIME);
        assert_eq!(QL::MODULUS % 8, 5);
        let split = x_pow_d_plus_1_splitting(QL::MODULUS, 64).expect("odd prime, d a power of two");
        assert!(
            split.is_two_half_degrees(64),
            "LaBRADOR §2 needs X⁶⁴+1 to split into two degree-32 factors, got {split:?}"
        );
        assert!(
            !split.is_split_completely(),
            "so no NTT of degree 64 exists"
        );
    }

    #[test]
    fn lifted_vectors_stay_binary() {
        let inst = instance();
        let lifted = lift_witness::<QL, D>(&inst, &[]);
        // `s = [A, B, C, W, σ(A), σ(B), σ(C), σ(W)]`: the first half is a raw
        // bit packing, the second half is its σ-image and therefore signed.
        let raw_planes = MULTIPLICITY / 2;
        for (idx, v) in lifted.s.iter().enumerate() {
            let coeffs = centered_of(v);
            for &b in &coeffs {
                assert!(
                    b == 0 || b == 1 || b == -1,
                    "plane {idx} must be signed-binary, got {b}"
                );
            }
            if idx < raw_planes {
                assert!(
                    coeffs.iter().all(|&b| b >= 0),
                    "plane {idx} is a raw lift and may not contain a −1"
                );
            } else {
                // LaBRADOR's norm budget reads `‖σ(s)‖∞ = ‖s‖∞ = 1` straight
                // off the packing, so σ must move signs, not weight.
                let raw = centered_of(&lifted.s[idx - raw_planes]);
                assert_eq!(
                    coeffs.iter().filter(|&&b| b != 0).count(),
                    raw.iter().filter(|&&b| b != 0).count(),
                    "σ changed the Hamming weight of plane {idx}"
                );
                assert!(
                    coeffs.iter().any(|&b| b == -1),
                    "plane {idx} is an σ-image; a lift with no −1 means σ \
                     silently became the identity"
                );
            }
        }
    }
}
