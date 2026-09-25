//! Rotation matrices: ring multiplication as coefficient-level linear algebra.
//!
//! Every other matrix in the crate acts *in the ring*:
//! [`RingMatrixKey`](crate::pcs::key::RingMatrixKey) multiplies ring entries,
//! [`BlockMat`] contracts ring rows. A verifier that folds a ring constraint
//! row that way pays `d` ring multiplications per entry, i.e. `O(d²)` field
//! operations, because it never stops to notice that multiplication by a
//! *fixed* ring element is a linear map on the `d` coefficients.
//!
//! Everything below is transcription from that paper, with cites. `eprint
//! 2026/1196` prints `rot` and `M_a` twice — once in the overview (§1.3, p. 7,
//! eq. (5)) and once in the construction (§3.2.1, p. 18, eq. (17)) — and the two
//! printings are identical:
//!
//! ```text
//! rot : F_q^d → F_q^d,   rot(a₀, …, a_{d−1}) = (−a_{d−1}, a₀, …, a_{d−2})
//! M_a := [cf(a), rot cf(a), …, rot^{d−1} cf(a)] ∈ F_q^{d×d}
//! ```
//!
//! `rot` is multiplication by `X` (`X·a = a₀X + … + a_{d−2}X^{d−1} + a_{d−1}X^d`
//! and `X^d = −1` in `R_q`), so column `j` of `M_a` is `cf(X^j a)` and
//! `a·b = Σ_j b_j·X^j a` gives, verbatim eq. (6)–(7) of p. 7,
//!
//! ```text
//! M_a · cf(b) = cf(c)   whenever   a·b = c          (eq. 17, §3.2.1 p. 18)
//! ```
//!
//! so a ring matrix `M ∈ R_q^{n×m}` expands to a coefficient matrix
//! `M̃ ∈ F_q^{(nd)×(md)}` of `d×d` blocks and `Mx = y` over `R_q` *is* the same
//! relation over `F_q` — which is what lets a sumcheck run on coefficients
//! instead of on ring elements.
//!
//! # Why the fold is `O(d)` and not `O(d²)`
//!
//! Hachi's route (§1.3 p. 8, eq. (8)) verifies `α⊤Mx = α⊤y` by sumchecking the
//! *two* table arguments of the matrix–vector product,
//!
//! ```text
//! Σ_{a,b ∈ {0,1}^{log d}}  α̃(a)·M̃(a,b)·x̃(b)            (eq. 8, p. 8)
//! ```
//!
//! which is quadratic in `d` for the verifier. Baking the `α` fold into the
//! matrix collapses it to one table (eq. (9), p. 8)
//!
//! ```text
//! Σ_{b ∈ {0,1}^{log d}}  (αM)~(b)·x̃(b)                  (eq. 9, p. 8)
//! ```
//!
//! and the paper then claims (§1.3, p. 8) the headline step: "the vector
//! `αM_a` can be computed in time `O(d)`. Firstly, compute the inner product
//! `α·cf(a)`. Next, `α·rot(cf(a))` can be computed as
//! `(α·cf(a) − a_{d−1}α^{d−1})·α − a_{d−1}`, and the same approach can be
//! applied to compute the rest of the entries."
//!
//! Writing `f_j := α·rot^j cf(a)` — with `α` the Vandermonde *row*
//! `(1, α, …, α^{d−1})`, so `f` is `αM_a` read column by column — that recursion
//! is one term: `rot` shifts every coefficient up by one and pushes the old
//! `u_{d−1}` through the `X^d = −1` wrap, so for `u = rot^j cf(a)`
//!
//! ```text
//! f_{j+1} = α·rot(u) = Σ_{i<d−1} u_i α^{i+1} − u_{d−1}
//!         = α·f_j − u_{d−1}·(α^d + 1)
//! f₀      = Σ_k α^k a_k
//! ```
//!
//! and since `u_{d−1} = a_{d−1−j}` never wraps for `j ≤ d−1` (the last
//! coordinate walks `a_{d−1}, a_{d−2}, …` down the coefficient vector), the whole
//! row costs `O(d)` field multiplications with no rotation materialised. The
//! paper's printed first step is exactly this instance:
//! `(αcf(a) − a_{d−1}α^{d−1})α − a_{d−1} = α f₀ − a_{d−1}(α^d + 1)`.
//!
//! That difference is *measured*, not just claimed: the test
//! `the_fast_fold_costs_linearly_and_the_expansion_quadratically` runs
//! [`fold_row`] on an operation-counting field and asserts its multiplication
//! count is `4d − 1` while the explicit contraction of [`multiplication_matrix`]
//! costs `d²` — and asserts in the same breath that the two routes return the
//! *same* vector, so the cheap one cannot be cheap because it does less work than
//! required.
//!
//! [`fold_row`] implements the recurrence, [`fold_matrix`] the row-and-block fold
//! `βMα` of eq. (10) (p. 8) / eq. (18) (p. 18), and the tests pin both against
//! the `O(d²)` contraction of the explicit `M_a`.
//!
//! # The `n × m` fold: eq. (10) and eq. (18)
//!
//! For a ring matrix `M = (M_{i,j}) ∈ R_q^{n×m}` whose entries each carry their
//! own multiplication matrix, the paper folds every block by `α` and then the
//! ring rows by `β := (1, β, …, β^{n−1})`, `β ∈ F_{q^k}`:
//!
//! ```text
//! βMα := β [ αM₁,₁  …  αM₁,ₘ ]                (eq. 10 p. 8, eq. 18 p. 18)
//!          ⋱        ⋱
//!          [ αMₙ,₁  …  αMₙ,ₘ ]
//!
//! Σ_{b ∈ {0,1}^{log md}} (βMα)~(b)·x̃(b)                     (eq. 11, p. 8)
//! ```
//!
//! where the second line is the paper's "bake the folding by `β` of `Mα` into a
//! single polynomial" step, so the verifier's sumcheck ranges over `log(md)`
//! variables instead of `2·log(md)`.
//!
//! and the contract that makes it a proof is `⟨βMα, cf(x)⟩ = ⟨β⊗α, cf(Mx)⟩`,
//! which the test `fold_contracts_against_the_ring_product` pins.
//!
//! # Row-tensor (vSIS-shaped) matrices
//!
//! A structured public-parameter matrix whose column index is a bit string,
//!
//! ```text
//! A[i, b] = Π_k F_k[i, b_k]        F_k ∈ R_q^{n×2}
//! ```
//!
//! (the "iterated row-tensor product" of Def. 2.2, p. 12 — `A = A₀⊗A₁⊗…⊗A_{µ−1}`
//! with `A_i ∈ R_q^{n×2}` — read as an *entrywise* product so that the row count
//! stays `n`; see the struct docs for why no other reading typechecks) has a
//! partial evaluation that costs `µ` ring products instead of `2^µ`: rotation
//! matrices are multiplicative (`M_a M_b = M_{ab}`) and `F_q`-linear, so
//!
//! ```text
//! Σ_b eq(b, e)·M_{A[i,b]} = Π_k ((1−e_k)M_{F_k[i,0]} + e_k M_{F_k[i,1]})
//! ```
//!
//! which is the verifier step of §3.2.2 (pp. 19–20), printed on p. 9 as
//!
//! ```text
//! (β⊗α) [ Π_{i=1}^{log m} (I_d(1−e_i) + M_{1,i}e_i) … ]_{row} e′
//! ```
//!
//! with the note that "each entry can be computed using log n multiplications
//! over `R_{q^k}`". Two things the paper does **not** say, and this module
//! therefore handles the more general way:
//!
//! * The printed factor `(1−e_i)I_d + e_i M_{*,i}` is only that product's `0`
//!   branch **if `F_k[i,0] = 1`**, i.e. if the tensor's first column is the
//!   constant polynomial `1`. Def. 2.2 never says so — `X_{n,µ}` is left
//!   completely unspecified. [`RowTensor`] takes arbitrary factors, so
//!   [`RowTensor::column_mle`] carries an `M_{F_k[i,0]}` that the paper's formula
//!   silently replaces by `I_d`; [`RowTensor::new`] is general and the test
//!   `row_tensor_with_unit_first_choice_gives_the_paper_factor` pins the special
//!   case the paper writes.
//! * `e′` — "the evaluation vector for the remaining log md − log m entries",
//!   p. 9 — is which variables pair with which index; the convention adopted here
//!   is the one [`evaluation_vector`] documents, and it is pinned by comparing
//!   against an expansion rather than by another formula.
//!
//! [`RowTensor`] carries both sides: [`RowTensor::to_block`] is the expansion,
//! [`RowTensor::column_mle`] the product formula, [`RowTensor::ring_mle`] its
//! ring-level twin and [`RowTensor::folded_row_mle`] that formula after the `α`
//! fold.
//!
//! Layering: `foundation → pcs::projection → pcs::rotation`. Nothing here is
//! scheme-specific, and nothing here needs an NTT — the tests run on
//! `q = 2³² − 99`, whose 2-adicity is 2.

use crate::pcs::mixed::BlockMat;
use crate::pcs::projection::{dot, to_coeffs, FieldMat};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// The negacyclic coefficient rotation
/// `rot(a₀, …, a_{d−1}) = (−a_{d−1}, a₀, …, a_{d−2})` — multiplication by `X`
/// in `Z_q[X]/(X^d + 1)`.
///
/// # Panics
/// If `v` is empty (there is no `d = 0` cyclotomic).
pub fn rot<R: Ring>(v: &[R]) -> Vec<R> {
    assert!(!v.is_empty(), "rotation needs at least one coefficient");
    let mut out = v.to_vec();
    let last = out.pop().expect("checked non-empty");
    core::iter::once(-last).chain(out).collect()
}

/// The Vandermonde row `(1, α, α², …, α^{n−1})`.
pub fn powers<R: Ring>(alpha: &R, n: usize) -> Vec<R> {
    let mut out = Vec::with_capacity(n);
    let mut acc = R::ONE;
    for _ in 0..n {
        out.push(acc);
        acc *= *alpha;
    }
    out
}

/// The ring element `1`, as a constant polynomial in degree `D`.
pub fn one_poly<R: Ring, const D: usize>() -> PolyRing<R, D> {
    let mut coeffs = vec![R::ZERO; D];
    coeffs[0] = R::ONE;
    PolyRing::from_coefficients(coeffs)
}

/// The `D × D` identity over the coefficient field.
pub fn identity_field_mat<R: Ring, const D: usize>() -> FieldMat<R> {
    let mut data = vec![R::ZERO; D * D];
    for i in 0..D {
        data[i * D + i] = R::ONE;
    }
    FieldMat::from_entries(D, D, data)
}

/// Entrywise `f` over two equally shaped coefficient-level matrices.
///
/// # Panics
/// If the shapes differ.
pub fn zip_entries<R: Ring>(
    a: &FieldMat<R>,
    b: &FieldMat<R>,
    f: impl Fn(&R, &R) -> R,
) -> FieldMat<R> {
    assert_eq!(
        (a.rows(), a.cols()),
        (b.rows(), b.cols()),
        "entrywise combination needs equal shapes"
    );
    let mut data = Vec::with_capacity(a.rows() * a.cols());
    for i in 0..a.rows() {
        for j in 0..a.cols() {
            data.push(f(
                a.get(i, j).expect("in range"),
                b.get(i, j).expect("in range"),
            ));
        }
    }
    FieldMat::from_entries(a.rows(), a.cols(), data)
}

/// The multiplication matrix `M_a ∈ F_q^{d×d}` of eq. (17): column `j` is
/// `rot^j(cf(a))`, so `M_a·cf(b) = cf(a·b)`.
pub fn multiplication_matrix<R: Ring, const D: usize>(a: &PolyRing<R, D>) -> FieldMat<R> {
    let mut data = vec![R::ZERO; D * D];
    let mut col = to_coeffs(core::slice::from_ref(a));
    for j in 0..D {
        for i in 0..D {
            data[i * D + j] = col[i];
        }
        col = rot(&col);
    }
    FieldMat::from_entries(D, D, data)
}

/// `α·M_a` for the Vandermonde row `α = (1, α, …, α^{d−1})`, in `O(d)`.
///
/// This is the paper's §1.3/p. 8 claim ("`αM_a` can be computed in time `O(d)`")
/// and §3.2.1/p. 18's "`given the structure of M_a` the vector `αM` can be
/// computed in `O(d)` time" — the step that buys the linear rather than quadratic
/// per-row verifier, and therefore what a verifier computes per constraint entry.
///
/// Concretely the returned vector is `f_j = α · rot^j cf(a)` for `j = 0..d`,
/// computed by the one-term recurrence derived in the module docs:
///
/// ```text
/// f₀      = Σ_k α^k a_k                       (d multiplications)
/// f_{j+1} = α·f_j − (α^d + 1)·a_{d−1−j}       (2 multiplications, j = 0..d−2)
/// ```
///
/// The index `d−1−j` never needs a modulus: for `j ≤ d−1` the coordinate
/// `rot^j cf(a)` pushes into the wrap is always a genuine `a_k`, so the negacyclic
/// sign is carried entirely by the `(α^d + 1)` factor. Total `4d − 1`
/// multiplications including the `powers` seed, against the `d²` of contracting
/// the explicit [`multiplication_matrix`]; the test
/// `the_fast_fold_costs_linearly_and_the_expansion_quadratically` counts them.
///
/// # Panics
/// If `D == 0`, on the `D − 1` loop bound. `d = 0` is not a cyclotomic degree, so
/// no caller reaches this.
pub fn fold_row<R: Ring, const D: usize>(alpha: &R, a: &PolyRing<R, D>) -> Vec<R> {
    let cf = to_coeffs(core::slice::from_ref(a));
    let pw = powers(alpha, D + 1);
    let wrap = pw[D] + R::ONE;
    let mut f = Vec::with_capacity(D);
    f.push(dot(&pw[..D], &cf));
    for j in 0..D - 1 {
        let prev = *f.last().expect("seeded with f_0");
        let last = cf[(D - 1 - j) % D];
        f.push(*alpha * prev - wrap * last);
    }
    f
}

/// The coefficient-level expansion `M̃ ∈ F_q^{(nd)×(md)}` of a ring matrix:
/// block `(i, j)` is `M_{M[i,j]}`, with row index `i·d + k` and column index
/// `j·d + l` (matching [`to_coeffs`]).
///
/// This is the `O(d²)` object the folds below avoid building; it is exposed
/// because "the expansion is a ring homomorphism" is precisely what a test
/// needs the fast route checked against.
pub fn expand_matrix<R: Ring, const D: usize>(m: &BlockMat<R, D>) -> FieldMat<R> {
    let (rows, cols) = (m.rows(), m.cols());
    let mut data = vec![R::ZERO; rows * D * cols * D];
    for i in 0..rows {
        for j in 0..cols {
            let block = multiplication_matrix(&m.row(i)[j]);
            for k in 0..D {
                for l in 0..D {
                    data[(i * D + k) * (cols * D) + j * D + l] = *block.get(k, l).expect("square");
                }
            }
        }
    }
    FieldMat::from_entries(rows * D, cols * D, data)
}

/// `β·M·α` — eq. (18): fold every block of the ring matrix `M` with the
/// Vandermonde row of `α`, then combine the ring rows with the weights `β`.
///
/// The result is indexed `j·d + k` (`k` fastest), i.e. it is the row vector
/// with `⟨βMα, cf(x)⟩ = ⟨β⊗α, cf(Mx)⟩` for every `x` — the statement the
/// sumcheck of eq. (19) proves. Cost `O(rows·cols·d)`: [`fold_row`] re-derives
/// the Vandermonde row per block, so the constant is `4d − 1` multiplications
/// per entry rather than the `3d − 2` a caller that hoists `powers(α, d + 1)`
/// out of the block loop would pay. Either way the dependence on `d` is linear,
/// which is the paper's claim; hoisting is left to the caller rather than
/// traded for a second entry point.
///
/// # Panics
/// Unless `beta.len() == m.rows()`.
pub fn fold_matrix<R: Ring, const D: usize>(beta: &[R], alpha: &R, m: &BlockMat<R, D>) -> Vec<R> {
    assert_eq!(beta.len(), m.rows(), "beta must weight every ring row");
    let mut out = vec![R::ZERO; m.cols() * D];
    for (i, w) in beta.iter().enumerate() {
        for j in 0..m.cols() {
            for (k, v) in fold_row(alpha, &m.row(i)[j]).iter().enumerate() {
                out[j * D + k] += *w * *v;
            }
        }
    }
    out
}

/// The evaluation vector `eq(·, e) ∈ F_q^{2^µ}` of the multilinear equality
/// polynomial: entry `b` is `Π_i (e_i if bit i of b is set, else 1 − e_i)`,
/// with bit `i` the `i`-th variable (the [`crate::sumcheck`] index convention).
///
/// Contracting it against a table is that table's multilinear extension at `e`,
/// which is what a verifier evaluates to close a sumcheck.
pub fn evaluation_vector<R: Ring>(point: &[R]) -> Vec<R> {
    let n = 1usize << point.len();
    let mut out = Vec::with_capacity(n);
    for b in 0..n {
        let mut acc = R::ONE;
        for (i, p) in point.iter().enumerate() {
            acc *= if (b >> i) & 1 == 1 { *p } else { R::ONE - *p };
        }
        out.push(acc);
    }
    out
}

/// Why a row-tensor matrix refused its input shape.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TensorShapeError {
    /// What was supplied, as `rows * 1000 + cols` (or `0` for no factors).
    pub got: usize,
    /// What the structure requires, in the same encoding.
    pub expected: usize,
}

impl fmt::Display for TensorShapeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "row-tensor shape mismatch: got {}, expected {}",
            self.got, self.expected
        )
    }
}

/// A row-tensor ("vSIS-shaped") matrix `A ∈ R_q^{n×2^µ}` with
/// `A[i, b] = Π_k F_k[i, b_k]`, built from `µ` factors `F_k ∈ R_q^{n×2}`.
///
/// The product is *entrywise over the ring*, so all factors share the row
/// count `n` and only the column index grows. That is the structure making
/// [`RowTensor::column_mle`] a `µ`-step product, and it is what the paper's
/// `X_{n,µ}` is supposed to sample.
///
/// # Reading Def. 2.2 (p. 12), and why it has to be this one
///
/// Def. 2.2 writes `A = A₀ ⊗ A₁ ⊗ ··· ⊗ A_{µ−1}` with `A_i ∈ R_q^{n×2}`, and
/// Table 1 (p. 11) insists `A ∈ R_q^{n×2^µ}` — an `n`-row matrix with `2^µ`
/// columns. The ordinary Kronecker product of `µ` such factors is
/// `n^µ × 2^µ`, which contradicts Table 1, so the "iterated *row*-tensor product"
/// has to be the entrywise column product adopted here. Supporting evidence is
/// the p. 9 product formula (§1.3; the construction repeats it in §3.2.2,
/// pp. 19–20), which is exactly the factorisation this reading gives — and which
/// is *false* for any reading where the row index also grows. The paper never
/// states it either way, and defines neither "vanishing" nor `X_{n,µ}` beyond "a
/// distribution over" that domain, offers no reduction from a known assumption
/// and no parameter table; see also `docs/survey-lattice-pcs.md`, which flags the
/// same gap. Everything here is therefore a *documented choice*, and
/// [`crate::pcs::rotation`] makes the structure explicit rather than the
/// paper's silent `A[i,0] = 1`.
#[derive(Clone, PartialEq, Eq)]
pub struct RowTensor<R: Ring, const D: usize> {
    factors: Vec<BlockMat<R, D>>,
}

impl<R: Ring, const D: usize> fmt::Debug for RowTensor<R, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "RowTensor({} factors, {}×{})",
            self.factors.len(),
            self.rows(),
            self.cols()
        )
    }
}

impl<R: Ring, const D: usize> RowTensor<R, D> {
    /// Wraps `µ` factors, each an `n × 2` ring matrix with the same `n`.
    ///
    /// # Errors
    /// [`TensorShapeError`] if there are no factors, or one is not `n × 2`.
    pub fn new(factors: &[BlockMat<R, D>]) -> Result<Self, TensorShapeError> {
        let rows = factors
            .first()
            .ok_or(TensorShapeError {
                got: 0,
                expected: 1,
            })?
            .rows();
        for f in factors {
            if f.cols() != 2 || f.rows() != rows {
                return Err(TensorShapeError {
                    got: f.rows() * 1000 + f.cols(),
                    expected: rows * 1000 + 2,
                });
            }
        }
        Ok(Self {
            factors: factors.to_vec(),
        })
    }

    /// Row count `n` (shared by every factor).
    pub fn rows(&self) -> usize {
        self.factors[0].rows()
    }

    /// Column count `2^µ`.
    pub fn cols(&self) -> usize {
        1usize << self.factors.len()
    }

    /// Number of factors `µ`.
    pub fn depth(&self) -> usize {
        self.factors.len()
    }

    /// Factor `k`.
    ///
    /// # Panics
    /// If `k >= depth`.
    pub fn factor(&self, k: usize) -> &BlockMat<R, D> {
        assert!(k < self.factors.len(), "factor index out of range");
        &self.factors[k]
    }

    /// Entry `(row, col)`, with `col` expanded into its bit string.
    pub fn get(&self, row: usize, col: usize) -> Option<PolyRing<R, D>> {
        if row >= self.rows() || col >= self.cols() {
            return None;
        }
        let mut acc = one_poly::<R, D>();
        for (k, f) in self.factors.iter().enumerate() {
            acc *= f.row(row)[(col >> k) & 1].clone();
        }
        Some(acc)
    }

    /// The explicit `n × 2^µ` expansion — the `O(2^µ)` reference this structure
    /// exists to avoid.
    pub fn to_block(&self) -> BlockMat<R, D> {
        let data = (0..self.rows())
            .flat_map(|i| (0..self.cols()).map(move |b| self.get(i, b).expect("in range")))
            .collect();
        BlockMat::new(self.rows(), self.cols(), data).expect("self-shaped")
    }

    /// `Σ_b eq(b, e)·M_{A[i,b]}` as the `µ`-step product
    /// `Π_k ((1−e_k)M_{F_k[i,0]} + e_k M_{F_k[i,1]})`.
    ///
    /// # Panics
    /// Unless `point.len() == depth` and `row < rows`.
    pub fn column_mle(&self, row: usize, point: &[R]) -> FieldMat<R> {
        assert_eq!(
            point.len(),
            self.depth(),
            "one evaluation coordinate per factor"
        );
        assert!(row < self.rows(), "row index out of range");
        let mut acc = identity_field_mat::<R, D>();
        for (k, p) in point.iter().enumerate() {
            let f = self.factor(k);
            let m0 = multiplication_matrix(&f.row(row)[0]);
            let m1 = multiplication_matrix(&f.row(row)[1]);
            let one_minus = R::ONE - *p;
            let combined = zip_entries(&m0, &m1, |a, b| one_minus * *a + *p * *b);
            acc = acc.matmul(&combined).expect("square blocks");
        }
        acc
    }

    /// The ring-level companion of [`RowTensor::column_mle`]:
    /// `Σ_b eq(b, e)·A[i,b] = Π_k ((1−e_k)F_k[i,0] + e_k F_k[i,1])`, one ring
    /// element rather than a `d × d` matrix.
    ///
    /// # Panics
    /// Unless `point.len() == depth` and `row < rows`.
    pub fn ring_mle(&self, row: usize, point: &[R]) -> PolyRing<R, D> {
        assert_eq!(point.len(), self.depth(), "one coordinate per factor");
        assert!(row < self.rows(), "row index out of range");
        let mut acc = one_poly::<R, D>();
        for (k, p) in point.iter().enumerate() {
            let f = self.factor(k);
            let one_minus = R::ONE - *p;
            let a = to_coeffs(&[f.row(row)[0].clone()]);
            let b = to_coeffs(&[f.row(row)[1].clone()]);
            let combo = PolyRing::from_coefficients(
                a.iter()
                    .zip(b.iter())
                    .map(|(x, y)| one_minus * *x + *p * *y)
                    .collect(),
            );
            acc *= combo;
        }
        acc
    }

    /// `α · Σ_b eq(b, e)·M_{A[i,b]}` — the folded partial evaluation the
    /// verifier of a ring-matrix sumcheck needs, in `O(µ·d² + d²)` rather than
    /// `O(2^µ·d²)`.
    ///
    /// The fold is a **row** contraction, `(αM)[j] = Σ_i α^i M[i,j]`: rotation
    /// matrices are not symmetric, so contracting the other way is a different
    /// vector (and `folded_row_mle` would stop agreeing with [`fold_row`]).
    ///
    /// # Panics
    /// Unless `point.len() == depth` and `row < rows`.
    pub fn folded_row_mle(&self, row: usize, alpha: &R, point: &[R]) -> Vec<R> {
        let mle = self.column_mle(row, point);
        let pw = powers(alpha, D);
        (0..D)
            .map(|j| {
                (0..D).fold(R::ZERO, |acc, i| {
                    acc + pw[i] * *mle.get(i, j).expect("square")
                })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use algebra::ring::zq::Zq;

    /// The house non-NTT instance: prime, `≡ 5 (mod 8)`, 2-adicity 2, so no
    /// NTT of degree `≥ 4` exists and every path here is coefficient-domain.
    type Q5 = Zq<4294967197>;
    /// The crate's NTT-friendly prime, to show nothing here depends on a
    /// transform either.
    type Z1 = Zq<8380417>;
    const D: usize = 8;
    const MOD8: u64 = 4_294_967_197;

    fn elt<R: Ring, const N: usize>(salt: u64, i: usize) -> PolyRing<R, N> {
        let coeffs = (0..N)
            .map(|k| {
                let v = (salt as i64 * 31 + i as i64 * 7 + k as i64) % 13 - 6;
                from_centered::<R>(v)
            })
            .collect();
        PolyRing::from_coefficients(coeffs)
    }

    fn ring_mat<R: Ring, const N: usize>(rows: usize, cols: usize, salt: u64) -> BlockMat<R, N> {
        let data = (0..rows)
            .flat_map(|i| (0..cols).map(move |j| elt::<R, N>(salt, i * cols + j)))
            .collect();
        BlockMat::new(rows, cols, data).expect("shaped")
    }

    /// A sparse element `c·X^k`: the boundary case where the wrap hits the sign.
    fn monomial<R: Ring, const N: usize>(k: usize, c: i64) -> PolyRing<R, N> {
        let mut coeffs = vec![R::ZERO; N];
        coeffs[k] = from_centered::<R>(c);
        PolyRing::from_coefficients(coeffs)
    }

    /// `Σ_i pw[i]·M[i][j]` for every column `j` — the `O(d²)` reference fold.
    fn quadratic_fold<R: Ring>(m: &FieldMat<R>, pw: &[R]) -> Vec<R> {
        (0..m.cols())
            .map(|j| {
                (0..m.rows()).fold(R::ZERO, |acc, i| {
                    acc + pw[i] * *m.get(i, j).expect("in range")
                })
            })
            .collect()
    }

    /// Column `c` of a coefficient-level matrix (`FieldMat` stores rows only).
    fn column_of<R: Ring>(m: &FieldMat<R>, c: usize) -> Vec<R> {
        (0..m.rows())
            .map(|i| *m.get(i, c).expect("in range"))
            .collect()
    }

    /// eq. (17): `M_a·cf(b) = cf(a·b)`, on the ring with no NTT.
    #[test]
    fn multiplication_matrix_is_ring_multiplication() {
        assert_eq!((MOD8 - 1).trailing_zeros(), 2, "the fixture has no NTT");
        for i in 0..4 {
            let a = elt::<Q5, D>(1, i);
            let b = elt::<Q5, D>(2, i);
            let got = multiplication_matrix(&a)
                .apply(&to_coeffs(&[b.clone()]))
                .expect("square");
            assert_eq!(got, to_coeffs(&[a * b]), "element {i}");
        }
    }

    /// The same identity on the NTT-friendly ring: a bug that only shows up for
    /// one `q` would be missed by a single-ring test.
    #[test]
    fn multiplication_matrix_works_on_the_ntt_ring_too() {
        let a = elt::<Z1, D>(3, 1);
        let b = elt::<Z1, D>(4, 2);
        let got = multiplication_matrix(&a)
            .apply(&to_coeffs(&[b.clone()]))
            .expect("square");
        assert_eq!(got, to_coeffs(&[a * b]));
    }

    /// `rot` is multiplication by `X`, and `d` rotations negate (`X^d = −1`).
    #[test]
    fn rotating_d_times_negates_and_matches_the_shift() {
        let cf = to_coeffs(&[elt::<Q5, D>(5, 0)]);
        let mut v = cf.clone();
        for k in 1..=D {
            v = rot(&v);
            let mut want = vec![Q5::ZERO; D];
            for (i, c) in cf.iter().enumerate() {
                if i + k < D {
                    want[i + k] = *c;
                } else {
                    want[i + k - D] = -*c;
                }
            }
            assert_eq!(v, want, "rot^{k}");
        }
    }

    /// Rotation matrices represent the ring: `M_a M_b = M_{ab}`.
    #[test]
    fn rotation_matrices_multiply_like_the_ring() {
        let a = elt::<Q5, D>(6, 1);
        let b = elt::<Q5, D>(7, 2);
        let left = multiplication_matrix(&a)
            .matmul(&multiplication_matrix(&b))
            .expect("square");
        assert_eq!(left, multiplication_matrix(&(a * b)));
    }

    /// The load-bearing identity: the `O(d)` recurrence agrees with contracting
    /// the Vandermonde row against the explicit `d × d` matrix. An off-by-one in
    /// the wrap term or in `a_{(d−1−j) mod d}` fails here.
    #[test]
    fn fold_row_matches_the_quadratic_contraction() {
        for alpha in [2u64, 3, 7, 12345, MOD8 - 2] {
            let alpha = Q5::from(alpha);
            let pw = powers(&alpha, D);
            for i in 0..3 {
                let a = elt::<Q5, D>(8, i);
                assert_eq!(
                    fold_row(&alpha, &a),
                    quadratic_fold(&multiplication_matrix(&a), &pw),
                    "alpha {alpha:?}, element {i}"
                );
            }
        }
    }

    /// A monomial is where the negacyclic sign lives: `α·M_{c·X^k}` is the
    /// Vandermonde row scaled by `c` and rotated by `k`, wrapping with a sign.
    #[test]
    fn fold_row_of_a_monomial_carries_the_negacyclic_sign() {
        let alpha = Q5::from(5u64);
        // a = X^{d-1}: rot^j(a) = X^{d-1+j}, which is X^{d-1} for j = 0 and
        // -X^{j-1} afterwards.
        let got = fold_row(&alpha, &monomial::<Q5, D>(D - 1, 1));
        let mut want = vec![Q5::ZERO; D];
        want[0] = alpha.pow((D - 1) as u64);
        for j in 1..D {
            want[j] = -alpha.pow((j - 1) as u64);
        }
        assert_eq!(got, want);
        // a = 3X²: rot^j(a) = 3X^{j+2}, negated once j+2 reaches d.
        let got2 = fold_row(&alpha, &monomial::<Q5, D>(2, 3));
        let three = Q5::from(3u64);
        let want2 = (0..D)
            .map(|j| {
                if j + 2 < D {
                    three * alpha.pow((j + 2) as u64)
                } else {
                    -three * alpha.pow((j + 2 - D) as u64)
                }
            })
            .collect::<Vec<_>>();
        assert_eq!(got2, want2);
    }

    // ---- the O(d) claim, *measured* ------------------------------------
    //
    // `Costed` is a real prime field (`131`) that also counts the multiplications
    // and additions each element takes part in. Prose in a doc comment cannot
    // establish that the fold is linear; a counter inside it can.

    /// A [`Ring`] that records how many field multiplications and additions it
    /// performs. Arithmetic is genuine `Z/131`, so a route can only pass the
    /// equality assertions by doing the *right* work.
    #[derive(Clone, Copy, PartialEq, Eq, Debug)]
    struct Costed(u64);

    /// The instrumented field's modulus: prime, so `Costed` is a field.
    const COST_Q: u64 = 131;

    // `std` is linked under `cfg(test)` by the crate root; the counters are
    // thread-local so that this instrument cannot be corrupted by another test
    // running in parallel on the same binary.
    std::thread_local! {
        static MULS: core::cell::Cell<usize> = core::cell::Cell::new(0);
        static ADDS: core::cell::Cell<usize> = core::cell::Cell::new(0);
    }

    impl Costed {
        fn new(x: u64) -> Self {
            Costed(x % COST_Q)
        }

        /// Zeroes both counters, runs `f`, and returns its result with the counts.
        fn measured<T>(f: impl FnOnce() -> T) -> (T, usize, usize) {
            MULS.with(|c| c.set(0));
            ADDS.with(|c| c.set(0));
            let out = f();
            (out, MULS.with(|c| c.get()), ADDS.with(|c| c.get()))
        }
    }

    impl core::ops::Add for Costed {
        type Output = Self;
        fn add(self, rhs: Self) -> Self {
            ADDS.with(|c| c.set(c.get() + 1));
            Costed::new(self.0 + rhs.0)
        }
    }
    impl core::ops::Sub for Costed {
        type Output = Self;
        fn sub(self, rhs: Self) -> Self {
            ADDS.with(|c| c.set(c.get() + 1));
            Costed::new(self.0 + COST_Q - rhs.0)
        }
    }
    impl core::ops::Mul for Costed {
        type Output = Self;
        fn mul(self, rhs: Self) -> Self {
            MULS.with(|c| c.set(c.get() + 1));
            Costed::new(self.0 * rhs.0)
        }
    }
    impl core::ops::Neg for Costed {
        type Output = Self;
        fn neg(self) -> Self {
            Costed::new(COST_Q - self.0)
        }
    }
    impl core::ops::AddAssign for Costed {
        fn add_assign(&mut self, rhs: Self) {
            *self = *self + rhs;
        }
    }
    impl core::ops::SubAssign for Costed {
        fn sub_assign(&mut self, rhs: Self) {
            *self = *self - rhs;
        }
    }
    impl core::ops::MulAssign for Costed {
        fn mul_assign(&mut self, rhs: Self) {
            *self = *self * rhs;
        }
    }
    impl From<u64> for Costed {
        fn from(x: u64) -> Self {
            Costed::new(x)
        }
    }
    impl Ring for Costed {
        const MODULUS: u64 = COST_Q;
        const ZERO: Self = Costed(0);
        const ONE: Self = Costed(1);
        fn rand(_rng: &mut impl rand::RngCore) -> Self {
            unimplemented!("Costed is a cost instrument, not a sampler")
        }
        fn square(&self) -> Self {
            *self * *self
        }
        fn pow(&self, power: u64) -> Self {
            let mut acc = Self::ONE;
            for _ in 0..power {
                acc *= *self;
            }
            acc
        }
        fn to_u128(&self) -> u128 {
            self.0 as u128
        }
    }

    /// `(muls, adds)` of the `O(d)` [`fold_row`] and of the `O(d²)` contraction of
    /// the explicit [`multiplication_matrix`], plus whether the two agree.
    fn fold_costs<const N: usize>() -> ((usize, usize), (usize, usize), bool) {
        let alpha = Costed::new(7);
        let a = PolyRing::<Costed, N>::from_coefficients(
            (0..N).map(|k| Costed::new(k as u64 + 2)).collect(),
        );
        // Built outside the measured window: the slow route needs the same
        // Vandermonde row the fast route derives internally.
        let pw = powers(&alpha, N);
        let (fast, fmul, fadd) = Costed::measured(|| fold_row(&alpha, &a));
        let (slow, smul, sadd) =
            Costed::measured(|| quadratic_fold(&multiplication_matrix(&a), &pw));
        ((fmul, fadd), (smul, sadd), fast == slow)
    }

    /// The headline claim of eprint 2026/1196 §1.3 (p. 8) / §3.2.1 (p. 18) is a
    /// *cost* claim, so it is checked as one: at every degree the fast fold costs
    /// exactly `4d − 1` multiplications — `d + 1` to seed the powers, `d` in the
    /// `α·cf(a)` inner product, `2` per recurrence step — and `2d` additions,
    /// while the explicit rotation-block contraction costs `d²` of each. Doubling
    /// `d` **doubles** the former and **quadruples** the latter. Both routes must
    /// also return the same vector, so the count cannot be earned by skipping
    /// work: the two assertions are in the same test on purpose.
    #[test]
    fn the_fast_fold_costs_linearly_and_the_expansion_quadratically() {
        let mut prev: Option<((usize, usize), (usize, usize))> = None;
        for d in [2usize, 4, 8, 16, 32] {
            let ((fmul, fadd), (smul, sadd), agree) = match d {
                2 => fold_costs::<2>(),
                4 => fold_costs::<4>(),
                8 => fold_costs::<8>(),
                16 => fold_costs::<16>(),
                _ => fold_costs::<32>(),
            };
            assert!(
                agree,
                "d = {d}: the two routes disagree, so the count is meaningless"
            );
            assert_eq!((fmul, fadd), (4 * d - 1, 2 * d), "d = {d}: fast cost");
            assert_eq!((smul, sadd), (d * d, d * d), "d = {d}: expansion cost");
            if let Some((p, q)) = prev {
                assert_eq!(fmul, 2 * p.0 + 1, "doubling d must nearly double the fold");
                assert_eq!(smul, 4 * q.0, "doubling d must quadruple the expansion");
                assert!(fmul < smul, "d = {d}: the fold must actually be cheaper");
            }
            prev = Some(((fmul, fadd), (smul, sadd)));
        }
        // The asymptotic statement, on the measured numbers: `cost/d` stays
        // bounded for the fold and grows without bound for the expansion.
        let ((fmul, _), (smul, _), _) = fold_costs::<32>();
        assert!(
            fmul * 32 < smul * 4,
            "d = 32: linear must beat quadratic by >8×"
        );
    }

    /// The two partial-evaluation routes are the *same object*: the `d × d`
    /// matrix product of [`RowTensor::column_mle`] is the multiplication matrix of
    /// the single ring element from [`RowTensor::ring_mle`]. Checked at every
    /// depth, so a wrong bit-index convention (which factor owns which variable)
    /// cannot survive in one route while the other looks right.
    #[test]
    fn column_mle_is_the_multiplication_matrix_of_the_ring_mle() {
        for depth in 1..=3usize {
            let factors = (0..depth)
                .map(|k| ring_mat::<Q5, D>(2, 2, 41 + k as u64))
                .collect::<Vec<_>>();
            let t = RowTensor::new(&factors).expect("2-wide factors");
            let point = (0..depth)
                .map(|i| from_centered::<Q5>(i as i64 - 3))
                .collect::<Vec<_>>();
            assert_eq!(t.cols(), 1 << depth, "depth {depth}");
            for row in 0..t.rows() {
                assert_eq!(
                    t.column_mle(row, &point),
                    multiplication_matrix(&t.ring_mle(row, &point)),
                    "depth {depth}, row {row}"
                );
            }
        }
    }

    /// `expand_matrix` is the `O(d²)` object; folding it must agree with
    /// [`fold_matrix`]. This is eq. (18) read two ways, and a transposed
    /// expansion fails it.
    #[test]
    fn fold_matrix_is_the_expanded_contraction() {
        let m = ring_mat::<Q5, D>(3, 4, 9);
        let beta: Vec<Q5> = (0..3).map(|i| from_centered::<Q5>(i as i64 - 1)).collect();
        let alpha = Q5::from(11u64);
        let expanded = expand_matrix(&m);
        let mut beta_alpha = Vec::with_capacity(3 * D);
        for i in 0..3 {
            for p in powers(&alpha, D) {
                beta_alpha.push(beta[i] * p);
            }
        }
        // `β ⊗ α` contracts the *rows* of M̃, so the result is indexed by the
        // column block: an expansion written the other way round fails here.
        let want = (0..m.cols() * D)
            .map(|c| dot(&beta_alpha, &column_of(&expanded, c)))
            .collect::<Vec<_>>();
        assert_eq!(fold_matrix(&beta, &alpha, &m), want);
    }

    /// The property the protocol rests on: contracting the fold against `cf(x)`
    /// equals contracting `β ⊗ α` against `cf(Mx)`.
    #[test]
    fn fold_contracts_against_the_ring_product() {
        let m = ring_mat::<Q5, D>(3, 4, 10);
        let beta: Vec<Q5> = (0..3).map(|i| from_centered::<Q5>(i as i64 + 2)).collect();
        let alpha = Q5::from(13u64);
        let x = (0..4).map(|j| elt::<Q5, D>(11, j)).collect::<Vec<_>>();
        let mx = m.contract_cols(&x).expect("sized");
        let lhs = dot(&fold_matrix(&beta, &alpha, &m), &to_coeffs(&x));
        let mut rhs = Q5::ZERO;
        for (i, b) in beta.iter().enumerate() {
            rhs += *b * dot(&powers(&alpha, D), &to_coeffs(&[mx[i].clone()]));
        }
        assert_eq!(lhs, rhs);
    }

    /// The row-tensor partial evaluation: the `µ`-step product equals the
    /// expansion contracted against the evaluation vector, in both the `d × d`
    /// matrix form and the ring form.
    #[test]
    fn row_tensor_partial_evaluation_matches_the_expansion() {
        let factors = (0..3)
            .map(|k| ring_mat::<Q5, D>(2, 2, 20 + k as u64))
            .collect::<Vec<_>>();
        let t = RowTensor::new(&factors).expect("2-wide factors");
        assert_eq!((t.rows(), t.cols(), t.depth()), (2, 8, 3));
        let point: Vec<Q5> = (0..3).map(|i| from_centered::<Q5>(i as i64 - 4)).collect();
        let ev = evaluation_vector(&point);
        let expanded = t.to_block();
        for row in 0..2 {
            for a in 0..D {
                for c in 0..D {
                    let want = (0..8).fold(Q5::ZERO, |acc, b| {
                        acc + ev[b]
                            * *multiplication_matrix(&expanded.row(row)[b])
                                .get(a, c)
                                .expect("square")
                    });
                    assert_eq!(
                        *t.column_mle(row, &point).get(a, c).expect("square"),
                        want,
                        "entry ({a},{c}) of row {row}"
                    );
                }
            }
            let mut ring_want = vec![Q5::ZERO; D];
            for (b, w) in ev.iter().enumerate() {
                for (k, c) in to_coeffs(&[expanded.row(row)[b].clone()])
                    .iter()
                    .enumerate()
                {
                    ring_want[k] += *w * *c;
                }
            }
            assert_eq!(to_coeffs(&[t.ring_mle(row, &point)]), ring_want);
        }
    }

    /// The paper's special case: with the `0` choice equal to `1` the factor is
    /// `(1−e)I_d + e·M_F`, and the folded route agrees with folding the
    /// expansion entry by entry.
    #[test]
    fn row_tensor_with_unit_first_choice_gives_the_paper_factor() {
        let one = one_poly::<Q5, D>();
        let factors = (0..2)
            .map(|k| {
                let data = (0..2)
                    .flat_map(|i| [one.clone(), elt::<Q5, D>(30 + k as u64, i)])
                    .collect();
                BlockMat::new(2, 2, data).expect("shaped")
            })
            .collect::<Vec<_>>();
        let t = RowTensor::new(&factors).expect("2-wide");
        let point: Vec<Q5> = vec![Q5::from(3u64), Q5::from(5u64)];
        let alpha = Q5::from(7u64);
        let ev = evaluation_vector(&point);
        let expanded = t.to_block();
        // folded_row_mle == Σ_b eq(b,e)·(α M_{A[1,b]})
        let want = (0..D)
            .map(|k| {
                (0..4).fold(Q5::ZERO, |acc, b| {
                    acc + ev[b] * fold_row(&alpha, &expanded.row(1)[b])[k]
                })
            })
            .collect::<Vec<_>>();
        assert_eq!(t.folded_row_mle(1, &alpha, &point), want);
        // With the unit 0-choice the first factor is exactly
        // (1−e₀)I_d + e₀·M_{F₀[·,1]}, so the product form must reduce to it.
        let m1 = multiplication_matrix(&t.factor(0).row(0)[1]);
        let paper_factor = zip_entries(&identity_field_mat::<Q5, D>(), &m1, |i, x| {
            (Q5::ONE - point[0]) * *i + point[0] * *x
        });
        let only_first = RowTensor::new(&[t.factor(0).clone()])
            .expect("one factor")
            .column_mle(0, &[point[0]]);
        assert_eq!(only_first, paper_factor);
        // and the second factor's unit column is I_d, so a full 2-factor
        // evaluation is the product of the two paper factors
        let m1b = multiplication_matrix(&t.factor(1).row(0)[1]);
        let second = zip_entries(&identity_field_mat::<Q5, D>(), &m1b, |i, x| {
            (Q5::ONE - point[1]) * *i + point[1] * *x
        });
        assert_eq!(
            t.column_mle(0, &point),
            paper_factor.matmul(&second).expect("square")
        );
    }

    /// A mis-shaped factor is a typed rejection, not a silently wrong matrix.
    #[test]
    fn row_tensor_rejects_a_factor_of_the_wrong_width() {
        let good = ring_mat::<Q5, D>(2, 2, 1);
        let wide = ring_mat::<Q5, D>(2, 3, 2);
        let tall = ring_mat::<Q5, D>(3, 2, 3);
        assert_eq!(
            RowTensor::new(&[wide.clone()]),
            Err(TensorShapeError {
                got: 2003,
                expected: 2002
            })
        );
        assert_eq!(
            RowTensor::new(&[good.clone(), tall]),
            Err(TensorShapeError {
                got: 3002,
                expected: 2002
            })
        );
        assert!(RowTensor::new(&[good.clone(), good]).is_ok());
        assert_eq!(
            RowTensor::<Q5, D>::new(&[]),
            Err(TensorShapeError {
                got: 0,
                expected: 1
            })
        );
    }

    /// The evaluation vector is the `eq` kernel: an indicator on the cube and
    /// the multilinear extension off it.
    #[test]
    fn evaluation_vector_interpolates() {
        let table: Vec<Q5> = (0..4).map(|i| Q5::from(i as u64 + 1)).collect();
        for b in 0..4 {
            let point: Vec<Q5> = (0..2).map(|i| Q5::from(((b >> i) & 1) as u64)).collect();
            let ev = evaluation_vector(&point);
            assert_eq!(dot(&ev, &table), table[b], "picks out entry {b}");
            for (j, w) in ev.iter().enumerate() {
                assert_eq!(*w, if j == b { Q5::ONE } else { Q5::ZERO }, "indicator");
            }
        }
        let point = [Q5::from(2u64), Q5::from(3u64)];
        let want = table[0]
            + (table[1] - table[0]) * point[0]
            + (table[2] - table[0]) * point[1]
            + (table[3] - table[2] - table[1] + table[0]) * point[0] * point[1];
        assert_eq!(dot(&evaluation_vector(&point), &table), want);
    }

    /// `to_coeffs` pads, so a sparse element still occupies a full block and
    /// the fold cannot shift the layout.
    #[test]
    fn padded_layout_survives_a_sparse_element() {
        let sparse = monomial::<Q5, D>(0, 4);
        assert_eq!(to_coeffs(&[sparse.clone()]).len(), D);
        let alpha = Q5::from(3u64);
        // multiplication by a constant scales the Vandermonde row
        let got = fold_row(&alpha, &sparse);
        let want = powers(&alpha, D)
            .iter()
            .map(|p| *p * Q5::from(4u64))
            .collect::<Vec<_>>();
        assert_eq!(got, want);
    }

    #[test]
    fn identity_and_zip_entries_compose_blocks() {
        let a = multiplication_matrix(&elt::<Q5, D>(40, 1));
        let id = identity_field_mat::<Q5, D>();
        assert_eq!(a.matmul(&id).expect("square"), a);
        let doubled = zip_entries(&a, &a, |x, y| *x + *y);
        for i in 0..D {
            for j in 0..D {
                assert_eq!(
                    *doubled.get(i, j).expect("in range"),
                    *a.get(i, j).expect("in range") * Q5::from(2u64)
                );
            }
        }
        assert_eq!(zip_entries(&a, &id, |x, _| *x), a);
    }
}
