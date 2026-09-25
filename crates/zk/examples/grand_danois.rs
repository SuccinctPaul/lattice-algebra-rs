//! Grand Danois — Kallesøe–Khoshakhlagh, eprint 2026/1196: a multilinear
//! polynomial commitment scheme over vSIS, as a scheme assembly.
//!
//! This file holds no cryptographic logic. The row-tensor ("vSIS") CRS and the
//! rotation-matrix row fold come from [`zk::pcs::rotation`], the two-stage
//! structured projection and its norm windows from [`zk::pcs::jl_compose`], the
//! Ajtai key from [`zk::pcs::key`], the gadget `G`/`G⁻¹` from
//! [`zk::pcs::gadget`], tensor contractions from [`zk::pcs::mixed`], the
//! coefficient bridge from [`zk::pcs::projection`], the σ-pairing that turns
//! eq. (15) into a field dot from [`zk::pcs::packing`], the exact-`ℓ2` arithmetic
//! from [`zk::shortness::exact_l2`] and the sumcheck of eq. (19) from
//! [`zk::sumcheck::circuit`]. What lives here is the instance, the message order, and the
//! equations the paper prints.
//!
//! # Steps covered (paper numbering; pages are the 25-page eprint PDF)
//!
//! * §3.1 (pp. 15–16) `Setup(1^λ, ℓ)` — `A ← X_{nA,µA}` with `2^µA ≥ δL1`,
//!   `B ← X_{nB,µB}` with `2^µB ≥ nAδr`, `D = [D1 | D2] ← X_{nD,µD}` with
//!   `2^µD ≥ δ̂·256r + δr`, each a row-tensor matrix with `nA = nB = nD = O(1)`
//!   (Table 1, p. 11): a transparent CRS, no trapdoor.
//! * §3.1 (p. 16) `Commit(pp, f)` — pack `f` into `s ∈ R_q^{L1×r}`,
//!   `ŝᵢ = G⁻¹_{L1}(sᵢ)`, `tᵢ = Aŝᵢ`, `t̂ᵢ = G⁻¹_{nA}(tᵢ)`,
//!   `cm = B·[t̂₁|…|t̂_r]`, state `st = (ŝᵢ, t̂ᵢ)_i`. Depth two, not a tree.
//! * §3.2 / Fig. 1 (p. 21) — `J, J′ ← D` (lemma 2.5), `p = Πs`,
//!   `w = aᵀ[s₁|…|s_r]`, `p̂ = Ĝ⁻¹(p)`, `ŵ = G⁻¹(w)`, `v = D(p̂,ŵ)ᵀ`, `c ← C^r`,
//!   `z = Σᵢcᵢŝᵢ`, `ẑ = Ĝ⁻¹(z)`, `z′ = (p̂,ŵ,t̂,ẑ)`, `cm′ = Commit(z′)`, then
//!   `α, β, γ` and the sumcheck of eq. (19) (p. 19):
//!   `Σᵢ(βMα)~(i)z′~(i) + γΣᵢσ̃(i)z′~(i) = H` with `H = (β⊗α)cf(y) + γy`,
//!   `y = [v, cm, 0, 0, 0]ᵀ`.
//! * eq. (14) (p. 17) — all five constraint rows, each a named check.
//! * eq. (15) (p. 17) — `⟨bᵀG_r, cf(ŵ)⟩ = y`, checked at the coefficient level and,
//!   on the prover's side, through the σ-pairing `const(Σⱼσ(bⱼ)wⱼ)`.
//! * §3.2.1 (pp. 18–19) — the verifier folds every constraint row in `O(d)`
//!   ([`fold_matrix`]) instead of building the `d×d` rotation blocks, which is
//!   this scheme's whole departure from Hachi's eq. (16) `Mx = y + (X^d+1)r`;
//!   §3.2.2 (pp. 19–20) — it evaluates the vSIS blocks through the row-tensor
//!   partial evaluation ([`RowTensor::folded_row_mle`]) instead of the expansion.
//! * Fig. 1's (p. 21) two norm bounds — `‖pᵢ‖₂ ≤ 337ω` and `‖(ŵ,t̂,ẑ)‖₂² ≤
//!   b²(nA L2 δd + L2 δd) + (L2 κ b′)² L1 d`, both exact integer `ℓ2²`
//!   comparisons, plus the certified extraction slack `√(337/30)·ω` of
//!   Theorem 3.3 (p. 20). Both gates are tripped by named tampers.
//!
//! # Steps deliberately NOT taken
//!
//! * **The recursion.** Fig. 1's last prover message and the "PoK of opening
//!   `z′`" are, in the paper's words, an invocation of "a norm-bounded polynomial
//!   commitment scheme", composed with LaBRADOR or Greyhound at the bottom. Here
//!   the prover sends `z′` in the clear and the verifier checks eq. (14) directly
//!   — the *alternative protocol* §3.2.3's knowledge-soundness proof reasons
//!   about. `cm′` is still sent and still checked, but by recomputation rather
//!   than by a proof of knowledge. So this is one layer of `Π_eval`, not the
//!   recursive scheme, and the size printed below is the core size, not the
//!   paper's estimated 80–90 KB.
//! * **Sumcheck degree.** eq. (19) is proved by the degree-2 circuit sum-check of
//!   [`zk::sumcheck::circuit`] with the oracles kept separate —
//!   `G = (U + γV)·W`, `U = (βMα)~`, `V = σ~`, `W = z′~` — so the verifier closes
//!   on the paper's `(ũ(r) + γṽ(r))·w̃(r)` rather than on the multilinear extension
//!   of a materialised product table. The two agree on the cube and differ off it
//!   (`sumcheck::circuit`'s `the_weighted_product_matches_the_table_on_the_cube_and_differs_off_it`
//!   pins that), so this is not a re-encoding of the same check. The `O(d)` fold is
//!   still exercised where it *is* the verifier's work — building `βMα`.
//!
//! # What the paper leaves undefined, and what this instance chose
//!
//! 1. **`X_{n,µ}` (Def. 2.2) is never specified.** The paper says only that
//!    `A = A₀⊗…⊗A_{µ−1}` with `Aᵢ ∈ R_q^{n×2}` is a "vSIS-friendly tensor
//!    distribution", never defines "vanishing", and gives no reduction, no
//!    hardness estimate and no parameter table. Here: `A[i,b] = Π_k F_k[i,b_k]`,
//!    the *entrywise* ("row") tensor product — the only reading under which
//!    `A ∈ R_q^{n×2^µ}` (rather than `n^µ×2^µ`) and under which §3.2.2's product
//!    formula holds. Factors are uniform over `R_q`; the paper's written formula
//!    additionally needs the `0`-choice to be `1`, which this instance does
//!    **not** impose (the capability handles the general case).
//! 2. **`L1 = 256r` is never stated but is forced.** `Π` maps `R^{256ȷ²r} →
//!    R^{256r}` while `s ∈ R^{L1×r}`, so `p = Πs = Ĵ[s₁|…|s_r]` aligns only when
//!    `L1 = m·ȷ²`. This instance generalises `256 → m = 4` to stay interactive,
//!    which puts it **outside** the `[30,337]` concentration window (checked at
//!    `m = 256` in `pcs::jl_compose`'s tests). The gate `‖pᵢ‖₂ ≤ 337ω` is still
//!    the paper's gate; at `m = 4` it is simply loose.
//! 3. **`Ĝ` vs `G`.** Fig. 1 writes `p̂ = Ĝ⁻¹_{L1}(p)`, `ẑ = Ĝ⁻¹_{δL1}(z)` but
//!    `ŵ = G⁻¹_r(w)`, while §3.2 says `ŵ = Ĝ⁻¹_r(w)`; and `D`'s budget
//!    `δ̂·256r + δr` says `p̂` has `δ̂` limbs and `ŵ` has `δ`. This instance takes
//!    `Ĝ` (base `b′`, `δ̂` limbs) for `p̂`/`ẑ` and `G` (base `b`, `δ` limbs) for
//!    `ŝ`/`t̂`/`ŵ` — the only assignment consistent with `D`'s width.
//! 4. **`δ = ⌈log_b q⌉` is wrong for centered digits.** [`zk::pcs::gadget::split`]
//!    uses balanced digits in `[−b/2, b/2]`, whose capacity is `≈ b^δ/2`, so
//!    `⌈log_b q⌉` limbs cannot represent every residue. Here `b = b′ = 8`,
//!    `δ = δ̂ = 16` (the paper's formula would say 11).
//! 5. **`2^µD ≥ δ̂·256r + δr` cannot be met by one tensor** — a power of two is
//!    generally not the sum of the two limb counts — so `D` is sampled as two row
//!    tensors, `D1` over `p̂` and `D2` over `ŵ`. Parameters are chosen so all four
//!    widths are exact powers of two, so no witness padding is needed; the
//!    paper's `≥` (which implies padding) is therefore not exercised.
//! 6. **`κ`, `ω`, `b′`, the challenge set `C` and Fig. 1's norm-bound symbols are
//!    never pinned down.** Here `C` is ternary (`κ = 1`), `ω² = L1·d·(coefficient
//!    bound)²`, and the `(ŵ,t̂,ẑ)` bound is Fig. 1's formula with those values
//!    substituted — which happens to stay below `q`, the precondition of the
//!    crate's exact-`ℓ2` direct route.
//! 7. **`k = λ/log q` is not expressible in this crate.** The sumcheck line runs
//!    over `F_{q^k}`, and `algebra::ring::extension::ExtField` is deliberately
//!    **not** a `Ring`, so no `FieldMat`/`PolyRing` can hold extension
//!    coefficients. This instance runs at `k = 1`: `α, β, γ ∈ F_q`, `a ∈ F_q^{L1}`.
//!    Consequences, stated rather than hidden: the §3.2.1 per-row fold is still
//!    `O(d)` (the recurrence is coefficientwise), but §3.2.2's treatment of `aᵀ`
//!    as a `k`-row matrix with `k×k` multiplication matrices degenerates to
//!    scalars, so that part of the paper is **not** exercised.
//! 8. **`Π`'s tensor orientation.** The paper evaluates `Ĵ` at `e′⊗e″` without
//!    saying which factor is the fast index; the Kronecker product forces `e″`
//!    (the `ȷ` blocks) slow and `e′` (`J`'s width) fast. And §3.2.2's
//!    `J′((J′e′)⊗e″)` has a typo'd first factor — the intro's `J′((Je′)⊗e″)` is
//!    the identity that holds. Both are pinned by tests in [`zk::pcs::jl_compose`].
//! 9. **The 80–90 KB figure is an estimate, not a measurement**, and so is
//!    "O(λℓ) verification": the paper states no bounding theorem. §3.3 (p. 23)
//!    derives it from `q` a 32-bit prime, `k = 4`, "an Ajtai commitment is 4KB",
//!    so `v` and `cm` are 8 KB, one degree-2 sumcheck over a `2³²` table 1.5 KB,
//!    and 5–6 recursions. The size below is measured for *this* instance and is
//!    not comparable to it.
//! 10. **Two slips in the paper, both harmless to the construction but load-bearing
//!     for a transcription.** (a) Lemma 3.2's proof (p. 17) prints
//!     `2^{−128n/m} + 2^{−128n/m²} = 2^{−128(n/m + n/m²)}` — a sum of exponentials
//!     is not an exponential of a sum, so eq. (13)'s error is understated by a
//!     factor 2 (`≤`, not `=`). Substituting `n = L`, `m = ȷ² = r` does turn
//!     `(n/m + n/m²)` into the `(Lȷ² + L)/ȷ⁴` of Theorem 3.3 (p. 22), which is how
//!     this file reads "the block count". (b) eq. (14)'s fourth row prints the
//!     `p̂`-block entry as `(c⊤G_{L1})`, but `c ∈ C^r` and `p̂ ∈ R_q^{δ̂L1}` with
//!     `r ≠ L1`, so that is not type-correct; the equation it abbreviates is
//!     §1.3's (p. 6) `Ĵz = c⊤p`, i.e. `Σᵢcᵢpᵢ = Ĵ(Σᵢcᵢŝᵢ)` with `pᵢ ∈ R_q^m` —
//!     **`m` rows**, which is what `constraint_matrix` emits for `ROW_P` and what
//!     check `C_P` verifies.
//!
//! Run with: `cargo run -p lattice-zk --example grand_danois`

use algebra::crypto::sampling::BitStream;
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::{PolynomialQuotientRing, Ring};
use zk::foundation::encoding::u32s_to_le_bytes;
use zk::foundation::fs::{absorb_rings, seed_stream};
use zk::foundation::sampling::{centered_bounded_poly, from_centered};
use zk::pcs::gadget::{join, split};
use zk::pcs::jl_compose::{
    extractor_slack_sq, isqrt_ceil, projection_gate_ok, StructuredProjection, RATIO_HIGH,
};
use zk::pcs::key::RingMatrixKey;
use zk::pcs::mixed::BlockMat;
use zk::pcs::projection::{const_term, dot, from_coeffs, sigma_pairing_vec, to_coeffs, FieldMat};
use zk::pcs::rotation::{evaluation_vector, fold_matrix, fold_row, one_poly, powers, RowTensor};
use zk::shortness::exact_l2::{direct_route_admissible, squared_norm};
use zk::sumcheck::circuit::{self, CircuitSumcheckProof, WeightedProduct};

/// `2³² − 99`: prime, `≡ 5 (mod 8)`, 2-adicity 2 — the house non-NTT instance,
/// so every step here runs in the coefficient domain.
type Q = Zq<4294967197>;
/// Ring degree `d`.
const D: usize = 8;
type Elt = PolyRing<Q, D>;

/// Projection rows `m` (the paper's 256; see header item 2).
const M: usize = 4;
/// Splitting factor `ȷ`, with `ȷ² = r`.
const JOTS: usize = 2;
/// `r = L2/d = ȷ²`: packed columns of the witness matrix.
const R: usize = JOTS * JOTS;
/// `L1 = m·r` — the alignment condition of header item 2.
const L1: usize = M * R;
/// `L2 = r·d`.
const L2: usize = R * D;
/// `L = L1·L2 = 2^ℓ`, with `ℓ = ℓ1 + ℓ2`.
const L: usize = L1 * L2;
const ELL1: usize = 4;
const ELL2: usize = 5;
/// CRS row counts `nA = nB = nD = O(1)`.
const N_A: usize = 4;
const N_B: usize = 4;
const N_D: usize = 4;

/// Decomposition base `b` and limb count `δ` (header item 4).
const BASE: u64 = 8;
const DIGITS: usize = 16;
/// Second base `b′` and limb count `δ̂`, for `p̂` and `ẑ`.
const SEC_BASE: u64 = 8;
const SEC_DIGITS: usize = 16;

/// Bound on every committed hypercube value, so `ω² = L1·d·COEF²` bounds each
/// packed column `‖s₂²`.
const COEF: i64 = 4;
/// Challenge bound `κ` (the challenge set `C` is ternary).
const KAPPA: u64 = 1;

/// `δL1`: columns of `A`, and the length of the decomposed `z`.
const Z_LEN: usize = DIGITS * L1;
/// `δ̂·δL1`: length of `ẑ`.
const ZH_LEN: usize = SEC_DIGITS * Z_LEN;
/// `δ̂L1`: length of `p̂`.
const PH_LEN: usize = SEC_DIGITS * L1;
/// `δr`: length of `ŵ`.
const WH_LEN: usize = DIGITS * R;
/// `δ·nA·r`: length of the stacked `t̂`.
const TH_LEN: usize = DIGITS * N_A * R;
/// Witness columns of the constraint matrix.
const C_COLS: usize = PH_LEN + WH_LEN + TH_LEN + ZH_LEN;
/// Constraint rows of eq. (14): `nD + nB + 1 + m + nA`.
const M_ROWS: usize = N_D + N_B + 1 + M + N_A;
/// Flattened witness length.
const FLAT: usize = C_COLS * D;
/// Sumcheck variables and table size.
const G: usize = 16;
const TABLE: usize = 1 << G;

/// Column offsets of the four witness parts inside `z′`.
const AT_P: usize = 0;
const AT_W: usize = PH_LEN;
const AT_T: usize = PH_LEN + WH_LEN;
const AT_Z: usize = PH_LEN + WH_LEN + TH_LEN;
/// Row offsets inside the constraint matrix.
const ROW_V: usize = 0;
const ROW_CM: usize = N_D;
const ROW_W: usize = N_D + N_B;
const ROW_P: usize = ROW_W + 1;
const ROW_T: usize = ROW_P + M;

/// `ω²`, the squared bound on each packed witness column `‖s‖₂²`.
const OMEGA_SQ: u128 = (L1 * D) as u128 * (COEF * COEF) as u128;
/// Fig. 1's squared bound on `(ŵ, t̂, ẑ)`: `b²(nA L2 δd + L2 δd) + (L2 κ b′)² L1 d`.
const BOUND_WTZ_SQ: u128 = (BASE * BASE) as u128
    * ((N_A * L2 * DIGITS * D + L2 * DIGITS * D) as u128)
    + (L2 as u128 * KAPPA as u128 * SEC_BASE as u128).pow(2) * (L1 * D) as u128;

/// eq. (14)'s five rows, eq. (15), the CRS structure, `cm′`, the sumcheck and the
/// two norm bounds — named once so prover, verifier and demo agree on what each
/// one is.
const C_V: &str = "eq14.1: v = D1·p̂ + D2·ŵ";
const C_CM: &str = "eq14.2: cm = B·t̂";
const C_W: &str = "eq14.3: cᵀG_r·ŵ = aᵀG_{L1}·Ĝ·ẑ";
const C_P: &str = "eq14.4: (cᵀ⊗I_m)·Ĝ·p̂ = Ĵ·G_{L1}·Ĝ·ẑ";
const C_T: &str = "eq14.5: (cᵀ⊗G_{nA})·t̂ = A·Ĝ·ẑ";
/// eq. (15) read two ways: the verifier's zero-padded `σ` over `F_q` (§3.2.1,
/// p. 19 — "0-padding σ to the length of the full witness") and the prover's
/// ring route through the σ-pairing of `pcs::packing`. They agree by
/// construction, so a failure is joint; naming them apart is what tells a
/// regression in `packing` from one in the padded contraction.
const C_EVAL: &str = "eq15: ⟨bᵀG_r, cf(ŵ)⟩ = y (padded σ)";
const C_EVAL_RING: &str = "eq15: const(Σⱼ σ(bⱼ)·wⱼ) = y (ring route)";
const C_CRS: &str = "crs §3.2.2: the vSIS blocks are the announced row tensors";
const C_BIND: &str = "cm′ binds z′";
const C_SUM: &str = "sumcheck eq. (19): rounds close at H";
const C_FINAL: &str = "sumcheck: final value = (ũ(r)+γṽ(r))·w̃(r)";
const C_GATE_P: &str = "gate-p: ‖p‖₂² ≤ 337²·ω² for every i";
const C_GATE_W: &str = "gate-wtz: ‖(ŵ,t̂,ẑ)‖₂² ≤ Fig. 1's bound";

/// Every check [`failing`] can report. `main` asserts each one is tripped by at
/// least one tamper, so this list cannot drift out of step with the demo.
const ALL_CHECKS: &[&str] = &[
    C_V,
    C_CM,
    C_W,
    C_P,
    C_T,
    C_EVAL,
    C_EVAL_RING,
    C_CRS,
    C_BIND,
    C_SUM,
    C_FINAL,
    C_GATE_P,
    C_GATE_W,
];

/// The sumcheck table must hold the flattened witness.
const _: () = assert!(FLAT <= TABLE, "the sumcheck table must hold the witness");

/// Why the proof was rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
enum DanoisError {
    /// The first named check that failed.
    Rejected(&'static str),
    /// A proof component did not have the shape the instance fixes.
    Malformed(&'static str),
}

impl core::fmt::Display for DanoisError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Rejected(what) => write!(f, "rejected: {what}"),
            Self::Malformed(what) => write!(f, "malformed proof: {what}"),
        }
    }
}

/// A vSIS public parameter: the factors (the succinct representation the verifier
/// folds) and the expansion (the matrix the constraint system uses). §3.2.2 is
/// what licenses the two agreeing, and check [`C_CRS`] is what tests it.
#[derive(Clone)]
struct TensorKey {
    tensor: RowTensor<Q, D>,
    mat: BlockMat<Q, D>,
}

impl TensorKey {
    fn publish(tensor: RowTensor<Q, D>) -> Self {
        let mat = tensor.to_block();
        Self { tensor, mat }
    }
}

/// The transparent CRS of §3.1.
#[derive(Clone)]
struct Crs {
    a: TensorKey,
    b: TensorKey,
    d1: TensorKey,
    d2: TensorKey,
}

/// A row-tensor matrix from `X_{n,µ}` with `cols = 2^µ` columns (header item 1).
///
/// # Panics
/// Unless `cols` is a power of two at least 2.
fn tensor(label: &[u8], seed: &[u8; 32], rows: usize, cols: usize) -> RowTensor<Q, D> {
    assert!(
        cols > 1 && cols.is_power_of_two(),
        "a row tensor needs 2^µ columns with µ ≥ 1"
    );
    let factors = (0..cols.trailing_zeros())
        .map(|k| {
            let data = (0..rows * 2)
                .map(|i| {
                    let mut xof =
                        seed_stream::<Shake256Xof>(&[label, b"/factor", &[k as u8]].concat(), seed);
                    xof.absorb(&(i as u64).to_le_bytes());
                    let mut stream = BitStream::new(&mut xof);
                    let coeffs = (0..D)
                        .map(|_| Q::from((stream.read_bits(32) as u64) % Q::MODULUS))
                        .collect();
                    PolyRing::from_coefficients(coeffs)
                })
                .collect();
            BlockMat::new(rows, 2, data).expect("shaped")
        })
        .collect::<Vec<_>>();
    RowTensor::new(&factors).expect("uniform shape")
}

/// §3.1 `Setup(1^λ, ℓ)`: `A`, `B` and the two halves of `D`, each a row tensor
/// whose width is exactly the limb count of the part it commits.
fn setup(seed: &[u8; 32]) -> Crs {
    Crs {
        a: TensorKey::publish(tensor(b"vSIS-A", seed, N_A, Z_LEN)),
        b: TensorKey::publish(tensor(b"vSIS-B", seed, N_B, TH_LEN)),
        d1: TensorKey::publish(tensor(b"vSIS-D1", seed, N_D, PH_LEN)),
        d2: TensorKey::publish(tensor(b"vSIS-D2", seed, N_D, WH_LEN)),
    }
}

/// Public statement: the commitment, the evaluation point and the claimed value.
#[derive(Clone)]
struct Instance {
    cm: Vec<Elt>,
    x: Vec<Q>,
    y: Q,
}

/// The prover's state `st = (ŝᵢ, t̂ᵢ)_{i∈[r]}` plus the packed witness `s`.
struct Witness {
    s_cols: Vec<Vec<Elt>>,
    s_hat: Vec<Elt>,
    t_hat: Vec<Elt>,
}

/// The prover's messages, in Fig. 1's order. `z′` is sent in the clear because
/// the recursion is not layered on (see the header).
#[derive(Clone)]
struct Proof {
    p_hat: Vec<Elt>,
    w_hat: Vec<Elt>,
    t_hat: Vec<Elt>,
    z_hat: Vec<Elt>,
    v: Vec<Elt>,
    cm_prime: Vec<Elt>,
    sumcheck: CircuitSumcheckProof<Q, G, 3>,
}

impl Proof {
    /// `z′ = (p̂, ŵ, t̂, ẑ)`.
    fn z_prime(&self) -> Vec<Elt> {
        [
            self.p_hat.as_slice(),
            self.w_hat.as_slice(),
            self.t_hat.as_slice(),
            self.z_hat.as_slice(),
        ]
        .concat()
    }
}

/// The ring element `1`.
fn one() -> Elt {
    one_poly::<Q, D>()
}

/// The additive identity of `R_q`.
fn zero() -> Elt {
    PolyRing::from_coefficients(vec![Q::ZERO; D])
}

/// The constant polynomial `x`.
fn scalar_poly(x: Q) -> Elt {
    PolyRing::from_coefficients(vec![x])
}

/// `b^k` in the field.
fn base_pow(k: usize) -> Q {
    Q::from(BASE).pow(k as u64)
}

/// `b′^l` as a constant polynomial.
fn sec_pow(l: usize) -> Elt {
    scalar_poly(Q::from(SEC_BASE).pow(l as u64))
}

/// `log₂(n)`.
///
/// # Panics
/// If `n` is not a power of two.
fn log2(n: usize) -> usize {
    assert!(n.is_power_of_two(), "width {n} is not a power of two");
    n.trailing_zeros() as usize
}

/// The committed polynomial: `L` hypercube values in `[-COEF, COEF]`.
fn committed(seed: &[u8; 32]) -> Vec<Q> {
    let mut xof = seed_stream::<Shake256Xof>(b"danois-f", seed);
    let mut stream = BitStream::new(&mut xof);
    (0..L)
        .map(|_| from_centered::<Q>(stream.read_bits(3) as i64 - COEF))
        .collect()
}

/// Pack `f` into `s ∈ R_q^{L1×r}` with `s[i][j][k] = f[i + L1·(j·d + k)]`, the
/// hypercube index splitting as `u = i + L1·c` (`i` the low `ℓ1` bits).
fn pack(f: &[Q]) -> Vec<Vec<Elt>> {
    (0..R)
        .map(|j| {
            (0..L1)
                .map(|i| {
                    PolyRing::from_coefficients((0..D).map(|k| f[i + L1 * (j * D + k)]).collect())
                })
                .collect()
        })
        .collect()
}

/// The multilinear evaluation `y = Σ_u eq(x, u)·f[u]`.
fn evaluate(f: &[Q], x: &[Q]) -> Q {
    let a = evaluation_vector(&x[..ELL1]);
    let b = evaluation_vector(&x[ELL1..]);
    let mut acc = Q::ZERO;
    for i in 0..L1 {
        for c in 0..L2 {
            acc += a[i] * b[c] * f[i + L1 * c];
        }
    }
    acc
}

/// §3.1 `Commit(pp, f)`.
fn commit(crs: &Crs, seed: &[u8; 32]) -> (Instance, Witness) {
    let f = committed(seed);
    let s_cols = pack(&f);
    let mut s_hat = Vec::with_capacity(R * Z_LEN);
    for col in &s_cols {
        s_hat.extend_from_slice(&split::<Q, D, BASE, DIGITS>(col));
    }
    let mut t = Vec::with_capacity(R * N_A);
    for i in 0..R {
        t.extend_from_slice(
            &crs.a
                .mat
                .contract_cols(&s_hat[i * Z_LEN..(i + 1) * Z_LEN])
                .expect("aligned"),
        );
    }
    let mut t_hat = Vec::with_capacity(TH_LEN);
    for i in 0..R {
        t_hat.extend_from_slice(&split::<Q, D, BASE, DIGITS>(&t[i * N_A..(i + 1) * N_A]));
    }
    let cm = crs.b.mat.contract_cols(&t_hat).expect("aligned");
    let x = FieldMat::uniform(b"danois-x", seed, 1, ELL1 + ELL2)
        .row(0)
        .to_vec();
    let y = evaluate(&f, &x);
    (
        Instance { cm, x, y },
        Witness {
            s_cols,
            s_hat,
            t_hat,
        },
    )
}

/// The Fiat–Shamir chain. Prover and verifier walk **the same** functions in the
/// same order, so the two sides cannot derive different challenges.
struct Fs {
    tr: Transcript<Shake256Xof>,
}

impl Fs {
    fn new(crs: &Crs, inst: &Instance) -> Self {
        let mut tr = Transcript::new(b"lattice-algebra/Z7/grand-danois");
        for t in [&crs.a, &crs.b, &crs.d1, &crs.d2] {
            for row in 0..t.mat.rows() {
                absorb_rings(&mut tr, b"crs", t.mat.row(row));
            }
        }
        absorb_rings(&mut tr, b"cm", &inst.cm);
        tr.absorb(b"x", &field_bytes(&inst.x));
        tr.absorb(b"y", &field_bytes(&[inst.y]));
        Self { tr }
    }

    fn seed(&mut self) -> [u8; 32] {
        let mut out = [0u8; 32];
        out.copy_from_slice(&self.tr.challenge_bytes(32));
        out
    }

    /// Fig. 1, message 1: `J, J′ ← D` (lemma 2.5).
    fn projection(&mut self) -> StructuredProjection<Q> {
        StructuredProjection::sample(b"danois-JJ", &self.seed(), M, JOTS)
    }

    /// Fig. 1, message 3: `c ← C^r`, ternary ring elements (`κ = 1`).
    fn challenges(&mut self, v: &[Elt]) -> Vec<Elt> {
        absorb_rings(&mut self.tr, b"v", v);
        let mut xof = seed_stream::<Shake256Xof>(b"danois-c", &self.seed());
        let mut stream = BitStream::new(&mut xof);
        (0..R)
            .map(|_| centered_bounded_poly::<Q, _, D>(&mut stream, KAPPA as u32))
            .collect()
    }

    /// Fig. 1, message 5: `α, β, γ ← F_{q^k}` — here `k = 1` (header item 7).
    fn folds(&mut self, z_prime: &[Elt]) -> (Q, Q, Q) {
        absorb_rings(&mut self.tr, b"z'", z_prime);
        let row = FieldMat::uniform(b"danois-folds", &self.seed(), 1, 3)
            .row(0)
            .to_vec();
        (row[0], row[1], row[2])
    }

    /// The eq. (19) sum-check's binding, seeded from the same transcript state.
    /// The prover and the verifier both derive it here, so the round challenges
    /// cannot be bound to a different statement than the one folded.
    fn sumcheck_binding(&mut self) -> Vec<u8> {
        self.tr.challenge_bytes(32)
    }
}

fn field_bytes(v: &[Q]) -> Vec<u8> {
    v.iter()
        .flat_map(|c| u32s_to_le_bytes(&[c.to_u128() as u32]))
        .collect()
}

/// `Ĵ = J′(I_ȷ⊗J)` as a ring matrix: the projection's field entries **implicitly
/// embedded into `R_q` as constant polynomials**.
fn jhat_ring(proj: &StructuredProjection<Q>) -> BlockMat<Q, D> {
    let block = proj.block();
    let mut data = Vec::with_capacity(block.rows() * block.cols());
    for i in 0..block.rows() {
        for j in 0..block.cols() {
            data.push(scalar_poly(block.row(i)[j]));
        }
    }
    BlockMat::new(block.rows(), block.cols(), data).expect("shaped")
}

/// The `aᵀG_{L1}` row of eq. (14): entry `j·δ + k` is `a_j·b^k`.
///
/// # Panics
/// Unless `a.len() == L1`.
fn a_gadget(a: &[Q]) -> Vec<Q> {
    assert_eq!(a.len(), L1, "a is a scalar vector of length L1");
    (0..L1)
        .flat_map(|j| (0..DIGITS).map(move |k| a[j] * base_pow(k)))
        .collect()
}

/// The `bᵀG_r` row of eq. (15): entry `j·δ + k` is `b_j·b^k`, with `b` the packed
/// `ℓ2` evaluation vector (`b_j ∈ R_q` holding `d` consecutive weights).
///
/// # Panics
/// Unless `x` has `ℓ1 + ℓ2` coordinates.
fn b_gadget(x: &[Q]) -> Vec<Elt> {
    assert_eq!(
        x.len(),
        ELL1 + ELL2,
        "the evaluation point has ℓ coordinates"
    );
    let beta = from_coeffs::<Q, D>(&evaluation_vector(&x[ELL1..]));
    let mut out = Vec::with_capacity(WH_LEN);
    for bj in beta.iter() {
        for k in 0..DIGITS {
            out.push(bj.clone() * scalar_poly(base_pow(k)));
        }
    }
    out
}

/// The constraint matrix `M` of eq. (14): `M_ROWS × C_COLS` ring elements.
///
/// Every entry is read off the gadget formulas the paper prints: a block acting
/// on a part decomposed as `x[j·δ + k]` and re-decomposed by `Ĝ` into
/// `x̂[(j·δ + k)·δ̂ + l]` carries `value·b^k·b′^l`.
fn constraint_matrix(
    crs: &Crs,
    proj: &StructuredProjection<Q>,
    c: &[Elt],
    a: &[Q],
) -> BlockMat<Q, D> {
    let mut m = vec![zero(); M_ROWS * C_COLS];
    let put = |m: &mut Vec<Elt>, row: usize, col: usize, v: Elt| m[row * C_COLS + col] = v;
    // Row block 1: D = [D1 | D2], on p̂ and ŵ.
    for x in 0..N_D {
        for q in 0..PH_LEN {
            put(&mut m, ROW_V + x, AT_P + q, crs.d1.mat.row(x)[q].clone());
        }
        for q in 0..WH_LEN {
            put(&mut m, ROW_V + x, AT_W + q, crs.d2.mat.row(x)[q].clone());
        }
    }
    // Row block 2: B, on t̂.
    for x in 0..N_B {
        for q in 0..TH_LEN {
            put(&mut m, ROW_CM + x, AT_T + q, crs.b.mat.row(x)[q].clone());
        }
    }
    // Row 3: cᵀG_r on ŵ, and −aᵀG_{L1}·Ĝ on ẑ.
    for (j, cj) in c.iter().enumerate() {
        for k in 0..DIGITS {
            put(
                &mut m,
                ROW_W,
                AT_W + j * DIGITS + k,
                cj.clone() * scalar_poly(base_pow(k)),
            );
        }
    }
    let a_g = a_gadget(a);
    for (p, ag) in a_g.iter().enumerate() {
        for l in 0..SEC_DIGITS {
            put(
                &mut m,
                ROW_W,
                AT_Z + p * SEC_DIGITS + l,
                scalar_poly(Q::ZERO - *ag) * sec_pow(l),
            );
        }
    }
    // Row block 4: (cᵀI_m)·Ĝ on p̂, and −Ĵ·G_{L1}·Ĝ on ẑ.
    let jhat = proj.block();
    for u in 0..M {
        let row = ROW_P + u;
        for q in 0..L1 {
            if q % M == u {
                for l in 0..SEC_DIGITS {
                    put(
                        &mut m,
                        row,
                        AT_P + q * SEC_DIGITS + l,
                        c[q / M].clone() * sec_pow(l),
                    );
                }
            }
        }
        for p in 0..Z_LEN {
            let coef = jhat.row(u)[p / DIGITS];
            for l in 0..SEC_DIGITS {
                put(
                    &mut m,
                    row,
                    AT_Z + p * SEC_DIGITS + l,
                    scalar_poly(Q::ZERO - coef * base_pow(p % DIGITS)) * sec_pow(l),
                );
            }
        }
    }
    // Row block 5: cᵀG_{nA} on t̂, and −A·Ĝ on ẑ.
    for x in 0..N_A {
        let row = ROW_T + x;
        // (cᵀ⊗G_{nA}) is block-diagonal in the Ajtai row: row x of the
        // constraint reads only limb x of each t̂ᵢ.
        for (i, ci) in c.iter().enumerate() {
            for k in 0..DIGITS {
                put(
                    &mut m,
                    row,
                    AT_T + i * DIGITS * N_A + x * DIGITS + k,
                    ci.clone() * scalar_poly(base_pow(k)),
                );
            }
        }
        for p in 0..Z_LEN {
            let entry = crs.a.mat.row(x)[p].clone();
            for l in 0..SEC_DIGITS {
                put(
                    &mut m,
                    row,
                    AT_Z + p * SEC_DIGITS + l,
                    (zero() - entry.clone()) * sec_pow(l),
                );
            }
        }
    }
    BlockMat::new(M_ROWS, C_COLS, m).expect("instance-sized")
}

/// The eq. (15) weight vector `σ`: `cf(bᵀG_r)` zero-padded to the whole witness
/// length (the paper's "0-padding σ to the length of the full witness").
fn sigma_vector(b_g: &[Elt]) -> Vec<Q> {
    let mut sigma = vec![Q::ZERO; FLAT];
    let cf = to_coeffs(b_g);
    sigma[AT_W * D..AT_W * D + cf.len()].copy_from_slice(&cf);
    sigma
}

/// One of eq. (19)'s three oracles: the flattened vector, zero-padded to the
/// `2^G` cube the sum-check runs over. The padding contributes `0·0` to every
/// entry of the circuit, so it leaves the claimed sum `H` untouched.
fn padded(values: &[Q]) -> Vec<Q> {
    assert!(values.len() <= TABLE, "the oracle must fit the cube");
    let mut t = vec![Q::ZERO; TABLE];
    t[..values.len()].copy_from_slice(values);
    t
}

/// `H = (β⊗α)cf(y) + γy` for `y = [v, cm, 0, 0, 0]ᵀ`: the public right-hand side
/// of eq. (19), computable without the witness.
fn claimed_sum(beta: &[Q], alpha: &Q, v: &[Elt], cm: &[Elt], y: Q, gamma: Q) -> Q {
    let pw = powers(alpha, D);
    let mut acc = Q::ZERO;
    for (i, row) in v.iter().chain(cm.iter()).enumerate() {
        acc += beta[i] * dot(&pw, &to_coeffs(core::slice::from_ref(row)));
    }
    acc + gamma * y
}

/// `aᵀ[s₁|…|s_r]` with `a` a scalar vector over the module.
fn row_times_matrix(a: &[Q], cols: &[Vec<Elt>]) -> Vec<Elt> {
    (0..R)
        .map(|j| {
            let mut acc = zero();
            for i in 0..L1 {
                acc += scalar_poly(a[i]) * cols[j][i].clone();
            }
            acc
        })
        .collect()
}

/// `Σᵢ cᵢ·xᵢ` for scalar weights.
fn combine_scalar(c: &[Q], x: &[Elt]) -> Elt {
    let mut acc = zero();
    for (w, v) in c.iter().zip(x) {
        acc += scalar_poly(*w) * v.clone();
    }
    acc
}

/// `Σᵢ cᵢ·xᵢ` for ring weights.
fn combine(c: &[Elt], x: &[Elt]) -> Elt {
    let mut acc = zero();
    for (w, v) in c.iter().zip(x) {
        acc += w.clone() * v.clone();
    }
    acc
}

/// Fig. 1's prover side, top to bottom (`prove_eval`, so the crate's
/// [`zk::sumcheck::prove`] stays in scope).
fn prove_eval(crs: &Crs, inst: &Instance, w: &Witness) -> Proof {
    let mut fs = Fs::new(crs, inst);
    let proj = fs.projection();
    let refs: Vec<&[Elt]> = w.s_cols.iter().map(|c| c.as_slice()).collect();
    // p = Πs = Ĵ[s₁|…|s_r], and w = aᵀ[s₁|…|s_r]
    let p = proj.apply_to_columns::<D>(&refs);
    let a = evaluation_vector(&inst.x[..ELL1]);
    let w_vec = row_times_matrix(&a, &w.s_cols);
    let p_hat = split::<Q, D, SEC_BASE, SEC_DIGITS>(&p);
    let w_hat = split::<Q, D, BASE, DIGITS>(&w_vec);
    let v = crs
        .d1
        .mat
        .contract_cols(&p_hat)
        .expect("aligned")
        .iter()
        .zip(crs.d2.mat.contract_cols(&w_hat).expect("aligned").iter())
        .map(|(x, y)| x.clone() + y.clone())
        .collect::<Vec<_>>();
    let c = fs.challenges(&v);
    // z = Σᵢ cᵢŝᵢ ∈ R^{δL1}, ẑ = Ĝ⁻¹(z)
    let mut z = vec![zero(); Z_LEN];
    for (i, ci) in c.iter().enumerate() {
        for (acc, s) in z.iter_mut().zip(&w.s_hat[i * Z_LEN..(i + 1) * Z_LEN]) {
            *acc += ci.clone() * s.clone();
        }
    }
    let z_hat = split::<Q, D, SEC_BASE, SEC_DIGITS>(&z);
    // z′ = (p̂, ŵ, t̂, ẑ), cm′ = Commit(z′)
    let z_prime = [
        p_hat.as_slice(),
        w_hat.as_slice(),
        w.t_hat.as_slice(),
        z_hat.as_slice(),
    ]
    .concat();
    let cm_prime = cm_key().matvec(&z_prime).expect("instance-sized");
    let (alpha, beta, gamma) = fs.folds(&z_prime);
    let beta_row = powers(&beta, M_ROWS);
    let b_g = b_gadget(&inst.x);
    let m = constraint_matrix(crs, &proj, &c, &a);
    let folded = fold_matrix(&beta_row, &alpha, &m);
    // eq. (19) as its own circuit: `(U + γV)·W` with U = (βMα)~, V = σ~, W = z′~,
    // proved by a degree-2 sum-check rather than by folding the materialised
    // product table — the two close on different claims off the cube.
    let oracle_u = padded(&folded);
    let oracle_v = padded(&sigma_vector(&b_g));
    let oracle_w = padded(&to_coeffs(&z_prime));
    let h = claimed_sum(&beta_row, &alpha, &v, &inst.cm, inst.y, gamma);
    let binding = fs.sumcheck_binding();
    let sumcheck = circuit::prove::<Q, G, 3, _>(
        &[&oracle_u, &oracle_v, &oracle_w],
        &h,
        b"danois-sumcheck",
        &binding,
        &mut WeightedProduct {
            weights: vec![Q::ONE, gamma],
        },
    )
    .expect("the honest z′ satisfies eq. (19)'s circuit");
    Proof {
        p_hat,
        w_hat,
        t_hat: w.t_hat.clone(),
        z_hat,
        v,
        cm_prime,
        sumcheck,
    }
}

/// The key `z′` is committed under (Fig. 1's `Commit`, the recursion's input).
fn cm_key() -> RingMatrixKey<Q, D> {
    RingMatrixKey::setup(b"danois-cm'", &[0xCDu8; 32], N_D, C_COLS)
}

/// Every named check, evaluated **without short-circuiting**, as the names that
/// did not hold. One source of truth for the checks is what lets the demo
/// attribute each tamper to the equations it really trips.
fn failing(crs: &Crs, inst: &Instance, pr: &Proof) -> Result<Vec<&'static str>, DanoisError> {
    let shapes = [
        (pr.p_hat.len(), PH_LEN),
        (pr.w_hat.len(), WH_LEN),
        (pr.t_hat.len(), TH_LEN),
        (pr.z_hat.len(), ZH_LEN),
        (pr.v.len(), N_D),
        (pr.cm_prime.len(), N_D),
    ];
    if let Some(&(got, expected)) = shapes.iter().find(|(got, expected)| got != expected) {
        return Err(DanoisError::Malformed(if got > expected {
            "component too long"
        } else {
            "component too short"
        }));
    }
    let mut fs = Fs::new(crs, inst);
    let proj = fs.projection();
    let c = fs.challenges(&pr.v);
    let z_prime = pr.z_prime();
    let (alpha, beta, gamma) = fs.folds(&z_prime);
    let a = evaluation_vector(&inst.x[..ELL1]);
    let b_g = b_gadget(&inst.x);
    let m = constraint_matrix(crs, &proj, &c, &a);
    let beta_row = powers(&beta, M_ROWS);

    // Recomputed prover quantities, all from the sent parts.
    let p = join::<Q, D, SEC_BASE, SEC_DIGITS>(&pr.p_hat);
    let w_vec = join::<Q, D, BASE, DIGITS>(&pr.w_hat);
    let z = join::<Q, D, SEC_BASE, SEC_DIGITS>(&pr.z_hat);
    let s_folded = join::<Q, D, BASE, DIGITS>(&z);
    let jhat = jhat_ring(&proj);

    let mut bad: Vec<&'static str> = Vec::new();
    let mut check = |holds: bool, name: &'static str| {
        if !holds {
            bad.push(name);
        }
    };

    // §3.2.2: the vSIS blocks really are the announced row tensors, so the
    // verifier may fold them by the product formula instead of the expansion.
    check(tensors_ok(crs, &alpha), C_CRS);

    // eq14.1: v = D1·p̂ + D2·ŵ
    let v_want = crs
        .d1
        .mat
        .contract_cols(&pr.p_hat)
        .expect("aligned")
        .iter()
        .zip(crs.d2.mat.contract_cols(&pr.w_hat).expect("aligned").iter())
        .map(|(x, y)| x.clone() + y.clone())
        .collect::<Vec<_>>();
    check(v_want == pr.v, C_V);

    // eq14.2: cm = B·t̂
    check(
        crs.b.mat.contract_cols(&pr.t_hat).expect("aligned") == inst.cm,
        C_CM,
    );

    // eq14.3: cᵀw = aᵀ(Σᵢ cᵢsᵢ)
    check(combine(&c, &w_vec) == combine_scalar(&a, &s_folded), C_W);

    // eq14.4: Σᵢ cᵢpᵢ = Ĵ(Σᵢ cᵢsᵢ) — the projection-consistency row
    let p_comb = (0..M)
        .map(|u| (0..R).fold(zero(), |acc, i| acc + c[i].clone() * p[i * M + u].clone()))
        .collect::<Vec<_>>();
    check(
        p_comb == jhat.contract_cols(&s_folded).expect("aligned"),
        C_P,
    );

    // eq14.5: Σᵢ cᵢtᵢ = A·z
    let t_comb = (0..N_A)
        .map(|u| {
            (0..R).fold(zero(), |acc, i| {
                let ti =
                    join::<Q, D, BASE, DIGITS>(&pr.t_hat[i * DIGITS * N_A..(i + 1) * DIGITS * N_A]);
                acc + c[i].clone() * ti[u].clone()
            })
        })
        .collect::<Vec<_>>();
    check(t_comb == crs.a.mat.contract_cols(&z).expect("aligned"), C_T);

    // eq15: ⟨bᵀG_r, cf(ŵ)⟩ = y (the verifier's padded-σ route), and the prover's
    // σ-pairing route through the ring.
    let sigma = sigma_vector(&b_g);
    check(dot(&sigma, &to_coeffs(&z_prime)) == inst.y, C_EVAL);
    let beta_packed = from_coeffs::<Q, D>(&evaluation_vector(&inst.x[ELL1..]));
    check(
        const_term(&sigma_pairing_vec(&beta_packed, &w_vec)) == inst.y,
        C_EVAL_RING,
    );

    // cm′ binds z′
    check(
        cm_key().matvec(&z_prime).expect("instance-sized") == pr.cm_prime,
        C_BIND,
    );

    // eq. (19): the degree-2 sum-check against the public H, then its output
    // claim tied to the circuit `(ũ(r) + γṽ(r))·w̃(r)`. That is *not* the
    // multilinear extension of the materialised product table — the two agree on
    // the cube and differ off it, which is what Def. 9 exists to keep apart
    // (`sumcheck::circuit`'s weighted-product test pins that identity).
    let folded = fold_matrix(&beta_row, &alpha, &m);
    let oracle_u = padded(&folded);
    let oracle_v = padded(&sigma);
    let oracle_w = padded(&to_coeffs(&z_prime));
    let h = claimed_sum(&beta_row, &alpha, &pr.v, &inst.cm, inst.y, gamma);
    let binding = fs.sumcheck_binding();
    let outcome =
        circuit::verify::<Q, G, 3>(&pr.sumcheck, &h, b"danois-sumcheck", &binding).ok();
    check(outcome.is_some(), C_SUM);
    check(
        outcome.as_ref().is_some_and(|(point, final_eval)| {
            (circuit::multilinear_at(&oracle_u, point)
                + gamma * circuit::multilinear_at(&oracle_v, point))
                * circuit::multilinear_at(&oracle_w, point)
                == *final_eval
        }),
        C_FINAL,
    );

    // gate-p: ‖pᵢ‖₂² ≤ 337²·ω² for every projected column
    let gates = (0..R).all(|i| {
        squared_norm(&to_coeffs(&p[i * M..(i + 1) * M]))
            .is_ok_and(|sq| projection_gate_ok(sq, OMEGA_SQ))
    });
    check(gates, C_GATE_P);

    // gate-wtz: the exact squared norm of (ŵ, t̂, ẑ) against Fig. 1's bound. A
    // norm the arithmetic cannot even certify is a *failed check*, not a panic:
    // this path sees adversarial input, so it must never abort the verifier.
    let wtz_ok = squared_norm(&to_coeffs(
        &[
            pr.w_hat.as_slice(),
            pr.t_hat.as_slice(),
            pr.z_hat.as_slice(),
        ]
        .concat(),
    ))
    .is_ok_and(|sq| sq <= BOUND_WTZ_SQ);
    check(
        direct_route_admissible::<Q>(BOUND_WTZ_SQ) && wtz_ok,
        C_GATE_W,
    );
    Ok(bad)
}

/// The §3.2.2 check for all four vSIS blocks: folding a tensor row through the
/// product formula must equal folding the **published expansion** at the same
/// point. Tampering either side breaks it, which is exactly the assumption the
/// verifier's complexity is priced on.
fn tensors_ok(crs: &Crs, alpha: &Q) -> bool {
    let point = FieldMat::uniform(b"danois-e", &[0xEEu8; 32], 1, log2(Z_LEN))
        .row(0)
        .to_vec();
    let blocks = [
        (&crs.a, Z_LEN),
        (&crs.b, TH_LEN),
        (&crs.d1, PH_LEN),
        (&crs.d2, WH_LEN),
    ];
    blocks.iter().all(|(k, width)| {
        let e = &point[..log2(*width)];
        let ev = evaluation_vector(e);
        (0..k.tensor.rows()).all(|x| {
            let fast = k.tensor.folded_row_mle(x, alpha, e);
            let slow = (0..D)
                .map(|j| {
                    (0..*width).fold(Q::ZERO, |acc, b| {
                        acc + ev[b] * fold_row(alpha, &k.mat.row(x)[b])[j]
                    })
                })
                .collect::<Vec<_>>();
            fast == slow
        })
    })
}

/// The measured norms the two gates decide on, for the honest proof: the point
/// of printing them is to show the bounds are not satisfied vacuously (a zero
/// witness would also pass).
fn norm_headroom(pr: &Proof) -> (u128, u128) {
    let p = join::<Q, D, SEC_BASE, SEC_DIGITS>(&pr.p_hat);
    let max_p_sq = (0..R)
        .map(|i| squared_norm(&to_coeffs(&p[i * M..(i + 1) * M])).expect("in range"))
        .max()
        .expect("r ≥ 1");
    let wtz_sq = squared_norm(&to_coeffs(
        &[
            pr.w_hat.as_slice(),
            pr.t_hat.as_slice(),
            pr.z_hat.as_slice(),
        ]
        .concat(),
    ))
    .expect("in range");
    (max_p_sq, wtz_sq)
}

/// The verifier: accept only when every check holds.
fn verify_all(crs: &Crs, inst: &Instance, pr: &Proof) -> Result<(), DanoisError> {
    match failing(crs, inst, pr)? {
        empty if empty.is_empty() => Ok(()),
        bad => Err(DanoisError::Rejected(bad[0])),
    }
}

fn proof_bytes(pr: &Proof) -> usize {
    (pr.p_hat.len()
        + pr.w_hat.len()
        + pr.t_hat.len()
        + pr.z_hat.len()
        + pr.v.len()
        + pr.cm_prime.len())
        * D
        * 4
        + pr.sumcheck.rounds.len() * 3 * 4
        + 4
}

/// A tamper demo: asserts the *whole* non-short-circuiting failing set, that the
/// named first complaint is what `verify_all` reports, and records the set for
/// the coverage assertion at the end of `main`.
fn main() {
    // Every check each tamper is *expected* to trip. A `failing()` check that no
    // input ever violates is not a check, it is a comment, so `main` closes by
    // asserting `ALL_CHECKS` is covered by the tampers actually run.
    let mut seen: Vec<&'static str> = Vec::new();
    let mut expect_reject = |label: &str,
                             crs: &Crs,
                             inst: &Instance,
                             pr: &Proof,
                             first: &'static str,
                             expected: &[&'static str]| {
        let bad = failing(crs, inst, pr).unwrap_or_else(|e| panic!("{label}: {e}"));
        assert!(!bad.is_empty(), "{label}: the tamper was accepted");
        assert_eq!(bad[0], first, "{label}: first complaint");
        let mut got = bad.clone();
        got.sort_unstable();
        got.dedup();
        let mut want = expected.to_vec();
        want.sort_unstable();
        want.dedup();
        assert_eq!(got, want, "{label}: failing set");
        match verify_all(crs, inst, pr) {
            Err(DanoisError::Rejected(name)) => assert_eq!(name, first, "{label}: attribution"),
            other => panic!("{label}: expected a rejection, got {other:?}"),
        }
        for name in want {
            assert!(
                ALL_CHECKS.contains(&name),
                "{label}: `{name}` is not a declared check"
            );
            if !seen.contains(&name) {
                seen.push(name);
            }
        }
        println!("  {label}: rejected by {bad:?}");
    };
    let seed = [0xD4u8; 32];
    let crs = setup(&seed);
    let (inst, w) = commit(&crs, &seed);
    let proof = prove_eval(&crs, &inst, &w);
    verify_all(&crs, &inst, &proof).expect("honest proof rejected");
    println!(
        "Grand Danois 2026/1196 — q = 2³²−99 (≡5 mod 8, no NTT), d = {D}, ℓ = {ELL1}+{ELL2}, L = {L}"
    );
    println!(
        "  m = {M}, ȷ = {JOTS}, r = {R}, L1 = {L1}, L2 = {L2}, b = {BASE}, δ = {DIGITS}, b′ = {SEC_BASE}, δ̂ = {SEC_DIGITS}, k = 1 (see the header for every deviation)"
    );
    println!(
        "  honest proof verifies: {} bytes; constraint matrix {}×{} ring elements, sumcheck table {TABLE}",
        proof_bytes(&proof),
        M_ROWS,
        C_COLS
    );
    println!(
        "  ω² = {OMEGA_SQ} → gate 337²ω² = {}; Fig. 1's (ŵ,t̂,ẑ) bound² = {BOUND_WTZ_SQ} (under q: {})",
        u128::from(RATIO_HIGH * RATIO_HIGH) * OMEGA_SQ,
        direct_route_admissible::<Q>(BOUND_WTZ_SQ)
    );
    println!(
        "  certified extraction slack √(337/30)·ω = {} against ω = {}",
        isqrt_ceil(extractor_slack_sq(OMEGA_SQ)),
        isqrt_ceil(OMEGA_SQ)
    );

    let false_y = Instance {
        y: inst.y + Q::ONE,
        ..inst.clone()
    };
    // The statement is absorbed before `c`, so a false `y` re-derives every
    // challenge: the three rows that read `c` fail alongside eq. (15) and the
    // sumcheck. Rows 1 and 2 do not read `c`, and they hold — as does `cm′`.
    expect_reject(
        "false claim y",
        &crs,
        &false_y,
        &proof,
        C_W,
        &[C_W, C_P, C_T, C_EVAL, C_EVAL_RING, C_SUM, C_FINAL],
    );
    let mut cm = inst.cm.clone();
    cm[0] = cm[0].clone() + one();
    let false_cm = Instance { cm, ..inst.clone() };
    expect_reject(
        "false commitment cm",
        &crs,
        &false_cm,
        &proof,
        C_CM,
        &[C_CM, C_W, C_P, C_T, C_SUM, C_FINAL],
    );

    let mut bad = proof.clone();
    bad.p_hat[0] = bad.p_hat[0].clone() + one();
    expect_reject(
        "tampered p̂",
        &crs,
        &inst,
        &bad,
        C_V,
        &[C_V, C_P, C_BIND, C_SUM, C_FINAL],
    );
    let mut bad = proof.clone();
    bad.w_hat[0] = bad.w_hat[0].clone() + one();
    expect_reject(
        "tampered ŵ",
        &crs,
        &inst,
        &bad,
        C_V,
        &[C_V, C_W, C_EVAL, C_EVAL_RING, C_BIND, C_SUM, C_FINAL],
    );
    let mut bad = proof.clone();
    bad.t_hat[0] = bad.t_hat[0].clone() + one();
    expect_reject(
        "tampered t̂",
        &crs,
        &inst,
        &bad,
        C_CM,
        &[C_CM, C_T, C_BIND, C_SUM, C_FINAL],
    );
    let mut bad = proof.clone();
    bad.z_hat[0] = bad.z_hat[0].clone() + one();
    expect_reject(
        "tampered ẑ",
        &crs,
        &inst,
        &bad,
        C_W,
        &[C_W, C_P, C_T, C_BIND, C_SUM, C_FINAL],
    );

    // Fig. 1's two norm gates, exercised. Balanced digits in `[−b′/2, b′/2]`
    // cannot come close to either bound at these parameters (the honest
    // `‖(ŵ,t̂,ẑ)‖²` is three orders of magnitude under Fig. 1's bound and
    // `max‖pᵢ‖²` five under `337²ω²`), so the only input that trips a gate is an
    // *out-of-range limb* — a value that decomposes nothing. Note these tampers
    // trip a constraint row too, which is the honest picture: a prover that
    // breaks a gate *while* satisfying eq. (14) is a vSIS break and cannot be
    // produced here. What the two cases do prove is that both gates are live
    // code, computed from the sent limbs and reported on the failures they decide.
    let fat = || PolyRing::from_coefficients(vec![Q::from(1_000_000u64); D]);
    let mut bad = proof.clone();
    bad.z_hat[0] = fat();
    expect_reject(
        "inflated ẑ limb (gate-wtz)",
        &crs,
        &inst,
        &bad,
        C_W,
        &[C_W, C_P, C_T, C_BIND, C_SUM, C_FINAL, C_GATE_W],
    );
    let mut bad = proof.clone();
    bad.p_hat[0] = fat();
    expect_reject(
        "inflated p̂ limb (gate-p)",
        &crs,
        &inst,
        &bad,
        C_V,
        &[C_V, C_P, C_BIND, C_SUM, C_FINAL, C_GATE_P],
    );
    let mut bad = proof.clone();
    bad.v[0] = bad.v[0].clone() + one();
    expect_reject(
        "tampered v",
        &crs,
        &inst,
        &bad,
        C_V,
        &[C_V, C_W, C_P, C_T, C_SUM, C_FINAL],
    );
    let mut bad = proof.clone();
    bad.cm_prime[0] = bad.cm_prime[0].clone() + one();
    expect_reject("tampered cm′", &crs, &inst, &bad, C_BIND, &[C_BIND]);
    let mut bad = proof.clone();
    bad.sumcheck.rounds[0][1] += Q::ONE;
    expect_reject(
        "tampered sumcheck round",
        &crs,
        &inst,
        &bad,
        C_SUM,
        &[C_SUM, C_FINAL],
    );

    // A CRS whose published expansion is not the announced row tensor: the
    // §3.2.2 route stops being valid. The rows still hold (they read the
    // expansion), so only the tensor check sees it.
    let mut broken = crs.clone();
    let mut data = broken
        .a
        .mat
        .row_iter()
        .flatten()
        .cloned()
        .collect::<Vec<_>>();
    data[0] = data[0].clone() + one();
    broken.a.mat = BlockMat::new(N_A, Z_LEN, data).expect("instance-sized");
    expect_reject(
        "CRS whose expansion is not the announced tensor",
        &broken,
        &inst,
        &proof,
        C_CRS,
        &[C_CRS, C_W, C_P, C_T, C_SUM, C_FINAL],
    );

    // A second honest witness, to show the verification is not seed-specific.
    let (inst2, w2) = commit(&crs, &[0xB1u8; 32]);
    let proof2 = prove_eval(&crs, &inst2, &w2);
    verify_all(&crs, &inst2, &proof2).expect("honest second instance");
    let (max_p_sq, wtz_sq) = norm_headroom(&proof);
    println!(
        "  gates are not vacuous: max ‖pᵢ‖² = {max_p_sq} against 337²ω² = {}, ‖(ŵ,t̂,ẑ)‖² = {wtz_sq} against {BOUND_WTZ_SQ}",
        u128::from(RATIO_HIGH * RATIO_HIGH) * OMEGA_SQ
    );
    println!(
        "  both norm gates are live: the inflated-limb tampers above trip them, and a prover breaking a gate *while* satisfying eq. (14) is by Theorem 3.3 a vSIS break, which no demo can hand-produce"
    );
    println!(
        "  a second honest witness verifies too ({} bytes, {} projected columns gated at 337ω)",
        proof_bytes(&proof2),
        R
    );
    // Dead-code check: a named check that no tamper ever trips is not a check.
    for name in ALL_CHECKS {
        assert!(
            seen.contains(name),
            "`{name}` is never tripped by any tamper: it is dead code"
        );
    }
    assert_eq!(
        seen.len(),
        ALL_CHECKS.len(),
        "coverage mismatch: {} of {} checks tripped",
        seen.len(),
        ALL_CHECKS.len()
    );
    println!(
        "  every tamper is rejected by the checks it actually violates, and all {} named checks are tripped by at least one",
        ALL_CHECKS.len()
    );
}
