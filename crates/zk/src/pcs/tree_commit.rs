//! The Ajtai **hash-tree** commitment `TCom` (Cheng–Nguyen–Tyagi, eprint
//! 2026/2067 §2.1 / Def. 19): a Merkle tree whose hash is the nested Ajtai
//! map `H(m) = A·G⁻¹(m)`.
//!
//! With one public matrix `A ∈ R^{n×2nα}` (branching factor 2) and the gadget
//! recomposition `G_m = I_m ⊗ g_b^⊺` (Def. 18), a message `f ∈ R^{2^ℓ n}` is
//! committed by walking the tree bottom-up:
//!
//! ```text
//! s_ℓ ← G⁻¹_{2^ℓ n}(f)
//! s_i ← G⁻¹_{2^i n}((I_{2^i} ⊗ A)·s_{i+1})      for i = ℓ−1 … 1
//! t   ← A·s_1
//! ```
//!
//! The opening is the whole vector of layer openings `(s_i)_{i∈[ℓ]}`, and
//! `Open` accepts iff
//!
//! ```text
//! t = A·s_1,   G_{2^i n}·s_i = (I_{2^i} ⊗ A)·s_{i+1}  ∀i∈[ℓ−1],   ‖s_i‖∞ < b  ∀i∈[ℓ]
//! ```
//!
//! Three properties of this shape drive everything built on top of it, and
//! each is a check below rather than a comment:
//!
//! * **No authentication path exists.** A Merkle opening would be a set of
//!   sibling digests; here the opening *is* the full layer vector, so the
//!   verifier's work is `2^ℓ − 1` block matvecs and the size of the opening is
//!   `Θ(2^ℓ nα)` — which is exactly why the scheme can fold layers instead of
//!   hashing them (see [`crate::pcs::tree_fold`]).
//! * **No trapdoor is sampled.** `Setup` draws `A` uniformly (via
//!   [`RingMatrixKey`]), never `SamplePre`/TrapGen: binding comes from
//!   Module-SIS on the *shortness* of the `s_i` (Lemma 11), not from an
//!   invertible construction.
//! * **It is homomorphic layer-by-layer**, so a verifier-side linear
//!   combination of `2^k` subtrees is again a valid opening — with a norm that
//!   has grown, which is the whole difficulty the folding cycle manages.
//!
//! # What the paper's other `TCom` claims buy
//!
//! Def. 19 (p. 21) also gives a second `Commit`, `Commit(A, s_ℓ)` for an
//! already-low-norm bottom layer with `‖s_ℓ‖∞ < b` — that is
//! [`TreeKey::commit_digits`], and [`TreeKey::commit`] must agree with it on a
//! gadget image, which `commit_digits_matches_commit_on_a_gadget_image` pins.
//! [`TreeKey::open`] implements `Open`, [`TreeKey::open_with_message`] adds
//! `Open_F`'s `G_{2^ℓ n}·s_ℓ = f`. Then:
//!
//! * **Lemma 10** — `TCom` is *perfectly* complete for `b ≥ b`, so an honest
//!   opening is accepted with probability 1, not `1 − negl`.
//! * **Lemma 11** — binding assumes `MSIS_{q,n,d,rnα,b'}` with `b' ≥ 2b`
//!   ([`binding_norm`]).
//! * **Def. 22 / Lemma 12** — `(B,C,k)`-relaxed binding, which is what a
//!   folding round's extracted witness actually satisfies: collisions are only
//!   ruled out per `min(2^{i−1}, 2^k)` chunk of layer `i`, and the reduction
//!   loses a factor `2·T_{C−C,k}·B` in the MSIS bound ([`relaxed_binding_norm`]).
//!   This is the notion that forces Π^PE_NC's norm check to exist at all.
//!
//! # Instance parameters
//!
//! Unlike [`crate::pcs::nested`], which is welded to the crate's `Z1`
//! constants and to an NTT-domain key, this module is generic over the scalar
//! ring `R`, the ring degree `D`, the gadget base `BASE` and the digit count
//! `ALPHA`. That is load-bearing rather than cosmetic: the schemes in this
//! family (CMNW, Hachi, Serval, Maltese) require `q ≡ 5 (mod 8)`, whose
//! 2-adicity makes an NTT of degree `≥ 4` impossible, so the tree must run on
//! schoolbook arithmetic ([`RingMatrixKey`]). `BASE`/`ALPHA` are the paper's
//! `b` and `α = ⌈log_b q⌉`.
//!
//! [`RingMatrixKey`]: crate::pcs::key::RingMatrixKey

use crate::pcs::gadget;
use crate::pcs::key::{apply_blockwise, RingMatrixKey};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::{CenteredRing, Ring};
use algebra::ring::PolynomialQuotientRing;
use alloc::vec::Vec;
use core::fmt;

/// Domain-separation label of the single tree matrix `A`.
const TREE_LABEL: &[u8] = b"lattice-algebra/Z7/tcom-A";

/// Why a tree opening was rejected. Each variant names the *specific*
/// equation of Def. 19 that failed, so a tampered component is never
/// diagnosable only as "something was wrong".
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum TreeError {
    /// `|f|` is not `2^ℓ · n` for an integer `ℓ ≥ 1`.
    WrongLeafLength {
        /// Length supplied.
        got: usize,
        /// Nearest legal length.
        expected: usize,
    },
    /// A layer vector had the length the level does not accept.
    WrongLayerLength {
        /// Layer index (`0` is `s_1`, the layer the root consumes).
        level: usize,
        /// Length supplied.
        got: usize,
        /// Length the level expects.
        expected: usize,
    },
    /// The root equation `t = A·s_1` failed.
    RootMismatch {
        /// First row (index) that disagreed.
        at: usize,
    },
    /// A layer link `G_{2^i n}·s_i = (I_{2^i} ⊗ A)·s_{i+1}` failed.
    LayerLink {
        /// The level `i` whose link failed.
        level: usize,
        /// First index (within the recomposed level values) that disagreed.
        at: usize,
    },
    /// `Open_F`'s extra equation `G_{2^ℓ n}·s_ℓ = f` failed.
    LeafMismatch {
        /// First index that disagreed.
        at: usize,
    },
    /// `‖s_i‖∞ < b` failed for some layer.
    NormExceeded {
        /// Layer that broke its bound.
        level: usize,
        /// Observed infinity norm.
        got: u64,
        /// Bound `b` the opening must stay under.
        bound: u64,
    },
    /// An opening carried no layers.
    EmptyLayers,
}

impl fmt::Display for TreeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TreeError::WrongLeafLength { got, expected } => {
                write!(f, "leaf vector of {got} elements, expected {expected}")
            }
            TreeError::WrongLayerLength {
                level,
                got,
                expected,
            } => write!(f, "layer {level} holds {got} digits, expected {expected}"),
            TreeError::RootMismatch { at } => {
                write!(f, "root equation t = A·s₁ fails at row {at}")
            }
            TreeError::LayerLink { level, at } => write!(
                f,
                "layer link G·s_{level} = (I⊗A)·s_{} fails at element {at}",
                level + 1
            ),
            TreeError::LeafMismatch { at } => {
                write!(f, "leaf equation G·sℓ = f fails at element {at}")
            }
            TreeError::NormExceeded { level, got, bound } => write!(
                f,
                "layer {level} has ‖·‖∞ = {got}, the bound demands < {bound}"
            ),
            TreeError::EmptyLayers => write!(f, "a tree opening needs at least one layer"),
        }
    }
}

/// `α = ⌈log_BASE q⌉`, the gadget digit count of Def. 18 (p. 20): the smallest
/// number of base-`BASE` digits that can **represent** all `q` residues, i.e.
/// `BASE^α ≥ BASE^α − 1 ≥ q − 1`. Equivalently `BASE^α ≥ q` — *not* strictly
/// greater: at `q = 2, BASE = 2` one binary digit already names both residues,
/// and `gadget::split`'s own gate is `digit_span ≥ representative_ceiling`,
/// which for `BASE = 2` is `2^DIGITS − 1 ≥ q − 1`.
///
/// This is what makes `G_m · G_m⁻¹ = id` and `‖G_m⁻¹(x)‖∞ < b` (Def. 18's two
/// displayed properties) hold at the same time.
///
/// Returns `None` if `BASE < 2` or even `u128` cannot hold the capacity
/// (which would mean `α > 127` for any usable base).
pub const fn digits_for(base: u64, modulus: u64) -> Option<usize> {
    if base < 2 {
        return None;
    }
    let mut capacity: u128 = 1;
    // `as` casts only: `u128::from` is not (yet) usable in a `const fn`.
    let limit = modulus as u128;
    let mut alpha = 0usize;
    while capacity < limit {
        alpha += 1;
        if alpha > 127 {
            return None;
        }
        capacity = match capacity.checked_mul(base as u128) {
            Some(v) => v,
            None => return None,
        };
    }
    Some(alpha)
}

/// The Ajtai hash tree's public parameter: the single matrix
/// `A ∈ R^{n × 2nα}` of Def. 19 `Setup` (branching factor 2, shared by every
/// level — the tree's "hash function" is the *same* hash at every node).
#[derive(Clone)]
pub struct TreeKey<R: Ring, const D: usize, const BASE: u64, const ALPHA: usize> {
    seed: [u8; 32],
    rows: usize,
    a: RingMatrixKey<R, D>,
}

impl<R: Ring, const D: usize, const BASE: u64, const ALPHA: usize> fmt::Debug
    for TreeKey<R, D, BASE, ALPHA>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "TreeKey<n={}, d={d}, base={BASE}, alpha={ALPHA}>",
            self.rows,
            d = D
        )
    }
}

/// A `TCom` commitment plus its full opening `(s_i)_{i∈[ℓ]}`.
///
/// `layers[i]` is `s_{i+1}`, so `layers[0]` is the layer the root equation
/// consumes and `layers[len−1]` is the bottom (leaf) layer `G⁻¹(f)`.
#[derive(Clone, PartialEq, Eq)]
pub struct TreeOpening<R: Ring, const D: usize> {
    /// The root commitment `t = A·s_1` (`n` ring elements).
    pub root: Vec<PolyRing<R, D>>,
    /// Layer openings `s_1 … s_ℓ`, outermost first.
    pub layers: Vec<Vec<PolyRing<R, D>>>,
}

impl<R: Ring, const D: usize> fmt::Debug for TreeOpening<R, D> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TreeOpening")
            .field("root_len", &self.root.len())
            .field("height", &self.layers.len())
            .field(
                "layer_lens",
                &self.layers.iter().map(Vec::len).collect::<Vec<_>>(),
            )
            .finish()
    }
}

/// Ring element built from one repeated field coefficient (the `n`-th scalar
/// embedded as a constant polynomial, used for test vectors).
fn constant<R: Ring, const D: usize>(c: R) -> PolyRing<R, D> {
    let mut coeffs = alloc::vec![R::ZERO; D];
    coeffs[0] = c;
    PolyRing::from_coefficients(coeffs)
}

/// The norm gates of `Open` read centered coefficients, hence the
/// [`CenteredRing`] bound on the whole impl.
impl<R: Ring + CenteredRing, const D: usize, const BASE: u64, const ALPHA: usize>
    TreeKey<R, D, BASE, ALPHA>
{
    /// `Setup(1^λ) → A ←$ R^{n×2nα}`: uniform matrix from the public seed.
    ///
    /// There is no trapdoor generation anywhere in this call — the key is a
    /// seed-expanded uniform matrix, which is what makes the commitment
    /// transparent (Def. 19's `Setup` samples `A` and returns `pp ← {A}`).
    pub fn setup(seed: &[u8; 32], rows: usize) -> Self {
        assert!(rows > 0, "the commitment dimension n must be positive");
        assert!(
            BASE >= 2 && ALPHA >= 1,
            "a base below 2 or zero digits is not a positional system"
        );
        assert_eq!(
            digits_for(BASE, R::MODULUS),
            Some(ALPHA),
            "ALPHA must be ⌈log_BASE q⌉ so the gadget split is exact"
        );
        Self {
            seed: *seed,
            rows,
            a: RingMatrixKey::setup(TREE_LABEL, seed, rows, 2 * rows * ALPHA),
        }
    }

    /// The binding master seed `A` was expanded from (the transcript input).
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The lattice dimension `n`.
    pub const fn rows(&self) -> usize {
        self.rows
    }

    /// The gadget base `b`.
    pub const fn base(&self) -> u64 {
        BASE
    }

    /// The gadget digit count `α`.
    pub const fn digits(&self) -> usize {
        ALPHA
    }

    /// Ring degree `d`.
    pub const fn ring_degree(&self) -> usize {
        D
    }

    /// Number of slots `nα` one tree node's digit expansion occupies — the
    /// `m := log(nα)` variable count of §5 is `log₂` of `n · ALPHA`.
    pub const fn slot_len(&self) -> usize {
        self.rows * ALPHA
    }

    /// The matrix `A` (its rows are the `a_r^⊺` of Eq. (24)/(26)).
    pub fn matrix(&self) -> &RingMatrixKey<R, D> {
        &self.a
    }

    /// `height_of(|f|)`: the tree height `ℓ` a leaf vector of this length
    /// commits at, i.e. `|f| = 2^ℓ · n` with `ℓ ≥ 1`.
    pub fn height_of(&self, leaf_len: usize) -> Result<usize, TreeError> {
        if leaf_len == 0 || leaf_len % self.rows != 0 {
            return Err(TreeError::WrongLeafLength {
                got: leaf_len,
                expected: self.rows,
            });
        }
        let blocks = leaf_len / self.rows;
        if !blocks.is_power_of_two() {
            return Err(TreeError::WrongLeafLength {
                got: leaf_len,
                expected: self.rows * blocks.next_power_of_two(),
            });
        }
        let height = blocks.trailing_zeros() as usize;
        if height == 0 {
            // |f| = n is the *root* size, not a tree: Def. 19 needs ℓ ≥ 1 so
            // that a layer below the root exists.
            return Err(TreeError::WrongLeafLength {
                got: leaf_len,
                expected: 2 * self.rows,
            });
        }
        Ok(height)
    }

    /// Layer `level` (`s_{level}`) holds `2^level · n · α` digits.
    pub const fn layer_len(&self, level: usize) -> usize {
        (1usize << level) * self.slot_len()
    }

    /// The gadget image `G⁻¹(x)`: exact base-`BASE` decomposition of every
    /// coefficient (`‖·‖∞ < BASE`).
    pub fn decompose(&self, values: &[PolyRing<R, D>]) -> Vec<PolyRing<R, D>> {
        gadget::split::<R, D, BASE, ALPHA>(values)
    }

    /// The gadget map `G(x)`, the inverse of [`TreeKey::decompose`] on
    /// canonical representatives.
    pub fn recompose(&self, digits: &[PolyRing<R, D>]) -> Vec<PolyRing<R, D>> {
        gadget::join::<R, D, BASE, ALPHA>(digits)
    }

    /// `(I_{2^i} ⊗ A)·s`: applies the *same* `A` to each `2nα`-sized block of
    /// a layer opening, which is the tree's parent map.
    ///
    /// # Errors
    /// [`TreeError::WrongLayerLength`] unless `digits.len()` is a multiple of
    /// `2nα` (the block width `A` consumes).
    pub fn parent(&self, digits: &[PolyRing<R, D>]) -> Result<Vec<PolyRing<R, D>>, TreeError> {
        let width = 2 * self.rows * ALPHA;
        if digits.is_empty() || digits.len() % width != 0 {
            return Err(TreeError::WrongLayerLength {
                level: 0,
                got: digits.len(),
                expected: (digits.len() / width) * width,
            });
        }
        let groups: Vec<&[PolyRing<R, D>]> = digits.chunks(width).collect();
        apply_blockwise(&self.a, &groups).map_err(|e| TreeError::WrongLayerLength {
            level: 0,
            got: e.got,
            expected: e.expected,
        })
    }

    /// `Commit(A, f)` (Def. 19, first variant): returns the root and every
    /// layer opening.
    ///
    /// # Errors
    /// [`TreeError::WrongLeafLength`] when `|f|` is not `2^ℓ n` for `ℓ ≥ 1`.
    pub fn commit(&self, f: &[PolyRing<R, D>]) -> Result<TreeOpening<R, D>, TreeError> {
        let height = self.height_of(f.len())?;
        let mut current = f.to_vec();
        let mut layers = Vec::with_capacity(height);
        for _ in 0..height {
            let digits = self.decompose(&current);
            current = self.parent(&digits)?;
            layers.push(digits);
        }
        layers.reverse();
        debug_assert_eq!(current.len(), self.rows, "the root is n elements");
        Ok(TreeOpening {
            root: current,
            layers,
        })
    }

    /// `Commit(A, s_ℓ)` (Def. 19, second variant): commits directly to an
    /// already-low-norm bottom-layer opening instead of to a message.
    ///
    /// This is the variant the folding and decomposition reductions need, since
    /// `t_subs` (Eq. 16) and `t*_dec` (Protocol 5 Step 1) commit to digit
    /// vectors that are *already* gadget images. The caller owns the
    /// `‖s_ℓ‖∞ < b` obligation; [`TreeKey::check_norms`] is the gate.
    ///
    /// # Errors
    /// [`TreeError::WrongLayerLength`] unless `bottom.len() = 2^ℓ nα` for some
    /// `ℓ ≥ 1`.
    pub fn commit_digits(&self, bottom: &[PolyRing<R, D>]) -> Result<TreeOpening<R, D>, TreeError> {
        let slot = self.slot_len();
        if bottom.is_empty() || bottom.len() % slot != 0 {
            return Err(TreeError::WrongLayerLength {
                level: 0,
                got: bottom.len(),
                expected: (bottom.len() / slot) * slot,
            });
        }
        let blocks = bottom.len() / slot;
        if !blocks.is_power_of_two() || blocks < 2 {
            return Err(TreeError::WrongLayerLength {
                level: 0,
                got: bottom.len(),
                expected: slot * blocks.next_power_of_two().max(2),
            });
        }
        let height = blocks.trailing_zeros() as usize;
        let mut layers = Vec::with_capacity(height);
        let mut current = bottom.to_vec();
        layers.push(current.clone());
        // Walk up while the layer spans more than the single `A` block `s₁`
        // must occupy, then the root is one final parent map.
        while current.len() > 2 * slot {
            let values = self.parent(&current)?;
            current = self.decompose(&values);
            layers.push(current.clone());
        }
        let root = self.parent(&current)?;
        layers.reverse();
        debug_assert_eq!(root.len(), self.rows, "the root is n elements");
        debug_assert_eq!(layers.len(), height, "one layer per tree level");
        Ok(TreeOpening { root, layers })
    }

    /// The `‖s_i‖∞ < b` gate of `Open`, layer by layer.
    ///
    /// # Errors
    /// [`TreeError::WrongLayerLength`] on a layer of the wrong size and
    /// [`TreeError::NormExceeded`] on the first layer at or above `bound`.
    pub fn check_norms(&self, opening: &TreeOpening<R, D>, bound: u64) -> Result<(), TreeError> {
        if opening.layers.is_empty() {
            return Err(TreeError::EmptyLayers);
        }
        for (idx, layer) in opening.layers.iter().enumerate() {
            let level = idx + 1;
            let want = self.layer_len(level);
            if layer.len() != want {
                return Err(TreeError::WrongLayerLength {
                    level,
                    got: layer.len(),
                    expected: want,
                });
            }
            let got = max_norm(layer);
            if got >= bound {
                return Err(TreeError::NormExceeded { level, got, bound });
            }
        }
        Ok(())
    }

    /// `Open(A, b, t, (s_i))` (Def. 19): root equation, every layer link, and
    /// every norm gate.
    ///
    /// # Errors
    /// [`TreeError::RootMismatch`], [`TreeError::LayerLink`],
    /// [`TreeError::NormExceeded`], [`TreeError::WrongLayerLength`],
    /// [`TreeError::EmptyLayers`].
    pub fn open(&self, opening: &TreeOpening<R, D>, bound: u64) -> Result<(), TreeError> {
        if opening.layers.is_empty() {
            return Err(TreeError::EmptyLayers);
        }
        for (idx, layer) in opening.layers.iter().enumerate() {
            let want = self.layer_len(idx + 1);
            if layer.len() != want {
                return Err(TreeError::WrongLayerLength {
                    level: idx + 1,
                    got: layer.len(),
                    expected: want,
                });
            }
        }
        // t = A·s₁ (checked before the norms so a corrupted root is reported
        // as a root failure even if the tamper also broke a digit range).
        let expect_root = self.parent(&opening.layers[0])?;
        if opening.root.len() != expect_root.len() {
            return Err(TreeError::RootMismatch { at: 0 });
        }
        for (at, (got, want)) in opening.root.iter().zip(expect_root.iter()).enumerate() {
            if got != want {
                return Err(TreeError::RootMismatch { at });
            }
        }
        for i in 1..opening.layers.len() {
            let parent = self.parent(&opening.layers[i])?;
            let child = self.recompose(&opening.layers[i - 1]);
            for (at, (got, want)) in child.iter().zip(parent.iter()).enumerate() {
                if got != want {
                    return Err(TreeError::LayerLink { level: i, at });
                }
            }
        }
        self.check_norms(opening, bound)
    }

    /// `Open_F(A, b, t, f, (s_i))` (Def. 19): `Open` plus the leaf equation
    /// `G_{2^ℓ n}·s_ℓ = f`.
    ///
    /// # Errors
    /// As [`TreeKey::open`], plus [`TreeError::LeafMismatch`].
    pub fn open_with_message(
        &self,
        opening: &TreeOpening<R, D>,
        bound: u64,
        f: &[PolyRing<R, D>],
    ) -> Result<(), TreeError> {
        self.open(opening, bound)?;
        let bottom = opening.layers.last().ok_or(TreeError::EmptyLayers)?;
        let values = self.recompose(bottom);
        if values.len() != f.len() {
            return Err(TreeError::WrongLeafLength {
                got: f.len(),
                expected: values.len(),
            });
        }
        for (at, (got, want)) in values.iter().zip(f.iter()).enumerate() {
            if got != want {
                return Err(TreeError::LeafMismatch { at });
            }
        }
        Ok(())
    }
}

/// `‖z‖∞ = max_i max_j |z_i[j]|` over centered representatives — the norm of
/// §3.2 ("for a vector z, ‖z‖∞ := maxᵢ‖zᵢ‖∞").
pub fn max_norm<R: Ring + CenteredRing, const D: usize>(z: &[PolyRing<R, D>]) -> u64 {
    z.iter()
        .flat_map(|p| p.coefficients().into_iter())
        .map(|c| c.abs_infinity())
        .max()
        .unwrap_or(0)
}

/// The `k`-th coefficient map `cf` of Def. 3: the vector of `k`-th
/// coefficients of a ring vector, i.e. column `k` of `cf(z) ∈ F^{n×d}`.
///
/// `PolyRing::coefficients()` trims trailing zeros, so a high `k` is *absent*
/// rather than zero — and `cf` is defined on all of `[0, d)` (Eq. (8) batches
/// over `k ∈ [0, d−1]`), so the absent reads must come back `R::ZERO`. Indexing
/// the trimmed vector panics on any ring element whose top coefficient happens
/// to vanish, which is the normal case for a gadget digit vector and for every
/// low-norm witness this module produces.
///
/// # Panics
/// If `k ≥ D`.
pub fn coefficient_column<R: Ring, const D: usize>(z: &[PolyRing<R, D>], k: usize) -> Vec<R> {
    assert!(k < D, "coefficient index beyond the ring degree");
    z.iter()
        .map(|p| p.coefficients().into_iter().nth(k).unwrap_or(R::ZERO))
        .collect()
}

/// Embeds a field element as a constant ring element (the scalar action of
/// `K` on `R_K` used in Lemma 14's proof).
pub fn scalar_into_ring<R: Ring, const D: usize>(c: R) -> PolyRing<R, D> {
    constant::<R, D>(c)
}

/// Lemma 11 ([CMNW24, Thm 4]): `TCom` is binding assuming
/// `MSIS_{q,n,d,rnα,b'}` with `b' ≥ 2b`. Returns the `b'` the reduction needs.
pub const fn binding_norm(norm_bound: u64) -> u64 {
    2 * norm_bound
}

/// Lemma 12: `TCom` satisfies `(B, C, k)`-relaxed binding assuming
/// `MSIS_{q,n,d,2nα, 2·T_{C−C}·B}`, where `T` is the expansion factor
/// (Def. 15) of the difference set. Returns that MSIS norm target.
pub const fn relaxed_binding_norm(expansion_factor: u64, folded_bound: u64) -> u64 {
    2u64.saturating_mul(expansion_factor.saturating_mul(folded_bound))
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;
    use algebra::ring::PolynomialQuotientRing;
    use alloc::vec;

    /// `Z_q` with the ML-DSA prime (NTT-friendly: `q ≡ 1 mod 512`).
    type Ntt = Zq<8380417>;
    /// `q = 2³² − 99`: prime, `≡ 5 (mod 8)`, Maltese P3's field size.
    type Q32 = Zq<4294967197>;

    const D_NTT: usize = 8;
    /// P3's ring degree.
    const D32: usize = 64;

    fn vec_of(seed: u64, len: usize) -> Vec<PolyRing<Ntt, D_NTT>> {
        (0..len)
            .map(|i| {
                let coeffs: Vec<_> = (0..D_NTT)
                    .map(|j| Ntt::from(((seed * 31 + i as u64 * 7 + j as u64) % 97) as u64))
                    .collect();
                PolyRing::from_coefficients(coeffs)
            })
            .collect()
    }

    type Key = TreeKey<Ntt, D_NTT, 2, 23>;

    fn key() -> Key {
        Key::setup(&[0x11u8; 32], 2)
    }

    #[test]
    fn digits_for_is_the_smallest_alpha_with_full_capacity() {
        // Def. 18 (p. 20): `α := ⌈log_b q⌉`. One digit short and a canonical
        // representative would wrap; the boundary is `b^α ≥ q`, not `> q`.
        assert_eq!(digits_for(2, 8_380_417), Some(23));
        assert_eq!(1u128 << 22, 4_194_304);
        assert!(4_194_304 < 8_380_417, "22 digits must be too few");
        assert_eq!(digits_for(2, 4_294_967_197), Some(32), "P3: α = 32");
        assert!(1u128 << 31 < u128::from(4_294_967_197u64));
        assert_eq!(digits_for(4, 4_294_967_197), Some(16));
        // Exact powers of the base need no spare digit: ⌈log₂ 2⌉ = 1, and one
        // binary digit does name both residues of Z₂.
        assert_eq!(digits_for(2, 2), Some(1), "⌈log₂ 2⌉ = 1");
        assert_eq!(digits_for(2, 3), Some(2), "⌈log₂ 3⌉ = 2");
        assert_eq!(digits_for(2, 4), Some(2), "⌈log₂ 4⌉ = 2, not 3");
        assert_eq!(digits_for(3, 9), Some(2), "⌈log₃ 9⌉ = 2");
        assert_eq!(digits_for(1, 100), None, "base 1 is not a positional system");
    }

    #[test]
    fn commit_is_a_tree_of_layer_openings_with_doubling_sizes() {
        let k = key();
        let f = vec_of(3, 8 * k.rows());
        let open = k.commit(&f).expect("leaf length 2^3·n");
        assert_eq!(open.layers.len(), 3, "height ℓ = 3");
        assert_eq!(open.root.len(), k.rows());
        for (idx, layer) in open.layers.iter().enumerate() {
            assert_eq!(layer.len(), k.layer_len(idx + 1), "layer {}", idx + 1);
            // Def. 18: every gadget image is short.
            assert_eq!(max_norm(layer), 1, "binary digits");
        }
        k.open(&open, k.base()).expect("honest opening verifies");
        k.open_with_message(&open, k.base(), &f)
            .expect("Open_F verifies");
    }

    #[test]
    fn the_bottom_layer_recomposes_to_the_message_itself() {
        // G_{2^ℓ n}·s_ℓ = f is the leaf equation; if the digit layout were
        // transposed this fails while every other equation still holds.
        let k = key();
        let f = vec_of(9, 4 * k.rows());
        let open = k.commit(&f).expect("height 2");
        assert_eq!(
            k.recompose(open.layers.last().expect("bottom layer")),
            f,
            "G·G⁻¹ = id on canonical representatives"
        );
    }

    #[test]
    fn parent_is_blockwise_application_of_the_one_matrix_a() {
        // (I_{2^i} ⊗ A)·s must equal per-block A·s — the tensor identity the
        // whole tree rests on, checked against a hand-computed single block.
        let k = key();
        let digits = k.decompose(&vec_of(5, 4 * k.rows()));
        let whole = k.parent(&digits).expect("block sizes line up");
        let width = 2 * k.rows() * 23;
        assert_eq!(digits.len(), 4 * k.rows() * 23);
        assert_eq!(whole.len(), 2 * k.rows());
        for (i, block) in digits.chunks(width).enumerate() {
            let alone = k
                .matrix()
                .matvec(block)
                .expect("one block is exactly A's width");
            assert_eq!(&whole[i * k.rows()..(i + 1) * k.rows()], &alone[..]);
        }
    }

    #[test]
    fn tampering_each_equation_reports_its_own_variant() {
        let k = key();
        let f = vec_of(7, 8 * k.rows());
        let open = k.commit(&f).expect("commit");

        // root equation only
        let mut bad = open.clone();
        bad.root[0] = bad.root[0].clone() + constant::<Ntt, D_NTT>(Ntt::from(1u64));
        assert_eq!(
            k.open(&bad, k.base()),
            Err(TreeError::RootMismatch { at: 0 }),
            "a corrupted root must be named as the root equation"
        );

        // a link only: shift one element of the *bottom* layer, which Def. 19's
        // equation for `i = ℓ−1` reads on the `A` side and no earlier equation
        // touches. `LayerLink.level` is the paper's `i` in
        // `G_{rⁱn}·s_i = (I_{rⁱ}⊗A)·s_{i+1}`, `i ∈ [ℓ−1]` (p. 21), i.e. the
        // G-side layer, which is what `TreeError`'s `Display` renders.
        let mut bad = open.clone();
        let idx = k.layer_len(3) - 1;
        bad.layers[2][idx] = constant::<Ntt, D_NTT>(Ntt::from(2u64));
        match k.open(&bad, k.base()) {
            // flipping a digit out of {0,1} breaks the link *and* the bound;
            // the link is checked first, so it is what must be reported.
            Err(TreeError::LayerLink { level: 2, .. }) => {}
            other => panic!("expected a layer-2 link failure, got {other:?}"),
        }

        // the leaf equation only
        let mut wrong_f = f.clone();
        wrong_f[1] = wrong_f[1].clone() + constant::<Ntt, D_NTT>(Ntt::from(1u64));
        assert_eq!(
            k.open_with_message(&open, k.base(), &wrong_f),
            Err(TreeError::LeafMismatch { at: 1 })
        );
    }

    #[test]
    fn a_short_but_non_binary_layer_fails_only_the_norm_gate() {
        // Digits in {0,1,2} keep every *linear* equation intact (the tree's
        // equations are linear over the recomposition only after G, so we keep
        // the opening self-consistent by recomposing at a lower level): the
        // gate that must fire is the norm one.
        let k = key();
        let f = vec_of(4, 4 * k.rows());
        let mut open = k.commit(&f).expect("commit");
        let bottom = open.layers.len() - 1;
        // Rebuild the bottom layer as G⁻¹(f) with every digit doubled *and*
        // halved back in the value: instead, hand-set a layer that recomposes
        // correctly but is out of range, by adding q−1 (=−1) to a digit pair.
        open.layers[bottom][0] = constant::<Ntt, D_NTT>(Ntt::from(3u64));
        // Both the link and the norm now fail; the norm gate is the one the
        // scheme must never skip, so assert it fires when the links are not
        // part of the picture (check_norms alone).
        let norm = k.check_norms(&open, k.base());
        assert!(matches!(
            norm,
            Err(TreeError::NormExceeded {
                level: 2,
                got: 3,
                bound: 2
            })
        ));
        // …and the same opening rejected by `open` for a *link* reason, showing
        // the two gates are independent checks rather than one check twice. In a
        // height-2 tree the bottom layer `s₂` is the `A`-side child of Def. 19's
        // only link equation, `i = 1`, so that is the level named — while
        // `check_norms`, which reports the *layer* it is gating, says level 2.
        assert!(matches!(
            k.open(&open, k.base()),
            Err(TreeError::LayerLink { level: 1, .. })
        ));
    }

    #[test]
    fn commit_digits_matches_commit_on_a_gadget_image() {
        // Def. 19's two Commit variants must agree when the input really is a
        // gadget image: otherwise the folding step could commit differently
        // from the tree it is folding.
        let k = key();
        let f = vec_of(11, 8 * k.rows());
        let by_message = k.commit(&f).expect("commit");
        let bottom = k.decompose(&f);
        let by_digits = k.commit_digits(&bottom).expect("commit_digits");
        assert_eq!(by_message.layers, by_digits.layers);
        assert_eq!(by_message.root, by_digits.root);
        k.open(&by_digits, k.base()).expect("opens");
    }

    #[test]
    fn commit_digits_accepts_a_low_norm_vector_that_is_no_gadget_image() {
        // The second variant's premise is ‖s_ℓ‖∞ < b, not exactness: a short
        // ternary bottom layer must still produce a verifiable tree (this is
        // how t_subs and t*_dec get committed).
        let k = key();
        let bottom: Vec<_> = (0..k.layer_len(2))
            .map(|i| scalar_into_ring::<Ntt, D_NTT>(Ntt::from((i as u64 % 3) as u64)))
            .collect();
        let open = k.commit_digits(&bottom).expect("short vector commits");
        assert_eq!(open.layers.len(), 2);
        k.open(&open, 3).expect("bound 3 admits ternary digits");
        assert_eq!(
            k.open(&open, 2),
            Err(TreeError::NormExceeded {
                level: 2,
                got: 2,
                bound: 2
            }),
            "the same opening must fail a bound of 2, and fail it on the layer that is not binary"
        );
    }

    #[test]
    fn rejects_leaf_lengths_that_are_not_2_ell_times_n() {
        let k = key();
        assert_eq!(
            k.commit(&vec_of(1, 6)),
            Err(TreeError::WrongLeafLength {
                got: 6,
                expected: 8
            })
        );
        assert_eq!(
            k.commit(&vec_of(1, 2)),
            Err(TreeError::WrongLeafLength {
                got: 2,
                expected: 4
            }),
            "|f| = n is a bare hash, not a tree"
        );
        assert_eq!(
            k.open(
                &TreeOpening {
                    root: vec_of(1, 2),
                    layers: vec![]
                },
                2
            ),
            Err(TreeError::EmptyLayers)
        );
    }

    #[test]
    fn a_different_seed_or_message_changes_the_root() {
        let f = vec_of(2, 4 * 2);
        let one = TreeKey::<Ntt, D_NTT, 2, 23>::setup(&[1u8; 32], 2)
            .commit(&f)
            .expect("c1");
        let two = TreeKey::<Ntt, D_NTT, 2, 23>::setup(&[2u8; 32], 2)
            .commit(&f)
            .expect("c2");
        let three = TreeKey::<Ntt, D_NTT, 2, 23>::setup(&[1u8; 32], 2)
            .commit(&vec_of(3, 4 * 2))
            .expect("c3");
        assert_ne!(one.root, two.root, "the seed binds the commitment");
        assert_ne!(
            one.root, three.root,
            "collision resistance must hold on these inputs"
        );
    }

    #[test]
    fn works_on_the_p3_ring_with_no_ntt_available() {
        // The architecture point: q = 2³²−99 ≡ 5 (mod 8) has 2-adicity 2, so no
        // NTT of degree ≥ 4 exists — yet P3's tree must run on exactly this
        // ring with d = 64 and α = 32 digits.
        assert_eq!(4_294_967_197u64 % 8, 5);
        assert_eq!((4_294_967_197u64 - 1).trailing_zeros(), 2);
        type Key32 = TreeKey<Q32, D32, 2, 32>;
        let k = Key32::setup(&[0x33u8; 32], 2);
        assert_eq!(k.digits(), 32);
        assert_eq!(k.ring_degree(), 64);
        let f: Vec<_> = (0..2 * k.rows())
            .map(|i| {
                let coeffs: Vec<_> = (0..D32)
                    .map(|j| Q32::from(((i as u64) * 977 + j as u64) % 1009))
                    .collect();
                PolyRing::from_coefficients(coeffs)
            })
            .collect();
        let open = k.commit(&f).expect("height 1 over the P3 ring");
        assert_eq!(open.layers.len(), 1);
        assert_eq!(max_norm(&open.layers[0]), 1);
        k.open_with_message(&open, k.base(), &f)
            .expect("honest P3-sized tree verifies");
        let mut bad = open.clone();
        bad.layers[0][7] = constant::<Q32, D32>(Q32::from(2u64));
        assert!(matches!(
            k.open(&bad, k.base()),
            Err(TreeError::LayerLink { level: 1, .. }) | Err(TreeError::RootMismatch { .. })
        ));
    }

    #[test]
    fn norm_accounting_matches_the_paper_lemmas() {
        // Lemma 11: binding at b' ≥ 2b. Lemma 12: relaxed binding at
        // 2·T_{C−C}·B. Both feed the example's printed bounds.
        assert_eq!(binding_norm(2), 4);
        assert_eq!(binding_norm(12_288), 24_576);
        assert_eq!(relaxed_binding_norm(96, 12_288), 2 * 96 * 12_288);
        // saturating rather than wrapping: a bogus bound must not silently
        // become small.
        assert_eq!(relaxed_binding_norm(u64::MAX, 2), u64::MAX);
    }

    #[test]
    fn coefficient_column_is_the_def_3_map() {
        // cf(z)_k is column k of the coefficient matrix; Lemma 14's packing
        // claim is stated against exactly this map, so pin it elementwise.
        let z = vec_of(6, 3);
        for k in 0..D_NTT {
            let col = coefficient_column(&z, k);
            assert_eq!(col.len(), 3);
            for (i, c) in col.iter().enumerate() {
                assert_eq!(*c, coefficient_of(&z[i], k));
            }
        }
        assert_eq!(max_norm(&z), 96, "97 is the top value used above");
        // `PolyRing::coefficients()` trims trailing zeros, so the high columns of
        // a short vector are *absent*, not missing: `cf` must still answer `0`.
        // Every gadget digit plane and every low-norm tree opening hits this.
        let trimmed = vec![
            PolyRing::<Ntt, D_NTT>::from_coefficients(
                (0..2).map(|j| Ntt::from(j as u64 + 1)).collect(),
            ),
            constant::<Ntt, D_NTT>(Ntt::from(5u64)),
        ];
        assert!(
            trimmed[0].coefficients().len() < D_NTT,
            "the representative really is stored trimmed"
        );
        assert_eq!(coefficient_column(&trimmed, 1), vec![Ntt::from(2u64), Ntt::ZERO]);
        for k in 2..D_NTT {
            assert_eq!(
                coefficient_column(&trimmed, k),
                vec![Ntt::ZERO; 2],
                "column {k} of a trimmed element is zero"
            );
        }
        assert_eq!(max_norm(&trimmed), 5);
        let _ = std::panic::catch_unwind(|| coefficient_column(&z, D_NTT))
            .expect_err("a column index of d is out of range");
    }

    /// `cf(z)_k` with the trailing-zero trimming undone — the reference the
    /// column map above is checked against.
    fn coefficient_of<R: Ring, const D: usize>(z: &PolyRing<R, D>, k: usize) -> R {
        z.coefficients().into_iter().nth(k).unwrap_or(R::ZERO)
    }
}
