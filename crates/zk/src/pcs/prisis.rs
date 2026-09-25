//! The PRISIS / PowerBASIS trapdoor commitment (SLAP §4, FMN §4).
//!
//! Both papers publish a matrix `B` that stacks several scaled copies of one
//! Ajtai matrix against a shared gadget column, together with a gadget
//! trapdoor for it, and commit by taking short preimages under `B`:
//!
//! ```text
//! FMN 2023/846 Fig. 4 (PowerBASIS, message length d+1)
//!   B  = [ W⁰A   0   … −G ]        Rᵢ := R·G⁻¹(W⁻ⁱG)
//!        [  0   W¹A  … −G ]   R̃ = [ R₀ ; … ; R_d ; 0 ]     B·R̃ = G_{n(d+1)}
//!        [  …              ]
//!        [  0    …  W^dA −G ]
//!
//! SLAP 2023/1469 Fig. 4 (Merkle-PRISIS, ℓ = 2 slots per level)
//!   B_j = [ A_j    0  −G ]
//!         [  0   w_jA_j −G ]
//! ```
//!
//! The two are one object: SLAP's `w_j` is FMN's `W = w·Iₙ`, and at `d+1 = 2`
//! FMN's block-diagonal `WⁱA` *is* SLAP's printed `[[A,0,−G],[0,wA,−G]]` —
//! checked entry-by-entry in
//! [`basis_pair_specialises_to_the_printed_slap_matrix`](tests) below.
//!
//! # Why a trapdoor is unavoidable here
//!
//! A SLAP tree node must satisfy, against **one** shared child value,
//! `t_{b,0} = A_j·s_{b,0} + G·t̂_b` and `t_{b,1} = w_j·A_j·s_{b,1} + G·t̂_b`.
//! Given the two children (fixed by the level below) the prover has to find the
//! parent `t_b = G·t̂_b` *and* both short openings at once: that is the joint
//! equation `B_j·(s_{b,0}, s_{b,1}, t̂_b)ᵗ = (−t_{b,0}, −t_{b,1})ᵗ`, i.e. a short
//! preimage under `B_j`. Gap G2 (no `TrapGen`/`SamplePre`) is what blocked these
//! two schemes, and [`TrapdoorKey`] is what unblocks them.
//!
//! # Deviations from the papers, stated
//!
//! * [`TrapdoorKey`]'s sampler is the Gaussian-free skeleton licensed by MP12
//!   Alg. 3's algebra and SLAP App. C's "deterministic preimage sampling".
//!   Hence [`BasisPair::randomise_trapdoor`] uses a bounded perturbation rather
//!   than a Gaussian parameter: the CRS `T` is short and random and obeys
//!   `B·T = G_{n(d+1)}` **exactly**, but the papers' σ-conditions
//!   (`σ₀ ≥ δ‖R̃‖·ω(√…)` in SLAP Lem. 4.1 / FMN Lem. 4.1) and their
//!   zero-knowledge simulations are *not* discharged here. The norm gates below
//!   are certified bounds derived from the keys ([`BasisPair::certified_bound`]),
//!   not Gaussian tails.
//! * `W` is a [`UnitMatrix`] — a certified unit pair, here a diagonal of scalar
//!   units — rather than a uniform `GL(n, R_q)` draw, because the crate has no
//!   solver over `R_q`. Every equation that uses `W` is still verified exactly.
//! * One message slot is one ring element and the leaf value is `f·e₁ ∈ Rⁿ`, as
//!   in both figures.

use crate::pcs::key::RingMatrixKey;
use crate::pcs::trapdoor::{
    add_vec, gadget_apply, gadget_inverse_matrix, gadget_matrix, hstack, matmul, neg_vec,
    preimage_random_with_trapdoor, preimage_with_trapdoor, scalar_elt, scale_vec, sub_vec,
    trapdoor_relation, vstack, zero_matrix, Elt, TrapError, TrapdoorKey, UnitMatrix,
};
use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::{Field, Ring};
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec;
use alloc::vec::Vec;

/// Maps a seed and a level index to a nonzero scalar of `R_q`, i.e. a unit.
///
/// The reduction is into `[1, q−1]`, so the draw can never be zero — a zero
/// `w_j` would collapse the right-hand branch of the tree to `0 = 0`.
fn unit_from_seed<R: Ring>(domain: &[u8], seed: &[u8; 32], tag: u64) -> R {
    let mut xof = Shake256Xof::new(&[]);
    xof.absorb(domain);
    xof.absorb(seed);
    xof.absorb(&tag.to_le_bytes());
    let mut buf = [0u8; 8];
    xof.squeeze(&mut buf);
    let raw = u64::from_le_bytes(buf);
    // into 1..q (q ≥ 2, so the range is inhabited)
    R::from(raw % (R::MODULUS - 1) + 1)
}

/// The `(d+1)`-slot BASIS matrix `B`, its raw trapdoor `R̃`, and what is needed
/// to check an opening.
#[derive(Clone)]
pub struct BasisPair<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> {
    a: RingMatrixKey<R, D>,
    b: RingMatrixKey<R, D>,
    rt: RingMatrixKey<R, D>,
    w_pow: Vec<RingMatrixKey<R, D>>,
    w_inv_pow: Vec<RingMatrixKey<R, D>>,
    slots: usize,
    n: usize,
    m: usize,
    t: usize,
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> core::fmt::Debug
    for BasisPair<R, D, BASE, DIGITS>
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(
            f,
            "BasisPair<slots {}, B {}×{}>",
            self.slots,
            self.b.rows(),
            self.b.cols()
        )
    }
}

/// A `B`-preimage split the way the two figures split it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasisOpening<R: Ring, const D: usize> {
    /// Slot `i`'s opening `sᵢ ∈ R^m`.
    pub s: Vec<Vec<Elt<R, D>>>,
    /// The shared gadget part `t̂ ∈ R^{n·DIGITS}`.
    pub t_hat: Vec<Elt<R, D>>,
}

/// A commitment and its opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BasisCommitment<R: Ring, const D: usize> {
    /// `t = G·t̂ ∈ Rⁿ`.
    pub t: Vec<Elt<R, D>>,
    /// The per-slot openings and the shared `t̂`.
    pub opening: BasisOpening<R, D>,
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> BasisPair<R, D, BASE, DIGITS> {
    /// FMN Fig. 4 items 1–4 (SLAP Fig. 4 items 2–5): from a TrapGen key and a
    /// unit `W`, build `B` and `R̃`, and assert `B·R̃ = G_{n(d+1)}`.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if `slots == 0` or `W` is not `n × n` for the
    /// key's height `n`. The relation is asserted, not returned: it is a
    /// property of this constructor, and a failure is a bug here.
    pub fn new(
        td: &TrapdoorKey<R, D, BASE, DIGITS>,
        w: &UnitMatrix<R, D>,
        slots: usize,
    ) -> Result<Self, TrapError> {
        if slots == 0 {
            return Err(TrapError::WrongShape {
                got: 0,
                expected: 1,
            });
        }
        let n = td.rows();
        if w.size() != n {
            return Err(TrapError::WrongShape {
                got: w.size(),
                expected: n,
            });
        }
        let (m, t) = (td.public().cols(), td.gadget_width());
        let g = td.gadget();
        let (w_pow, w_inv_pow) = w.powers(slots);
        // Rᵢ = R_trap · G⁻¹(W⁻ⁱ·G), one m×t block per slot — but `G⁻¹` must be
        // taken of the gadget **embedded in slot i of the wide one**, because
        // `B`'s gadget column is `t·slots` wide: with the narrow `W⁻ⁱ·G` the
        // preimage comes back `t` columns wide and no longer stacks against the
        // zero block that closes `R̃`.
        let mut blocks: Vec<RingMatrixKey<R, D>> = Vec::with_capacity(slots + 1);
        for i in 0..slots {
            let wi_g = matmul(&w_inv_pow[i], &g)?;
            let embedded = hstack(&[
                &zero_matrix::<R, D>(n, i * t),
                &wi_g,
                &zero_matrix::<R, D>(n, (slots - i - 1) * t),
            ])?;
            blocks.push(matmul(
                td.trapdoor(),
                &gadget_inverse_matrix::<R, D, BASE, DIGITS>(&embedded)?,
            )?);
        }
        blocks.push(zero_matrix::<R, D>(t, t * slots));
        let refs: Vec<&RingMatrixKey<R, D>> = blocks.iter().collect();
        let rt = vstack(&refs)?;
        // Block row i of B is [ 0 … WⁱA … 0 | −G ].
        let mut rows: Vec<Vec<Elt<R, D>>> = Vec::with_capacity(n * slots);
        for i in 0..slots {
            let wi_a = matmul(&w_pow[i], td.public())?;
            for r in 0..n {
                let mut row = vec![scalar_elt::<R, D>(R::ZERO); m * slots + t];
                for c in 0..m {
                    row[i * m + c] = wi_a
                        .get(r, c)
                        .cloned()
                        .unwrap_or_else(|| scalar_elt::<R, D>(R::ZERO));
                }
                for c in 0..t {
                    row[m * slots + c] = -g
                        .get(r, c)
                        .cloned()
                        .unwrap_or_else(|| scalar_elt::<R, D>(R::ZERO));
                }
                rows.push(row);
            }
        }
        let b = RingMatrixKey::from_entries(n * slots, m * slots + t, rows.concat());
        let pair = Self {
            a: td.public().clone(),
            b,
            rt,
            w_pow,
            w_inv_pow,
            slots,
            n,
            m,
            t,
        };
        assert!(
            trapdoor_relation::<R, D, BASE, DIGITS>(&pair.b, &pair.rt).expect("composable"),
            "B.Rt must equal the height n(d+1) gadget"
        );
        Ok(pair)
    }

    /// The stacked matrix `B ∈ R_q^{n(d+1) × (m(d+1)+nδ)}`.
    pub fn b(&self) -> &RingMatrixKey<R, D> {
        &self.b
    }

    /// The raw trapdoor `R̃` with `B·R̃ = G_{n(d+1)}`.
    pub fn raw_trapdoor(&self) -> &RingMatrixKey<R, D> {
        &self.rt
    }

    /// The underlying Ajtai matrix `A`.
    pub fn a(&self) -> &RingMatrixKey<R, D> {
        &self.a
    }

    /// `W⁰, …, W^d`.
    pub fn w_pow(&self) -> &[RingMatrixKey<R, D>] {
        &self.w_pow
    }

    /// `Iₙ, W⁻¹, …, W^{-d}`.
    pub fn w_inv_pow(&self) -> &[RingMatrixKey<R, D>] {
        &self.w_inv_pow
    }

    /// Slot count `d+1`.
    pub fn slots(&self) -> usize {
        self.slots
    }

    /// Module rank `n`.
    pub fn n(&self) -> usize {
        self.n
    }

    /// Columns of `A` = the length of one slot's opening.
    pub fn slot_len(&self) -> usize {
        self.m
    }

    /// Gadget width `t = n·DIGITS` = the length of `t̂`.
    pub fn gadget_width(&self) -> usize {
        self.t
    }

    /// `G_{n(d+1)}`, the gadget the CRS trapdoor must hit.
    pub fn gadget_of_b(&self) -> RingMatrixKey<R, D> {
        gadget_matrix::<R, D, BASE, DIGITS>(self.n * self.slots)
    }

    /// The certified `‖·‖∞` bound on a preimage taken through `trap`: every
    /// honest opening satisfies `‖sᵢ‖∞ ≤` this, which is the `γ` the figures'
    /// norm gate consumes.
    ///
    /// Derived by [`certified_preimage_bound`] from the actual entries of
    /// `trap`, not from a worst case over the sampling distribution. The bound
    /// is the *tight* one on purpose: the gate has to leave room below
    /// `(q − 1)/2` for a falsifying opening to be representable at all, and the
    /// looser form [`crate::pcs::trapdoor::bound_of_matrix`] returns overshoots
    /// `q/2` at this crate's ring degree on a `(d + 1)`-slot basis.
    pub fn certified_bound(&self, trap: &RingMatrixKey<R, D>) -> u64 {
        certified_preimage_bound::<R, D, BASE, DIGITS>(trap, 0)
    }

    /// FMN Fig. 4 item 5 / SLAP Fig. 4 item 6: `T ← SamplePre(B, R̃, G_{n(d+1)})`.
    ///
    /// Each column of the gadget is sampled with its own perturbation, derived
    /// from `(seed, column)`. The result is asserted to satisfy
    /// `B·T = G_{n(d+1)}` exactly.
    ///
    /// With `perturbation = 0` this returns `R̃` itself, whose bottom `t` rows
    /// are zero — and then `t = G·t̂` would be `0` for every message, which is
    /// why a nonzero perturbation is not an optimisation here. See
    /// [`BasisPair::commit`].
    ///
    /// # Errors
    /// [`TrapError::NotComposable`] if `R̃` is not `B`-shaped.
    pub fn randomise_trapdoor(
        &self,
        seed: &[u8; 32],
        perturbation: u32,
    ) -> Result<RingMatrixKey<R, D>, TrapError> {
        let want = self.gadget_of_b();
        let mut cols = Vec::with_capacity(want.cols());
        for j in 0..want.cols() {
            let target = (0..want.rows())
                .map(|i| want.get(i, j).cloned().unwrap())
                .collect::<Vec<_>>();
            let mut col_seed = *seed;
            for (k, b) in col_seed.iter_mut().enumerate() {
                *b ^= ((j as u64).to_le_bytes()[k % 8])
                    .wrapping_mul(0x9E)
                    .wrapping_add(k as u8);
            }
            cols.push(preimage_random_with_trapdoor::<R, D, BASE, DIGITS>(
                &self.b,
                &self.rt,
                &target,
                b"crs",
                &col_seed,
                perturbation,
            )?);
        }
        let mut entries = vec![scalar_elt::<R, D>(R::ZERO); self.rt.rows() * cols.len()];
        for (j, c) in cols.iter().enumerate() {
            for (i, e) in c.iter().enumerate() {
                entries[i * cols.len() + j] = e.clone();
            }
        }
        let t = RingMatrixKey::from_entries(self.rt.rows(), cols.len(), entries);
        assert!(
            trapdoor_relation::<R, D, BASE, DIGITS>(&self.b, &t).expect("composable"),
            "the randomised CRS trapdoor must satisfy B.T = the height n(d+1) gadget"
        );
        Ok(t)
    }

    /// Commit step 2: the target `u = (−fᵢ·Wⁱ·e₁)ᵢ ∈ R^{n(d+1)}`.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] unless `f` has one ring element per slot.
    pub fn commit_target(&self, f: &[Elt<R, D>]) -> Result<Vec<Elt<R, D>>, TrapError> {
        if f.len() != self.slots {
            return Err(TrapError::WrongShape {
                got: f.len(),
                expected: self.slots,
            });
        }
        let e1 = self.first_basis();
        let mut u = Vec::with_capacity(self.n * self.slots);
        for i in 0..self.slots {
            let wie1 = self.w_pow[i].matvec(&e1).map_err(shape)?;
            u.extend(neg_vec(&scale_vec(&f[i], &wie1)));
        }
        Ok(u)
    }

    /// Commit steps 3–4: the preimage through `trap`, split into
    /// `(s₀, …, s_d, t̂)`, and `t = G·t̂`.
    ///
    /// # Errors
    /// As [`commit_target`], plus the preimage's own shape refusals.
    pub fn commit(
        &self,
        trap: &RingMatrixKey<R, D>,
        f: &[Elt<R, D>],
    ) -> Result<BasisCommitment<R, D>, TrapError> {
        let u = self.commit_target(f)?;
        let x = preimage_with_trapdoor::<R, D, BASE, DIGITS>(&self.b, trap, &u)?;
        let s: Vec<Vec<Elt<R, D>>> = (0..self.slots)
            .map(|i| x[i * self.m..(i + 1) * self.m].to_vec())
            .collect();
        let t_hat = x[self.slots * self.m..].to_vec();
        let t = gadget_apply::<R, D, BASE, DIGITS>(&t_hat);
        Ok(BasisCommitment {
            t,
            opening: BasisOpening { s, t_hat },
        })
    }

    /// Every `Open` equation of FMN Fig. 4 / SLAP Fig. 4 that does **not** hold,
    /// named, without short-circuiting: `A·sᵢ + fᵢ·e₁ = W⁻ⁱ·t` per slot, plus the
    /// recomposition `G·t̂ = t` binding the opening to the commitment.
    ///
    /// Listing the whole set (rather than the first failure) is what lets a
    /// caller attribute a tamper to exactly the equations it trips.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if any input vector has the wrong length.
    pub fn failing(
        &self,
        commitment: &BasisCommitment<R, D>,
        f: &[Elt<R, D>],
    ) -> Result<Vec<String>, TrapError> {
        let mut bad = failing_basis_relation(
            &self.a,
            &self.w_inv_pow,
            &commitment.t,
            f,
            &commitment.opening.s,
        )?;
        if gadget_apply::<R, D, BASE, DIGITS>(&commitment.opening.t_hat) != commitment.t {
            bad.push("recompose(t = G t-hat)".to_string());
        }
        Ok(bad)
    }

    /// The `‖cᵢ·sᵢ‖∞ ≤ γ` relaxation gate of both figures' `Open`, as the slots
    /// that fail it.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] unless `c` has one multiplier per slot.
    pub fn failing_norms(
        &self,
        commitment: &BasisCommitment<R, D>,
        c: &[Elt<R, D>],
        gamma: u64,
    ) -> Result<Vec<String>, TrapError> {
        if c.len() != self.slots {
            return Err(TrapError::WrongShape {
                got: c.len(),
                expected: self.slots,
            });
        }
        Ok((0..self.slots)
            .filter(|i| {
                crate::pcs::trapdoor::vector_infinity_norm(&scale_vec(
                    &c[*i],
                    &commitment.opening.s[*i],
                )) > gamma
            })
            .map(|i| format!("norm(s[{i}]) <= {gamma}"))
            .collect())
    }

    /// The vector `e₁ ∈ Rⁿ`: the direction a leaf message is embedded in.
    pub fn first_basis(&self) -> Vec<Elt<R, D>> {
        let mut e1 = vec![scalar_elt::<R, D>(R::ZERO); self.n];
        e1[0] = scalar_elt::<R, D>(R::ONE);
        e1
    }
}

/// The certified `‖·‖∞` a gadget preimage `x = M·G⁻¹(v)` takes through `M`.
///
/// FMN Lem. 4.1 / SLAP Lem. 4.1 state completeness as a chain of Gaussian
/// parameter inequalities whose endpoint is the norm gate, `‖sᵢ‖ ≤ γ`. This
/// crate's sampler is the Gaussian-free skeleton of MP12 Alg. 3 (see
/// [`crate::pcs::trapdoor`]), so the same endpoint is reached in one algebraic
/// step, and it needs no distribution: `x` *is* `M·G⁻¹(v)`, and every entry of
/// `G⁻¹(v)` is a digit, hence `‖G⁻¹(v)_j‖∞ ≤ dz = ⌊BASE/2⌋`. With the ring
/// product's convolution inequality `‖a·b‖∞ ≤ ‖a‖₁·‖b‖∞` — each of the `D`
/// terms `a_i b_j` with `i + j ≡ k (mod D)` uses a distinct `i` —
///
/// ```text
/// ‖(M·z)ᵢ‖∞ ≤ Σ_j ‖M_ij‖₁ · ‖z_j‖∞ ≤ dz · Σ_j ‖M_ij‖₁
/// ```
///
/// so `dz · max_i Σ_j ‖M_ij‖₁` bounds every coordinate of every preimage
/// through `M`, which is the `γ` a scheme can publish. `worst_row_l1` is that
/// row sum, over the *coefficient-wise* `ℓ₁` of each ring entry.
///
/// [`crate::pcs::trapdoor::bound_of_matrix`] returns this quantity multiplied
/// by `D` as well, which is valid but `D` times looser: it converts the digit
/// bound from `‖·‖∞` to `‖·‖₁` (a factor `D`) *after* already summing the
/// matrix entries' coefficients (the same factor `D`). At `D = 64` that is the
/// difference between a gate that sits inside `R_q`'s centered range and one
/// that does not — which is why [`BasisPair::certified_bound`] derives its own.
#[must_use]
pub fn certified_preimage_bound<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    m: &RingMatrixKey<R, D>,
    extra: u64,
) -> u64 {
    let dz = crate::pcs::gadget::digit_half_width(BASE);
    let mut worst: u64 = 0;
    for i in 0..m.rows() {
        worst = worst.max(worst_row_l1::<R, D>(m, i));
    }
    extra.saturating_add(dz.saturating_mul(worst))
}

/// `Σ_j ‖M_ij‖₁` for one row: the sum over columns of the coefficient-wise `ℓ₁`
/// of each ring entry, in centered representatives (`min(x, q − x)`, which needs
/// only the modulus, as [`crate::pcs::trapdoor::vector_infinity_norm`] does).
#[must_use]
pub fn worst_row_l1<R: Ring, const D: usize>(m: &RingMatrixKey<R, D>, row: usize) -> u64 {
    m.row(row)
        .iter()
        .map(|e| {
            crate::foundation::encoding::ring_to_u32::<R, D>(e)
                .iter()
                .map(|&c| {
                    let x = u64::from(c);
                    x.min(R::MODULUS - x)
                })
                .sum::<u64>()
        })
        .sum()
}

/// One level of SLAP's Merkle-PRISIS CRS: `(A_j, w_j, T_j)`.
#[derive(Clone, Debug)]
pub struct PrisisLevel<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> {
    pair: BasisPair<R, D, BASE, DIGITS>,
    trap: RingMatrixKey<R, D>,
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>
    PrisisLevel<R, D, BASE, DIGITS>
{
    /// The level's public basis halves `(A_j, w_j)`.
    ///
    /// `trap` — SLAP Fig. 4 item 6's `T_j`, the `SamplePre` preimage with
    /// `B_j·T_j = G_{2n}` — is deliberately **not** reachable from here: Figs. 4
    /// and 5 print it inside `crs`, but no `Open`/`Verify` step reads it, only
    /// `Commit` does, so a scheme assembly that wants to stay on the verifier's
    /// side cannot accidentally consult the trapdoor.
    pub fn pair(&self) -> &BasisPair<R, D, BASE, DIGITS> {
        &self.pair
    }
}

/// SLAP Fig. 4's Merkle-PRISIS tree over `h` levels.
#[derive(Clone, Debug)]
pub struct PrisisTree<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> {
    levels: Vec<PrisisLevel<R, D, BASE, DIGITS>>,
    bound: u64,
}

/// A committed tree: the root and every internal node's opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TreeProof<R: Ring, const D: usize> {
    /// The root `t_ε = C ∈ Rⁿ`.
    pub root: Vec<Elt<R, D>>,
    /// One entry per internal node, ordered level-descending.
    pub nodes: Vec<NodeProof<R, D>>,
}

/// One internal node's opening.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeProof<R: Ring, const D: usize> {
    /// Level `j ∈ [h]`, `1` being the level whose children are the leaves'
    /// parents (Fig. 4 walks `j = h, …, 1`).
    pub level: usize,
    /// The parent path `b ∈ Z₂^{j−1}`, root-first bits as an integer.
    pub prefix: usize,
    /// Left child's Ajtai opening `s_{(b,0)} ∈ R^m`.
    pub s0: Vec<Elt<R, D>>,
    /// Right child's Ajtai opening `s_{(b,1)} ∈ R^m`.
    pub s1: Vec<Elt<R, D>>,
    /// The node's gadget part `t̂_b`.
    pub t_hat: Vec<Elt<R, D>>,
    /// `t_b = G·t̂_b`, the node's value at level `j−1`.
    pub value: Vec<Elt<R, D>>,
}

impl<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize> PrisisTree<R, D, BASE, DIGITS> {
    /// SLAP Fig. 4 `Setup(1^λ)` for `h` levels: per level run TrapGen, draw the
    /// unit `w_j`, build `B_j`/`R̃_j`, then randomise the CRS trapdoor `T_j`.
    /// Level index `j−1` in `levels` is level `j`, so the order matches the
    /// verification equation's `Σ_{j=1}^{h}`.
    ///
    /// # Panics
    /// If `h == 0`, or if a level cannot be built (a shape bug, not caller
    /// error).
    pub fn setup(seed: &[u8; 32], n: usize, mbar: usize, h: usize, perturbation: u32) -> Self
    where
        R: Field,
    {
        assert!(h > 0, "a tree needs at least one level");
        let mut levels = Vec::with_capacity(h);
        let mut bound = 0;
        for j in 1..=h {
            let label = format!("slap-level-{j}");
            let td = TrapdoorKey::<R, D, BASE, DIGITS>::generate(label.as_bytes(), seed, n, mbar);
            let w = UnitMatrix::<R, D>::scalar_units(&vec![
                unit_from_seed::<R>(
                    b"slap-w", seed, j as u64
                );
                n
            ])
            .expect("a nonzero scalar of a field ring is a unit");
            let pair = BasisPair::<R, D, BASE, DIGITS>::new(&td, &w, 2)
                .expect("the level shapes are consistent by construction");
            let mut tseed = *seed;
            for (k, b) in tseed.iter_mut().enumerate() {
                *b = seed[k] ^ (j as u8).wrapping_mul(31).wrapping_add(k as u8);
            }
            let trap = pair
                .randomise_trapdoor(&tseed, perturbation)
                .expect("the CRS preimage is well-shaped");
            bound = bound.max(pair.certified_bound(&trap));
            levels.push(PrisisLevel { pair, trap });
        }
        Self { levels, bound }
    }

    /// Number of levels `h`; the tree commits to `2^h` leaves.
    pub fn height(&self) -> usize {
        self.levels.len()
    }

    /// Level `j` (1-based).
    pub fn level(&self, j: usize) -> Option<&PrisisLevel<R, D, BASE, DIGITS>> {
        self.levels.get(j - 1)
    }

    /// The `‖s‖∞` bound every honest opening on this CRS obeys.
    pub fn certified_bound(&self) -> u64 {
        self.bound
    }

    /// SLAP Fig. 4 `Commit`: leaves `t_b = f_b·e₁` for `b ∈ Z₂^h`, then for
    /// `j = h, …, 1` and each `b ∈ Z₂^{j−1}` the joint preimage
    /// `(s_{(b,0)}, s_{(b,1)}, t̂_b)` under `B_j` of `(−t_{(b,0)}, −t_{(b,1)})`,
    /// setting `t_b := G·t̂_b`.
    ///
    /// # Panics
    /// If `leaves.len() != 2^h`, or if a level's own relation fails — the
    /// per-node assertions are the scheme's completeness statement, checked as
    /// it is built.
    pub fn commit(&self, leaves: &[Elt<R, D>]) -> TreeProof<R, D> {
        let h = self.height();
        assert_eq!(leaves.len(), 1 << h, "one leaf per root-to-leaf path");
        let n = self.levels[0].pair.n();
        // table[j][prefix] = t at level j (path of length j); j = h holds leaves
        let mut table: Vec<Vec<Vec<Elt<R, D>>>> =
            (0..=h).map(|j| vec![Vec::new(); 1 << j]).collect();
        for (b, f) in leaves.iter().enumerate() {
            table[h][b] = scale_vec(f, &self.levels[0].pair.first_basis());
        }
        let mut nodes: Vec<NodeProof<R, D>> = Vec::new();
        for j in (1..=h).rev() {
            let level = &self.levels[j - 1];
            for prefix in 0..(1 << (j - 1)) {
                let mut target = Vec::with_capacity(2 * n);
                for bit in 0..2 {
                    target.extend(neg_vec(&table[j][(prefix << 1) | bit]));
                }
                let x = preimage_with_trapdoor::<R, D, BASE, DIGITS>(
                    &level.pair.b,
                    &level.trap,
                    &target,
                )
                .expect("the target has B_j's height");
                let m = level.pair.slot_len();
                let value = gadget_apply::<R, D, BASE, DIGITS>(&x[2 * m..]);
                let node = NodeProof {
                    level: j,
                    prefix,
                    s0: x[..m].to_vec(),
                    s1: x[m..2 * m].to_vec(),
                    t_hat: x[2 * m..].to_vec(),
                    value: value.clone(),
                };
                // The two equations Fig. 4 is built from (sign convention of the
                // printed B_j: B_j·(s₀,s₁,t̂)ᵗ = (−t_{b,0}, −t_{b,1})ᵗ).
                let a_s0 = level.pair.a.matvec(&node.s0).expect("m columns");
                assert_eq!(
                    sub_vec(&value, &a_s0),
                    table[j][prefix << 1],
                    "left child: t_(b,0) = G t-hat_b - A_j s_(b,0)"
                );
                let a_s1 = level.pair.a.matvec(&node.s1).expect("m columns");
                let wa_s1 = level.pair.w_pow[1].matvec(&a_s1).expect("n rows");
                assert_eq!(
                    sub_vec(&value, &wa_s1),
                    table[j][(prefix << 1) | 1],
                    "right child: t_(b,1) = G t̂_b − w_j A_j s_(b,1)"
                );
                table[j - 1][prefix] = value;
                nodes.push(node);
            }
        }
        TreeProof {
            root: table[0][0].clone(),
            nodes,
        }
    }

    /// The openings `s_{b:j}` for the path `path` (root-first bits), one vector
    /// per level, exactly what Fig. 4's `Open` reads out of `st`.
    ///
    /// # Panics
    /// If `path.len() != h` or a node of the path is missing.
    pub fn path_openings(&self, proof: &TreeProof<R, D>, path: &[bool]) -> Vec<Vec<Elt<R, D>>> {
        assert_eq!(path.len(), self.height(), "one bit per level");
        let mut prefix = 0usize;
        let mut out = Vec::with_capacity(path.len());
        for (idx, bit) in path.iter().enumerate() {
            let j = idx + 1;
            let node = proof
                .nodes
                .iter()
                .find(|p| p.level == j && p.prefix == prefix)
                .unwrap_or_else(|| panic!("node (level {j}, prefix {prefix}) is not in the proof"));
            out.push(if *bit {
                node.s1.clone()
            } else {
                node.s0.clone()
            });
            prefix = (prefix << 1) | usize::from(*bit);
        }
        out
    }

    /// SLAP Fig. 4 `Open`: the named set of equations that do **not** hold.
    ///
    /// The single verification equation is
    /// `Σ_{j=1}^{h} w_j^{b_j}·A_j·s_{b:j} + f_b·e₁ = t`; the norm gate is
    /// [`PrisisTree::failing_norms`]. Both are non-short-circuiting.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if the path, the openings or a slot vector do
    /// not match the tree.
    pub fn failing(
        &self,
        root: &[Elt<R, D>],
        path: &[bool],
        f_b: &Elt<R, D>,
        openings: &[Vec<Elt<R, D>>],
    ) -> Result<Vec<String>, TrapError> {
        let h = self.height();
        if path.len() != h {
            return Err(TrapError::WrongShape {
                got: path.len(),
                expected: h,
            });
        }
        if openings.len() != h {
            return Err(TrapError::WrongShape {
                got: openings.len(),
                expected: h,
            });
        }
        let n = self.levels[0].pair.n();
        if root.len() != n {
            return Err(TrapError::WrongShape {
                got: root.len(),
                expected: n,
            });
        }
        let mut acc = vec![scalar_elt::<R, D>(R::ZERO); n];
        for (idx, s) in openings.iter().enumerate() {
            let level = &self.levels[idx].pair;
            if s.len() != level.slot_len() {
                return Err(TrapError::WrongShape {
                    got: s.len(),
                    expected: level.slot_len(),
                });
            }
            let mut term = level.a.matvec(s).map_err(shape)?;
            if path[idx] {
                term = level.w_pow[1].matvec(&term).map_err(shape)?;
            }
            acc = add_vec(&acc, &term);
        }
        let lhs = add_vec(&acc, &scale_vec(f_b, &self.levels[0].pair.first_basis()));
        let mut bad = Vec::new();
        if lhs != root.to_vec() {
            bad.push("root: sum_j w_j^b_j A_j s_b:j + f_b e1 = t".to_string());
        }
        Ok(bad)
    }

    /// The `‖c·s_{b:j}‖∞ ≤ γ` gate over a path, naming each level that fails.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] unless `c` has one multiplier per level.
    pub fn failing_norms(
        &self,
        openings: &[Vec<Elt<R, D>>],
        c: &[Elt<R, D>],
        gamma: u64,
    ) -> Result<Vec<String>, TrapError> {
        if c.len() != self.height() || openings.len() != self.height() {
            return Err(TrapError::WrongShape {
                got: c.len().max(openings.len()),
                expected: self.height(),
            });
        }
        Ok((0..self.height())
            .filter(|j| {
                crate::pcs::trapdoor::vector_infinity_norm(&scale_vec(&c[*j], &openings[*j]))
                    > gamma
            })
            .map(|j| format!("norm(s[{}]) <= {gamma}", j + 1))
            .collect())
    }

    /// Every per-level relation of a whole proof, as the names of the failures:
    /// `t_{b:j} = w^{b_j}·A_j·s_{b:j} + t_{b:j−1}` for both children of every
    /// node, and `t_b = G·t̂_b`.
    ///
    /// A verifier never runs this (Fig. 4's `Open` checks only the telescoped
    /// sum) — it is the prover-side completeness statement, which is what makes
    /// the tree's additive root accumulation checkable at all.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if a node names a level the tree does not have.
    pub fn failing_levels(
        &self,
        proof: &TreeProof<R, D>,
        leaves: &[Elt<R, D>],
    ) -> Result<Vec<String>, TrapError> {
        let h = self.height();
        let n = self.levels[0].pair.n();
        let e1 = self.levels[0].pair.first_basis();
        let mut bad = Vec::new();
        for node in &proof.nodes {
            let level = self
                .levels
                .get(node.level - 1)
                .ok_or(TrapError::WrongShape {
                    got: node.level,
                    expected: h,
                })?;
            if gadget_apply::<R, D, BASE, DIGITS>(&node.t_hat) != node.value {
                bad.push(format!(
                    "level {}: node {}: t != G t-hat",
                    node.level, node.prefix
                ));
            }
            for (bit, s) in [(false, &node.s0), (true, &node.s1)] {
                if s.len() != level.pair.slot_len() {
                    return Err(TrapError::WrongShape {
                        got: s.len(),
                        expected: level.pair.slot_len(),
                    });
                }
                // child value: the leaf f·e₁ at level h, else the child node's
                // own recomposed value
                let child_path = (node.prefix << 1) | usize::from(bit);
                let child_value = if node.level == h {
                    scale_vec(&leaves[child_path], &e1)
                } else {
                    let child = proof
                        .nodes
                        .iter()
                        .find(|p| p.level == node.level + 1 && p.prefix == child_path)
                        .ok_or(TrapError::WrongShape {
                            got: child_path,
                            expected: 1 << node.level,
                        })?;
                    child.value.clone()
                };
                let mut term = level.pair.a.matvec(s).map_err(shape)?;
                if bit {
                    term = level.pair.w_pow[1].matvec(&term).map_err(shape)?;
                }
                if sub_vec(&node.value, &term) != child_value {
                    bad.push(format!(
                        "level {}: node {}: child {} equation",
                        node.level, node.prefix, bit as u8
                    ));
                }
            }
        }
        if proof.root.len() != n {
            return Err(TrapError::WrongShape {
                got: proof.root.len(),
                expected: n,
            });
        }
        Ok(bad)
    }
}

fn shape(e: crate::pcs::key::KeyShapeError) -> TrapError {
    TrapError::WrongShape {
        got: e.got,
        expected: e.expected,
    }
}

/// The PowerBASIS opening relation for an **arbitrary** slot-multiplier list:
/// `A·sᵢ + fᵢ·e₁ = Vᵢ·t` for each slot `i`, where `Vᵢ` is normally `W⁻ⁱ`.
///
/// Free-standing because the folded instances of FMN Fig. 6 keep `A` but swap
/// the multiplier for `W^{k·r}`-powers, so the check cannot be tied to the one
/// `W` the CRS was built from. Returns the names of the slots that fail, never
/// short-circuiting.
///
/// # Errors
/// [`TrapError::WrongShape`] naming the first axis that does not line up.
pub fn failing_basis_relation<R: Ring, const D: usize>(
    a: &RingMatrixKey<R, D>,
    w_inv_pow: &[RingMatrixKey<R, D>],
    t: &[Elt<R, D>],
    f: &[Elt<R, D>],
    s: &[Vec<Elt<R, D>>],
) -> Result<Vec<String>, TrapError> {
    let (n, m) = (a.rows(), a.cols());
    if t.len() != n {
        return Err(TrapError::WrongShape {
            got: t.len(),
            expected: n,
        });
    }
    if f.len() != w_inv_pow.len() || s.len() != w_inv_pow.len() {
        return Err(TrapError::WrongShape {
            got: f.len().max(s.len()),
            expected: w_inv_pow.len(),
        });
    }
    let mut e1 = vec![scalar_elt::<R, D>(R::ZERO); n];
    e1[0] = scalar_elt::<R, D>(R::ONE);
    let mut bad = Vec::new();
    for (i, (si, wi)) in s.iter().zip(w_inv_pow.iter()).enumerate() {
        if si.len() != m {
            return Err(TrapError::WrongShape {
                got: si.len(),
                expected: m,
            });
        }
        if wi.rows() != n || wi.cols() != n {
            return Err(TrapError::WrongShape {
                got: wi.cols(),
                expected: n,
            });
        }
        let lhs = add_vec(&a.matvec(si).map_err(shape)?, &scale_vec(&f[i], &e1));
        if lhs != wi.matvec(t).map_err(shape)? {
            bad.push(format!("eq14[slot {i}]"));
        }
    }
    Ok(bad)
}

/// FMN Fig. 6 step 2(b): the stride-`k` regrouping of a coefficient vector,
/// `f(X) = Σ_{t∈[k]} X^{t−1}·f_t(X^k)` with `f_t[j] = f[t−1+k·j]`.
///
/// # Errors
/// [`TrapError::WrongShape`] unless `coeffs.len()` is a nonzero multiple of `k` —
/// the papers take `d+1 = kʰ`, so a ragged vector is a caller bug.
pub fn split_by_stride<R: Ring, const D: usize>(
    coeffs: &[Elt<R, D>],
    k: usize,
) -> Result<Vec<Vec<Elt<R, D>>>, TrapError> {
    if k == 0 || coeffs.len() % k != 0 || coeffs.is_empty() {
        return Err(TrapError::WrongShape {
            got: coeffs.len(),
            expected: k.max(1),
        });
    }
    Ok((0..k)
        .map(|t| {
            (0..coeffs.len() / k)
                .map(|j| coeffs[t + j * k].clone())
                .collect()
        })
        .collect())
}

/// `Σᵢ cᵢ·X^i` at a ring point, by Horner with ring multiplications.
pub fn poly_eval<R: Ring, const D: usize>(coeffs: &[Elt<R, D>], point: &Elt<R, D>) -> Elt<R, D> {
    let mut acc = scalar_elt::<R, D>(R::ZERO);
    for c in coeffs.iter().rev() {
        acc = acc * point.clone() + c.clone();
    }
    acc
}

/// FMN Fig. 6 step 2(g) / SLAP Fig. 2's `ẑ_{b}`: the strided fold of a vector of
/// slot openings, `s'ᵢ = Σ_{t∈[k]} α_t·s_{k·i+t−1}`.
///
/// # Errors
/// [`TrapError::WrongShape`] unless `alpha` is nonempty, `prev.len()` is a
/// multiple of `k`, and every slot vector has the same length.
pub fn fold_openings<R: Ring, const D: usize>(
    prev: &[Vec<Elt<R, D>>],
    alpha: &[Elt<R, D>],
) -> Result<Vec<Vec<Elt<R, D>>>, TrapError> {
    let k = alpha.len();
    if k == 0 || prev.is_empty() || prev.len() % k != 0 {
        return Err(TrapError::WrongShape {
            got: prev.len(),
            expected: k.max(1),
        });
    }
    let len = prev[0].len();
    if prev.iter().any(|p| p.len() != len) {
        return Err(TrapError::WrongShape {
            got: prev.iter().map(|p| p.len()).max().unwrap_or(0),
            expected: len,
        });
    }
    Ok((0..prev.len() / k)
        .map(|i| {
            let mut acc = vec![scalar_elt::<R, D>(R::ZERO); len];
            for t in 0..k {
                acc = add_vec(&acc, &scale_vec(&alpha[t], &prev[k * i + t]));
            }
            acc
        })
        .collect())
}

/// FMN Fig. 6 step 2(e): `t' := (Σ_{t∈[k]} α_t·W^{−(t−1)})·t`.
///
/// # Errors
/// [`TrapError::WrongShape`] if `alpha` is empty, longer than the available
/// powers, or `t` is not `n` long.
pub fn fold_commitment<R: Ring, const D: usize>(
    w_inv_pow: &[RingMatrixKey<R, D>],
    alpha: &[Elt<R, D>],
    t: &[Elt<R, D>],
) -> Result<Vec<Elt<R, D>>, TrapError> {
    let n = w_inv_pow.first().map_or(0, |w| w.rows());
    if alpha.is_empty() || alpha.len() > w_inv_pow.len() {
        return Err(TrapError::WrongShape {
            got: alpha.len(),
            expected: w_inv_pow.len(),
        });
    }
    if t.len() != n {
        return Err(TrapError::WrongShape {
            got: t.len(),
            expected: n,
        });
    }
    let mut acc = vec![scalar_elt::<R, D>(R::ZERO); n];
    for (i, a) in alpha.iter().enumerate() {
        let term = w_inv_pow[i].matvec(t).map_err(shape)?;
        acc = add_vec(&acc, &scale_vec(a, &term));
    }
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    type Q5 = Zq<4294967197>;
    const BIN: u64 = 2;
    const K32: usize = 32;

    fn td() -> TrapdoorKey<Q5, 4, BIN, K32> {
        TrapdoorKey::generate(b"pair", &[3u8; 32], 1, 2)
    }

    fn unit() -> UnitMatrix<Q5, 4> {
        UnitMatrix::scalar_units(&[Q5::from(1_000_003u64)]).unwrap()
    }

    fn msg(slots: usize, tag: u64) -> Vec<Elt<Q5, 4>> {
        (0..slots)
            .map(|i| scalar_elt::<Q5, 4>(Q5::from(tag * 17 + i as u64 + 5)))
            .collect()
    }

    #[test]
    fn basis_pair_satisfies_the_gadget_relation_at_several_slot_counts() {
        for slots in [1usize, 2, 3, 4] {
            let pair = BasisPair::<Q5, 4, BIN, K32>::new(&td(), &unit(), slots).unwrap();
            assert!(
                trapdoor_relation::<Q5, 4, BIN, K32>(pair.b(), pair.raw_trapdoor()).unwrap(),
                "B.Rt = G_n(d+1) must hold at {slots} slots"
            );
            assert_eq!(pair.b().rows(), slots, "n = 1 here, so B has d+1 rows");
            assert_eq!(
                pair.b().cols(),
                slots * pair.slot_len() + pair.gadget_width(),
                "FMN's m' = m(d+1) + n*delta"
            );
            assert_eq!(
                pair.raw_trapdoor().cols(),
                slots * pair.gadget_width(),
                "n' = n*delta*(d+1)"
            );
        }
    }

    #[test]
    fn basis_pair_specialises_to_the_printed_slap_matrix() {
        // SLAP Fig. 4 prints B = [[A, 0, −G], [0, wA, −G]]. Entry-by-entry.
        let t = td();
        let w = unit();
        let pair = BasisPair::<Q5, 4, BIN, K32>::new(&t, &w, 2).unwrap();
        let (m, tw) = (pair.slot_len(), pair.gadget_width());
        let g = gadget_matrix::<Q5, 4, BIN, K32>(1);
        let zero = scalar_elt::<Q5, 4>(Q5::ZERO);
        let wv = w.value().get(0, 0).cloned().unwrap();
        for c in 0..m {
            let a = t.public().get(0, c).cloned().unwrap();
            assert_eq!(pair.b().get(0, c), Some(&a), "B[0, c] = A[c]");
            assert_eq!(pair.b().get(1, c), Some(&zero), "B[1, c] = 0");
            assert_eq!(
                pair.b().get(1, m + c),
                Some(&(wv.clone() * a)),
                "B[1, m+c] = w*A[c]"
            );
            assert_eq!(pair.b().get(0, m + c), Some(&zero), "B[0, m+c] = 0");
        }
        for c in 0..tw {
            let neg_g = -g.get(0, c).cloned().unwrap();
            assert_eq!(pair.b().get(0, 2 * m + c), Some(&neg_g), "B[0, -G]");
            assert_eq!(pair.b().get(1, 2 * m + c), Some(&neg_g), "B[1, -G]");
        }
    }

    #[test]
    fn commit_then_open_passes_every_equation_and_the_gate() {
        let pair = BasisPair::<Q5, 4, BIN, K32>::new(&td(), &unit(), 2).unwrap();
        let trap = pair.randomise_trapdoor(&[7u8; 32], 2).unwrap();
        let f = msg(2, 4);
        let c = pair.commit(&trap, &f).unwrap();
        assert_eq!(pair.failing(&c, &f).unwrap(), Vec::<String>::new());
        let bound = pair.certified_bound(&trap);
        let one = scalar_elt::<Q5, 4>(Q5::ONE);
        assert!(bound > 0, "the bound is derived from the key");
        assert_eq!(
            pair.failing_norms(&c, &[one.clone(), one], bound).unwrap(),
            Vec::<String>::new(),
            "an honest opening must satisfy the certified bound"
        );
    }

    #[test]
    fn an_unrandomised_crs_trapdoor_would_make_every_commitment_zero() {
        // The reason FMN Fig. 4 item 5 / SLAP item 6 sample T at all.
        let pair = BasisPair::<Q5, 4, BIN, K32>::new(&td(), &unit(), 2).unwrap();
        let rt = pair.raw_trapdoor();
        for i in rt.rows() - pair.gadget_width()..rt.rows() {
            for j in 0..rt.cols() {
                assert_eq!(
                    rt.get(i, j),
                    Some(&scalar_elt::<Q5, 4>(Q5::ZERO)),
                    "Rt's last t rows are the zero block"
                );
            }
        }
        let f = msg(2, 3);
        let via_rt = pair.commit(rt, &f).unwrap();
        assert_eq!(
            via_rt.t,
            vec![scalar_elt::<Q5, 4>(Q5::ZERO); 1],
            "committing through Rt gives t = G*0 = 0"
        );
        let trap = pair.randomise_trapdoor(&[9u8; 32], 2).unwrap();
        assert_ne!(trap, *rt, "the randomised CRS must differ from Rt");
        assert_ne!(
            pair.commit(&trap, &f).unwrap().t,
            vec![scalar_elt::<Q5, 4>(Q5::ZERO); 1],
            "and then t is a real commitment"
        );
    }

    #[test]
    fn every_tamper_trips_exactly_the_equations_it_breaks() {
        let pair = BasisPair::<Q5, 4, BIN, K32>::new(&td(), &unit(), 3).unwrap();
        let trap = pair.randomise_trapdoor(&[1u8; 32], 2).unwrap();
        let f = msg(3, 2);
        let c = pair.commit(&trap, &f).unwrap();
        let one = scalar_elt::<Q5, 4>(Q5::ONE);
        let all = || {
            vec![
                "eq14[slot 0]".to_string(),
                "eq14[slot 1]".to_string(),
                "eq14[slot 2]".to_string(),
                "recompose(t = G t-hat)".to_string(),
            ]
        };
        // wrong message in slot 1 only
        let mut f1 = f.clone();
        f1[1] = f1[1].clone() + one.clone();
        assert_eq!(
            pair.failing(&c, &f1).unwrap(),
            vec!["eq14[slot 1]".to_string()]
        );
        // wrong opening in slot 0 only
        let mut c2 = c.clone();
        c2.opening.s[0][0] = c2.opening.s[0][0].clone() + one.clone();
        assert_eq!(
            pair.failing(&c2, &f).unwrap(),
            vec!["eq14[slot 0]".to_string()]
        );
        // wrong commitment: all three slots and the recomposition
        let mut c3 = c.clone();
        c3.t[0] = c3.t[0].clone() + one.clone();
        assert_eq!(pair.failing(&c3, &f).unwrap(), all());
        // wrong t̂ alone: *only* the recomposition breaks. eq14 reads the
        // transmitted `t`, which is still honest here, so this case is what
        // proves `t = G·t̂` is not a redundant check — without it a prover
        // could hand over a `t` no gadget image explains.
        let mut c4 = c.clone();
        c4.opening.t_hat[0] = c4.opening.t_hat[0].clone() + one.clone();
        assert_eq!(
            pair.failing(&c4, &f).unwrap(),
            vec!["recompose(t = G t-hat)".to_string()]
        );
    }

    #[test]
    fn norm_gate_fires_only_on_the_slot_it_is_shown() {
        let pair = BasisPair::<Q5, 4, BIN, K32>::new(&td(), &unit(), 2).unwrap();
        let trap = pair.randomise_trapdoor(&[4u8; 32], 1).unwrap();
        let f = msg(2, 1);
        let mut c = pair.commit(&trap, &f).unwrap();
        let one = scalar_elt::<Q5, 4>(Q5::ONE);
        // The gate has to be read against the bound the trapdoor actually
        // certifies: a small magic number like 3 rejects *both* honest slots,
        // which would make "only the inflated slot is reported" unfalsifiable.
        let gamma = pair.certified_bound(&trap);
        assert!(pair
            .failing_norms(&c, &[one.clone(), one.clone()], gamma)
            .unwrap()
            .is_empty());
        // Past half the modulus the centered representative is the largest
        // magnitude the ring has, so no certified bound can absorb it.
        let big = scalar_elt::<Q5, 4>(Q5::from(Q5::MODULUS / 2));
        c.opening.s[1][0] = c.opening.s[1][0].clone() + big;
        assert_eq!(
            pair.failing_norms(&c, &[one.clone(), one], gamma).unwrap(),
            vec![format!("norm(s[1]) <= {gamma}")],
            "only the inflated slot may be reported"
        );
    }

    #[test]
    fn the_certified_bound_counts_the_ring_degree_once_not_twice() {
        // FMN/SLAP Lem. 4.1's endpoint is `‖sᵢ‖ ≤ γ`; the crate's Gaussian-free
        // sampler reaches it as `γ = dz · max_i Σ_j ‖M_ij‖₁`. The row sum already
        // runs over the `D` coefficients of every entry, so scaling by `D` again
        // — as `trapdoor::bound_of_matrix` does — is a factor-`D` looseness, and
        // on a `(d+1)`-slot basis that is what pushed the gate past `(q−1)/2`.
        const DD: usize = 4;
        let pair = BasisPair::<Q5, DD, BIN, K32>::new(&td(), &unit(), 3).unwrap();
        let trap = pair.randomise_trapdoor(&[11u8; 32], 2).unwrap();
        // the row sum, recomputed here without either function's help
        let worst = (0..trap.rows())
            .map(|i| {
                trap.row(i)
                    .iter()
                    .map(|e| {
                        crate::foundation::encoding::ring_to_u32::<Q5, DD>(e)
                            .iter()
                            .map(|&c| {
                                let x = u64::from(c);
                                x.min(Q5::MODULUS - x)
                            })
                            .sum::<u64>()
                    })
                    .sum::<u64>()
            })
            .max()
            .unwrap_or(0);
        assert_eq!(worst_row_l1::<Q5, DD>(&trap, 0), {
            (0..trap.cols())
                .map(|j| {
                    crate::foundation::encoding::ring_to_u32::<Q5, DD>(trap.get(0, j).unwrap())
                        .iter()
                        .map(|&c| {
                            let x = u64::from(c);
                            x.min(Q5::MODULUS - x)
                        })
                        .sum::<u64>()
                })
                .sum::<u64>()
        });
        let gamma = pair.certified_bound(&trap);
        assert_eq!(
            gamma, worst,
            "base 2 has dz = 1, so γ is exactly the worst row sum"
        );
        assert_eq!(
            crate::pcs::trapdoor::bound_of_matrix::<Q5, DD, BIN, K32>(&trap, 0),
            (DD as u64 * worst + 1),
            "the trapdoor form is the same row sum times D"
        );
        // γ must actually bound what the scheme hands out: every honest slot,
        // and the CRS preimage's own coordinates.
        let f = msg(3, 7);
        let c = pair.commit(&trap, &f).unwrap();
        for (i, s) in c.opening.s.iter().enumerate() {
            let n = crate::pcs::trapdoor::vector_infinity_norm(s);
            assert!(n <= gamma, "slot {i} has ‖s‖∞ = {n} > γ = {gamma}");
        }
        assert!(
            crate::pcs::trapdoor::vector_infinity_norm(&c.opening.t_hat) <= gamma,
            "t̂ is a preimage row too"
        );
        // and it must be *tight enough to be a gate*: the loose form would let a
        // slot grow D times past γ and still "verify".
        assert!(gamma < (Q5::MODULUS - 1) / 2, "γ must sit in the centered range");
    }

    #[test]
    fn shapes_are_refused_with_the_real_numbers() {
        let pair = BasisPair::<Q5, 4, BIN, K32>::new(&td(), &unit(), 2).unwrap();
        let wide = UnitMatrix::scalar_units(&[Q5::from(5u64), Q5::from(7u64)]).unwrap();
        // `BasisPair` is not `PartialEq`, so compare the refusals only
        assert_eq!(
            BasisPair::<Q5, 4, BIN, K32>::new(&td(), &wide, 2).map(|_| ()),
            Err(TrapError::WrongShape {
                got: 2,
                expected: 1
            }),
            "W must be n x n for the key's n"
        );
        assert_eq!(
            BasisPair::<Q5, 4, BIN, K32>::new(&td(), &unit(), 0).map(|_| ()),
            Err(TrapError::WrongShape {
                got: 0,
                expected: 1
            })
        );
        assert_eq!(
            pair.commit_target(&msg(3, 0)),
            Err(TrapError::WrongShape {
                got: 3,
                expected: 2
            })
        );
    }

    #[test]
    fn tree_commitments_open_at_every_leaf_and_levels_hold() {
        let tree = PrisisTree::<Q5, 4, BIN, K32>::setup(&[5u8; 32], 1, 2, 2, 2);
        let leaves = msg(4, 8);
        let proof = tree.commit(&leaves);
        assert_eq!(proof.nodes.len(), 3, "one internal node per prefix");
        assert_eq!(
            tree.failing_levels(&proof, &leaves).unwrap(),
            Vec::<String>::new(),
            "every per-level relation must hold"
        );
        assert!(tree.certified_bound() > 0, "the bound comes from the keys");
        for b in 0..4usize {
            let path = vec![b >> 1 & 1 == 1, b & 1 == 1];
            let openings = tree.path_openings(&proof, &path);
            assert_eq!(openings.len(), 2);
            assert_eq!(
                tree.failing(&proof.root, &path, &leaves[b], &openings)
                    .unwrap(),
                Vec::<String>::new(),
                "leaf {b} must open against the root"
            );
            let one = scalar_elt::<Q5, 4>(Q5::ONE);
            assert_eq!(
                tree.failing_norms(&openings, &[one.clone(), one], tree.certified_bound())
                    .unwrap(),
                Vec::<String>::new()
            );
            // flipping the last path bit points at a different leaf's f_b
            let mut wrong = path.clone();
            wrong[1] = !wrong[1];
            assert_eq!(
                tree.failing(&proof.root, &wrong, &leaves[b], &openings)
                    .unwrap(),
                vec!["root: sum_j w_j^b_j A_j s_b:j + f_b e1 = t".to_string()],
                "a mismatched path must be refused"
            );
        }
    }

    #[test]
    fn a_tampered_node_breaks_exactly_its_own_level_relations() {
        let tree = PrisisTree::<Q5, 4, BIN, K32>::setup(&[6u8; 32], 1, 2, 2, 1);
        let leaves = msg(4, 2);
        let mut proof = tree.commit(&leaves);
        assert!(tree.failing_levels(&proof, &leaves).unwrap().is_empty());
        let one = scalar_elt::<Q5, 4>(Q5::ONE);
        proof.nodes[0].s1[0] = proof.nodes[0].s1[0].clone() + one.clone();
        let bad = tree.failing_levels(&proof, &leaves).unwrap();
        assert_eq!(bad.len(), 1, "one equation, the tampered node's child");
        assert_eq!(bad[0], "level 2: node 0: child 1 equation");
        // and the root equation no longer holds for either leaf of that node
        let openings = tree.path_openings(&proof, &[false, true]);
        assert_eq!(
            tree.failing(&proof.root, &[false, true], &leaves[1], &openings)
                .unwrap(),
            vec!["root: sum_j w_j^b_j A_j s_b:j + f_b e1 = t".to_string()]
        );
    }

    #[test]
    fn a_single_level_tree_is_the_two_slot_pair() {
        // h = 1: Fig. 4's tree collapses to one Commit step, so the root must
        // equal the BasisPair commitment of the same leaves through the same T.
        let tree = PrisisTree::<Q5, 4, BIN, K32>::setup(&[7u8; 32], 1, 2, 1, 2);
        let leaves = msg(2, 1);
        let proof = tree.commit(&leaves);
        let level = tree.level(1).unwrap();
        let pair = &level.pair;
        let mut target = Vec::new();
        for f in &leaves {
            target.extend(neg_vec(&scale_vec(f, &pair.first_basis())));
        }
        let x = preimage_with_trapdoor::<Q5, 4, BIN, K32>(pair.b(), &level.trap, &target).unwrap();
        let m = pair.slot_len();
        assert_eq!(
            gadget_apply::<Q5, 4, BIN, K32>(&x[2 * m..]),
            proof.root,
            "the tree root is the pair's t = G t-hat"
        );
        assert_eq!(&x[..m], proof.nodes[0].s0.as_slice());
        assert_eq!(&x[m..2 * m], proof.nodes[0].s1.as_slice());
    }
}
