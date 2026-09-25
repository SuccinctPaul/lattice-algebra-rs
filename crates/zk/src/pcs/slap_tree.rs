//! SLAP's split-and-fold tree machinery — the *protocol* half of
//! Albrecht–Fenzi–Lapiha–Nguyen, eprint 2023/1469, Fig. 4 + Fig. 5.
//!
//! [`crate::pcs::trapdoor`] supplies `TrapGen`/`SamplePre` and
//! [`crate::pcs::prisis`] supplies the per-level basis
//! `B_j = [[A_j, 0, −G], [0, w_j A_j, −G]]`, the tree commitment and Fig. 4's
//! single-path `Open`. What neither supplies is the object the *evaluation*
//! protocol lives on: SLAP does not open one path, it opens **all `2^j` blocks
//! of a level at once**, folds those blocks across rounds with the challenge
//! monomials, and ends by checking the telescoped root equation against the
//! **folded** blocks. That index algebra — which bit of a coefficient index
//! selects which level's node — is this module. The fold primitives it exposes
//! ([`fold_coeffs`], [`partial_evaluations`], [`TreeOpenings::fold`]) are the
//! same linear maps Fenzi–Moghaddas–Nguyen (eprint 2023/846) Fig. 6 applies to
//! a *flat* PowerBASIS instance, so `examples/fmn.rs` reads them too.
//!
//! # The indexing fact everything rests on
//!
//! SLAP §5 (p. 32) writes the polynomial as `f(X) = Σ_{b ∈ Z₂^h} f_b · X^int(b)`
//! and fixes the convention with `int((i, j)) = int(i) + 2^k · int(j)` (§5.1,
//! p. 32). That identity holds only if the *first* bit `b₁` is the **least
//! significant** bit of `int(b)` — so level `j`'s branch bit is bit `j − 1` of
//! the coefficient index, and the parity split `f = f₀(X²) + X f₁(X²)` of
//! Fig. 2 (p. 10) is exactly level 1, whose matrix is `A₁` — the root merge:
//!
//! ```text
//! node at level j  =  low (j−1) bits of the coefficient index   (2^(j−1) nodes)
//! branch at level j=  bit (j−1)                                 (2^j openings)
//! openings of level j are indexed by  int(b₁ … b_j) = index mod 2^j
//! ```
//!
//! [`PrisisTree`](crate::pcs::prisis::PrisisTree) indexes its leaves the other
//! way round (`path_openings` takes the bits root-first, so its leaf index is
//! `bitrev(h, int(b))`). [`TreeOpenings::from_proof`] is the one place that
//! reversal happens, and its test checks it against
//! [`PrisisTree::path_openings`](crate::pcs::prisis::PrisisTree::path_openings)
//! for *every* leaf instead of trusting the arithmetic.
//!
//! # The round, verbatim from Fig. 5 (p. 35)
//!
//! With `l_τ = l_{τ−1} − k`, `u_τ = u_{τ−1}^{2^k}` and `kk = 2^k`:
//!
//! ```text
//! (c)  f̄_ι(X, i) = Σ_j f_{ι,(i,j)} X^int(j)         z_{ι,i} = f̄_ι(u_τ, i)
//! (d)  send (z_{ι,i})_i  and  (s_{ι,i:t})_{i ∈ Z₂^≤k}
//! (e)  α_{ι,i,κ} ← (X^r)^{r·2^k}
//! (f)  f_{τ,κ}[j] = Σ_ι Σ_i α_{ι,i,κ} f_ι[int(i) + kk·int(j)]
//!      s_{τ,κ,t}[x] = Σ_ι Σ_i α_{ι,i,κ} s_{ι,t+k}[int(i) + kk·int(x)]
//!      t_{τ,κ} = Σ_ι Σ_i α_{ι,i,κ}(t_ι − Σ_{t=1}^{k} w^{i_t}_{(τ−1)k+t} A_{(τ−1)k+t} s_{ι,i:t})
//!      z_{τ,κ} = Σ_ι Σ_i α_{ι,i,κ} z_{ι,i}                β_τ = (r·2^k) β_{τ−1}
//! checks:  z_ι == Σ_i z_{ι,i} u^int(i)   and   ‖s_{ι,i:t}‖ ≤ (r 2^k)^{τ−1} β
//! ```
//!
//! `s_{ι,i:t}` is the block of the *length-`t` prefix* of `i`, which is why one
//! round carries `Σ_{t=1}^{k} 2^t = 2^{k+1} − 2` blocks per claim — matching
//! Lemma 5.9's per-message bound `2^k N⌈log q⌉ + 2^{k+1} m N⌈log 2(r2^k)^i β⌉`
//! (p. 42). The final check is relation (6)'s `R^{(r)}_{h−kℓ, β_ℓ}` evaluated on
//! the folded blocks ([`FoldInstance::verify_final`]).
//!
//! # Why the fold needs no new preimage sampling
//!
//! §5.1 (p. 33–34) expands `g_{κ,j}·e₁` and gets Eq. (7), whose content is that
//! `Σ_ι Σ_i α_{ι,i,κ}(t_ι − Σ_t w^{i_t} A_t s_{ι,i:t})` *is* the value the
//! remaining levels telescope to. [`FoldInstance::fold_round`] computes exactly
//! that quantity and the base case checks it, so no `SamplePre` runs during
//! evaluation — which is what keeps the prover at Lemma 5.9's `O(r²md)` rather
//! than re-running Fig. 4 each round.
//!
//! # The challenge space: the paper's gloss vs its own definition
//!
//! Fig. 5 draws `α` from `(X^r)^{r2^k}`. Table 2 (p. 36) glosses `X` as "the set
//! of **signed** monomials ±Xⁱ", whereas §2 (p. 12) defines
//! `X := {1, X, …, X^{2N−1}}`. The two name the same `2N` elements — `X^N = −1`
//! gives `X^{i+N} = −X^i` — so the signed reading is a consequence, not an
//! extension. [`Alpha::sample`] therefore draws exponents that are multiples of
//! `r` inside `[0, 2D)`, which is what makes `‖α‖₁ = 1` and `α` a unit — the
//! property Fig. 2's last paragraph (p. 10) needs for "the updated openings are
//! scaled by monomials, and thus remain short".
//!
//! # What is deliberately not here
//!
//! * **The trapdoors.** `T_j` is the `SamplePre` trapdoor for `B_j`
//!   (`B_j·T_j = G_{2n}`, Fig. 4 item 6) and [`crate::pcs::prisis`] owns it.
//!   Figs. 4 and 5 print `crs := (A_j, w_j, T_j)` and carry `T` into the
//!   relation's first component too, but no `Open` or `Verify` step *reads* it:
//!   only `Commit` (item 4) and `Eval` do. This module's verifier-side code
//!   therefore takes `A`/`w` alone and the assemblies keep `T` on the prover
//!   side. That is a reading of the printed text, and it is consistent with the
//!   survey's §1 row "**trusted setup** (trapdoors)".
//! * **Re-randomisation.** §3 (h-PRISIS → Module-SIS) re-samples the CRS blocks;
//!   that is a reduction technique and changes no equation checked here.
//! * **Gaussians and zero knowledge.** See [`crate::pcs::trapdoor`]'s "What is
//!   not claimed" — SLAP §5.4's simulator needs MP12's `SampleD`, which this
//!   crate does not have.
//! * **The `a^⊤` row of `PRISIS.Sample`** (Fig. 1, p. 9) is already inside
//!   `TrapdoorKey`'s published `A = [Ā | G − ĀR]`; nothing here re-adds it.

use crate::pcs::key::{KeyShapeError, RingMatrixKey};
use crate::pcs::prisis::{fold_openings, poly_eval, PrisisTree, TreeProof};
use crate::pcs::trapdoor::{
    add_vec, scale_vec, scalar_elt, sub_vec, vector_infinity_norm, Elt, TrapError,
};
use algebra::crypto::xof::Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::format;
use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Turns a key-shape refusal into the module's own.
fn shape(e: KeyShapeError) -> TrapError {
    TrapError::WrongShape {
        got: e.got,
        expected: e.expected,
    }
}

/// `log2(kk)` when `kk` is a power of two, `None` otherwise.
const fn log2_exact(kk: usize) -> Option<usize> {
    if kk == 0 || kk & (kk - 1) != 0 {
        return None;
    }
    let mut k = 0;
    let mut v = kk;
    while v > 1 {
        v >>= 1;
        k += 1;
    }
    Some(k)
}

/// Reverses the low `len` bits of `v`.
#[must_use]
pub const fn bitrev(len: usize, v: usize) -> usize {
    let mut out = 0usize;
    let mut i = 0;
    while i < len {
        if (v >> i) & 1 == 1 {
            out |= 1 << (len - 1 - i);
        }
        i += 1;
    }
    out
}

/// The bits `b₁ … b_h` of a coefficient index with `b₁` the **least**
/// significant (SLAP §5's `int((i, j)) = int(i) + 2^k int(j)`), returned in the
/// root-first order
/// [`PrisisTree::path_openings`](crate::pcs::prisis::PrisisTree::path_openings)
/// expects.
#[must_use]
pub fn path_bits(index: usize, h: usize) -> Vec<bool> {
    (0..h).map(|j| (index >> j) & 1 == 1).collect()
}

/// Reorders a coefficient vector from SLAP's index convention (`b₁` = LSB, so
/// the parity split is the first level) into the leaf order
/// [`PrisisTree::commit`](crate::pcs::prisis::PrisisTree::commit) reads (path
/// bits root-first).
///
/// # Panics
/// If `coeffs.len()` is not a power of two.
#[must_use]
pub fn leaves_in_tree_order<R: Ring, const D: usize>(coeffs: &[Elt<R, D>]) -> Vec<Elt<R, D>> {
    let h = coeffs.len().trailing_zeros() as usize;
    assert_eq!(
        1usize << h,
        coeffs.len(),
        "a Merkle-PRISIS tree commits to 2^h leaves"
    );
    (0..coeffs.len())
        .map(|tree_index| coeffs[bitrev(h, tree_index)].clone())
        .collect()
}

/// `x^e` by repeated ring multiplication; `e` is a small *index*, never a
/// scalar of the ring.
#[must_use]
pub fn pow_elt<R: Ring, const D: usize>(x: &Elt<R, D>, e: usize) -> Elt<R, D> {
    let mut acc = scalar_elt::<R, D>(R::ONE);
    for _ in 0..e {
        acc = acc * x.clone();
    }
    acc
}

/// The `A_j` and the power-`1` matrix `W_j = w_j·Iₙ` of every level of a
/// committed tree, in the order `j = 1 … h` that Fig. 4's `Σ_{j=1}^{h}` uses.
///
/// # Panics
/// If the tree has no level (only reachable from a zero-height tree).
#[must_use]
pub fn tree_keys<R: Ring, const D: usize, const BASE: u64, const DIGITS: usize>(
    tree: &PrisisTree<R, D, BASE, DIGITS>,
) -> (Vec<RingMatrixKey<R, D>>, Vec<RingMatrixKey<R, D>>) {
    let mut a = Vec::with_capacity(tree.height());
    let mut w = Vec::with_capacity(tree.height());
    for j in 1..=tree.height() {
        let level = tree.level(j).expect("levels are 1-based and present");
        a.push(level.pair().a().clone());
        w.push(level.pair().w_pow()[1].clone());
    }
    (a, w)
}

/// Fig. 4's decommitment state `st = (s_b)_{b ∈ Z₂^{≤h}}` laid out per level in
/// the fold's indexing: `level(t)[x]` is the opening of the level-`t+1` node
/// whose path int (LSB-first) is `x`, for `x < 2^{t+1}`.
#[derive(Clone, Debug)]
pub struct TreeOpenings<R: Ring, const D: usize> {
    levels: Vec<Vec<Vec<Elt<R, D>>>>,
}

impl<R: Ring, const D: usize> TreeOpenings<R, D> {
    /// Level arrays that are already in the fold's layout.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if a level does not hold `2^(t+1)` entries, or
    /// the entries of one level differ in length.
    pub fn from_levels(levels: Vec<Vec<Vec<Elt<R, D>>>>) -> Result<Self, TrapError> {
        for (t, array) in levels.iter().enumerate() {
            if array.len() != 1usize << (t + 1) {
                return Err(TrapError::WrongShape {
                    got: array.len(),
                    expected: 1usize << (t + 1),
                });
            }
            if let Some(first) = array.first() {
                let len = first.len();
                if array.iter().any(|v| v.len() != len) {
                    return Err(TrapError::WrongShape {
                        got: array.iter().map(|v| v.len()).max().unwrap_or(0),
                        expected: len,
                    });
                }
            }
        }
        Ok(Self { levels })
    }

    /// Reads a committed tree's [`TreeProof`] into the fold's layout.
    ///
    /// `proof` keys a node by `(level j, prefix)` with `prefix` read root-first;
    /// the same node is keyed here by `int(b₁ … b_j) = bitrev(j−1, prefix) +
    /// b_j·2^{j−1}`, since the branch bit `b_j` is the most significant bit of
    /// the LSB-first path int.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if a level's nodes are missing or a node's
    /// opening is not `m` long.
    pub fn from_proof<const BASE: u64, const DIGITS: usize>(
        tree: &PrisisTree<R, D, BASE, DIGITS>,
        proof: &TreeProof<R, D>,
    ) -> Result<Self, TrapError> {
        let h = tree.height();
        let m = tree
            .level(1)
            .ok_or(TrapError::WrongShape {
                got: 0,
                expected: 1,
            })?
            .pair()
            .slot_len();
        let zero = scalar_elt::<R, D>(R::ZERO);
        let mut levels = Vec::with_capacity(h);
        for j in 1..=h {
            let mut array = vec![vec![zero.clone(); m]; 1usize << j];
            for prefix in 0..(1usize << (j - 1)) {
                let node = proof
                    .nodes
                    .iter()
                    .find(|p| p.level == j && p.prefix == prefix)
                    .ok_or(TrapError::WrongShape {
                        got: prefix,
                        expected: 1usize << (j - 1),
                    })?;
                if node.s0.len() != m || node.s1.len() != m {
                    return Err(TrapError::WrongShape {
                        got: node.s0.len().max(node.s1.len()),
                        expected: m,
                    });
                }
                let low = bitrev(j - 1, prefix);
                array[low] = node.s0.clone();
                array[low | (1 << (j - 1))] = node.s1.clone();
            }
            levels.push(array);
        }
        Ok(Self { levels })
    }

    /// Levels remaining (`h` at the start, `l_τ` after `τ` rounds).
    #[must_use]
    pub fn height(&self) -> usize {
        self.levels.len()
    }

    /// Level `t` (0-based): `2^{t+1}` openings of `m` ring elements each.
    #[must_use]
    pub fn level(&self, t: usize) -> &[Vec<Elt<R, D>>] {
        &self.levels[t]
    }

    /// The blocks a round of factor `kk` sends: levels `0 … log2(kk) − 1`.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if `kk` is not a power of two or exceeds the
    /// remaining height.
    pub fn sent_blocks(&self, kk: usize) -> Result<Vec<Vec<Vec<Elt<R, D>>>>, TrapError> {
        let k = log2_exact(kk).ok_or(TrapError::WrongShape {
            got: kk,
            expected: 2,
        })?;
        if k > self.height() {
            return Err(TrapError::WrongShape {
                got: self.height(),
                expected: k,
            });
        }
        Ok((0..k).map(|t| self.levels[t].clone()).collect())
    }

    /// Fig. 5 item 2(f)ii on one level:
    /// `s'_t[x] = Σ_i α_i · s_{t+k}[int(i) + kk·int(x)]`.
    ///
    /// The re-indexing into
    /// [`crate::pcs::prisis::fold_openings`]'s contiguous stride layout happens
    /// here so the two conventions cannot drift: the swap is exactly
    /// `int(i) + kk·int(x) ↔ kk·int(x) + i`.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if `kk` is not a power of two, `target` is out
    /// of range, or level `target + log2(kk)` is missing.
    fn fold_level(&self, target: usize, alpha: &[Elt<R, D>]) -> Result<Vec<Vec<Elt<R, D>>>, TrapError> {
        let kk = alpha.len();
        let k = log2_exact(kk).ok_or(TrapError::WrongShape {
            got: kk,
            expected: 2,
        })?;
        let src = self.levels.get(target + k).ok_or(TrapError::WrongShape {
            got: self.height(),
            expected: target + k + 1,
        })?;
        let want = 1usize << (target + 1);
        if src.len() != want * kk {
            return Err(TrapError::WrongShape {
                got: src.len(),
                expected: want * kk,
            });
        }
        let mut permuted = Vec::with_capacity(src.len());
        for x in 0..want {
            for i in 0..kk {
                permuted.push(src[i + kk * x].clone());
            }
        }
        fold_openings(&permuted, alpha)
    }

    /// All surviving levels after one round of factor `kk = 2^k` for a **single**
    /// claim's α vector: `height(self) − log2(kk)` levels.
    ///
    /// # Errors
    /// As [`TreeOpenings::fold_level`].
    pub fn fold(&self, alpha: &[Elt<R, D>]) -> Result<Self, TrapError> {
        let k = log2_exact(alpha.len()).ok_or(TrapError::WrongShape {
            got: alpha.len(),
            expected: 2,
        })?;
        Self::fold_multi(core::slice::from_ref(self), &[alpha.to_vec()], k)
    }

    /// The same fold across `r` claims — Fig. 5 item 2(f)ii's
    /// `s_{τ,κ,t}[x] = Σ_ι Σ_i α_{ι,i,κ} s_{ι,t+k}[int(i) + kk·int(x)]`,
    /// evaluated for one output claim `κ`.
    ///
    /// `alphas[ι]` is the column `(α_{ι,0,κ}, …, α_{ι,kk−1,κ})`.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] if `alphas` does not pair one-to-one with
    /// `openings`, if the openings have different heights, or if a fold level is
    /// missing.
    pub fn fold_multi(
        openings: &[TreeOpenings<R, D>],
        alphas: &[Vec<Elt<R, D>>],
        k: usize,
    ) -> Result<Self, TrapError> {
        if openings.is_empty() || openings.len() != alphas.len() {
            return Err(TrapError::WrongShape {
                got: openings.len().max(alphas.len()),
                expected: openings.len().min(alphas.len()),
            });
        }
        let kk = alphas[0].len();
        if log2_exact(kk) != Some(k) {
            return Err(TrapError::WrongShape {
                got: kk,
                expected: 1usize << k,
            });
        }
        let height = openings[0].height();
        if height < k {
            return Err(TrapError::WrongShape {
                got: height,
                expected: k,
            });
        }
        let mut levels = Vec::with_capacity(height - k);
        for t in 0..(height - k) {
            let mut acc: Option<Vec<Vec<Elt<R, D>>>> = None;
            for (ι, op) in openings.iter().enumerate() {
                if op.height() != height {
                    return Err(TrapError::WrongShape {
                        got: op.height(),
                        expected: height,
                    });
                }
                if op.levels[t].is_empty() || op.levels[t][0].len() != openings[0].levels[t][0].len() {
                    return Err(TrapError::WrongShape {
                        got: op.levels[t].first().map_or(0, Vec::len),
                        expected: openings[0].levels[t][0].len(),
                    });
                }
                let part = op.fold_level(t, &alphas[ι])?;
                acc = Some(match acc {
                    None => part,
                    Some(prev) => prev
                        .into_iter()
                        .zip(part)
                        .map(|(a, b)| add_vec(&a, &b))
                        .collect(),
                });
            }
            levels.push(acc.unwrap_or_default());
        }
        Self::from_levels(levels)
    }
}

/// `Σ_{i < kk} α_i · coeffs[kk·j + i]` — Fig. 5 item 2(f)i on one claim, and
/// FMN Fig. 6 item 2(f) with `kk = k`.
///
/// # Errors
/// [`TrapError::WrongShape`] if `alpha` is empty or `coeffs.len()` is not a
/// nonzero multiple of `alpha.len()`.
pub fn fold_coeffs<R: Ring, const D: usize>(
    coeffs: &[Elt<R, D>],
    alpha: &[Elt<R, D>],
) -> Result<Vec<Elt<R, D>>, TrapError> {
    let kk = alpha.len();
    if kk == 0 || coeffs.is_empty() || coeffs.len() % kk != 0 {
        return Err(TrapError::WrongShape {
            got: coeffs.len(),
            expected: kk.max(1),
        });
    }
    Ok((0..coeffs.len() / kk)
        .map(|j| {
            let mut acc = scalar_elt::<R, D>(R::ZERO);
            for (i, a) in alpha.iter().enumerate() {
                acc = acc + scale_vec(a, &[coeffs[kk * j + i].clone()])[0].clone();
            }
            acc
        })
        .collect())
}

/// `z_i = f̄_i(u_next)` for the stride-`kk` slices of `coeffs` — Fig. 5 items
/// 2(c)i/ii, FMN Eq. (17), where `f̄_i` collects the coefficients whose index is
/// `≡ i (mod kk)`.
///
/// # Errors
/// [`TrapError::WrongShape`] if `kk` is `0` or `coeffs.len()` is not a nonzero
/// multiple of `kk`.
pub fn partial_evaluations<R: Ring, const D: usize>(
    coeffs: &[Elt<R, D>],
    u_next: &Elt<R, D>,
    kk: usize,
) -> Result<Vec<Elt<R, D>>, TrapError> {
    if kk == 0 || coeffs.is_empty() || coeffs.len() % kk != 0 {
        return Err(TrapError::WrongShape {
            got: coeffs.len(),
            expected: kk.max(1),
        });
    }
    Ok((0..kk)
        .map(|i| {
            let slice: Vec<Elt<R, D>> = (0..coeffs.len() / kk)
                .map(|j| coeffs[i + kk * j].clone())
                .collect();
            poly_eval(&slice, u_next)
        })
        .collect())
}

/// The α tensor of Fig. 5 item 2(e): `values[ι][i]` is the `r`-tuple
/// `(α_{ι,i,1}, …, α_{ι,i,r}) ∈ (X^r)^r`.
#[derive(Clone, Debug)]
pub struct Alpha<R: Ring, const D: usize> {
    /// `values[ι][i][κ]`.
    pub values: Vec<Vec<Vec<Elt<R, D>>>>,
}

impl<R: Ring, const D: usize> Alpha<R, D> {
    /// `r · kk` tuples of `r` elements of `X^power`, drawn from `xof`.
    ///
    /// `power` is the amortisation parameter `r` of `(X^r)`: the exponent is
    /// drawn as `power · j` for `j < 2D/power`, which stays inside the
    /// `2D`-element monomial group of `R_q = Z_q[X]/(X^D + 1)`.
    ///
    /// # Panics
    /// If `claims` or `kk` is zero, or `power` exceeds `2D`.
    pub fn sample<X: Xof>(claims: usize, kk: usize, power: usize, xof: &mut X) -> Self {
        assert!(claims >= 1 && kk >= 1, "the fold needs at least one α");
        assert!(power >= 1 && power <= 2 * D, "X^r needs r ≤ 2N");
        let span = (2 * D) / power;
        let draw = |xof: &mut X| {
            let mut buf = [0u8; 8];
            xof.squeeze(&mut buf);
            let e = ((u64::from_le_bytes(buf) as usize) % span) * power;
            let mut coeffs = vec![R::ZERO; D];
            // X^e reduced mod 2D: X^D = −1, so exponents ≥ D flip the sign.
            coeffs[e % D] = if (e / D) % 2 == 1 { -R::ONE } else { R::ONE };
            PolyRing::<R, D>::from_coefficients(coeffs)
        };
        Self {
            values: (0..claims)
                .map(|_| {
                    (0..kk)
                        .map(|_| (0..claims).map(|_| draw(xof)).collect())
                        .collect()
                })
                .collect(),
        }
    }

    /// The `r × kk` α table for one output claim `κ`.
    #[must_use]
    pub fn for_claim(&self, κ: usize) -> Vec<Vec<Elt<R, D>>> {
        (0..self.values.len())
            .map(|ι| {
                (0..self.values[ι].len())
                    .map(|i| self.values[ι][i][κ].clone())
                    .collect()
            })
            .collect()
    }

    /// Claim count `r`.
    #[must_use]
    pub fn claims(&self) -> usize {
        self.values.len()
    }

    /// Fold factor `kk`.
    #[must_use]
    pub fn kk(&self) -> usize {
        self.values.first().map_or(0, |v| v.len())
    }
}

/// One round's prover message (Fig. 5 item 2(d)).
#[derive(Clone, Debug)]
pub struct RoundMessage<R: Ring, const D: usize> {
    /// `z[ι][i]` — the `kk` partial evaluations per claim.
    pub z: Vec<Vec<Elt<R, D>>>,
    /// `blocks[ι][t][x]` — level `t+1`'s `2^{t+1}` openings, per claim.
    pub blocks: Vec<Vec<Vec<Vec<Elt<R, D>>>>>,
}

/// The final prover message (Fig. 5 item 3).
#[derive(Clone, Debug)]
pub struct FinalMessage<R: Ring, const D: usize> {
    /// `coeffs[κ]` — the `2^{h−kℓ}` coefficients of each folded polynomial.
    pub coeffs: Vec<Vec<Elt<R, D>>>,
    /// `openings[κ]` — every surviving level's blocks.
    pub openings: Vec<TreeOpenings<R, D>>,
}

/// Why a fold step refused.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FoldError {
    /// A vector or matrix axis had the wrong length.
    Shape(TrapError),
    /// The instance is the verifier's view: it holds neither the openings nor
    /// the coefficients, so it cannot build a prover message.
    NoWitness,
    /// The instance is the verifier's view: it holds no openings.
    NoTrapdoor,
}

impl fmt::Display for FoldError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FoldError::Shape(e) => write!(f, "fold shape: {e}"),
            FoldError::NoWitness => write!(
                f,
                "this instance is the verifier's view: it holds no witness to open"
            ),
            FoldError::NoTrapdoor => {
                write!(f, "this instance is the verifier's view and holds no openings")
            }
        }
    }
}

impl From<TrapError> for FoldError {
    fn from(e: TrapError) -> Self {
        FoldError::Shape(e)
    }
}

/// The outcome of one round: the next instance (same prover/verifier view as
/// the input) and **every** check of this round that did not hold.
#[must_use]
pub struct RoundOutcome<R: Ring, const D: usize> {
    /// Round `τ`'s successor.
    pub next: FoldInstance<R, D>,
    /// Names of the failing checks, never short-circuited.
    pub failing: Vec<String>,
}

/// The state Fig. 5 carries between rounds: `((A_j, w_j)_{remaining}, (t_κ),
/// u_τ, (z_κ), β_τ)` plus, on the prover side only, the surviving level arrays.
///
/// One type serves both roles, and that is the point: [`FoldInstance::fold_round`]
/// is a single code path, so "the verifier's `t_τ`" and "the prover's `t_τ`"
/// cannot silently disagree.
#[derive(Clone, Debug)]
pub struct FoldInstance<R: Ring, const D: usize> {
    round: usize,
    a: Vec<RingMatrixKey<R, D>>,
    w: Vec<RingMatrixKey<R, D>>,
    u: Elt<R, D>,
    beta: u64,
    roots: Vec<Vec<Elt<R, D>>>,
    claims: Vec<Elt<R, D>>,
    coeffs: Option<Vec<Vec<Elt<R, D>>>>,
    openings: Option<Vec<TreeOpenings<R, D>>>,
}

impl<R: Ring, const D: usize> FoldInstance<R, D> {
    /// Builds the round-`0` (or already-folded) **prover's** instance: the
    /// statement plus the witness coefficients and the surviving level arrays.
    ///
    /// `a[j]`/`w[j]` are the *remaining* levels, `a[0]` being level
    /// `(τ−1)k+1`.
    ///
    /// # Errors
    /// [`TrapError::WrongShape`] naming the axis that does not line up: level
    /// count vs coefficient count, `n` vs the root length, one opening array per
    /// claim, `2^{t+1}` entries on level `t`.
    pub fn new(
        round: usize,
        a: &[RingMatrixKey<R, D>],
        w: &[RingMatrixKey<R, D>],
        u: &Elt<R, D>,
        beta: u64,
        roots: &[Vec<Elt<R, D>>],
        claims: &[Elt<R, D>],
        coeffs: &[Vec<Elt<R, D>>],
        openings: Option<Vec<TreeOpenings<R, D>>>,
    ) -> Result<Self, TrapError> {
        Self::build(
            round,
            a,
            w,
            u,
            beta,
            roots,
            claims,
            Some(coeffs.to_vec()),
            openings,
        )
    }

    /// The same instance from the **verifier's** side: only the public statement
    /// `(A_j, w_j, t_κ, u_τ, z_κ, β_τ)`. No openings, and — because Fig. 5's
    /// rounds never ask for them — no coefficients either: the folded
    /// polynomials arrive in the final message and are checked there.
    ///
    /// # Errors
    /// As [`FoldInstance::new`].
    pub fn statement(
        round: usize,
        a: &[RingMatrixKey<R, D>],
        w: &[RingMatrixKey<R, D>],
        u: &Elt<R, D>,
        beta: u64,
        roots: &[Vec<Elt<R, D>>],
        claims: &[Elt<R, D>],
    ) -> Result<Self, TrapError> {
        Self::build(round, a, w, u, beta, roots, claims, None, None)
    }

    fn build(
        round: usize,
        a: &[RingMatrixKey<R, D>],
        w: &[RingMatrixKey<R, D>],
        u: &Elt<R, D>,
        beta: u64,
        roots: &[Vec<Elt<R, D>>],
        claims: &[Elt<R, D>],
        coeffs: Option<Vec<Vec<Elt<R, D>>>>,
        openings: Option<Vec<TreeOpenings<R, D>>>,
    ) -> Result<Self, TrapError> {
        if a.is_empty() || a.len() != w.len() {
            return Err(TrapError::WrongShape {
                got: a.len().max(w.len()),
                expected: a.len().min(w.len()),
            });
        }
        let h = a.len();
        let n = a[0].rows();
        if a.iter().any(|m| m.rows() != n || m.cols() != a[0].cols()) {
            return Err(TrapError::WrongShape {
                got: a.iter().map(|m| m.cols()).max().unwrap_or(0),
                expected: a[0].cols(),
            });
        }
        if w.iter().any(|m| m.rows() != n || m.cols() != n) {
            return Err(TrapError::WrongShape {
                got: w.iter().map(|m| m.cols()).max().unwrap_or(0),
                expected: n,
            });
        }
        let r = claims.len();
        if r == 0 || roots.len() != r || coeffs.as_ref().map_or(r, |c| c.len()) != r {
            return Err(TrapError::WrongShape {
                got: roots.len(),
                expected: r,
            });
        }
        for root in roots {
            if root.len() != n {
                return Err(TrapError::WrongShape {
                    got: root.len(),
                    expected: n,
                });
            }
        }
        if let Some(cs) = &coeffs {
            for c in cs {
                if c.len() != 1usize << h {
                    return Err(TrapError::WrongShape {
                        got: c.len(),
                        expected: 1usize << h,
                    });
                }
            }
        }
        if let Some(op) = &openings {
            if op.len() != r {
                return Err(TrapError::WrongShape {
                    got: op.len(),
                    expected: r,
                });
            }
            for o in op {
                if o.height() != h {
                    return Err(TrapError::WrongShape {
                        got: o.height(),
                        expected: h,
                    });
                }
                for array in &o.levels {
                    for v in array {
                        if v.len() != a[0].cols() {
                            return Err(TrapError::WrongShape {
                                got: v.len(),
                                expected: a[0].cols(),
                            });
                        }
                    }
                }
            }
        }
        Ok(Self {
            round,
            a: a.to_vec(),
            w: w.to_vec(),
            u: u.clone(),
            beta,
            roots: roots.to_vec(),
            claims: claims.to_vec(),
            coeffs,
            openings,
        })
    }

    /// Rounds already run (`τ`).
    #[must_use]
    pub fn round(&self) -> usize {
        self.round
    }

    /// Remaining levels `l_τ = h − kτ`.
    #[must_use]
    pub fn levels_left(&self) -> usize {
        self.a.len()
    }

    /// Claim count `r`.
    #[must_use]
    pub fn claims(&self) -> usize {
        self.claims.len()
    }

    /// The current norm slack `(r 2^k)^τ β`.
    #[must_use]
    pub fn beta(&self) -> u64 {
        self.beta
    }

    /// `u_τ`.
    #[must_use]
    pub fn u(&self) -> &Elt<R, D> {
        &self.u
    }

    /// `(t_{τ,κ})_κ`.
    #[must_use]
    pub fn roots(&self) -> &[Vec<Elt<R, D>>] {
        &self.roots
    }

    /// `(z_{τ,κ})_κ`.
    #[must_use]
    pub fn z(&self) -> &[Elt<R, D>] {
        &self.claims
    }

    /// The remaining levels' `A` matrices (`a[0]` is level `(τ−1)k+1`). Public
    /// because they are CRS material: a verifier needs them to state an
    /// instance, and they are the *only* part of a level it ever reads.
    #[must_use]
    pub fn levels_a(&self) -> &[RingMatrixKey<R, D>] {
        &self.a
    }

    /// The remaining levels' `W_j = w_j·Iₙ` matrices.
    #[must_use]
    pub fn levels_w(&self) -> &[RingMatrixKey<R, D>] {
        &self.w
    }

    /// The folded coefficient vectors, when this instance knows them: `Some` on
    /// the prover's side, `None` on the verifier's ([`FoldInstance::statement`]).
    #[must_use]
    pub fn coeffs(&self) -> Option<&[Vec<Elt<R, D>>]> {
        self.coeffs.as_deref()
    }

    /// The same statement reduced to what a verifier holds: no openings, no
    /// coefficients. Fig. 5 never asks for either before the final message.
    #[must_use]
    pub fn verifier_view(&self) -> Self {
        let mut out = self.clone();
        out.openings = None;
        out.coeffs = None;
        out
    }

    /// `u_{τ+1} = u_τ^{2^k}` — recomputed here, never read from the message.
    #[must_use]
    pub fn next_u(&self, kk: usize) -> Elt<R, D> {
        let k = log2_exact(kk).expect("a power-of-two folding factor");
        (0..k).fold(self.u.clone(), |acc, _| acc.clone() * acc)
    }

    /// Fig. 5 item 2(b)–(d): the partial evaluations and the `k` top levels'
    /// blocks of every claim.
    ///
    /// # Errors
    /// [`FoldError::NoWitness`] on the verifier's view (it holds neither the
    /// coefficients nor the openings);
    /// [`FoldError::Shape`] if `kk` is not a power of two or exceeds the
    /// remaining depth.
    pub fn prover_round(&self, kk: usize) -> Result<RoundMessage<R, D>, FoldError> {
        let openings = self.openings.as_ref().ok_or(FoldError::NoWitness)?;
        let coeffs = self.coeffs.as_ref().ok_or(FoldError::NoWitness)?;
        let k = log2_exact(kk).ok_or(FoldError::Shape(TrapError::WrongShape {
            got: kk,
            expected: 2,
        }))?;
        if k > self.levels_left() {
            return Err(FoldError::Shape(TrapError::WrongShape {
                got: self.levels_left(),
                expected: k,
            }));
        }
        let u_next = self.next_u(kk);
        let z = coeffs
            .iter()
            .map(|c| partial_evaluations(c, &u_next, kk).map_err(FoldError::Shape))
            .collect::<Result<Vec<_>, _>>()?;
        let blocks = openings
            .iter()
            .map(|o| o.sent_blocks(kk).map_err(FoldError::Shape))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(RoundMessage { z, blocks })
    }

    /// Fig. 5 item 2: this round's checks and the successor instance.
    ///
    /// The verifier's `t_{τ,κ}` is computed from the **received** blocks while
    /// the successor's openings come from the prover's own arrays, so a cheat on
    /// a block shifts the commitment without shifting the witness — which is
    /// what makes the base case catch it ([`FoldInstance::verify_final`]).
    ///
    /// Reported in `failing`, none of them short-circuiting:
    /// * `z-decompose(round τ,claim ι)` — `z_ι == Σ_i z_{ι,i} u^int(i)`
    ///   (item 2(d)i);
    /// * `norm(round τ,claim ι,level t,path x) <= β` — item 2(d)ii.
    ///
    /// # Errors
    /// [`FoldError::Shape`] if the message's shapes do not match the instance
    /// or `alpha` is not `r × kk`.
    pub fn fold_round(
        &self,
        msg: &RoundMessage<R, D>,
        alpha: &Alpha<R, D>,
    ) -> Result<RoundOutcome<R, D>, FoldError> {
        let kk = alpha.kk();
        let k = log2_exact(kk).ok_or(FoldError::Shape(TrapError::WrongShape {
            got: kk,
            expected: 2,
        }))?;
        if alpha.claims() != self.claims() || msg.z.len() != self.claims() {
            return Err(FoldError::Shape(TrapError::WrongShape {
                got: alpha.claims().max(msg.z.len()),
                expected: self.claims(),
            }));
        }
        if k > self.levels_left() {
            return Err(FoldError::Shape(TrapError::WrongShape {
                got: self.levels_left(),
                expected: k,
            }));
        }
        for (ι, zi) in msg.z.iter().enumerate() {
            if zi.len() != kk {
                return Err(FoldError::Shape(TrapError::WrongShape {
                    got: zi.len(),
                    expected: kk,
                }));
            }
            if msg.blocks.len() <= ι || msg.blocks[ι].len() != k {
                return Err(FoldError::Shape(TrapError::WrongShape {
                    got: msg.blocks.get(ι).map_or(0, Vec::len),
                    expected: k,
                }));
            }
            for (t, array) in msg.blocks[ι].iter().enumerate() {
                if array.len() != 1usize << (t + 1) {
                    return Err(FoldError::Shape(TrapError::WrongShape {
                        got: array.len(),
                        expected: 1usize << (t + 1),
                    }));
                }
                for v in array {
                    if v.len() != self.a[t].cols() {
                        return Err(FoldError::Shape(TrapError::WrongShape {
                            got: v.len(),
                            expected: self.a[t].cols(),
                        }));
                    }
                }
            }
        }
        let mut failing = Vec::new();
        // Item 2(d)i: the partial evaluations recombine to the current claim.
        for (ι, claim) in self.claims.iter().enumerate() {
            let mut acc = scalar_elt::<R, D>(R::ZERO);
            for (i, zi) in msg.z[ι].iter().enumerate() {
                acc = acc + scale_vec(zi, &[pow_elt(&self.u, i)])[0].clone();
            }
            if &acc != claim {
                failing.push(format!("z-decompose(round {},claim {ι})", self.round + 1));
            }
        }
        // Item 2(d)ii: every received block obeys this round's slack.
        for (ι, levels) in msg.blocks.iter().enumerate() {
            for (t, array) in levels.iter().enumerate() {
                for (x, v) in array.iter().enumerate() {
                    if vector_infinity_norm(v) > self.beta {
                        failing.push(format!(
                            "norm(round {},claim {ι},level {},path {x}) <= {}",
                            self.round + 1,
                            t + 1,
                            self.beta
                        ));
                    }
                }
            }
        }
        // Item 2(f): t̃, t_τ, z_τ, and — on the prover's side — the folded
        // coefficients and blocks. The verifier's successor keeps `coeffs: None`,
        // which is what makes "the verifier never reads the witness" a property
        // of the type rather than a comment.
        let n = self.a[0].rows();
        let zero = scalar_elt::<R, D>(R::ZERO);
        let mut next_roots: Vec<Vec<Elt<R, D>>> = (0..self.claims())
            .map(|_| vec![zero.clone(); n])
            .collect();
        let mut next_claims: Vec<Elt<R, D>> = vec![zero.clone(); self.claims()];
        let mut next_coeffs: Option<Vec<Vec<Elt<R, D>>>> =
            self.coeffs.as_ref().map(|cs| {
                (0..self.claims())
                    .map(|_| vec![zero.clone(); cs[0].len() / kk])
                    .collect()
            });
        for κ in 0..self.claims() {
            for ι in 0..self.claims() {
                let col: Vec<Elt<R, D>> =
                    (0..kk).map(|i| alpha.values[ι][i][κ].clone()).collect();
                let mut t_acc = vec![zero.clone(); n];
                let mut z_acc = zero.clone();
                for i in 0..kk {
                    let mut tt = self.roots[ι].clone();
                    for t in 0..k {
                        let x = i & ((1usize << (t + 1)) - 1);
                        let mut term = self.a[t].matvec(&msg.blocks[ι][t][x]).map_err(shape)?;
                        if (i >> t) & 1 == 1 {
                            term = self.w[t].matvec(&term).map_err(shape)?;
                        }
                        tt = sub_vec(&tt, &term);
                    }
                    t_acc = add_vec(&t_acc, &scale_vec(&col[i], &tt));
                    z_acc = z_acc + scale_vec(&col[i], &[msg.z[ι][i].clone()])[0].clone();
                }
                next_roots[κ] = add_vec(&next_roots[κ], &t_acc);
                next_claims[κ] = next_claims[κ].clone() + z_acc;
                if let Some(cs) = &self.coeffs {
                    let folded = fold_coeffs(&cs[ι], &col)?;
                    let acc = next_coeffs
                        .as_mut()
                        .expect("next_coeffs tracks self.coeffs");
                    for (j, v) in folded.into_iter().enumerate() {
                        acc[κ][j] = acc[κ][j].clone() + v;
                    }
                }
            }
        }
        let next_openings = match &self.openings {
            None => None,
            Some(op) => {
                let mut per_claim = Vec::with_capacity(self.claims());
                for κ in 0..self.claims() {
                    let alphas: Vec<Vec<Elt<R, D>>> = (0..self.claims())
                        .map(|ι| (0..kk).map(|i| alpha.values[ι][i][κ].clone()).collect())
                        .collect();
                    per_claim.push(TreeOpenings::fold_multi(op, &alphas, k)?);
                }
                Some(per_claim)
            }
        };
        let next = Self {
            round: self.round + 1,
            a: self.a[k..].to_vec(),
            w: self.w[k..].to_vec(),
            u: self.next_u(kk),
            beta: self.beta * (self.claims() * kk) as u64,
            roots: next_roots,
            claims: next_claims,
            coeffs: next_coeffs,
            openings: next_openings,
        };
        Ok(RoundOutcome { next, failing })
    }

    /// Fig. 5 item 3: the folded polynomials and every surviving block.
    ///
    /// # Errors
    /// [`FoldError::NoTrapdoor`] on the verifier's view, which has neither.
    pub fn final_message(&self) -> Result<FinalMessage<R, D>, FoldError> {
        let openings = match &self.openings {
            None => return Err(FoldError::NoTrapdoor),
            Some(o) => o.clone(),
        };
        let coeffs = match &self.coeffs {
            None => return Err(FoldError::NoTrapdoor),
            Some(c) => c.clone(),
        };
        Ok(FinalMessage { coeffs, openings })
    }

    /// Fig. 5 item 4 / relation (6): membership in
    /// `R^{(r)}_{h−kℓ, (r2^k)^ℓ β}` — every check, named, without
    /// short-circuiting.
    ///
    /// * `eval(claim κ)` — `f_{ℓ,κ}(u_ℓ) = z_{ℓ,κ}`;
    /// * `root(claim κ, leaf b)` — `Σ_{j=1}^{l} w_{kℓ+j}^{b_j} A_{kℓ+j} s_{b:j}
    ///   + f_b·e₁ = t_κ`: Fig. 4's additive root accumulation read out on the
    ///   **folded** blocks;
    /// * `final-norm(claim κ, level j, path x) <= β_ℓ`.
    ///
    /// # Errors
    /// [`FoldError::Shape`] if the message does not match the instance.
    pub fn verify_final(&self, msg: &FinalMessage<R, D>) -> Result<Vec<String>, FoldError> {
        if msg.coeffs.len() != self.claims() || msg.openings.len() != self.claims() {
            return Err(FoldError::Shape(TrapError::WrongShape {
                got: msg.coeffs.len().max(msg.openings.len()),
                expected: self.claims(),
            }));
        }
        let h = self.levels_left();
        if h == 0 {
            return Err(FoldError::Shape(TrapError::WrongShape {
                got: 0,
                expected: 1,
            }));
        }
        let n = self.a[0].rows();
        let m = self.a[0].cols();
        let mut e1 = vec![scalar_elt::<R, D>(R::ZERO); n];
        e1[0] = scalar_elt::<R, D>(R::ONE);
        let mut bad = Vec::new();
        for (κ, coeffs) in msg.coeffs.iter().enumerate() {
            if coeffs.len() != 1usize << h {
                return Err(FoldError::Shape(TrapError::WrongShape {
                    got: coeffs.len(),
                    expected: 1usize << h,
                }));
            }
            if msg.openings[κ].height() != h {
                return Err(FoldError::Shape(TrapError::WrongShape {
                    got: msg.openings[κ].height(),
                    expected: h,
                }));
            }
            if poly_eval(coeffs, &self.u) != self.claims[κ] {
                bad.push(format!("eval(claim {κ})"));
            }
            for (j, array) in msg.openings[κ].levels.iter().enumerate() {
                for (x, v) in array.iter().enumerate() {
                    if v.len() != m {
                        return Err(FoldError::Shape(TrapError::WrongShape {
                            got: v.len(),
                            expected: m,
                        }));
                    }
                    if vector_infinity_norm(v) > self.beta {
                        bad.push(format!(
                            "final-norm(claim {κ}, level {}, path {x}) <= {}",
                            j + 1,
                            self.beta
                        ));
                    }
                }
            }
            for b in 0..coeffs.len() {
                let mut acc = vec![scalar_elt::<R, D>(R::ZERO); n];
                for j in 0..h {
                    let x = b & ((1usize << (j + 1)) - 1);
                    let v = &msg.openings[κ].levels[j][x];
                    let mut term = self.a[j].matvec(v).map_err(shape)?;
                    if (b >> j) & 1 == 1 {
                        term = self.w[j].matvec(&term).map_err(shape)?;
                    }
                    acc = add_vec(&acc, &term);
                }
                let lhs = add_vec(&acc, &scale_vec(&coeffs[b], &e1));
                if lhs != self.roots[κ] {
                    bad.push(format!("root(claim {κ}, leaf {b})"));
                }
            }
        }
        Ok(bad)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use algebra::crypto::xof::Shake256Xof;
    use algebra::ring::zq::Zq;

    type Q = Zq<4294967197>;
    const D: usize = 8;
    /// Base 256 with **5** planes. The span check has to be *two-sided*: a
    /// base-256 greedy digit is folded into `[−127, 128]`, so `4` planes reach
    /// only `−127·(256⁴−1)/255 = −2.1391·10⁹` on the negative side, short of the
    /// least-absolute ceiling `−(q−1)/2 = −2.1475·10⁹`, even though the positive
    /// half `128·(256⁴−1)/255 = 2.1559·10⁹` clears it. The unrepresentable band
    /// is ~0.2% of `R_q`, so a 4-plane split is not "usually fine" here — it is
    /// `G·G⁻¹ ≠ id` on the inputs this module commits. The papers' plane rule
    /// `δ̃ = ⌊log_δ q⌋ + 1` needs a plane of headroom on an even base for
    /// exactly this reason (2023/846 Def. 2.13; `gadget::digit_expansion_is_exact`).
    /// 5 planes keep `G·G⁻¹ = id` exact at `5n` wide instead of `32n`.
    const BASE: u64 = 256;
    const DIGITS: usize = 5;
    const N: usize = 2;
    const MBAR: usize = 8;

    fn coeffs(h: usize, tag: u64) -> Vec<Elt<Q, D>> {
        (0..1usize << h)
            .map(|i| scalar_elt::<Q, D>(Q::from(tag * 101 + i as u64 * 7 + 3)))
            .collect()
    }

    fn tree(h: usize) -> PrisisTree<Q, D, BASE, DIGITS> {
        PrisisTree::setup(&[0x5au8; 32], N, MBAR, h, 1)
    }

    fn starts(h: usize) -> (PrisisTree<Q, D, BASE, DIGITS>, Vec<Elt<Q, D>>, FoldInstance<Q, D>, u64) {
        let t = tree(h);
        let cs = coeffs(h, 5);
        let proof = t.commit(&leaves_in_tree_order(&cs));
        let (a, w) = tree_keys(&t);
        let op = vec![TreeOpenings::from_proof(&t, &proof).unwrap()];
        let u = scalar_elt::<Q, D>(Q::from(17u64));
        let beta = t.certified_bound();
        let z = vec![poly_eval(&cs, &u)];
        let inst = FoldInstance::new(
            0,
            &a,
            &w,
            &u,
            beta,
            &[proof.root.clone()],
            &z,
            &[cs.clone()],
            Some(op),
        )
        .expect("shapes");
        (t, cs, inst, beta)
    }

    #[test]
    fn bitrev_is_an_involution_and_the_leaf_permutation_is_its_own() {
        for h in 1..=5 {
            for i in 0..(1usize << h) {
                assert_eq!(bitrev(h, bitrev(h, i)), i, "bitrev is an involution");
            }
            let cs = coeffs(h, 1);
            let perm = leaves_in_tree_order(&cs);
            for i in 0..cs.len() {
                assert_eq!(perm[bitrev(h, i)], cs[i], "the relabelling is a bijection");
            }
            // A tree committed through the permutation still opens on every
            // path with the LSB-first convention (the paper's), which is the
            // one fact the rest of this module is built on.
            let t = tree(h);
            let proof = t.commit(&perm);
            for i in 0..cs.len() {
                assert!(
                    t.failing(&proof.root, &path_bits(i, h), &cs[i], &t.path_openings(&proof, &path_bits(i, h)))
                        .unwrap()
                        .is_empty(),
                    "leaf {i} of a {h}-level tree must open"
                );
            }
        }
    }

    #[test]
    fn tree_openings_layout_agrees_with_path_openings_on_every_leaf() {
        let h = 3;
        let t = tree(h);
        let cs = coeffs(h, 2);
        let proof = t.commit(&leaves_in_tree_order(&cs));
        let op = TreeOpenings::from_proof(&t, &proof).expect("layout");
        assert_eq!(op.height(), h);
        for (j, array) in op.levels.iter().enumerate() {
            assert_eq!(array.len(), 1usize << (j + 1), "level {} block count", j + 1);
        }
        for i in 0..(1usize << h) {
            let path = path_bits(i, h);
            let via_tree = t.path_openings(&proof, &path);
            for (j, s) in via_tree.iter().enumerate() {
                assert_eq!(
                    *s,
                    op.level(j)[i & ((1usize << (j + 1)) - 1)],
                    "leaf {i} level {}",
                    j + 1
                );
            }
        }
    }

    #[test]
    fn folding_rounds_keeps_the_base_case_exactly_true() {
        for (h, kk, rounds) in [(3, 2, 1), (4, 2, 2), (4, 4, 1), (4, 2, 1), (3, 2, 2), (4, 4, 2)] {
            let (_t, _cs, inst, _beta) = starts(h);
            let mut cur = inst;
            // The verifier starts from the public statement alone: same levels,
            // same root, same claim — no witness, no openings.
            let mut check = FoldInstance::statement(
                0,
                cur.levels_a(),
                cur.levels_w(),
                cur.u(),
                cur.beta(),
                cur.roots(),
                cur.z(),
            )
            .expect("statement");
            for round in 0..rounds {
                let msg = cur.prover_round(kk).expect("message");
                let mut xof = Shake256Xof::new(&[(round * 7) as u8; 8]);
                let alpha = Alpha::sample(cur.claims(), kk, 1, &mut xof);
                let out = cur.fold_round(&msg, &alpha).expect("round");
                assert!(out.failing.is_empty(), "h={h} kk={kk} round {round}: {:?}", out.failing);
                // The verifier's view reaches the same t and z.
                let vout = check.fold_round(&msg, &alpha).expect("round");
                assert_eq!(out.next.roots(), vout.next.roots());
                assert_eq!(out.next.z(), vout.next.z());
                assert_eq!(vout.next.levels_a(), &cur.levels_a()[log2_exact(kk).unwrap()..]);
                check = vout.next;
                cur = out.next;
            }
            let fin = cur.final_message().expect("final");
            let k = log2_exact(kk).unwrap();
            if rounds * k == h {
                // Fig. 5 step 4's verdict is membership in `R^{(r)}_{h−kℓ, β_ℓ}`,
                // and §5's relation (3) is written over `(A_j, w_j, T_j)_{j∈[h]}`
                // with `∀b ∈ Z₂^h` — §5.1 opens by taking `k ∈ [h]` and
                // `l := h − k`. With `h − kℓ = 0` there is no tree left to
                // telescope, so *refusing* is the paper-faithful behaviour (the
                // instance is not "empty but valid"), and the verifier's view
                // refuses identically from the public statement alone.
                let refused = Err(FoldError::Shape(TrapError::WrongShape {
                    got: 0,
                    expected: 1,
                }));
                assert_eq!(cur.verify_final(&fin), refused, "h={h} kk={kk}: fully folded");
                assert_eq!(
                    check.verify_final(&fin),
                    refused,
                    "the statement-only verifier must reach the same verdict"
                );
            } else {
                let bad = cur.verify_final(&fin).expect("shapes");
                assert!(bad.is_empty(), "h={h} kk={kk} rounds={rounds}: {bad:?}");
                assert_eq!(
                    check.verify_final(&fin).expect("shapes"),
                    Vec::<String>::new(),
                    "the statement-only verifier must reach the same verdict"
                );
            }
            assert_eq!(cur.levels_left(), h - rounds * k);
        }
    }

    #[test]
    fn two_claims_fold_without_breaking_the_base_case() {
        let h = 3;
        let t = tree(h);
        let cs = [coeffs(h, 9), coeffs(h, 11)];
        let proofs = [
            t.commit(&leaves_in_tree_order(&cs[0])),
            t.commit(&leaves_in_tree_order(&cs[1])),
        ];
        let (a, w) = tree_keys(&t);
        let op: Vec<TreeOpenings<Q, D>> = proofs
            .iter()
            .map(|p| TreeOpenings::from_proof(&t, p).unwrap())
            .collect();
        let u = scalar_elt::<Q, D>(Q::from(19u64));
        let beta = t.certified_bound();
        let z: Vec<Elt<Q, D>> = cs.iter().map(|c| poly_eval(c, &u)).collect();
        let roots: Vec<Vec<Elt<Q, D>>> = proofs.iter().map(|p| p.root.clone()).collect();
        let mut cur =
            FoldInstance::new(0, &a, &w, &u, beta, &roots, &z, &cs, Some(op)).expect("two claims");
        for _ in 0..2 {
            let msg = cur.prover_round(2).expect("message");
            let mut xof = Shake256Xof::new(b"two-claims-a");
            let alpha = Alpha::sample(2, 2, 2, &mut xof);
            let out = cur.fold_round(&msg, &alpha).expect("round");
            assert!(out.failing.is_empty(), "{:?}", out.failing);
            cur = out.next;
        }
        let fin = cur.final_message().unwrap();
        let bad = cur.verify_final(&fin).unwrap();
        assert!(bad.is_empty(), "{bad:?}");
        assert_eq!(cur.beta(), beta * 16, "β grows by (r 2^k) per round");
    }

    #[test]
    fn a_false_partial_evaluation_trips_only_the_recombination_checks() {
        let (_t, _cs, inst, _beta) = starts(3);
        let msg = inst.prover_round(2).unwrap();
        let mut xof = Shake256Xof::new(b"alpha-1");
        let alpha = Alpha::sample(1, 2, 1, &mut xof);
        let mut lied = msg.clone();
        lied.z[0][0] = lied.z[0][0].clone() + scalar_elt::<Q, D>(Q::ONE);
        let out = inst.fold_round(&lied, &alpha).unwrap();
        assert_eq!(
            out.failing,
            vec!["z-decompose(round 1,claim 0)".to_string()],
            "a false z_i breaks the recombination and nothing else"
        );
        // The offset then surfaces again one round later: the folded claim is
        // wrong while the prover's own coefficients stayed honest.
        let msg2 = out.next.prover_round(2).unwrap();
        let mut xof2 = Shake256Xof::new(b"alpha-2");
        let alpha2 = Alpha::sample(1, 2, 1, &mut xof2);
        let out2 = out.next.fold_round(&msg2, &alpha2).unwrap();
        assert_eq!(out2.failing, vec!["z-decompose(round 2,claim 0)".to_string()]);
        let fin = out2.next.final_message().unwrap();
        assert!(
            out2.next.verify_final(&fin).unwrap().is_empty(),
            "the last round's z_τ is rebuilt from honest partial evaluations"
        );
    }

    #[test]
    fn a_swollen_block_shifts_the_commitment_and_breaks_every_leaf() {
        let (_t, _cs, inst, beta) = starts(4);
        let msg = inst.prover_round(2).unwrap();
        let mut xof = Shake256Xof::new(b"alpha-3");
        let alpha = Alpha::sample(1, 2, 1, &mut xof);
        let mut swollen = msg.clone();
        // Fig. 5 item 2(d)ii refuses a block with `‖s‖ > (r 2^k)^{τ−1} β`, so the
        // swell has to be measured *against β*, not as a literal: β is the
        // certified preimage bound `extra + (BASE/2)·max-row-ℓ₁`
        // (`prisis::certified_preimage_bound`), which grows with the digit base,
        // and an honest opening here sits two orders of magnitude below it. A
        // `+64` swell is therefore *inside* the bound — the verifier is right to
        // accept it. `β + 1` is the smallest coefficient that the check must
        // reject, and it stays inside the centered window so its representative
        // really is `β + 1`.
        assert!(
            beta + 1 < (Q::MODULUS - 1) / 2,
            "β = {beta} must leave room above it inside the centered window"
        );
        assert!(
            vector_infinity_norm(&msg.blocks[0][0][1]) <= beta,
            "the honest block is inside its bound, so a failure below is meaningful"
        );
        swollen.blocks[0][0][1][0] = scalar_elt::<Q, D>(Q::from(beta + 1));
        let out = inst.fold_round(&swollen, &alpha).unwrap();
        assert_eq!(out.failing.len(), 1, "{:?}", out.failing);
        assert!(
            out.failing[0].starts_with("norm(round 1,claim 0,level 1,path 1)"),
            "{:?}",
            out.failing
        );
        assert!(out.failing[0].ends_with(&format!("<= {beta}")));
        // One more round so two levels survive, then the base case: the
        // verifier's t carries the shift, the prover's blocks do not.
        let msg2 = out.next.prover_round(2).unwrap();
        let mut xof2 = Shake256Xof::new(b"alpha-4");
        let alpha2 = Alpha::sample(1, 2, 1, &mut xof2);
        let out2 = out.next.fold_round(&msg2, &alpha2).unwrap();
        assert!(out2.failing.iter().all(|s| s.starts_with("norm(")), "{:?}", out2.failing);
        let fin = out2.next.final_message().unwrap();
        let bad = out2.next.verify_final(&fin).unwrap();
        let roots: Vec<&String> = bad.iter().filter(|s| s.starts_with("root(")).collect();
        assert_eq!(roots.len(), 4, "all 2^2 surviving leaves must fail: {bad:?}");
        assert!(
            !bad.iter().any(|s| s.starts_with("eval(")),
            "the evaluation claim is untouched: {bad:?}"
        );
    }

    #[test]
    fn a_tampered_surviving_block_breaks_only_the_leaves_below_it() {
        let (_t, _cs, inst, _beta) = starts(4);
        let mut cur = inst;
        let mut xofs = [Shake256Xof::new(b"t-1"), Shake256Xof::new(b"t-2")];
        for xof in xofs.iter_mut() {
            let msg = cur.prover_round(2).unwrap();
            let alpha = Alpha::sample(1, 2, 1, xof);
            cur = cur.fold_round(&msg, &alpha).unwrap().next;
        }
        let mut fin = cur.final_message().unwrap();
        // Two rounds of `kk = 2` consumed levels 1 and 2, so the surviving tree
        // has `l = h − kℓ = 2` levels and 4 leaves, re-based to `Z_2^2` — Fig. 5
        // item 3 sends `(s_{ℓ,κ,i})_{i ∈ Z_2^{≤ h−kℓ}}`, and relation (3) reads
        // leaf `b` as `Σ_{j=1}^{h} w_j^{b_j} A_j s_{b:j} + f_b = t`, i.e. leaf b
        // consumes level j's block `b mod 2^j`. Surviving level index 0 (the old
        // level 3) holds 2 blocks, and block x of it is read by exactly the
        // leaves whose bit 0 is x: folded leaves 1 and 3.
        fin.openings[0].levels[0][1][0] =
            fin.openings[0].levels[0][1][0].clone() + scalar_elt::<Q, D>(Q::from(3u64));
        let bad = cur.verify_final(&fin).unwrap();
        assert_eq!(
            bad,
            vec![
                "root(claim 0, leaf 1)".to_string(),
                "root(claim 0, leaf 3)".to_string()
            ],
            "a level-3 block sits under exactly the leaves that read it"
        );
    }

    #[test]
    fn a_false_final_coefficient_breaks_its_own_leaf_and_the_claim() {
        let (_t, _cs, inst, _beta) = starts(4);
        let mut cur = inst;
        for seed in [b"f-1", b"f-2"] {
            let msg = cur.prover_round(2).unwrap();
            let mut xof = Shake256Xof::new(seed);
            let alpha = Alpha::sample(1, 2, 1, &mut xof);
            cur = cur.fold_round(&msg, &alpha).unwrap().next;
        }
        let mut fin = cur.final_message().unwrap();
        // Fig. 5 item 3 sends `f_ℓ ∈ R_q[X]^{≤ 2^{h−kℓ}−1}`: after two `kk = 2`
        // rounds of an `h = 4` tree the folded polynomial has `2² = 4`
        // coefficients, so the tampered one is index 2 of the *folded* vector
        // (index 6 was read in the pre-fold coordinate).
        assert_eq!(fin.coeffs[0].len(), 4, "2^(h − kℓ) coefficients survive");
        fin.coeffs[0][2] = fin.coeffs[0][2].clone() + scalar_elt::<Q, D>(Q::ONE);
        let bad = cur.verify_final(&fin).unwrap();
        assert_eq!(
            bad,
            vec!["eval(claim 0)".to_string(), "root(claim 0, leaf 2)".to_string()],
            "coefficient 2 appears in leaf 2's equation and in the claim"
        );
    }

    /// The `(position, negative)` of a signed monomial: panics unless `α` really
    /// is `±X^p`. `X^D = −1` in `R_q = Z_q[X]/(X^D + 1)`, so the *unreduced*
    /// exponent `α` stands for is `position` when the sign is `+1` and
    /// `position + D` when it is `−1` — the reduced position is an index, not an
    /// exponent, and the two disagree whenever the sampled exponent reaches `D`.
    fn signed_monomial(α: &Elt<Q, D>) -> (usize, bool) {
        let coeffs = α.coefficients();
        let mut nz = coeffs.iter().enumerate().filter(|(_, c)| **c != Q::ZERO);
        let (pos, c) = nz.next().expect("a monomial has a nonzero coefficient");
        assert!(nz.next().is_none(), "a monomial has exactly one nonzero coefficient");
        assert!(
            *c == Q::ONE || *c == -Q::ONE,
            "the unit's coefficient is a sign, not a scalar"
        );
        assert_eq!(vector_infinity_norm(&[α.clone()]), 1, "‖±X^p‖∞ = 1");
        (pos, *c == -Q::ONE)
    }

    /// A hand-built `±X^pos`, for a control the sampler need not produce.
    fn monomial_at(pos: usize, neg: bool) -> Elt<Q, D> {
        let mut coeffs = vec![Q::ZERO; D];
        coeffs[pos] = if neg { -Q::ONE } else { Q::ONE };
        PolyRing::<Q, D>::from_coefficients(coeffs)
    }

    /// The unreduced exponent behind a signed monomial.
    fn exponent_of(α: &Elt<Q, D>) -> usize {
        let (pos, neg) = signed_monomial(α);
        if neg {
            pos + D
        } else {
            pos
        }
    }

    #[test]
    fn monomial_challenges_are_units_with_one_nonzero_coefficient() {
        let mut xof = Shake256Xof::new(b"mono");
        let a = Alpha::<Q, D>::sample(2, 4, 1, &mut xof);
        assert_eq!(a.claims(), 2);
        assert_eq!(a.kk(), 4);
        assert_eq!(a.for_claim(1).len(), 2);
        for (ι, row) in a.values.iter().enumerate() {
            for (i, tuple) in row.iter().enumerate() {
                assert_eq!(tuple.len(), 2, "α_{{{ι},{i}}} has r entries");
                for α in tuple {
                    signed_monomial(α);
                }
            }
        }
        // Fig. 5 item 2(e) draws `α ← (X^r)^{r 2^k}`, i.e. from the subgroup
        // `⟨X^r⟩` of the `2D`-element monomial group. Membership there is a
        // statement about the *unreduced* exponent, because `Alpha::sample`
        // stores `X^e` as a sign flip at index `e mod D`.
        //
        // `r` must fail to generate the group for that membership to be a check
        // at all: `|⟨X^r⟩| = 2D/gcd(r, 2D)`, so with `gcd(r, 2D) = 1` (e.g.
        // `r = 3`, `2D = 16`) `⟨X^r⟩` is *every* monomial and "the exponent is a
        // multiple of r" cannot fail — it is not even well defined, since
        // `X^3 = X^19` and `3 | 19` is false. `r = 4` divides `2D` properly
        // (`⟨X^4⟩ = {±1, ±X^4}`, four elements out of sixteen), and there the
        // reduced position is forced to a multiple of `r` as well.
        let mut xof4 = Shake256Xof::new(b"mono-r");
        let r4 = Alpha::<Q, D>::sample(1, 2, 4, &mut xof4);
        for tuple in &r4.values[0] {
            for α in tuple {
                let (pos, _) = signed_monomial(α);
                let e = exponent_of(α);
                assert_eq!(e % 4, 0, "α = X^{e} must lie in ⟨X^4⟩");
                assert_eq!(pos % 4, 0, "4 | D here, so the index itself is a multiple of r");
            }
        }
        // The sign folding is real, not vacuous: `r = 3` draws exponents in
        // {0, 3, 6, 9, 12, 15}, and any `e ≥ D` lands at a position that is *not*
        // a multiple of 3 (`X^9 = −X` sits at index 1). Asserting the old
        // `pos % r == 0` therefore read the wrong number; the invariant on the
        // unreduced exponent is the one that holds.
        let mut xof3 = Shake256Xof::new(b"mono-r3");
        let r3 = Alpha::<Q, D>::sample(1, 8, 3, &mut xof3);
        let mut folded_past_d = 0;
        for tuple in &r3.values[0] {
            for α in tuple {
                let (pos, _) = signed_monomial(α);
                let e = exponent_of(α);
                assert_eq!(e % 3, 0, "α = X^{e} is a power of X^3");
                if pos % 3 != 0 {
                    folded_past_d += 1;
                    assert!(pos < D && e >= D, "position {pos} is e = {e} reduced mod X^D = −1");
                }
            }
        }
        assert!(
            folded_past_d > 0,
            "r = 3 must actually produce exponents ≥ D, else this case proves nothing"
        );
        // And the check bites: these are monomial units with one nonzero
        // coefficient of magnitude 1 — everything the loop above over `a.values`
        // accepts — yet neither lies in `⟨X^4⟩`, so the exponent predicate must
        // reject both. Without them the `r = 4` assertions could be satisfied by
        // any signed monomial whatsoever.
        let outside = [
            monomial_at(2, false), //  X^2
            monomial_at(1, true),  // −X
            monomial_at(4, true),  // −X^4, the sign-folded member of ⟨X^4⟩
        ];
        for α in &outside[..2] {
            let e = exponent_of(α);
            assert_ne!(e % 4, 0, "X^{e} is outside ⟨X^4⟩ and must be rejected");
        }
        assert_eq!(exponent_of(&outside[2]) % 4, 0, "the predicate does not over-reject");
    }

    #[test]
    fn fold_coeffs_and_partial_evaluations_agree_with_the_direct_expansion() {
        // FMN Eq. (17) / SLAP Fig. 5 item 2(d)i: the pieces rebuild f(u).
        let cs = coeffs(4, 21);
        let u = scalar_elt::<Q, D>(Q::from(31u64));
        let u_next = (0..3).fold(u.clone(), |acc, _| acc.clone() * acc);
        let zs = partial_evaluations(&cs, &u_next, 8).unwrap();
        let mut rebuilt = scalar_elt::<Q, D>(Q::ZERO);
        for (i, z) in zs.iter().enumerate() {
            rebuilt = rebuilt + scale_vec(z, &[pow_elt(&u, i)])[0].clone();
        }
        assert_eq!(rebuilt, poly_eval(&cs, &u), "Eq. (17)");
        let alpha: Vec<Elt<Q, D>> = (0..8)
            .map(|i| scalar_elt::<Q, D>(Q::from(i as u64 + 1)))
            .collect();
        let folded = fold_coeffs(&cs, &alpha).unwrap();
        assert_eq!(folded.len(), 2);
        for (j, v) in folded.iter().enumerate() {
            let mut acc = scalar_elt::<Q, D>(Q::ZERO);
            for (i, a) in alpha.iter().enumerate() {
                acc = acc + scale_vec(a, &[cs[8 * j + i].clone()])[0].clone();
            }
            assert_eq!(*v, acc);
        }
        // TreeOpenings::fold's stride matches the same indexing on vectors.
        let op = TreeOpenings::from_levels(
            (1..=4usize)
                .map(|t| {
                    (0..1usize << t)
                        .map(|x| {
                            (0..3usize)
                                .map(|c| scalar_elt::<Q, D>(Q::from((10 * t + x + c) as u64)))
                                .collect()
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let folded_op = op.fold(&alpha).unwrap();
        assert_eq!(folded_op.height(), 1);
        for x in 0..2usize {
            let mut acc = vec![scalar_elt::<Q, D>(Q::ZERO); 3];
            for (i, a) in alpha.iter().enumerate() {
                acc = add_vec(&acc, &scale_vec(a, &op.level(3)[i + 8 * x]));
            }
            assert_eq!(folded_op.level(0)[x], acc, "stride int(i) + kk·int(x)");
        }
    }

    #[test]
    fn shapes_are_refused_rather_than_guessed() {
        let h = 2;
        let t = tree(h);
        let cs = coeffs(h, 33);
        let proof = t.commit(&leaves_in_tree_order(&cs));
        let (a, w) = tree_keys(&t);
        let u = scalar_elt::<Q, D>(Q::from(5u64));
        let z = vec![poly_eval(&cs, &u)];
        let too_tall = vec![vec![scalar_elt::<Q, D>(Q::ZERO); a[0].rows() + 1]];
        assert_eq!(
            FoldInstance::new(0, &a, &w, &u, 1, &too_tall, &z, &[cs.clone()], None).err(),
            Some(TrapError::WrongShape {
                got: 3,
                expected: 2
            }),
            "a root of the wrong height is refused"
        );
        assert_eq!(
            FoldInstance::new(0, &a, &w, &u, 1, &[], &z, &[cs.clone()], None).err(),
            Some(TrapError::WrongShape { got: 0, expected: 1 }),
            "a statement with no root is refused"
        );
        assert_eq!(
            fold_coeffs(&cs, &[] as &[Elt<Q, D>]),
            Err(TrapError::WrongShape {
                got: 4,
                expected: 1
            })
        );
        assert_eq!(
            partial_evaluations(&cs, &u, 3),
            Err(TrapError::WrongShape {
                got: 4,
                expected: 3
            })
        );
        assert_eq!(
            TreeOpenings::from_levels(vec![vec![vec![scalar_elt::<Q, D>(Q::ZERO); 1]]]).err(),
            Some(TrapError::WrongShape {
                got: 1,
                expected: 2
            }),
            "level 1 holds 2^1 = 2 blocks, not 1"
        );
        let mut inst =
            FoldInstance::new(0, &a, &w, &u, 1, &[proof.root.clone()], &z, &[cs.clone()], None)
                .unwrap();
        assert_eq!(inst.prover_round(2).err(), Some(FoldError::NoWitness));
        let msg = RoundMessage {
            z: vec![vec![scalar_elt::<Q, D>(Q::ZERO); 2]],
            blocks: vec![vec![vec![vec![scalar_elt::<Q, D>(Q::ZERO); a[0].cols()]; 2]]],
        };
        let alpha = Alpha::sample(1, 2, 1, &mut Shake256Xof::new(b"shape"));
        // Each round consumes `k = log₂(kk) = 1` level (Fig. 5 item 2(a):
        // `l_τ = l_{τ−1} − k`), so an `h = 2` tree reaches `l = 0` only after
        // *two* rounds. Both messages here are the all-zero one the shapes allow
        // at either level, and the fold is chained: `levels_left` must fall by
        // one per round, which is the invariant the discarded call hid.
        inst = inst.fold_round(&msg, &alpha).expect("first round").next;
        assert_eq!(inst.levels_left(), 1, "one kk=2 round leaves l = h − k = 1");
        inst = inst.fold_round(&msg, &alpha).expect("second round").next;
        assert_eq!(inst.levels_left(), 0);
        assert_eq!(
            inst.verify_final(&FinalMessage {
                coeffs: vec![vec![scalar_elt::<Q, D>(Q::ZERO); 1]],
                openings: vec![TreeOpenings::from_levels(vec![]).unwrap()],
            }),
            Err(FoldError::Shape(TrapError::WrongShape {
                got: 0,
                expected: 1
            })),
            "a fully folded instance has no base case to check"
        );
    }
}
