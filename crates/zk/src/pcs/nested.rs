//! Nested-gadget Ajtai hashing (Z7 capability for the CMNW / SLAP line).
//!
//! Both schemes commit through a *chain* of gadget-decomposed Ajtai hashes
//! rather than Greyhound's fixed two layers. With the gadget `G` and level
//! matrices `A₁, …, A_ℓ`, each level is the map
//!
//! ```text
//! h_i(x) = A_i · G⁻¹(x)
//! ```
//!
//! and committing to `f` runs the levels from the bottom up, so the opening
//! "path" is the chain of short preimages `(s₀, …, s_ℓ)` — explicitly **not**
//! Merkle sibling hashes, which is why this line needs no trapdoor sampler
//! (survey §1 CMNW row; the preimages come from `G⁻¹`, not from SamplePre).
//!
//! Reading the shapes off CMNW's own instantiation: `t = (I ⊗ A₁)·s₁` with
//! `s₁ = G⁻¹((I ⊗ A₂)·G⁻¹(f))`, i.e. `h₁(h₂(f))` up to the tensor factor,
//! which is carried here by the level widths instead of a separate mechanism.
//!
//! # Why shortness is the point
//!
//! Every intermediate `G⁻¹(·)` output is binary, so `‖sᵢ‖∞ = 1` by
//! construction. Knowledge proofs against these commitments extract a *short*
//! chain, and it is that bound — not the algebra — that the soundness argument
//! consumes; [`NestedGadget::preimage_chain`] is what a scheme hands to its
//! norm gate.

use crate::pcs::greyhound::{ntt_op, AjtaiKeyHeap};
use crate::pcs::{RingElt, DELTA, DIM, N_ROWS};
use alloc::vec::Vec;
use core::fmt;

/// Typed rejection for the nested-gadget layer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum NestedError {
    /// A level was asked for that the key does not have.
    UnknownLevel,
    /// An input had the width the level does not accept.
    WrongWidth {
        /// Width the caller supplied.
        got: usize,
        /// Width the level expects.
        expected: usize,
    },
    /// The key was built with no levels.
    EmptyKey,
}

impl fmt::Display for NestedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NestedError::UnknownLevel => write!(f, "no such level in this key"),
            NestedError::WrongWidth { got, expected } => {
                write!(f, "level takes {expected} ring elements, got {got}")
            }
            NestedError::EmptyKey => write!(f, "a nested key needs at least one level"),
        }
    }
}

/// A chain of gadget-decomposed Ajtai hashes `h_i(x) = A_i · G⁻¹(x)`.
///
/// Level `0` is the outermost (its output is the commitment); level
/// `levels − 1` is the innermost, the one that consumes the polynomial.
#[derive(Clone)]
pub struct NestedGadget {
    seed: [u8; 32],
    /// `keys[i]` has `N_ROWS` rows and `widths[i] · DELTA` columns, where
    /// `widths[i]` is the number of ring elements level `i` accepts.
    keys: Vec<AjtaiKeyHeap>,
    /// Ring elements accepted by each level.
    widths: Vec<usize>,
}

impl fmt::Debug for NestedGadget {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("NestedGadget")
            .field("levels", &self.keys.len())
            .field("widths", &self.widths)
            .finish()
    }
}

impl NestedGadget {
    /// Builds `ℓ` levels from one master seed. `widths[i]` is how many ring
    /// elements level `i` hashes; each level's key is `N_ROWS × widths[i]·δ`.
    ///
    /// Every level outputs `N_ROWS` ring elements, so a chain of more than one
    /// level is only well-formed when all but the innermost width equal
    /// `N_ROWS`; [`NestedGadget::commit_chain`] reports the mismatch rather
    /// than hashing a length it was not given.
    ///
    /// # Panics
    /// If `widths` is empty or any width is zero (a level that hashes nothing
    /// would make the chain degenerate).
    pub fn setup(seed: &[u8; 32], widths: &[usize]) -> Self {
        assert!(!widths.is_empty(), "a nested key needs at least one level");
        assert!(
            widths.iter().all(|&w| w > 0),
            "a level with width zero would never be hashed into"
        );
        let keys = widths
            .iter()
            .enumerate()
            .map(|(i, &w)| {
                // The level index must enter the label: with only
                // (label, seed) two levels of equal width would expand to
                // the *same* matrix and the chain would collapse.
                let mut label = b"nested-gadget-level".to_vec();
                label.extend_from_slice(&(i as u32).to_le_bytes());
                AjtaiKeyHeap::setup(&label, seed, N_ROWS, w * DELTA)
            })
            .collect();
        Self {
            seed: *seed,
            keys,
            widths: widths.to_vec(),
        }
    }

    /// The binding master seed.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// The gadget digit count each level expands to.
    pub const fn digits(&self) -> usize {
        DELTA
    }

    /// The ring degree of the committed elements.
    pub const fn ring_degree(&self) -> usize {
        DIM
    }

    /// Number of levels.
    pub fn levels(&self) -> usize {
        self.keys.len()
    }

    /// Widths accepted by each level, outermost first.
    pub fn widths(&self) -> &[usize] {
        &self.widths
    }

    /// `h_i(x) = A_i · G⁻¹(x)`: expand `x` into its binary digit planes and
    /// apply the level matrix.
    ///
    /// # Errors
    /// [`NestedError::UnknownLevel`] for a level index out of range,
    /// [`NestedError::WrongWidth`] if `x.len()` is not the level's width.
    pub fn hash_level(&self, level: usize, x: &[RingElt]) -> Result<Vec<RingElt>, NestedError> {
        let key = self.keys.get(level).ok_or(NestedError::UnknownLevel)?;
        let expected = self.widths[level];
        if x.len() != expected {
            return Err(NestedError::WrongWidth {
                got: x.len(),
                expected,
            });
        }
        let digits = crate::pcs::gadget::split::<_, DIM, 2, DELTA>(x);
        debug_assert_eq!(digits.len(), expected * DELTA);
        Ok(key.commit(&digits, &ntt_op()))
    }

    /// Runs the whole chain bottom-up on `f` and returns
    /// `(commitment, preimages)` where `preimages[i]` is the digit expansion
    /// fed into level `i` — the object a knowledge proof reveals.
    ///
    /// `f` must have the width of the **innermost** level.
    ///
    /// # Errors
    /// As [`hash_level`], plus [`NestedError::EmptyKey`] is impossible by the
    /// constructor's invariant.
    pub fn commit_chain(
        &self,
        f: &[RingElt],
    ) -> Result<(Vec<RingElt>, Vec<Vec<RingElt>>), NestedError> {
        let last = self.keys.len() - 1;
        if f.len() != self.widths[last] {
            return Err(NestedError::WrongWidth {
                got: f.len(),
                expected: self.widths[last],
            });
        }
        let mut current = f.to_vec();
        let mut preimages = Vec::with_capacity(self.keys.len());
        // Bottom level first: its digits are the innermost preimage.
        for level in (0..self.keys.len()).rev() {
            let digits = crate::pcs::gadget::split::<_, DIM, 2, DELTA>(&current);
            preimages.push(digits.clone());
            current = self.keys[level].commit(&digits, &ntt_op());
            // Every upper level consumes `widths[level-1]` elements; the
            // chain is only well-formed when the widths line up.
            if level > 0 && current.len() != self.widths[level - 1] {
                return Err(NestedError::WrongWidth {
                    got: current.len(),
                    expected: self.widths[level - 1],
                });
            }
        }
        preimages.reverse();
        Ok((current, preimages))
    }

    /// The digit chains revealed by [`commit_chain`], for a norm gate.
    ///
    /// Every entry is a binary digit plane, so the infinity norm is `1` by
    /// construction; this helper exists so a scheme asserts that rather than
    /// assuming it.
    pub fn preimage_chain(&self, f: &[RingElt]) -> Result<Vec<Vec<RingElt>>, NestedError> {
        Ok(self.commit_chain(f)?.1)
    }
}

/// A level of a **tensor** key: one small Ajtai matrix `A ∈ R_q^{n×cols·δ}`
/// applied block-wise, i.e. the map `I_blocks ⊗ A`.
#[derive(Clone)]
struct TensorLevel {
    blocks: usize,
    cols: usize,
    key: AjtaiKeyHeap,
}

/// Block-diagonal (tensor) gadget keys `(I_m ⊗ A)`.
///
/// Maltese and CMNW do not hash a whole level with one wide matrix; they
/// apply the *same* small `A` independently to `2^i` blocks:
///
/// ```text
/// s_ℓ = G⁻¹(f)                    (leaves)
/// s_i = G⁻¹((I_{2^i} ⊗ A) · s_{i+1})
/// t   = A · s_1                   (root)
/// ```
///
/// The distinction is not cosmetic: `I_m ⊗ A` and a single
/// `A' ∈ R_q^{n × m·cols·δ}` have different lattice geometry, and it is the
/// *block-wise* form whose short preimages the norm argument consumes.
/// [`NestedGadget`] keeps the wide form (Greyhound/LaBRADOR's outer layer);
/// both lanes stay reachable here.
#[derive(Clone)]
pub struct TensorGadget {
    seed: [u8; 32],
    levels: Vec<TensorLevel>,
}

impl TensorGadget {
    /// Builds one level per `(blocks, cols)` pair, **outermost first**: index
    /// `0` produces the root and the last index consumes the leaves, matching
    /// [`TensorGadget::commit_tree`]. Level `i`'s key is `N_ROWS × cols·δ`,
    /// derived from the shared seed with the level index mixed into the
    /// domain-separation label.
    ///
    /// # Panics
    /// If `levels` is empty, or any `blocks`/`cols` is zero.
    pub fn setup(seed: &[u8; 32], levels: &[(usize, usize)]) -> Self {
        assert!(!levels.is_empty(), "a tensor key needs at least one level");
        assert!(
            levels.iter().all(|&(b, c)| b > 0 && c > 0),
            "levels with zero blocks or columns are not keys"
        );
        Self {
            seed: *seed,
            levels: levels
                .iter()
                .enumerate()
                .map(|(i, &(blocks, cols))| {
                    let mut label = b"tensor-gadget-level".to_vec();
                    label.extend_from_slice(&(i as u32).to_le_bytes());
                    TensorLevel {
                        blocks,
                        cols,
                        key: AjtaiKeyHeap::setup(&label, seed, N_ROWS, cols * DELTA),
                    }
                })
                .collect(),
        }
    }

    /// The binding master seed.
    pub fn seed(&self) -> &[u8; 32] {
        &self.seed
    }

    /// `(blocks, cols)` per level, outermost first.
    pub fn shape(&self) -> Vec<(usize, usize)> {
        self.levels.iter().map(|l| (l.blocks, l.cols)).collect()
    }

    /// Number of levels.
    pub fn levels(&self) -> usize {
        self.levels.len()
    }

    /// Input length level `i` accepts.
    pub fn input_len(&self, level: usize) -> Option<usize> {
        self.levels.get(level).map(|l| l.blocks * l.cols)
    }

    /// Output length of level `i`: `blocks · N_ROWS`.
    pub fn output_len(&self, level: usize) -> Option<usize> {
        self.levels.get(level).map(|l| l.blocks * N_ROWS)
    }

    /// `(I_blocks ⊗ A) · G⁻¹(x)`: split `x` into `blocks` groups of `cols`,
    /// digit-decompose each group and apply the shared `A` to it.
    ///
    /// # Errors
    /// [`NestedError::UnknownLevel`] / [`NestedError::WrongWidth`] as for
    /// [`NestedGadget::hash_level`].
    pub fn hash(&self, level: usize, x: &[RingElt]) -> Result<Vec<RingElt>, NestedError> {
        let l = self.levels.get(level).ok_or(NestedError::UnknownLevel)?;
        let expected = l.blocks * l.cols;
        if x.len() != expected {
            return Err(NestedError::WrongWidth {
                got: x.len(),
                expected,
            });
        }
        let op = ntt_op();
        let mut out = Vec::with_capacity(l.blocks * N_ROWS);
        for block in x.chunks(l.cols) {
            let digits = crate::pcs::gadget::split::<_, DIM, 2, DELTA>(block);
            out.extend_from_slice(&l.key.commit(&digits, &op));
        }
        Ok(out)
    }

    /// Runs the tree relation bottom-up on `f`, returning
    /// `(root, preimages)` where `preimages[i]` is the digit expansion fed
    /// into level `i`.
    ///
    /// Level `i + 1`'s output must be exactly level `i`'s input; a mismatch is
    /// reported rather than silently truncated or zero-padded.
    ///
    /// # Errors
    /// [`NestedError::WrongWidth`] on a length the innermost level or an
    /// intermediate level does not accept.
    pub fn commit_tree(
        &self,
        f: &[RingElt],
    ) -> Result<(Vec<RingElt>, Vec<Vec<RingElt>>), NestedError> {
        let last = self.levels.len() - 1;
        let expected = self.levels[last].blocks * self.levels[last].cols;
        if f.len() != expected {
            return Err(NestedError::WrongWidth {
                got: f.len(),
                expected,
            });
        }
        let mut current = f.to_vec();
        let mut preimages = Vec::with_capacity(self.levels.len());
        for level in (0..self.levels.len()).rev() {
            let l = &self.levels[level];
            let block = l.cols;
            if current.len() % block != 0 {
                return Err(NestedError::WrongWidth {
                    got: current.len(),
                    expected: (current.len() / block) * block,
                });
            }
            let mut next = Vec::with_capacity((current.len() / block) * N_ROWS);
            for grp in current.chunks(block) {
                let digits = crate::pcs::gadget::split::<_, DIM, 2, DELTA>(grp);
                preimages.push(digits.clone());
                next.extend_from_slice(&l.key.commit(&digits, &ntt_op()));
            }
            if level > 0 {
                let want = self.levels[level - 1].blocks * self.levels[level - 1].cols;
                if next.len() != want {
                    return Err(NestedError::WrongWidth {
                        got: next.len(),
                        expected: want,
                    });
                }
            }
            current = next;
        }
        preimages.reverse();
        Ok((current, preimages))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::encoding::ring_to_u32;
    use crate::foundation::sampling::from_centered;
    use crate::pcs::Z1Coeff;
    use algebra::ring::traits::CenteredRing;
    use algebra::ring::PolynomialQuotientRing;
    #[allow(unused_imports)]
    use alloc::vec;

    /// Three levels, outermost first. Each level outputs `N_ROWS` elements, so
    /// the two outer widths are `N_ROWS`; the innermost takes the polynomial.
    fn widths() -> Vec<usize> {
        vec![N_ROWS, N_ROWS, N_ROWS]
    }

    fn key() -> NestedGadget {
        NestedGadget::setup(&[0x5eu8; 32], &widths())
    }

    fn poly(seed: u64, len: usize) -> Vec<RingElt> {
        (0..len)
            .map(|i| {
                let coeffs: Vec<_> = (0..DIM)
                    .map(|j| {
                        let v = (seed as i64 * 31 + i as i64 * 7 + j as i64) % 9;
                        from_centered::<Z1Coeff>(v - 4)
                    })
                    .collect();
                RingElt::from_coefficients(coeffs)
            })
            .collect()
    }

    fn max_norm(elts: &[RingElt]) -> u64 {
        elts.iter()
            .flat_map(ring_to_u32::<Z1Coeff, DIM>)
            .map(|c| Z1Coeff::from(u64::from(c)).abs_infinity())
            .max()
            .unwrap_or(0)
    }

    #[test]
    fn level_hash_is_the_matrix_applied_to_the_digit_planes() {
        // h_i(x) must equal A_i · G⁻¹(x) with G⁻¹ the exact binary split:
        // check the digit count and that recombining the digits returns x, so
        // the level really consumes the gadget image and not something else.
        let k = key();
        let x = poly(1, k.widths()[2]);
        let digits = crate::pcs::gadget::split::<_, DIM, 2, DELTA>(&x);
        assert_eq!(digits.len(), x.len() * DELTA);
        assert_eq!(max_norm(&digits), 1, "digits are binary");
        let back = crate::pcs::gadget::join::<_, DIM, 2, DELTA>(&digits);
        for (orig, rt) in x.iter().zip(back.iter()) {
            assert_eq!(
                ring_to_u32::<Z1Coeff, DIM>(orig),
                ring_to_u32::<Z1Coeff, DIM>(rt)
            );
        }
        let hashed = k.hash_level(2, &x).expect("innermost level");
        assert_eq!(hashed.len(), N_ROWS, "every level outputs n rows");
    }

    #[test]
    fn chain_runs_bottom_up_and_reveals_short_preimages() {
        let k = key();
        let f = poly(7, k.widths()[2]);
        let (com, preimages) = k.commit_chain(&f).expect("chain");
        assert_eq!(com.len(), N_ROWS);
        assert_eq!(preimages.len(), k.levels());
        for plane in &preimages {
            assert_eq!(max_norm(plane), 1, "every preimage in the chain is binary");
        }
        // widths must line up: level i consumes widths[i] elements
        for (i, plane) in preimages.iter().enumerate() {
            assert_eq!(plane.len(), k.widths()[i] * DELTA);
        }
    }

    #[test]
    fn chain_is_deterministic_and_depends_on_the_input() {
        let k = key();
        let a = k.commit_chain(&poly(3, 4)).expect("chain").0;
        let b = k.commit_chain(&poly(3, 4)).expect("chain").0;
        let c = k.commit_chain(&poly(4, 4)).expect("chain").0;
        assert_eq!(a, b, "same input, same commitment");
        assert_ne!(a, c, "different input must move the commitment");
    }

    #[test]
    fn a_different_seed_gives_a_different_chain() {
        let one = NestedGadget::setup(&[1u8; 32], &widths());
        let two = NestedGadget::setup(&[2u8; 32], &widths());
        let f = poly(5, 4);
        assert_ne!(
            one.commit_chain(&f).expect("c1").0,
            two.commit_chain(&f).expect("c2").0
        );
    }

    #[test]
    fn equal_width_levels_are_distinct_matrices() {
        // Load-bearing: the level index enters the key label. If it did not,
        // every level of equal width would expand to the SAME matrix and the
        // chain would silently collapse into repeated squaring by one key.
        let k = key();
        assert!(k.levels() >= 2);
        assert_eq!(k.widths()[0], k.widths()[1], "test needs equal widths");
        let x = poly(11, k.widths()[0]);
        let h0 = k.hash_level(0, &x).expect("level 0");
        let h1 = k.hash_level(1, &x).expect("level 1");
        assert_ne!(h0, h1, "levels must not share a key");
    }

    #[test]
    fn rejects_out_of_range_levels_and_bad_widths() {
        let k = key();
        assert_eq!(k.hash_level(9, &poly(1, 4)), Err(NestedError::UnknownLevel));
        assert!(matches!(
            k.hash_level(0, &poly(1, 3)),
            Err(NestedError::WrongWidth {
                got: 3,
                expected: N_ROWS
            })
        ));
        assert!(matches!(
            k.commit_chain(&poly(1, 5)),
            Err(NestedError::WrongWidth {
                got: 5,
                expected: 4
            })
        ));
    }

    #[test]
    fn mismatched_level_widths_are_refused_not_silently_mis_hashed() {
        // widths [4, 8, 4]: the innermost level emits N_ROWS = 4 elements but
        // level 1 demands 8, so the chain must report the mismatch instead of
        // producing a commitment to nothing.
        let k = NestedGadget::setup(&[9u8; 32], &[4, 8, 4]);
        let r = k.commit_chain(&poly(2, 4));
        assert!(matches!(r, Err(NestedError::WrongWidth { .. })));
    }

    #[test]
    fn tensor_hash_is_blockwise_application_of_one_key() {
        let t = TensorGadget::setup(&[0x77u8; 32], &[(3, 4)]);
        let x = poly(1, 12); // 3 blocks × 4 columns
        let got = t.hash(0, &x).expect("hash");
        assert_eq!(got.len(), 3 * N_ROWS, "blocks × n out");

        // The same seed with one block yields the same level-0 key `A`, so
        // hashing group-by-group must reproduce `(I₃ ⊗ A)·G⁻¹(x)` exactly.
        let one = TensorGadget::setup(&[0x77u8; 32], &[(1, 4)]);
        let expect: Vec<RingElt> = x
            .chunks(4)
            .flat_map(|grp| one.hash(0, grp).expect("single block accepts 4 elements"))
            .collect();
        assert_eq!(got, expect, "(I⊗A) must equal per-block A");
    }

    #[test]
    fn tensor_and_wide_keys_are_not_the_same_object() {
        // Guards against silently aliasing the two shapes: same seed, same
        // total width, different geometry ⇒ different digest.
        let wide = NestedGadget::setup(&[0x2au8; 32], &[8]);
        let tensor = TensorGadget::setup(&[0x2au8; 32], &[(2, 4)]);
        let x = poly(4, 8);
        let h_wide = wide.hash_level(0, &x).expect("wide");
        let h_tensor = tensor.hash(0, &x).expect("tensor");
        assert_eq!(h_wide.len(), N_ROWS);
        assert_eq!(h_tensor.len(), 2 * N_ROWS);
        assert_ne!(
            h_wide,
            &h_tensor[..N_ROWS],
            "tensor is not a truncated wide hash"
        );
    }

    #[test]
    fn tensor_tree_runs_bottom_up_with_binary_preimages() {
        // Both levels (2 blocks × 4 cols): the innermost consumes 8 leaves and
        // emits 2·N_ROWS = 8 elements, which the outer level accepts as-is.
        let t = TensorGadget::setup(&[0x31u8; 32], &[(2, 4), (2, 4)]);
        let f = poly(6, 8);
        let (root, preimages) = t.commit_tree(&f).expect("tree");
        assert_eq!(root.len(), 2 * N_ROWS);
        // two groups hashed per level
        assert_eq!(preimages.len(), 4);
        for plane in &preimages {
            assert_eq!(plane.len(), 4 * DELTA, "one digit expansion per group");
        }
        for plane in &preimages {
            assert_eq!(max_norm(plane), 1, "tensor preimages are binary");
        }
    }

    #[test]
    fn tensor_rejects_wrong_input_length() {
        let t = TensorGadget::setup(&[0x44u8; 32], &[(3, 4)]);
        assert!(matches!(
            t.hash(0, &poly(1, 11)),
            Err(NestedError::WrongWidth {
                got: 11,
                expected: 12
            })
        ));
        assert_eq!(t.hash(9, &poly(1, 12)), Err(NestedError::UnknownLevel));
        assert!(matches!(
            t.commit_tree(&poly(1, 7)),
            Err(NestedError::WrongWidth { .. })
        ));
    }
}
