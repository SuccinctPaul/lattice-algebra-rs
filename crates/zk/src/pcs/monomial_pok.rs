//! Batched monomial-challenge proof of opening knowledge (Z7 support).
//!
//! An Ajtai commitment `m = A₀·h` is *binding* only for short `h`, so "I know
//! an opening of these commitments" is a statement about a **norm-bounded
//! witness in a linear relation** — exactly what a `Σ`-protocol for
//! `MSIS`-style relations proves. This module is Fig. 1 of Hwang–Seo–Song
//! (2024/306), the batched protocol `Π_Open` inherited from
//! Baum–Bootle–Cerulli–Del Pino–Groth–Lyubashevsky (2018/822), specialised to
//! the *non-hiding* commitment, i.e. with the `A₁·η` randomness and its
//! responses `τ` absent:
//!
//! ```text
//! 1:  for j < κ:  g_j ← U(Z_pⁿ),   gg_j = A₀·Ecd(g_j)         ──gg_j──▶
//! 2:                              c_{j,0} … c_{j,m−1} ← U(C)  ◀──c──
//! 3:  t_j = g_j + Σᵢ c_{j,i}·hᵢ                               ──t_j──▶
//! 4:        check ‖t_j‖₂ ≤ β_Open  and  A₀·t_j ?= gg_j + Σᵢ c_{j,i}·mᵢ
//! ```
//!
//! Three things make this shape worth its own module rather than an inline loop:
//!
//! * **The challenge set is `{1, X, …, X^{2d−1}}`**, not field elements or
//!   small-coefficient polynomials. A monomial is a *unit* of `R` with `ℓ₁`
//!   norm `1`, and its action is a signed permutation of the coefficients
//!   ([`rotate`]), so `‖Σᵢ cᵢhᵢ‖` never grows past `Σᵢ‖hᵢ‖`. That is the
//!   Benhamouda–Camenisch–Krenn–Lyubashevsky–Neven (2014/381) trick for making
//!   the response bound independent of the challenge, and it is why `κ` depends
//!   on `d` alone ([`rounds_for`] is `⌈λ/log₂(2d)⌉`, since `|C| = 2d`).
//! * **Batching**: one round proves knowledge of `m` openings at once under a
//!   *different* monomial per commitment, and the violations are reported per
//!   round ([`OpenViolation`]) so a scheme layer can attribute a bad proof to
//!   the equation it really broke.
//! * **Every product is an existing capability**: [`RingMatrixKey::matvec`] for
//!   the Ajtai map and [`BlockMat::contract_rows`] for the `Σᵢ cᵢ·(rowᵢ)` fold.
//!   This module adds the protocol shape and the norm gate, not a third matrix
//!   engine.
//!
//! # Why no `τ`, no `γ`, no coset sampler
//!
//! The hiding variant draws `ηᵢ ← D_{Z^d,σ₁}^{µ+ν}` per commitment, appends
//! `A₁ = [A₁′|I_µ]`, answers with `τ_j = γ_j + Σᵢ c_{j,i}ηᵢ` as well, and gets
//! simulatability from Hint-MLWE (Thm. 4) *instead of* rejection sampling —
//! with the masks coming from the randomized encoding `R.Ecd`. That is the one
//! paper step with no counterpart in this repo
//! ([`algebra::crypto::sampling::DiscreteGaussian`] is spherical over `Z`, not
//! over a coset of `P·Zᵈ`). Nothing here stands in for it: this is the
//! non-hiding protocol, and the omitted lines are recorded in
//! `examples/celpc.rs`.
//!
//! Layering: `foundation → pcs::digit_pack → pcs::monomial_pok`. The protocol
//! never looks at a message modulus; masks arrive already encoded.

use crate::foundation::fs::seed_stream;
use crate::pcs::digit_pack::uniform_below;
use crate::pcs::key::RingMatrixKey;
use crate::pcs::mixed::BlockMat;
use crate::pcs::projection::to_coeffs;
use crate::shortness::exact_l2::{squared_norm, ExactL2Error};
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::{CenteredRing, PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Why a protocol step refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum PokError {
    /// A proof component has the wrong length for the instance.
    WrongShape {
        /// Which component.
        part: &'static str,
        /// Length supplied.
        got: usize,
        /// Length the instance requires.
        expected: usize,
    },
    /// A ring vector is narrower or wider than the key's column count.
    KeyWidth {
        /// Which vector.
        part: &'static str,
        /// Length supplied.
        got: usize,
        /// `A₀.cols()`.
        expected: usize,
    },
    /// A norm bound could not be evaluated.
    Norm(ExactL2Error),
}

impl fmt::Display for PokError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PokError::WrongShape {
                part,
                got,
                expected,
            } => write!(f, "{part}: {got} elements against {expected}"),
            PokError::KeyWidth {
                part,
                got,
                expected,
            } => write!(
                f,
                "{part}: {got} ring elements against a key of {expected} columns"
            ),
            PokError::Norm(err) => write!(f, "norm gate: {err}"),
        }
    }
}

/// One of Fig. 1's two verifier gates, for the round that failed it.
///
/// Reported per round and without short-circuiting, so a scheme layer can
/// distinguish "round 3's relation failed" from "the proof was invalid".
///
/// Deliberately *not* `#[non_exhaustive]`: these two gates are the whole of
/// Fig. 1's check, and a scheme assembly should have to handle both.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpenViolation {
    /// Fig. 1 step 12: `A₀·t_j ≠ gg_j + Σᵢ c_{j,i}·mᵢ`.
    Linear {
        /// The round whose relation failed.
        round: usize,
    },
    /// Fig. 1 step 11: `‖t_j‖₂² > β²`.
    TooLong {
        /// The round whose response overshot the bound.
        round: usize,
    },
}

/// A batched opening proof: the mask commitments and the responses, indexed by
/// round (`mask_commitments[j].len() = µ`, `responses[j].len() = ℓ`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OpenProof<R: Ring, const D: usize> {
    /// `gg_j = A₀·g_j` — sent first, and what the challenges are bound to.
    pub mask_commitments: Vec<Vec<PolyRing<R, D>>>,
    /// `t_j = g_j + Σᵢ c_{j,i}·hᵢ`.
    pub responses: Vec<Vec<PolyRing<R, D>>>,
}

/// `Xᵏ` as a ring element for `k ∈ [0, 2d)`: one challenge from the set `C` of
/// Fig. 1.
///
/// `k` is taken `mod 2d`, which is exact because `X^{2d} = 1` in
/// `R = Z[X]/(Xᵈ+1)`; `Xᵏ = −X^{k−d}` once `k ≥ d`.
pub fn monomial<R: Ring, const D: usize>(k: usize) -> PolyRing<R, D> {
    let k = k % (2 * D);
    let mut coeffs = vec![R::ZERO; D];
    coeffs[k % D] = if k < D { R::ONE } else { R::ZERO - R::ONE };
    PolyRing::from_coefficients(coeffs)
}

/// `Xᵏ·a` for a monomial `k`: the signed rotation of `a`'s coefficients, one
/// minus per crossing of `Xᵈ = −1` plus a global minus when `k ≥ d`.
///
/// Cost `O(D)` against the schoolbook ring product's `O(D²)`, and *identical* to
/// it. The rotation is a permutation up to sign, which is the property
/// `β_Open` leans on.
pub fn rotate<R: Ring, const D: usize>(a: &PolyRing<R, D>, k: usize) -> PolyRing<R, D> {
    let k = k % (2 * D);
    let shift = k % D;
    let mut out = vec![R::ZERO; D];
    for (i, &c) in to_coeffs::<R, D>(core::slice::from_ref(a))
        .iter()
        .enumerate()
    {
        let target = i + shift;
        if target >= D {
            out[target - D] = R::ZERO - c;
        } else {
            out[target] = c;
        }
    }
    if k >= D {
        for o in out.iter_mut() {
            *o = R::ZERO - *o;
        }
    }
    PolyRing::from_coefficients(out)
}

/// `κ = ⌈λ / log₂(2d)⌉`, Fig. 1's repetition count: one round over a
/// `2d`-element challenge set buys `log₂(2d)` bits of soundness.
///
/// `⌊log₂(2d)⌋` is used in the denominator, so a non-power-of-two challenge set
/// rounds `κ` *up* rather than silently buying a smaller soundness error.
pub fn rounds_for(dimension: usize, security: usize) -> usize {
    let bits = (2 * dimension).ilog2().max(1) as usize;
    security.div_ceil(bits)
}

/// The `κ × msgs` exponents of Fig. 1's challenge table, i.e. the raw draws
/// `k_{j,i} ← U([0, 2d))` that index `C = {1, X, …, X^{2d−1}}`.
///
/// Kept separate from [`challenges`] because the *reason* the response bound
/// `β_Open` does not depend on the challenges is a property of the exponents:
/// each one acts as [`rotate`], a signed permutation. The test
/// `the_fold_is_a_sum_of_rotations` asserts exactly that against the ring
/// product the protocol actually uses.
pub fn challenge_exponents<const D: usize>(
    label: &[u8],
    seed: &[u8; 32],
    rounds: usize,
    msgs: usize,
) -> Vec<Vec<usize>> {
    let mut xof = seed_stream::<Shake256Xof>(label, seed);
    (0..rounds)
        .map(|_| {
            (0..msgs)
                .map(|_| usize::try_from(uniform_below(&mut xof, 2 * D as u64)).expect("k < 2d"))
                .collect()
        })
        .collect()
}

/// The `κ × msgs` monomial table `c_{j,i} ← U(C)` of Fig. 1 step 6, expanded
/// from one Fiat–Shamir seed in a labeled stream.
pub fn challenges<R: Ring, const D: usize>(
    label: &[u8],
    seed: &[u8; 32],
    rounds: usize,
    msgs: usize,
) -> Vec<Vec<PolyRing<R, D>>> {
    challenge_exponents::<D>(label, seed, rounds, msgs)
        .into_iter()
        .map(|row| row.into_iter().map(|k| monomial::<R, D>(k)).collect())
        .collect()
}

/// `‖⃗v‖₂²` over the coefficient flattening of a ring vector — the shape every
/// CELPC norm gate is written against (`‖(t ‖ τ)‖₂ ≤ β_Open`,
/// `‖(2·hhᵢ ‖ 2·ηᵢ)‖₂ ≤ 2d·β`).
///
/// # Errors
/// [`PokError::Norm`] if the accumulation overflows `u128`.
pub fn norm_sq<R: CenteredRing, const D: usize>(v: &[PolyRing<R, D>]) -> Result<u128, PokError> {
    squared_norm(&to_coeffs::<R, D>(v)).map_err(PokError::Norm)
}

/// `c·⃗v` for an integer scalar `c` read in the ring: the doubling `PC.Open`
/// gates its norm checks on.
pub fn scale<R: Ring, const D: usize>(v: &[PolyRing<R, D>], c: R) -> Vec<PolyRing<R, D>> {
    v.iter()
        .map(|elt| {
            PolyRing::from_coefficients(
                to_coeffs::<R, D>(core::slice::from_ref(elt))
                    .iter()
                    .map(|x| *x * c)
                    .collect(),
            )
        })
        .collect()
}

/// `Σᵢ cᵢ·⃗vᵢ` — the row fold Fig. 1 steps 8/12 and `PC.Eval` step 1 all need,
/// delegated to [`BlockMat::contract_rows`] so the contraction lives in one
/// place.
///
/// # Errors
/// [`PokError::WrongShape`] unless the rows are uniform and `c` has exactly one
/// weight per row.
pub fn fold_rows<R: Ring, const D: usize>(
    c: &[PolyRing<R, D>],
    rows: &[&[PolyRing<R, D>]],
) -> Result<Vec<PolyRing<R, D>>, PokError> {
    let width = rows.first().map_or(0, |r| r.len());
    let uneven = rows.iter().any(|r| r.len() != width);
    if uneven || rows.is_empty() {
        return Err(PokError::WrongShape {
            part: "fold rows",
            got: rows.len(),
            expected: if rows.is_empty() { 1 } else { width },
        });
    }
    let mat = BlockMat::from_rows(rows).map_err(|_| PokError::WrongShape {
        part: "fold rows",
        got: width,
        expected: rows.len() * width,
    })?;
    mat.contract_rows(c).map_err(|_| PokError::WrongShape {
        part: "fold weights",
        got: c.len(),
        expected: rows.len(),
    })
}

/// The prover's first message: `gg_j = A₀·g_j` for every round.
///
/// # Errors
/// [`PokError::KeyWidth`] if a mask is not `A₀.cols()` long.
pub fn commit_masks<R: Ring, const D: usize>(
    key: &RingMatrixKey<R, D>,
    masks: &[&[PolyRing<R, D>]],
) -> Result<Vec<Vec<PolyRing<R, D>>>, PokError> {
    masks
        .iter()
        .map(|g| {
            key.matvec(g).map_err(|e| PokError::KeyWidth {
                part: "mask",
                got: e.got,
                expected: e.expected,
            })
        })
        .collect()
}

/// The prover's whole message: the mask commitments plus
/// `t_j = g_j + Σᵢ c_{j,i}·hᵢ` (Fig. 1 steps 5 and 8).
///
/// # Errors
/// [`PokError::WrongShape`] when the round counts or witness widths disagree —
/// a disagreement that a `zip` would otherwise hide — and [`PokError::KeyWidth`]
/// as in [`commit_masks`].
pub fn prove_open<R: Ring, const D: usize>(
    key: &RingMatrixKey<R, D>,
    masks: &[&[PolyRing<R, D>]],
    witnesses: &[&[PolyRing<R, D>]],
    challenges: &[Vec<PolyRing<R, D>>],
) -> Result<OpenProof<R, D>, PokError> {
    if witnesses.is_empty() {
        return Err(PokError::WrongShape {
            part: "witnesses",
            got: 0,
            expected: 1,
        });
    }
    let width = witnesses[0].len();
    if width != key.cols() || witnesses.iter().any(|w| w.len() != width) {
        return Err(PokError::KeyWidth {
            part: "witness",
            got: witnesses.iter().map(|w| w.len()).min().unwrap_or(0),
            expected: key.cols(),
        });
    }
    if challenges.len() != masks.len() {
        return Err(PokError::WrongShape {
            part: "round count",
            got: challenges.len(),
            expected: masks.len(),
        });
    }
    let mask_commitments = commit_masks(key, masks)?;
    let responses = challenges
        .iter()
        .zip(masks.iter())
        .map(|(c_j, g_j)| {
            Ok(fold_rows(c_j, witnesses)?
                .iter()
                .zip(g_j.iter())
                .map(|(f, m)| f.clone() + m.clone())
                .collect())
        })
        .collect::<Result<Vec<_>, PokError>>()?;
    Ok(OpenProof {
        mask_commitments,
        responses,
    })
}

/// Fig. 1 steps 11–12 for **every** round, without short-circuiting.
///
/// `beta_sq` is `β_Open²`; `commitments[i]` is the `i`-th commitment
/// `mᵢ = A₀·hᵢ`.
///
/// # Errors
/// [`PokError`] on a shape mismatch — a malformed proof, kept distinct from a
/// false statement ([`OpenViolation`]).
pub fn open_violations<R: CenteredRing, const D: usize>(
    key: &RingMatrixKey<R, D>,
    commitments: &[&[PolyRing<R, D>]],
    proof: &OpenProof<R, D>,
    challenges: &[Vec<PolyRing<R, D>>],
    beta_sq: u128,
) -> Result<Vec<OpenViolation>, PokError> {
    let msgs = commitments.len();
    if proof.mask_commitments.len() != proof.responses.len() {
        return Err(PokError::WrongShape {
            part: "mask/response round count",
            got: proof.mask_commitments.len(),
            expected: proof.responses.len(),
        });
    }
    if challenges.len() != proof.responses.len() {
        return Err(PokError::WrongShape {
            part: "challenge round count",
            got: challenges.len(),
            expected: proof.responses.len(),
        });
    }
    for c in commitments {
        if c.len() != key.rows() {
            return Err(PokError::WrongShape {
                part: "commitment",
                got: c.len(),
                expected: key.rows(),
            });
        }
    }
    for (j, row) in proof.responses.iter().enumerate() {
        if row.len() != key.cols() {
            return Err(PokError::KeyWidth {
                part: "response",
                got: row.len(),
                expected: key.cols(),
            });
        }
        if proof.mask_commitments[j].len() != key.rows() {
            return Err(PokError::WrongShape {
                part: "mask commitment",
                got: proof.mask_commitments[j].len(),
                expected: key.rows(),
            });
        }
        if challenges[j].len() != msgs {
            return Err(PokError::WrongShape {
                part: "challenges per round",
                got: challenges[j].len(),
                expected: msgs,
            });
        }
    }
    let mut bad: Vec<OpenViolation> = Vec::new();
    for (j, t) in proof.responses.iter().enumerate() {
        let lhs = key.matvec(t).map_err(|e| PokError::KeyWidth {
            part: "response",
            got: e.got,
            expected: e.expected,
        })?;
        let rhs_fold = fold_rows(&challenges[j], commitments)?;
        let rhs: Vec<PolyRing<R, D>> = rhs_fold
            .iter()
            .zip(proof.mask_commitments[j].iter())
            .map(|(f, g)| f.clone() + g.clone())
            .collect();
        if lhs != rhs {
            bad.push(OpenViolation::Linear { round: j });
        }
        if norm_sq(t)? > beta_sq {
            bad.push(OpenViolation::TooLong { round: j });
        }
    }
    Ok(bad)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::foundation::sampling::from_centered;
    use algebra::ring::zq::Zq;

    /// The house non-NTT prime (`2³² − 99 ≡ 5 (mod 8)`, no NTT past degree 2).
    type Q5 = Zq<4294967197>;
    const D: usize = 64;
    type Elt = PolyRing<Q5, D>;

    const MU: usize = 2;
    const ELL: usize = 3;
    const MSGS: usize = 4;
    const KAPPA: usize = 6;
    /// Every coefficient of a `small()` element is inside `[-50, 50]`.
    const COEF: u64 = 50;

    fn zero() -> Elt {
        Elt::from_coefficients(vec![Q5::ZERO; D])
    }

    fn one() -> Elt {
        Elt::from_coefficients(vec![Q5::ONE])
    }

    fn small(seed: u64, len: usize) -> Vec<Elt> {
        (0..len)
            .map(|i| {
                Elt::from_coefficients(
                    (0..D)
                        .map(|k| {
                            from_centered::<Q5>(
                                ((seed * 31 + i as u64 * 7 + k as u64) % (2 * COEF as u64)) as i64
                                    - COEF as i64,
                            )
                        })
                        .collect(),
                )
            })
            .collect()
    }

    /// An honest instance of the protocol at the toy shape: `key · witness =
    /// commitment`, masks derived independently, one challenge table.
    struct Fixture {
        key: RingMatrixKey<Q5, D>,
        witnesses: Vec<Vec<Elt>>,
        commitments: Vec<Vec<Elt>>,
        masks: Vec<Vec<Elt>>,
        table: Vec<Vec<Elt>>,
    }

    fn fixture() -> Fixture {
        let key = RingMatrixKey::<Q5, D>::setup(b"pok", &[7u8; 32], MU, ELL);
        let witnesses: Vec<Vec<Elt>> = (0..MSGS).map(|i| small(i as u64 + 1, ELL)).collect();
        let refs: Vec<&[Elt]> = witnesses.iter().map(|v| v.as_slice()).collect();
        let commitments: Vec<Vec<Elt>> = refs.iter().map(|w| key.matvec(w).expect("ok")).collect();
        let masks: Vec<Vec<Elt>> = (0..KAPPA).map(|j| small(j as u64 + 40, ELL)).collect();
        let table = challenges::<Q5, D>(b"c", &[9u8; 32], KAPPA, MSGS);
        Fixture {
            key,
            witnesses,
            commitments,
            masks,
            table,
        }
    }

    impl Fixture {
        fn witness_refs(&self) -> Vec<&[Elt]> {
            self.witnesses.iter().map(|v| v.as_slice()).collect()
        }
        fn commitment_refs(&self) -> Vec<&[Elt]> {
            self.commitments.iter().map(|v| v.as_slice()).collect()
        }
        fn mask_refs(&self) -> Vec<&[Elt]> {
            self.masks.iter().map(|v| v.as_slice()).collect()
        }
    }

    /// Fig. 1's completeness argument with monomial challenges: each
    /// `c·h` is a rotation of `h`, so `‖t_j‖∞ ≤ (m+1)·max ‖h‖∞` and the honest
    /// proof sits under `β² = ℓd·((m+1)·COEF)²` — with room to spare, which is
    /// what makes the gate non-vacuous.
    fn honest_beta_sq() -> u128 {
        u128::from((ELL * D) as u64)
            * u128::from((MSGS + 1) as u64 * COEF)
            * u128::from((MSGS + 1) as u64 * COEF)
    }

    #[test]
    fn monomial_challenges_are_the_units_the_paper_claims() {
        for k in 0..2 * D {
            let c = monomial::<Q5, D>(k);
            let l1: u64 = to_coeffs::<Q5, D>(&[c.clone()])
                .iter()
                .map(|x| x.abs_infinity())
                .sum();
            assert_eq!(l1, 1, "‖X^{k}‖₁ must be 1");
            let inv = monomial::<Q5, D>((2 * D - k) % (2 * D));
            assert_eq!(
                c * inv,
                one(),
                "Xᵏ·X⁻ᵏ ≠ 1 at k = {k}: a non-unit challenge would make the \
                 relation check vacuous"
            );
        }
        assert_eq!(monomial::<Q5, D>(2 * D), monomial::<Q5, D>(0));
    }

    #[test]
    fn rotate_matches_the_ring_product() {
        let a = small(3, 1).remove(0);
        for k in 0..2 * D {
            assert_eq!(
                rotate(&a, k),
                a.clone() * monomial::<Q5, D>(k),
                "the O(d) rotation disagrees with the ring product at k = {k}"
            );
        }
    }

    #[test]
    fn rotate_preserves_norms() {
        let v = small(5, 4);
        let base = norm_sq(&v).expect("ok");
        for k in [0usize, 1, 17, D - 1, D, D + 5, 2 * D - 1] {
            let rotated: Vec<Elt> = v.iter().map(|x| rotate(x, k)).collect();
            assert_eq!(norm_sq(&rotated).expect("ok"), base, "k = {k}");
        }
    }

    /// Why `β_Open` may not mention the challenges: the fold Fig. 1 step 8
    /// performs is a sum of **signed permutations** of the witnesses, so its
    /// coefficient-wise magnitude is bounded by `Σᵢ‖hᵢ‖∞` whatever is drawn.
    /// Asserted against the ring product the protocol really runs, so a
    /// challenge that stopped being a monomial — a small-polynomial set, say —
    /// would break this test rather than only the security proof.
    #[test]
    fn the_fold_is_a_sum_of_rotations() {
        let f = fixture();
        let exps = challenge_exponents::<D>(b"c", &[9u8; 32], KAPPA, MSGS);
        assert_eq!(exps.len(), KAPPA);
        assert!(
            exps.iter().flatten().all(|&k| k < 2 * D),
            "an exponent outside [0, 2d) is outside C"
        );
        assert!(
            exps[0][0] != exps[0][1] || exps[0][0] != exps[1][0],
            "the table must not be a constant matrix, or the fold below is vacuous"
        );
        for (j, row) in f.table.iter().enumerate() {
            for (i, c) in row.iter().enumerate() {
                assert_eq!(*c, monomial::<Q5, D>(exps[j][i]), "table [{j}][{i}]");
            }
            let mut want = vec![zero(); ELL];
            for (i, w) in f.witnesses.iter().enumerate() {
                for (o, v) in want.iter_mut().zip(w.iter()) {
                    *o = o.clone() + rotate(v, exps[j][i]);
                }
            }
            assert_eq!(
                fold_rows(row, &f.witness_refs()).expect("shapes"),
                want,
                "round {j}: the row fold is not the sum of rotations"
            );
        }
    }

    /// Does `rounds` repetitions over a `2·dimension`-element challenge set
    /// reach the `2^-security` error target? Decided by exact integer
    /// exponentiation with saturation, so this is independent of whatever
    /// logarithm [`rounds_for`] uses internally.
    fn buys_security(dimension: usize, rounds: usize, security: usize) -> bool {
        let base = (2 * dimension) as u128;
        // λ = 128 is the top of `u128`, so "reached 2^128" is exactly "the
        // product overflowed", which the checked multiply below reports.
        let target: u128 = if security >= 127 {
            u128::MAX
        } else {
            1u128 << security
        };
        let mut acc: u128 = 1;
        for _ in 0..rounds {
            match acc.checked_mul(base) {
                Some(v) => acc = v,
                None => return true,
            }
            if acc >= target {
                return true;
            }
        }
        acc >= target
    }

    #[test]
    fn rounds_for_matches_the_repetition_formula() {
        assert_eq!(rounds_for(D, 128), 19, "κ = ⌈128/log₂128⌉");
        assert_eq!(rounds_for(D, 7), 1);
        // κ = ⌈128/9⌉ = 15 at d = 256. The 9 this test used to assert is
        // log₂(2d) itself — the bits one round buys, not the round count.
        assert_eq!(rounds_for(256, 128), 15);
        assert_eq!(rounds_for(4, 128), 43, "⌈128/3⌉");
        // What the number is *for*: it buys the error target, and one round
        // fewer does not. Checked by integer exponentiation, not by re-running
        // the formula, so the two cannot drift together.
        for d in [D, 256usize, 4] {
            let kappa = rounds_for(d, 128);
            assert!(
                buys_security(d, kappa, 128),
                "κ = {kappa} rounds at d = {d} does not reach 2⁻¹²⁸"
            );
            assert!(
                !buys_security(d, kappa - 1, 128),
                "κ = {kappa} is not minimal at d = {d}: {} rounds already buy it",
                kappa - 1
            );
        }
        // A non-power-of-two challenge set: the denominator is ⌊log₂(2d)⌋, so
        // κ is charged *more* rounds than ⌈128/log₂126⌉ = 19. That is
        // deliberate — under-buying soundness is the failure this guards — and
        // pinning the value is what stops a future "simplification" to real
        // logarithms from quietly cutting CELPC's round count.
        assert_eq!(rounds_for(63, 128), 22);
        assert!(rounds_for(63, 128) > 19, "conservative against the real log");
        assert!(buys_security(63, rounds_for(63, 128), 128));
    }

    #[test]
    fn challenges_are_bound_to_the_seed_and_stay_in_c() {
        let table = challenges::<Q5, D>(b"c", &[1u8; 32], 4, 3);
        assert_eq!(table.len(), 4);
        assert_eq!(table, challenges::<Q5, D>(b"c", &[1u8; 32], 4, 3));
        assert_ne!(table, challenges::<Q5, D>(b"c", &[2u8; 32], 4, 3), "seed");
        assert_ne!(table, challenges::<Q5, D>(b"d", &[1u8; 32], 4, 3), "label");
        for row in &table {
            assert_eq!(row.len(), 3);
            for c in row {
                let l1: u64 = to_coeffs::<Q5, D>(&[c.clone()])
                    .iter()
                    .map(|x| x.abs_infinity())
                    .sum();
                assert_eq!(l1, 1, "a challenge left the monomial set");
            }
        }
    }

    #[test]
    fn honest_open_proves_and_verifies() {
        let f = fixture();
        let proof =
            prove_open(&f.key, &f.mask_refs(), &f.witness_refs(), &f.table).expect("shapes");
        assert_eq!(proof.responses.len(), KAPPA);
        assert_eq!(proof.mask_commitments.len(), KAPPA);
        assert!(
            !proof
                .responses
                .iter()
                .any(|r| r.iter().any(|e| *e == zero())),
            "a zero response would make the checks below trivially satisfiable"
        );
        assert_eq!(
            open_violations(
                &f.key,
                &f.commitment_refs(),
                &proof,
                &f.table,
                honest_beta_sq()
            )
            .expect("well-shaped"),
            Vec::new(),
            "honest proof rejected"
        );
    }

    #[test]
    fn a_wrong_response_is_the_linear_relation_of_its_own_round() {
        let f = fixture();
        let mut proof =
            prove_open(&f.key, &f.mask_refs(), &f.witness_refs(), &f.table).expect("shapes");
        proof.responses[2][0] = proof.responses[2][0].clone() + one();
        assert_eq!(
            open_violations(
                &f.key,
                &f.commitment_refs(),
                &proof,
                &f.table,
                honest_beta_sq()
            )
            .expect("well-shaped"),
            vec![OpenViolation::Linear { round: 2 }],
            "only round 2's relation may fail"
        );
    }

    #[test]
    fn a_tampered_commitment_fails_every_rounds_relation() {
        // The batched form must not hide a bad commitment behind the other
        // `m−1` rows: since each round uses all `m` challenges, tampering with
        // one commitment breaks all κ relations.
        let f = fixture();
        let proof =
            prove_open(&f.key, &f.mask_refs(), &f.witness_refs(), &f.table).expect("shapes");
        let mut bad = f.commitments.clone();
        bad[1][0] = bad[1][0].clone() + one();
        let brefs: Vec<&[Elt]> = bad.iter().map(|v| v.as_slice()).collect();
        assert_eq!(
            open_violations(&f.key, &brefs, &proof, &f.table, honest_beta_sq())
                .expect("well-shaped"),
            (0..KAPPA)
                .map(|round| OpenViolation::Linear { round })
                .collect::<Vec<_>>(),
        );
    }

    #[test]
    fn the_norm_gate_is_independent_of_the_relation() {
        // An oversized mask with an honestly derived `gg_j` satisfies the
        // relation for every round and trips `TooLong` alone; widen β and the
        // same proof passes, so the two gates are not redundant.
        let f = fixture();
        let fat: Vec<Vec<Elt>> = (0..KAPPA)
            .map(|_| {
                (0..ELL)
                    .map(|i| Elt::from_coefficients(vec![Q5::from(i as u64 + 1); D]))
                    .collect()
            })
            .collect();
        let frefs: Vec<&[Elt]> = fat.iter().map(|v| v.as_slice()).collect();
        let proof = prove_open(&f.key, &frefs, &f.witness_refs(), &f.table).expect("shapes");
        let viol = open_violations(&f.key, &f.commitment_refs(), &proof, &f.table, 1_000)
            .expect("well-shaped");
        assert_eq!(
            viol,
            (0..KAPPA)
                .map(|round| OpenViolation::TooLong { round })
                .collect::<Vec<_>>()
        );
        assert_eq!(
            open_violations(&f.key, &f.commitment_refs(), &proof, &f.table, u128::MAX)
                .expect("well-shaped"),
            Vec::new(),
            "the relation must still hold, so TooLong really is only the bound"
        );
    }

    #[test]
    fn malformed_shapes_are_errors_not_violations() {
        let f = fixture();
        let proof = OpenProof {
            mask_commitments: vec![vec![zero(); MU]; KAPPA],
            responses: vec![vec![zero(); ELL - 1]; KAPPA],
        };
        assert_eq!(
            open_violations(&f.key, &f.commitment_refs(), &proof, &f.table, u128::MAX),
            Err(PokError::KeyWidth {
                part: "response",
                got: ELL - 1,
                expected: ELL
            })
        );
        // A fold whose weights and rows disagree is refused, not truncated.
        let rows = f.witness_refs();
        assert_eq!(
            fold_rows(&f.table[0][..MSGS - 1], &rows[..MSGS]),
            Err(PokError::WrongShape {
                part: "fold weights",
                got: MSGS - 1,
                expected: MSGS
            })
        );
        // And a witness of the wrong width never reaches the key.
        let narrow = small(1, ELL - 1);
        assert_eq!(
            prove_open(&f.key, &f.mask_refs(), &[narrow.as_slice()][..], &f.table),
            Err(PokError::KeyWidth {
                part: "witness",
                got: ELL - 1,
                expected: ELL
            })
        );
        // Mismatched round counts cannot be silently zipped away either.
        assert_eq!(
            prove_open(
                &f.key,
                &f.mask_refs()[..KAPPA - 1],
                &f.witness_refs(),
                &f.table
            ),
            Err(PokError::WrongShape {
                part: "round count",
                got: KAPPA,
                expected: KAPPA - 1
            })
        );
    }

    #[test]
    fn scale_is_the_integer_multiple_the_open_gate_expects() {
        let v = small(2, 3);
        let two = Q5::ONE + Q5::ONE;
        assert_eq!(
            norm_sq(&scale(&v, two)).expect("ok"),
            4 * norm_sq(&v).expect("ok")
        );
        assert_eq!(scale(&v, Q5::ONE), v);
        assert_eq!(
            scale(&v, Q5::ZERO),
            vec![zero(); v.len()],
            "scaling by zero must collapse the vector"
        );
    }
}
