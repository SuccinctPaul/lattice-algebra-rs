//! Multi-assertion batched sumcheck (Z3, the Π_batch shape).
//!
//! Proves `K` sumcheck claims over the same `{0,1}^G` hypercube with **one**
//! round structure, in the shape LatticeFold's `Π_batch` uses to merge
//! linearization, multilinear-evaluation and range checks (survey §1.3):
//!
//! 1. the challenger derives a batch weight `γ` *after* the caller has
//!    absorbed the claimed values (so `γ` binds the statement);
//! 2. every claim is folded with a γ-power weight, optionally under its
//!    eq-polynomial `eq(βᵢ, ·)` (the per-instance binding weight);
//! 3. one plain sumcheck runs on the combined table, and the single final
//!    evaluation ties the whole batch back to public data.
//!
//! # Soundness
//!
//! Beyond the single-claim round bound (see the [`super`] module docs), the
//! batch adds one Schwartz–Zippel factor: a prover whose claim set does not
//! all hold must satisfy `Σᵢ γⁱ·(false claim)` against round-consistency,
//! which succeeds with probability `≤ K/|R|` over the γ draw.
//!
//! In this crate's transparent-table mode the verifier holds the tables and
//! re-derives the combined table with [`combined_table`] to tie the final
//! evaluation; a committed deployment replaces the tables by committed
//! openings exactly as LatticeFold does — the round structure is unchanged.

use super::{prove, verify, RoundChallenger, SumcheckProof};
use algebra::ring::MatrixElement;
use alloc::{vec, vec::Vec};

/// One batched assertion: table `Tᵢ` with claimed sum
/// `vᵢ = Σ_x wᵢ(x)·Tᵢ(x)`, where the position weight `wᵢ` is the all-ones
/// tensor or the eq-polynomial `eq(βᵢ, ·)` for the optional point `βᵢ`.
#[derive(Debug, Clone)]
pub struct BatchClaim<'a, R, const G: usize> {
    /// Truth table over `{0,1}^G` (`2^G` entries).
    pub table: &'a [R],
    /// Optional eq-polynomial point: the claim is `⟨eq(βᵢ, ·), Tᵢ⟩` instead
    /// of the plain sum.
    pub eq_point: Option<&'a [R; G]>,
    /// The claimed (weighted) sum.
    pub claimed: R,
}

/// A completed batch: the γ-power batch weight and the single combined
/// sumcheck proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BatchedProof<R: MatrixElement, const G: usize> {
    /// The batch weight `γ` (bound to the absorbed claims).
    pub gamma: R,
    /// The one combined sumcheck run.
    pub proof: SumcheckProof<R, G>,
}

/// The position weights `w(x) = eq(β, x)` over the whole hypercube (the
/// all-ones table when `β` is `None`).
pub fn eq_weights<R, const G: usize>(eq_point: Option<&[R; G]>) -> Vec<R>
where
    R: MatrixElement + Clone,
{
    match eq_point {
        None => vec![R::one(); 1 << G],
        Some(beta) => {
            let mut out = Vec::with_capacity(1 << G);
            for idx in 0..1 << G {
                let mut bits = [false; G];
                for (g, bit) in bits.iter_mut().enumerate() {
                    *bit = (idx >> g) & 1 == 1;
                }
                out.push(super::eq_tensor(beta, &bits));
            }
            out
        }
    }
}

/// Builds the combined table `T* = Σᵢ γⁱ·wᵢ·Tᵢ` (prover and verifier use
/// the same function; in transparent mode the verifier recomputes it to tie
/// the final evaluation back).
///
/// # Panics
/// If any claim's table length is not `2^G`, or `claims` is empty.
pub fn combined_table<R, const G: usize>(claims: &[BatchClaim<'_, R, G>], gamma: &R) -> Vec<R>
where
    R: MatrixElement + Clone + core::ops::AddAssign + core::ops::MulAssign,
{
    assert!(!claims.is_empty(), "a batch needs at least one claim");
    let mut out = vec![R::zero(); 1 << G];
    let mut weight = R::one();
    for claim in claims {
        let weights = eq_weights::<R, G>(claim.eq_point);
        for (dst, (t, w)) in out.iter_mut().zip(claim.table.iter().zip(weights.iter())) {
            *dst += weight.clone() * w.clone() * t.clone();
        }
        weight *= gamma.clone();
    }
    out
}

/// The combined claimed sum `v* = Σᵢ γⁱ·vᵢ` from the per-claim values.
///
/// # Panics
/// If `claims` is empty.
pub fn combined_claim<R, const G: usize>(claims: &[BatchClaim<'_, R, G>], gamma: &R) -> R
where
    R: MatrixElement + Clone + core::ops::AddAssign + core::ops::MulAssign,
{
    assert!(!claims.is_empty(), "a batch needs at least one claim");
    let mut acc = R::zero();
    let mut weight = R::one();
    for claim in claims {
        acc += weight.clone() * claim.claimed.clone();
        weight *= gamma.clone();
    }
    acc
}

/// Derives the batch weight from the challenger: `γ = round_challenge(0, 0)`
/// — the round-message absorb inside the challenger is what binds `γ` to
/// everything the caller absorbed (the claims; a commitment in a committed
/// deployment).
fn batch_gamma<R>(challenger: &mut dyn RoundChallenger<R>) -> R
where
    R: MatrixElement,
{
    challenger.round_challenge(&R::zero(), &R::zero())
}

/// Prover: folds the claims with γ-power weights and runs one sumcheck.
///
/// The challenger must already carry the public statement (absorb the
/// claimed values — and any commitment — before calling; see the module
/// docs). The claims' honest sums are the `claimed` values.
///
/// # Panics
/// If any table length is not `2^G`.
pub fn prove_batched<R, const G: usize>(
    claims: &[BatchClaim<'_, R, G>],
    challenger: &mut dyn RoundChallenger<R>,
) -> BatchedProof<R, G>
where
    R: MatrixElement + Clone + Send + Sync + core::ops::AddAssign + core::ops::MulAssign,
{
    let gamma = batch_gamma(challenger);
    let table = combined_table(claims, &gamma);
    let proof = prove::<R, G>(&table, challenger);
    BatchedProof { gamma, proof }
}

/// Verifier: re-derives `γ`, folds the claims and runs the single round
/// loop. Returns the challenge point and the combined final evaluation so
/// the application ties the batch back to public data (transparent mode:
/// recompute [`combined_table`] and evaluate it at the challenge point).
///
/// # Errors
/// `None` on any round-inconsistency or final-evaluation mismatch.
pub fn verify_batched<R, const G: usize>(
    proof: &BatchedProof<R, G>,
    claimed: &[R],
    challenger: &mut dyn RoundChallenger<R>,
) -> Option<(Vec<R>, R)>
where
    R: MatrixElement + Clone + core::ops::AddAssign + core::ops::MulAssign,
{
    // reconstruct the claim list as (claimed, no eq) pairs — the eq points
    // only enter through the combined table, whose fold the round loop
    // checks against `v*`; the claimed folding here mirrors combined_claim
    // for the claims the verifier knows.
    debug_assert!(!claimed.is_empty());
    let gamma = batch_gamma(challenger);
    let mut acc = R::zero();
    let mut weight = R::one();
    for v in claimed {
        acc += weight.clone() * v.clone();
        weight *= gamma.clone();
    }
    let (challenges, final_eval) = verify::<R, G>(&proof.proof, acc, challenger)?;
    Some((challenges, final_eval))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sumcheck::FsChallenger;
    use algebra::crypto::xof::Shake128Xof;
    use algebra::ring::zq::Zq;

    type Rq = Zq<8380417>;
    const G: usize = 6;

    fn test_table(seed: u64) -> Vec<Rq> {
        (0..1 << G)
            .map(|i| Rq::from((seed * 100 + i as u64 * 7) % 101))
            .collect()
    }

    fn plain_claims(tables: &[Vec<Rq>]) -> Vec<BatchClaim<'_, Rq, G>> {
        tables
            .iter()
            .map(|t| BatchClaim {
                table: t,
                eq_point: None,
                claimed: t.iter().fold(Rq::zero(), |a, b| a + *b),
            })
            .collect()
    }

    #[test]
    fn honest_batch_verifies_with_one_round_structure() {
        let tables = [test_table(1), test_table(2), test_table(3)];
        let claims = plain_claims(&tables);

        let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"batch-honest");
        ch.absorb(b"claims", &[1, 2, 3]); // statement binding
        let proof = prove_batched::<Rq, G>(&claims, &mut ch);

        let claimed: Vec<Rq> = claims.iter().map(|c| c.claimed).collect();
        let mut chv = FsChallenger::<Shake128Xof, Rq>::new(b"batch-honest");
        chv.absorb(b"claims", &[1, 2, 3]);
        let (challenges, final_eval) =
            verify_batched::<Rq, G>(&proof, &claimed, &mut chv).expect("honest batch");
        assert_eq!(challenges.len(), G);

        // the single final evaluation is the combined table at the point
        // (the sumcheck folds variable g with the round-g challenge,
        // splitting the table on bit G−1−g — see the contract test)
        let combined = combined_table(&claims, &proof.gamma);
        let mut point_eval = Rq::zero();
        for (idx, t) in combined.iter().enumerate() {
            let mut w = Rq::one();
            for (g, r) in challenges.iter().enumerate() {
                let bit = (idx >> (G - 1 - g)) & 1 == 1;
                w *= if bit { *r } else { Rq::one() - *r };
            }
            point_eval += w * *t;
        }
        assert_eq!(final_eval, point_eval);
    }

    #[test]
    fn eq_point_claims_bind_per_instance() {
        // eq(β)-weighted claims: the claimed value is ⟨eq(β), T⟩
        let beta: [Rq; G] = core::array::from_fn(|i| Rq::from(3 + i as u64));
        let table = test_table(5);
        let claimed: Rq = (0..1 << G)
            .map(|idx| {
                let mut bits = [false; G];
                for (g, bit) in bits.iter_mut().enumerate() {
                    *bit = (idx >> g) & 1 == 1;
                }
                super::super::eq_tensor(&beta, &bits) * table[idx]
            })
            .fold(Rq::zero(), |a, b| a + b);
        let claims = [BatchClaim {
            table: &table,
            eq_point: Some(&beta),
            claimed,
        }];

        let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"batch-eq");
        let proof = prove_batched::<Rq, G>(&claims, &mut ch);
        let mut chv = FsChallenger::<Shake128Xof, Rq>::new(b"batch-eq");
        assert!(verify_batched::<Rq, G>(&proof, &[claimed], &mut chv).is_some());

        // a shifted claimed value breaks the round consistency
        let mut chv = FsChallenger::<Shake128Xof, Rq>::new(b"batch-eq");
        assert!(verify_batched::<Rq, G>(&proof, &[claimed + Rq::from(1)], &mut chv).is_none());
    }

    #[test]
    fn forged_single_claim_breaks_the_batch() {
        // An inflated TABLE breaks the verifier's folded v* at round 1.
        let tables = [test_table(1), test_table(2)];
        let honest = plain_claims(&tables);
        let mut fake_table = tables[1].clone();
        fake_table[3] += Rq::from(7);
        let fake = [
            BatchClaim {
                table: &tables[0],
                eq_point: None,
                claimed: honest[0].claimed,
            },
            BatchClaim {
                table: &fake_table,
                eq_point: None,
                claimed: honest[1].claimed,
            },
        ];

        let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"batch-forge");
        ch.absorb(b"claims", &[9]);
        let proof = prove_batched::<Rq, G>(&fake, &mut ch);

        let claimed: Vec<Rq> = honest.iter().map(|c| c.claimed).collect();
        let mut chv = FsChallenger::<Shake128Xof, Rq>::new(b"batch-forge");
        chv.absorb(b"claims", &[9]);
        assert!(verify_batched::<Rq, G>(&proof, &claimed, &mut chv).is_none());

        // The committed-claim forger goes further: it proves the fake table
        // under the INFLATED statement (self-consistent round loop). The
        // transparent-mode tie-back catches it — the final evaluation does
        // not match the honest combined table at the challenge point.
        let inflated = [
            BatchClaim {
                table: &tables[0],
                eq_point: None,
                claimed: honest[0].claimed,
            },
            BatchClaim {
                table: &fake_table,
                eq_point: None,
                claimed: honest[1].claimed + Rq::from(7),
            },
        ];
        let mut ch2 = FsChallenger::<Shake128Xof, Rq>::new(b"batch-forge");
        ch2.absorb(b"claims", &[9]);
        let proof2 = prove_batched::<Rq, G>(&inflated, &mut ch2);

        let mut chv2 = FsChallenger::<Shake128Xof, Rq>::new(b"batch-forge");
        chv2.absorb(b"claims", &[9]);
        let inflated_claims: Vec<Rq> = vec![honest[0].claimed, honest[1].claimed + Rq::from(7)];
        let (challenges, final_eval) =
            verify_batched::<Rq, G>(&proof2, &inflated_claims, &mut chv2)
                .expect("self-consistent forgery passes the round loop");

        // tie-back against the HONEST tables fails
        let honest_combined = combined_table(&honest, &proof2.gamma);
        let mut point_eval = Rq::zero();
        for (idx, t) in honest_combined.iter().enumerate() {
            let mut w = Rq::one();
            for (g, r) in challenges.iter().enumerate() {
                let bit = (idx >> (G - 1 - g)) & 1 == 1;
                w *= if bit { *r } else { Rq::one() - *r };
            }
            point_eval += w * *t;
        }
        assert_ne!(
            final_eval, point_eval,
            "the fake table diverges at the point"
        );
    }

    #[test]
    fn gamma_binds_the_absorbed_statement() {
        // two different absorbed statements → two different batch weights
        let tables = [test_table(4)];
        let claims = plain_claims(&tables);
        let mut ch1 = FsChallenger::<Shake128Xof, Rq>::new(b"gamma-bind");
        ch1.absorb(b"claims", &[1]);
        let p1 = prove_batched::<Rq, G>(&claims, &mut ch1);
        let mut ch2 = FsChallenger::<Shake128Xof, Rq>::new(b"gamma-bind");
        ch2.absorb(b"claims", &[2]);
        let p2 = prove_batched::<Rq, G>(&claims, &mut ch2);
        assert_ne!(p1.gamma, p2.gamma);
    }
}
