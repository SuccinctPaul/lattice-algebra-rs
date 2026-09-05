//! GreyHound-style multilinear sumcheck over a commutative ring (L5, Z3).
//!
//! Proves the claim `Σ_{x ∈ {0,1}^G} T(x) = S` for an explicit truth table
//! `T ∈ R^{2^G}`. The protocol works over **any commutative ring** — no
//! inverses are needed: per-round challenges come from a caller-supplied
//! challenge closure (deterministically derived from a shared transcript on
//! both sides), and the round messages are the two partial sums of the
//! (multilinear) folded table.
//!
//! Soundness: `G` rounds of Schwartz–Zippel over the challenge ring (for
//! `R = Z_{2^32}[X]/(X^64+1)` that is 2048 random bits per round). In the Z3
//! R1CS flow the table is the per-gate residual vector of the batched
//! opening response, so the sumcheck replaces Z2's single γ-combination with
//! round-by-round folding.

use algebra::ring::MatrixElement;

/// A completed sumcheck: the per-round linear messages plus the final
/// evaluation of the folded table at the challenge point.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SumcheckProof<R: MatrixElement, const G: usize> {
    /// Round `i` message: `(h_i(0), h_i(1))` — the two partial sums of the
    /// table folded over rounds `0..i`, split by the current variable.
    pub rounds: Vec<(R, R)>,
    /// `T(r)` — the table evaluated at the full challenge point.
    pub final_eval: R,
}

impl<R: MatrixElement, const G: usize> SumcheckProof<R, G> {
    /// Number of table entries this proof is shaped for.
    pub fn table_len() -> usize {
        1 << G
    }
}

/// Runs the prover side. `challenge` yields the per-round ring challenges
/// (identically derived by prover and verifier — e.g. from a shared
/// transcript seed). The table's honest sum is the claimed value.
pub fn prove<R, const G: usize>(
    table: &[R],
    challenge: &mut dyn FnMut() -> R,
) -> SumcheckProof<R, G>
where
    R: MatrixElement + Clone,
{
    assert_eq!(table.len(), 1 << G, "table must have 2^G entries");
    let mut cur = table.to_vec();
    let mut rounds = Vec::with_capacity(G);

    for _ in 0..G {
        let half = cur.len() / 2;
        let mut h0 = R::zero();
        let mut h1 = R::zero();
        for j in 0..half {
            h0 = h0 + cur[j].clone();
            h1 = h1 + cur[j + half].clone();
        }
        rounds.push((h0.clone(), h1.clone()));
        let r = challenge();
        for j in 0..half {
            let lo = cur[j].clone();
            let hi = cur[j + half].clone();
            cur[j] = lo.clone() + r.clone() * (hi - lo);
        }
        cur.truncate(half);
    }
    SumcheckProof {
        rounds,
        final_eval: cur.remove(0),
    }
}

/// Runs the verifier side: round-by-round consistency (`h(0) + h(1)` equals
/// the incoming claim) and the final evaluation match. Returns the derived
/// challenge point and the final evaluation so applications can tie the
/// folded claim back to public data.
pub fn verify<R, const G: usize>(
    proof: &SumcheckProof<R, G>,
    claimed_sum: R,
    challenge: &mut dyn FnMut() -> R,
) -> Option<(Vec<R>, R)>
where
    R: MatrixElement + Clone,
{
    if proof.rounds.len() != G {
        return None;
    }
    let mut claim = claimed_sum;
    let mut challenges = Vec::with_capacity(G);
    for (h0, h1) in &proof.rounds {
        if h0.clone() + h1.clone() != claim {
            return None;
        }
        let r = challenge();
        challenges.push(r.clone());
        // fold: interpolate the claim at the challenge point
        claim = h0.clone() + r * (h1.clone() - h0.clone());
    }
    if proof.final_eval != claim {
        return None;
    }
    Some((challenges, proof.final_eval.clone()))
}

/// `eq(r, x) = Π_i (r_i·x_i + (1−r_i)(1−x_i))` — the multilinear equality
/// polynomial, used by verifiers that fold public gate data.
pub fn eq_tensor<R, const G: usize>(r: &[R; G], x: &[bool; G]) -> R
where
    R: MatrixElement + Clone,
{
    let mut acc = R::one();
    for i in 0..G {
        let term = if x[i] {
            r[i].clone()
        } else {
            R::one() - r[i].clone()
        };
        acc = acc * term;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::crypto::xof::{Shake128Xof, Xof};
    use algebra::ring::traits::MatrixElement;
    use algebra::ring::zq::Zq;

    type Rq = Zq<8380417>;

    /// Ring challenges derived from a fresh SHAKE stream seeded identically
    /// on both sides.
    fn zq_challenger(seed: &[u8]) -> impl FnMut() -> Rq {
        let mut xof = Shake128Xof::new(seed);
        let mut buf = [0u8; 4];
        move || {
            xof.squeeze(&mut buf);
            Rq::from(u64::from(u32::from_le_bytes(buf)))
        }
    }

    #[test]
    fn honest_sumcheck_over_ring_table() {
        let table: Vec<Rq> = (0..1024usize)
            .map(|i| Rq::from(((i * 37) % 97) as u64))
            .collect();
        let sum: Rq = table
            .iter()
            .fold(<Rq as MatrixElement>::zero(), |a, b| a + *b);

        let mut ch = zq_challenger(b"sumcheck-common");
        let proof = prove::<Rq, 10>(&table, &mut ch);

        let mut chv = zq_challenger(b"sumcheck-common");
        let (challenges, final_eval) =
            verify::<Rq, 10>(&proof, sum, &mut chv).expect("honest sumcheck must verify");
        assert_eq!(challenges.len(), 10);
        assert_eq!(final_eval, proof.final_eval);
    }

    #[test]
    fn wrong_claim_is_rejected() {
        let table: Vec<Rq> = (0..256usize).map(|i| Rq::from((i % 13) as u64)).collect();
        let mut ch_p = zq_challenger(b"wrong-claim");
        let proof = prove::<Rq, 8>(&table, &mut ch_p);

        let mut ch_v = zq_challenger(b"wrong-claim");
        let wrong: Rq = Rq::from(1);
        assert!(verify::<Rq, 8>(&proof, wrong, &mut ch_v).is_none());
    }

    #[test]
    fn tampered_round_message_is_rejected() {
        let table: Vec<Rq> = (0..64usize).map(|i| Rq::from((i * 3) as u64)).collect();
        let mut ch_p = zq_challenger(b"tamper");
        let mut proof = prove::<Rq, 6>(&table, &mut ch_p);
        proof.rounds[2].0 += Rq::from(1);
        let mut ch_v = zq_challenger(b"tamper");
        let sum: Rq = table
            .iter()
            .fold(<Rq as MatrixElement>::zero(), |a, b| a + *b);
        assert!(verify::<Rq, 6>(&proof, sum, &mut ch_v).is_none());
    }

    #[test]
    fn challenge_divergence_detected() {
        // A verifier transcript that diverges from the prover's must fail
        // the final evaluation check (folding used different challenges).
        let table: Vec<Rq> = (0..32usize).map(|i| Rq::from((i * 7) as u64)).collect();
        let mut ch_p = zq_challenger(b"diverge");
        let proof = prove::<Rq, 5>(&table, &mut ch_p);
        let mut ch_v = zq_challenger(b"DIVERGE");
        let sum: Rq = table
            .iter()
            .fold(<Rq as MatrixElement>::zero(), |a, b| a + *b);
        // round consistency holds; challenges diverge → final mismatch
        assert!(verify::<Rq, 5>(&proof, sum, &mut ch_v).is_none());
    }
}
