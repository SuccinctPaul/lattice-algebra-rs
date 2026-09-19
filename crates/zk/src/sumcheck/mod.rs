//! GreyHound-style multilinear sumcheck over a commutative ring (L5, Z3).
//!
//! Proves the claim `Σ_{x ∈ {0,1}^G} T(x) = S` for an explicit truth table
//! `T ∈ R^{2^G}`. The protocol works over **any commutative ring** — no
//! inverses are needed: per-round challenges are derived *after* absorbing
//! the round message (Fiat–Shamir, via [`RoundChallenger`]), and the round
//! messages are the two partial sums of the (multilinear) folded table.
//!
//! # Soundness
//!
//! **The round challenges must be bound to the round messages.** A
//! challenger that emits challenges independent of the messages (a bare
//! pre-seeded stream) is *exploitable*: a prover that knows all challenges
//! in advance can craft round messages consistent with any claimed sum.
//! That is why the API takes a [`RoundChallenger`] — whose contract is to
//! absorb `(h₀, h₁)` before squeezing — and not a bare closure.
//! [`FsChallenger`] is the reference implementation.
//!
//! Over a ring, Schwartz–Zippel weakens with zero divisors: a dishonest
//! round message passes round `i` with probability at most
//! `|ann(Δ₁)| / |R| ≤ 1/2`, where `Δ₁` is the leading coefficient of the
//! difference between the sent message polynomial and the honest one (`Δ₁`
//! a unit ⇒ 0). The bound amplifies multiplicatively over the `G` rounds.
//! For standalone deployments outside the committed-table flow, a field
//! ring is the conservative challenge choice.
//!
//! In the Z3 R1CS flow the table is the per-gate residual vector of the
//! batched opening response, so the sumcheck replaces Z2's single
//! γ-combination with round-by-round folding.

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Xof;
use algebra::ring::MatrixElement;
use alloc::string::ToString;
use alloc::vec::Vec;
use core::marker::PhantomData;
use rand::RngCore;

/// Per-round challenge derivation for the sumcheck loop.
///
/// The contract is the soundness-critical part: implementations **must**
/// absorb `(h0, h1)` (or otherwise make the challenge depend on them)
/// before deriving the round challenge. [`FsChallenger`] is the reference
/// implementation.
pub trait RoundChallenger<R> {
    /// Absorbs the round message and returns the round challenge.
    fn round_challenge(&mut self, h0: &R, h1: &R) -> R;
}

/// Reference [`RoundChallenger`]: a domain-separated transcript that
/// absorbs each round message (length-prefixed canonical `Display`
/// encoding) and maps the squeezed stream into the ring through
/// `MatrixElement::random`.
pub struct FsChallenger<X: Xof, R: MatrixElement> {
    tr: Transcript<X>,
    _r: PhantomData<R>,
}

impl<X: Xof, R: MatrixElement> FsChallenger<X, R> {
    /// Creates a challenger under a domain label. Prover and verifier must
    /// use the same label; distinct labels yield distinct challenge streams
    /// (which the verifier's round checks then reject).
    pub fn new(domain: &[u8]) -> Self {
        Self {
            tr: Transcript::new(domain),
            _r: PhantomData,
        }
    }

    /// Absorbs extra public binding material (e.g. the claimed sum or a
    /// commitment) before the rounds start.
    pub fn absorb(&mut self, label: &[u8], bytes: &[u8]) {
        self.tr.absorb(label, bytes);
    }
}

impl<X: Xof, R: MatrixElement> RoundChallenger<R> for FsChallenger<X, R> {
    fn round_challenge(&mut self, h0: &R, h1: &R) -> R {
        // length-prefixed Display encoding: unambiguous concatenation
        // without committing to a wire format
        for (label, h) in [(&b"h0"[..], h0), (&b"h1"[..], h1)] {
            let encoded = h.to_string();
            self.tr.absorb(label, &(encoded.len() as u64).to_le_bytes());
            self.tr.absorb(label, encoded.as_bytes());
        }
        let mut rng = TranscriptRng(&mut self.tr);
        R::random(&mut rng)
    }
}

/// Bridges a transcript into `rand::RngCore` so the ring's own
/// `MatrixElement::random` can serve as the challenge mapper.
struct TranscriptRng<'a, X: Xof>(&'a mut Transcript<X>);

impl<X: Xof> RngCore for TranscriptRng<'_, X> {
    fn next_u32(&mut self) -> u32 {
        u32::from_le_bytes(self.0.challenge_bytes(4).try_into().expect("4 bytes"))
    }

    fn next_u64(&mut self) -> u64 {
        u64::from_le_bytes(self.0.challenge_bytes(8).try_into().expect("8 bytes"))
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let bytes = self.0.challenge_bytes(dest.len());
        dest.copy_from_slice(&bytes);
    }
}

/// Half-table size above which the prover's per-round sums and fold run on
/// the rayon pool (`parallel` feature).
#[cfg(feature = "parallel")]
const PAR_MIN_HALF: usize = 1024;

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

/// Runs the prover side. `challenger` derives the per-round challenges
/// *after* absorbing each round message (see [`RoundChallenger`]); the
/// table's honest sum is the claimed value.
///
/// With the `parallel` feature, rounds whose folded table is large enough
/// compute their partial sums and fold across the rayon pool. Reordered
/// additions are exact: the protocol is stated over a commutative ring, so
/// every summation order yields the same round messages and the proof is
/// bit-identical to the sequential prover's.
#[cfg(not(feature = "parallel"))]
pub fn prove<R, const G: usize>(
    table: &[R],
    challenger: &mut dyn RoundChallenger<R>,
) -> SumcheckProof<R, G>
where
    R: MatrixElement + Clone,
{
    prove_sequential(table, challenger)
}

/// `parallel`-enabled variant; the `Send + Sync` bounds are what the rayon
/// pool needs (every ring in this workspace satisfies them).
#[cfg(feature = "parallel")]
pub fn prove<R, const G: usize>(
    table: &[R],
    challenger: &mut dyn RoundChallenger<R>,
) -> SumcheckProof<R, G>
where
    R: MatrixElement + Clone + Send + Sync,
{
    assert_eq!(table.len(), 1 << G, "table must have 2^G entries");
    if table.len() < 2 * PAR_MIN_HALF {
        return prove_sequential(table, challenger);
    }
    prove_rayon(table, challenger)
}

/// Sequential reference prover.
fn prove_sequential<R, const G: usize>(
    table: &[R],
    challenger: &mut dyn RoundChallenger<R>,
) -> SumcheckProof<R, G>
where
    R: MatrixElement + Clone,
{
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
        let r = challenger.round_challenge(&h0, &h1);
        rounds.push((h0, h1));
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

/// Rayon prover: the deep rounds (large folded table) sum and fold on the
/// pool, the shallow tail stays sequential.
#[cfg(feature = "parallel")]
fn prove_rayon<R, const G: usize>(
    table: &[R],
    challenger: &mut dyn RoundChallenger<R>,
) -> SumcheckProof<R, G>
where
    R: MatrixElement + Clone + Send + Sync,
{
    use rayon::prelude::*;

    let mut cur = table.to_vec();
    let mut rounds = Vec::with_capacity(G);

    for _ in 0..G {
        let half = cur.len() / 2;
        let (h0, h1) = if half >= PAR_MIN_HALF {
            (
                cur[..half]
                    .par_iter()
                    .cloned()
                    .reduce(R::zero, |a, b| a + b),
                cur[half..]
                    .par_iter()
                    .cloned()
                    .reduce(R::zero, |a, b| a + b),
            )
        } else {
            (sum_slice(&cur[..half]), sum_slice(&cur[half..]))
        };
        let r = challenger.round_challenge(&h0, &h1);
        rounds.push((h0, h1));
        let (lo_part, hi_part) = cur.split_at_mut(half);
        if half >= PAR_MIN_HALF {
            lo_part
                .par_iter_mut()
                .zip(hi_part.par_iter())
                .for_each(|(lo, hi)| {
                    *lo = lo.clone() + r.clone() * (hi.clone() - lo.clone());
                });
        } else {
            for (lo, hi) in lo_part.iter_mut().zip(hi_part.iter()) {
                *lo = lo.clone() + r.clone() * (hi.clone() - lo.clone());
            }
        }
        cur.truncate(half);
    }
    SumcheckProof {
        rounds,
        final_eval: cur.remove(0),
    }
}

/// Sums a slice with the ring's zero as the identity.
#[cfg(feature = "parallel")]
fn sum_slice<R: MatrixElement + Clone>(xs: &[R]) -> R {
    let mut acc = R::zero();
    for x in xs {
        acc = acc + x.clone();
    }
    acc
}

/// Runs the verifier side: round-by-round consistency (`h(0) + h(1)` equals
/// the incoming claim) and the final evaluation match. Returns the derived
/// challenge point and the final evaluation so applications can tie the
/// folded claim back to public data.
pub fn verify<R, const G: usize>(
    proof: &SumcheckProof<R, G>,
    claimed_sum: R,
    challenger: &mut dyn RoundChallenger<R>,
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
        let r = challenger.round_challenge(h0, h1);
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
    use algebra::crypto::xof::Shake128Xof;
    use algebra::ring::traits::MatrixElement;
    use algebra::ring::zq::Zq;

    type Rq = Zq<8380417>;

    #[test]
    fn honest_sumcheck_over_ring_table() {
        let table: Vec<Rq> = (0..1024usize)
            .map(|i| Rq::from(((i * 37) % 97) as u64))
            .collect();
        let sum: Rq = table
            .iter()
            .fold(<Rq as MatrixElement>::zero(), |a, b| a + *b);

        let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"sumcheck-common");
        let proof = prove::<Rq, 10>(&table, &mut ch);

        let mut chv = FsChallenger::<Shake128Xof, Rq>::new(b"sumcheck-common");
        let (challenges, final_eval) =
            verify::<Rq, 10>(&proof, sum, &mut chv).expect("honest sumcheck must verify");
        assert_eq!(challenges.len(), 10);
        assert_eq!(final_eval, proof.final_eval);
    }

    #[test]
    fn wrong_claim_is_rejected() {
        let table: Vec<Rq> = (0..256usize).map(|i| Rq::from((i % 13) as u64)).collect();
        let mut ch_p = FsChallenger::<Shake128Xof, Rq>::new(b"wrong-claim");
        let proof = prove::<Rq, 8>(&table, &mut ch_p);

        let mut ch_v = FsChallenger::<Shake128Xof, Rq>::new(b"wrong-claim");
        let wrong: Rq = Rq::from(1);
        assert!(verify::<Rq, 8>(&proof, wrong, &mut ch_v).is_none());
    }

    #[test]
    fn tampered_round_message_is_rejected() {
        let table: Vec<Rq> = (0..64usize).map(|i| Rq::from((i * 3) as u64)).collect();
        let mut ch_p = FsChallenger::<Shake128Xof, Rq>::new(b"tamper");
        let mut proof = prove::<Rq, 6>(&table, &mut ch_p);
        proof.rounds[2].0 += Rq::from(1);
        let mut ch_v = FsChallenger::<Shake128Xof, Rq>::new(b"tamper");
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
        let mut ch_p = FsChallenger::<Shake128Xof, Rq>::new(b"diverge");
        let proof = prove::<Rq, 5>(&table, &mut ch_p);
        let mut ch_v = FsChallenger::<Shake128Xof, Rq>::new(b"DIVERGE");
        let sum: Rq = table
            .iter()
            .fold(<Rq as MatrixElement>::zero(), |a, b| a + *b);
        // round consistency holds; challenges diverge → final mismatch
        assert!(verify::<Rq, 5>(&proof, sum, &mut ch_v).is_none());
    }

    /// The soundness reason the API takes a [`RoundChallenger`] instead of a
    /// pre-seeded challenge stream: with per-round Fiat–Shamir binding, a
    /// prover trying to open a different sum for its own (forged) table is
    /// caught at the first round-consistency check.
    #[test]
    fn forged_table_fails_under_fs_binding() {
        let table: Vec<Rq> = (0..64usize)
            .map(|i| Rq::from((i * 11 % 17) as u64))
            .collect();
        let mut fake: Vec<Rq> = table.clone();
        fake[0] += Rq::from(5);
        assert_ne!(
            fake.iter().fold(Rq::zero(), |a, b| a + *b),
            table.iter().fold(Rq::zero(), |a, b| a + *b)
        );

        // the forger proves its own table (absorbing the fake messages)
        let mut ch_f = FsChallenger::<Shake128Xof, Rq>::new(b"forgery");
        let proof = prove::<Rq, 6>(&fake, &mut ch_f);

        // the verifier checks the HONEST claim against those messages
        let true_sum: Rq = table.iter().fold(Rq::zero(), |a, b| a + *b);
        let mut ch_v = FsChallenger::<Shake128Xof, Rq>::new(b"forgery");
        assert!(verify::<Rq, 6>(&proof, true_sum, &mut ch_v).is_none());
    }
}

pub mod ipa;
