//! Degree-`L` multilinear sum-check over a *sum of products* of tables
//! (eprint 2026/1983 Fig. 2 / §3.4, §6.1, §7.4).
//!
//! # Why this module exists next to [`crate::sumcheck`]
//!
//! The base [`crate::sumcheck::prove`] sends one `(h(0), h(1))` pair per round
//! and folds linearly, which proves a claim about the multilinear extension of
//! a **single** table. Akita's checks are not of that shape: the range stage
//! sums `eq(tau_0, x) * prod_k (s(x) - k(k+1))` (Eq. 115, individual degree
//! `1 + b*/2`) and the fused stage sums
//! `ew(x) * m(x) + (gamma * eq + zeta_bin * eq_bin) * ew(x) * ew(x)`
//! (Eq. 160, individual degree 3). A degree-`L` round polynomial is not
//! recoverable from its two Boolean endpoints, so this module implements
//! Figure 2's compressed format: the prover sends the coefficients
//! `(s_{j,0}, s_{j,2}, ..., s_{j,L})` — the linear one omitted — and the
//! verifier recovers it from the running claim,
//!
//! ```text
//! s_{j,1} = T_j - 2 s_{j,0} - sum_{i >= 2} s_{j,i}
//! ```
//!
//! which is inversion-free and one field element per round cheaper (§3.5 counts
//! the same saving for its equality-factored variant). All rejection therefore
//! sits at the *final* check, so the caller must compare the returned running
//! claim against [`summand_at`] at the returned point.
//!
//! # The summand shape
//!
//! A summand is a sum of products of named multilinear tables: `terms[k]` lists
//! factor indices, factor `i` being the MLE of `factors[i]` over `{0,1}^G`.
//! Constant multiples (the `gamma`, `zeta_bin`, `zeta_norm` weights) are folded
//! into the corresponding factor tables, which is what the paper's "public
//! weight that combines claim c" amounts to. Products of the *same* factor
//! (Eq. 160's `ew * ew`) are written by listing the index twice, so no table is
//! duplicated and the round degree stays the term length.
//!
//! # Statements are values, so they can be added
//!
//! Akita never runs a lone sum-check at the top level: Eq. (125) fuses the norm
//! term into the last range-tree sum-check and Eq. (128) fuses the binding term
//! into the relation row,
//!
//! ```text
//! sum_x (P_rng(x)   + zeta_norm P_norm(x))   = C_rng   + zeta_norm C_norm   (125)
//! sum_x (P_base(x)  +          P_bind(x))    = C_base  + C_bind             (128)
//! ```
//!
//! both "with no new sum-check rounds". [`Summand`] is a statement as a value and
//! [`fuse`] is their addition: concatenated factors, renumbered terms, summed
//! claims. See [`fuse`] for the one hypothesis that makes the addition sound.
//!
//! # Soundness
//!
//! Figure 2 item 1: if the claimed sum differs from the Boolean sum of the
//! summand, acceptance has probability at most `G * L / |F|` (Theorem 3.7).
//! That bound presumes the challenge depends on the *whole* round message, which
//! is why this module declares [`DegChallenger`] instead of reusing
//! [`crate::sumcheck::RoundChallenger`] — whose `(h0, h1)` contract cannot see
//! the remaining coefficients.
//!
//! # Figure 2, transcribed (p. 33)
//!
//! ```text
//! Claim: T = Σ_{x∈{0,1}^µ} g(x), where g : F^µ → F has individual degree ≤ ℓ.
//! Verifier state: running claim T_1 := T.
//! For j = 1, …, µ:
//!   1. P → V: the round polynomial s_j(X_j) := Σ_{x_{j+1..µ}} g(r_1,…,r_{j−1}, X_j, x_{j+1},…,x_µ)
//!      of degree ≤ ℓ, with its linear coefficient omitted: (s_{j,0}, s_{j,2}, …, s_{j,ℓ}).
//!   2. V recovers the linear coefficient from the running claim T_j = s_j(0) + s_j(1),
//!         s_{j,1} = T_j − 2 s_{j,0} − Σ_{i≥2} s_{j,i}.
//!   3. V → P: sample r_j ← F and set T_{j+1} := s_j(r_j).
//! Final check: V accepts iff g(r_1, …, r_µ) = T_{µ+1}.
//! ```
//!
//! Theorem 3.7 (p. 32) states both halves this module is built to serve: item 1
//! "Interactive soundness. If `T ≠ Σ_{x∈{0,1}^µ} g(x)`, then a cheating prover
//! causes the verifier to accept with probability at most `µℓ/|F|`", and item 2
//! `(ℓ + 1)`-special soundness, "Fix the prefix and the prover's round-j
//! message. If `ℓ + 1` distinct challenges … have continuations certifying the
//! corresponding honest residual sums, then interpolation identifies the round
//! polynomial with the honest degree-at-most-`ℓ` polynomial `s_j`." Item 2 is
//! why [`prove`] keeps its own copy of the honest cube sum rather than deriving
//! it from the caller's claim: a false claim must still be met with the *true*
//! round polynomials.

use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::Xof;
use algebra::ring::Ring;
use alloc::vec;
use alloc::vec::Vec;
use core::iter::Sum;
use core::marker::PhantomData;

/// Per-round challenge derivation for a degree-`L` sum-check.
///
/// Same soundness contract as [`crate::sumcheck::RoundChallenger`], widened to
/// the whole message: an implementation **must** make the challenge depend on
/// every coefficient it is handed before returning one.
pub trait DegChallenger<R> {
    /// Absorbs the round message and returns the round challenge.
    fn round_challenge(&mut self, message: &[R]) -> R;
}

/// Reference [`DegChallenger`]: a domain-separated transcript that absorbs each
/// coefficient of the round message, position-tagged.
pub struct FsDegChallenger<X: Xof, R: Ring> {
    tr: Transcript<X>,
    _r: PhantomData<R>,
}

impl<X: Xof, R: Ring> FsDegChallenger<X, R> {
    /// Creates a challenger under a domain label. Prover and verifier must use
    /// the same label; distinct labels give divergent challenge streams, which
    /// the final check then rejects.
    pub fn new(domain: &[u8]) -> Self {
        Self {
            tr: Transcript::new(domain),
            _r: PhantomData,
        }
    }

    /// Absorbs public binding material (a commitment payload, a claimed value)
    /// before the rounds start.
    pub fn absorb(&mut self, label: &[u8], bytes: &[u8]) {
        self.tr.absorb(label, bytes);
    }
}

impl<X: Xof, R: Ring> DegChallenger<R> for FsDegChallenger<X, R> {
    fn round_challenge(&mut self, message: &[R]) -> R {
        for (i, coefficient) in message.iter().enumerate() {
            // Canonical fixed-width encoding: the position is absorbed with the
            // value so reordering a message cannot survive.
            self.tr.absorb(b"pos", &(i as u64).to_le_bytes());
            self.tr
                .absorb(b"msg", &coefficient.to_u128().to_le_bytes());
        }
        let bytes = self.tr.challenge_bytes(8);
        let mut raw = [0u8; 8];
        raw.copy_from_slice(&bytes[..8]);
        // Rejection-free into the field up to a 2^-32 bias on the top bits; the
        // protocol's own budget (Qmax, Eq. 224) is not claimed here.
        R::from(u64::from_le_bytes(raw) % R::MODULUS)
    }
}

/// A completed degree-`L` sum-check: one truncated coefficient vector per round
/// (Figure 2's `(s_{j,0}, s_{j,2}, ..., s_{j,L})`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FusedProof<R: Ring> {
    /// The degree bound this proof was produced under.
    pub degree: usize,
    /// The variable count `G` this proof runs over, i.e. the number of rounds
    /// the statement demands. Carried explicitly because the verifier otherwise
    /// has to read it off [`FusedProof::rounds`] and could not tell a truncated
    /// proof from a shorter statement.
    pub variables: usize,
    /// Round `j`'s message: `L` coefficients, the linear one omitted.
    pub rounds: Vec<Vec<R>>,
}

/// The number of coefficients a round message carries for degree bound `L`.
pub const fn message_len(l: usize) -> usize {
    // s_0 plus s_2..s_L: exactly L entries for L >= 1, since s_1 is recovered
    // from the running claim rather than sent.
    if l < 1 {
        0
    } else {
        l
    }
}

/// `log2` of a power-of-two table length, i.e. the variable count `G`.
///
/// # Panics
/// If `n` is not a power of two.
pub const fn variables(n: usize) -> usize {
    assert!(n.is_power_of_two() && n >= 2, "a sum-check table must be a power-of-two length >= 2");
    n.trailing_zeros() as usize
}

/// The Boolean sum of `sum_terms prod_{i in term} factors[i](x)` over `{0,1}^G`.
///
/// # Panics
/// If a table is mis-sized, a term is empty, or a term references an unknown
/// factor.
pub fn summand_sum<R: Ring>(factors: &[&[R]], terms: &[&[usize]]) -> R {
    let n = checked_shape(factors, terms);
    let mut acc = R::ZERO;
    for x in 0..n {
        let mut row = R::ZERO;
        for term in terms {
            let mut product = R::ONE;
            for &i in term.iter() {
                product *= factors[i][x];
            }
            row += product;
        }
        acc += row;
    }
    acc
}

/// Validates the factor/term shape and returns the table length.
fn checked_shape<R: Ring>(factors: &[&[R]], terms: &[&[usize]]) -> usize {
    assert!(!factors.is_empty(), "a sum-check needs at least one factor");
    let n = factors[0].len();
    for f in factors {
        assert_eq!(f.len(), n, "all factor tables must share one cube");
    }
    assert!(n.is_power_of_two() && n >= 2, "table length must be a power of two");
    assert!(!terms.is_empty(), "a summand needs at least one term");
    for term in terms {
        assert!(!term.is_empty(), "an empty term is a constant, not a product");
        for &i in term.iter() {
            assert!(i < factors.len(), "term references a missing factor");
        }
    }
    n
}

/// The summand's value at a point, from the per-factor values.
pub fn summand_at<R: Ring>(values: &[R], terms: &[&[usize]]) -> R {
    let mut acc = R::ZERO;
    for term in terms {
        let mut product = R::ONE;
        for &i in term.iter() {
            product *= values[i];
        }
        acc += product;
    }
    acc
}

/// The multilinear extension of one length-`2^G` table at `r`, by folding the
/// whole table (the reference path: `O(2^G)`, what a *direct* verifier pays).
///
/// # Panics
/// If `r.len()` and the table length disagree, or the length is not a power of
/// two.
pub fn fold_table<R: Ring>(table: &[R], r: &[R]) -> R {
    let g = variables(table.len());
    assert_eq!(r.len(), g, "the point must have log2(len) coordinates");
    let mut cur = table.to_vec();
    for j in 0..g {
        let half = cur.len() / 2;
        for x in 0..half {
            let lo = cur[x];
            cur[x] = lo + r[j] * (cur[x + half] - lo);
        }
        cur.truncate(half);
    }
    cur[0]
}

/// Each factor's multilinear extension at `r`.
pub fn factor_values<R: Ring>(factors: &[&[R]], r: &[R]) -> Vec<R> {
    factors.iter().map(|table| fold_table(table, r)).collect()
}

/// One sum-check statement, held by value: the summand's factor tables, its
/// product terms, and the claimed sum.
///
/// This is the owned counterpart of [`prove`]'s borrowed `factors`/`terms` pair,
/// and it exists so that two statements can be *combined* — which is what
/// Eq. (128) and Eq. (125) both are. A sum-check statement that cannot be named
/// as a value cannot be added to another one.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Summand<R> {
    /// The summand's multilinear factor tables, all over one cube.
    pub factors: Vec<Vec<R>>,
    /// Each product of the sum-of-products, as factor indices.
    pub terms: Vec<Vec<usize>>,
    /// The claimed sum `T`.
    pub claimed: R,
}

impl<R: Ring> Summand<R> {
    /// The individual-degree bound this summand demands: its longest product.
    pub fn degree(&self) -> usize {
        self.terms.iter().map(|t| t.len()).max().unwrap_or(1)
    }

    /// The cube every factor lives on.
    ///
    /// # Panics
    /// If the tables are ragged — a shape the fused prover cannot express.
    pub fn cube(&self) -> usize {
        let n = self.factors.first().map_or(0, Vec::len);
        assert!(
            self.factors.iter().all(|f| f.len() == n),
            "all factor tables must share one cube"
        );
        n
    }

    /// The honest Boolean sum of the summand, which a caller needing to *derive*
    /// a claim (rather than restate a prover's) computes with.
    ///
    /// # Panics
    /// As [`summand_sum`], on a mis-shaped summand.
    pub fn boolean_sum(&self) -> R
    where
        R: Sum<R>,
    {
        let refs: Vec<&[R]> = self.factors.iter().map(|f| f.as_slice()).collect();
        let trefs: Vec<&[usize]> = self.terms.iter().map(|t| t.as_slice()).collect();
        summand_sum::<R>(&refs, &trefs)
    }

    /// Runs Figure 2's prover on this summand, at its own degree bound.
    ///
    /// # Panics
    /// As [`prove`].
    pub fn prove(&self, challenger: &mut dyn DegChallenger<R>) -> FusedProof<R>
    where
        R: Sum<R>,
    {
        let refs: Vec<&[R]> = self.factors.iter().map(|f| f.as_slice()).collect();
        let trefs: Vec<&[usize]> = self.terms.iter().map(|t| t.as_slice()).collect();
        prove::<R>(&refs, &trefs, self.degree(), self.claimed, challenger)
    }

    /// Figure 2's whole verifier: recover the point and running claim from the
    /// messages, fold every factor at that point, and require the running claim
    /// to equal the summand there. `true` only if the proof is well-formed *and*
    /// closes, so a caller cannot mistake a truncation for an acceptance.
    pub fn accepts(&self, proof: &FusedProof<R>, challenger: &mut dyn DegChallenger<R>) -> bool
    where
        R: Sum<R>,
    {
        let refs: Vec<&[R]> = self.factors.iter().map(|f| f.as_slice()).collect();
        let trefs: Vec<&[usize]> = self.terms.iter().map(|t| t.as_slice()).collect();
        match verify::<R>(proof, self.claimed, challenger) {
            None => false,
            Some((r, run)) => {
                let values: Vec<R> = refs.iter().map(|table| fold_table(table, &r)).collect();
                summand_at(&values, &trefs) == run
            }
        }
    }
}

/// Eq. (128)'s additive fusion of two sum-check statements into one:
///
/// ```text
/// sum_x (P_base(x) + P_bind(x)) = C_base + C_bind                          (128)
/// ```
///
/// The paper uses it to fold the norm binding into the ordinary relation and
/// range-binding sum-check without adding a round, and the reason it is sound to
/// do so is the sentence after the equation: "The ordinary relation is
/// independent of `eta_norm`, while every norm-check residual has positive degree
/// in `eta_norm`. Thus a false norm-check identity cannot cancel a false ordinary
/// relation identically in the batching challenge." Fusing therefore *preserves*
/// soundness only when the two statements' randomness is disjoint in exactly that
/// way — a caller that hands `fuse` two claims weighted by the *same* challenge
/// has built a cancelable pair, which is why the extra weights are folded into
/// `extra`'s factor tables by the caller ([`crate::pcs::norm_route::pi_binding`])
/// rather than here.
///
/// Shape: `extra`'s factor indices are renumbered past `base`'s tables, and the
/// two term lists are concatenated, so the result sums the union of both products
/// over one cube. The cubes must already match — a sum-check is one statement
/// over one Boolean domain, so zero-padding to the larger domain is the caller's
/// job (which is why [`crate::pcs::norm_route::pi_binding`] returns a full-length
/// weight table rather than a span-relative one: a zero-padded factor keeps the
/// Boolean sum of every product it appears in).
///
/// `None` on a cube mismatch, or on an empty statement, neither of which has a
/// sum-check to fuse into.
pub fn fuse<R: Ring>(base: &Summand<R>, extra: &Summand<R>) -> Option<Summand<R>> {
    if base.factors.is_empty() || extra.factors.is_empty() {
        return None;
    }
    if base.cube() != extra.cube() {
        return None;
    }
    let offset = base.factors.len();
    let mut factors = base.factors.clone();
    factors.extend(extra.factors.iter().cloned());
    let terms = base
        .terms
        .iter()
        .cloned()
        .chain(extra.terms.iter().map(|t| {
            t.iter()
                .map(|i| i + offset)
                .collect::<Vec<usize>>()
        }))
        .collect();
    Some(Summand {
        factors,
        terms,
        claimed: base.claimed + extra.claimed,
    })
}

/// Runs the Figure-2 prover. `terms` is the summand's sum-of-products shape and
/// `claimed` the statement's claimed sum (the honest prover passes
/// [`summand_sum`]).
///
/// The individual degree is `L = max_k |terms[k]|`; every round message carries
/// `L` coefficients.
///
/// # Panics
/// If the shape is invalid ([`checked_shape`]) or the degree bound is below the
/// summand's real degree.
pub fn prove<R>(
    factors: &[&[R]],
    terms: &[&[usize]],
    degree: usize,
    claimed: R,
    challenger: &mut dyn DegChallenger<R>,
) -> FusedProof<R>
where
    R: Ring + Sum<R>,
{
    let n = checked_shape(factors, terms);
    let g = variables(n);
    let real = terms.iter().map(|t| t.len()).max().unwrap_or(1);
    assert!(
        degree >= real,
        "declared degree {degree} cannot carry a term of degree {real}"
    );
    let l = degree;

    let mut cur: Vec<Vec<R>> = factors.iter().map(|f| f.to_vec()).collect();
    let mut claim = claimed;
    let mut rounds = Vec::with_capacity(g);

    for j in 0..g {
        let half = cur[0].len() / 2;
        let mut coeffs = vec![R::ZERO; l + 1];
        for x in 0..half {
            for term in terms {
                let poly = linear_product(term, &cur, x, half);
                for (d, c) in poly.iter().enumerate() {
                    coeffs[d] += *c;
                }
            }
        }
        // The prover knows every coefficient; the *verifier* is the side that
        // must recover s_1 from the running claim (Figure 2, item 2).
        let mut message = Vec::with_capacity(message_len(l));
        message.push(coeffs[0]);
        if l >= 2 {
            message.extend_from_slice(&coeffs[2..]);
        }
        debug_assert_eq!(message.len(), message_len(l));
        // The prover's invariants, re-derived from the tables each round rather
        // than propagated, so they can actually fail:
        //
        // (a) the round polynomial must be the true endpoint sum of the current
        //     cube — anchored on the *tables*, not on `claim`, because the
        //     caller may hand this function a false sum (that is precisely the
        //     case the compressed format must survive, its only rejection being
        //     the final check) and Theorem 3.7 item 2 still requires the honest
        //     degree-`L` polynomials to be the ones sent;
        // (b) from round 1 on, the running claim must have caught up with that
        //     value: claim_j = s_{j-1}(r_{j-1}), and summing the table folded at
        //     r_{j-1} gives exactly s_{j-1}(r_{j-1}). A fold that drifted would
        //     otherwise be silently baked into every later message.
        //
        // Debug-only: (a) re-sums the cube, which the prover's hot loop has no
        // reason to do.
        #[cfg(debug_assertions)]
        {
            let refs: Vec<&[R]> = cur.iter().map(|t| t.as_slice()).collect();
            let honest = summand_sum::<R>(&refs, terms);
            debug_assert_eq!(
                horner(&coeffs, R::ONE) + coeffs[0],
                honest,
                "round {j}'s polynomial is not the sum it must represent"
            );
            if j > 0 {
                debug_assert_eq!(
                    claim, honest,
                    "round {j}: the running claim left the tables behind"
                );
            }
        }
        let r = challenger.round_challenge(&message);
        rounds.push(message);
        claim = horner(&coeffs, r);
        for table in cur.iter_mut() {
            for x in 0..half {
                let lo = table[x];
                table[x] = lo + r * (table[x + half] - lo);
            }
            table.truncate(half);
        }
    }
    FusedProof {
        degree: l,
        variables: g,
        rounds,
    }
}

/// `sum_d coeffs[d] * r^d`.
fn horner<R: Ring>(coeffs: &[R], r: R) -> R {
    let mut acc = R::ZERO;
    let mut power = R::ONE;
    for c in coeffs {
        acc += power * *c;
        power *= r;
    }
    acc
}

/// `prod_{i in term} (lo_i + T (hi_i - lo_i))`, coefficient-major.
fn linear_product<R: Ring>(term: &[usize], cur: &[Vec<R>], x: usize, half: usize) -> Vec<R> {
    let mut poly = vec![R::ZERO; term.len() + 1];
    poly[0] = R::ONE;
    let mut degree = 0usize;
    for &i in term.iter() {
        let lo = cur[i][x];
        let slope = cur[i][x + half] - lo;
        for d in (1..=degree + 1).rev() {
            poly[d] = poly[d - 1] * slope + poly[d] * lo;
        }
        poly[0] *= lo;
        degree += 1;
    }
    poly
}

/// Runs the Figure-2 verifier: recovers each round's linear coefficient from the
/// running claim, folds, and returns the challenge point with the final running
/// claim. The caller must check that claim against [`summand_at`] — that single
/// equality is the whole rejection the compressed format performs.
///
/// `None` on a malformed proof (wrong round count, wrong message length).
pub fn verify<R>(
    proof: &FusedProof<R>,
    claimed: R,
    challenger: &mut dyn DegChallenger<R>,
) -> Option<(Vec<R>, R)>
where
    R: Ring + Sum<R>,
{
    let l = proof.degree;
    let g = proof.rounds.len();
    if l < 1 || g < 1 {
        return None;
    }
    // A proof that dropped a round is not a proof of this statement: the
    // returned point would have one coordinate fewer than the cube the caller
    // checks against, which the final evaluation would meet with a panic rather
    // than a rejection. `variables` is the declared round count (Figure 2's
    // `µ'`, one challenge per Boolean variable), so the mismatch is visible.
    if proof.variables != g {
        return None;
    }
    let mut claim = claimed;
    let mut r = Vec::with_capacity(g);
    for message in &proof.rounds {
        if message.len() != message_len(l) {
            return None;
        }
        let s0 = message[0];
        let s1 = claim - s0 - s0 - message[1..].iter().copied().sum::<R>();
        let challenge = challenger.round_challenge(message);
        r.push(challenge);
        let mut next = s0 + challenge * s1;
        let mut power = challenge * challenge;
        for c in message[1..].iter() {
            next += power * *c;
            power *= challenge;
        }
        claim = next;
    }
    Some((r, claim))
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::crypto::xof::Shake256Xof;
    use algebra::ring::zq::Zq;

    type Fq = Zq<4_294_967_197>;

    fn table(seed: u64, n: usize) -> Vec<Fq> {
        (0..n)
            .map(|i| Fq::from(((i as u64 + 1) * (seed * 7 + 3)) % Fq::MODULUS))
            .collect()
    }

    /// Runs both sides and returns `(point, running claim, honest summand value)`.
    fn round_trip(
        factors: &[&[Fq]],
        terms: &[&[usize]],
        degree: usize,
    ) -> (Vec<Fq>, Fq, Fq) {
        let claimed = summand_sum::<Fq>(factors, terms);
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"fused-test");
        let proof = prove::<Fq>(factors, terms, degree, claimed, &mut p);
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"fused-test");
        let (r, final_claim) = verify::<Fq>(&proof, claimed, &mut v).expect("shape");
        let values = factor_values::<Fq>(factors, &r);
        (r, final_claim, summand_at(&values, terms))
    }

    #[test]
    fn honest_run_closes_at_the_final_check_for_every_degree() {
        for degree in 1..=5usize {
            let factors: Vec<Vec<Fq>> =
                (0..degree).map(|i| table(i as u64 + 1, 1 << 4)).collect();
            let refs: Vec<&[Fq]> = factors.iter().map(|f| f.as_slice()).collect();
            let term: Vec<usize> = (0..degree).collect();
            let terms: Vec<&[usize]> = vec![term.as_slice()];
            let (r, claim, expected) = round_trip(&refs, &terms, degree);
            assert_eq!(claim, expected, "degree {degree} must close");
            assert_eq!(r.len(), 4, "one challenge per variable");
        }
    }

    #[test]
    fn the_round_message_carries_exactly_l_coefficients() {
        let w = table(2, 1 << 4);
        let m = table(3, 1 << 4);
        let factors: Vec<&[Fq]> = vec![&w, &m];
        let terms: Vec<&[usize]> = vec![&[0, 1]];
        let claimed = summand_sum::<Fq>(&factors, &terms);
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"len");
        let proof = prove::<Fq>(&factors, &terms, 2, claimed, &mut p);
        assert!(proof
            .rounds
            .iter()
            .all(|msg| msg.len() == message_len(2) && msg.len() == 2));
        // a degree-3 summand sends 3 coefficients, one fewer than the L+1
        // points an uncompressed round message would
        let mut p3 = FsDegChallenger::<Shake256Xof, Fq>::new(b"len");
        let cubic = prove::<Fq>(&factors, &[&[0, 0, 1]], 3, claimed, &mut p3);
        assert!(cubic.rounds.iter().all(|msg| msg.len() == 3));
    }

    #[test]
    fn sum_of_products_is_the_sum_of_the_products() {
        let a = table(6, 1 << 3);
        let b = table(7, 1 << 3);
        let c = table(8, 1 << 3);
        let factors: Vec<&[Fq]> = vec![&a, &b, &c];
        let t0: Vec<usize> = vec![0, 1];
        let t1: Vec<usize> = vec![2];
        let terms: Vec<&[usize]> = vec![&t0, &t1];
        let claimed = summand_sum::<Fq>(&factors, &terms);
        let direct: Fq = (0..1 << 3).map(|x| a[x] * b[x] + c[x]).sum();
        assert_eq!(claimed, direct);
        assert_ne!(
            claimed,
            a.iter().copied().sum::<Fq>() + c.iter().copied().sum::<Fq>(),
            "the fixture must not degenerate to a linear sum"
        );
        let (_, claim, expected) = round_trip(&factors, &terms, 2);
        assert_eq!(claim, expected);
    }

    #[test]
    fn repeated_factor_is_the_cubic_range_term_of_eq_160() {
        // ew * ew * eq, written with the same index twice.
        let w = table(4, 1 << 4);
        let e = table(5, 1 << 4);
        let factors: Vec<&[Fq]> = vec![&w, &e];
        let term: Vec<usize> = vec![1, 0, 0];
        let terms: Vec<&[usize]> = vec![term.as_slice()];
        let claimed = summand_sum::<Fq>(&factors, &terms);
        let direct: Fq = (0..1 << 4).map(|x| e[x] * w[x] * w[x]).sum();
        assert_eq!(claimed, direct);
        let (_, claim, expected) = round_trip(&factors, &terms, 3);
        assert_eq!(claim, expected);
    }

    #[test]
    fn a_false_claim_breaks_the_final_equality() {
        // The compressed format has no per-round rejection, so the load-bearing
        // assertion is claim-vs-summand: a false sum must make them disagree.
        let w = table(9, 1 << 4);
        let m = table(10, 1 << 4);
        let factors: Vec<&[Fq]> = vec![&w, &m];
        let terms: Vec<&[usize]> = vec![&[0, 1]];
        let honest = summand_sum::<Fq>(&factors, &terms);
        let lie = honest + Fq::ONE;
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"lie");
        let proof = prove::<Fq>(&factors, &terms, 2, lie, &mut p);
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"lie");
        let (r, claim) = verify::<Fq>(&proof, lie, &mut v).expect("shape");
        let values = factor_values::<Fq>(&factors, &r);
        assert_ne!(
            claim,
            summand_at(&values, &terms),
            "proving a false sum must break the only check the format has"
        );
    }

    #[test]
    fn proof_is_bound_to_the_transcript_label() {
        let w = table(11, 1 << 3);
        let factors: Vec<&[Fq]> = vec![&w];
        let terms: Vec<&[usize]> = vec![&[0]];
        let claimed = summand_sum::<Fq>(&factors, &terms);
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"label-a");
        let proof = prove::<Fq>(&factors, &terms, 1, claimed, &mut p);
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"label-b");
        let (r, claim) = verify::<Fq>(&proof, claimed, &mut v).expect("shape");
        assert_ne!(
            claim,
            summand_at(&factor_values::<Fq>(&factors, &r), &terms),
            "a diverging challenge stream must not close the final check"
        );
    }

    #[test]
    fn malformed_proofs_are_rejected_by_shape() {
        let w = table(12, 1 << 3);
        let factors: Vec<&[Fq]> = vec![&w];
        let terms: Vec<&[usize]> = vec![&[0, 0]];
        let claimed = summand_sum::<Fq>(&factors, &terms);
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"shape");
        let base = prove::<Fq>(&factors, &terms, 2, claimed, &mut p);
        let mut short_round = base.clone();
        short_round.rounds[0].pop();
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"shape");
        assert!(verify::<Fq>(&short_round, claimed, &mut v).is_none());
        let mut dropped = base.clone();
        dropped.rounds.pop();
        let mut v2 = FsDegChallenger::<Shake256Xof, Fq>::new(b"shape");
        assert!(verify::<Fq>(&dropped, claimed, &mut v2).is_none());
        // the declared round count must match the messages it ships with, in
        // both directions: too few is a truncation, too many is a lie about the
        // cube the final check will be evaluated on
        assert_eq!(base.variables, 3, "an 8-entry table is 3 variables");
        let mut overstated = base.clone();
        overstated.variables = 4;
        let mut v4 = FsDegChallenger::<Shake256Xof, Fq>::new(b"shape");
        assert!(verify::<Fq>(&overstated, claimed, &mut v4).is_none());
        let mut zeroed = base.clone();
        zeroed.degree = 0;
        let mut v3 = FsDegChallenger::<Shake256Xof, Fq>::new(b"shape");
        assert!(verify::<Fq>(&zeroed, claimed, &mut v3).is_none());
        assert_eq!(message_len(1), 1);
        assert_eq!(message_len(4), 4);
        assert_eq!(message_len(0), 0);
    }

    /// A prover that computes its round polynomials from the tables but is
    /// handed a false claim must still send the *honest* messages (Theorem 3.7
    /// item 2's premise), and the lie has to surface at the final check rather
    /// than at the prover's own invariant.
    #[test]
    fn a_lie_changes_the_claim_and_not_the_messages() {
        let w = table(16, 1 << 3);
        let m = table(17, 1 << 3);
        let factors: Vec<&[Fq]> = vec![&w, &m];
        let terms: Vec<&[usize]> = vec![&[0, 1]];
        let honest = summand_sum::<Fq>(&factors, &terms);
        let mut p1 = FsDegChallenger::<Shake256Xof, Fq>::new(b"two-claims");
        let honest_proof = prove::<Fq>(&factors, &terms, 2, honest, &mut p1);
        let mut p2 = FsDegChallenger::<Shake256Xof, Fq>::new(b"two-claims");
        let lied_proof = prove::<Fq>(&factors, &terms, 2, honest + Fq::ONE, &mut p2);
        assert_eq!(
            honest_proof.rounds, lied_proof.rounds,
            "the messages are functions of the tables, not of the claim"
        );
        assert_eq!(honest_proof.variables, 3);
        // and the two runs diverge only in what the verifier ends up comparing
        let mut v1 = FsDegChallenger::<Shake256Xof, Fq>::new(b"two-claims");
        let (r, claim) = verify::<Fq>(&lied_proof, honest + Fq::ONE, &mut v1).expect("shape");
        assert_ne!(claim, summand_at(&factor_values::<Fq>(&factors, &r), &terms));
    }

    #[test]
    #[should_panic(expected = "cannot carry a term of degree")]
    fn an_understated_degree_bound_is_refused() {
        let w = table(13, 1 << 3);
        let factors: Vec<&[Fq]> = vec![&w];
        let claimed = summand_sum::<Fq>(&factors, &[&[0, 0, 0]]);
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"deg");
        prove::<Fq>(&factors, &[&[0, 0, 0]], 2, claimed, &mut p);
    }

    #[test]
    #[should_panic(expected = "power of two")]
    fn a_non_power_of_two_table_is_refused() {
        let w = table(14, 12);
        let factors: Vec<&[Fq]> = vec![&w];
        summand_sum::<Fq>(&factors, &[&[0]]);
    }

    /// Cross-checks [`fold_table`] against an independent `eq(r, x)` tensor
    /// contraction, so the extension the final check compares against is not
    /// defined in terms of itself.
    #[test]
    fn fold_table_is_the_eq_tensor_contraction() {
        const G: usize = 4;
        let t = table(15, 1 << G);
        let r = [Fq::from(3u64), Fq::from(9u64), Fq::from(2u64), Fq::from(11u64)];
        let rvec = r.to_vec();
        let got = fold_table::<Fq>(&t, &rvec);
        let mut acc = Fq::ZERO;
        let mut acc2 = Fq::ZERO;
        for x in 0..(1 << G) {
            let bits: [bool; G] = core::array::from_fn(|j| (x >> (G - 1 - j)) & 1 == 1);
            let mut weight = Fq::ONE;
            for j in 0..G {
                weight *= if bits[j] { r[j] } else { Fq::ONE - r[j] };
            }
            acc += weight * t[x];
            acc2 += crate::sumcheck::eq_tensor::<Fq, G>(&r, &bits) * t[x];
        }
        assert_eq!(got, acc);
        assert_eq!(got, acc2);
        assert_eq!(variables(16), G);
    }

    /// Two honest statements, fused exactly as Eq. (128) does.
    fn pair() -> (Summand<Fq>, Summand<Fq>) {
        let a = table(21, 1 << 3);
        let b = table(22, 1 << 3);
        let c = table(23, 1 << 3);
        let base = Summand {
            factors: vec![a.clone(), b.clone()],
            terms: vec![vec![0, 1]],
            claimed: Fq::ZERO,
        };
        let extra = Summand {
            factors: vec![c.clone(), b.clone()],
            terms: vec![vec![0, 0, 1]],
            claimed: Fq::ZERO,
        };
        let base = Summand {
            claimed: base.boolean_sum(),
            ..base
        };
        let extra = Summand {
            claimed: extra.boolean_sum(),
            ..extra
        };
        (base, extra)
    }

    #[test]
    fn a_fused_statement_proves_both_summands_in_one_run() {
        let (base, extra) = pair();
        assert_eq!(base.degree(), 2);
        assert_eq!(extra.degree(), 3);
        let fused = fuse(&base, &extra).expect("one cube");
        // the concatenation and the renumbering, pinned index by index
        assert_eq!(fused.factors.len(), 4);
        assert_eq!(fused.terms, vec![vec![0, 1], vec![2, 2, 3]]);
        assert_eq!(fused.claimed, base.claimed + extra.claimed);
        assert_eq!(fused.degree(), 3, "the messages must carry the longer product");
        assert_eq!(
            fused.boolean_sum(),
            base.boolean_sum() + extra.boolean_sum(),
            "the sum of the sums is the sum of the union"
        );
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"fuse");
        let proof = fused.prove(&mut p);
        assert_eq!(proof.degree, 3);
        assert_eq!(proof.rounds.len(), 3, "one round per cube variable");
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"fuse");
        assert!(fused.accepts(&proof, &mut v), "the honest fused run closes");
    }

    #[test]
    fn an_honest_relation_cannot_mask_a_false_binding() {
        // The property Eq. (128)'s non-cancellation sentence buys: fusing the two
        // statements must not make the pair *more* permissive than each half
        // already is. Here the false half is a claim one off its own Boolean sum.
        let (base, extra) = pair();
        let lying = Summand {
            claimed: extra.claimed + Fq::ONE,
            ..extra.clone()
        };
        let mut pv = FsDegChallenger::<Shake256Xof, Fq>::new(b"mask");
        assert!(
            base.accepts(&base.prove(&mut pv), &mut FsDegChallenger::<Shake256Xof, Fq>::new(b"mask")),
            "the true half does verify on its own"
        );
        let fused = fuse(&base, &lying).expect("one cube");
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"mask");
        let proof = fused.prove(&mut p);
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"mask");
        assert!(
            !fused.accepts(&proof, &mut v),
            "a false binding claim fused into a true relation must still be refused"
        );
    }

    #[test]
    fn accepts_is_not_a_pass_on_a_malformed_or_off_transcript_proof() {
        let (base, extra) = pair();
        let fused = fuse(&base, &extra).expect("one cube");
        let mut p = FsDegChallenger::<Shake256Xof, Fq>::new(b"morph");
        let proof = fused.prove(&mut p);
        let mut honest = FsDegChallenger::<Shake256Xof, Fq>::new(b"morph");
        assert!(fused.accepts(&proof, &mut honest));
        // a dropped round is a truncation, not an acceptance
        let mut dropped = proof.clone();
        dropped.rounds.pop();
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"morph");
        assert!(!fused.accepts(&dropped, &mut v));
        // a moved coefficient is caught by the final check, not by a panic
        let mut moved = proof.clone();
        moved.rounds[1][0] += Fq::ONE;
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"morph");
        assert!(!fused.accepts(&moved, &mut v));
        // and a proof of one statement never verifies another's claim
        let mut other = fused.clone();
        other.claimed += Fq::ONE;
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"morph");
        assert!(!other.accepts(&proof, &mut v));
        // a different transcript label diverges the challenge stream
        let mut v = FsDegChallenger::<Shake256Xof, Fq>::new(b"other-label");
        assert!(!fused.accepts(&proof, &mut v));
    }

    #[test]
    fn fuse_refuses_shapes_it_cannot_represent() {
        let (base, extra) = pair();
        // mismatched cubes: one sum-check is one Boolean domain
        let short = Summand {
            factors: extra.factors.iter().map(|f| f[..4].to_vec()).collect(),
            terms: extra.terms.clone(),
            claimed: extra.claimed,
        };
        assert_eq!(short.cube(), 4);
        assert!(fuse(&base, &short).is_none());
        // an empty statement has no summand to add
        let empty = Summand {
            factors: Vec::new(),
            terms: Vec::new(),
            claimed: Fq::ZERO,
        };
        assert!(fuse(&base, &empty).is_none());
        assert!(fuse(&empty, &base).is_none());
        // ragged tables are a shape error, reported where it is made
        assert_eq!(base.cube(), 8);
    }
}
