//! The **degree-`Δ` sum-check** of Cheng–Nguyen–Tyagi, eprint 2026/2067,
//! Definition 9 (p. 17) — the non-multilinear variant Maltese's reductions
//! actually run, and the reason [`crate::sumcheck`]'s multilinear one cannot
//! stand in for it.
//!
//! # The distinction, in the paper's own words
//!
//! > "The sum-check protocol `(r ∈ K^ℓ, y ∈ K) ← SC(v, ℓ, G)` is a polyIOR that
//! > checks that the sum of evaluations of a **ℓ-variate, degree at most `d`
//! > polynomial** `G ∈ K_{≤d}[X_1,...,X_ℓ]` on the Boolean hypercube results in
//! > some claimed value `v ∈ K`. … The output of the sum-check protocol is a
//! > claim that **`y ?= G(r)`** for some random point `r ∈ K^ℓ`." (Def. 9, p. 17)
//!
//! [`crate::sumcheck`] implements the *multilinear* case: its input is an
//! explicit truth table `T ∈ R^{2^G}` and its output claim is `T̃(r)`, the
//! multilinear extension **of the table**. Every Maltese reduction needs
//! something else — a *circuit* in multilinear oracles:
//!
//! ```text
//! Π^Fold  Eq. (15)  p. 31:  G(X) = Σ_j q̃_subs,j(X)·s̃_j(X)          Δ = 2
//! Π^PE_NC Step 1(c) p. 28:  G(X) = êq(X,r)·Σ_k ξ^k·N_b(ĉf(s)_k(X))  Δ = 2b
//! ```
//!
//! The two readings agree **on the hypercube** — so they prove the very same
//! claim `v` — and disagree **off** it, so they end at different claims:
//! `G(r) = Σ_j q̃_j(r)·s̃_j(r)` versus `(x ↦ Σ_j q_j(x)s_j(x))̃ (r)`. That is not
//! cosmetic. Protocol 4 Step 2(c) (p. 33) *defines* `y_subs` as the first, and
//! only that one is re-provable against the `t_subs` commitment through Eq. (17)
//! (p. 31) — the second is a claim about a vector no commitment binds, so a
//! verifier that accepted it has nothing left to check. Protocol 3 Step 2(b)
//! (p. 28) is the same equation, `y_N =? êq(r_N, r)·Σ_k ξ^k·N_b(cf(a_l)_k)`,
//! which *is* `G(r_N)`: under the multilinear reading an honestly-short opening
//! makes the table vanish identically, hence `y_N = 0`, while `N_b` of the
//! packed claim at a random point is not `0` — so the literal step rejects
//! every honest proof. Both protocols therefore need this module.
//!
//! # How this one works
//!
//! Round `i`'s message is the **coefficient vector** of
//!
//! ```text
//! h_i(X) := Σ_{b ∈ {0,1}^{n−i}} G(ρ_1,...,ρ_{i−1}, X, b)
//! ```
//!
//! of degree at most `Δ`, since each oracle is multilinear and `G` has
//! per-variable degree at most `Δ`. The verifier checks `h_i(0) + h_i(1)`
//! against the running claim and folds that claim forward by evaluating the
//! *sent* polynomial at its own challenge. Coefficient form is what keeps this
//! division-free: interpolating from evaluations would need inverses of the
//! Lagrange denominators, and `R_F` has no general inverse — the same reason
//! [`crate::sumcheck`] only ever interpolates linearly.
//!
//! The prover needs no symbolics either: a multilinear oracle restricted to the
//! round line is the linear polynomial `(1−X)·p(0,b) + X·p(1,b)`, so [`LinePoly`]
//! arithmetic carries the circuit and its coefficients are summed.
//!
//! The round challenge is bound to **every** coefficient of the message (see
//! [`round_challenge`]), not just to `h(0), h(1)`: with a degree-`Δ` message an
//! unbound tail is a free choice for a cheating prover, and
//! [`crate::sumcheck`]'s own soundness note calls an unbound challenge stream
//! exploitable.
//!
//! # Soundness caveat, inherited and widened
//!
//! [`crate::sumcheck`] documents that over a ring, Schwartz–Zippel weakens with
//! zero divisors. The same applies here and *more* strongly, since the round
//! polynomials have degree `Δ > 1`: a dishonest message passes round `i` with
//! probability `|ann(Δ_Δ)|/|R|` over its leading coefficient. Maltese takes
//! challenges in the extension field `K` (§4, Protocols 1–2) precisely to avoid
//! this; a `K = F` compilation inherits the caveat and must say so.

use crate::sumcheck::{FsChallenger, RoundChallenger};
use algebra::crypto::xof::Shake256Xof;
use algebra::ring::MatrixElement;
use alloc::{format, string::String, string::ToString, vec, vec::Vec};
use core::fmt;

/// A univariate polynomial in the round line variable `X`, ascending
/// coefficients, degree at most `NC − 1`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinePoly<R: MatrixElement, const NC: usize> {
    /// `coeffs[0] + coeffs[1]·X + … + coeffs[NC−1]·X^{NC−1}`.
    pub coeffs: [R; NC],
}

impl<R: MatrixElement, const NC: usize> LinePoly<R, NC> {
    /// The zero polynomial.
    ///
    /// `core::array::from_fn` rather than `[R::zero(); NC]`: [`MatrixElement`]
    /// does not imply `Copy`, and ring elements are heap-backed.
    pub fn zero() -> Self {
        Self {
            coeffs: core::array::from_fn(|_| R::zero()),
        }
    }

    /// The constant polynomial `v`.
    pub fn constant(v: R) -> Self {
        let mut out = Self::zero();
        out.coeffs[0] = v;
        out
    }

    /// A degree-`d` monomial `c·X^d`, zero if `d ≥ NC`.
    pub fn monomial(c: R, d: usize) -> Self {
        let mut out = Self::zero();
        if d < NC {
            out.coeffs[d] = c;
        }
        out
    }

    /// The line `(1 − X)·lo + X·hi` through `(0, lo)` and `(1, hi)` — the
    /// restriction of a *multilinear* oracle to the round line.
    ///
    /// # Panics
    /// If `NC < 2`; a line needs two coefficients.
    pub fn from_line(lo: R, hi: R) -> Self {
        assert!(NC >= 2, "a line needs at least two coefficients");
        let mut out = Self::zero();
        out.coeffs[0] = lo.clone();
        out.coeffs[1] = hi - lo;
        out
    }

    /// `self + other`.
    pub fn add_assign(&mut self, other: &Self) {
        for (acc, term) in self.coeffs.iter_mut().zip(other.coeffs.iter()) {
            *acc = acc.clone() + term.clone();
        }
    }

    /// `c · self`.
    pub fn scaled(&self, c: &R) -> Self {
        let mut out = Self::zero();
        for (acc, term) in out.coeffs.iter_mut().zip(self.coeffs.iter()) {
            *acc = term.clone() * c.clone();
        }
        out
    }

    /// `self + c` for a constant `c`.
    pub fn offset(&self, c: R) -> Self {
        let mut out = self.clone();
        out.coeffs[0] = out.coeffs[0].clone() + c;
        out
    }

    /// `self · other`, which must fit in the declared degree `NC − 1`.
    ///
    /// # Errors
    /// [`CircuitError::DegreeOverflow`] if a *non-zero* term lands at or beyond
    /// coefficient `NC`. Dropping one silently would make the round message lie
    /// about the circuit, so the caller is told to raise `NC` instead.
    pub fn mul(&self, other: &Self) -> Result<Self, CircuitError> {
        let mut out = Self::zero();
        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in other.coeffs.iter().enumerate() {
                let product = a.clone() * b.clone();
                if i + j >= NC {
                    if product != R::zero() {
                        return Err(CircuitError::DegreeOverflow {
                            degree: i + j,
                            declared: NC - 1,
                        });
                    }
                    continue;
                }
                out.coeffs[i + j] = out.coeffs[i + j].clone() + product;
            }
        }
        Ok(out)
    }

    /// The polynomial at `x`, by Horner. Division-free, so it works over `R_F`.
    pub fn eval(&self, x: &R) -> R {
        let mut acc = R::zero();
        for coefficient in self.coeffs.iter().rev() {
            acc = acc * x.clone() + coefficient.clone();
        }
        acc
    }

    /// `self(1)`: the sum of the coefficients.
    pub fn at_one(&self) -> R {
        self.coeffs.iter().cloned().sum()
    }
}

/// Why a generalized sum-check could not be run, or was refused.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CircuitError {
    /// A component table did not have exactly `2^NV` entries.
    WrongLength {
        /// Entries supplied.
        got: usize,
        /// Entries required.
        expected: usize,
    },
    /// The composition needs a larger degree bound than declared.
    DegreeOverflow {
        /// Degree a non-zero term reached.
        degree: usize,
        /// The declared bound `Δ`.
        declared: usize,
    },
    /// The claimed sum is not the circuit's hypercube sum: the prover refuses to
    /// emit a proof of a false statement.
    ClaimMismatch,
    /// A proof had a different number of rounds than `NV`.
    WrongRounds {
        /// Rounds supplied.
        got: usize,
        /// Rounds required.
        expected: usize,
    },
    /// A round message failed its consistency check with the running claim, or
    /// did not reproduce the challenge point it claims to.
    RoundRejected {
        /// The round (1-based) that failed.
        round: usize,
    },
    /// The carried final evaluation differs from the one derived from the proof's
    /// own last round message.
    FinalMismatch,
}

impl fmt::Display for CircuitError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CircuitError::WrongLength { got, expected } => {
                write!(f, "table of {got} entries, expected {expected}")
            }
            CircuitError::DegreeOverflow { degree, declared } => write!(
                f,
                "the composition reaches degree {degree} but the declared bound is {declared}; \
                 the round polynomial would be truncated"
            ),
            CircuitError::ClaimMismatch => {
                write!(f, "the claimed sum is not the hypercube sum of the circuit")
            }
            CircuitError::WrongRounds { got, expected } => {
                write!(f, "proof of {got} rounds, expected {expected}")
            }
            CircuitError::RoundRejected { round } => {
                write!(f, "round {round}'s message fails the running-claim check")
            }
            CircuitError::FinalMismatch => write!(
                f,
                "the sent final evaluation is not the last round message at the challenge point"
            ),
        }
    }
}

/// The circuit a [`CircuitSumcheckProof`] proves a claim about.
///
/// Implementors add `G(line_0, …, line_{t−1})` into `acc`, where `line_c` is
/// oracle `c` restricted to the round line: linear in `X`, while `G` as a whole
/// reaches degree `NC − 1`. Called once per suffix assignment, so keep it
/// allocation-light.
pub trait Composition<R: MatrixElement, const NC: usize> {
    /// `acc += G(lines)`.
    fn compose(
        &mut self,
        lines: &[LinePoly<R, NC>],
        acc: &mut LinePoly<R, NC>,
    ) -> Result<(), CircuitError>;
}

/// The two-oracle product `G(X) = A(X)·B(X)`, which reaches degree exactly 2 and
/// so needs `NC = 3`.
///
/// This is the shape a claim takes when one factor is a **committed** multilinear
/// table and the other is **public**: Hachi's ring-switching step (eprint
/// 2026/156, §1.3 p. 7) lifts `Σ_k M_k(X)·z_k(X) = w(X) + (X^d+1)·r(X)` to
/// `Z_q[X]`, commits to `P := mle[(z′,r′)]`, draws `α ← F_{q^k}`, and is left
/// with the field inner-product claim
///
/// ```text
/// Σ_{i∈{0,1}^µ} P(i)·Q(i) = V,      Q public,
/// ```
///
/// whose `Q` holds the `α`-powers the substitution produces. Maltese's Eq. (15)
/// (`Σ_j q̃_subs,j(X)·s̃_j(X)`, p. 31) is a sum of these. `A` is the committed
/// factor and `B` the public one; the protocol itself does not care which is
/// which, but the caller's opening obligation does.
pub struct Product;

impl<R: MatrixElement> Composition<R, 3> for Product {
    fn compose(
        &mut self,
        lines: &[LinePoly<R, 3>],
        acc: &mut LinePoly<R, 3>,
    ) -> Result<(), CircuitError> {
        if lines.len() != 2 {
            return Err(CircuitError::WrongLength {
                got: lines.len(),
                expected: 2,
            });
        }
        acc.add_assign(&lines[0].mul(&lines[1])?);
        Ok(())
    }
}

/// A completed degree-`Δ` sum-check (Def. 9) over `NV` variables, where the
/// round messages carry `NC = Δ + 1` coefficients.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CircuitSumcheckProof<R: MatrixElement, const NV: usize, const NC: usize> {
    /// Round `i`'s message: the ascending coefficients of `h_i`.
    pub rounds: Vec<[R; NC]>,
    /// The derived challenge point `ρ ∈ R^NV`.
    pub point: Vec<R>,
    /// `G(ρ)` — the *circuit* value at `ρ`, Def. 9's output claim.
    pub final_eval: R,
}

/// The multilinear extension of `table` at `point`: `µ` halvings along the
/// leading variable, which is the same fold [`prove`] makes internally, so the
/// two cannot drift.
///
/// Exposed because Def. 9's output claim is about the **circuit** at `ρ`, and the
/// caller's obligation is to tie that claim to its own oracles — which needs this
/// map over any [`MatrixElement`] domain, an extension field included (that is
/// exactly what Hachi's substituted claim lives in).
///
/// # Panics
/// If `table.len() != 2^point.len()`: a truncated table would make the fold agree
/// with the extension at the vertices it never read.
pub fn multilinear_at<R: MatrixElement>(table: &[R], point: &[R]) -> R {
    let len = 1usize << point.len();
    assert_eq!(
        table.len(),
        len,
        "a point of {} variables spans {len} entries, but the table has {}",
        point.len(),
        table.len()
    );
    let mut cur = table.to_vec();
    for rho in point {
        let half = cur.len() / 2;
        cur = (0..half)
            .map(|i| cur[i].clone() + rho.clone() * (cur[half + i].clone() - cur[i].clone()))
            .collect();
    }
    cur[0].clone()
}

/// Squeezes the round challenge, bound to the **whole** message.
///
/// [`FsChallenger`]'s own contract is to absorb `(h0, h1)` before squeezing; at
/// degree `Δ ≥ 2` that leaves `Δ − 1` coefficients unbound, so the full
/// length-prefixed coefficient list is absorbed first. The encoding matches
/// `FsChallenger::round_challenge`'s (`Display`, length-prefixed) so the two
/// sides cannot drift.
fn round_challenge<R: MatrixElement, const NC: usize>(
    challenger: &mut FsChallenger<Shake256Xof, R>,
    message: &[R; NC],
) -> R {
    let mut encoded = String::new();
    for coefficient in message.iter() {
        let text = coefficient.to_string();
        encoded.push_str(&format!("{}:{}", text.len(), text));
    }
    challenger.absorb(b"h", encoded.as_bytes());
    challenger.round_challenge(&message[0], &message[1])
}

/// Prover side of Def. 9: `NV` rounds for
/// `claimed_sum =? Σ_{X ∈ {0,1}^NV} G(X)`, where `G` is `circuit` applied to the
/// supplied multilinear oracle `tables`.
///
/// # Errors
/// [`CircuitError::WrongLength`] if a table is not `2^NV` long,
/// [`CircuitError::DegreeOverflow`] if `NC − 1` understates the circuit,
/// [`CircuitError::ClaimMismatch`] if the statement is false.
pub fn prove<R, const NV: usize, const NC: usize, C>(
    tables: &[&[R]],
    claimed_sum: &R,
    domain: &[u8],
    binding: &[u8],
    circuit: &mut C,
) -> Result<CircuitSumcheckProof<R, NV, NC>, CircuitError>
where
    R: MatrixElement,
    C: Composition<R, NC> + ?Sized,
{
    let len = 1usize << NV;
    if let Some(short) = tables.iter().find(|table| table.len() != len) {
        return Err(CircuitError::WrongLength {
            got: short.len(),
            expected: len,
        });
    }
    let mut state: Vec<Vec<R>> = tables.iter().map(|table| table.to_vec()).collect();
    let mut rounds = Vec::with_capacity(NV);
    let mut point: Vec<R> = Vec::with_capacity(NV);
    let mut claim = claimed_sum.clone();
    let mut challenger = FsChallenger::<Shake256Xof, R>::new(domain);
    challenger.absorb(b"binding", binding);
    for _ in 0..NV {
        let half = state[0].len() / 2;
        let mut lines = vec![LinePoly::<R, NC>::zero(); state.len()];
        let mut message = LinePoly::<R, NC>::zero();
        for b in 0..half {
            for (index, table) in state.iter().enumerate() {
                lines[index] = LinePoly::from_line(table[b].clone(), table[half + b].clone());
            }
            circuit.compose(&lines, &mut message)?;
        }
        if message.coeffs[0].clone() + message.at_one() != claim {
            return Err(CircuitError::ClaimMismatch);
        }
        let rho = round_challenge(&mut challenger, &message.coeffs);
        claim = message.eval(&rho);
        rounds.push(message.coeffs);
        point.push(rho.clone());
        // Fold every oracle with the challenge just derived — not the previous
        // one, which is the off-by-one that makes a generalized sum-check lie.
        for table in state.iter_mut() {
            for b in 0..half {
                let lo = table[b].clone();
                let hi = table[half + b].clone();
                table[b] = lo.clone() + rho.clone() * (hi - lo);
            }
            table.truncate(half);
        }
    }
    Ok(CircuitSumcheckProof {
        rounds,
        point,
        final_eval: claim,
    })
}

/// Verifier side: replays the challenge stream, checks each round message
/// against the running claim, and returns `(ρ, G(ρ))` for the application to tie
/// to its own public data — which is the whole point of Def. 9's output form.
///
/// # Errors
/// [`CircuitError::WrongRounds`], [`CircuitError::RoundRejected`],
/// [`CircuitError::FinalMismatch`].
pub fn verify<R, const NV: usize, const NC: usize>(
    proof: &CircuitSumcheckProof<R, NV, NC>,
    claimed_sum: &R,
    domain: &[u8],
    binding: &[u8],
) -> Result<(Vec<R>, R), CircuitError>
where
    R: MatrixElement,
{
    if proof.rounds.len() != NV {
        return Err(CircuitError::WrongRounds {
            got: proof.rounds.len(),
            expected: NV,
        });
    }
    let mut claim = claimed_sum.clone();
    let mut point = Vec::with_capacity(NV);
    let mut challenger = FsChallenger::<Shake256Xof, R>::new(domain);
    challenger.absorb(b"binding", binding);
    for (index, message) in proof.rounds.iter().enumerate() {
        let line = LinePoly::<R, NC> {
            coeffs: message.clone(),
        };
        if line.coeffs[0].clone() + line.at_one() != claim {
            return Err(CircuitError::RoundRejected { round: index + 1 });
        }
        let rho = round_challenge(&mut challenger, message);
        if proof.point.get(index) != Some(&rho) {
            return Err(CircuitError::RoundRejected { round: index + 1 });
        }
        claim = line.eval(&rho);
        point.push(rho);
    }
    if proof.final_eval != claim {
        return Err(CircuitError::FinalMismatch);
    }
    Ok((point, claim))
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::extension::ExtField;
    use algebra::ring::zq::Zq;
    use algebra::ring::traits::Ring;

    type F = Zq<4294967197>;
    const NV: usize = 3;
    /// `Δ = 2` for a product circuit, so three coefficients per round.
    const NC: usize = 3;
    const LEN: usize = 1 << NV;
    const DOMAIN: &[u8] = b"circuit-test";

    fn vec_at(len: usize, base: u64) -> Vec<F> {
        (0..len)
            .map(|i| F::from((base + i as u64 * 7) % 1_000_003))
            .collect()
    }

    /// `G(X) = a(X)·b(X)·c(X)` — needs `NC ≥ 4`, and reports an overflow below
    /// that rather than truncating.
    struct Triple;

    impl<const NC: usize> Composition<F, NC> for Triple {
        fn compose(
            &mut self,
            lines: &[LinePoly<F, NC>],
            acc: &mut LinePoly<F, NC>,
        ) -> Result<(), CircuitError> {
            let quad = lines[0].mul(&lines[1])?;
            acc.add_assign(&quad.mul(&lines[2])?);
            Ok(())
        }
    }

    fn sum_of_products(tables: &[&[F]]) -> F {
        (0..LEN).fold(F::ZERO, |acc, x| {
            acc + tables
                .iter()
                .fold(F::ONE, |product, table| product * table[x])
        })
    }

    /// The multilinear extension of `table` at `point`.
    fn mle(table: &[F], point: &[F]) -> F {
        let mut cur = table.to_vec();
        for rho in point {
            let half = cur.len() / 2;
            cur = (0..half)
                .map(|i| cur[i] + *rho * (cur[half + i] - cur[i]))
                .collect();
        }
        cur[0]
    }

    #[test]
    fn the_output_claim_is_the_circuit_not_the_table_extension() {
        // The reason this module exists. On the cube the two readings coincide —
        // they prove the same `v` — and off the cube they must not.
        let a = vec_at(LEN, 1);
        let b = vec_at(LEN, 500_000);
        let binding = b"deg2".to_vec();
        let claimed = sum_of_products(&[&a, &b]);
        let proof = prove::<F, NV, NC, _>(&[&a, &b], &claimed, DOMAIN, &binding, &mut Product)
            .expect("honest claim");
        let (point, final_eval) =
            verify::<F, NV, NC>(&proof, &claimed, DOMAIN, &binding).expect("verifies");
        assert_eq!(final_eval, proof.final_eval);
        assert_eq!(proof.rounds.len(), NV);
        assert_eq!(proof.rounds[0].len(), NC);
        // G(r) = Σ_j ã_j(r)·b̃_j(r): the product of the two extensions.
        let circuit = mle(&a, &point) * mle(&b, &point);
        assert_eq!(final_eval, circuit, "Def. 9's output claim is G(r)");
        // …and NOT the extension of the pointwise product table.
        let table: Vec<F> = a.iter().zip(b.iter()).map(|(x, y)| *x * *y).collect();
        let table_reading = mle(&table, &point);
        assert_ne!(
            table_reading, circuit,
            "if these agree the degree-2 machinery proves nothing new"
        );
        // The hypercube sums, however, are the same number.
        assert_eq!(claimed, table.iter().copied().sum::<F>());
    }

    #[test]
    fn three_oracle_products_reach_the_declared_degree_exactly() {
        let (a, b, c) = (vec_at(LEN, 3), vec_at(LEN, 11), vec_at(LEN, 257));
        let claimed = sum_of_products(&[&a, &b, &c]);
        let binding = b"tri".to_vec();
        // NC = 3 is Δ = 2: too small for a cubic.
        let mut narrow = Triple;
        assert!(prove::<F, NV, 3, _>(&[&a, &b, &c], &claimed, DOMAIN, &binding, &mut narrow)
            .is_err_and(|err| matches!(
                err,
                CircuitError::DegreeOverflow { degree: 3, declared: 2 }
            )));
        // NC = 4 is Δ = 3: fits, and the claim is the cubic at ρ.
        let proof = prove::<F, NV, 4, _>(&[&a, &b, &c], &claimed, DOMAIN, &binding, &mut Triple)
            .expect("cubic fits NC = 4");
        let (point, final_eval) =
            verify::<F, NV, 4>(&proof, &claimed, DOMAIN, &binding).expect("verifies");
        assert_eq!(final_eval, mle(&a, &point) * mle(&b, &point) * mle(&c, &point));
    }

    #[test]
    fn a_forged_round_message_is_rejected_at_its_own_round() {
        let a = vec_at(LEN, 1);
        let b = vec_at(LEN, 9);
        let claimed = sum_of_products(&[&a, &b]);
        let binding = b"bind".to_vec();
        let honest =
            prove::<F, NV, NC, _>(&[&a, &b], &claimed, DOMAIN, &binding, &mut Product).expect("prove");
        let mut forged = honest.clone();
        forged.rounds[1][2] += F::ONE;
        assert_eq!(
            verify::<F, NV, NC>(&forged, &claimed, DOMAIN, &binding),
            Err(CircuitError::RoundRejected { round: 2 }),
            "the quadratic coefficient is bound to the *next* challenge"
        );
        // A proof does not replay under another statement…
        assert!(matches!(
            verify::<F, NV, NC>(&honest, &claimed, DOMAIN, b"other"),
            Err(CircuitError::RoundRejected { .. })
        ));
        // …nor with a truncated transcript.
        let mut short = honest.clone();
        short.rounds.pop();
        assert_eq!(
            verify::<F, NV, NC>(&short, &claimed, DOMAIN, &binding),
            Err(CircuitError::WrongRounds {
                got: 2,
                expected: 3
            })
        );
    }

    #[test]
    fn the_prover_refuses_a_false_claim_and_a_wrong_shape() {
        let a = vec_at(LEN, 1);
        let b = vec_at(LEN, 9);
        let lie = sum_of_products(&[&a, &b]) + F::ONE;
        assert_eq!(
            prove::<F, NV, NC, _>(&[&a, &b], &lie, DOMAIN, b"", &mut Product),
            Err(CircuitError::ClaimMismatch)
        );
        assert_eq!(
            prove::<F, NV, NC, _>(&[&a[..LEN - 1], &b], &lie, DOMAIN, b"", &mut Product),
            Err(CircuitError::WrongLength {
                got: LEN - 1,
                expected: LEN
            })
        );
    }

    #[test]
    fn the_degree_guard_tests_the_product_not_the_nominal_shape() {
        // `G = a·flat + z·z` at `NC = 2` (nominal degree 1, though two factors are
        // multiplied): `flat` has a zero slope and `z` is the zero table, so every
        // term of degree ≥ 2 is exactly zero and must not trip the guard.
        let a = vec_at(LEN, 1);
        let flat = vec![F::from(5u64); LEN];
        let zero = vec![F::ZERO; LEN];
        let claimed = sum_of_products(&[&a, &flat]);
        let proof = prove::<F, NV, 2, _>(
            &[&a, &flat, &zero, &zero],
            &claimed,
            DOMAIN,
            b"",
            &mut PairProductZero,
        )
        .expect("the high terms are exactly zero");
        let (point, final_eval) = verify::<F, NV, 2>(&proof, &claimed, DOMAIN, b"").expect("ok");
        assert_eq!(final_eval, mle(&a, &point) * F::from(5u64));
        // The same shape with a *sloped* second factor does overflow.
        let sloped = vec_at(LEN, 9);
        assert!(prove::<F, NV, 2, _>(
            &[&a, &sloped, &zero, &zero],
            &sum_of_products(&[&a, &sloped]),
            DOMAIN,
            b"",
            &mut PairProductZero
        )
        .is_err_and(|err| matches!(err, CircuitError::DegreeOverflow { .. })));
    }

    /// `a·b + 0·0`, used to show the overflow guard tests the product, not the
    /// nominal degree.
    struct PairProductZero;

    impl Composition<F, 2> for PairProductZero {
        fn compose(
            &mut self,
            lines: &[LinePoly<F, 2>],
            acc: &mut LinePoly<F, 2>,
        ) -> Result<(), CircuitError> {
            acc.add_assign(&lines[0].mul(&lines[1])?);
            acc.add_assign(&lines[2].mul(&lines[3])?);
            Ok(())
        }
    }

    #[test]
    fn line_polys_evaluate_at_the_line_ends_and_agree_with_direct_arithmetic() {
        let (lo, hi) = (F::from(11u64), F::from(29u64));
        let line = LinePoly::<F, NC>::from_line(lo, hi);
        assert_eq!(line.coeffs[0], lo);
        assert_eq!(line.eval(&F::ZERO), lo);
        assert_eq!(line.eval(&F::ONE), hi);
        assert_eq!(line.at_one(), hi);
        let squared = line.mul(&line).expect("degree 2 fits NC = 3");
        let x = F::from(123_456u64);
        let direct = {
            let at = lo + x * (hi - lo);
            at * at
        };
        assert_eq!(squared.eval(&x), direct, "Horner == the squared line");
        assert_eq!(LinePoly::<F, NC>::constant(x).at_one(), x);
        assert_eq!(LinePoly::<F, NC>::monomial(x, 2).eval(&F::from(3u64)), x * F::from(9u64));
        assert_eq!(LinePoly::<F, NC>::monomial(x, 5).coeffs, [F::ZERO; NC]);
        assert_eq!(squared.scaled(&hi).coeffs[0], squared.coeffs[0] * hi);
    }

    /// Hachi's §1.3 step is a product of a committed table and a public one,
    /// **over the extension field** — that is where its `Õ(k)` verifier comes
    /// from. This runs [`Product`] there, and pins Def. 9's output form: the
    /// protocol ends at the circuit value `Ã(ρ)·B̃(ρ)`, not at a claim about a
    /// table sum, which is the distinction [`crate::sumcheck`] cannot cross.
    #[test]
    fn the_product_circuit_proves_an_inner_product_over_an_extension_field() {
        type E = ExtField<F, 4, 2>;
        let z = E::z_generator();
        let a: Vec<E> = vec_at(LEN, 3)
            .iter()
            .map(|v| E::from_base(*v))
            .collect();
        // Genuinely extension-valued weights: two base coefficients each, so a
        // silent collapse to the base field would show up as an inequality.
        let b: Vec<E> = (0..LEN)
            .map(|i| {
                E::from_base(F::from(1 + i as u64))
                    + z.clone() * E::from_base(F::from(7 + 3 * i as u64))
            })
            .collect();
        let claimed: E = (0..LEN).fold(E::zero(), |acc, i| acc + a[i].clone() * b[i].clone());
        let binding = b"hachi-shaped";
        let proof =
            prove::<E, NV, 3, _>(&[&a, &b], &claimed, DOMAIN, binding, &mut Product)
                .expect("the prover proves a true field inner product");
        let (rho, final_eval) = verify::<E, NV, 3>(&proof, &claimed, DOMAIN, binding)
            .expect("the verifier accepts and hands back (ρ, G(ρ))");

        assert_eq!(rho.len(), NV);
        assert_eq!(final_eval, proof.final_eval);
        assert_eq!(
            final_eval,
            multilinear_at(&a, &rho) * multilinear_at(&b, &rho),
            "Def. 9's output claim is the circuit evaluated at ρ"
        );
    }

    /// [`multilinear_at`] is the map the protocol folds: at a vertex it returns
    /// the table entry, and at a general point it matches an independent
    /// `Σ_i U(i)·êq(i,r)` expansion — over the extension field, where the
    /// coefficients genuinely mix.
    #[test]
    fn multilinear_at_agrees_with_the_equality_polynomial_expansion() {
        type E = ExtField<F, 4, 2>;
        let z = E::z_generator();
        let one = E::one();
        let table: Vec<E> = (0..LEN)
            .map(|i| {
                E::from_base(F::from(2 + i as u64))
                    + z.clone() * E::from_base(F::from(5 * i as u64))
            })
            .collect();
        let point: Vec<E> = (0..NV)
            .map(|j| {
                z.clone() * E::from_base(F::from(9 + j as u64))
                    + E::from_base(F::from(3 + j as u64))
            })
            .collect();
        let mut expect = E::zero();
        for bits in 0..LEN {
            let mut weight = one.clone();
            for j in 0..NV {
                let factor = if (bits >> (NV - 1 - j)) & 1 == 1 {
                    point[j].clone()
                } else {
                    one.clone() - point[j].clone()
                };
                weight = weight * factor;
            }
            expect = expect + table[bits].clone() * weight;
        }
        assert_eq!(multilinear_at(&table, &point), expect);
        for bits in 0..LEN {
            let vertex: Vec<E> = (0..NV)
                .map(|j| {
                    if (bits >> (NV - 1 - j)) & 1 == 1 {
                        one.clone()
                    } else {
                        E::zero()
                    }
                })
                .collect();
            assert_eq!(multilinear_at(&table, &vertex), table[bits], "vertex {bits}");
        }
    }

    #[test]
    #[should_panic(expected = "spans")]
    fn multilinear_at_refuses_a_table_that_does_not_span_the_point() {
        let point: Vec<F> = (0..NV - 1).map(|_| F::from(7u64)).collect();
        let _ = multilinear_at(&vec_at(LEN, 3), &point);
    }

    /// [`Product`] is exactly two oracles: a third is refused rather than quietly
    /// paired, and a false claim is refused by the prover itself.
    #[test]
    fn the_product_circuit_refuses_a_third_oracle_and_a_false_claim() {
        let (a, b, c) = (vec_at(LEN, 3), vec_at(LEN, 5), vec_at(LEN, 7));
        assert_eq!(
            prove::<F, NV, NC, _>(&[&a, &b, &c], &F::ZERO, DOMAIN, b"", &mut Product),
            Err(CircuitError::WrongLength {
                got: 3,
                expected: 2
            }),
            "pairing three oracles would be a different circuit than declared"
        );
        let lie = sum_of_products(&[&a, &b]) + F::ONE;
        assert_eq!(
            prove::<F, NV, NC, _>(&[&a, &b], &lie, DOMAIN, b"", &mut Product),
            Err(CircuitError::ClaimMismatch)
        );
    }
}
