//! Noisy ring encodings (L5): the Regev / Ring-LWE **encoding scheme** of
//! eprint 2021/322 §4 (Def. 8) instantiated as in §7.2.
//!
//! Rinocchio does not commit with an Ajtai/SIS hash — its "commitments" are
//! *encodings*, i.e. semantically secure noisy encryptions of ring elements on
//! which only ring-linear combinations can be computed. This module is that
//! capability, in the ring form of §7.2's "Regev-style Encoding":
//!
//! ```text
//! Gen(Γ)      : s ← R_Q^n                       sk = s
//! E_sk(m)     : a ← R_Q,  e ← χ_σ              C = (−a, a·s + q·e + m)
//! D_sk(C)     : (a_0·s + c_1) mod q  =  m
//! ```
//!
//! with `Γ = (q, Q, n, α)`, `q` the *message* characteristic (the ring `R`
//! the program is written over) and `Q` the encoding modulus, `(q, Q) = 1`.
//! The noise enters multiplied by `q`, so it disappears under the final
//! reduction and decryption is **exact** — the paper's "statistically-correct
//! encoding scheme". What is *not* free is the noise budget: the accumulated
//! `q·e + m` has to stay inside the centered window `(−Q/2, Q/2]`, otherwise
//! the lift wraps and the encoding decrypts to a different ring element. That
//! budget is what makes the encoding only **ℓ-linearly-homomorphic** for a
//! fixed `ℓ` (§7.2, "On the suitability of the encoding"), and it is tracked
//! explicitly here: [`Encoding::noise_bound`] is carried through
//! [`eval`] and refused once it reaches [`Encoding::CEILING`].
//!
//! Def. 8's three required properties are all implemented here:
//! - **ℓ-linearly homomorphic** → [`eval`] (ring-scalar combinations of
//!   encodings, with the noise accounting the definition silently assumes);
//! - **quadratic root detection** → [`detect_quadratic_root`] (the verifier
//!   decides `Q(a_1,…,a_t) = 0` using `sk`);
//! - **image verification** → [`image_ok`] (is this element of the encoding
//!   space at all, i.e. within the declared noise budget).
//!
//! # What this is *not*
//!
//! The hardness is Ring-LWE, and it buys **hiding only**. Nothing here is
//! binding: an Ajtai/SIS commitment (`crate::commitment`, `crate::pcs`) is a
//! different object with a different soundness story. Rinocchio's soundness
//! rests on generalized q-PDH / augmented q-PKE over these encodings, and the
//! stronger *linear-only extractability* the paper needs for its Groth16-like
//! variant (§4.2, §6) is stated as a **conjecture**, not a theorem.

use crate::foundation::fs::seed_stream;
use crate::foundation::sampling::uniform_poly;
use algebra::crypto::sampling::{sample_rej_bounded, BitStream};
use algebra::crypto::xof::Xof;
use algebra::ring::number_theory::gcd_u64;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::{CenteredRing, Ring};
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use alloc::vec;
use alloc::vec::Vec;
use core::fmt;

/// Why an encoding could not be produced or accepted.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegevError {
    /// The accumulated noise bound reached the centered window `(Q−1)/2`:
    /// further homomorphic operations would decrypt to the wrong element.
    NoiseBudget {
        /// The bound the operation would produce.
        declared: u64,
        /// `(Q−1)/2`, the largest admissible bound.
        ceiling: u64,
    },
    /// The instance parameters are not the paper's: it requires `(q, Q) = 1`
    /// and `q < Q`.
    BadParams {
        /// Message characteristic `q`.
        message: u64,
        /// Encoding modulus `Q`.
        encoding: u64,
    },
    /// A proof / encoding component did not have the expected shape.
    Shape(&'static str),
}

impl fmt::Display for RegevError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoiseBudget {
                declared,
                ceiling,
            } => write!(
                f,
                "noise budget exhausted: {declared} >= ceiling {ceiling} (the encoding would decrypt wrongly)"
            ),
            Self::BadParams {
                message,
                encoding,
            } => write!(
                f,
                "invalid Γ = (q, Q): need coprime q < Q, got q = {message}, Q = {encoding}"
            ),
            Self::Shape(what) => write!(f, "malformed encoding: {what}"),
        }
    }
}

/// The secret key `sk = s`: one ring element of `R_Q = Z_Q[X]/(X^D+1)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegevKey<const Q: u64, const D: usize> {
    s: PolyRing<Zq<Q>, D>,
}

impl<const Q: u64, const D: usize> RegevKey<Q, D> {
    /// `Gen(1^κ, Γ)`: expands the secret from a seed (`s ← Z_Q^D`).
    pub fn gen<X: Xof>(seed: &[u8; 32]) -> Self {
        let mut xof = seed_stream::<X>(b"rinocchio-regev-gen", seed);
        Self {
            s: uniform_poly::<Zq<Q>, _, D>(&mut BitStream::new(&mut xof)),
        }
    }

    /// Borrows the secret. Public *within* the designated-verifier setting:
    /// the verifier holds `sk` and the setup's trapdoor.
    pub fn secret(&self) -> &PolyRing<Zq<Q>, D> {
        &self.s
    }
}

/// An encoding `C = (a_0, c_1) ∈ R_Q × R_Q` of one ring element, carrying the
/// prover's own bound on `‖q·e + m‖∞`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Encoding<const Q: u64, const D: usize> {
    /// First component `a_0 = −a`.
    pub a0: PolyRing<Zq<Q>, D>,
    /// Second component `c_1 = a·s + q·e + m`.
    pub c1: PolyRing<Zq<Q>, D>,
    /// Upper bound on the infinity norm of the *integer* noise `q·e + m`.
    pub noise_bound: u64,
}

impl<const Q: u64, const D: usize> Encoding<Q, D> {
    /// `(Q−1)/2`: the largest noise the centered decryption lift still
    /// recovers exactly.
    pub const CEILING: u64 = (Q - 1) / 2;
    /// Wire size of one encoding: two ring elements of `D` coefficients.
    pub const BYTES: usize = 2 * D * 8;
}

/// Padded coefficient list of a ring element (see
/// [`crate::qrp::pad_coefficients`] — repeated here so the two domains stay
/// independent).
fn coeffs<R: Ring, const D: usize>(p: &PolyRing<R, D>) -> Vec<R> {
    let mut c = p.coefficients();
    c.resize(D, R::ZERO);
    c
}

/// `Σ_i |c_i|` of a ring element with canonical representatives — the factor
/// the noise grows by under multiplication by `c`.
pub fn l1_norm<R: Ring, const D: usize>(p: &PolyRing<R, D>) -> u64 {
    coeffs::<R, D>(p)
        .iter()
        .fold(0u128, |acc, c| acc + c.to_u128())
        .try_into()
        .expect("an l1 norm of a ring element fits u64")
}

/// Embeds a message-ring element into the encoding ring coefficient-wise
/// (`Z_q → Z_Q`, injective because `q < Q`).
pub fn embed<const M: u64, const Q: u64, const D: usize>(
    p: &PolyRing<Zq<M>, D>,
) -> PolyRing<Zq<Q>, D> {
    PolyRing::from_coefficients(
        coeffs::<Zq<M>, D>(p)
            .iter()
            .map(|c| Zq::<Q>::new(c.to_u128() as u64))
            .collect(),
    )
}

fn zq_from_i128<const Q: u64>(v: i128) -> Zq<Q> {
    let q = i128::from(Q);
    Zq::<Q>::new(v.rem_euclid(q) as u64)
}

/// The noise budget of one *fresh* encoding with per-coefficient noise bound
/// `e_bound`: `q·e + m` reaches at most `q·e_bound + (q − 1)`.
pub const fn base_noise_bound(message: u64, e_bound: u64) -> u64 {
    message * e_bound + message - 1
}

fn check_params(message: u64, encoding: u64) -> Result<(), RegevError> {
    if message >= encoding || gcd_u64(message, encoding) != 1 {
        return Err(RegevError::BadParams { message, encoding });
    }
    Ok(())
}

/// `E_sk(m)`: samples `a ← R_Q` and a centered noise vector `e` from
/// `seed`, and returns `C = (−a, a·s + q·e + m)` together with its noise
/// bound [`base_noise_bound`].
///
/// # Errors
/// [`RegevError::BadParams`] if `Γ` violates `(q, Q) = 1` or `q < Q`;
/// [`RegevError::NoiseBudget`] if even a single fresh encoding cannot fit the
/// centered window (the noise parameter is too large for `Q`).
pub fn encode<const M: u64, const Q: u64, const D: usize, X: Xof>(
    sk: &RegevKey<Q, D>,
    seed: &[u8; 32],
    message: &PolyRing<Zq<M>, D>,
    e_bound: u32,
) -> Result<Encoding<Q, D>, RegevError> {
    check_params(M, Q)?;
    let bound = base_noise_bound(M, u64::from(e_bound));
    if bound >= Encoding::<Q, D>::CEILING {
        return Err(RegevError::NoiseBudget {
            declared: bound,
            ceiling: Encoding::<Q, D>::CEILING,
        });
    }
    let mut xof = seed_stream::<X>(b"rinocchio-regev-encode", seed);
    let a: PolyRing<Zq<Q>, D> = uniform_poly::<Zq<Q>, _, D>(&mut BitStream::new(&mut xof));
    let noise: Vec<i64> = coeffs::<Zq<M>, D>(message)
        .iter()
        .map(|_| sample_rej_bounded::<Zq<M>>(&mut BitStream::new(&mut xof), e_bound))
        .collect();
    let msg = coeffs::<Zq<M>, D>(message);
    let prod = a.clone() * sk.s.clone();
    let c1 = {
        let add: Vec<Zq<Q>> = noise
            .iter()
            .zip(msg.iter())
            .map(|(&e, &m)| {
                let n = i128::from(M) * i128::from(e) + m.to_u128() as i128;
                zq_from_i128::<Q>(n)
            })
            .collect();
        prod + PolyRing::from_coefficients(add)
    };
    Ok(Encoding {
        a0: -a,
        c1,
        noise_bound: bound,
    })
}

/// `D_sk(C)`: returns the plaintext and the recovered `‖q·e + m‖∞`.
///
/// The lift is the centered representative of `c_1 − a_0·s` in `(−Q/2, Q/2]`;
/// it equals the true integer noise exactly while `‖q·e + m‖∞ < Q/2`, which is
/// what [`Encoding::noise_bound`] tracks.
pub fn decrypt_with_noise<const M: u64, const Q: u64, const D: usize>(
    sk: &RegevKey<Q, D>,
    enc: &Encoding<Q, D>,
) -> (PolyRing<Zq<M>, D>, u64) {
    let a = -enc.a0.clone();
    let v = enc.c1.clone() - a * sk.s.clone();
    let mut msg = Vec::with_capacity(D);
    let mut inf = 0u64;
    for c in coeffs::<Zq<Q>, D>(&v) {
        let n = i128::from(c.centered());
        let m = n.rem_euclid(i128::from(M));
        let abs = if n < 0 {
            u64::try_from(-n).unwrap_or(u64::MAX)
        } else {
            u64::try_from(n).unwrap_or(u64::MAX)
        };
        inf = inf.max(abs);
        msg.push(Zq::<M>::new(m as u64));
    }
    (PolyRing::from_coefficients(msg), inf)
}

/// `D_sk(C)`: the plaintext ring element.
pub fn decrypt<const M: u64, const Q: u64, const D: usize>(
    sk: &RegevKey<Q, D>,
    enc: &Encoding<Q, D>,
) -> PolyRing<Zq<M>, D> {
    decrypt_with_noise::<M, Q, D>(sk, enc).0
}

/// Def. 8's **image verification**: `enc` is a valid encoding of *some* ring
/// element iff its recovered noise stayed inside the declared budget (an
/// encoding whose noise is larger is either out of the image or has already
/// wrapped into a different plaintext class).
pub fn image_ok<const M: u64, const Q: u64, const D: usize>(
    sk: &RegevKey<Q, D>,
    enc: &Encoding<Q, D>,
    budget: u64,
) -> bool {
    decrypt_with_noise::<M, Q, D>(sk, enc).1 <= budget
}

/// Def. 8's **ℓ-linear homomorphism**: `Eval(pk, (C_j), (r_j)) = Σ_j r_j·C_j`,
/// an encoding of `Σ_j r_j·m_j` whose noise bound is
/// `Σ_j ‖r_j₁ · bound_j`.
///
/// The ring scalar multiplies *both* components, so the noise grows by the
/// coefficient ℓ¹-norm of `r_j` — the `ℓ`-linearity the paper's "for any fixed
/// ℓ there is a choice of Γ" sentence is about.
///
/// # Errors
/// [`RegevError::NoiseBudget`] when the accumulated bound reaches the
/// centered window: the result would no longer decrypt to `Σ r_j·m_j`.
/// [`RegevError::Shape`] when the coefficient and encoding counts differ.
pub fn eval<const M: u64, const Q: u64, const D: usize>(
    coeffs_r: &[PolyRing<Zq<M>, D>],
    encs: &[Encoding<Q, D>],
) -> Result<Encoding<Q, D>, RegevError> {
    if coeffs_r.len() != encs.len() {
        return Err(RegevError::Shape("one ring scalar per encoding"));
    }
    let mut a0 = PolyRing::<Zq<Q>, D>::from_coefficients(vec![Zq::<Q>::ZERO; D]);
    let mut c1 = a0.clone();
    let mut bound: u128 = 0;
    for (r, enc) in coeffs_r.iter().zip(encs.iter()) {
        let rr = embed::<M, Q, D>(r);
        a0 += rr.clone() * enc.a0.clone();
        c1 += rr.clone() * enc.c1.clone();
        bound += u128::from(l1_norm::<Zq<M>, D>(r)) * u128::from(enc.noise_bound);
    }
    let ceiling = u128::from(Encoding::<Q, D>::CEILING);
    if bound >= ceiling {
        return Err(RegevError::NoiseBudget {
            declared: bound.min(u128::from(u64::MAX)) as u64,
            ceiling: Encoding::<Q, D>::CEILING,
        });
    }
    Ok(Encoding {
        a0,
        c1,
        noise_bound: bound as u64,
    })
}

/// A ring-linear form `Σ_i w_i·x_i + c` over the message ring, the summand of
/// Def. 8's quadratic polynomial `Q(x_1, …, x_t)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinForm<const M: u64, const D: usize> {
    /// Weights `w_i`, one per encoding handed to [`detect_quadratic_root`].
    pub weights: Vec<PolyRing<Zq<M>, D>>,
    /// Public constant term `c` (the verifier knows `s`, so it can form the
    /// input-wire contributions itself).
    pub offset: PolyRing<Zq<M>, D>,
}

impl<const M: u64, const D: usize> LinForm<M, D> {
    /// The zero form with the given offset.
    pub fn constant(c: PolyRing<Zq<M>, D>) -> Self {
        Self {
            weights: Vec::new(),
            offset: c,
        }
    }
}

/// A quadratic form `Σ_k L_k·R_k − Σ_k O_k` over the plaintexts hidden under
/// a list of encodings.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct QuadraticForm<const M: u64, const D: usize> {
    /// Left factors.
    pub left: Vec<LinForm<M, D>>,
    /// Right factors, one per left factor.
    pub right: Vec<LinForm<M, D>>,
    /// Subtrahend linear forms.
    pub out: Vec<LinForm<M, D>>,
}

impl<const M: u64, const D: usize> QuadraticForm<M, D> {
    /// The empty (always-zero) form.
    pub fn zero() -> Self {
        Self {
            left: Vec::new(),
            right: Vec::new(),
            out: Vec::new(),
        }
    }
}

/// Def. 8's **quadratic root detection**: using `sk`, decide whether
/// `Q(m_1, …, m_t) = 0` for the plaintexts under `encs`.
///
/// This is the capability the designated verifier is built from — no pairing,
/// no group, and crucially **no multiplication of encodings**: the verifier
/// decrypts first and multiplies in the clear, which is exactly why the
/// construction stays sound under the (conjectured) linear-only assumption
/// rather than needing one more assumption on top.
pub fn detect_quadratic_root<const M: u64, const Q: u64, const D: usize>(
    sk: &RegevKey<Q, D>,
    encs: &[Encoding<Q, D>],
    qf: &QuadraticForm<M, D>,
) -> bool {
    assert_eq!(
        qf.left.len(),
        qf.right.len(),
        "a quadratic form pairs its left and right factors"
    );
    let plain: Vec<PolyRing<Zq<M>, D>> = encs.iter().map(|e| decrypt::<M, Q, D>(sk, e)).collect();
    let zero = PolyRing::<Zq<M>, D>::from_coefficients(vec![Zq::<M>::ZERO; D]);
    let apply = |f: &LinForm<M, D>| {
        assert_eq!(
            f.weights.len(),
            plain.len(),
            "every linear form sees every encoded value"
        );
        let mut acc = f.offset.clone();
        for (w, p) in f.weights.iter().zip(plain.iter()) {
            acc += w.clone() * p.clone();
        }
        acc
    };
    let mut acc = zero.clone();
    for (l, r) in qf.left.iter().zip(qf.right.iter()) {
        acc += apply(l) * apply(r);
    }
    for o in &qf.out {
        acc -= apply(o);
    }
    acc == zero
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::crypto::xof::Shake128Xof;

    /// Message characteristic: `F_1009[X]/(X^4+1)` has zero divisors, so the
    /// encoded ring is a ring and not a field.
    const MQ: u64 = 1009;
    /// Encoding modulus `2^32 − 99`: prime, `≡ 5 (mod 8)`, **no NTT** — the
    /// house non-NTT instance, so every product here runs schoolbook.
    const EQ: u64 = 4_294_967_197;
    const E_BOUND: u32 = 1;
    const DIM: usize = 4;

    type Msg = Zq<MQ>;
    type Enc = Zq<EQ>;

    fn c<M: Ring, const D: usize>(v: u64) -> PolyRing<M, D> {
        PolyRing::from_coefficients(vec![M::from(v)])
    }

    fn msg(v: &[u64]) -> PolyRing<Msg, DIM> {
        assert_eq!(v.len(), DIM);
        PolyRing::from_coefficients(v.iter().map(|&x| Msg::from(x)).collect())
    }

    fn fresh(seed: u8) -> RegevKey<EQ, DIM> {
        let mut s = [0u8; 32];
        s[0] = seed;
        RegevKey::<EQ, DIM>::gen::<Shake128Xof>(&s)
    }

    fn enc_of(sk: &RegevKey<EQ, DIM>, tag: u8, m: &PolyRing<Msg, DIM>) -> Encoding<EQ, DIM> {
        let mut s = [0u8; 32];
        s[31] = tag;
        encode::<MQ, EQ, DIM, Shake128Xof>(sk, &s, m, E_BOUND).expect("encodes")
    }

    #[test]
    fn decryption_is_exact_and_recovers_the_declared_noise() {
        let sk = fresh(1);
        for k in 0..64u8 {
            let m = msg(&[u64::from(k), 3, 7, MQ - 1]);
            let e = enc_of(&sk, k, &m);
            let (got, inf) = decrypt_with_noise::<MQ, EQ, DIM>(&sk, &e);
            assert_eq!(got, m, "statistical correctness at k = {k}");
            assert!(
                inf <= e.noise_bound,
                "noise {inf} exceeded the declared bound {}",
                e.noise_bound
            );
            assert!(image_ok::<MQ, EQ, DIM>(&sk, &e, e.noise_bound));
        }
    }

    #[test]
    fn eval_is_ring_linear_and_stays_inside_the_budget() {
        let sk = fresh(2);
        let ms: Vec<_> = (0..3u8).map(|i| msg(&[i as u64 + 1, 5, 9, 3])).collect();
        let es: Vec<_> = ms
            .iter()
            .enumerate()
            .map(|(i, m)| enc_of(&sk, i as u8, m))
            .collect();
        let rs = vec![c::<Msg, DIM>(13), c::<Msg, DIM>(1), msg(&[2, 0, 1, 0])];
        let combined = eval::<MQ, EQ, DIM>(&rs, &es).expect("budget");
        let want = {
            let mut acc = c::<Msg, DIM>(0);
            for (r, m) in rs.iter().zip(ms.iter()) {
                acc = acc + r.clone() * m.clone();
            }
            acc
        };
        assert_eq!(decrypt::<MQ, EQ, DIM>(&sk, &combined), want);
        let manual = rs.iter().zip(es.iter()).fold(0u128, |acc, (r, e)| {
            acc + u128::from(l1_norm::<Msg, DIM>(r)) * u128::from(e.noise_bound)
        });
        assert_eq!(
            u128::from(combined.noise_bound),
            manual,
            "the bound must be the accumulated l1-weighted noise, not a guess"
        );
        assert!(u64::try_from(manual).is_ok());
    }

    #[test]
    fn an_oversized_noise_parameter_is_refused_at_encoding_time() {
        let sk = fresh(3);
        let mut s = [0u8; 32];
        s[0] = 9;
        // base_noise_bound(q, B) = q·B + q − 1 must stay under (Q−1)/2.
        let too_big = (EQ / 2 / MQ + 2) as u32;
        let err = encode::<MQ, EQ, DIM, Shake128Xof>(&sk, &s, &msg(&[1, 0, 0, 0]), too_big)
            .expect_err("must refuse");
        assert!(matches!(err, RegevError::NoiseBudget { .. }), "{err}");
        assert!(
            encode::<MQ, EQ, DIM, Shake128Xof>(&sk, &s, &msg(&[1, 0, 0, 0]), too_big - 8).is_ok(),
            "the refusal must sit at the window edge, not below it"
        );
    }

    #[test]
    fn eval_refuses_when_the_budget_is_exhausted() {
        let sk = fresh(4);
        let e = enc_of(&sk, 1, &msg(&[1, 2, 3, 4]));
        let scalar = c::<Msg, DIM>(MQ - 1);
        // `Σ_j ‖r_j‖₁ · bound_j` is the accumulation rule, with `‖r‖₁` the
        // unsigned coefficient sum — the conservative reading, since `−1`
        // written as `q − 1` is charged `q − 1`.
        let per_copy = u128::from(l1_norm::<Msg, DIM>(&scalar)) * u128::from(e.noise_bound);
        let ceiling = u128::from(Encoding::<EQ, DIM>::CEILING);
        assert!(per_copy > 0 && per_copy < ceiling, "one copy must fit");
        // `eval` refuses at `bound >= ceiling`, so the last copy count that
        // still fits is `(ceiling − 1) / per_copy`. Deriving it is the point:
        // this test used to assert that sixty copies blow the budget, and sixty
        // accumulate 121 988 160 of a 2 147 483 598 window — a factor of
        // seventeen short, so the assertion proved nothing about the bound.
        let last = usize::try_from((ceiling - 1) / per_copy).expect("a fixture-sized count");
        // `usize` has no `From` into `u128`, so widen through `u128::try_from`.
        let last_wide = u128::try_from(last).expect("a fixture-sized count");
        let scalars = || vec![scalar.clone(); last];
        let many = scalars();
        let es = vec![e.clone(); last];
        let sum = eval::<MQ, EQ, DIM>(&many, &es).expect("the last in-budget combination");
        assert_eq!(
            u128::from(sum.noise_bound),
            per_copy * last_wide,
            "the accumulated bound is exactly ℓ¹ × copies × base bound"
        );
        let mut over = scalars();
        over.push(scalar.clone());
        let mut over_es = es.clone();
        over_es.push(e.clone());
        let err = eval::<MQ, EQ, DIM>(&over, &over_es)
            .expect_err("one copy past the window must be refused");
        assert!(matches!(err, RegevError::NoiseBudget { .. }), "{err}");
        match err {
            RegevError::NoiseBudget { declared, ceiling: c } => {
                assert_eq!(c, Encoding::<EQ, DIM>::CEILING, "the reported window");
                assert_eq!(
                    u128::from(declared),
                    per_copy * (last_wide + 1),
                    "the refusal must name the bound it actually accumulated"
                );
            }
            other => panic!("expected a NoiseBudget refusal, got {other}"),
        }
        assert!(
            eval::<MQ, EQ, DIM>(&many[..3], &es[..3]).is_ok(),
            "a short combination must still succeed"
        );
    }

    #[test]
    fn noise_beyond_the_window_decrypts_to_a_different_element() {
        // The budget is not decoration: pushing the recovered value past the
        // centered window makes the lift wrap, and the encoding then decrypts
        // to a *wrong* plaintext rather than failing loudly.
        let sk = fresh(5);
        let m = msg(&[7, 0, 3, 1]);
        let e = enc_of(&sk, 1, &m);
        // The bump has to be past the window for *every* honest noise value,
        // `|M·e' + m| ≤ base_noise_bound(M, 1) = 2017`, and it must not be a
        // multiple of `M` — a multiple of `M` is invisible mod `M` and leaves
        // the plaintext alone, which is the next test's attack. This used to be
        // `300_000·M`, i.e. exactly that invisible bump, at a size (3.0e8) that
        // was nowhere near the 2.1e9 window either.
        let honest_max = base_noise_bound(MQ, u64::from(E_BOUND));
        let bump_value = Encoding::<EQ, DIM>::CEILING + honest_max + 31;
        let bump: PolyRing<Enc, DIM> =
            PolyRing::from_coefficients(vec![Enc::from(bump_value); DIM]);
        let blown = Encoding {
            a0: e.a0.clone(),
            c1: e.c1.clone() + bump,
            noise_bound: e.noise_bound,
        };
        let (got, inf) = decrypt_with_noise::<MQ, EQ, DIM>(&sk, &blown);
        assert!(inf > Encoding::<EQ, DIM>::CEILING / 4, "{inf}");
        assert!(inf <= Encoding::<EQ, DIM>::CEILING, "centered by definition");
        assert_ne!(got, m, "the wrapped lift must change the plaintext");
        assert!(!image_ok::<MQ, EQ, DIM>(&sk, &blown, e.noise_bound));
        // Mechanism, not just "different": every coefficient wrapped by
        // exactly one `Q`, so each recovered coordinate moved by
        // `(bump − Q) mod M`, uniformly and independently of the sampled noise.
        let shift = (i128::from(bump_value) - i128::from(EQ)).rem_euclid(i128::from(MQ)) as u64;
        assert_ne!(shift, 0, "a zero shift is the invisible bump again");
        let want: Vec<u64> = coeffs::<Msg, DIM>(&m)
            .iter()
            .map(|x| (x.to_u128() as u64 + shift) % MQ)
            .collect();
        let have: Vec<u64> = coeffs::<Msg, DIM>(&got)
            .iter()
            .map(|x| x.to_u128() as u64)
            .collect();
        assert_eq!(have, want, "each coordinate moved by exactly one wrapped Q");
    }

    #[test]
    fn a_multiple_of_q_added_to_c1_keeps_the_plaintext_but_breaks_the_image() {
        // The attack the image-verification property exists for: because the
        // noise enters as `q·e`, adding `q·z` to `c_1` leaves the decrypted
        // message *unchanged* while growing the noise. No equation over
        // plaintexts can see it — only the budget check can.
        let sk = fresh(6);
        let m = msg(&[11, 2, 5, 9]);
        let e = enc_of(&sk, 1, &m);
        let z: PolyRing<Enc, DIM> = PolyRing::from_coefficients(vec![Enc::from(100u64); DIM]);
        let re = Encoding {
            a0: e.a0.clone(),
            c1: e.c1.clone() + z * PolyRing::from_coefficients(vec![Enc::from(MQ); DIM]),
            noise_bound: e.noise_bound,
        };
        assert_eq!(decrypt::<MQ, EQ, DIM>(&sk, &re), m);
        assert!(!image_ok::<MQ, EQ, DIM>(&sk, &re, e.noise_bound));
    }

    #[test]
    fn quadratic_root_detection_decides_the_plaintext_relation() {
        let sk = fresh(7);
        let a = msg(&[3, 1, 4, 1]);
        let b = msg(&[5, 9, 2, 6]);
        let ea = enc_of(&sk, 1, &a);
        let eb = enc_of(&sk, 2, &b);
        // Q(x, y) = x*y - (a*b) = 0 on the actual plaintexts.
        let product = a.clone() * b.clone();
        let qf = QuadraticForm {
            left: vec![LinForm {
                weights: vec![c::<Msg, DIM>(1), c::<Msg, DIM>(0)],
                offset: c::<Msg, DIM>(0),
            }],
            right: vec![LinForm {
                weights: vec![c::<Msg, DIM>(0), c::<Msg, DIM>(1)],
                offset: c::<Msg, DIM>(0),
            }],
            out: vec![LinForm {
                weights: vec![c::<Msg, DIM>(0), c::<Msg, DIM>(0)],
                offset: product.clone(),
            }],
        };
        assert!(detect_quadratic_root::<MQ, EQ, DIM>(
            &sk,
            &[ea.clone(), eb.clone()],
            &qf
        ));
        let wrong = QuadraticForm {
            out: vec![LinForm {
                weights: vec![c::<Msg, DIM>(0), c::<Msg, DIM>(0)],
                offset: product + c::<Msg, DIM>(1),
            }],
            ..qf.clone()
        };
        assert!(!detect_quadratic_root::<MQ, EQ, DIM>(
            &sk,
            &[ea, eb],
            &wrong
        ));
    }

    #[test]
    fn the_parameters_are_checked() {
        // q | Q violates `(q, Q) = 1`: the noise would no longer be a
        // uniformly-hidden coset of the q-torsion, and decryption mod q would
        // be blind to the wrapping.
        let sk = RegevKey::<9, 2>::gen::<Shake128Xof>(&[0u8; 32]);
        let m = PolyRing::from_coefficients(vec![Zq::<3>::from(1u64)]);
        let err = encode::<3, 9, 2, Shake128Xof>(&sk, &[0u8; 32], &m, 1)
            .expect_err("q must be coprime to Q");
        assert_eq!(
            err,
            RegevError::BadParams {
                message: 3,
                encoding: 9
            }
        );
    }

    #[test]
    fn encoding_is_randomised_not_deterministic_in_the_message() {
        let sk = fresh(8);
        let m = msg(&[4, 4, 4, 4]);
        let a = enc_of(&sk, 1, &m);
        let b = enc_of(&sk, 2, &m);
        assert_ne!(a, b, "E must be probabilistic (semantic security)");
        assert_eq!(
            decrypt::<MQ, EQ, DIM>(&sk, &a),
            decrypt::<MQ, EQ, DIM>(&sk, &b)
        );
    }
}
