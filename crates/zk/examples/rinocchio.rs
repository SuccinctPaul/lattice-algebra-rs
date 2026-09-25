//! Rinocchio: SNARKs for Ring Arithmetic — Ganesh, Nitulescu and
//! Soria-Vazquez, eprint 2021/322, **Figure 1** — as a scheme assembly.
//!
//! This file holds no cryptographic logic. The relation is built by
//! [`zk::qrp`] (exceptional sets, Lagrange interpolation over a ring, monic
//! divisibility), and every "commitment" is produced and read by [`zk::encoding`]
//! (the §7.2 Regev / Ring-LWE encoding with its `Gen`/`E`/`D`, its ring-linear
//! `Eval`, its image verification and its quadratic root detection). What lives
//! here is the circuit, the SRS layout of Eq. (4), the nine proof elements, and
//! the three verification equations (5)–(7).
//!
//! # What this scheme is *not*, and the page says so explicitly
//!
//! * **Not ring-SIS.** The string "SIS" never occurs in the paper. Knowledge
//!   soundness (Theorem 3) is stated over the **generalized (4d+4)-PDH** and
//!   the **generalized augmented (4d+3)-PKE** assumptions for the encoding
//!   scheme, and §4.2 relates those to *linear-only extractability*: the paper
//!   proves that IND-CPA + linear-only extractable ⇒ both q-PDH and augmented
//!   q-PKE (Lemmas 4 and 5), notes that linear-only extractability is
//!   therefore "at least as strong", and then says of the Regev/TFHE/Joye-Libert
//!   candidates it actually uses that they are **conjectured** to be linear-only
//!   — "we have no proof of it being strictly stronger or equivalent". Nothing
//!   here pretends otherwise; there is no shortness argument, no norm gate and
//!   no SIS kernel vector anywhere in the verification path.
//! * **Not Fiat–Shamir, and not in the ROM.** There is no transcript, no
//!   challenge, no hashing of the proof. The proof is a plain 9-tuple and the
//!   argument is already non-interactive in the standard model.
//! * **Designated verifier.** `Verify(vk, u, π)` takes `vk = (sk, crs, s, α,
//!   α_v, α_w, α_y, β, r_v, r_w, r_y)`: the verifier holds the *encoding secret
//!   key* and the *setup trapdoor* and decrypts. That is what buys the quadratic
//!   check (7) without pairings — and it is also why the same CRS cannot be
//!   reused across proofs the way a public-coin one can (§2.1's leakage note).
//! * **Trusted, linear-size setup.** Eq. (4) is `2(d+1) + 7(m−ℓ)` encodings —
//!   linear in the witness, not constant, and `s` is sampled by a *trusted*
//!   party whose trapdoor survives into `vk`.
//! * **QRP, not QAP.** The program is a Quadratic *Ring* Program (Def. 7): the
//!   wire polynomials live in `R[x]` for a ring `R` with zero divisors, and the
//!   interpolation points come from an exceptional set, because over a ring the
//!   evaluation map `R[x]/(t) → R^d` is an isomorphism **iff** the points are
//!   exceptional (Proposition 2).
//!
//! # Instance
//!
//! `R = F_1009[X]/(X^4 + 1)` — a genuine ring, not a field: `1009 ≡ 1 (mod 8)`
//! makes 2 a square, so `X^4 + 1 = (X^2 + sX + 1)(X^2 − sX + 1)` splits and `R`
//! has zero divisors. Encodings live over `R_Q = Z_Q[X]/(X^4+1)` with
//! `Q = 2^32 − 99` (prime, `≡ 5 mod 8`, **no NTT**), which is coprime to 1009 as
//! §7.2's `Γ = (q, Q, n, α)` requires. Every ring product therefore runs on the
//! schoolbook negacyclic path.
//!
//! The toy numbers are for demonstration, not security: the soundness error is
//! `1/|A*|` (Theorem 3) and `A*` here is the 1006 nonzero constants of `F_1009`,
//! whereas §4.1 assumes an exceptional set *exponential* in `κ`; and the
//! Regev-style parameters are far inside the regime where Ring-LWE is hard.
//!
//! Not assembled here: §5.3's zk-Rinocchio (Fig. 2), which adds nine more CRS
//! encodings of `t(s)` and blinds `V_mid, W_mid, Y_mid` with `δ·t(s)`, and §6's
//! Groth16-like variant.
//!
//! Run with: `cargo run -p lattice-zk --example rinocchio`

use algebra::crypto::xof::{Shake256Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::{PolynomialQuotientRing, Ring};
use zk::encoding::{
    base_noise_bound, decrypt, detect_quadratic_root, embed, encode, eval, image_ok, Encoding,
    LinForm, QuadraticForm, RegevError, RegevKey,
};
use zk::foundation::fs::seed_stream;
use zk::qrp::{
    constant_inverse, nonzero_ring_element, ring_constant, ExceptionalSet, Gate, Qrp, RelPoly,
};

/// Message characteristic `q`: the computation ring is `F_q[X]/(X^D+1)`.
const QC: u64 = 1009;
/// Encoding modulus `Q` — `2^32 − 99`, prime, `≡ 5 (mod 8)`, no NTT.
const QE: u64 = 4_294_967_197;
/// Ring dimension `D`.
const D: usize = 4;
/// Per-coefficient noise bound `B_e` of a fresh encoding.
const E_BOUND: u32 = 1;

type M = Zq<QC>;
type R = PolyRing<M, D>;
type Enc = Encoding<QE, D>;
type Sk = RegevKey<QE, D>;

/// Noise ceiling of one fresh encoding: `q·B_e + (q − 1)`.
const BASE_NOISE: u64 = base_noise_bound(QC, E_BOUND as u64);

/// The demo circuit: three fan-in-2 multiplications over `R`,
/// `a3 = a1·a2`, `a4 = a3·a2`, `a5 = a4·a3`.
const GATES: [Gate; 3] = [
    Gate {
        left: 1,
        right: 2,
        out: 3,
    },
    Gate {
        left: 3,
        right: 2,
        out: 4,
    },
    Gate {
        left: 4,
        right: 3,
        out: 5,
    },
];
/// `m`: the program's wire count (wire `0` is the constant wire, `a_0 = 1`).
const WIRES: usize = 5;
/// `I_mid = ℓ+1, …, m`: the secret intermediate wires Fig. 1 encodes.
const MID: [usize; 2] = [3, 4];

/// The nine proof components, in Fig. 1's order. `X^` is the paper's `X̂`,
/// the `α`-blinded twin of `X`.
const NAMES: [&str; 9] = ["A", "A^", "B", "B^", "C", "C^", "D", "D^", "F"];

// Fig. 1's checks, named once so the prover, the verifier and the demo agree.
// `i0..i8` are Def. 8's image verification, per component.
const IMAGE: [&str; 9] = [
    "i0: A is in the image of E",
    "i1: A^ is in the image of E",
    "i2: B is in the image of E",
    "i3: B^ is in the image of E",
    "i4: C is in the image of E",
    "i5: C^ is in the image of E",
    "i6: D is in the image of E",
    "i7: D^ is in the image of E",
    "i8: F is in the image of E",
];
const E5A: &str = "5a: V^_mid = alpha_v*V_mid";
const E5B: &str = "5b: W^_mid = alpha_w*W_mid";
const E5C: &str = "5c: Y^_mid = alpha_y*Y_mid";
const E5D: &str = "5d: H^ = alpha*H";
const E6: &str = "6: L = beta*L_span";
const E7: &str = "7: P = H*t(s)";
const EQUATIONS: [&str; 6] = [E5A, E5B, E5C, E5D, E6, E7];

/// Derives a 32-byte sub-seed, so every encoding in the SRS and the proof gets
/// its own randomness from one setup seed.
fn subseed(seed: &[u8; 32], domain: &[u8]) -> [u8; 32] {
    let mut x = seed_stream::<Shake256Xof>(domain, seed);
    let v = x.squeeze_vec(32);
    v.as_slice()
        .try_into()
        .expect("SHAKE returns the requested length")
}

fn zero() -> R {
    ring_constant::<M, D>(M::ZERO)
}

fn one() -> R {
    ring_constant::<M, D>(M::ONE)
}

/// `Σ_k a_k · p_k(x)` evaluated at `x` — the setup's `v_k(s)` / the verifier's
/// `v_io(s)`.
fn combine_at(polys: &[RelPoly<M, D>], a: &[R], x: &R) -> R {
    RelPoly::linear_combination(a, polys).evaluate(x)
}

/// Eq. (4)'s structured reference string: `2(d+1) + 7(m−ℓ)` encodings.
///
/// Note what is *absent*: no encodings for the input/output wires. The
/// designated verifier knows `s`, so it evaluates `v_io(s)`, `w_io(s)`,
/// `y_io(s)` itself.
#[derive(Debug, Clone)]
struct Srs {
    /// `{E(s^i)}_{i=0}^{d}` — how the prover encodes an explicit polynomial.
    pow: Vec<Enc>,
    /// `{E(α·s^i)}_{i=0}^{d}` — the same for `D̂ = E(α·h(s))`.
    alpha_pow: Vec<Enc>,
    /// `{E(r_v·v_k(s))}`, `{E(r_w·w_k(s))}`, `{E(r_y·y_k(s))}` over `I_mid`.
    v: Vec<Enc>,
    w: Vec<Enc>,
    y: Vec<Enc>,
    /// `{E(α_v r_v v_k(s))}`, `{E(α_w r_w w_k(s))}`, `{E(α_y r_y y_k(s))}`.
    av: Vec<Enc>,
    aw: Vec<Enc>,
    ay: Vec<Enc>,
    /// `{E(β(r_v v_k(s) + r_w w_k(s) + r_y y_k(s)))}` — the span check.
    beta: Vec<Enc>,
}

impl Srs {
    /// Number of encodings in the SRS: `2(d+1) + 7(m−ℓ)`, linear in the
    /// witness, per Eq. (4).
    fn n_encodings(&self) -> usize {
        self.pow.len() + self.alpha_pow.len() + 7 * self.v.len()
    }

    fn bytes(&self) -> usize {
        self.n_encodings() * Enc::BYTES
    }
}

/// `vk = (sk, crs, s, α, α_v, α_w, α_y, β, r_v, r_w, r_y)` — the *private*
/// verification key. Everything in it except `crs` is the setup trapdoor.
#[derive(Debug, Clone)]
struct VerifierKey {
    sk: Sk,
    s: R,
    alpha: R,
    av: R,
    aw: R,
    ay: R,
    beta: R,
    rv: R,
    rw: R,
    ry: R,
    qrp: Qrp<M, D>,
    max_terms: usize,
}

impl VerifierKey {
    /// The verifier's noise budget for one proof component: at most
    /// `max_terms` ring-scalar products of fresh encodings, each of which
    /// multiplies the noise by the scalar's coefficient ℓ¹-norm (`≤ D·(q−1)`).
    fn budget(&self) -> u64 {
        (self.max_terms as u64) * (D as u64) * (QC - 1) * BASE_NOISE
    }
}

/// `π = (A, Â, B, B̂, C, Ĉ, D, D̂, F)` — nine encodings, linear in the witness.
#[derive(Debug, Clone)]
struct Proof {
    parts: [Enc; 9],
}

impl Proof {
    fn bytes(&self) -> usize {
        9 * Enc::BYTES
    }
}

/// Why a proof was rejected or could not be formed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum RinocchioError {
    /// A Fig. 1 verification equation, or a Def. 8 image test, failed.
    Rejected(&'static str),
    /// The witness does not satisfy the program, so `t ∤ VW − Y` and there is
    /// no quotient `h(x)` to encode.
    Unsatisfied,
    /// A homomorphic combination would push the noise out of the centered
    /// window, so the resulting encoding would not decrypt correctly.
    Budget(RegevError),
}

impl core::fmt::Display for RinocchioError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Rejected(what) => write!(f, "rejected: {what}"),
            Self::Unsatisfied => write!(f, "the witness does not satisfy the QRP"),
            Self::Budget(e) => write!(f, "noise budget: {e}"),
        }
    }
}

/// `Setup(1^κ, R)` — Fig. 1's left column. Trusted: the trapdoor
/// `(s, α, α_v, α_w, α_y, β, r_v, r_w, r_y)` is generated here and *kept*.
fn setup(seed: &[u8; 32]) -> (Srs, VerifierKey) {
    let set = ExceptionalSet::<M, D>::canonical(&(1..QC).map(M::from).collect::<Vec<_>>())
        .expect("the nonzero constants of a field are an exceptional set");
    let qrp = Qrp::from_gates(&GATES, WIRES, &set).expect("a 3-gate program over 6 wires");
    let d = qrp.degree();
    assert_eq!(d, GATES.len(), "one target root per multiplication gate");

    let sk = RegevKey::<QE, D>::gen::<Shake256Xof>(&subseed(seed, b"rinocchio:gen"));
    let s = set
        .draw_secret(d, b"rinocchio:s", seed)
        .expect("A* is nonempty");
    // r_v, r_w, α, α_v, α_w, α_y <- R*: every nonzero point of a canonical
    // exceptional set is a unit (Lemma 6), so drawing from A gives units.
    let rv = set.draw(b"rinocchio:rv", seed);
    let rw = set.draw(b"rinocchio:rw", seed);
    let alpha = set.draw(b"rinocchio:alpha", seed);
    let av = set.draw(b"rinocchio:av", seed);
    let aw = set.draw(b"rinocchio:aw", seed);
    let ay = set.draw(b"rinocchio:ay", seed);
    // beta <- R \ {0}: not required to be a unit, so it is a plain ring draw.
    let beta = nonzero_ring_element::<M, D>(b"rinocchio:beta", seed);
    let ry = rv.clone() * rw.clone();

    for (name, unit) in [
        ("s", &s),
        ("r_v", &rv),
        ("r_w", &rw),
        ("r_y", &ry),
        ("alpha", &alpha),
        ("alpha_v", &av),
        ("alpha_w", &aw),
        ("alpha_y", &ay),
    ] {
        assert!(
            constant_inverse::<M, D>(unit).is_some(),
            "Fig. 1 samples {name} from R*"
        );
    }

    let vs = qrp.v_at(&s);
    let ws = qrp.w_at(&s);
    let ys = qrp.y_at(&s);
    let mut pow = Vec::with_capacity(d + 1);
    let mut alpha_pow = Vec::with_capacity(d + 1);
    let mut s_pow = one();
    for i in 0..=d {
        pow.push(enc(&sk, seed, b"rinocchio:pow", i as u64, &s_pow));
        let a_s = alpha.clone() * s_pow.clone();
        alpha_pow.push(enc(&sk, seed, b"rinocchio:apow", i as u64, &a_s));
        s_pow = s_pow * s.clone();
    }
    let mut v = Vec::with_capacity(MID.len());
    let mut w = Vec::with_capacity(MID.len());
    let mut y = Vec::with_capacity(MID.len());
    let mut av_v = Vec::with_capacity(MID.len());
    let mut aw_w = Vec::with_capacity(MID.len());
    let mut ay_y = Vec::with_capacity(MID.len());
    let mut beta_span = Vec::with_capacity(MID.len());
    for (j, &k) in MID.iter().enumerate() {
        let vk_ = rv.clone() * vs[k].clone();
        let wk_ = rw.clone() * ws[k].clone();
        let yk_ = ry.clone() * ys[k].clone();
        v.push(enc(&sk, seed, b"rinocchio:v", j as u64, &vk_));
        w.push(enc(&sk, seed, b"rinocchio:w", j as u64, &wk_));
        y.push(enc(&sk, seed, b"rinocchio:y", j as u64, &yk_));
        av_v.push(enc(
            &sk,
            seed,
            b"rinocchio:av",
            j as u64,
            &(av.clone() * vk_.clone()),
        ));
        aw_w.push(enc(
            &sk,
            seed,
            b"rinocchio:aw",
            j as u64,
            &(aw.clone() * wk_.clone()),
        ));
        ay_y.push(enc(
            &sk,
            seed,
            b"rinocchio:ay",
            j as u64,
            &(ay.clone() * yk_.clone()),
        ));
        beta_span.push(enc(
            &sk,
            seed,
            b"rinocchio:beta",
            j as u64,
            &(beta.clone() * (vk_ + wk_ + yk_)),
        ));
    }
    let crs = Srs {
        pow,
        alpha_pow,
        v,
        w,
        y,
        av: av_v,
        aw: aw_w,
        ay: ay_y,
        beta: beta_span,
    };
    let max_terms = MID.len().max(d - 1);
    let vk = VerifierKey {
        sk,
        s,
        alpha,
        av,
        aw,
        ay,
        beta,
        rv,
        rw,
        ry,
        qrp,
        max_terms,
    };
    (crs, vk)
}

/// One fresh encoding from the setup's coins.
fn enc(sk: &Sk, seed: &[u8; 32], domain: &[u8], idx: u64, m: &R) -> Enc {
    let mut tag = Vec::from(domain);
    tag.extend_from_slice(&idx.to_le_bytes());
    encode::<QC, QE, D, Shake256Xof>(sk, &subseed(seed, &tag), m, E_BOUND)
        .expect("a fresh encoding fits the noise window")
}

/// `Prove(crs, u, w)` — Fig. 1's middle column. The prover sees **only** the
/// SRS: never `s`, `α`, `β`, `r_v`, and never the encoding secret key.
fn prove(qrp: &Qrp<M, D>, crs: &Srs, a: &[R]) -> Result<Proof, RinocchioError> {
    let mid: Vec<R> = MID.iter().map(|&k| a[k].clone()).collect();
    let e = |r: Result<Enc, RegevError>| r.map_err(RinocchioError::Budget);
    let a_enc = e(eval::<QC, QE, D>(&mid, &crs.v))?;
    let ah = e(eval::<QC, QE, D>(&mid, &crs.av))?;
    let b_enc = e(eval::<QC, QE, D>(&mid, &crs.w))?;
    let bh = e(eval::<QC, QE, D>(&mid, &crs.aw))?;
    let c_enc = e(eval::<QC, QE, D>(&mid, &crs.y))?;
    let ch = e(eval::<QC, QE, D>(&mid, &crs.ay))?;
    // h(x) = (v(x)w(x) - y(x)) / t(x): the prover needs the *polynomial*,
    // because D = E(h(s)) is formed homomorphically from {E(s^i)}.
    let h = qrp.quotient(a).ok_or(RinocchioError::Unsatisfied)?;
    let hc: Vec<R> = (0..h.n_terms()).map(|i| h.coeff(i)).collect();
    let d_enc = e(eval::<QC, QE, D>(&hc, &crs.pow[..hc.len()]))?;
    let dh = e(eval::<QC, QE, D>(&hc, &crs.alpha_pow[..hc.len()]))?;
    let f = e(eval::<QC, QE, D>(&mid, &crs.beta))?;
    Ok(Proof {
        parts: [a_enc, ah, b_enc, bh, c_enc, ch, d_enc, dh, f],
    })
}

/// Every check Fig. 1 prints, evaluated without short-circuiting, so a tamper
/// reports the whole set it trips rather than the first one.
fn failing(vk: &VerifierKey, u: &[R], pi: &Proof) -> Vec<&'static str> {
    let mut bad = Vec::new();
    let budget = vk.budget();
    for (i, name) in IMAGE.iter().enumerate() {
        if !image_ok::<QC, QE, D>(&vk.sk, &pi.parts[i], budget) {
            bad.push(*name);
        }
    }
    // The designated verifier decrypts: this is what no public-coin reader
    // holding only `crs` can do.
    let dec: Vec<R> = pi
        .parts
        .iter()
        .map(|c| decrypt::<QC, QE, D>(&vk.sk, c))
        .collect();
    let rv_inv = constant_inverse::<M, D>(&vk.rv).expect("r_v is a unit");
    let rw_inv = constant_inverse::<M, D>(&vk.rw).expect("r_w is a unit");
    let ry_inv = constant_inverse::<M, D>(&vk.ry).expect("r_y = r_v*r_w is a unit");
    let v_mid = rv_inv.clone() * dec[0].clone();
    let v_hat = rv_inv.clone() * dec[1].clone();
    let w_mid = rw_inv.clone() * dec[2].clone();
    let w_hat = rw_inv.clone() * dec[3].clone();
    let y_mid = ry_inv.clone() * dec[4].clone();
    let y_hat = ry_inv.clone() * dec[5].clone();
    let h = dec[6].clone();
    let h_hat = dec[7].clone();
    if v_hat != vk.av.clone() * v_mid {
        bad.push(E5A);
    }
    if w_hat != vk.aw.clone() * w_mid {
        bad.push(E5B);
    }
    if y_hat != vk.ay.clone() * y_mid {
        bad.push(E5C);
    }
    if h_hat != vk.alpha.clone() * h {
        bad.push(E5D);
    }
    // (6): L = beta * L_span, with L_span = r_v V_mid + r_w W_mid + r_y Y_mid,
    // i.e. the sum of the three *decrypted* components (no de-blinding needed).
    let l_span = dec[0].clone() + dec[2].clone() + dec[4].clone();
    if dec[8] != vk.beta.clone() * l_span {
        bad.push(E6);
    }
    // (7): P = (v_io(s) + V_mid)(w_io(s) + W_mid) - (y_io(s) + Y_mid) = H*t(s).
    // This is exactly Def. 8's quadratic root detection: the verifier decrypts,
    // then multiplies in the clear — no pairing, and no multiplication of two
    // encodings (which is what the linear-only conjecture forbids).
    let ts = vk.qrp.t.evaluate(&vk.s);
    let vio = combine_at(&vk.qrp.v, u, &vk.s);
    let wio = combine_at(&vk.qrp.w, u, &vk.s);
    let yio = combine_at(&vk.qrp.y, u, &vk.s);
    let at = |slot: usize, w: R| -> Vec<R> {
        let mut v = vec![zero(); 9];
        v[slot] = w;
        v
    };
    let qf = QuadraticForm {
        left: vec![LinForm {
            weights: at(0, rv_inv),
            offset: vio,
        }],
        right: vec![LinForm {
            weights: at(2, rw_inv),
            offset: wio,
        }],
        out: vec![
            LinForm {
                weights: at(4, ry_inv),
                offset: yio,
            },
            LinForm {
                weights: at(6, ts),
                offset: zero(),
            },
        ],
    };
    if !detect_quadratic_root::<QC, QE, D>(&vk.sk, &pi.parts, &qf) {
        bad.push(E7);
    }
    bad
}

/// `Verify(vk, u, π)`.
fn verify(vk: &VerifierKey, u: &[R], pi: &Proof) -> Result<(), RinocchioError> {
    let bad = failing(vk, u, pi);
    match bad.first() {
        Some(what) => Err(RinocchioError::Rejected(what)),
        None => Ok(()),
    }
}

/// The witness: the public inputs plus the intermediate wires they force.
fn witness() -> (Vec<R>, Vec<R>) {
    let a1 =
        PolyRing::from_coefficients(vec![M::from(3u64), M::from(1u64), M::ZERO, M::from(2u64)]);
    let a2 =
        PolyRing::from_coefficients(vec![M::from(5u64), M::ZERO, M::from(2u64), M::from(1u64)]);
    let a3 = a1.clone() * a2.clone();
    let a4 = a3.clone() * a2.clone();
    let a5 = a4.clone() * a3.clone();
    let a = vec![one(), a1, a2, a3, a4, a5];
    let mut u = a.clone();
    for &k in &MID {
        u[k] = zero();
    }
    (a, u)
}

/// Adds a ring element to one component's second encoding slot.
fn bump(pi: &Proof, i: usize, delta: &R) -> Proof {
    let mut parts = pi.parts.clone();
    parts[i].c1 = parts[i].c1.clone() + embed::<QC, QE, D>(delta);
    Proof { parts }
}

/// Adds `q·z` to a component: because the noise enters as `q·e`, this leaves
/// the decrypted plaintext *exactly* where it was and grows only the noise —
/// until `z` is large enough to leave the centered window.
fn inject_noise(pi: &Proof, i: usize, z: u64) -> Proof {
    let mut parts = pi.parts.clone();
    let lifted: PolyRing<Zq<QE>, D> = PolyRing::from_coefficients(vec![Zq::<QE>::new(z * QC); D]);
    parts[i].c1 = parts[i].c1.clone() + lifted;
    Proof { parts }
}

/// Asserts a tamper is rejected, that the set of failing checks is *exactly*
/// `expected`, and that `verify` attributes it to the first one.
fn expect_reject(label: &str, vk: &VerifierKey, u: &[R], pi: &Proof, expected: &[&str]) {
    let bad = failing(vk, u, pi);
    assert!(!bad.is_empty(), "{label}: the tamper was accepted");
    let mut got = bad.clone();
    got.sort_unstable();
    got.dedup();
    let mut want = expected.to_vec();
    want.sort_unstable();
    want.dedup();
    assert_eq!(got, want, "{label}: failing set");
    match verify(vk, u, pi) {
        Err(RinocchioError::Rejected(name)) => assert_eq!(name, bad[0], "{label}: attribution"),
        other => panic!("{label}: expected a rejection, got {other:?}"),
    }
    println!("  {label}: rejected by {bad:?}");
}

fn main() {
    let seed = [0x21u8; 32];
    let (crs, vk) = setup(&seed);
    let (a, u) = witness();

    assert!(
        vk.qrp.is_satisfied(&a),
        "the demo trace must satisfy the program"
    );
    let mut wrong_wire = a.clone();
    wrong_wire[5] = wrong_wire[5].clone() + one();
    assert!(
        !vk.qrp.is_satisfied(&wrong_wire),
        "a wrong output wire must not satisfy the program"
    );

    let proof = prove(&vk.qrp, &crs, &a).expect("honest proof");
    verify(&vk, &u, &proof).expect("honest proof rejected");
    let a_star = QC as usize - GATES.len();
    println!(
        "Rinocchio 2021/322 Fig. 1 — R = F_{QC}[X]/(X^{D}+1) (has zero divisors); \
         encodings over Z_{QE} (prime, 5 mod 8, no NTT)"
    );
    println!(
        "  program: m = {WIRES} wires, d = {} gates, |A*| = {a_star}, soundness error 1/{a_star} (toy)",
        GATES.len()
    );
    println!(
        "  trusted SRS: {} encodings = {} bytes (linear in the witness); proof: 9 encodings = {} bytes",
        crs.n_encodings(),
        crs.bytes(),
        proof.bytes()
    );
    println!(
        "  designated verifier holds sk + (s, alpha, alpha_v, alpha_w, alpha_y, beta, r_v, r_w, r_y); no transcript, no ROM"
    );
    println!("  checks: Def. 8 image verification {IMAGE:?} then Fig. 1's equations {EQUATIONS:?}");
    println!(
        "  honest proof verifies; widest component uses {} of the {} noise budget",
        proof
            .parts
            .iter()
            .map(|c| c.noise_bound)
            .max()
            .unwrap_or_default(),
        vk.budget()
    );

    // Each of the nine encodings, tampered on its own, is caught by the
    // equations it actually appears in — never by "some check".
    let unit = PolyRing::from_coefficients(vec![M::ONE]);
    for i in 0..9 {
        let bad = bump(&proof, i, &unit);
        let expected: &[&str] = match i {
            0 => &[E5A, E6, E7],
            1 => &[E5A],
            2 => &[E5B, E6, E7],
            3 => &[E5B],
            4 => &[E5C, E6, E7],
            5 => &[E5C],
            6 => &[E5D, E7],
            7 => &[E5D],
            _ => &[E6],
        };
        expect_reject(&format!("tampered {}", NAMES[i]), &vk, &u, &bad, expected);
    }

    // The noise budget is load-bearing. Adding q*z to a component leaves the
    // decrypted plaintext *exactly* where it was, so no equation over
    // plaintexts can see it: only Def. 8's image verification does.
    for i in [0usize, 4, 7, 8] {
        let bad = inject_noise(&proof, i, 200_000);
        let got = failing(&vk, &u, &bad);
        assert_eq!(got, vec![IMAGE[i]], "noise injection on {}", NAMES[i]);
        assert_eq!(
            decrypt::<QC, QE, D>(&vk.sk, &bad.parts[i]),
            decrypt::<QC, QE, D>(&vk.sk, &proof.parts[i]),
            "the tamper must preserve the plaintext, or the image check is not what caught it"
        );
        println!(
            "  re-randomised {} beyond the budget: rejected by {got:?} (plaintext unchanged)",
            NAMES[i]
        );
    }

    // ... and once the noise leaves the centered window entirely, the encoding
    // decrypts to a *different* ring element and the equations fire too: the
    // budget is what makes the encoding statistically correct.
    let blown = inject_noise(&proof, 0, 2_200_000);
    let got = failing(&vk, &u, &blown);
    assert!(
        got.contains(&E5A) && got.contains(&E6) && got.contains(&E7),
        "{got:?}"
    );
    assert_ne!(
        decrypt::<QC, QE, D>(&vk.sk, &blown.parts[0]),
        decrypt::<QC, QE, D>(&vk.sk, &proof.parts[0]),
        "a wrapped noise lift must change the plaintext"
    );
    println!("  noise past (Q-1)/2 on A: rejected by {got:?} (plaintext wrapped)");

    // A prover that picks its fresh noise parameter outside the window never
    // gets as far as a proof.
    let too_big = (QE / 2 / QC + 2) as u32;
    let err = encode::<QC, QE, D, Shake256Xof>(&vk.sk, &subseed(&seed, b"x"), &zero(), too_big)
        .expect_err("q*B_e + q - 1 must stay under (Q-1)/2");
    assert!(matches!(err, RegevError::NoiseBudget { .. }), "{err}");
    println!("  encoding with B_e = {too_big}: refused inside E_sk ({err})");

    // A false statement: the claim enters only through equation (7).
    let mut wrong_out = u.clone();
    wrong_out[5] = wrong_out[5].clone() + one();
    expect_reject("false public output", &vk, &wrong_out, &proof, &[E7]);
    let mut wrong_in = u.clone();
    wrong_in[1] = wrong_in[1].clone() + one();
    expect_reject("false public input", &vk, &wrong_in, &proof, &[E7]);

    // A witness that does not satisfy the circuit cannot produce a proof at
    // all: t(x) does not divide V(x)W(x) - Y(x).
    let mut cheating = a.clone();
    cheating[4] = cheating[4].clone() + one();
    assert_eq!(
        prove(&vk.qrp, &crs, &cheating).err(),
        Some(RinocchioError::Unsatisfied),
        "an inconsistent trace must have no quotient"
    );
    println!("  inconsistent witness: no h(x) with t | VW-Y, so no proof to send");

    println!("  every tamper is rejected by the checks it actually violates");
}
