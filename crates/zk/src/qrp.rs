//! Quadratic Ring Programs: the "QAP over rings" relation layer (L5).
//!
//! This is the information-theoretic half of a ring SNARK — the object a
//! *public-coin* QAP argument also uses, but here the coefficient ring is an
//! arbitrary finite commutative ring with identity, not a field. Everything in
//! this module therefore avoids field-only operations:
//!
//! - the target polynomial `t(x) = Π_g (x − r_g)` is **monic**, so divisibility
//!   `t | p` is decided by long division that never inverts anything
//!   ([`RelPoly::div_rem_monic`]);
//! - interpolation runs over an [`ExceptionalSet`] (Def. 5), i.e. a point set
//!   whose *pairwise differences are units* — exactly the hypothesis the
//!   generalized Schwartz–Zippel lemma (eprint 2021/322, §2.3 Lemma 2) and
//!   the CRT isomorphism `R[x]/(t) ≅ Π R[x]/(x−r_g)`
//!   (§3, Eq. 2) need. Proposition 2 of that paper shows the requirement is
//!   *necessary*: without it the evaluation map is not injective and
//!   "`t` divides `p`" stops meaning "`p` vanishes on the roots".
//!
//! The relation (Def. 7): an assignment `a_0 = 1, a_1, …, a_m` satisfies the
//! program iff `t(x)` divides `V(x)·W(x) − Y(x)` with
//! `V = Σ a_k v_k`, `W = Σ a_k w_k`, `Y = Σ a_k y_k`.
//!
//! [`Qrp::from_gates`] implements the per-gate construction of Theorem 6
//! (one multiplication gate ⇒ degree-1 target, indicator wire polynomials)
//! composed by Theorem 7/8 into a program for a whole fan-in-2 circuit.
//!
//! # Division by the target is exact, not approximate
//!
//! [`Qrp::quotient`] returns `None` unless the remainder is *the zero
//! polynomial*; a scheme that accepted an approximate or partial quotient
//! would silently weaken the reduction from "false proof" to "q-PDH
//! challenge" (Lemma 7 there).

use crate::foundation::fs::seed_stream;
use crate::foundation::sampling::uniform_ring_from_seed;
use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::Field;
use algebra::ring::{PolynomialQuotientRing, Ring};
use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, AddAssign, Mul, Sub};

/// One fan-in-2 multiplication gate: `a_out = a_left · a_right`.
///
/// Wire index `0` is the reserved constant wire, which every program fixes to
/// the ring's identity (Def. 7's `a_0 = 1`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Gate {
    /// Left input wire.
    pub left: usize,
    /// Right input wire.
    pub right: usize,
    /// Output wire.
    pub out: usize,
}

/// Padded coefficient list of a ring element.
///
/// [`PolyRing::coefficients`] trims trailing zeros, so every caller that
/// needs the `D`-vector view of an element has to re-pad it; this is the one
/// place that knows how.
pub fn pad_coefficients<R: Ring, const D: usize>(p: &PolyRing<R, D>) -> Vec<R> {
    let mut c = p.coefficients();
    c.resize(D, R::ZERO);
    c
}

/// The constant polynomial `c` of `R[X]/(X^D + 1)`.
pub fn ring_constant<R: Ring, const D: usize>(c: R) -> PolyRing<R, D> {
    PolyRing::from_coefficients(vec![c])
}

/// The inverse of `p` inside `R[X]/(X^D+1)` **when `p` is a nonzero
/// constant**, else `None`.
///
/// Deliberately narrow: a program only ever inverts exceptional-set
/// differences, target-polynomial evaluations at a non-root, and the setup's
/// blinding scalars, all of which are constants by construction. Inverting a
/// general element of `R[X]/(X^D+1)` needs extended Euclid against `X^D+1`
/// and is not used here.
pub fn constant_inverse<R: Field, const D: usize>(p: &PolyRing<R, D>) -> Option<PolyRing<R, D>> {
    let c = pad_coefficients::<R, D>(p);
    if c[1..].iter().any(|v| *v != R::ZERO) {
        return None;
    }
    c[0].inverse().map(|inv| ring_constant::<R, D>(inv))
}

/// A univariate polynomial whose coefficients are elements of
/// `R_D = R[X]/(X^D + 1)`.
///
/// This is `R_D[x]` — the ring the QRP's `v_k`, `w_k`, `y_k`, `t` live in.
/// Trailing zero coefficients are trimmed, so `PartialEq` is canonical.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RelPoly<R: Ring, const D: usize> {
    c: Vec<PolyRing<R, D>>,
}

impl<R: Ring, const D: usize> RelPoly<R, D> {
    /// The zero polynomial.
    pub fn zero() -> Self {
        Self {
            c: vec![ring_constant::<R, D>(R::ZERO)],
        }
    }

    /// The constant-one polynomial.
    pub fn one() -> Self {
        Self {
            c: vec![ring_constant::<R, D>(R::ONE)],
        }
    }

    /// Builds from ascending coefficients, trimming trailing zeros.
    pub fn from_coefficients(c: Vec<PolyRing<R, D>>) -> Self {
        let mut c = c;
        while c.len() > 1 && c[c.len() - 1] == ring_constant::<R, D>(R::ZERO) {
            c.pop();
        }
        if c.is_empty() {
            c.push(ring_constant::<R, D>(R::ZERO));
        }
        Self { c }
    }

    /// The `x^i` coefficient (zero beyond the degree).
    pub fn coeff(&self, i: usize) -> PolyRing<R, D> {
        self.c
            .get(i)
            .cloned()
            .unwrap_or_else(|| ring_constant::<R, D>(R::ZERO))
    }

    /// Number of stored coefficients: `degree() + 1`.
    pub fn n_terms(&self) -> usize {
        self.c.len()
    }

    /// Whether this is the zero polynomial.
    pub fn is_zero(&self) -> bool {
        self.c.len() == 1 && self.c[0] == ring_constant::<R, D>(R::ZERO)
    }

    /// `degree()`, with the zero polynomial at degree 0 (matching
    /// [`algebra::poly::UniPolynomial::degree`]).
    pub fn degree(&self) -> usize {
        self.c.len() - 1
    }

    /// The leading `x^degree()` coefficient.
    pub fn leading(&self) -> PolyRing<R, D> {
        self.c[self.c.len() - 1].clone()
    }

    /// Horner evaluation at `s`.
    pub fn evaluate(&self, s: &PolyRing<R, D>) -> PolyRing<R, D> {
        self.c
            .iter()
            .rev()
            .fold(ring_constant::<R, D>(R::ZERO), |acc, c| {
                acc * s.clone() + c.clone()
            })
    }

    /// `Σ_k a_k · p_k(x)` — the prover's and verifier's wire combination.
    pub fn linear_combination(coeffs: &[PolyRing<R, D>], polys: &[RelPoly<R, D>]) -> Self {
        assert_eq!(
            coeffs.len(),
            polys.len(),
            "one coefficient per wire polynomial"
        );
        let mut acc = vec![ring_constant::<R, D>(R::ZERO)];
        for (a, p) in coeffs.iter().zip(polys.iter()) {
            for (i, b) in p.c.iter().enumerate() {
                while acc.len() <= i {
                    acc.push(ring_constant::<R, D>(R::ZERO));
                }
                acc[i] = acc[i].clone() + a.clone() * b.clone();
            }
        }
        Self::from_coefficients(acc)
    }

    /// `(q, r)` with `self = q · t + r` and `r` zero or of smaller length than
    /// `t`. Requires `t` **monic** — the only ring operation long division
    /// needs, which is why the layer works over rings with zero divisors.
    ///
    /// # Panics
    /// If `t` is not monic.
    pub fn div_rem_monic(&self, t: &Self) -> (Self, Self) {
        assert!(
            t.leading() == ring_constant::<R, D>(R::ONE),
            "long division here needs a monic divisor"
        );
        let mut rem = self.c.clone();
        let n = t.c.len();
        if rem.len() < n {
            return (Self::zero(), Self::from_coefficients(rem));
        }
        let mut q = vec![ring_constant::<R, D>(R::ZERO); rem.len() - n + 1];
        for i in (0..q.len()).rev() {
            let coef = rem[i + n - 1].clone();
            q[i] = coef.clone();
            if coef == ring_constant::<R, D>(R::ZERO) {
                continue;
            }
            for (j, tj) in t.c.iter().enumerate() {
                let sub = coef.clone() * tj.clone();
                rem[i + j] = rem[i + j].clone() - sub;
            }
        }
        (Self::from_coefficients(q), Self::from_coefficients(rem))
    }

    /// The exact quotient `self / t`, or `None` when `t` does not divide
    /// `self`. Panics if `t` is not monic (see [`Self::div_rem_monic`]).
    pub fn div_exact(&self, t: &Self) -> Option<Self> {
        let (q, r) = self.div_rem_monic(t);
        r.is_zero().then_some(q)
    }

    /// `x − r`.
    pub fn linear_factor(r: &PolyRing<R, D>) -> Self {
        Self::from_coefficients(vec![-r.clone(), ring_constant::<R, D>(R::ONE)])
    }
}

impl<R: Ring, const D: usize> Add for RelPoly<R, D> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self {
        let n = self.c.len().max(rhs.c.len());
        self.c.resize(n, ring_constant::<R, D>(R::ZERO));
        for (i, b) in rhs.c.into_iter().enumerate() {
            self.c[i] = self.c[i].clone() + b;
        }
        Self::from_coefficients(self.c)
    }
}

impl<R: Ring, const D: usize> Sub for RelPoly<R, D> {
    type Output = Self;
    fn sub(mut self, rhs: Self) -> Self {
        let n = self.c.len().max(rhs.c.len());
        self.c.resize(n, ring_constant::<R, D>(R::ZERO));
        for (i, b) in rhs.c.into_iter().enumerate() {
            self.c[i] = self.c[i].clone() - b;
        }
        Self::from_coefficients(self.c)
    }
}

impl<R: Ring, const D: usize> Mul for RelPoly<R, D> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        if self.is_zero() || rhs.is_zero() {
            return Self::zero();
        }
        let mut acc = vec![ring_constant::<R, D>(R::ZERO); self.c.len() + rhs.c.len() - 1];
        for (i, a) in self.c.iter().enumerate() {
            for (j, b) in rhs.c.iter().enumerate() {
                acc[i + j] = acc[i + j].clone() + a.clone() * b.clone();
            }
        }
        Self::from_coefficients(acc)
    }
}

impl<R: Ring, const D: usize> AddAssign for RelPoly<R, D> {
    fn add_assign(&mut self, rhs: Self) {
        *self = self.clone() + rhs;
    }
}

/// A canonical exceptional set `A = {0, a_1, …, a_{n−1}}` of
/// `R_D = R[X]/(X^D+1)` (Def. 5, Lemma 6).
///
/// "Canonical" is Lemma 6's normal form: the first point is `0` and every
/// other point is a unit, so `A* = A \ A_Q ⊂ R*` — the restriction the
/// generalized q-PDH / q-PKE assumptions and the `1/|A*|` soundness error are
/// stated over.
///
/// The points are built as **constants** of `R_D` from distinct nonzero
/// scalars of `R`. That is the ring analogue of the paper's `A = F ⊂ R` for
/// polynomial-wire programs (§A.1) and of the prime-ring "NTT-slot diagonal"
/// challenge set in [`crate::foundation::sampling::diagonal_set_poly`]: two
/// distinct constants differ in a nonzero scalar, which is a unit of
/// `R_D`, so the exceptional property is *structural* rather than
/// probabilistic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExceptionalSet<R: Ring, const D: usize> {
    points: Vec<PolyRing<R, D>>,
}

impl<R: Field, const D: usize> ExceptionalSet<R, D> {
    /// Builds `{0} ∪ {scalars}` and *verifies* Def. 5 by inverting every
    /// pairwise difference.
    ///
    /// Returns `None` if a scalar is zero or two scalars coincide — either
    /// breaks the unit-difference property the interpolation and the CRT
    /// argument rest on.
    pub fn canonical(scalars: &[R]) -> Option<Self> {
        let zero = ring_constant::<R, D>(R::ZERO);
        let mut points = vec![zero];
        for s in scalars {
            if *s == R::ZERO {
                return None;
            }
            points.push(ring_constant::<R, D>(*s));
        }
        for i in 0..points.len() {
            for j in 0..points.len() {
                if i != j
                    && constant_inverse::<R, D>(&(points[i].clone() - points[j].clone())).is_none()
                {
                    return None;
                }
            }
        }
        Some(Self { points })
    }

    /// All points, `A[0] == 0`.
    pub fn points(&self) -> &[PolyRing<R, D>] {
        &self.points
    }

    /// `|A|`.
    pub fn len(&self) -> usize {
        self.points.len()
    }

    /// Whether the set is empty (never for a constructed set; required
    /// alongside [`Self::len`]).
    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    /// `A_Q = {0, a_1, …, a_{d−1}}`: the `d` gate roots, i.e. the roots of the
    /// target polynomial.
    ///
    /// The set must carry `d` roots **and** leave one point over for `A*`, so
    /// the boundary is `|A| = d + 1`: a three-gate program on `{0, 3, 5, 7}` is
    /// the smallest legal instance, and the guard used to read `<= d + 1`,
    /// which rejected exactly that. `secret_points` below documents that
    /// `A* ≠ ∅` whenever this succeeds, which only holds at the relaxed bound.
    pub fn gate_roots(&self, d: usize) -> Option<&[PolyRing<R, D>]> {
        if self.points.len() < d + 1 {
            return None; // need every root *plus* at least one secret point
        }
        Some(&self.points[..d])
    }

    /// `A* = A \ A_Q` — the pool the setup draws the secret point `s` from.
    /// Nonempty whenever [`Self::gate_roots`] succeeds.
    pub fn secret_points(&self, d: usize) -> Option<&[PolyRing<R, D>]> {
        if self.points.len() < d + 1 {
            return None;
        }
        Some(&self.points[d..])
    }

    /// The Lagrange basis of the first `d` points: `L_g(r_h) = δ_{g,h}`.
    ///
    /// `None` when the points are not exceptional (a denominator fails to
    /// invert), which is Proposition 2's contrapositive: without the
    /// exceptional property this map is not an isomorphism and the basis does
    /// not exist.
    pub fn lagrange_basis(&self, d: usize) -> Option<Vec<RelPoly<R, D>>> {
        let roots = self.gate_roots(d)?;
        let mut out = Vec::with_capacity(d);
        for g in 0..d {
            let mut num = RelPoly::<R, D>::one();
            let mut den = ring_constant::<R, D>(R::ONE);
            for h in 0..d {
                if h == g {
                    continue;
                }
                num = num * RelPoly::linear_factor(&roots[h].clone());
                den *= roots[g].clone() - roots[h].clone();
            }
            let inv = constant_inverse::<R, D>(&den)?;
            out.push(num * RelPoly::from_coefficients(vec![inv]));
        }
        Some(out)
    }

    /// A uniform **unit** of the ring, drawn from `A \ {0}`.
    ///
    /// Lemma 6's normal form is exactly what makes this sound: in a canonical
    /// exceptional set every point except `0` is a unit, so the setup's
    /// `r_v, r_w, α, α_v, α_w, α_y ← R*` can be sampled from the public pool
    /// without ever landing on a non-invertible element.
    pub fn draw(&self, domain: &[u8], seed: &[u8]) -> PolyRing<R, D> {
        assert!(
            self.points.len() > 1,
            "a canonical exceptional set with only 0 has no unit to draw"
        );
        draw_from(&self.points[1..], domain, seed)
    }

    /// A uniform point of `A* = A \ A_Q` (Fig. 1's `s ← A*`).
    ///
    /// Returns `None` when the set has no point outside the gate roots.
    pub fn draw_secret(&self, d: usize, domain: &[u8], seed: &[u8]) -> Option<PolyRing<R, D>> {
        let pool = self.secret_points(d)?;
        Some(draw_from(pool, domain, seed))
    }
}

/// A uniform element of `pool`, indexed by a domain-separated XOF stream.
fn draw_from<R: Ring, const D: usize>(
    pool: &[PolyRing<R, D>],
    domain: &[u8],
    seed: &[u8],
) -> PolyRing<R, D> {
    assert!(!pool.is_empty(), "an empty pool has nothing to draw");
    let mut xof = seed_stream::<Shake128Xof>(domain, seed);
    let mut buf = [0u8; 8];
    xof.squeeze(&mut buf);
    let idx = usize::try_from(u64::from_le_bytes(buf) % (pool.len() as u64))
        .expect("a pool index fits usize");
    pool[idx].clone()
}

/// A uniform element of `R_D \ {0}` from a domain-separated seed.
///
/// Fig. 1 draws `β ← R \ {0}`: unlike `s`, `r_v`, `α`, it is *not* required to
/// be a unit, so it cannot come from the exceptional set. The rejection is on
/// the zero element only, which for any ring of practical size is sampled in
/// one round.
///
/// # Panics
/// If 32 consecutive draws all land on zero (statistically unreachable).
pub fn nonzero_ring_element<R: Ring, const D: usize>(domain: &[u8], seed: &[u8]) -> PolyRing<R, D> {
    let zero = ring_constant::<R, D>(R::ZERO);
    for round in 0..32u64 {
        let mut tag = Vec::from(domain);
        tag.extend_from_slice(&round.to_le_bytes());
        let p = uniform_ring_from_seed::<R, D>(&tag, seed);
        if p != zero {
            return p;
        }
    }
    panic!("uniform draws must not all be zero")
}

/// A Quadratic Ring Program: `(t, {v_k}, {w_k}, {y_k})` (Def. 7 / Def. 10).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Qrp<R: Ring, const D: usize> {
    /// Target polynomial `t(x) = Π_g (x − r_g)`; monic of degree `#gates`.
    pub t: RelPoly<R, D>,
    /// `v_0 … v_m`.
    pub v: Vec<RelPoly<R, D>>,
    /// `w_0 … w_m`.
    pub w: Vec<RelPoly<R, D>>,
    /// `y_0 … y_m`.
    pub y: Vec<RelPoly<R, D>>,
    /// The gate roots, i.e. the roots of `t`.
    pub roots: Vec<PolyRing<R, D>>,
}

impl<R: Field, const D: usize> Qrp<R, D> {
    /// Builds the QRP of a fan-in-2 multiplication circuit (Theorem 6 applied
    /// gate-by-gate and composed by Theorem 7 / Theorem 8).
    ///
    /// `wires` is `m`: the program has wire polynomials `0..=m`, one per
    /// circuit wire plus the constant wire `0`. Gate `g` is pinned to the root
    /// `r_g = A[g]`, and the wire polynomials are the Lagrange interpolations
    /// of the gate table: `v_k(r_g) = [k = g.left]`, `w_k(r_g) = [k = g.right]`,
    /// `y_k(r_g) = [k = g.out]`.
    ///
    /// Returns `None` if the circuit has no multiplication gate, if the
    /// exceptional set is too small for the gate count, or if the gate table
    /// references a wire outside `0..=wires`.
    pub fn from_gates(gates: &[Gate], wires: usize, set: &ExceptionalSet<R, D>) -> Option<Self> {
        let d = gates.len();
        if d == 0 || wires == 0 {
            return None;
        }
        for g in gates {
            if g.left > wires || g.right > wires || g.out > wires {
                return None;
            }
        }
        let roots = set.gate_roots(d)?.to_vec();
        let basis = set.lagrange_basis(d)?;
        let zero = ring_constant::<R, D>(R::ZERO);
        let width = basis.iter().map(RelPoly::n_terms).max().unwrap_or(1);
        let mut v = Vec::with_capacity(wires + 1);
        let mut w = Vec::with_capacity(wires + 1);
        let mut y = Vec::with_capacity(wires + 1);
        for k in 0..=wires {
            let build = |pick: fn(&Gate) -> usize| {
                let mut acc = vec![zero.clone(); width];
                for (g, gate) in gates.iter().enumerate() {
                    if pick(gate) == k {
                        for (i, b) in basis[g].c.iter().enumerate() {
                            acc[i] = acc[i].clone() + b.clone();
                        }
                    }
                }
                RelPoly::from_coefficients(acc)
            };
            v.push(build(|g| g.left));
            w.push(build(|g| g.right));
            y.push(build(|g| g.out));
        }
        let mut t = RelPoly::<R, D>::one();
        for r in &roots {
            t = t * RelPoly::linear_factor(r);
        }
        Some(Self { t, v, w, y, roots })
    }

    /// Program size `m` (Def. 7: "the size of Q").
    pub fn size(&self) -> usize {
        self.v.len() - 1
    }

    /// Program degree `deg t` (§3.1: one root per multiplication gate).
    pub fn degree(&self) -> usize {
        self.t.degree()
    }

    /// `(V, W, Y)` for the assignment `a` — a *QRP solution* when `a` is valid
    /// (Def. 7's closing paragraph).
    pub fn solution(&self, a: &[PolyRing<R, D>]) -> (RelPoly<R, D>, RelPoly<R, D>, RelPoly<R, D>) {
        (
            RelPoly::linear_combination(a, &self.v),
            RelPoly::linear_combination(a, &self.w),
            RelPoly::linear_combination(a, &self.y),
        )
    }

    /// `p(x) = V(x)W(x) − Y(x)`.
    pub fn product(&self, a: &[PolyRing<R, D>]) -> RelPoly<R, D> {
        let (v, w, y) = self.solution(a);
        v * w - y
    }

    /// `h(x) = (V·W − Y) / t`, `None` exactly when the assignment does not
    /// satisfy the program.
    pub fn quotient(&self, a: &[PolyRing<R, D>]) -> Option<RelPoly<R, D>> {
        self.product(a).div_exact(&self.t)
    }

    /// The Def. 7 satisfiability test.
    pub fn is_satisfied(&self, a: &[PolyRing<R, D>]) -> bool {
        self.quotient(a).is_some()
    }

    /// The `v_k(x)` values, one per wire — the trusted setup's
    /// `{E(r_v·v_k(s))}` inputs.
    pub fn v_at(&self, x: &PolyRing<R, D>) -> Vec<PolyRing<R, D>> {
        self.v.iter().map(|p| p.evaluate(x)).collect()
    }

    /// The `w_k(x)` values.
    pub fn w_at(&self, x: &PolyRing<R, D>) -> Vec<PolyRing<R, D>> {
        self.w.iter().map(|p| p.evaluate(x)).collect()
    }

    /// The `y_k(x)` values.
    pub fn y_at(&self, x: &PolyRing<R, D>) -> Vec<PolyRing<R, D>> {
        self.y.iter().map(|p| p.evaluate(x)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use algebra::ring::zq::Zq;

    type Big = Zq<4294967197>; // 2^32-99: prime, 5 mod 8, no NTT
    type Small = Zq<1009>;
    const DB: usize = 64;
    const DS: usize = 4;

    fn sc<R: Ring>(v: u64) -> R {
        R::from(v)
    }

    /// The three-gate circuit `a3 = a1*a2`, `a4 = a3*a2`, `a5 = a4*a3`.
    fn circuit<R: Field, const D: usize>(scalars: &[R]) -> (Qrp<R, D>, ExceptionalSet<R, D>) {
        let set = ExceptionalSet::<R, D>::canonical(scalars).expect("exceptional set");
        let gates = [
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
        let qrp = Qrp::from_gates(&gates, 5, &set).expect("program");
        (qrp, set)
    }

    fn assignment<R: Field, const D: usize>(vals: &[Vec<u64>]) -> Vec<PolyRing<R, D>> {
        vals.iter()
            .map(|v| {
                assert_eq!(v.len(), D);
                PolyRing::from_coefficients(v.iter().map(|&c| R::from(c)).collect())
            })
            .collect()
    }

    #[test]
    fn the_exceptional_set_boundary_is_d_roots_plus_one_secret_point() {
        // `|A| = d + 1` is the smallest legal set and `|A| = d` is not, because
        // `A* = A \ A_Q` has to hold the secret point `s` the setup samples.
        // Pinning both sides of the line is what stops the relaxed guard from
        // being relaxed once more to `|A| ≥ d`, which would leave `A*` empty
        // and the hiding point undefined.
        let set =
            ExceptionalSet::<Small, DS>::canonical(&[sc::<Small>(3), sc::<Small>(5)]).expect("set");
        assert_eq!(set.len(), 3);
        assert!(
            set.gate_roots(2).is_some(),
            "|A| = d + 1 = 3 must admit d = 2"
        );
        assert_eq!(set.secret_points(2).map(|p| p.len()), Some(1));
        assert!(
            set.gate_roots(3).is_none(),
            "d = 3 leaves no secret point and must be refused"
        );
        assert!(
            set.secret_points(3).is_none(),
            "secret_points must refuse on the same boundary as gate_roots"
        );
    }

    #[test]
    fn lagrange_basis_interpolates_the_exceptional_points() {
        let (_, set) = circuit::<Small, DS>(&[sc::<Small>(3), sc::<Small>(5), sc::<Small>(7)]);
        let basis = set.lagrange_basis(3).expect("basis");
        for g in 0..3 {
            for h in 0..3 {
                let want = if g == h {
                    ring_constant::<Small, DS>(Small::ONE)
                } else {
                    ring_constant::<Small, DS>(Small::ZERO)
                };
                assert_eq!(basis[g].evaluate(&set.points()[h]), want, "L_{g}(r_{h})");
            }
        }
    }

    #[test]
    fn wire_polynomials_interpolate_the_gate_table() {
        let (qrp, set) = circuit::<Small, DS>(&[sc::<Small>(3), sc::<Small>(5), sc::<Small>(7)]);
        let gates = [(1usize, 2usize, 3usize), (3, 2, 4), (4, 3, 5)];
        assert_eq!(qrp.degree(), 3);
        assert_eq!(qrp.size(), 5);
        for (g, (l, r, o)) in gates.into_iter().enumerate() {
            let zero = ring_constant::<Small, DS>(Small::ZERO);
            let one = ring_constant::<Small, DS>(Small::ONE);
            let root = set.points()[g].clone();
            for k in 0..=5 {
                assert_eq!(
                    qrp.v[k].evaluate(&root),
                    if l == k { one.clone() } else { zero.clone() },
                    "v_{k}(r_{g})"
                );
                assert_eq!(
                    qrp.w[k].evaluate(&root),
                    if r == k { one.clone() } else { zero.clone() },
                    "w_{k}(r_{g})"
                );
                assert_eq!(
                    qrp.y[k].evaluate(&root),
                    if o == k { one.clone() } else { zero.clone() },
                    "y_{k}(r_{g})"
                );
            }
            assert!(qrp.t.evaluate(&root).is_zero(), "t must vanish at r_{g}");
        }
    }

    #[test]
    fn divisibility_is_equivalent_to_gate_satisfaction() {
        let (qrp, _) = circuit::<Small, DS>(&[sc::<Small>(3), sc::<Small>(5), sc::<Small>(7)]);
        let a1: Vec<u64> = vec![3, 1, 0, 2];
        let a2: Vec<u64> = vec![5, 0, 2, 1];
        let w1 = assignment::<Small, DS>(&[a1.clone()]);
        let w2 = assignment::<Small, DS>(&[a2.clone()]);
        let p3 = w1[0].clone() * w2[0].clone();
        let p4 = p3.clone() * w2[0].clone();
        let p5 = p4.clone() * p3.clone();
        let a = {
            let mut v = vec![ring_constant::<Small, DS>(Small::ONE)];
            v.extend([w1[0].clone(), w2[0].clone(), p3, p4, p5]);
            v
        };
        assert!(qrp.is_satisfied(&a), "a consistent trace must satisfy");
        let h = qrp.quotient(&a).expect("quotient");
        // deg h <= deg t - 2 is what makes {E(s^i)}_{i<=deg t} enough for D.
        assert!(
            h.degree() + 2 <= qrp.degree(),
            "deg h = {} must be <= deg t - 2",
            h.degree()
        );

        // Break one gate: the remainder must be nonzero, and it must be
        // nonzero *at the broken gate's root* (Eq. 2's isomorphism).
        let mut bad = a.clone();
        bad[4] = bad[4].clone() + ring_constant::<Small, DS>(Small::ONE);
        assert!(
            !qrp.is_satisfied(&bad),
            "an inconsistent trace must not satisfy"
        );
        let p = qrp.product(&bad);
        assert!(!p.evaluate(&qrp.roots[1]).is_zero(), "gate 2 is broken");
        assert!(
            !p.evaluate(&qrp.roots[2]).is_zero(),
            "gate 3 depends on wire 4"
        );
        assert!(p.evaluate(&qrp.roots[0]).is_zero(), "gate 1 is untouched");
    }

    #[test]
    fn monic_long_division_round_trips_without_inverting() {
        // Runs over the house non-NTT prime 2^32-99 at dimension 64.
        let (qrp, _) = circuit::<Big, DB>(&[sc::<Big>(11), sc::<Big>(13), sc::<Big>(17)]);
        let mk = |k: u64| ring_constant::<Big, DB>(Big::from(k));
        // Non-constant inputs, so the gate products exercise real ring
        // multiplication rather than scalar arithmetic dressed up as a ring.
        let mk_poly = |terms: &[(usize, u64)]| {
            let mut coeffs = vec![Big::ZERO; DB];
            for &(i, v) in terms {
                coeffs[i] = Big::from(v);
            }
            PolyRing::<Big, DB>::from_coefficients(coeffs)
        };
        let (w1, w2) = (
            mk_poly(&[(0, 3), (5, 2), (DB - 1, 7)]),
            mk_poly(&[(1, 11), (2, 13)]),
        );
        // The trace has to *obey* the gates (a3 = a1·a2, a4 = a3·a2,
        // a5 = a4·a3) or `t ∤ p` and the test asserts a falsehood — the
        // progression this used to hand it, `[1, 8, 15, 22, 29, 36]`, fails
        // gate 1 as 22 ≠ 8·15 = 120.
        let p3 = w1.clone() * w2.clone();
        let p4 = p3.clone() * w2.clone();
        let p5 = p4.clone() * p3.clone();
        let a = vec![mk(1), w1, w2, p3, p4, p5];
        let (v, w, y) = qrp.solution(&a);
        let p = v * w - y;
        let (q, r) = p.div_rem_monic(&qrp.t);
        assert!(r.is_zero(), "the constructed trace is consistent");
        assert_eq!(q * qrp.t.clone(), p, "p = q*t exactly");
        // ... and the zero remainder above is not automatic: one wrong wire
        // leaves a nonzero remainder, which is what makes the honest case mean
        // anything.
        let mut broken = a.clone();
        broken[5] = broken[5].clone() + mk(1);
        let (vb, wb, yb) = qrp.solution(&broken);
        let (_, rb) = (vb * wb - yb).div_rem_monic(&qrp.t);
        assert!(
            !rb.is_zero(),
            "an inconsistent trace must not divide out either"
        );
        // A divisor that is not monic is refused rather than silently
        // approximated — that is the whole point of the ring-safe division.
        let two = RelPoly::<Big, DB>::from_coefficients(vec![mk(2)]);
        let res = std::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            p.div_rem_monic(&two);
        }));
        assert!(res.is_err(), "non-monic divisors must panic");
    }

    #[test]
    fn a_non_exceptional_set_is_rejected() {
        // Duplicate points: r_i - r_j = 0 is not a unit, so the Lagrange basis
        // (and hence the QRP) must not be built.
        assert!(
            ExceptionalSet::<Small, DS>::canonical(&[sc::<Small>(3), sc::<Small>(3)]).is_none()
        );
        // Zero as a "nonzero" point collapses onto A[0] = 0.
        assert!(
            ExceptionalSet::<Small, DS>::canonical(&[sc::<Small>(0), sc::<Small>(5)]).is_none()
        );
        // Too few points for the gate count: no room left for the secret s.
        let set = ExceptionalSet::<Small, DS>::canonical(&[sc::<Small>(3)]).expect("set");
        let gates = [
            Gate {
                left: 1,
                right: 1,
                out: 2,
            },
            Gate {
                left: 2,
                right: 1,
                out: 3,
            },
        ];
        assert!(Qrp::from_gates(&gates, 3, &set).is_none());
        assert!(set.gate_roots(2).is_none());
    }

    #[test]
    fn the_ring_is_not_a_field_so_zero_divisors_exist() {
        // The QRP layer must be sound over a ring with zero divisors: that is
        // Rinocchio's whole premise. X^4+1 = (X^2+sX+1)(X^2-sX+1) over GF(1009)
        // because 2 is a square there (1009 = 1 mod 8); s = 395 squares to 2.
        let s = (0..1009u64).find(|x| x * x % 1009 == 2).expect("sqrt(2)");
        let u = PolyRing::<Small, DS>::from_coefficients(
            [1u64, s, 1, 0]
                .iter()
                .map(|&c| Small::from(c))
                .collect::<Vec<_>>(),
        );
        let v = PolyRing::<Small, DS>::from_coefficients(
            [1u64, 1009 - s, 1, 0]
                .iter()
                .map(|&c| Small::from(c))
                .collect::<Vec<_>>(),
        );
        assert_eq!(
            u.clone() * v.clone(),
            ring_constant::<Small, DS>(Small::ZERO)
        );
        assert_ne!(u, ring_constant::<Small, DS>(Small::ZERO));
        assert_ne!(v, ring_constant::<Small, DS>(Small::ZERO));
        // and the constant-only inverses the layer uses are unaffected
        assert!(constant_inverse::<Small, DS>(&u).is_none());
        assert!(
            constant_inverse::<Small, DS>(&ring_constant::<Small, DS>(Small::from(7u64))).is_some()
        );
    }

    #[test]
    fn the_setup_draws_land_in_the_advertised_pools() {
        // Fig. 1 samples `s <- A*` and the blinding scalars from R*; the
        // helpers must not be able to hand back a point that is a gate root
        // (that would make t(s) = 0 and collapse the whole argument).
        let (qrp, set) = circuit::<Small, DS>(&[
            sc::<Small>(3),
            sc::<Small>(5),
            sc::<Small>(7),
            sc::<Small>(11),
            sc::<Small>(13),
        ]);
        for round in 0..16u8 {
            let mut seed = [0u8; 32];
            seed[0] = round;
            let s = set.draw_secret(3, b"rinocchio-s", &seed).expect("pool");
            assert!(set.secret_points(3).expect("pool").contains(&s));
            assert!(!qrp.roots.contains(&s), "s must not be a gate root");
            assert!(constant_inverse::<Small, DS>(&qrp.t.evaluate(&s)).is_some());
            let r = set.draw(b"rinocchio-rv", &seed);
            assert!(set.points().contains(&r));
        }
        let beta = nonzero_ring_element::<Small, DS>(b"rinocchio-beta", &[2u8; 32]);
        assert_ne!(beta, ring_constant::<Small, DS>(Small::ZERO));
        // Fig. 1 asks only for beta != 0, not for a unit; a uniform draw of a
        // ring with zero divisors can legitimately land on a zero divisor, so
        // nothing stronger may be asserted here. The draw is, however, fixed
        // by the seed, which is what makes the setup reproducible.
        assert_eq!(
            beta,
            nonzero_ring_element::<Small, DS>(b"rinocchio-beta", &[2u8; 32])
        );
        assert_ne!(
            beta,
            nonzero_ring_element::<Small, DS>(b"rinocchio-beta", &[3u8; 32])
        );
    }

    #[test]
    fn target_evaluation_at_a_non_root_is_a_unit() {
        // The setup needs t(s) invertible for s in A* (zk-Rinocchio's simulator
        // divides by it); over a ring that is an assumption, so it is checked.
        let (qrp, set) = circuit::<Small, DS>(&[sc::<Small>(3), sc::<Small>(5), sc::<Small>(7)]);
        for s in set.secret_points(3).expect("secret pool") {
            let ts = qrp.t.evaluate(s);
            assert!(
                constant_inverse::<Small, DS>(&ts).is_some(),
                "t(s) must be a unit"
            );
        }
    }
}
