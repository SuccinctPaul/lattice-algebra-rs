//! Prime-field extensions `F_{q^k} = F_q[Z]/(Z^k − A)` (L1 algebra layer).
//!
//! Why this exists: Hachi (eprint 2026/156) gets its square-root verifier by
//! running the sumcheck over an **extension field**, so the verifier's heavy
//! step costs `Õ(k)` base operations instead of a full ring multiplication —
//! and it needs genuine division, to interpolate low-degree round
//! polynomials. See `docs/survey-lattice-pcs.md` §4, gap G6.
//!
//! # Why this is not a `Ring`
//!
//! [`Ring`](crate::ring::traits::Ring) is this crate's *scalar* `Z_q`
//! capability, and it demands `const ZERO`/`const ONE`. Building an array of
//! `K` copies of an associated const of a **generic** element type is not
//! expressible in const context in stable Rust, which is exactly why
//! [`PolyRing`](crate::ring::poly_ring::PolyRing) implements
//! [`PolynomialQuotientRing`](crate::ring::traits::PolynomialQuotientRing)
//! rather than `Ring`. This type therefore presents itself through plain
//! methods, and additionally implements
//! [`MatrixElement`](crate::ring::traits::MatrixElement) directly — the
//! blanket `MatrixElement`-for-`Ring` impl cannot overlap it, since this type
//! is not a `Ring` — so the `sumcheck` domain accepts it unchanged.
//!
//! # The irreducibility hypothesis is checked, not assumed
//!
//! `F_q[Z]/(Z^k − A)` is a field **iff** `Z^k − A` is irreducible over `F_q`.
//! The type cannot prove that about its `const` parameters, so the invariant
//! is enforced operationally: [`inverse`](ExtField::inverse) solves a linear
//! system over `F_q` and returns `None` when it is singular — a witness that
//! `Z^k − A` factors. A wrong `(q, k, A)` therefore fails loudly at the first
//! inversion rather than silently becoming a ring with zero divisors;
//! `a_reducible_choice_fails_loudly` pins that behaviour with the explicit
//! factorization `(Z² − 4094)(Z² + 4094) = Z⁴ − 2` over the crate's Z1 prime.
//!
//! For Hachi's shape (`k = 4`, `A = 2`, `q = 2³² − 99 ≡ 5 (mod 8)`) the
//! extension is a field. Over a `q ≡ 1 (mod 8)` prime — such as Z1's
//! `8380417` — `Z⁴ − 2` is **not** irreducible.
//!
//! # No centered representatives, no NTT
//!
//! An extension element is a vector of `k` residues, so there is no canonical
//! representative in `(−q/2, q/2]` and no `CenteredRing` impl — take norms
//! component-wise through [`ExtField::coeffs`]. And `q = 2³² − 99` is not
//! NTT-friendly, so multiplication here is schoolbook plus the binomial
//! reduction, `O(k²)` base operations, with no transform dependency.

use crate::ring::traits::{Field, MatrixElement, Ring};
use core::fmt;
use core::iter::Sum;
use core::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

/// An element of `F_q[Z]/(Z^K − A)`, stored as `K` base coefficients in
/// ascending powers of `Z`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ExtField<B: Ring, const K: usize, const A: u64> {
    coeffs: [B; K],
}

impl<B: Ring, const K: usize, const A: u64> Default for ExtField<B, K, A> {
    fn default() -> Self {
        Self {
            coeffs: [B::ZERO; K],
        }
    }
}

impl<B: Ring, const K: usize, const A: u64> ExtField<B, K, A> {
    /// The characteristic — the base modulus.
    pub const fn characteristic() -> u64 {
        B::MODULUS
    }

    /// The extension degree `K`.
    pub const fn degree() -> usize {
        K
    }

    /// The `K` base coefficients, ascending powers of `Z`.
    pub const fn coeffs(&self) -> [B; K] {
        self.coeffs
    }

    /// The constant coefficient.
    pub const fn constant(&self) -> B {
        self.coeffs[0]
    }

    /// The additive identity.
    pub fn zero() -> Self {
        Self::default()
    }

    /// The multiplicative identity.
    pub fn one() -> Self {
        let mut coeffs = [B::ZERO; K];
        coeffs[0] = B::ONE;
        Self { coeffs }
    }

    /// Whether this is the additive identity.
    pub fn is_zero(&self) -> bool {
        self.coeffs.iter().all(|c| *c == B::ZERO)
    }

    /// Embeds a base-field element as a constant.
    pub fn from_base(b: B) -> Self {
        let mut coeffs = [B::ZERO; K];
        coeffs[0] = b;
        Self { coeffs }
    }

    /// The class of `Z`: satisfies `Z^K = A`, and generates the extension
    /// when `Z^K − A` is irreducible.
    pub fn z_generator() -> Self {
        let mut coeffs = [B::ZERO; K];
        if K > 1 {
            coeffs[1] = B::ONE;
        }
        Self { coeffs }
    }

    /// Multiplies every coefficient by a base-field scalar. This is the hot
    /// path when a verifier folds extension-valued round messages by *base*
    /// challenges, and it must not pay for a full extension product.
    pub fn mul_base(&self, s: B) -> Self {
        let mut out = *self;
        for c in out.coeffs.iter_mut() {
            *c *= s;
        }
        out
    }

    /// `self · self`.
    pub fn square(&self) -> Self {
        self.mul_raw(self)
    }

    /// Square-and-multiply exponentiation.
    pub fn pow(&self, mut power: u64) -> Self {
        let mut result = Self::one();
        let mut base = *self;
        while power > 0 {
            if power & 1 == 1 {
                result = result.mul_raw(&base);
            }
            base = base.square();
            power >>= 1;
        }
        result
    }

    /// Schoolbook product with the binomial reduction `Z^K = A` applied on
    /// the fly.
    ///
    /// Both operands have degree `< K`, so every product term lands at
    /// degree `< 2K − 1` and a **single** fold suffices: degree `K + t` is
    /// `A · Z^t` with `t < K`. Written as one pass into a length-`K`
    /// accumulator rather than a length-`2K − 1` scratch array, because an
    /// array length that is an *expression* over a const generic requires the
    /// unstable `generic_const_exprs` feature.
    pub fn mul_raw(&self, other: &Self) -> Self {
        let a_red = B::from(A);
        let mut out = [B::ZERO; K];
        for (i, x) in self.coeffs.iter().enumerate() {
            if *x == B::ZERO {
                continue;
            }
            for (j, y) in other.coeffs.iter().enumerate() {
                if *y == B::ZERO {
                    continue;
                }
                let d = i + j;
                let term = *x * *y;
                if d < K {
                    out[d] += term;
                } else {
                    out[d - K] += term * a_red;
                }
            }
        }
        Self { coeffs: out }
    }

    /// The matrix of "multiply by `self`" in the basis `1, Z, …, Z^(K−1)`:
    /// **column** `j` holds the coordinates of `self · Z^j`.
    fn multiplication_matrix(&self) -> [[B; K]; K] {
        let z = Self::z_generator();
        let mut powers = [Self::zero(); K];
        powers[0] = Self::one();
        for j in 1..K {
            powers[j] = powers[j - 1].mul_raw(&z);
        }
        let mut m = [[B::ZERO; K]; K];
        for (j, p) in powers.iter().enumerate() {
            let column = self.mul_raw(p).coeffs;
            // `m` indexes rows, so the coordinate vector goes down a column.
            // Writing it into `m[j]` instead transposes the whole matrix and
            // silently solves the wrong system.
            for (i, v) in column.iter().enumerate() {
                m[i][j] = *v;
            }
        }
        m
    }
}

impl<B: Ring + Field, const K: usize, const A: u64> ExtField<B, K, A> {
    /// Solves `self · u = 1` by Gauss–Jordan elimination over `F_q`.
    ///
    /// `None` means `self` is zero, or that the system is singular — in the
    /// latter case `self` is a **zero divisor**, witnessing that `Z^K − A` is
    /// reducible and that this type is not a field for these parameters.
    pub fn inverse(&self) -> Option<Self> {
        if self.is_zero() {
            return None;
        }
        let mut m = self.multiplication_matrix();
        let mut rhs = [B::ZERO; K];
        rhs[0] = B::ONE;

        for col in 0..K {
            let pivot = (col..K).find(|&r| m[r][col] != B::ZERO)?;
            m.swap(col, pivot);
            rhs.swap(col, pivot);
            let inv = m[col][col].inverse()?;
            for value in m[col].iter_mut() {
                *value *= inv;
            }
            rhs[col] *= inv;
            // Snapshot the (now normalized) pivot row: eliminating every
            // other row reads it while `m` is mutably borrowed.
            let pivot_row = m[col];
            let pivot_rhs = rhs[col];
            for (r, row) in m.iter_mut().enumerate() {
                if r == col || row[col] == B::ZERO {
                    continue;
                }
                let factor = row[col];
                for (c, cell) in row.iter_mut().enumerate() {
                    *cell -= factor * pivot_row[c];
                }
                rhs[r] -= factor * pivot_rhs;
            }
        }
        Some(Self { coeffs: rhs })
    }
}

impl<B: Ring, const K: usize, const A: u64> From<u64> for ExtField<B, K, A> {
    fn from(v: u64) -> Self {
        Self::from_base(B::from(v))
    }
}

impl<B: Ring, const K: usize, const A: u64> From<B> for ExtField<B, K, A> {
    fn from(b: B) -> Self {
        Self::from_base(b)
    }
}

impl<B: Ring, const K: usize, const A: u64> Add for ExtField<B, K, A> {
    type Output = Self;
    fn add(self, other: Self) -> Self {
        let mut coeffs = self.coeffs;
        for (c, o) in coeffs.iter_mut().zip(other.coeffs.iter()) {
            *c += *o;
        }
        Self { coeffs }
    }
}

impl<B: Ring, const K: usize, const A: u64> Sub for ExtField<B, K, A> {
    type Output = Self;
    fn sub(self, other: Self) -> Self {
        let mut coeffs = self.coeffs;
        for (c, o) in coeffs.iter_mut().zip(other.coeffs.iter()) {
            *c -= *o;
        }
        Self { coeffs }
    }
}

impl<B: Ring, const K: usize, const A: u64> Mul for ExtField<B, K, A> {
    type Output = Self;
    fn mul(self, other: Self) -> Self {
        self.mul_raw(&other)
    }
}

impl<B: Ring, const K: usize, const A: u64> Neg for ExtField<B, K, A> {
    type Output = Self;
    fn neg(self) -> Self {
        let mut coeffs = self.coeffs;
        for c in coeffs.iter_mut() {
            *c = -*c;
        }
        Self { coeffs }
    }
}

impl<B: Ring + Field, const K: usize, const A: u64> Div for ExtField<B, K, A> {
    type Output = Self;
    fn div(self, other: Self) -> Self {
        let inv = other
            .inverse()
            .expect("division by a non-invertible extension element");
        self.mul_raw(&inv)
    }
}

impl<B: Ring, const K: usize, const A: u64> AddAssign for ExtField<B, K, A> {
    fn add_assign(&mut self, other: Self) {
        *self = *self + other;
    }
}

impl<B: Ring, const K: usize, const A: u64> SubAssign for ExtField<B, K, A> {
    fn sub_assign(&mut self, other: Self) {
        *self = *self - other;
    }
}

impl<B: Ring, const K: usize, const A: u64> MulAssign for ExtField<B, K, A> {
    fn mul_assign(&mut self, other: Self) {
        *self = *self * other;
    }
}

impl<B: Ring + Field, const K: usize, const A: u64> DivAssign for ExtField<B, K, A> {
    fn div_assign(&mut self, other: Self) {
        *self = *self / other;
    }
}

impl<B: Ring, const K: usize, const A: u64> Sum for ExtField<B, K, A> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::zero(), Add::add)
    }
}

impl<B: Ring, const K: usize, const A: u64> fmt::Debug for ExtField<B, K, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // The coefficients must appear: printing only the type parameters
        // makes two unequal elements render identically, which turns an
        // assertion failure into an unsolvable puzzle.
        write!(f, "ExtField<{}, Z^{} - {:?}>", B::MODULUS, K, self.coeffs)
    }
}

impl<B: Ring + fmt::Display, const K: usize, const A: u64> fmt::Display for ExtField<B, K, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, c) in self.coeffs.iter().enumerate() {
            if i > 0 {
                write!(f, " + ")?;
            }
            write!(f, "{c}·Z^{i}")?;
        }
        Ok(())
    }
}

/// Implemented directly rather than through the blanket impl: that one
/// requires [`Ring`], which this type deliberately does not wear (see the
/// module docs). This is the seam that lets `sumcheck` run over the
/// extension without change.
impl<B: Ring + Field + fmt::Display, const K: usize, const A: u64> MatrixElement
    for ExtField<B, K, A>
{
    fn zero() -> Self {
        ExtField::zero()
    }

    fn one() -> Self {
        ExtField::one()
    }

    fn random(rng: &mut impl rand::RngCore) -> Self {
        let mut coeffs = [B::ZERO; K];
        for c in coeffs.iter_mut() {
            *c = B::rand(rng);
        }
        Self { coeffs }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::number_theory::{is_prime_u64, x_pow_d_plus_1_splitting};
    use crate::ring::zq::Zq;
    use alloc::vec::Vec;

    /// Hachi's characteristic: `2³² − 99 ≡ 5 (mod 8)`.
    type Q5 = Zq<4294967197>;
    /// This crate's Z1 prime: `≡ 1 (mod 8)`, where `Z⁴ − 2` factors.
    type Q1 = Zq<8380417>;

    type F = ExtField<Q5, 4, 2>;

    const MOD8: u64 = 4_294_967_197;

    fn el(vals: [u64; 4]) -> F {
        F {
            coeffs: vals.map(|v| Q5::from(v % MOD8)),
        }
    }

    #[test]
    fn shape_matches_the_hachi_parameter() {
        assert_eq!(F::characteristic(), 4_294_967_197);
        assert_eq!(F::degree(), 4);
        assert_eq!(MOD8 % 8, 5, "the field we test needs q ≡ 5 mod 8");
    }

    #[test]
    fn arithmetic_agrees_with_polynomial_arithmetic() {
        // (1 + 2Z + 3Z² + 4Z³)·(5 + Z³): raw degrees 0..6, then Z⁴ = 2
        // folds 4→0, 5→1, 6→2.
        let a = el([1, 2, 3, 4]);
        let b = el([5, 0, 0, 1]);
        let raw = [5u64, 10, 15, 21, 2, 3, 4];
        let expect = [
            raw[0] + 2 * raw[4],
            raw[1] + 2 * raw[5],
            raw[2] + 2 * raw[6],
            raw[3],
        ];
        let product = a * b;
        for (got, want) in product.coeffs().iter().zip(expect.iter()) {
            assert_eq!(got.to_u128(), u128::from(*want));
        }
        assert_eq!(F::z_generator().pow(4), F::from(2u64), "Z⁴ = A");
    }

    #[test]
    fn field_axioms_hold() {
        let x = el([3, 11, 5, 23]);
        let y = el([1, 7, 0, 19]);
        let z = el([29, 2, 13, 0]);
        assert_eq!((x + y) + z, x + (y + z));
        assert_eq!(x * (y + z), x * y + x * z);
        assert_eq!(x * F::one(), x);
        assert_eq!(x - x, F::zero());
        assert_eq!(x * F::zero(), F::zero());
        assert_eq!(x + (-x), F::zero());
        // commutativity: a field, not merely an algebra
        assert_eq!(x * y, y * x);
        assert!(!x.is_zero());
        assert!(F::zero().is_zero());
    }

    #[test]
    fn powers_and_inverses_agree() {
        let x = el([2, 3, 5, 7]);
        assert_eq!(x.square(), x * x);
        assert_eq!(x.pow(6), x * x * x * x * x * x);
        let inv = x.inverse().expect("nonzero in a field");
        assert_eq!(x * inv, F::one());
        assert_eq!(el([9, 9, 9, 9]) / x, el([9, 9, 9, 9]) * inv);
        assert_eq!(F::zero().inverse(), None, "zero has no inverse");
    }

    #[test]
    fn every_nonzero_element_is_invertible_over_the_hachi_field() {
        // Invertibility of every nonzero element *is* the field property.
        let small: Vec<u64> = (0..4).collect();
        let mut checked = 0usize;
        for a0 in &small {
            for a1 in &small {
                for a2 in &small {
                    for a3 in &small {
                        let x = el([*a0, *a1, *a2, *a3]);
                        if x.is_zero() {
                            continue;
                        }
                        let inv = x
                            .inverse()
                            .unwrap_or_else(|| panic!("Z⁴ − 2 must be irreducible: {x}"));
                        assert_eq!(x * inv, F::one());
                        checked += 1;
                    }
                }
            }
        }
        assert!(checked > 250, "expected a broad sweep, checked {checked}");
    }

    #[test]
    fn base_embedding_and_scalar_multiplication_agree() {
        let b = Q5::from(1234u64);
        let x = el([1, 2, 3, 4]);
        assert_eq!(
            x * F::from_base(b),
            x.mul_base(b),
            "the base action must equal multiplication by a constant"
        );
        assert_eq!(F::from_base(b).constant(), b);
        assert_eq!(F::from(b), F::from_base(b));
    }

    #[test]
    fn matrix_element_seam_exposes_zero_one_sums_and_display() {
        // This is what lets the `sumcheck` domain run over the extension.
        assert_eq!(<F as MatrixElement>::zero(), F::zero());
        assert_eq!(<F as MatrixElement>::one(), F::one());
        let parts = Vec::from([el([1, 0, 0, 0]), el([0, 1, 0, 0]), el([2, 3, 0, 0])]);
        let total: F = parts.into_iter().sum();
        assert_eq!(total, el([3, 4, 0, 0]));
        assert_eq!(
            alloc::string::ToString::to_string(&el([1, 2, 3, 4])),
            "1·Z^0 + 2·Z^1 + 3·Z^2 + 4·Z^3"
        );
    }

    #[test]
    fn a_reducible_choice_fails_loudly() {
        // Over the Z1 prime (q ≡ 1 mod 8) 2 IS a square: 4094² ≡ 2, so
        // Z⁴ − 2 = (Z² − 4094)(Z² + 4094) factors and the quotient has zero
        // divisors. The type must report that, not pretend to be a field.
        type Bad = ExtField<Q1, 4, 2>;
        let root = Q1::from(4094u64);
        assert_eq!(root.square(), Q1::from(2u64), "4094² ≡ 2 mod 8380417");

        let z2 = {
            let mut e = Bad::zero();
            e.coeffs[2] = Q1::ONE;
            e
        };
        let f = z2 - Bad::from_base(root);
        let g = z2 + Bad::from_base(root);

        assert!(!f.is_zero() && !g.is_zero());
        assert_eq!(
            f * g,
            Bad::zero(),
            "(Z²−c)(Z²+c) = Z⁴−2 = 0 in the quotient"
        );
        assert!(
            f.inverse().is_none(),
            "a zero divisor must refuse to invert"
        );

        // The same shape over Hachi's q ≡ 5 mod 8 gives a real field: none of
        // these quadratics is a zero divisor.
        for c in 1..50u64 {
            let cand = el([0, 0, 1, 0]) - F::from(c);
            assert!(
                cand.inverse().is_some(),
                "Z² − {c} must invert when Z⁴ − 2 is irreducible"
            );
        }
    }

    // Maltese's Protocols 1–2 sum-check over `K = F_{q^e}` with `e = 8` at `d = 64`
    // (Fig. 5 p. 45's P3 column). The house prime cannot state that —
    // `number_theory::the_eight_degree_regime_needs_a_prime_outside_the_house_class`
    // pins why, and adds that the `e = 8` prime with 2-adicity 1 is out of reach of
    // *this* type, because `Z⁸ − A` is irreducible only when `q ≡ 1 (mod 4)`. The
    // branch that satisfies both does exist, and this lands it: `q = 2³² − 527`,
    // `≡ 113 (mod 128)`, whose `X⁶⁴ + 1` splits into eight degree-8 factors, with
    // `K = F_q[Z]/(Z⁸ − 3)`.
    #[test]
    fn an_eight_degree_extension_exists_at_a_prime_in_p3s_regime() {
        const Q: u64 = 4_294_966_769; // 2³² − 527
        assert!(is_prime_u64(Q));
        assert_eq!(Q % 128, 113);
        assert_eq!(
            Q % 4,
            1,
            "the binomial criterion's `4 | n ⇒ q ≡ 1 (mod 4)` clause"
        );
        let split = x_pow_d_plus_1_splitting(Q, 64).expect("odd prime, d a power of two");
        assert_eq!(
            (split.factor_degree, split.factor_count),
            (8, 8),
            "P3's (d = 64, e = 8) shape"
        );

        type K8 = ExtField<Zq<Q>, 8, 3>;
        assert_eq!(K8::characteristic(), Q);
        assert_eq!(K8::degree(), 8);
        assert_eq!(K8::z_generator().pow(8), K8::from(3u64), "Z⁸ = A");

        // Invertibility of every nonzero element *is* the field property, and here
        // it is the only thing deciding that `Z⁸ − 3` is irreducible: 3⁸ elements of
        // small support, each solved against its own linear system.
        let mut checked = 0usize;
        for code in 0u64..3u64.pow(8) {
            let mut coeffs = [0u64; 8];
            let mut rest = code;
            for c in coeffs.iter_mut() {
                *c = (rest % 3) as u64;
                rest /= 3;
            }
            let x = K8 {
                coeffs: coeffs.map(|v| Zq::<Q>::from(v)),
            };
            if x.is_zero() {
                continue;
            }
            let inv = x
                .inverse()
                .unwrap_or_else(|| panic!("Z⁸ − 3 must be irreducible: {x}"));
            assert_eq!(x * inv, K8::one());
            checked += 1;
        }
        assert_eq!(checked, 3usize.pow(8) - 1, "the sweep must have run");
    }
}
