//! Explicit NTT-domain representation (M1).
//!
//! Keeping polynomials in the evaluation domain avoids paying a transform
//! per multiplication — the key optimization behind ML-DSA's matrix handling
//! (`Â` never leaves the NTT domain) and LaBRADOR-style batched openings.
//! `NttDomain<R, N>` is the typed marker for "these `N` values are the
//! evaluations of some `PolyRing` element".

use crate::ntt::NttOperatorOptimized;
use crate::poly::UniPolynomial;
use crate::ring::poly_ring::PolyRing;
use crate::ring::PolynomialQuotientRing;
use crate::ring::TwoAdicRing;

/// An element of `PolyRing` stored in the NTT (evaluation) domain, over `N`
/// slots (`N` is the ring dimension as `usize`).
///
/// The layout is whatever [`NttOperatorOptimized::forward`] produces
/// (bit-reversed order); the type deliberately does not expose individual
/// evaluations — only domain-wise operations and the conversion back.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NttDomain<R: TwoAdicRing, const N: usize> {
    values: [R; N],
}

impl<R: TwoAdicRing, const N: usize> NttDomain<R, N> {
    /// Wraps raw evaluation values without checking (trusted construction;
    /// prefer `PolyRing::to_ntt` unless the values were sampled directly in
    /// the NTT domain, as `ExpandA` does).
    pub fn from_values(values: [R; N]) -> Self {
        Self { values }
    }

    /// The zero element of the NTT domain (all evaluations zero).
    pub fn zero() -> Self {
        Self {
            values: [R::ZERO; N],
        }
    }

    /// Domain-wise addition (identical semantics to coefficient addition).
    #[must_use]
    pub fn add(&self, rhs: &Self) -> Self {
        let mut values = self.values;
        for (a, &b) in values.iter_mut().zip(&rhs.values) {
            *a += b;
        }
        Self { values }
    }

    /// Domain-wise subtraction.
    #[must_use]
    pub fn sub(&self, rhs: &Self) -> Self {
        let mut values = self.values;
        for (a, &b) in values.iter_mut().zip(&rhs.values) {
            *a -= b;
        }
        Self { values }
    }

    /// Borrows the raw evaluation values (layout is the operator's
    /// bit-reversed order; treat as opaque across versions).
    pub fn values(&self) -> &[R; N] {
        &self.values
    }

    /// Domain-wise multiplication — one coefficient-domain convolution
    /// without any transform.
    #[must_use]
    pub fn mul(&self, rhs: &Self) -> Self {
        let mut values = self.values;
        for (a, &b) in values.iter_mut().zip(&rhs.values) {
            *a *= b;
        }
        Self { values }
    }
}

impl<R: TwoAdicRing, const DEGREE_BOUND: usize> PolyRing<R, DEGREE_BOUND> {
    /// Transforms into the NTT domain (`O(N log N)`).
    ///
    /// # Panics
    /// If `(R, DEGREE_BOUND)` is not NTT friendly (checked by the operator).
    pub fn to_ntt(
        &self,
        op: &NttOperatorOptimized<R, { DEGREE_BOUND }>,
    ) -> NttDomain<R, { DEGREE_BOUND }> {
        let mut buf = [R::ZERO; DEGREE_BOUND];
        for (dst, &src) in buf.iter_mut().zip(self.coefficients().iter()) {
            *dst = src;
        }
        op.forward_negacyclic(&mut buf);
        NttDomain { values: buf }
    }

    /// Transforms back from the NTT domain (`O(N log N)`).
    pub fn from_ntt(
        v: NttDomain<R, { DEGREE_BOUND }>,
        op: &NttOperatorOptimized<R, { DEGREE_BOUND }>,
    ) -> Self {
        let mut buf = v.values;
        op.inverse_negacyclic(&mut buf);
        let mut inner = UniPolynomial::from_coefficients(buf.to_vec());
        inner.normalize();
        Self { inner }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ring::zq::Zq;

    type Zq17 = Zq<17>;
    type R = PolyRing<Zq17, 8>;

    fn poly(v: &[u64]) -> R {
        R::from_coefficients(v.iter().map(|&x| Zq17::new(x)).collect())
    }

    #[test]
    fn roundtrip_recovers_coefficients() {
        let op = NttOperatorOptimized::<Zq17, 8>::new();
        let a = poly(&[1, 2, 3]);
        let back = R::from_ntt(a.to_ntt(&op), &op);
        assert_eq!(back, a);
    }

    #[test]
    fn domain_mul_matches_ring_mul() {
        let op = NttOperatorOptimized::<Zq17, 8>::new();
        let a = poly(&[1, 2, 3]);
        let b = poly(&[4, 5]);

        let via_ntt = R::from_ntt(a.to_ntt(&op).mul(&b.to_ntt(&op)), &op);
        assert_eq!(via_ntt, a * b);
    }

    #[test]
    fn domain_add_matches_ring_add() {
        let op = NttOperatorOptimized::<Zq17, 8>::new();
        let a = poly(&[1, 2]);
        let b = poly(&[3, 4]);
        let via_ntt = R::from_ntt(a.to_ntt(&op).add(&b.to_ntt(&op)), &op);
        assert_eq!(via_ntt, a + b);
    }

    #[test]
    fn mul_then_add_composes() {
        let op = NttOperatorOptimized::<Zq17, 8>::new();
        let a = poly(&[1, 2, 3, 4]);
        let b = poly(&[5, 6]);
        let c = poly(&[7]);

        let lhs = R::from_ntt(a.to_ntt(&op).mul(&b.to_ntt(&op)).add(&c.to_ntt(&op)), &op);
        assert_eq!(lhs, a * b + c);
    }
}
