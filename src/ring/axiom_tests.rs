//! Ring-axiom property tests, instantiated over a spread of moduli.
//!
//! Acceptance gate for M0: the axioms must hold on every modulus the crate
//! is used with — small test primes, NIST PQC moduli and SNARK-friendly
//! power-of-two moduli alike (≥ 8 instances; currently 15).

use crate::ring::traits::{CenteredRing, Field, TwoAdicRing};
use crate::ring::zq::Zq;
use crate::ring::Ring;
use rand::rngs::StdRng;
use rand::SeedableRng;

type Zq2 = Zq<2>;
type Zq3 = Zq<3>;
type Zq5 = Zq<5>;
type Zq13 = Zq<13>;
type Zq17 = Zq<17>;
type Zq97 = Zq<97>;
type Zq257 = Zq<257>;
type Zq3329 = Zq<3329>;
type Zq7681 = Zq<7681>;
type Zq12289 = Zq<12289>;
type Zq65537 = Zq<65537>;
type Zq786433 = Zq<786433>;
type ZqMersenne31 = Zq<2147483647>; // 2^31 - 1
type ZqDilithium = Zq<8380417>; // FIPS 204
type ZqLaBrador = Zq<4294967296>; // 2^32 (LaBRADOR, composite!)

/// The representative set used for exhaustive small-scale axiom checks:
/// edges (0, 1, q-1, q-2), small values and the middle of the range.
fn representatives<R: Ring>() -> Vec<R> {
    let q = R::MODULUS;
    let mut vals = vec![0u64, 1, 2, 3, q - 1, q / 2];
    if q > 5 {
        vals.push(q - 2);
        vals.push(q / 3 + 1);
    }
    vals.into_iter().map(R::from).collect()
}

/// Exhaustive check of `f` over all triples of a fixed representative set
/// plus a few pseudo-random elements.
fn check_triples<R: Ring>(mut f: impl FnMut(R, R, R) -> bool) {
    let mut rng = StdRng::seed_from_u64(0xC0FFEE);
    let mut elems = representatives::<R>();
    elems.push(R::rand(&mut rng));
    elems.push(R::rand(&mut rng));
    for &a in &elems {
        for &b in &elems {
            for &c in &elems {
                assert!(f(a, b, c), "axiom violated for a={a}, b={b}, c={c}");
            }
        }
    }
}

fn check_pairs<R: Ring>(mut f: impl FnMut(R, R) -> bool) {
    let mut rng = StdRng::seed_from_u64(0xBEEF);
    let mut elems = representatives::<R>();
    elems.push(R::rand(&mut rng));
    for &a in &elems {
        for &b in &elems {
            assert!(f(a, b), "axiom violated for a={a}, b={b}");
        }
    }
}

macro_rules! ring_axiom_tests {
    ($($name:ident => $ty:ty),* $(,)?) => {
        $(
            mod $name {
                use super::*;

                #[test]
                fn add_associativity() {
                    check_triples::<$ty>(|a, b, c| (a + b) + c == a + (b + c));
                }

                #[test]
                fn add_commutativity() {
                    check_pairs::<$ty>(|a, b| a + b == b + a);
                }

                #[test]
                fn add_identity() {
                    check_pairs::<$ty>(|a, _b| a + <$ty as Ring>::ZERO == a);
                }

                #[test]
                fn add_inverse() {
                    check_pairs::<$ty>(|a, _b| a + (-a) == <$ty as Ring>::ZERO);
                }

                #[test]
                fn mul_associativity() {
                    check_triples::<$ty>(|a, b, c| (a * b) * c == a * (b * c));
                }

                #[test]
                fn mul_commutativity() {
                    check_pairs::<$ty>(|a, b| a * b == b * a);
                }

                #[test]
                fn mul_identity() {
                    check_pairs::<$ty>(|a, _b| a * <$ty as Ring>::ONE == a);
                }

                #[test]
                fn distributivity() {
                    check_triples::<$ty>(|a, b, c| a * (b + c) == a * b + a * c);
                }

                #[test]
                fn negation_is_mul_by_minus_one() {
                    check_pairs::<$ty>(|a, _b| -a == <$ty as Ring>::ZERO - a);
                }

                #[test]
                fn square_matches_pow2() {
                    check_pairs::<$ty>(|a, _b| a.square() == a.pow(2));
                }

                #[test]
                fn field_inverses() {
                    // Only meaningful for prime moduli; skipped otherwise.
                    if !<$ty as Ring>::IS_PRIME {
                        return;
                    }
                    check_pairs::<$ty>(|a, _b| {
                        a == <$ty as Ring>::ZERO || a * a.inverse().unwrap() == <$ty as Ring>::ONE
                    });
                }

                #[test]
                fn two_adic_generator_order() {
                    // For prime moduli, g = two_adic_generator(b) must have
                    // order exactly 2^b, for every b <= TWO_ADICITY.
                    if !<$ty as Ring>::IS_PRIME {
                        return;
                    }
                    for bits in 0..=<$ty as TwoAdicRing>::TWO_ADICITY as usize {
                        let g = <$ty as TwoAdicRing>::two_adic_generator(bits);
                        let order = 1u64 << bits;
                        assert_eq!(g.pow(order), <$ty as Ring>::ONE, "g^(2^{bits}) != 1");
                        if bits > 0 {
                            assert_ne!(
                                g.pow(order / 2),
                                <$ty as Ring>::ONE,
                                "g^(2^{}/2) == 1: order too small",
                                order
                            );
                        }
                    }
                }

                #[test]
                fn centered_ring_semantics() {
                    let q = <$ty as Ring>::MODULUS as i64;
                    for a in representatives::<$ty>() {
                        let c = a.centered();
                        // centered stays in (-q/2, q/2]
                        assert!(c > -q / 2 && c <= (q + 1) / 2, "centered {c} out of range for q={q}");
                        // centered(a) ≡ a (mod q)
                        assert_eq!((c as i128).rem_euclid(q as i128) as u64, a.to_u128() as u64 % <$ty as Ring>::MODULUS);
                        // |c| == abs_infinity
                        assert_eq!(c.unsigned_abs(), a.abs_infinity());
                    }
                    // zero and one norms
                    assert_eq!(<$ty>::ZERO.abs_infinity(), 0);
                    assert_eq!(<$ty>::ONE.abs_infinity(), 1);
                    assert!(<$ty>::ZERO.leq_infinity(0));
                    assert!(!<$ty>::ONE.leq_infinity(0));
                }
            }
        )*
    };
}

ring_axiom_tests! {
    zq2 => Zq2,
    zq3 => Zq3,
    zq5 => Zq5,
    zq13 => Zq13,
    zq17 => Zq17,
    zq97 => Zq97,
    zq257 => Zq257,
    zq3329 => Zq3329,           // FIPS 203
    zq7681 => Zq7681,
    zq12289 => Zq12289,         // FIPS 206 (Falcon)
    zq65537 => Zq65537,
    zq786433 => Zq786433,       // 1 + 3 * 2^18
    zq_mersenne31 => ZqMersenne31,
    zq_dilithium => ZqDilithium, // FIPS 204
    zq_la_brador => ZqLaBrador,  // 2^32, exercises the composite-modulus path
}
