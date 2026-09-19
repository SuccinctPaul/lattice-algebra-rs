use crate::ring::reduction::ModularArithmetic;
use crate::ring::zq::Zq;

/// Modular arithmetic for `Zq<MODULUS>`.
///
/// Multiplication uses 128-bit intermediate arithmetic ("Barrett-style"
/// native modulo), which modern compilers lower to efficient code for
/// 64-bit moduli. Precondition for all methods: operands are already
/// reduced, i.e. `< MODULUS`.
impl<const MODULUS: u64> ModularArithmetic<MODULUS> for Zq<MODULUS> {
    /// Modular addition: (a + b) mod MODULUS
    ///
    /// # Precondition
    /// a, b < MODULUS
    #[inline(always)]
    fn mod_add(a: u64, b: u64) -> u64 {
        let (sum, carried) = a.overflowing_add(b);
        // `carried` means the true sum is `sum + 2^64`, which the conditional
        // subtract below cannot reach. It requires MODULUS > 2^63, and there
        // 2^64 = MODULUS + (2^64 - MODULUS) with 0 < 2^64 - MODULUS <
        // MODULUS, so the carry reduces to that residue. Adding it stays inside
        // u64 (sum < MODULUS, residue < MODULUS, MODULUS <= u64::MAX) and one
        // further conditional subtract finishes the job.
        if carried {
            let sum = sum.wrapping_add(MODULUS.wrapping_neg());
            if sum >= MODULUS {
                sum - MODULUS
            } else {
                sum
            }
        } else if sum >= MODULUS {
            sum - MODULUS
        } else {
            sum
        }
    }

    /// Modular subtraction: (a - b) mod MODULUS
    ///
    /// # Precondition
    /// a, b < MODULUS
    #[inline(always)]
    fn mod_sub(a: u64, b: u64) -> u64 {
        if a >= b {
            a - b
        } else {
            MODULUS - (b - a)
        }
    }

    /// Modular multiplication: (a * b) mod MODULUS
    ///
    /// Power-of-two moduli (the LaBRADOR-style `q = 2^32` instance) reduce
    /// by masking; everything else uses 128-bit arithmetic to avoid
    /// overflow. The branch folds away under monomorphization in release
    /// builds and is perfectly predicted in debug builds.
    ///
    /// # Precondition
    /// a, b < MODULUS
    #[inline(always)]
    fn mod_mul(a: u64, b: u64) -> u64 {
        if (MODULUS & (MODULUS - 1)) == 0 {
            a.wrapping_mul(b) & (MODULUS - 1)
        } else {
            ((a as u128 * b as u128) % (MODULUS as u128)) as u64
        }
    }

    /// Barrett reduction for arbitrary 128-bit value
    #[inline(always)]
    fn barrett_reduce(x: u128) -> u64 {
        if (MODULUS & (MODULUS - 1)) == 0 {
            (x as u64) & (MODULUS - 1)
        } else {
            (x % (MODULUS as u128)) as u64
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn test_mod_mul_small_modulus() {
        // Test with small modulus
        type Zq17 = Zq<17>;
        assert_eq!(Zq17::mod_mul(6, 3), 1); // 6*3=18 ≡ 1 (mod 17)
        assert_eq!(Zq17::mod_mul(5, 4), 3); // 5*4=20 ≡ 3 (mod 17)
        assert_eq!(Zq17::mod_mul(16, 16), 1); // 16*16=256 ≡ 1 (mod 17)
    }

    #[test]
    fn test_mod_mul_large_modulus() {
        // Test with large modulus (> 2^32)
        const LARGE_MOD: u64 = (1u64 << 40) + 7;
        type ZqLarge = Zq<LARGE_MOD>;

        // Test basic multiplication
        let a = 12345678901234u64 % LARGE_MOD;
        let b = 98765432109876u64 % LARGE_MOD;
        let expected = ((a as u128 * b as u128) % (LARGE_MOD as u128)) as u64;
        let result = ZqLarge::mod_mul(a, b);
        assert_eq!(
            result, expected,
            "Modular multiplication failed for large modulus"
        );

        // Test edge cases
        assert_eq!(ZqLarge::mod_mul(0, b), 0);
        assert_eq!(ZqLarge::mod_mul(a, 0), 0);
        assert_eq!(ZqLarge::mod_mul(1, b), b);
        assert_eq!(ZqLarge::mod_mul(a, 1), a);
    }

    #[test]
    fn test_mod_mul_kyber_modulus() {
        // Test with Kyber's modulus q = 3329
        type Zq3329 = Zq<3329>;
        assert_eq!(Zq3329::mod_mul(1000, 2000), 1000u64 * 2000 % 3329);
        assert_eq!(Zq3329::mod_mul(3328, 3328), (3328u64 * 3328) % 3329);
    }

    #[test]
    fn test_mod_mul_dilithium_modulus() {
        // Test with Dilithium's modulus q = 8380417
        const Q: u64 = 8380417;
        type ZqDilithium = Zq<Q>;

        let a = 1234567u64;
        let b = 7654321u64;
        let expected = ((a as u128 * b as u128) % (Q as u128)) as u64;
        assert_eq!(ZqDilithium::mod_mul(a, b), expected);
    }

    #[test]
    fn test_mod_mul_max_values() {
        // Test with maximum 64-bit modulus
        const MAX_MOD: u64 = u64::MAX - 58; // A large prime
        type ZqMax = Zq<MAX_MOD>;

        let a = MAX_MOD - 1;
        let b = MAX_MOD - 2;
        let expected = ((a as u128 * b as u128) % (MAX_MOD as u128)) as u64;
        assert_eq!(ZqMax::mod_mul(a, b), expected);
    }

    #[test]
    fn test_mod_add_sub() {
        type Zq17 = Zq<17>;

        // Addition
        assert_eq!(Zq17::mod_add(5, 13), 1); // 5+13=18 ≡ 1
        assert_eq!(Zq17::mod_add(0, 16), 16);
        assert_eq!(Zq17::mod_add(16, 1), 0);

        // Subtraction
        assert_eq!(Zq17::mod_sub(3, 5), 15); // 3-5 = -2 ≡ 15
        assert_eq!(Zq17::mod_sub(5, 3), 2);
        assert_eq!(Zq17::mod_sub(0, 1), 16);
    }

    /// Differential check of the three reductions against a `u128` reference at
    /// moduli where `a + b` overflows 64 bits, which the historical single
    /// conditional subtract silently dropped.
    fn check_reductions_against_reference<const M: u64>() {
        use rand::rngs::StdRng;
        use rand::{Rng, SeedableRng};

        let m = u128::from(M);
        let mut values = vec![0u64, 1, 2, M - 1, M - 2, M / 2, M / 2 + 1, M / 3 + 1];
        let mut rng = StdRng::seed_from_u64(0x5EED_1234);
        values.extend((0..48).map(|_| rng.random_range(0..M)));

        for &a in &values {
            for &b in &values {
                let (au, bu) = (u128::from(a), u128::from(b));
                assert_eq!(
                    <Zq<M> as ModularArithmetic<M>>::mod_add(a, b),
                    ((au + bu) % m) as u64,
                    "mod_add({a}, {b}) mod {M}"
                );
                assert_eq!(
                    <Zq<M> as ModularArithmetic<M>>::mod_sub(a, b),
                    ((au + m - bu) % m) as u64,
                    "mod_sub({a}, {b}) mod {M}"
                );
                assert_eq!(
                    <Zq<M> as ModularArithmetic<M>>::mod_mul(a, b),
                    ((au * bu) % m) as u64,
                    "mod_mul({a}, {b}) mod {M}"
                );
            }
        }
    }

    #[test]
    fn reductions_at_moduli_just_above_2_63() {
        check_reductions_against_reference::<18446744073709551557>(); // u64::MAX - 58, prime
        check_reductions_against_reference::<18446744069414584321>(); // Goldilocks, 2^64 - 2^32 + 1
        check_reductions_against_reference::<9223372036854775809>(); // 2^63 + 1
    }

    #[test]
    fn reductions_at_the_top_and_bottom_of_the_domain() {
        check_reductions_against_reference::<18446744073709551615>(); // u64::MAX, composite: largest legal q
        check_reductions_against_reference::<2305843009213693951>(); // 2^61 - 1, Mersenne prime
        check_reductions_against_reference::<9223372036854775783>(); // largest prime below 2^63
    }

    /// The pre-fix reduction: one conditional subtract after a `wrapping_add`.
    /// Kept here so the fixtures above are demonstrably load-bearing rather
    /// than merely passing.
    const fn legacy_mod_add(a: u64, b: u64, modulus: u64) -> u64 {
        let sum = a.wrapping_add(b);
        if sum >= modulus {
            sum - modulus
        } else {
            sum
        }
    }

    #[test]
    fn carry_out_of_u64_is_what_the_fix_handles() {
        const M: u64 = 18446744073709551557; // u64::MAX - 58, prime
        let (a, b) = (M - 1, M - 1);
        let correct = (((a as u128) + (b as u128)) % (M as u128)) as u64;

        // The fixtures distinguish the two implementations: the legacy form
        // silently drops the 2^64 carry ...
        assert_ne!(
            legacy_mod_add(a, b, M),
            correct,
            "test fixture no longer exercises the carry path"
        );
        // ... while the shipped one returns the reference value.
        assert_eq!(
            <Zq<M> as ModularArithmetic<M>>::mod_add(a, b),
            correct,
            "mod_add must fold the carry back as (2^64 mod q)"
        );
    }

    #[test]
    fn test_mod_arithmetic_consistency() {
        // Verify that mod operations are consistent with ring axioms
        type Zq101 = Zq<101>;

        for a in 0..101u64 {
            for b in 0..101u64 {
                // Addition is correct
                let sum = Zq101::mod_add(a, b);
                assert_eq!(sum, (a + b) % 101);

                // Subtraction is correct
                let diff = Zq101::mod_sub(a, b);
                assert_eq!(diff, ((a as i64 - b as i64).rem_euclid(101)) as u64);

                // Multiplication is correct
                let prod = Zq101::mod_mul(a, b);
                assert_eq!(prod, (a * b) % 101);
            }
        }
    }
}
