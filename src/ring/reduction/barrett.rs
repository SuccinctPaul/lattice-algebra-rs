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
        let sum = a.wrapping_add(b);
        if sum >= MODULUS {
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
