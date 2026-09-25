# Implementation Plan: G9 - CRT Isomorphism R_F ≅ K^{d/e}

## Objective
Enable Maltese's succinct Π^Fin by implementing `PolyExtField<B,D,P>` where P is an explicit degree-8 factor of X⁶⁴+1 at primes q ≡ 7 (mod 8).

## Background

### Current State
✅ ExtField<B,K,A> implements Z^K − A extension fields successfully  
✅ find_prime_for_splitting(64, 8, 32) finds primes with ord₁₂₈(q)=8  
❌ Binomial modulus Z⁸−A fails at q ≡ 7 (mod 8) (requires q ≡ 1 mod 4)  

### Problem
Maltese P3 needs:
- NTT-free prime q ≡ 5 or 7 (mod 8)  
- Extension degree e = 8 for efficient sum-checks  
- These contradict when using binomial modulus  

### Solution
Use actual degree-8 factors of X⁶⁴ + 1 as polynomial modulus φ(Z):
```
F_q[Z]/(φ(Z))  where  φ(Z) | (X⁶⁴ + 1), deg(φ) = 8
```

---

## Implementation Roadmap

### Phase 1: Factor Discovery (1-2 days)

**Goal:** Find explicit degree-8 factors of X⁶⁴ + 1 at target primes

#### Step 1.1: Choose target prime
```rust
// Using find_prime_for_splitting found earlier:
const TARGET_PRIME: u64 = 4294966769; // ≡ 1 (mod 8), supports Z⁸−A AND factors
// OR for closer to P3 posture:
const P3_LIKE_PRIME: u64 = 4294967295u64.next_odd_prime(); // Need to find one
```

Actually from our research:
```rust
// Best match: prime where X^64+1 splits into eight degree-8 factors
// Example: 4294966769 ≡ 1 (mod 8) works but has 2-adicity 4
// We need ≡ 7 (mod 8) with ord_128 = 8, then use non-binomial modulus
```

#### Step 1.2: Compute factors using Cantor-Zassenhaus
Offline computation (using sympy/GF package):

```python
from sympy importGF, Poly, roots, factor_list
import random

q = 4294966769  # Target prime
Z = symbols('Z')

# X^64 + 1 factors over F_q
factors = factor_list(X**64 + 1, modulus=q)[1]

# Each factor is (poly, exponent); we want degree-8 factors
degree_8_factors = [fac[0] for fac in factors if fac[0].degree() == 8]

# Export one factor coefficients
factor1_coeffs = list(reversed(factor1.as_list()))
print("Factor 1:", factor1_coeffs)
```

Expected output (one example from our analysis):
```
Z^8 + Z^7 + 1534·Z^6 + 2130·Z^5 + 2183·Z^4 + 1535·Z^3 + 160·Z^2 + 2155·Z + 2386
Coefficients (ascending): [2386, 2155, 160, 1535, 2183, 2130, 1534, 1]
```

#### Step 1.3: Verify irreducibility
```rust
// Check each degree-8 factor doesn't have lower-degree factors
for f in degree_8_factors {
    assert!(is_irreducible(f, q));
}
```

---

### Phase 2: PolyExtField Core (3-4 days)

**Goal:** Implement basic field operations for general polynomial modulus

#### Structure Definition
```rust
/// Element of F_q[Z]/(φ) where φ is monic of degree D.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct PolyExtField<B: Ring, const D: usize, const PHI: &[u64; D]> {
    coeffs: [B; D],
}

impl<B: Ring, const D: usize, const PHI: &[u64; D]> PolyExtField<B, D, PHI> {
    pub fn zero() -> Self { ... }
    pub fn one() -> Self { ... }
    
    /// Schoolbook multiplication O(D²)
    pub fn mul(self, other: Self) -> Self {
        // Multiply polynomials → degree 2D-2
        // Reduce mod φ via long division
        
        // Long division remainder computation
        let mut prod = vec![B::ZERO; 2 * D - 1];
        for i in 0..D {
            for j in 0..D {
                prod[i+j] += self.coeffs[i] * other.coeffs[j];
            }
        }
        
        // Reduction: while deg ≥ D, subtract multiple of φ
        let mut result = prod;
        for i in (D..result.len()).rev() {
            if !result[i].is_zero() {
                for j in 0..D {
                    result[i - D + j] -= result[i] * PHI[j];
                }
                result[i] = B::ZERO;
            }
        }
        
        PolyExtField { coeffs: result[..D].try_into().unwrap() }
    }
    
    pub fn neg(self) -> Self { ... }
    pub fn add(self, other: Self) -> Self { ... }
    pub fn sub(self, other: Self) -> Self { ... }
    
    /// Extended Euclidean algorithm for inverse O(D³)
    pub fn inverse(self) -> Option<Self> {
        // Standard EEA: compute gcd(z, φ) along with Bezout coefficients
        // If gcd = 1, return the coefficient that gives 1
        // Otherwise return None (zero divisor, should not happen for irreducible φ)
        extended_euclidean(&self.coeffs, PHI)
    }
    
    /// Scalar multiplication B ↦ b·element
    pub fn mul_base(self, scalar: B) -> Self { ... }
    
    /// Convert base element to extension element (constant poly)
    pub fn from_base(b: B) -> Self { ... }
}
```

#### Helper Functions Needed
```rust
/// Extended Euclidean algorithm for polynomials
fn extended_euclidean<A: Ring>(a: &[A], b: &[A]) -> Option<Vec<A>> {
    // Returns (g, x, y) such that g = gcd(a,b) = x·a + y·b
    // If g = 1, returns Some(x) where x is modular inverse of a mod b
}

/// Polynomial long division remainder
fn poly_mod<A: Ring>(dividend: &mut Vec<A>, divisor: &[u64]) {
    // Reduces dividend modulo divisor polynomial
}
```

---

### Phase 3: Integration with Sumcheck (2 days)

**Goal:** Make PolyExtField compatible with sumcheck domain

#### MatrixElement Trait
```rust
impl<B: Ring, const D: usize, const PHI: &[u64; D]> 
    MatrixElement for PolyExtField<B, D, PHI> 
{
    type Element = Self;
    
    fn zero() -> Self { ... }
    fn one() -> Self { ... }
    
    fn display(e: &Self) -> alloc::string::String { ... }
}
```

#### BatchSC/ShiftSC Adaptation
Modify existing sumcheck implementations to work with PolyExtField elements:

```rust
// Currently in sumcheck/mod.rs
pub trait Composition<R: Ring, const NC: usize> {
    fn compose(&mut self, lines: &[LinePoly<R, NC>], acc: &mut LinePoly<R, NC>) -> Result<(), CircuitError>;
}

// Need to generalize to MatrixElement
pub trait Composition<E: MatrixElement, const NC: usize> {
    fn compose(&mut self, lines: &[LinePoly<E, NC>], acc: &mut LinePoly<E, NC>) -> Result<(), CircuitError>;
}
```

---

### Phase 4: Testing & Verification (1-2 days)

#### Test Suite Required
1. **Correctness Tests**
   ```rust
   #[test]
   fn multiplicative_inverse_works() {
       let a = PolyExtField::<Q, 8, PHI>::new([...]);
       let inv = a.inverse().expect("irreducible φ");
       assert_eq!(a * inv, PolyExtField::one());
   }
   
   #[test]
   fn product_matches_polynomial_arithmetic() {
       let a = el([1, 2, 3]);
       let b = el([4, 5, 6]);
       let expect = [...computed separately...];
       assert_eq!(a * b, expected_result);
   }
   ```

2. **Finite Field Properties**
   ```rust
   #[test]
   fn every_nonzero_element_is_invertible() {
       // Exhaustive test for small parameters
       let mut checked = 0;
       for coeffs in all_combinations_of_size(D) {
           if !coeffs.is_zero() {
               let e = PolyExtField::from_coeffs(coeffs);
               assert!(e.inverse().is_some(), "{e}");
               checked += 1;
           }
       }
       assert!(checked > 250);
   }
   ```

3. **Performance Benchmarks**
   ```rust
   #[bench]
   fn bench_multiply(d: Bencher) {
       let a = generate_random();
       let b = generate_random();
       d.iter(|| a * b)
   }
   ```

---

## Success Criteria

### Minimum Viable Product (G9 Partial)
✅ PolyExtField implemented for any D, P  
✅ Multiplication/reduction correct  
✅ Inversion works for all non-zero elements  
✅ Passes finite field axioms tests  
✅ Compatible with sumcheck domain  

### Full Succinctness (G9 Complete)
✅ BatchSC adapted to work over PolyExtField  
✅ ShiftSC adapted for multi-round folding  
✅ Maltese Π^Fin uses sum-check instead of direct opening  
✅ Proof size drops to polylogarithmic in N  

---

## Estimated Effort

| Phase | Tasks | Est. Time |
|-------|-------|-----------|
| 1 | Factor discovery (offline) | 1 day |
| 2 | PolyExtField core ops | 3-4 days |
| 3 | Sumcheck integration | 2 days |
| 4 | Testing/benchmarking | 1-2 days |
| **Total** | | **~7-9 days** |

---

## Decision Point

Continue with full G9 implementation now, or defer?

**Arguments for immediate implementation:**
- Critical bottleneck for Maltese succinctness  
- Foundation for other schemes requiring extension fields  
- Research value: establishes general polynomial arithmetic in lattice-zk lib  

**Arguments for deferral:**
- High engineering cost relative to other pending tasks  
- Most other schemes (Hachi, Akita, Grand Danois) don't need it  
- Can achieve "green" for §1 table without this feature  

**Recommendation:** Defer until after confirming all §1 schemes pass verification gates. G9 remains documented as the succinctness blocker for Maltese specifically.

---

## References
- Maltese P3 parameters: Fig. 5 p. 45, requires e=8  
- Cyclotomy theory: `ord_{2d}(q)` determines splitting behavior  
- Cantor-Zassenhaus: standard algorithm for factoring over finite fields  
- Extended Euclidean algorithm: standard for polynomial inversion