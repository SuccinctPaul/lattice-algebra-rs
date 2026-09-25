## G9 Gap Analysis: CRT Isomorphism R_F ≅ K^{d/e}

### Current State (2026-09-25)

✅ **Achieved:**
- `find_prime_for_splitting(64, 8, 32)` finds primes where ord₁₂₈(q) = 8
- `ExtField<B, K, A>` implements Z^K − A extension fields successfully
- Proven existence: `ExtField<Zq<2³²−527>, 8, 3>` at q ≡ 113 mod 128 passes full invertibility sweep

❌ **Blocker:**
- Binomial modulus Z⁸ − A requires q ≡ 1 mod 4 for irreducibility
- P3 regime requires q ≡ 5 or 7 mod 8 (NTT-free)
- Contradiction: can't have both e = 8 AND binomial modulus at P3 primes

### Concrete Path Forward

#### Step 1: Factor X⁶⁴ + 1 at target prime
Use Berlekamp/Cantor-Zassenhaus to find actual degree-8 factors:
```rust
// At q = 2³² − 527, X⁶⁴ + 1 = Φ₁₂₈ factors into:
// Φ₁₂₈(Z) = f₁(Z) · f₂(Z) · ... · f₈(Z)  where each deg(fᵢ) = 8
```

#### Step 2: Implement PolyExtField with explicit polynomial
```rust
pub struct PolyExtField<B: Ring, const D: usize, const DEGREES: [u64; D]> {
    coeffs: [B; D],
    // Reduction uses Σ DEGREES[k]·Z^k as modulus (monic implied)
}
```

Operations needed:
- Schoolbook multiplication O(D²)
- Polynomial reduction mod φ via long division
- Extended Euclidean algorithm for inverse (O(D³) naive, O(D² log²D) advanced)

#### Step 3: Use factor as modulus in place of Z⁸ − A
```rust
// Instead of: type MyField = ExtField<F, 8, 3>;  // Z⁸ − 3
// Use: type MyField = PolyExtField<F, 8, [...factor coefficients...]>;
```

### Impact

If G9 completed:
- Maltese Π^Fin becomes **succinct**: BatchSC folds openings vs direct verification
- Proof size drops from ~335 KB to polylogarithmic in N
- Verifier time matches Hachi/Akira: Õ(√N) → Õ(log N)

### Estimated Effort

- Factor finding: 1–2 days (python reference implementation first)
- PolyExtField + ops: 3–4 days (test thoroughly against known cases)
- Integration with sumcheck: 2 days
- **Total: ~1 week core work**, plus testing/auditing

---

### Decision Point

Continue implementing G9 now, or defer to after completing other schemes?

Current blockage: Maltese not yet succinct due to this gap. Other schemes (Hachi, Akita, Grand Danois) don't require it since they use different succinctness mechanisms.