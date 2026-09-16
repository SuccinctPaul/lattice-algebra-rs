# Lattice-based zkSNARK Primitives Survey

> Scope: lattice-based zkSNARK / folding / batch-argument schemes and the
> **reusable cryptographic primitives** they are built from.
> Outcomes land in two places: the implementations in this crate (see §2,
> the primitive → implementation map) and the explicitly tracked open items
> (the ⏳ rows at the end of §2).
> Scheme names and terminology stay in English; notation follows crate
> conventions: `R = Z_{2^32}[X]/(X^64+1)` (the folding ring),
> `R_q = Z_q[X]/(X^256+1)` (the ML-DSA ring), Ajtai commitment `c = A·w`
> (`A` expanded from a seed, `w` short).
>
> Citations were checked against eprint full texts / metadata; items that
> could not be verified are marked as such.

## 0. One-paragraph summary

Every mainstream lattice zkSNARK is built from the same set of reusable
primitives: **Ajtai/SIS commitments + small-norm challenge sampling
(hyperball / fixed-weight sparse / non-unit linear `X−a`) + amortized
batched openings (linear combinations / inner products) + gadget and b-bit
decompositions (approximate shortness, norm control) + ring sumcheck +
folding (homomorphic commitment updates, batch decomposition checks,
cross-term absorption) + Fiat–Shamir (2-adic rings demand non-unit /
strong-sampling challenge sets)**. The `zk` crate provides all of these at
the primitive layer. Milestone history: Z1–Z4 landed the base versions;
three later rounds added the previously missing pieces — the **hyperball
sampler**, the **digit-based projection argument**
(`shortness::balanced`), **LatticeFold-style decomposition folding**
(`folding::latticefold`), the **MatRiCT fixed-weight sampler**, the **JL
projection argument** (`shortness::projection`), the **recursive
full-relation opening mode** (`opening::prove_recursive`), the **Z2
blinded Σ-protocol** (`sigma::z2`), and the **integer lift / 2-adic
ModSwitch / strong-sampling-set** helpers (`instance::ring`,
`foundation::sampling`).

## 1. Schemes and their primitives

### 1.1 LaBRADOR (Beullens–Seiler, CRYPTO 2023, eprint 2022/1341)

Transparent R1CS proofs (the paper's statement language is R1CS **mod
2^64+1** over the ring `Z_q[X]/(X^64+1)` with prime `q ≡ 5 mod 8`; 58 KB
for 10^6 constraints). Note the paper's ring is **not** `Z_{2^32}` — this
repository's `opening` module is an isomorphic 2-adic simplified variant.

Primitives:
1. **Ajtai/SIS commitments**: `C = A·s`, linearly homomorphic, no trapdoor,
   no noise;
2. **Amortized dot-product batched opening**: r inner-product constraints
   proved at once via a small-norm linear combination; coefficient norms
   grow as `√(r·τ)`, and each round applies a **base-b digit
   decomposition** `z = z₀ + b·z₁` to push the witness back to small norms
   (recursive amortization);
3. **HyperBall challenge sampling**: challenges uniform inside an
   l1/l∞ ball (the `hyperball` module in the lattirust implementation);
   the norm budget feeds the soundness accounting directly;
4. **Projection argument (modular Johnson–Lindenstrauss, GHL21)**: the
   verifier draws a random projection `Π: Z_q^{dn} → Z_q^{256}`, the
   prover sends `p = Π·s`; the correctness of `p` is exactly 256 extra
   constant-term inner-product equations carried "for free" by the
   batched proof; accepting `‖p‖₂ ≤ √128·B` implies w.o.p.
   `‖s‖₂ ≲ √(128/30)·B ≈ 2.07·B`;
5. **Invertibility (non-unit) lemma (Lyubashevsky–Seiler, eprint
   2017/523)**: for `q ≡ 5 (mod 8)` every small-norm non-zero element is
   invertible, so challenge differences `a−b` are invertible and the
   extraction equations have no zero divisors. The 2-adic counterpart is
   "odd-element challenges" (see §1.5).

### 1.2 Greyhound (Nguyen–Seiler, CRYPTO 2024, eprint 2024/1293)

The first concretely efficient polynomial commitment from standard lattice
assumptions (53 KB evaluation proofs at `N = 2^30`); combined with
LaBRADOR it forms a full SNARK.

Primitives:
1. **Gadget matrix and `G^{-1}`**: `G_n = I_n ⊗ [1,2,…,2^{δ−1}]`;
   `G^{-1}(t)` is the entry-wise binary decomposition — the base
   building block for approximate/exact shortness;
2. **Two-layer commitments**: inner (the gadget-decomposed digits,
   LaBRADOR-style Ajtai) + outer (quotients / cross terms);
3. **Quotient polynomial commitments**: `f(X) − y` is divisible by the
   **linear factor `X − a`** — commit to the bounded-coefficient quotient
   `q(X)` directly (`X−a` itself has `‖·‖∞ ≤ 2` and needs no inverse):
   the PCS form of the "non-unit linear challenge";
4. Split-and-fold, halving the degree each round, with an amortized
   Σ-protocol at the bottom.

### 1.3 LatticeFold / LatticeFold+ (Boneh–Chen, eprint 2024/257 / 2025/247)

Lattice folding for IVC/SNARKs (the Nova counterpart). The instance
interface `R_hom`: `y = A·f` (Ajtai) ∧ `‖f‖∞ < B` ∧ `mle[f](r) = v̂` — the
witness is simultaneously committed, norm-bounded and multilinearly
evaluated; the three assertions are carried by the linear check, the norm
check and the **ring sumcheck** respectively.

Primitives (all verified against the paper):
1. **Batch decomposition (`split_{b,k}`, quotient/residue checks)**: write
   the coefficients in base b with k digits, `f = Σ b^i·f_i`
   (`‖f_i‖∞ < b = ⌈B^{1/k}⌉`); the verifier checks
   `Σ b^i·A·f_i == A·f` and `Σ b^i·v̂_i == v̂` — exact linear identities;
   violating them yields a short kernel vector (an MSIS break);
2. **Combination lemma**: `A·(Σρᵢfᵢ) = Σρᵢ·(A·fᵢ)` for arbitrary ring
   weights `ρᵢ` — the algebraic basis for folding weights;
3. **Strong-sampling-set challenges**: the folding challenge `ρ` comes
   from `{a : a−b invertible}` (`C = Z_q` when the NTT splits fully; for
   small moduli the NTT-slot diagonal set `|C| = q^τ ≈ 2^128`); the
   small-challenge subset `C_small` requires expansion factor
   `‖C_small‖_op ≤ c`;
4. **Vanishing-polynomial norm check**: `g(u) = ∏_{i∈[b]}(X−i)(X+i)` has
   zero set exactly `[−b, b]`; a sumcheck over the ℓ variables proves
   "every digit is in range" — the sumcheck carries both folding validity
   and the norm bound;
5. **Multi-assertion batched sumcheck (Π_batch)**: linearization,
   multilinear evaluation, range and CCS gate checks merged into a single
   sumcheck with `(β, γ, α, μ, ζ)` weights;
6. **Nova-style cross-term absorption**: `C_o = C₁ + ρ·C₂ + …` with the
   cross terms absorbed via separate Ajtai commitments `u_j` (Ajtai has no
   noise; the only difficulty is norm growth, handled by 1 + 4).

(This crate's `folding::latticefold` = the reusable core of primitives
1 + splitting query + homomorphic folding; `folding::nova` is the
Nova-style relaxed-R1CS line — the two are complementary.)

### 1.4 LaZer Library (Lyubashevsky–Seiler–Steuer, CCS 2024, eprint 2024/1846)

A layered lattice-proof library engineering the LaBRADOR/LNP22 framework
(AVX-512 NTT base). Verified core techniques:
1. **mod-p → R_q lift**: the integer statement `A·s ≡ t (mod p)` becomes
   `A·s + p·v = t` over `R_q` (with an extra short secret `v` guarding
   against overflow);
2. **Random-challenge-matrix approximate shortness**:
   `u = T·[s; v] + y` (`T` a small integer matrix, `y` a short mask) —
   small `‖u‖` implies `s, v` are short and overflow-free with
   overwhelming probability;
3. Mask commitments + the amortized Σ-protocol (the Ajtai form of ZK
   blinding); ALS20 product proofs handle Boolean constraints.

### 1.5 Rinocchio (Ganesh–Nitulescu–Soria-Vazquez, CCS 2022, eprint 2021/322)

**QRP (Quadratic Ring Programs)**: the QAP-style encoding framework
generalized to commutative rings (`Z_p[X]/(X^d+1)`, `Z_{2^k}`),
designated-verifier. Primitives: extractable ring-encoding commitments,
divisibility checks against a target polynomial, and the requirement that
**2-adic challenges must be odd elements** (the non-zero-divisor/unit
subset) — the same lineage as this crate's `nonunit_linear_poly`
(`C = X − a`, `a` odd).

### 1.6 SLAP (Albrecht–Fenzi–Lapiha–Nguyen, EUROCRYPT 2024, eprint 2023/1469)

The first non-interactive extractable polynomial commitment from standard
assumptions, with polylog proof/verification. Primitives: **tree-based
Ajtai commitments** (a vector hash tree), split-and-fold evaluation with
decreasing challenges, and the "challenge-space size vs extraction slack"
trade-off analysis (contrasted with the subtractive-set limitation of
Bulletproofs-style lattice folding).

### 1.7 Ligetron (Wang–Hazay–Venkitasubramaniam, IEEE S&P 2024,
DOI 10.1109/SP54263.2024.00086)

**Not lattice-based**: a space-efficient Ligero variant (Merkle/hash
commitments; post-quantum via hashing) + a WASM front end. Listed for
contrast only — "post-quantum SNARK" ≠ "lattice SNARK".

### 1.8 MatRiCT / MatRiCT-Au / MatRiCT+ (eprint 2019/1287 (CCS 2019) /
CCS 2020 / 2021/545 (S&P 2022); Esgin–Zhao–Steinfeld–Liu–Liu et al.)

Payment-privacy application stack on the ESLL19 toolbox:
1. **Fixed-Hamming-weight sparse challenges**
   `C^d_{w,p} = {deg < d, HW = w, non-zero amplitude = p}` — keeps `c·s`
   short and `c−c′` non-zero (this crate's `in_ball_poly` is the `p = 1`
   special case; `fixed_weight_poly` is the general shape);
2. **Bit-decomposition range proofs** (amount bounds) and one-out-of-many
   (anonymity sets);
3. **FS with aborts** (rejection sampling; it appears 19 times in the
   paper).

### 1.9 The Lyubashevsky-line Σ-protocol toolbox (the modern context for
`sigma`)

- **ESLL19** (CRYPTO 2019): new techniques for short small-norm
  challenges/responses;
- **LNS21** (eprint 2020/1183) / **LNP22** (eprint 2022/284, CRYPTO 2022):
  the current standard framework — uniform/sparse challenges + **bimodal
  rejection sampling** + gadget-decomposition parameters + approximate
  range/norm proofs + product proofs; Biscuit and LaZer build on it;
- **BLOOM** (eprint 2022/1307): the ±c bimodal challenge distribution
  removes the rejection overhead for large anonymity sets;
- **ACL'22** (CRYPTO 2022): lattice SNARKs + recursive composition (PCD),
  the early form of "Nova on lattices";
- **FS-with-aborts analysis**: eprint 2023/245, 2023/246.

### 1.10 The lattice folding ecosystem (2024–2026, existence verified)

After LatticeFold: **Lova** (2024/1964, unstructured lattices),
**Neo / SuperNeo** (2025/294 / 2026/242, small-field pay-per-bit),
**SALSAA** (2025/2124), **Symphony** (2025/1905), **Cyclo** (2026/359),
**PikkuFold** (2026/1809), **LatticeBlindFold** (2026/1857, ZK folding),
**"Improving LatticeFold+ with ℓ₂-norm checks"** (2026/721). Shared
primitives: homomorphic commitment updates, explicit cross-term
commitments, large challenge spaces, per-round norm management
(decomposition / modulus switching / scaling).

> Note: the frequently conflated names "Alpine / Shadow / Grease" could
> not be located (a full title scan of eprint 2024–2025 found nothing);
> the ecosystem list above sticks to verifiable entries.

### 1.11 Shared foundations

- **MSIS / SelfTargetMSIS / LWE** assumptions (same family as ML-DSA;
  parameters calibratable with the lattice-estimator — this repository
  already ships a Core-SVP estimator in `algebra::security`);
- **2-adic ring semantics**: the unit criterion is the parity of the
  coefficient sum; `X` is always a unit; the ideal `(X−a)` for odd `a` has
  index 2 — no `Z_{2^k}` scheme can design challenges around this;
- **Fiat–Shamir**: domain-separated transcripts + per-shape re-expansion
  (the FIPS 203/204 pattern); FS soundness depends on the per-round
  challenge space being a strong-sampling set.

## 2. Primitive → implementation map (this crate)

| # | Primitive | Used by | Location in this crate | Status |
| --- | --- | --- | --- | --- |
| 1 | Ajtai/SIS commitment (seed-expanded key, linearly homomorphic) | all | `commitment::ajtai` (Z1 ring), `opening::Z2CommitKey`, `sumcheck::ipa::IpaKey`, `folding::nova::FoldKey`, `shortness::balanced::ShortKey`, `folding::latticefold::LfKey` | ✅ |
| 2 | uniform / CBD / centered-bounded sampling | LNP22-line, PQC | `foundation::sampling::{uniform_poly, cbd_poly, centered_bounded_poly}` | ✅ |
| 3 | fixed-weight sparse in-ball challenge (τ-sparse ±1) | Lyubashevsky-line, Dilithium | `foundation::sampling::in_ball_poly` | ✅ |
| 3b | **fixed-weight + amplitude challenge `C^d_{w,p}`** (any dimension) | MatRiCT, BLOOM | `foundation::sampling::fixed_weight_poly` | ✅ |
| 4 | non-unit linear challenge `X − a` (`a` odd) | Rinocchio (odd elements), Greyhound (quotient polys), 2-adic batched openings | `foundation::sampling::nonunit_linear_poly` | ✅ |
| 5 | **HyperBall challenge vectors** (`‖β‖∞ ≤ b ∧ ‖β‖₁ ≤ B`) | LaBRADOR (lattirust `hyperball`), LNP22 mask distributions | `foundation::sampling::hyperball_vec` | ✅ |
| 6 | amortized batched opening (masked quadratic terms `m_k/q_k`) | LaBRADOR, LNP22, LaZer | `opening` | ✅ |
| 7 | multilinear ring-sumcheck (any commutative ring, no inverses) | LatticeFold/+, Greyhound | `sumcheck` | ✅ |
| 8 | gadget-IPA (approximate opening) | Greyhound | `sumcheck::ipa` | ✅ |
| 9 | gadget split + provable slack | LaBRADOR recursion, LNP22 decompositions | `shortness::gadget::{gadget_split, approx_linear_check, slack_bound}` | ✅ |
| 10 | **digit-based projection / approximate shortness** (balanced `2^γ` split + exact link + norm gates) | LaBRADOR norm control (`z = z₀+b·z₁`), LNP22 decomposition arguments, MatRiCT range proofs | `shortness::balanced` | ✅ |
| 11 | **b-bit balanced batch decomposition** (quotient vanishes in `Z_{2^32}`, exact in the ring) | LatticeFold (`split_{b,k}` + `Π*_dec` checks), Neo/Cyclo | `folding::latticefold::{decompose_balanced, recompose}` | ✅ |
| 12 | **decomposition folding + splitting query + homomorphic fold** | LatticeFold/+, ACL'22 | `folding::latticefold::{prove_fold_decompose, verify_fold_decompose}` | ✅ |
| 13 | Nova-style folding / IVC (cross-term absorption, relaxed instances) | LatticeFold Expansion, ACL'22, Nova-line | `folding::nova` | ✅ |
| 14 | FS transcript (domain separation + per-shape re-expansion + non-unit challenges) | all | `foundation::fs` + `foundation::sampling::nonunit_linear_poly` + `algebra::crypto::transcript` | ✅ |
| 15 | discrete Gaussian sampling (CDT) | Falcon, some Σ-protocols | `algebra::crypto::sampling::DiscreteGaussian` | ✅ (algebra layer) |
| 16 | rejection sampling / FS with aborts (HVZK) | LNP22, MatRiCT, Dilithium | `sigma::fs_prove` (rejection loop) | ✅ |
| 17 | JL-variant projection argument (±1 entries, Hanson–Wright concentration) | full LaBRADOR (GHL21, tight √(128/30) gap) | `shortness::projection` (simplified variant: certified bound 2×B, k-parameterized confidence) | ✅ (tight GHL constants / amortized integration ⏳) |
| 18 | **ZK blinded Σ-response** (mask commitment first + small non-unit challenge + rejection sampling) | LaZer, LNP22, Biscuit (Z2-line HVZK) | `sigma::z2` | ✅ (the full LaZer integer-statement protocol ⏳) |
| 19 | LaBRADOR recursion (masked terms committed before the challenges open them → full relation soundness) | full LaBRADOR | `opening::{prove_recursive, verify_recursive}` (transparent full-relation mode, O(G) size) | ✅ (amortized size optimization ⏳) |
| 20 | multi-assertion batched sumcheck (β/γ/α/μ/ζ weights), vanishing-polynomial range check | LatticeFold Π_batch | — | ⏳ next step for `sumcheck` |
| 21 | 2-adic ModSwitch (coefficient-truncation ring homomorphism) + integer lift `A·s + 2^k·v = t` | Alpine/Shadow line, LaZer | `instance::ring::{modswitch_ring, split_mod_2k}` | ✅ (prime-ring switching ⏳) |
| 22 | **strong-sampling-set challenge** (invertible differences: odd sum = unit) | LatticeFold, LaBRADOR (LS18) | `foundation::sampling::odd_sum_poly` (+ small non-unit `nonunit_small_poly`) | ✅ (NTT-diagonal prime rings ⏳) |
| 23 | lookup / bit arguments (non-arithmetic constraints) | all (acknowledged weak spot) | — | ⏳ research branch |

## 3. Protocol details of the newer pieces (matching the code)

### 3.1 `foundation::sampling::hyperball_vec`

Rejection sampling on `{β ∈ R^k : ‖β‖∞ ≤ b, ‖β‖₁ ≤ B}`: coefficients are
drawn by masked rejection (uniform on `[-b, b]`) and the whole vector is
re-drawn while the total l1 budget is exceeded. Deterministic (XOF-driven)
and reproducible (KAT-friendly). Uses: batched-opening challenge vectors
and folding/splitting challenges — `‖ζ‖₁` feeds the norm gates directly.
The same module also provides `fixed_weight_poly` (MatRiCT `C^d_{w,p}`),
`nonunit_small_poly` (small non-unit challenges for 2-adic Σ-protocols)
and `odd_sum_poly` (strong-sampling-set draws).

### 3.2 `shortness::balanced` (digit-based projection argument)

Statement: with `c = A·w` public, prove `‖w − ζ·t‖∞ ≤ certified_bound(γ, B_h)`.

```text
v = w − ζ·t
v = 2^γ·h + l        ← balanced split: exact, ‖l‖∞ ≤ 2^{γ−1}
        ──h, l──▶    verify: A·(2^γ·h + l) == c − ζ·(A·t)  (exact link)
                     ‖l‖∞ ≤ 2^{γ−1}, ‖h‖∞ ≤ B_h            (norm gates)
```

Where the content is: the link is exact ⟹ the revealed `h` is the true
high part of `v` (a forger cannot shrink it); binding ⟹ `(h,l)` pins `v`
(a second accepting digit pair would give a short kernel vector).
Transparent design: the digits are short, so a recursion can re-commit
them under a fresh Ajtai key. Literature lineage: LaBRADOR's per-round
`z = z₀ + b·z₁` norm control, LNP22 decomposition arguments and
LatticeFold's quotient/residue checks — all instances of the
"decomposition digits + norm gates + linear identity" pattern. The
companion `shortness::projection` module implements the *other* LaBRADOR
mechanism (the l2 JL projection).

### 3.3 `shortness::projection` (JL projection argument)

Statement: with `c = A·w` public, certify `‖w‖₂ ≤ 2·B` by revealing
`p = Π·w` for a verifier-chosen ±1 projection `Π` (`k` rows). Acceptance
threshold `‖p‖₂ ≤ √(2k)·B`; the honest floor is `√(k/2)·‖w‖₂`
(Hanson–Wright), giving the 2× certified-bound gap. `k` parameterizes the
confidence; the sparse-cheater rejection probability is `3^{-K}`-shaped
(a single inflated coefficient survives only if all K rows miss it).
LaBRADOR's tuned entry distribution tightens the gap to `√(128/30) ≈
2.07` — tracked as the remaining refinement.

### 3.4 `opening::{prove_recursive, verify_recursive}` (LaBRADOR recursion)

```text
first message:  c = A₁·w, d = A₁·y, c_m = A₂·m, c_q = A₂·q
challenges:     C, γ ← H(key, c, d, c_m, c_q)
response:       z' = w + C·y, t* = Σγ^k m_k, q* = Σγ^k q_k,
                m, q revealed
verify:         A₁·z' == c + C·d;  A₂·m == c_m;  A₂·q == c_q;
                t* == Σγ^k m_k;  q* == Σγ^k q_k;
                Σγ^k R_k(z') == C·t* + C²·q*
```

Because the masked terms are pinned before the challenges open them, the
compact mode's single parity bit becomes **full relation soundness**:
substituting the gate expansion `R_k(z') = R_k(w) + C·m_k + C²·q_k` into
the final equation forces `Σγ^k R_k(w) = 0` — the pre-committed witness
satisfies the gates exactly in the ring. Cost: the revealed masked-term
vectors (`2·GATES` ring elements) dominate the proof size; amortizing
that revelation is precisely LaBRADOR's contribution and remains a size
milestone.

### 3.5 `sigma::z2` (blinded HVZK Σ-response over the Z2 ring)

The Z2-line counterpart of `sigma`: mask commitment `d = A·y` first, then
a **small non-unit challenge** (`nonunit_small_poly`: ternary
coefficients, even coefficient sum — small enough that responses stay
short, non-invertible so extraction survives), and a rejection-sampled
response `z = y + C·w` bounded by `B_Z`. HVZK via the rejection loop;
relaxed forking extraction as in Z1. This is the K2 blinding step for the
committed-opening line.

### 3.6 `instance::ring::{split_mod_2k, modswitch_ring}` and
`foundation::sampling::odd_sum_poly`

- `split_mod_2k`: the LaZer integer lift — `x = lo + 2^k·hi`
  coefficient-wise, turning `A·s ≡ t (mod 2^k)` into the exact ring
  equation `A·s + 2^k·v = t` with a hidden short carry vector;
- `modswitch_ring`: coefficient-truncation `Z_{2^32}[X]/(X^D+1) →
  Z_Q[X]/(X^D+1)` — a ring homomorphism, so `ms(A·w) == ms(A)·ms(w)`
  (commitments re-stated over smaller rings without re-opening);
- `odd_sum_poly`: uniform draws conditioned on an odd coefficient sum —
  the strong-sampling set (odd differences are units) for the 2-adic
  rings.

## 4. Reference entry points

- hyperball / fixed-weight / small non-unit / strong-sampling-set
  challenges: `crates/zk/src/foundation/sampling.rs`
- Z2 blinded Σ-response (HVZK): `crates/zk/src/sigma/z2.rs`
- integer lift / 2-adic ModSwitch:
  `crates/zk/src/instance/ring.rs::{split_mod_2k, modswitch_ring}`
- digit-based projection argument: `crates/zk/src/shortness/balanced.rs`
- JL projection argument (l2): `crates/zk/src/shortness/projection.rs`
- recursive full-relation mode:
  `crates/zk/src/opening/mod.rs::{prove_recursive, verify_recursive}`
- decomposition folding: `crates/zk/src/folding/latticefold.rs`
- contract tests: `crates/zk/tests/protocol_contract.rs`
- soundness & completeness review:
  `crates/zk/docs/review-soundness-completeness.md`

## 5. References (eprint numbers verified)

- LaBRADOR: [2022/1341](https://eprint.iacr.org/2022/1341) (CRYPTO 2023)
- Greyhound: [2024/1293](https://eprint.iacr.org/2024/1293) (Nguyen–Seiler, CRYPTO 2024)
- LatticeFold: [2024/257](https://eprint.iacr.org/2024/257); LatticeFold+: [2025/247](https://eprint.iacr.org/2025/247) (Boneh–Chen)
- LaZer Library: [2024/1846](https://eprint.iacr.org/2024/1846) (CCS 2024)
- SLAP: [2023/1469](https://eprint.iacr.org/2023/1469) (EUROCRYPT 2024)
- Rinocchio: [2021/322](https://eprint.iacr.org/2021/322) (CCS 2022)
- Ligetron: IEEE S&P 2024, DOI 10.1109/SP54263.2024.00086 (non-lattice, listed for contrast)
- MatRiCT: [2019/1287](https://eprint.iacr.org/2019/1287) (CCS 2019); MatRiCT+: [2021/545](https://eprint.iacr.org/2021/545) (S&P 2022)
- LNP22: [2022/284](https://eprint.iacr.org/2022/284); LNS21: [2020/1183](https://eprint.iacr.org/2020/1183); BLOOM: [2022/1307](https://eprint.iacr.org/2022/1307); LS18 invertibility lemma: [2017/523](https://eprint.iacr.org/2017/523); FS-with-aborts analyses: [2023/245](https://eprint.iacr.org/2023/245), [2023/246](https://eprint.iacr.org/2023/246)
- Folding ecosystem: Lova [2024/1964](https://eprint.iacr.org/2024/1964); Neo [2025/294](https://eprint.iacr.org/2025/294); SuperNeo [2026/242](https://eprint.iacr.org/2026/242); SALSAA [2025/2124](https://eprint.iacr.org/2025/2124); Symphony [2025/1905](https://eprint.iacr.org/2025/1905); Cyclo [2026/359](https://eprint.iacr.org/2026/359); LatticeBlindFold [2026/1857](https://eprint.iacr.org/2026/1857); LatticeFold+ ℓ₂-norm improvement [2026/721](https://eprint.iacr.org/2026/721)
- NIST FIPS 203/204 (reference semantics for CBD / SampleInBall / rejection sampling)
