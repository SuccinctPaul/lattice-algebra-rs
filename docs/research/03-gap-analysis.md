# Gap Assessment and Vertical Comparison: How Far from an "algebra Base Service"

> Companion documents: requirements and acceptance criteria in [01-requirements.md](01-requirements.md),
> horizontal peer data in [02-peer-research.md](02-peer-research.md). This document does only two things:
> **scoring (where the gaps are)** and **prioritising (what to do first)**. Every score points at
> checkable evidence (file paths / commands / compile errors).

---

## 1. Scoring Rubric

- **0–4 maturity**: 0 missing | 1 mentioned in docs only | 2 partially implemented | 3 implemented with a CI gate | 4 implemented + gate + an outward-facing service commitment.
- **Dimension level = the lowest score among the REQs in that dimension** (a base service is a weakest-link barrel: one broken consumer is enough to veto "dependable").
- The scores are not a capability ranking, they are a **dependability** ranking. High-scoring technical design items (trait decomposition, KAT coverage, claims register) do not mask the 0 scores on contract items.

| Dimension | Level | Decisive failing items | Existing high-scoring items (do not lose them) |
| --- | :-: | --- | --- |
| D1 Consumption contract | **1** | not published on crates.io (REQ-D1-01), no API gate, removing the facade directly breaks `LPN-zk` (REQ-D1-03/04) | conventional commits + git-cliff changelog; `integrating.mdx` is already written up |
| D2 Portability and dependencies | **0** | no `no_std` (REQ-D2-01); `Ring::rand` leaks `rand` types (REQ-D2-03); `[lib] name` inconsistent with the package name (REQ-D1-06) | the dependency surface was already tiny; `--locked` across all CI; features off by default |
| D3 Algebra coverage | **1** (0 before the fix) | ~~`Zq` axioms do not hold inside the value range the docs claim~~ → **fixed (2026-09-19)**; the lowest items are now three **undeclared boundaries**: ">64-bit moduli, cyclic rings, cross-stack interoperability" (REQ-D3-02/03/05) | const-generic parameterisation; capability trait decomposition; axiom modulus set 15→17 and now covering `q > 2⁶³`; three-path NTT cross-validation |
| D4 Performance dependability | **0** | the performance page has a single set of local numbers (M4 Pro), no multi-platform, no threshold gate (REQ-D4-01/02); docs drift from the actual state of `simd` (REQ-D4-05) | all numbers come from in-repo criterion benchmarks; `simd`/`parallel` are off by default and compiled in CI |
| D5 Trust assurance | **1** | no external audit, no fuzzing, no coverage (REQ-D5-01/02/03) | **511 official KAT/ACVP vectors byte-exact** (ML-DSA 279 + ML-KEM 183 + Falcon 10 + Frodo 18 + NTRU 9 + sntrup 12) + provenance + regeneration scripts; `crypto::ct`; claims register; zero `unsafe` |
| D6 Governance and operations | **1** | 2 authors, 1 tag, no release pipeline (REQ-D6-01/02) | docs site + per-crate `examples/` + `doc_snippet_check.rs` to prevent doc rot |
| **Overall (take the minimum)** | **0–1** | does not yet have the shape of a service others can depend on | — |

**One-line conclusion**: this is a library with a **mature kernel and a missing shell**. The shape of the
algebra layer (layering, capability traits, determinism, KAT) already matches the design standard of
arkworks/plonky3; almost everything that is missing is the "service shell" — publishing, contracts,
portability, gates, multi-platform measurement, governance.
The good news: shell-type work carries low technical risk, can be parallelised, and is mostly a one-off
investment that CI then guards for the long term.

---

## 2. Vertical Comparison A: How Servable Each In-Stack Layer (L0–L6) Is

The first meaning of "vertical": **asking down your own stack — can every layer be consumed independently, published independently, audited independently?**

| Layer | Where it lives today | Independently consumable? | Change radius | Barrier to servicing |
| --- | --- | :-: | --- | --- |
| L0 scalar ring `Zq<q>`, `Ring`/`Field`/`TwoAdicRing`/`CenteredRing` | `algebra::ring` | 🟡 | the whole stack (shared by PQC + ZK) | value-range boundary defect (§D3-01); traits are not dyn compatible |
| L1 NTT engine (const-generic twiddles, CT/DIT + GS/DIF) | `algebra::ntt` | 🟡 | all 2-adic schemes | same crate as L0, so taking NTT means also taking sampling/XOF |
| L2 polynomials `PolyRing`/`UniPolynomial`/`SparsePolynomial` | `algebra::poly`, `ring::poly_ring` | 🟡 | ring schemes | only `X^n+1`; the cyclic ring `X^n−1` is missing |
| L3 module lattices `ModuleVector`/`ModuleMatrix`(+NTT), ExpandA, rounding/hints | `algebra::module` | 🟡 | ML-KEM/ML-DSA/Z1 | two container families coexist — `matrix::GenericMatrix` (legacy) and `module::ModuleVector` → consumers have to guess which one to use |
| L4 crypto infra XOF/sampling/transcript/bit packing/`ct` | `algebra::crypto` | ❌ | all schemes and all ZK proofs | **same crate as L0–L3, yet it carries `rand`/`sha3`/`rustfft`/`serde`**: a consumer that only wants a pure ring operation ends up with all of those dependencies |
| L5 protocol components Ajtai/Σ/IPA/sumcheck/folding | `lattice-zk` | 🟡 | the ZK line | explicitly marked experimental; no stability tiering (REQ-D1-05) |
| L6 schemes ML-KEM/ML-DSA/Falcon/Frodo/NTRU/sntrup | `lattice-pqc` | ✅ | a single scheme | Falcon is constrained by the policy of not shipping stable before the FIPS 206 freeze (reasonable) |

**The structural problem (the most important row in this table)**: L0–L4 are all packaged into **one crate** (`lattice-algebra`, roughly 10.9k LOC).
The consequence is that three "service-level" capabilities are impossible:

1. **Consume on demand**: a consumer that only wants L0/L1 ring operations also drags in L4's `rand`/`sha3`/`rustfft` dependencies;
2. **Independent publishing / independent semver**: one L4 sampler change and one L0 trait change share a single version number, so consumers cannot judge the blast radius;
3. **Independent auditing**: the audit scope cannot be narrowed (for a base service, "audit only L0+L1" is a significant cost difference).

Benchmarking (details in 02): **arkworks splits the same kind of content into six separately published
crates — `ark-ff` / `ark-poly` / `ark-ec` / `ark-serialize` / `ark-std` / `ark-relations`**;
**plonky3 splits `field`/`mac`/`mds`/`poseidon`/`merkle`/`fri`/`util` into independent crates that can each
be versioned**, and both are `no_std`. In other words: **"layering" already holds on paper (the L0–L6 diagram),
but not yet at crate granularity.**

### 2.1 Distribution of Consumer Entry Points (the Real Vertical Usage Surface)

| Consumer | Layers used | Evidence |
| --- | --- | --- |
| `lattice-pqc` | L0+L1+L2+L3+L4 (the full stack) | `crates/pqc/Cargo.toml` depends only on `lattice-algebra` + `sha3`/`zeroize`/`sha2` |
| `lattice-zk` | L0+L1+L2+L3+L4 | `crates/zk/Cargo.toml` depends only on `lattice-algebra` + `rand` |
| External: `LPN-zk` (already broken) | only L0 plus the matrix/vector of L3 | `use lattice_algebra_rs::matrix::…`, `ring::zq::Zq` |
| Potential: `condor-rs`/`fips203`/`fips204`/`ml_kem.rs`/`baby-kyber-rs` etc. | L0–L4 (currently each hand-rolling its own) | see the internal duplication table in §4 |

Conclusion: **the only existing external consumer uses just the two bottom layers**. That is consistent with
the judgement about "packaging L0–L4 together" — after splitting the layers into crates, the leanest tier
(only L0+L1) is the entry point with the lowest integration cost.

---

## 3. Vertical Comparison B: Timeline (Where We Sit on the Curve)

The project spans **2024-12-31 → 2026-09-18** (roughly 21 months, 60 commits, 2 authors, 1 tag).
Aligned to the stage model for "becoming a base service":

| Stage | Goal | Acceptance criterion | Status |
| --- | --- | --- | :-: |
| **S0 Correctness kernel** | one ring stack feeding both PQC and ZK | both lines share the same L0–L4; KAT byte-exact | ✅ **done, and a strength** |
| **S1 Publishable** | others can integrate with one line in `Cargo.toml` and are not broken by upgrades | crates.io + semver policy + API gate + deprecation window | ❌ **currently stuck here** |
| **S2 Portable** | the target matrix covers the platforms consumers actually ship to | `no_std` + wasm + multi-arch CI | ❌ |
| **S3 Measurable** | performance promises are checkable and regression-testable | multi-platform benchmarks + threshold gate + same frame as production references | ❌ |
| **S4 Auditable** | third-party endorsement + continuous assurance | audit + fuzz + coverage + CT tooling | 🟡 (good assurance baseline, endorsement missing) |
| **S5 Ecosystem** | become the default choice with spillover adoption | ≥2 consumers outside this repo + multiple maintainers + a change-review mechanism | ❌ |

> The point of the stage model is the **order**: S1/S2 are prerequisites for S3–S5 (without a version policy
> and a target matrix, there is no benchmark and no adoption that can be promised).
> It also shows that "do performance first" is the wrong ordering — what costs the most today is not missing
> AVX-512, but the missing release pipeline that does not break downstream consumers.

For the peer timeline comparison (release cadence, audit rounds, adoption curve) see
[02-peer-research.md](02-peer-research.md) §4.

---

## 4. Internal Duplication: The "Hand-Rolling" the Base Service Must Replace

Similar implementations under `/Users/paul/zkp/lattice_based/` (both LOC and file paths were verified one by
one during this research with `find | wc -l` / `grep`; reproduction commands in Appendix A):

| Parallel stack | Ownership | Where its algebra layer comes from | Hand-rolled volume | Relation to this repo |
| --- | --- | --- | --- | --- |
| `lettuce/` (fork, overridden by a local `[patch.crates-io]`) | external author + local maintenance | ships a complete L0–L4 | **8,129 LOC** (`ntt.rs`, `structures/*`, `montgomery.rs`, `probability/*`) | our `digital_objects` is being built on top of it; the capabilities its TODOs name explicitly (twiddle iterator / rayon parallelism / roots lookup table / rejection sampling) we already have |
| `hachi-pcs/` | collaborator's repo | `ark-ff 0.5` + **`tfhe-ntt 0.6.1`** + hand-rolled | 4,681 LOC (`src/arithmetic/*`) | when picking a lattice PCS it bypassed this repo and chose Zama's NTT |
| `feanor-math` | upstream | the whole library is algebra (`ring.rs`/`field.rs`/`rings/*`/`algorithms/convolution/ntt.rs`/`reduce_lift/*`) | 46.8k LOC | the direct benchmark for our trait hierarchy |
| `tfhe-rs` (Zama) | upstream | `tfhe-ntt` + `tfhe-fft` (native32/64/128, prime32/64, SIMD kernels) | 24.4k LOC | the de facto external "lattice NTT vendor" |
| `Lazarus` | upstream | its own crate **`name = "algebra"`** | 865 LOC (`zq.rs`/`polynomial_ring.rs`/`rq_matrix.rs`) | the closest precedent; and it **collides with our package name** (REQ-D1-06) |
| `condor-rs` (Nethermind) | upstream | ships `labrador/src/ring/*` | 2,051 LOC; `Zq` hardcodes `q=2^32` | counter-evidence for the differentiating point of const-generic `Zq<q>` |
| `latticefold` (Nethermind) | upstream | separate crate **`cyclotomic-rings`** built on `ark-ff 0.4` | 6,641 LOC | another ring stack for what corresponds to our `zk::folding::latticefold` |
| Kyber family: `fips203` / `fips204` / `kyber` / `baby-kyber-rs` / `ml_kem.rs` / `KEMs::ml-kem` | 5 upstream + 1 local | each with its own ring/NTT/CBD/reject/XOF | total ≈ **20k LOC** of same-origin duplication (`KEMs/ml-kem/src/algebra.rs` 22 KB; 7 `// TODO: Add checks` in `ml_kem.rs`) | same layer as `pqc::mlkem`/`mldsa`; source of KAT cross-validation |
| Labrador family: `Lazarus/algebra` + `condor-rs` + `ashlang/ring-math` + `Cupcake` + `hachi-pcs` | upstream | five nearly isomorphic `{Zq, Poly, Rq, RqMatrix, RqVector}` | 1.4k–2.6k LOC each | the same L0–L3 implemented independently five times |
| Sampling/Gaussian: `lattigo/ring/sampler_*` (Go 7.8k) / `qfall-crypto` trapdoor / `lpn/gauss.rs` / `rust-fn-dsa` DD sampler / `lettuce/probability` | upstream | each its own | — | the L4 capability is re-implemented 6 times |

**Judgement (the single most important finding of this research)**: inside the organisation, the direct
competitor of the base service is not arkworks, but **yet another copy of a 300-line NTT** and
**the already-available `tfhe-ntt` / `lettuce`**.
So the meaning of that `Zq::inverse` boundary defect in §2.2 is not "a bug" — it is the only way the
foundation proves its value: **fix it once, and every copier benefits**; conversely, as long as the contract
(D1/D2) still scores 0, copiers will keep copying.

---

## 5. Gap List (Ordered by Actionability)

Effort: S ≤ 1 day | M 1–4 days | L > 4 days (one person, including tests and CI).

### P0 — Stop the bleeding: "existing consumers stop breaking, new consumers can plug in"

| # | Gap | Action | Effort | Closure criterion |
| --- | --- | --- | :-: | --- |
| G1 ✅ fixed | ~~`Zq` is incorrect inside the domain the docs claim (`q ≤ 2⁶⁴`)~~: `mod_add` loses the carry once `q > 2⁶³`, `inverse()` uses `i64` intermediates and returns a non-inverse, `centered()` has the same kind of cast | replaced with carry-folding `mod_add`, EGCD doing Bézout over `u128` modulo, centered over `u128`/`i128`; axiom modulus set 15→17 (including Goldilocks with `q > 2⁶³`), plus targeted differential tests and mechanism tests asserting the "old expression necessarily disagrees" | S–M | **met**: `make gate` exit 0, 726 tests pass; documented value range = tested range (see the correction record in 01 §2.2) |
| G2 | unpublished, no version policy | `cargo publish` for the three crates + `release.yml` (tag→release→crates.io→docs) + a Stability section added to `CONTRIBUTING.md` | M | a clean project can `cargo add lattice-algebra` |
| G3 | no gate on the public API | `cargo public-api` snapshot in-repo + CI diff turns red immediately | S | deleting/changing a public item necessarily shows red |
| G4 🟡 partially done | removing the facade broke `LPN-zk` | **consumer side is done**: `../LPN-zk` migrated to the current API on 2026-09-19 (`cargo check` + `cargo test` fully green; the migration mapping table and the 6 friction points it surfaced are in 01 §2.1b). **Still missing**: a "consumer regression" CI on this repo's side (bringing consumers into the workspace or compiling them from a CI checkout) and a written migration table | M | ~~`LPN-zk` `cargo check` passes~~ ✅; what is left is "consumers in CI" |
| G5 | `[lib] name` is generic and inconsistent with the package name | align the lib name with the package name (`algebra`→`lattice_algebra` etc.), add `pub use` aliases during the transition | S | `use lattice_algebra::ring::Ring;` compiles |
| G6 | `Ring::rand` leaks `rand` types | our own sealed RNG trait or a purely seeded API (consistent with the existing "XOF first" principle) | M | number of third-party types in public signatures = 0 (script-checkable) |
| G7 | doc drift (the performance page says "no SIMD", while `simd`/`simd-mlkem`/`simd-frodo` already exist) | sync the performance page and the feature table + add `make docs-check` | S | claims match the `Cargo.toml` features |

### P1 — Portability and measurability: turn "trial usage" into "the default"

| # | Gap | Action | Effort |
| --- | --- | --- | --- |
| G8 | no `no_std` | `#![no_std]` + `alloc`, with `std` behind a feature (currently only 8 files and 20 occurrences of `use std::`); add `wasm32-unknown-unknown` and `thumbv7em-none-eab` legs to CI | M–L |
| G9 | L0–L4 in a single crate | split crates by layer (at minimum `*-ring`/`*-ntt`/`*-module`/`*-crypto` individually consumable), keep an umbrella crate for compatibility | L |
| G10 | no performance promise | multi-platform benchmarks (linux-x86_64 + macOS aarch64, plus wasm/emscripten if supported), baseline comparison and threshold gate, a table sharing the frame with `liboqs`/RustCrypto | L |
| G11 | two matrix containers (`matrix::GenericMatrix` vs `module::ModuleVector/Matrix`) | mark legacy explicitly + a migration path, or fold them together | M |
| G12 | cyclic ring `X^n−1`, non-power-of-two `n` (needed on the SNARK side) | add the L2 ring family + cross-validation tests | M–L |
| G13 | no fuzzing / no coverage | `cargo fuzz` over all decoding entry points; put `cargo llvm-cov` behind the gate (threshold per core layer). **Baseline measured (2026-09-19, `--workspace --all-features`): lines 92.41% / regions 93.44% / functions 90.42%, 1132 lines uncovered**; details in the repo README's "Coverage baseline" section | M |
| G23 | **zero executed coverage on the rayon paths of the `parallel` backend** (new measured finding) | the `#[cfg(feature="parallel")]` operator blocks in `matrix.rs`/`vector.rs`, `sumcheck::prove_rayon`(205–264) and `commitment::key::mul_vec`(58–68) are all unexecuted lines under `--all-features` coverage. Note that CI **already has** an `--all-features` test leg and still never reached these branches — meaning either the test sizes never cross the parallel thresholds (`PARALLEL_THRESHOLD²=1024`, `PAR_MIN_TERMS`), or there are no callers at all. Approach: add a "sequential == parallel" equivalence test for each of the three (at sizes that straddle the threshold), and have CI run one coverage leg with `--features parallel` | M |

### P2 — Competitiveness: from "usable" to "the preferred choice"

| # | Gap | Action |
| --- | --- | --- |
| G14 | no external audit | submit the L0/L1 + ML-DSA/ML-KEM paths for audit; write the results back into the claims register |
| G15 | CT relies on manual judgement | put dudect/`ct-analyze`/assembly audits into a recurring CI job |
| G16 | backends are not replaceable | define a unified dispatch contract (safe SIMD ↔ asm ↔ multithreaded) while keeping zero `unsafe` by default (0 `unsafe` in the current workspace is a selling point; an asm backend must be explicitly isolated). **Define the contract in the shape of `mldsa-native`'s "fixed frontend + unified backend interface", to avoid liboqs's per-parameter-set × per-ISA directory explosion** |
| G17 | no handle for cross-language consumers | export KAT/test vectors as JSON/JSONL (the provenance directory already exists) so the Go/C/Solidity side can align; the LaBRADOR C reference implementation (`lattice-dogs/labrador`) has **no KAT harness**, which makes it a target for our differential testing |
| G18 | single-maintainer governance | a second owner, an RFC process (interface changes go through a checklist), a consumer-committee-style requirements register (REQ-D6-04) |
| G19 | no cross-version compatibility gate | follow `tfhe-rs`: `backward_compatibility` tests + a dedicated CI job that uses already-frozen old byte artifacts to verify the pk/sk/ct/sig encodings (REQ-D1-07) |
| G20 | no "module × platform" promise matrix | follow liboqs' `ALGORITHMS.md`/`PLATFORMS.md`: add `STABILITY.md`, listing stability / CT status / platform support level per module (REQ-D6-07). It only needs to be stitched onto the existing claims register; effort S |
| G21 | moduli can only be parameterised, not specialised | follow `tfhe-ntt`'s kernel matrix (`prime32/{generic,shoup}`, `prime64/{generic_solinas,less_than_Nbit}`): promote the modulus shape to a type-level selection, and write a "adding a new modulus does not touch the core" recipe (REQ-D3-07). **This is the differentiating point that goes head-to-head with larkworks's per-modulus instance files** |
| G22 | the assurance tiers do not separate "tested" from "proven" | state which class of tool (`kani`/`crate-verify`/CBMC-over-FFI) is intended for the hottest paths (NTT kernel / `ct` selectors), and split columns accordingly in the claims register (REQ-D5-07; benchmarked against `mldsa-native`'s HOL-Light + Isabelle baseline) |

**Peer-best five-condition comparison (the core judgement of this research, source: 02 §3.1)**: as of 2026-09-19,
no one simultaneously satisfies all five of "① published ② modulus/degree generic ③ `no_std`
④ capability traits ⑤ serving both PQC and ZK".
Current state of this project: **④⑤ hold; for ② the "shape" holds (const-generic `Zq<Q>` + `PolyRing<R,N>`)
but there is a boundary defect inside the claimed domain (see G1; only after the fix does it truly count as met);
①③ are entirely unmet.**
→ **The distance is two layers of engineering shell, not mathematics.** Cautionary counter-example:
`module-lattice` satisfies ①③④ but pins the ring degree to `U256` and has zero ZK surface, was created on
2026-01-27, reached 0.2.3 by 05-10, and has **5,492,955 downloads in 4 months** — the window is real,
but it only rewards whoever publishes first.

---

## 6. Non-Goals: What We Explicitly Will Not Do (avoiding base-service scope creep)

- **No general EC/SNARK finite-field algebra** (256-bit prime fields, curve arithmetic): inside the organisation
  this is already covered by `ark-algebra`/`Plonky3`/`gnark`; the boundary of this service is lattice algebra.
  If interoperability is ever needed, build an **adaptation layer**, not a re-implementation (REQ-D3-05).
- **No chasing extreme SIMD**: the absolute performance gap versus `liboqs`/`RustCrypto` is not the main adoption
  barrier (not one row of the failing items in §1 is "slow"); keep zero `unsafe` and default compilability,
  and put heavy kernels behind optional backend features.
- **No stable release of Falcon before the FIPS 206 freeze** (carrying over the existing decision).
- **No hash-based / code-based schemes** (carrying over the existing non-goals).
- **No competing with arkworks on number of abstractions, nor with liboqs on number of schemes**: neither
  strength is a success criterion for this service (02 §7).

### 6.1 Counter-Arguments (the three questions this project must be able to answer)

1. **The "shared algebra foundation" proposition has not been validated by any production deployment.** The
   strongest counter-example comes from Zama: it owns the strongest Rust lattice ring/NTT layer in this survey
   (`tfhe-ntt` 0.7.1), yet when building its ZK prover (`tfhe-zk-pok`) it uses the discrete-log vector commitments
   of `ark-bls12-381`/`ark-ec` and **does not reuse its own ring layer**.
   → Our only possible answer is the existing fact that "one and the same foundation runs both the PQC and the ZK
   schemes and protocols, with KAT alignment" (both the `pqc` and `zk` crates depend only on `algebra`), not a vision.
2. **ICICLE has already written "unified `Rq`/`Tq` traits + negacyclic NTT + balanced decomposition + JL + norm
   bounds" into a documented API.** → The differentiation is not "having thought of these abstractions", but
   "already published + generic moduli + `no_std` + same source as PQC" (02 §3).
3. **The assurance baseline has already been raised to machine-proven level by `mldsa-native`
   (CBMC + HOL-Light + Isabelle) and `libcrux-*` (HACL\*→Rust).** → Among the Rust camp our CT claims are
   near the front, but as a "PQC implementation" we are benchmarked against them; that is why G14/G15/G22 exist,
   and also the part that cannot be waved away with a single sentence about "zero `unsafe`".

---

## Appendix A: How to Reproduce Every Claim in This Document

```sh
# scale / governance signals
git log --reverse --format='%ci' | head -1; git log -1 --format='%ci'
git tag | wc -l; git shortlog -sn --all | head; git log --oneline | grep -cE '\(.*\)!'   # number of breaking commits

# current contract state
grep -n "name = " crates/*/Cargo.toml          # package name vs [lib] name
grep -n "fn rand" crates/algebra/src/ring/traits.rs   # rand types leaking into the public trait signature
grep -rn "use std::" crates/algebra/src | wc -l       # surface to change for no_std

# L0 boundary defect: before the fix this was reproduced with throwaway probes, now it is hardened into in-repo regression tests
#   cargo test -p lattice-algebra --lib ring::zq::tests
#     inverse_above_2_63_is_a_real_inverse      (q = u64::MAX-58: the old implementation gave Some(21), 12345*21 ≢ 1)
#     inverse_just_below_2_63_is_unchanged      (q = 9223372036854775783: the largest prime below 2^63)
#     centered_is_exact_above_2_63 / division_recovers_the_multiplier_at_the_top_of_the_domain
#   cargo test -p lattice-algebra --lib ring::reduction::barrett
#     reductions_at_moduli_just_above_2_63 / reductions_at_the_top_and_bottom_of_the_domain
#     carry_out_of_u64_is_what_the_fix_handles  (asserts the old expression necessarily disagrees with the reference value)
#   cargo test -p lattice-algebra --lib ring::axiom_tests::zq_goldilocks   (all axioms for q > 2^63)
# Correction record: an earlier draft claimed "at q ≈ 2^63 inverse returns None for invertible elements", but that modulus is in fact composite (digit sum 90),
#   so returning None is correct behaviour — the real boundary is q > 2^63. See 01 §2.2.
# dyn compatibility: let _: Box<dyn algebra::ring::Ring> = ...;  -> E0038

# consumer breakage
cd ../LPN-zk && cargo check   # virtual manifest error

# internal parallel stacks (data source for §4)
grep -H "^name" ../Lazarus/*/Cargo.toml                    # name = "algebra" conflict
grep -rn "TODO" ../lettuce/lettuce/src/ntt.rs              # twiddle iterator / rayon parallelism / roots lookup table
sed -n '1,20p' ../hachi-pcs/Cargo.toml                     # ark-ff 0.5 + tfhe-ntt 0.6.1
head -12 ../condor-rs/labrador/src/ring/zq.rs              # q = 2^32 hardcoded
find ../lettuce/lettuce/src -name '*.rs' | xargs wc -l | tail -1   # 8129

# missing service shell
grep -rn "fuzz\|llvm-cov\|public-api\|publish" .github/workflows/ci.yml Makefile   # no matches
```
