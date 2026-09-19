# Requirements research: making `lattice-algebra` the algebra base service for the organization

> What this document does: it answers three questions — **what a "base service" actually means**, **who is
> filing the requirements (the real consumer profile)**, and **the requirement list with its acceptance criteria**.
> The gap assessment is in [03-gap-analysis.md](03-gap-analysis.md), peer data in [02-peer-research.md](02-peer-research.md).
>
> Conclusion first: **the L0–L4 algebra core already has the technical shape of something reusable, but not yet
> the service shape of something dependable.** The hardest evidence is a real consumer that is already broken
> inside the repository (`LPN-zk`, see §2.1), plus a reproducible L0 boundary-correctness defect (see §2.2).

---

## 1. Defining the "algebra base service"

Not "a nicely written library", but **the foundation others have to use — and dare to use**. Broken down by
service commitment, six classes of conditions must hold at the same time:

| # | Dimension | Service commitment (one sentence) | The negative (what happens without it) |
| --- | --- | --- | --- |
| D1 | **consumption contract** | a version number, stability tiers, a breaking-change window, an API-diff gate | one upstream refactor breaks every downstream consumer (already happened) |
| D2 | **portability and dependencies** | compiles for `no_std`/wasm/multiple architectures; the public API leaks no third-party types; dependencies can be version-pinned | consumers are forced to sync on RNG/hash major versions |
| D3 | **algebra coverage** | the rings/fields/structures consumers need are already in the core, so nobody has to hand-write them | every project hand-rolls its own NTT and sampling, and the base gets bypassed |
| D4 | **dependable performance** | multi-platform benchmarks in CI, regression thresholds, a replaceable backend | "3× slower than the reference implementation" goes unnoticed by everyone |
| D5 | **assurance** | constant-time as tooling, fuzzing, coverage, external audits, a claims register | a "research code" label that keeps it out of production paths |
| D6 | **governance and operations** | multiple maintainers, a release pipeline, a support channel, docs and migration guides | single-maintainer bus factor, fluctuating with one person's schedule |

**Scope boundary (must be fixed first, otherwise no gap can be judged)**: this service targets **lattice-side
algebra** (`Z_q`, `Z_q[X]/(X^n±1)`, module lattices, NTT, sampling, XOF/transcript), not general-purpose
finite-field / elliptic-curve algebra. Inside the organization, `ark-algebra`, `Plonky3`, `gnark`/`cosnark` and
`mpz` already cover the EC/SNARK side, and for the base service to take them on what it needs is **the same trait
contract**, not the same implementation (see §3 REQ-D3-05).

---

## 2. Consumer profiles and requirement evidence

### 2.1 The one existing external consumer: `LPN-zk` (was broken; migrated 2026-09-19, see §2.1b)

`/Users/paul/zkp/lattice_based/LPN-zk` (last commit 2025-01-13) consumes this repository as a path dependency:

```toml
# LPN-zk/Cargo.toml
lattice-algebra-rs = { path = "../lattice-algebra-rs" }
rand = "0.8.5"
```

```rust
// string-commitment-scheme/src/lib.rs
use lattice_algebra_rs::matrix::ring_matrix::RingMatrix;
use lattice_algebra_rs::matrix::vector_arithmatic::VectorArithmatic;
use lattice_algebra_rs::matrix::{Matrix, MatrixScalarType};
use lattice_algebra_rs::ring::zq::Zq;
```

What `cargo check` reports today:

```
error: failed to get `lattice-algebra-rs` as a dependency of package `LPN-commitment-scheme`
  Unable to update /Users/paul/zkp/lattice_based/lattice-algebra-rs
  found a virtual manifest at `.../Cargo.toml` instead of a package manifest
```

**This one case exposes four independent contract-level problems at the same time:**

| Evidence | Requirement it exposes |
| --- | --- |
| the facade crate `lattice-algebra-rs` was deleted in the W1 split, and `integrating.mdx` kept nothing but a line saying "has been removed" | **REQ-D1-03 breaking changes need a window + a migration table**: the facade should have stayed as a `#[deprecated]` forwarding shim for at least one minor version |
| the repository is still marked `version = "0.1.0"`, while history contains several breaking `refactor(...)!` commits | **REQ-D1-01/D1-02 versioning and stability**: even during 0.x, a breaking commit must come with a minor bump and a CHANGELOG section |
| the `VectorArithmatic` / `MatrixScalarType` the consumer referenced no longer exist in the current API (`matrix` only has `GenericMatrix`/`GenericVector` plus the `RingMatrix` alias left), and `RingMatrix` going from struct to type alias is an implicit break as well | **REQ-D1-04 public-API gate**: `cargo public-api` diff in CI, any deletion is red |
| the consumer pins `rand = "0.8.5"`, while `algebra::ring::Ring`'s trait method signature is `fn rand(rng: &mut impl rand::RngCore)` (workspace `rand = "0.9.1"`) | **REQ-D2-03 the public API must not leak third-party types**: `Ring::rand` locks the `rand` version into the trait contract, so consumers on another `rand` major version cannot pass in their own RNG |

> This is not a hypothetical risk: a dependency type showing up in a trait method signature is the same as demanding
> that every consumer sync `rand` major versions with this repository.

#### 2.1b That consumer completed the migration on 2026-09-19 — and the migration itself exposed 6 integration friction points

`../LPN-zk` (its uncommitted Jan-2025 WIP was backed up as a patch first, nothing was destroyed) is now green under
both `cargo check` and `cargo test`. Old → new mapping:

| Old API (2025-01) | Current API | Notes |
| --- | --- | --- |
| `lattice_algebra_rs::…` | `algebra::…` | the mismatch between package name `lattice-algebra` and lib name `algebra` (REQ-D1-06) bites directly here |
| `matrix::ring_matrix::RingMatrix` | `matrix::matrix::RingMatrix` | same-name module nesting (the `#![allow(clippy::module_inception)]` at the top of `lib.rs` is the proof); ugly path, but it works |
| `matrix::{Matrix, MatrixScalarType}` + `a.concat(&b, HORIZONTAL)` | `a.concat_horizontal(&b)` / `concat_vertical` | the enum parameter became named methods — **an improvement** |
| `RingMatrix::rand(rng, r, c)` | `RingMatrix::random(rng, r, c)` | clashed with `Ring::rand`, so the rename is reasonable |
| `RingMatrix::from_col_vector(v)` | **nothing equivalent** → the consumer wrote its own `col_vector()` (`new` + `set`) | capability gap ①: no public entry point for "construct from data" |
| `VectorArithmatic::hamming_wight(&v)` | **nothing equivalent** → the consumer wrote its own `hamming_weight()` | capability gap ②: Hamming weight (norm/weight checks are just as common on the lattice ZK side) |
| `#[derive(Ord, PartialOrd)] struct … { A: RingMatrix<B> }` | **fails to compile** | capability gap ③: `GenericMatrix` no longer derives `Ord`/`PartialOrd`, a silent capability narrowing that the consumer can only fix by deleting the derive |

The remaining two:
- **the `rand` version lock-in** (the empirical case for REQ-D2-03): the migration forced `LPN-zk` from `rand 0.8.5`
  up to `0.9.1` (`rand::thread_rng()` → `rand::rng()`), solely because `rand::RngCore` appears in the `Ring::rand`
  signature;
- **`Display` preserved** (`matrix.rs:592`): the `to_string()` debug output was not lost — that part was done right.

**Migration conclusion**: one real integration = 3 public capability gaps + 1 dependency leak + 1 naming/path problem.
These are all actionable requirements at the base-service level, not disagreements about taste — on that basis we suggest
adding `REQ-D3-08 matrices/vectors constructible from data (from_row_major / from_col_vector)`,
`REQ-D3-09 a vector weight and norm toolbox (hamming_weight and friends)`,
and `REQ-D1-08 removing capabilities such as ordering from container types must be recorded explicitly`.

### 2.2 L0 boundary correctness: `Zq` did not hold inside its own documented domain ✅ fixed (2026-09-19)

`crates/algebra/src/ring/zq.rs:10` declares `Z_q: q <= 2^64`. Measured during this research (a throwaway probe, since
hardened into an in-repo regression test), the confirmed failing boundary is **`q > 2^63`**:

| Path | Test case | Measured result before the fix |
| --- | --- | --- |
| `reduction/barrett.rs:16` `mod_add` (`wrapping_add` + a single conditional subtraction) | `q = u64::MAX-58` (prime), `a = b = q-1` | gets `18446744073709551496`, should be `18446744073709551555` — **one 2⁶⁴ carry correction missing**. Root cause: when `a+b ≥ 2⁶⁴` the carry is discarded; that branch is reachable only when `q > 2⁶³` |
| `zq.rs` `inverse()` (extended Euclid seeded with `MODULUS as i64`) | `q = u64::MAX-58`, `a = 12345` | `Some(21)`, while `12345·21 mod q = 259245 ≠ 1` — **silently returns a non-inverse**. With `q > 2⁶³`, `MODULUS as i64` is negative |
| `CenteredRing::centered()` (`value as i64` / `MODULUS as i64`) | `q = 2⁶⁴−2³²+1` (Goldilocks) | the same class of `i64` cast problem; `2v` can also overflow within `i64` |
| existing coverage | ring-axiom property tests | 15 moduli, range **2 … 2³²** → the intervals above sit entirely outside test coverage |

> **A correction to the first draft of this report**: the draft additionally listed "`inverse(3)` returns `None` at
> `q = 9223372036754775783`, breaking the `Field` axiom" — **that claim does not hold**: the digits of
> `9223372036754775783` sum to 90, so it is divisible by 3 and is **composite**, and `None` is the correct behavior
> there. The largest prime below `2^63` is `9223372036854775783`, and the old implementation was measured there to
> **give the correct result**. The defect boundary is therefore precisely "**fails for `q > 2⁶³`**", not "fails
> already close to `2⁶³`".

**What was fixed (already in the repository)**
- `mod_add` now uses `overflowing_add` and folds the carry back in as `2⁶⁴ mod q` (i.e. `q.wrapping_neg()`), then subtracts conditionally;
- `inverse()` is now a `u128` extended Euclid with the Bézout coefficients reduced at every step → no intermediate value overflows anywhere in the `q ≤ u64::MAX` domain;
- `centered()` now computes in `u128`/`i128` (keeping it branch-free); the narrowing is exact because `|result| ≤ q/2 ≤ i64::MAX`;
- tested domain aligned: the ring-axiom suite's moduli go from 15 to **17**, adding `2⁶¹−1` (a Mersenne prime) and
  `2⁶⁴−2³²+1` (Goldilocks, **above `2⁶³`**, so additions produce a carry); boundary primes whose `q−1` trial division
  cannot factor quickly (such as `u64::MAX−58`) are covered instead by targeted differential tests in
  `zq`/`reduction::barrett` (including the composite upper bound `u64::MAX`), because `primitive_root` uses trial
  division and putting those in the axiom suite would hang CI;
- plus a "mechanism test", `carry_out_of_u64_is_what_the_fix_handles`: it asserts that the old expression **disagrees
  with the reference value** on the same inputs, so these fixtures cannot decay into tests that always pass.

`make gate` result: **exit 0, 726 tests passing** (including the three new boundary suites and the 8 new targeted tests).

**Left over (same class of requirement, not done yet)**: >64-bit moduli under `REQ-D3-02` remain a non-goal (they need an explicit declaration),
and "documented domain = tested domain" is currently kept aligned by hand — `STABILITY.md` (REQ-D6-07) should lock it in.


### 2.3 The real competition on the demand side: not arkworks, but "a second algebra stack is already in use"

During this research each item below was verified inside `/Users/paul/zkp/lattice_based/` (commands in 03 appendix A),
and the conclusion is worse than "nobody uses it yet": **lattice work inside the organization is already running a
second and a third algebra stack, and they are the ones we do not maintain.**

| Evidence | Fact | What it means for the base service |
| --- | --- | --- |
| `lettuce/` (a fork of `codeberg.org/ccertain/lettuce`, with a local `mine` remote + `[patch.crates-io] path` override; latest commit 2026-01-23) | contains a **complete 8,129 LOC parallel L0–L4 stack**: `ntt.rs`, `structures/{fields,polynomial,matrix,vector}.rs`, `montgomery.rs`, `probability/{gaussian,ternary}.rs`. Its own TODOs name exactly the capabilities we already have: `ntt.rs:9` "unity root iterators, run in parallel with rayon / cache a root lookup table", `commitments/bdlop/linear_nizk.rs:74` "TODO: rejection sampling" | the demand is **real and already satisfied by someone else**. Our own upper-layer project (`lettuce/digital_objects`, a local package) is built on that external stack — the competition is between "replace it" and "everyone keeps writing their own" |
| `hachi-pcs/` (collaborator georgeorourke, latest commit 2026-01-30) | lattice PCS: `ark-ff 0.5` + **`tfhe-ntt 0.6.1`** + 4,681 LOC of hand-rolled `src/arithmetic/{ring,poly,poly_vec_ntt,poly_mat_ntt,poly_chal,field}` | a lattice project within the same organizational radius, when it hits lattice NTT, **defaults to Zama's `tfhe-ntt` + arkworks** rather than this repository |
| `Lazarus/algebra/Cargo.toml` | `name = "algebra"` — **a direct package-name clash** with this repository's `[lib] name = "algebra"`; and `algebra/src/polynomial_ring.rs:26` carries a "todo: use NTT to speed up" | this repository currently cannot appear in a dependency graph together with Lazarus (REQ-D1-06 escalates from "naming preference" to "hard conflict") |
| `condor-rs/labrador/src/ring/zq.rs` | `Zq` hardcodes `q = 2^32` with `u32` wrapping storage (no const-generic modulus) | our const-generic `Zq<q>` is a genuine differentiator and should be claimed explicitly in the comparison table |
| `KEMs/ml-kem/src/algebra.rs` (RustCrypto, 22 KB) | the upstream production-grade ML-KEM ships its own `FieldElement(u16)`/`Polynomial`/`NttPolynomial`/`sample_cbd`/`sample_uniform`/`Xof` | exactly the same layer as `pqc::mlkem`: this is the benchmark for credibility, and also the easiest source of the "we have that too" illusion |
| `fips203`/`fips204`/`kyber`/`baby-kyber-rs`/`ml_kem.rs` | five Kyber-family copies of ring/NTT/CBD/reject/XOF, roughly 20k LOC of same-origin duplication in total (`ml_kem.rs` has 7 `// TODO: Add checks`) | the duplication cost is itself the business case, but it also shows that **these teams do not think they need an internal base** unless integrating is cheaper than copying |

**Demand-side conclusion**: the case for a base service can never be "nobody has an algebra library", it is
"**one and the same lattice algebra is currently carried by 6+ independent implementations, two of which (`lettuce`,
`tfhe-ntt`) already carry our own upper-layer projects**". So the first goal of the requirement list is not adding
features, it is **pushing the cost of integrating below the cost of copying** (all of D1 + D2 derives from this).


### 2.4 Requirement tiers (consumer's point of view)

| Priority | Requirement | Criterion |
| --- | --- | --- |
| **P0 blocking** | versioning/release pipeline, API-diff gate, breaking-change window, the `Zq` boundary fix, removing the `rand` leak from the public API, `no_std` | miss any one of them and some consumer breaks or cannot integrate |
| **P1 adoption** | the layered crate split (L0/L1 usable on their own), multi-platform CI with benchmark thresholds, decoder fuzzing, pluggable generic XOF/hash, non-2-adic moduli and the cyclic ring `X^n−1`, extension rings / relative norms | decides whether "trying it out" becomes "the default choice" |
| **P2 competitiveness** | pluggable backends (asm/AVX-512/GPU), cross-language KAT export, formal/parameterized verification, multi-organization governance | decides whether it can become the organization's single algebra base |

---

## 3. Requirement list and acceptance criteria

Format: **REQ-ID | requirement | current status | acceptance criterion (machine-checkable)**.
Current status markers: ✅ met | 🟡 partial | ❌ missing.

### D1 Consumption contract

| ID | Requirement | Status | Acceptance criterion |
| --- | --- | --- | --- |
| REQ-D1-01 | published to crates.io, consumable as a versioned dependency | ❌ | `cargo publish --dry-run` passes for all three crates; `lattice-algebra` resolves on crates.io; CI has a release job |
| REQ-D1-02 | a semantic versioning policy (including the breaking-change rules for the 0.x period) | ❌ | a Stability section added to `CONTRIBUTING.md`: a breaking commit must carry a minor bump + a `BREAKING CHANGE:` body + a migration entry; the git-cliff template emits a "Migration" section |
| REQ-D1-03 | a breaking-change window | ❌ | old entry points kept with `#[deprecated(since, note)]` for ≥1 minor version; deleting a deprecated item needs its own PR |
| REQ-D1-04 | a public-API regression gate | ❌ | CI adds `cargo public-api --deny-warnings` (or a `cargo check-api` snapshot diff), with `api/` snapshots committed |
| REQ-D1-05 | stability tiers (stable / experimental labeled explicitly) | 🟡 | the existing `docs/.../review-soundness-completeness.md` and the "experimental" wording in `zk` are promoted to first-class citizens: every `pub` item is either stable or carries an `EXPERIMENTAL` attribute/doc marker, enumerable by a script |
| REQ-D1-06 | lib name matching the package name, searchable, conflict-free | ❌ | change `[lib] name` from `algebra`/`pqc`/`zk` to match the package name (`lattice_algebra` etc.). Two hard pieces of evidence: ① `use lattice_algebra::…` currently fails to compile outright (package name `lattice-algebra`, lib name `algebra`); ② upstream `Lazarus/algebra/Cargo.toml` already declares a crate with `name = "algebra"`, and **identical names cannot coexist in one dependency graph** |

### D2 Portability and dependencies

| ID | Requirement | Status | Acceptance criterion |
| --- | --- | --- | --- |
| REQ-D2-01 | `#![no_std]` + `alloc` | ❌ (std-only today) | `#![no_std]` at the top of `algebra`, with `use std::` only in files behind a `std` feature; CI adds `--target thumbv7em-none-eab`/`wasm32-unknown-unknown` compile legs |
| REQ-D2-02 | a declared target matrix (OS/arch/no os/wasm/embedded) | ❌ | a new target-matrix page in `docs`, plus a CI matrix covering every row marked "supported" |
| REQ-D2-03 | the public API leaks no third-party types | ❌ | change `Ring::rand(&mut impl rand::RngCore)` to our own sealed trait (`RngRead`/`SeedSource`) or route it entirely through XOF seeds; the number of items in `cargo doc` where "a dependency type appears in a public signature" = 0 (detectable by a script over the `--document-private-items` output) |
| REQ-D2-04 | minimal and replaceable dependencies (SHA3/XOF backend, FFT backend) | 🟡 | the default dependency tree (`cargo tree -e normal`) stays ≤ its current size and `rustfft` can be switched off by a feature; the XOF becomes a trait, allowing implementations other than `sha3` to be injected |
| REQ-D2-05 | reproducible builds (lockfile + `--locked` everywhere) | 🟡 | `--locked` is already in CI; add `cargo vet` (or `cargo deny`) and a license allowlist to CI |
| REQ-D2-06 | an MSRV policy (when it may be raised, and whether raising it is breaking) | 🟡 | declare that "an MSRV change = minor, announced one release ahead"; the CI matrix already has a 1.85.0 leg, but "why 1.85" must be upgraded from a comment to documentation |

### D3 Algebra coverage

| ID | Requirement | Status | Acceptance criterion |
| --- | --- | --- | --- |
| REQ-D3-01 | documented domain = tested domain | ✅ **fixed (2026-09-19, see §2.2)** | `mod_add`/`inverse`/`centered` are correct over the whole `q ≤ u64::MAX` domain; the axiom modulus set goes 15→17 (including Goldilocks **above `2⁶³`**), the remaining boundary primes are covered by targeted differential tests; `make gate` exit 0 / 726 tests |
| REQ-D3-02 | a scalar ring with large moduli (> 64 bit) | ❌ | either list it explicitly as a non-goal or provide `ZqBigInt` (`crypto-bigint`/our own limbs); either is acceptable, but it must be explicit |
| REQ-D3-03 | ring family coverage: `X^n+1` (yes), the cyclic ring `X^n−1` (no), binary fields `GF(2^k)` (no), non-2-adic moduli (fallback exists) | 🟡 | `audit.mdx` already lists the cyclic ring as 📋; acceptance = a working cyclic-ring NTT cross-checked against schoolbook |
| REQ-D3-04 | consumers can bring their own ring without changing the core | 🟡 | the traits are not sealed and are dyn-safe (or declare explicitly that dyn is not a goal). Measured: `Box<dyn Ring>` fails to compile with **E0038**, because `Ring: Sized` and the methods take `Self` as a type parameter — a normal trade-off for zero-cost algebra (ark-ff is not object-safe either), but **it has to be written down as an ADR**, together with the official alternative "when you need dynamic dispatch" (enum wrapper / newtype); otherwise every consumer trips over it once |
| REQ-D3-05 | an interop contract with the organization's non-lattice algebra | ❌ | decide and document it: whether to provide an adapter layer between `Field`/`Ring` (ark `Field` ↔ our traits), or state plainly "lattice stack only" |
| REQ-D3-06 | complex lattices / cyclotomic rings (cyclotomic beyond `X^n+1`, the Falcon number field `Q(ζ_m)`) | 🟡 | Falcon is currently a self-contained port carrying its own FFT/NTRU solver; acceptance = extract it into a general L2/L3 capability, or declare it scheme-local |

### D4 Dependable performance

| ID | Requirement | Status | Acceptance criterion |
| --- | --- | --- | --- |
| REQ-D4-01 | multi-platform benchmarks (today there is only one set of numbers, from a local M4 Pro) | ❌ | CI runs benchmarks on at least two runner classes, x86_64-linux and aarch64, and stores the results; every row of the performance page is annotated with platform + rustc |
| REQ-D4-02 | a regression-threshold gate (already listed as 📋 in the roadmap) | ❌ | compare `cargo bench` output against a baseline, red on more than X% regression |
| REQ-D4-03 | side-by-side comparison with production-grade reference implementations | ❌ | at least a ratio table against `liboqs`/RustCrypto `ml-kem`/`ml-dsa` on identical hardware (admitting the gap is also a service commitment) |
| REQ-D4-04 | pluggable backends (safe SIMD ↔ asm ↔ multithreaded) | 🟡 | `simd`/`parallel` exist and are off by default (good), but a unified dispatch layer and a runtime feature-detection contract are missing; the `wide` path has no explicit AVX-512/NEON kernels |
| REQ-D4-05 | documented performance claims kept in sync with measurements | ❌ | `performance.mdx` still says "no AVX/NEON kernels yet" while the `simd`/`simd-mlkem`/`simd-frodo` features and `crates/algebra/src/simd` already exist → documentation drift, needs a consistency-check script |

### D5 Assurance

| ID | Requirement | Status | Acceptance criterion |
| --- | --- | --- | --- |
| REQ-D5-01 | third-party audit | ❌ | at least one external audit report covering the L0/L1 + ML-DSA/ML-KEM paths, with public findings mapped to fixes |
| REQ-D5-02 | decoder/codec fuzzing | ❌ | `cargo fuzz` targets covering every `from_bytes`/`Decode` entry point, 7×24 or a scheduled 1h CI run with no crashes |
| REQ-D5-03 | a coverage threshold | ❌ | `cargo llvm-cov` in CI with per-layer thresholds (suggested: L0–L4 ≥ 80% line coverage) |
| REQ-D5-04 | constant time as tooling, not manual review | 🟡 | `crypto::ct` plus branch minimization already exist (a genuine advantage); add dudect/`ct-analyze`/`valgrind` statistics or an assembly audit (currently listed as follow-up) |
| REQ-D5-05 | a claims register | ✅ | the claimed/residual two-way table in `security-status.mdx` is a strong practice rarely seen in comparable open-source libraries; keep it and extend it per crate |
| REQ-D5-06 | CVE/yank process | 🟡 | `SECURITY.md` already has a disclosure policy; add a yank/patch-release decision tree |

### D6 Governance and operations

| ID | Requirement | Status | Acceptance criterion |
| --- | --- | --- | --- |
| REQ-D6-01 | multiple maintainers / bus factor | ❌ | `git log`: 2 authors, roughly 60 commits (2024-12-31 → 2026-09-18); acceptance = ≥2 owners with review authority + a backup owner for each critical module |
| REQ-D6-02 | release pipeline (tag → release → crates.io → docs) | ❌ | only 1 tag (`v0.1.0`); acceptance = a `release.yml` that publishes all three crates in one click + the matching tags + versioned docs |
| REQ-D6-03 | consumer entry points (issue templates, integration escalations, change review) | 🟡 | `CONTRIBUTING.md` is contributor-facing; the "I am a consumer" path (API requests, performance issues, migration help) is missing |
| REQ-D6-04 | a list of internal integration cases (who uses it, which layer) | ❌ | one live table: consumer × modules used × version × feedback; that table is itself a requirement source |
| REQ-D6-05 | documentation (design/integration/examples) | ✅ | the vocs site (architecture, feature map, parameter sets, performance, security claims) + an `examples/` directory per crate + `doc_snippet_check.rs` keeping doc code compilable — high standard among comparable projects |
| REQ-D6-06 | change communication (changelog readability, breaking summary) | 🟡 | git-cliff is wired up; but breaking commits only surface in `refactor(x)!` titles and the 0.x version never moved → consumers have no mechanical way to notice breakage |

---

### Four requirements added from the peer baseline (per [02-peer-research.md](02-peer-research.md) §4)

The four things peers already do in an established way and we have none of, registered as requirements:

| ID | Requirement | Where peers do it | Status | Acceptance criterion |
| --- | --- | --- | --- | --- |
| REQ-D1-07 | **cross-version compatibility of serialization/keys as a CI property** | `tfhe-rs` (a `backward_compatibility/` module + a dedicated CI job) | ❌ | frozen byte artifacts from older versions (already in `tests/data/`) decode and pass on the new version; add a `compat` CI job covering pk/sk/ct/sig encodings |
| REQ-D3-07 | **modulus-shape specialization**: new moduli are plugged in through a type-level choice rather than hand-written instances | `tfhe-ntt` (the kernel matrix under one API: `prime32/{generic,shoup,less_than_30bit}`, `prime64/{generic_solinas,less_than_50bit…63bit}`) | 🟡 | we already have the const-generic `Zq<Q>` (better than larkworks' per-modulus instance files), but no Shoup/Solinas specialization; acceptance = one "add a new modulus" recipe + a rehearsal of a third-party PR that changes no core code |
| REQ-D5-07 | a machine-checked assurance path (at least for the hottest paths) | `mldsa-native` (CBMC + HOL-Light/s2n-bignum proving the assembly is secret-independent in timing; Isabelle proving the Neon-NTT Barrett/Montgomery kernels), `libcrux-*` (HACL\*→Rust) | ❌ | no big-bang requirement; acceptance = declare "which layer intends to use which tool" (`crate-verify`/`kani`/CBMC-over-FFI all qualify), and distinguish "tested" from "proven" in the claims register |
| REQ-D6-07 | **a public layered matrix**: module × (stability / CT status / supported platforms / optimization targets) | liboqs `ALGORITHMS.md` + `PLATFORMS.md` (it states that it follows the Rust platform tier scheme), and "every CT failure is on the record" | 🟡 | our `security-status.mdx` already covers the "claims" half; add the "platform × module" matrix: which layers are stable, and on which platforms we guarantee it compiles / runs / has been CT-tested |

## 4. How this research judges the "distance"

No conclusion here, so as not to blur it with the gap assessment. The rubric is fixed:

1. each REQ gets a maturity level from 0–4 (0 missing / 1 mentioned in docs / 2 partially landed / 3 landed with a gate / 4 landed + gate + outward commitment);
2. each dimension takes the **lowest score** among its REQs as the dimension level (a base service is a weakest-link chain, not a weighted average — one broken consumer is enough to veto "dependable");
3. align item by item with the peer best, taken from [02-peer-research.md](02-peer-research.md);
4. output: dimension radar + distance table + P0/P1/P2 ordering, see [03-gap-analysis.md](03-gap-analysis.md).

Under this rubric the **current blockers** are: D1 (level 1: mentioned in docs only), D2 (level 0: `no_std`, naming and
the API leak all three missing), D3 (level 0–1: the `Zq` boundary defect unfixed), D4 (level 0: no multi-platform
benchmarks or thresholds), D5 (level 0–1), D6 (level 1–2). Only D6-05/D5-05 reach level 3 (gated in CI or machine-verifiable).
