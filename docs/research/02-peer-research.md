# Peer research and horizontal comparison: where is the industry baseline for an algebra base

> Data collection date **2026-09-19**: every item re-checked against the crates.io API and the GitHub API (all version numbers,
> dates, download counts, star counts and `archived` statuses below are the result of local API queries on that day, not
> second-hand); architecture details come from public repository source/CI and local clones (`ark-algebra`, `Plonky3`, `tfhe-rs`,
> `Lazarus`, `feanor-math`, `hachi-pcs`, `lettuce`). Companion docs: the requirements list is in
> [01-requirements.md](01-requirements.md), our own score and the timeline comparison are in [03-gap-analysis.md](03-gap-analysis.md).

---

## 1. Sample selection

- **Class A · general-purpose ZK algebra bases** (they define the engineering shape of a "base service"): arkworks, Plonky3,
  zkcrypto `ff`/`group`, RustCrypto `crypto-bigint`, halo2curves, winterfell `winter-math`.
- **Class B · lattice-specific algebra / scheme stacks** (the territory we actually compete in): RustCrypto `module-lattice`,
  larkworks, Lazarus, condor-rs, LatticeFold/`cyclotomic-rings`/`stark-rings`, ICICLE, feanor-math, Zama `tfhe-ntt`/`tfhe-rs`,
  Lattigo, OpenFHE, SEAL, `mldsa-native`/`mlkem-native`, liboqs, the LaBRADOR C reference implementation, `fn-dsa`.

---

## 2. Horizontal matrix A: general-purpose algebra bases (the engineering-commitment baseline)

| Dimension | **This project** | arkworks | Plonky3 | zkcrypto ff/group | RustCrypto c-bigint | winterfell | halo2curves |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Latest version (date) | 0.1.0 **not published** | 0.6.0 (2026-04-26) | 0.7.0 (2026-09-04) | ff 0.14.0 (2026-05-30) | 0.7.5 (2026-06-22) | 0.13.1 (2025-07-19) | 0.10.0 (2026-05-14), **repo archived** |
| Installable from crates.io | ❌ (none of the three package names `lattice-algebra`/`lattice-pqc`/`lattice-zk` **is currently taken**) | ✅ | ✅ (`p3-*`) | ✅ | ✅ | ✅ | ✅ |
| Cumulative downloads (this re-check) | 0 | `ark-ff` **96,358,403** | `p3-field` 2,721,559 | `ff` 237,733,433 | 278,404,489 | `winter-math` 864,586 | 1,009,166 |
| `no_std` | ❌ std-only (8 files, 20 occurrences of `use std::`) | ✅ `#![cfg_attr(not(feature="std"), no_std)]` + `#![deny(unsafe_code)]` | ✅ whole stack `no_std + alloc` | ✅ | ✅ | ✅ (incl. WASM) | 🟡 (`asm` requires `std`) |
| Crate granularity | ❌ **single crate for L0–L4 (10.9k LOC)** | 🟡 ff/ec/poly/serialize/std/relations + `curves/` | ✅ extremely fine (the local clone alone has 36 workspace members: field/dft/fri/challenger/commit/merkle/mds/poseidon/util…) | ✅ minimal surface (traits only) | ✅ one crate per algorithm | 🟡 | 🟡 |
| MSRV | declares 1.85 (CI has a 1.85 leg) | ⚠️ released 1.75, master already requires 1.89 (PR #1121, breaking) | ❌ does not declare `rust-version` | 1.85 | **written policy: an MSRV bump is not breaking and can land in a patch** | 1.87 | 1.74 |
| CI target matrix | ❌ single runner (ubuntu/x86_64) + 6 feature legs | multiple OS, no SIMD leg | ✅ linux/macos/**windows** + explicit SIMD legs (`avx2`/`avx512f`/`gfni`/`sve2` on arm64) + `wasm32-unknown-unknown` build + `wasm32-wasip1` tests run under wasmtime | ✅ | ✅ | ✅ incl. WASM | 🟡 |
| Release pipeline | ❌ manual, 1 tag | 🟡 manual, plus a history of `cargo publish --no-verify` | ✅ release-plz + per-crate tag (`p3-field-v0.7.0`) | ✅ | ✅ (106 releases) | ✅ | 🟡 |
| public-API gate | ❌ | ❌ | ❌ (relies on the crate boundary itself) | 🟡 RFC process | ❌ | ❌ | ❌ |
| External audit | ❌ | ❌ (no field-arithmetic audit of the algebra body itself) | ✅ Least Authority (2024-07-16 declared production ready) | ❌ (README explicitly makes no CT claim) | ✅ NCC Group/Entropy (with the caveat that "the implementation has since diverged significantly") | ❌ (README states itself as unaudited and not fit for production) | ❌ |
| Axiom/property test infrastructure | ✅ 15-modulus ring-axiom set (2…2³²) + three-path NTT cross-check | ✅ `ark-algebra-test-templates` (a separately published fixtures crate) | ✅ `p3-field-testing` (incl. SIMD↔scalar equivalence) | 🟡 | 🟡 | ✅ proptest | 🟡 |
| Constant-time tooling | ❌ (has `crypto::ct` + a claims register) | ❌ | ❌ | 🟡 (`subtle`, the ecosystem standard) | 🟡 (`ctutils` + `*_vartime` naming discipline) | ❌ | 🟡 |
| FIPS/official vector alignment | ✅ **511 KAT/ACVP vectors byte-exact** | n/a | n/a | n/a | ✅ | n/a | n/a |

**How to read Class A**: on the **mathematical-correctness evidence** column this project meets or beats its peers (KAT density,
three-path cross-check, the claims register are rare practice in this class); the gap **sits entirely in the engineering-shell
columns**. Note that winterfell is willing to write "unaudited, not fit for production" in its README —
**peers earn trust through explicit maturity statements, not through silence.**

---

## 3. Horizontal matrix B: lattice-specific stacks (the territory we actually have to win)

| Project | Release / activity (re-checked against the API on 2026-09-19) | What the algebra layer gives | What it does not give (= our position) |
| --- | --- | --- | --- |
| **RustCrypto `module-lattice`** | **0.2.3, created 2026-01-27, updated 2026-05-10, 5,492,955 downloads** | `no_std`, edition 2024, **MSRV 1.85 (same as ours)**, `hybrid-array` const-generic vectors, a `Field` trait (`small_reduce`/`barrett_reduce`), `Elem/Polynomial/Vector/NttPolynomial/NttVector/NttMatrix`, `ctutils`+`ZeroizeOnDrop` throughout | ring degree **welded to `U256` (X²⁵⁶+1)**; only one modulus shape (Barrett), so Montgomery/STARK-friendly primes do not fit; no decomposition, no Gaussian sampling, no XOF/transcript; **zero ZK surface** |
| **larkworks `lark`** | only **0.1.0 / 2019-01-15** on crates.io (1,892 downloads); repo 21★, pushed **2024-05-20**, 16 open issues; **not published** (the `license = ""` in the root `Cargo.toml` blocks `cargo publish` outright) | the earliest (2019) attempt at a "Rust lattice algebra library": `field/ring/polynomial/vector/domain` layering + Ajtai/Chipmunk hashes | hand-written per-modulus instances in `definition.rs`/`instances/{f3329,f8380417,ring12289,…}` (adding one modulus means writing 4 instance files); the source states outright that it restricts to NTTField "for convenience"; **does not reuse `ark-ff`/`ark-poly`** (depends only on `ark-std`), so there is no interop with arkworks. Its open issues are exactly our requirements list: #10 better polynomial ring abstraction, #12 NTT form, #14 `no_std`+WASM, #5 CI |
| **Lazarus** | 75★, **6 contributors**, pushed **2026-07-12**; crates.io 0.1.0 (2025-05-14, **571 downloads**) | the module split is exactly the shape we want: `algebra/{zq, ring/{poly,polyvec,polymat}, ntt, rng, sampling/{uniform,binomial,gaussian,rejection,challenge}}` + `pcs`/`arithmetization`/`labrador`/`greyhound`; **its differential-testing discipline is worth copying** (`verify_ntt.py` as a 1:1 Python twin, byte-by-byte assertions on the CDF155 table, NTT↔transparent adjoint tests) | the modulus is **not** const-generic: `pub struct Zq { value: usize }` + `const Q = (1<<32)-99` hardcoded, plus an `assert!(usize::BITS >= 64)` compile-time fence; inversion goes through `a^(q-2)` (no Montgomery/CT); std-only; `PolynomialRing`+`RqMatrix` and `ring` coexist as two APIs; issue #9 "Matrix struct" open since 2024-11. **The comparison table and the self-reported performance numbers in its README cannot be trusted** |
| **condor-rs** (Nethermind) | 22★, **`archived = true`**, last push 2025-09-09; not published | the LaBRADOR scheme stack (`labrador/src/ring/{zq,rq,rq_vector,rq_matrix}`) | the `Zq` constant `Q = u32::MAX` relies on bare u32 wrap-around (fast but entirely non-reusable); **zero trait declarations** inside `ring/`; closed issue #79 ("defect in the decomposition computation") + open #58 "Define usable rings" = the ring abstraction was never solved |
| **LatticeFold + `cyclotomic-rings` + `stark-rings`** | 129★, 13 contributors, pushed 2026-05-01; **no release, not published** (issue **#193 "LatticeFold crate release"** open since 2025-09) | genuinely extracts reusable layers: `SuitableRing` trait + `rings/{babybear,frog,goldilocks,stark}` + `challenge_set/` + balanced decomposition; rings built on `ark_ff::PrimeField` (the most arkworks-native design in this niche) | `rust-toolchain` pins `nightly-2025-03-06`; the README states outright "prototype, has not been through careful code review, NOT ready for production", `cargo bench` takes about 48 hours |
| **ICICLE** (Ingonyama) | 502★, v4.0.0 (2025-07-11), pushed **2025-11-10** (untouched for ~10 months); `icicle-core` on crates.io **frozen at 1.3.0 / 2024-02-14 (1,928 downloads)**, `icicle-babykoala`/`icicle-runtime` **not published** | **the ZK half is the product that most resembles our target**: documented unified traits for `Zq`/`Rq = Zq[X]/(X^d+1)`/`Tq` (evaluation form), `NegacyclicNtt` + `NegacyclicNttConfig` (backend/device/async), balanced base-b decomposition, ℓ₂/ℓ∞ norm-bound checks, reproducible JL projection, rejection-sampled challenge polynomials; q = baby bear × koala bear = 4289678649214369793; host/device generic slices let one set of traits feed both CPU and CUDA | **the reason you cannot get it is precisely release engineering**: git-only, the crates.io version stopped in 2024; the zero-copy `reinterpret_slice` is exposed as `unsafe` with only a Safety comment (no static layout assertions) |
| **feanor-math** | pushed 2025-05, single author, 46.8k LOC | the entire library is lattice algebra: `ring.rs`/`field.rs`/`rings/*`/`algorithms/convolution/ntt.rs`/`matrix`/`reduce_lift` — **the trait hierarchy most directly comparable to ours** | no organizational backing, no scheme layer (contains no PQC/ZK protocols) |
| **Zama `tfhe-ntt` / `tfhe-rs`** | `tfhe-ntt` **0.7.1 (2026-04-21, 326,982 downloads)**; `tfhe-rs` v1.8.1 (2026-09-17), 1,664★, **64 contributors**, MSRV 1.91.1, SLSA L3, ≥40 workflows | **the single finding most worth copying in this research**: `tfhe-ntt/src` is a "**kernel matrix specialised by modulus shape**" — `native{32,64,128}`, `prime32/{generic, less_than_30bit, less_than_31bit, shoup}`, `prime64/{generic_solinas, less_than_50bit…63bit, shoup}`, `fastdiv`/`roots`/`product`/`u256_impl`; several modulus families under one API = **a finished answer to "adding a new modulus without touching the core"**. Plus a `backward_compatibility/` module + a dedicated CI job (cross-version key/ciphertext compatibility as a tested property), GPU/FPGA (`hpu`) backends, a `cbindgen` C API, a WASM-JS parallel API | NTT/FFT only — no module lattices, no schemes, no ZK protocol layer. **And: when Zama itself builds ZK proofs (`tfhe-zk-pok`) it depends on `ark-bls12-381`/`ark-ec`/`ark-ff`/`ark-poly` and does not reuse its own ring layer** (see the §8 risks) |
| **Lattigo** (Go) | v6.2.0 (2026-02-02), 1,446★, pushed 2026-06-16 | the README states "**strictly layered, the packages form a linear dependency chain**": `ring` → `core/{rlwe,rgsw}` → `schemes/{bgv,bfv,ckks}` → `circuits` → `multiparty`; the `ring` package itself is scheme-agnostic and usable directly (`ntt`/`modular_reduction`/`basis_extension` (RNS MODUP/MODDOWN)/`automorphism`/`subring_ops`/`sampler_{gaussian,ternary,uniform}`/`vec_ops`/`pool`) | pure Go, **zero assembly in the whole tree** (traded for cross-platform and WASM); runtime `N` (not type-level dimensions); offers no capability at all to Rust consumers |
| **OpenFHE** | 1.5.1 (2026-04-10), 1,200★, pushed 2026-09-19, **about 4 releases/year**; NumFOCUS funded, governance document v2.0 (adopted 2021-03-21: Steering → Crypto Team (≥1 meeting per quarter, consensus voting, handles newly published attacks) → Advisory Board) | the most mature organisational model of "algebra as a base": the three layers `core/pke/binfhe` + **two HALs** (`math/hal`, with four big-integer backends coexisting; `lattice/hal` with `poly-interface.h`/`dcrtpoly-interface.h`/`lat-backend.h`) + DCRT↔Coeff as a first-class, documented axis (`Best_Performance.md` gives a per-module build recipe) | **two cautionary tales (both open issues)**: #1303 ("sort out correctness and optimisation of the big-integer backends, and retire MATHBACKEND 2") = 3 of the 4 backends are unfunded liabilities; #1294 ("provide a supported GPU/accelerator interop surface, eliminating the need to patch OpenFHE") — the CUDA backend FIDESlib needs `public:` injected at 9 points across **7 header files** just to compile, and the maintainers' judgement is "cannot be merged as is: that would turn arbitrary internal implementations into a de facto ABI commitment". In addition `lattice/hal/README.md` and `Best_Performance.md` still advertise the Intel HEXL/AVX512-IFMA backend, while `grep -i hexl` over the whole tree returns no match and `CMakeLists.txt` has no `WITH_INTEL_HEXL` option = **the backend was removed, the documentation was not updated** (the same disease as the SIMD documentation drift in our `performance.mdx`) |
| **`mldsa-native` / `mlkem-native`** (PQCA / Linux Foundation) | 108★ / 236★, both pushed 2026-09-18; `CODEOWNERS`/`MAINTAINERS.md`/`RELEASE.md`/`SOUNDNESS.md`/`API-CONVENTIONS.md` | **the industry ceiling on correctness assurance**: a fixed C front end + **swappable arithmetic back ends and the FIPS-202 back end behind the same interface header files** (portable C / AArch64 Neon / x86-64 AVX2 / 32-bit Armv8.1-M Helium); CBMC covers memory safety, type safety and absence of UB for all C back ends; **HOL-Light + s2n-bignum prove that all AArch64 and x86-64 assembly is functionally correct, memory safe and has a timing independent of secrets** (and explicitly lists two exceptions: `rej_uniform` is deliberately variable-time on public data, and `rej_uniform_eta{2,4}` claims CT but is not yet proven); Isabelle/HOL proofs of the scalar decomposition algorithm plus the formal treatment of the Neon-NTT Barrett/Montgomery kernels; full official ACVP + Wycheproof; downstream AWS-LC/liboqs/CHERIOT-PQC | C90, a single scheme family, no traits/generics. **It is our assurance target line, not a feature competitor** |
| **liboqs** | 3,067★, 107 open issues, pushed 2026-09-19; 0.13.0(2025-04)→0.14.0(2025-07)→0.15.0(2025-11)→**0.16.0(2026-07-09)**, about 3–4 releases/year | **the governance artefacts are the most worth porting wholesale**: `ALGORITHMS.md`, a per-scheme matrix (standardisation status / main implementation + pinned commit / upstream maintainability / OQS tier / NIST level / **constant time** / **formal verification** / optimisation target) + written criteria (Tier 1 Core requires "CT testing on all parameter sets in CI + ≥2 committers + a CODEOWNERS entry"); `PLATFORMS.md` **explicitly models the Rust platform-tier system**; the `tests/constant_time` approach is "every failure is recorded"; KAT+ACVP+fuzz (4 fuzz targets)+coverage+**weekly continuous benchmarking**+**downstream release testing** (oqs-provider/boringssl/openssh) | **still no reusable algebra layer after 17 years**: under `src/kem/ml_kem/` you get `mlkem-native_{512,768,1024}_{ref,x86_64,aarch64}` plus `cupqc_*_cuda`, `icicle_*_icicle_cuda` — a **per-parameter-set × per-ISA × per-GPU directory explosion**; the only shared layer, `src/common/`, is primitives (sha2/sha3/aes/rand/shims), not algebra |
| **`fn-dsa` / `fn-dsa-comm` (pornin)** | 0.4.0 (2026-07-22), roughly 94.8k / 98.8k downloads each — **the highest download count of any Rust Falcon crate** | splits **NTT/negacyclic arithmetic out into `fn-dsa-comm` so others can reuse it** (our `pqc::falcon` is precisely the counter-example: a self-contained port) | Falcon-specific, not a general base |
| **`libcrux-ml-dsa` (HACL\*→Rust)** | 0.0.10 (2026-07-15), 186,505 downloads, built on `libcrux-hacl-rs` 2.3M / `libcrux-intrinsics` 3.4M | the existence of a "**verifiably generated** Rust lattice arithmetic" channel is a ready-made reference for our "formal" path | generated output, not a reusable trait base |
| **LaBRADOR C reference implementation** | 54★, pushed 2025-02-20 | `polx/poly/polz.c` + hand-written `ntt.S`/`invntt.S` + `data{24..64}.c` precomputed per `LOGQ` (where `LOGQ=32,QOFF=99` is exactly the modulus Lazarus hardcodes) + `jlproj.c` + the `chihuahua/dachshund` front ends | **no KAT/ACVP harness, no CT tooling, no SIMD dispatch** — precisely the target our differential tests / vector alignment should aim at |

### 3.1 Class B verdict (the single most important external conclusion of this research)

> **As of 2026-09-19, no project satisfies all of: ① published on crates.io; ② generic modulus / ring degree (const-generic);
> ③ `no_std`; ④ capabilities as traits; ⑤ consumed by both PQC schemes and lattice zkSNARKs.**

- The one satisfying ①③④ (`module-lattice`) **fails ②⑤** (dimension welded to 256, zero ZK surface);
- The one satisfying ②④⑤ (ICICLE's lattice API) **fails ①** (crates.io stopped at 1.3.0 of 2024-02-14);
- The one satisfying ②④⑤ and having a release cadence (Lazarus) **fails ② (hardcoded modulus) and ③**, with 571 downloads;
- The one satisfying ①③ with the strictest engineering (`mldsa-native` and friends) is **C** and a single scheme family.

**And the three projects that "should have become the base" are each stuck on utterly mundane engineering items**: larkworks is
stuck on an empty `license = ""` field so `cargo publish` cannot run; LattiRust is stuck on having **no LICENSE at all**
(legally unusable); LatticeFold is stuck on a pinned nightly toolchain + no release published (issue #193).
→ The reason this position was lost has **never been the mathematics, but the service shell**. That is the same conclusion
[03 §1](03-gap-analysis.md) reaches about our own score.

---

## 4. Governance and assurance baseline (four things peers do and we have none of)

| Peer practice | Evidence | What it demands of us |
| --- | --- | --- |
| **Layered public matrices**: per scheme × (standardisation status / CT / formal verification / optimisation target) + per platform tiers, with written criteria | liboqs `ALGORITHMS.md`, `PLATFORMS.md` (states itself as modelled on the Rust platform-tier system) | Add REQ-D6-07: one `STABILITY.md`/`PLATFORMS.md` stating clearly which layers are stable, how far each platform is supported, and the CT status module by module. Our `security-status.mdx` already delivers the "claims" half; the "platform/module matrix" half is missing |
| **Front end / back end separation + swappable back ends with a written integration contract** | `mldsa-native`/`mlkem-native`: the native back ends are unified behind the `src/native/api.h` interface, "minimising duplicated code and reasoning burden"; the AArch64/x86-64 assembly is **all proven timing-independent from secrets via HOL-Light** | REQ-D4-04 upgrades from "add SIMD" to "**define a back-end contract**" (including the expectations for CBMC / proof-style tooling); otherwise every new SIMD back end re-enacts the liboqs directory explosion |
| **Cross-version compatibility as a CI property** | `tfhe-rs`'s `backward_compatibility/` module + a dedicated CI job; OpenFHE uses `RELEASE.md` + an rc process | Add REQ-D1-07: **backward-compatibility tests** for the serialization format and for keys/parameters (we have the `serialization.mdx` design page but no compatibility regression) |
| **Continuous benchmarking of performance and key sizes + regression gates** | `tfhe-rs` ≥40 workflows, incl. `benchmark_perf_regression.yml`, `benchmark_ct_key_sizes.yml`, `benchmark_tfhe_{fft,ntt}.yml`; liboqs weekly continuous benchmarking | The industrial version of REQ-D4-01/02: not "run a benchmark once" but **benchmarks as a CI property + a weekly trend** |
| **Governance and funding structure** | OpenFHE: NumFOCUS sponsorship + Steering/Crypto Team/Advisory Board (v2.0, 2021-03-21); PQCA/Linux Foundation hosts `mldsa-native` | The concrete shape of REQ-D6-01: a single-person project cannot self-certify that it "will not stall"; what is needed is **inheritable governance artefacts** (CODEOWNERS, MAINTAINERS, decision records), not more code |

**The two cautionary lessons from OpenFHE** (they must go into the design constraints):
1. **A HAL with only one implementation + documentation advertising a removed back end** (HEXL is no longer in the tree,
   `Best_Performance.md` still recommends it) = our `performance.mdx` currently says "no AVX/NEON kernels yet" while the `simd`
   feature already exists — **the same disease** (REQ-D4-05).
2. **No supported accelerator interop surface → users can only patch upstream** (FIDESlib needs `public:` injected at 9 points in
   7 header files) = if our trait surface is not enough, the consumer's fate is not "a bit slower" but **a fork** (see §6; the
   industry already does exactly this).

---

## 5. Timeline view: cadence comparison

| Actor | Cadence anchors (verified this pass) | Implication |
| --- | --- | --- |
| This project | 2024-12-31 → 2026-09-18 (21 months), 60 commits, 2 authors, 1 tag, 0 releases | Not short on implementation speed; short on commitment actions |
| Plonky3 | 0.5.4 / 0.6.3 patches (2026-07-30) → 0.7.0 (2026-09-04), release-plz automatic per-crate tags | merging is versioning; no manual "release day" needed |
| arkworks | 0.4.x → (**21 months**) → 0.5.0 (2024-10-28) → (**18 months**) → 0.6.0 (2026-04-26); users asked for a 0.4.3 patch over one derive warning (#980) | The cost of hoarding major versions: long-lived branches nobody maintains. **Cadence to avoid** |
| liboqs | 0.13.0(2025-04) → 0.14.0(2025-07) → 0.15.0(2025-11) → 0.16.0(2026-07), about 3–4 releases/year | governance-shaped cadence |
| OpenFHE | 1.4.0(2025-08) → 1.4.2(2025-10) → 1.5.0(2026-02) → 1.5.1(2026-04), about 4 releases/year | quarterly cadence + an rc process |
| SEAL | 4.4.3(2026-08-04) → 4.4.4(2026-08-28) → 4.4.5(2026-09-14), and the README's first sentence is "4.4 is a critical **security** update (untrusted input handling / memory safety / interop fixes)" | High adoption ≠ a reusable base; but **the patch cadence is part of the credibility** |
| `module-lattice` | created 2026-01-27 → 0.2.3 (2026-05-10) → **5,492,955 downloads** | "the RustCrypto brand + `no_std` + published" = **5.5M downloads in 4 months**. In our equivalent window, downloads are 0 |
| larkworks / Lazarus / LatticeFold / ICICLE | 2019-01 stuck at 0.1.0 / 0.1.0 (2025-05, 571 dl) / no release / crates.io stuck at 1.3.0 of 2024-02 | The historical failure mode of lattice algebra bases is consistent: **release and governance stall**, not insufficient mathematics |

---

## 6. The most important peer insight: **algebra libraries are forked rather than followed**

Almost nobody in Class A "uses the upstream algebra and follows its upgrades": SP1 renamed and self-hosted plonky3 as `slop-*`
(6.8.0, 2026-09-11) and pinned `=0.4.3-succinct` for a long time; Ceno pins `=0.4.3`; Miden publishes `p3-miden-*`; Argument
maintains its own Plonky3 fork; Filecoin's `blstrs` has been frozen at 0.7.1 (2023-09) for three years while
`filecoin-proofs-api` is already at 19.1.0; halo2curves was simply archived; and arkworks itself concedes that its release graph
is tangled (#1103: `ark-ff`'s test templates depend on `ark-ec`, so field-only tests have to drag the whole EC stack along).

Class B is the same, and **right under our noses**: locally we are already a fork of `lettuce` (overridden with a
`[patch.crates-io] path`), and a collaborator's `hachi-pcs` chose `ark-ff 0.5` + `tfhe-ntt 0.6.1` + 4,681 lines of hand-rolled
`src/arithmetic/*`.

> Conclusion: **fork resistance = ① a small and stable trait surface; ② frequent releases with windows for breakage;
> ③ everything injectable (back end / hash / RNG / serialization), so that forking loses its reason.** These three map to
> G2/G3/G4/G6 in the gap list and to REQ-D4-04; they are the **reason for existing**, not engineering decoration.

---

## 7. Copy verbatim / explicitly do not copy

| Peer practice | Adopt | Rationale (in this project's context) |
| --- | :-: | --- |
| Plonky3 `release-plz` + per-crate tags + fine-grained crate split | ✅ | closes REQ-D1-01/02, REQ-D6-02 and "L0–L4 cannot be taken layer by layer" (G9) in one move |
| Plonky3 CI: explicit SIMD feature legs + `wasm32-unknown-unknown` + `wasip1` tests run under wasmtime | ✅ | our `wide`-family `simd` features have **so far only ever compiled on the single linux-x86_64 leg**; nobody in the lattice camp is doing this, so it is the cheapest and the most differentiating |
| `tfhe-ntt`'s **kernel matrix specialised by modulus shape** (`prime32/{generic,shoup,less_than_30bit}`, `prime64/{generic_solinas,less_than_50bit…63bit}`) | ✅ | this is the finished answer to "adding a new modulus without touching the core", and the path that upgrades our const-generic `Zq<Q>` from "parameterised" to "specialised" (REQ-D3-07) |
| liboqs' layered `ALGORITHMS.md`/`PLATFORMS.md` matrices + "record every CT failure" | ✅ | splices naturally onto the existing claims register; REQ-D6-07 |
| `mldsa-native` front-end/back-end contract (unified interface headers + swappable back ends + proven assembly) | ✅ (staged) | define the contract first, proof capability can come later; otherwise every new SIMD back end re-enacts the directory explosion |
| Lazarus' differential-testing discipline (1:1 Python twin + byte-by-byte CDF table assertions + adjoint tests) | ✅ | we already have 511 vectors and 13,000 differential cases in `fpr`, so this is an **extension, not new construction**; the target should be the LaBRADOR C reference (it has no KAT harness) |
| `module-lattice`'s hygiene items: `no_std` + `hybrid-array` + `ctutils`/`zeroize` + `[lints] workspace`, edition 2024 / MSRV 1.85 | ✅ | **same MSRV and same edition as us, yet published and already at 5.5M downloads** → the gap is purely publishability and contract, so it is highly reachable |
| ark `FpConfig<N>` + `Fp<MontBackend<Cfg,N>, N>` double const-generic | ❌ | precisely the source of arkworks' unreadable signatures (#901, extension-field type gymnastics). `Zq<const Q: u64>` with a single parameter + capability traits are strictly better — **do not regress "to align with arkworks"** |
| ark `#[unroll_for_loops(12)]` + `#[inline(always)]` | ❌ | #1104: one `into_bigint` → ~6k lines of Rust → 40k lines of LLVM IR, 500 ms of codegen for a single function. We should add a compile-time baseline to CI |
| larkworks `definition.rs` + per-modulus `instances/*.rs` | ❌ | writing 4 instance files per new modulus is **the anti-pattern we have to beat** (its open issue #10 is complaining about exactly this) |
| halo2curves: the `asm` feature requires `std` | ❌ | conflicts with REQ-D2-01 |
| liboqs: per-parameter-set × per-ISA × per-GPU directory explosion | ❌ | no shared algebra layer = still no algebra base after 17 years |
| OpenFHE: compile-time `#define` to pick the HAL, 4 back ends but only 1 affordable | ❌ | #1303/#1294 are the ending; the number of back ends must be aligned with maintenance capacity |

---

## 8. The window of opportunity, and a risk this document has to state

**Evidence that "this position is still empty"**: none of the five conditions in §3.1 is met simultaneously by any project; the
three competitors are stuck respectively on a LICENSE field / no LICENSE / a pinned nightly; to this day nobody in the lattice
camp has CI with cross-target platforms + SIMD feature legs; and `module-lattice` proves that **a lattice algebra crate at the
same MSRV/edition, once published, immediately reaches seven-figure download counts**.

**Risks (the arguments you will hear if we do not do this)**:
1. **The proposition "PQC and ZK share one algebra base" has not been validated by any production deployment.** The most
   countervailing data point comes from Zama: it owns the strongest Rust lattice ring/NTT layer in this research (`tfhe-ntt`),
   yet when it builds ZK proofs (`tfhe-zk-pok`) it chooses `ark-bls12_381`/`ark-ec` (discrete-log vector commitments) and
   **does not reuse its own ring layer**.
2. ICICLE has already written "unified `Rq`/`Tq` traits + negacyclic NTT + balanced decomposition + JL + norm bounds" up as a
   documented API — **our differentiation lies not in "having thought of these abstractions" but in "published + generic modulus +
   `no_std` + PQC from the same source"**.
3. `mldsa-native`/`libcrux` have raised the assurance baseline to the level of machine-checked proofs; our CT claims rank near the
   top in the Rust camp, but under the identity of "a PQC implementation" the peers we are measured against are those
   (see 03 §5 P2/G14–G15).

→ The position of this document set is therefore: **do not widen the mathematical scope; first turn the algebra we already have
   into a service that is publishable, portable across targets and regression-tested** (03 §5 P0), and then calibrate every
   later step against the copy list in §7 — rather than competing with arkworks on the number of abstractions or with liboqs on
   the number of schemes.

---

## 9. Not verified / not trusted

- **The reverse-dependency counts for ark-ff / p3-field (512 / 111)**: the crates.io `reverse_dependencies` re-check returned 0
  this time (not obtained, pagination/permissions), so the body text cites only **download counts** (exact values, re-checked).
- **Peer performance numbers**: neither arkworks nor Plonky3 publishes a citable formal benchmark table; the performance
  comparison table in the Lazarus README and the self-reported figures in condor-rs are self-measured and partly blank. → This
  document makes **no "N× faster than X" statement of any kind**; horizontal performance must be measured against a self-built
  same-machine baseline (REQ-D4-03).
- **`lark-mont4x`**, `gf2k`, `m4d`, `GOTC`, `MSCryPTO`, `gallaea`, and the Phala/Infinigence lattice crates: no corresponding
  repository found, so they are not used as peer samples. `argument-studio/brainfuck` and Mina's Rust algebra crates were
  likewise not found.
- **Lattigo's claim of "performance comparable to C++ libraries"**: the 2025 ACM comparison study it cites
  (doi 10.1145/3729706.3729711) was not retrievable this time, so the conclusion is not trusted.
- **OpenFHE's `B256`/`B64` kernels and its `ABI/NATIVE/NUMA/PTHREADS` backend labels**: not found on the current `main`; the
  actual knobs are `MATHBACKEND∈{2,4,6}`, `NATIVE_SIZE∈{32,64,128}`, `WITH_OPENMP`, `WITH_NATIVEOPT`. The body text uses the latter.
- **The artifact repository of the Falcon vectorisation paper (IACR 2025/1867)**: the abstract page gives no URL, and the
  8.4×/4× figures have not been reproduced or verified; they serve only as directional support for "BaseSampler is the bottleneck".
