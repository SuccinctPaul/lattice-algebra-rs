# Lattice Algebra Rust

[![CI](https://github.com/SuccinctPaul/lattice-algebra-rs/workflows/CI/badge.svg)](https://github.com/SuccinctPaul/lattice-algebra-rs/actions?query=workflow%3ACI)
![minimum rustc 1.85](https://img.shields.io/badge/rustc-1.85+-red.svg)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/SuccinctPaul/lattice-algebra-rs)

A multi-crate Rust workspace for lattice-based cryptography: one algebraic
foundation from which both NIST PQC schemes (ML-KEM / ML-DSA / Falcon plus
the round-3 alternates FrodoKEM / NTRU / Streamlined NTRU Prime) and
lattice-based zkSNARKs (LaBRADOR / GreyHound / LatticeFold-style) derive
directly.

> **Vision**: the "arkworks / plonky3 for lattice-based cryptography".
> The full architecture design lives in the docs site:
> **https://succinctpaul.github.io/lattice-algebra-rs/** (deployed from
> `main` by CI), or run it locally via [`docs/README.md`](docs/README.md)
> (`cd docs && npm install && npm run dev`).

## Workspace layout

| Crate | Path | Contents |
| --- | --- | --- |
| `lattice-algebra` | [`crates/algebra`](crates/algebra) | L0–L4 foundation: scalar rings (`Zq`), negacyclic polynomial rings (`PolyRing`), capability traits (`Ring`/`Field`/`TwoAdicRing`/`CenteredRing`), NTT + NTT-domain views, module-lattice vectors/matrices, XOF / transcript / sampling crypto |
| `lattice-pqc` | [`crates/pqc`](crates/pqc) | NIST PQC schemes on the foundation: **ML-KEM** (FIPS 203) keygen / encapsulate / decapsulate and **ML-DSA** (FIPS 204) keygen / sign / verify, all three parameter sets each, byte-exact with the official ACVP vectors; **Falcon** (round-3 spec) keygen / sign / verify, byte-exact with the official round-3 KATs; and the round-3 lattice alternates **FrodoKEM** (both AES/SHAKE matrix-A variants), **NTRU** and **Streamlined NTRU Prime** (all parameter sets), byte-exact with the official round-3 submission KATs. FN-DSA (FIPS 206) is still a draft — parameter sets may shift before the freeze; no stable release until then |
| `lattice-zk` | [`crates/zk`](crates/zk) | Lattice zkSNARK building blocks, organized by domain — `foundation` (samplers / Fiat–Shamir / encoding), `instance` (the `Z_{2^32}` ring + toy R1CS), `commitment` (shared Ajtai key + Z1 SIS instance), then the protocol domains `sigma` (Lyubashevsky FS-NIZK), `opening` (LaBRADOR-style batched opening), `sumcheck` (ring-sumcheck + gadget-IPA), `shortness` (projection / norm-bound arguments) and `folding` (Nova-style and LatticeFold-style). A primitive-level survey maps each domain to the literature (`crates/zk/docs/survey-lattice-zksnarks.md`) |

## Usage

Depend on the crates you need (lib names: `algebra`, `pqc`, `zk`):

```toml
[dependencies]
lattice-algebra = "0.1.0"   # use algebra::ring::...
lattice-pqc     = "0.1.0"   # use pqc::mldsa::...
lattice-zk      = "0.1.0"   # use zk::sigma, zk::opening, zk::folding, ...
```

```rust
use algebra::module::ModuleVector;
use pqc::mldsa::{MlDsa65, MlDsaParams};
use zk::commitment::ajtai::CommitmentKey;
```

## Requirements

- Rust 1.85.0 or later (MSRV, verified in CI)
- Runtime dependencies of the foundation: `rand`, `rustfft`, `serde`, `sha3`

## Development

```sh
make gate                     # the merge gate: fmt + clippy -D warnings + tests
cargo test --workspace        # 670+ tests (unit + integration + doc, incl. all KAT suites)
cargo bench --workspace       # criterion: foundation, ML-DSA, Falcon, Z1-Z4 protocols

make kat                      # regenerate KAT/ACVP fixtures from official NIST sources + verify
make audit                    # RustSec advisories, licenses, no-unsafe policy scan
```

Each crate carries its own `README.md` (see `crates/<name>/README.md`),
runnable `examples/`, integration tests in `crates/<name>/tests/`, and
criterion benchmarks in `crates/<name>/benches/`. See
[`scripts/`](scripts) and the [`Makefile`](Makefile) for the full
maintenance tooling.

### Test coverage (`make coverage`)

```sh
brew install cargo-llvm-cov   # or: cargo install cargo-llvm-cov
make coverage                 # per-file line/function/region table
make coverage-missing         # + the exact uncovered line numbers per file
make coverage-gate FLOOR=80   # same run, non-zero exit below the floor
make coverage-html            # browsable HTML for one crate
```

**What it tells us.** 511 official KAT/ACVP vectors prove that the *happy paths*
are byte-exact; they say nothing about which lines our tests never execute at
all. Source-based coverage (`cargo llvm-cov`) closes exactly that gap: it answers
"has any test ever run this branch?" — the rejection-sampling retry limits, the
`None` arms of the decoders, the SIMD-vs-scalar fallback selection, the
`debug_assert` precondition paths. Those are the lines where a regression hides
silently, and they are the lines a "reference implementation" claim rests on.

**What it does not tell us — read this before trusting a big number.**

- **Not correctness.** A covered line only proves it executed, not that its
  result was checked. Our own example: `module::rounding`'s hint probe ran in CI
  every day, was 100% covered, and asserted nothing (it only `println!`s) — it
  became a real test only when the identities were turned into `assert_eq!`s.
- **Not soundness, not resistance to adversarial input.** Coverage measures the
  inputs our tests chose, which is why fuzzing the decoders
  ([`make audit`](#development) does not do it yet) is the complement, not a
  substitute.
- **Not constant-time.** Line coverage is blind to whether a branch was taken in
  secret-dependent order.
- **Region/branch coverage is the honest second column.** A function can be 100%
  "lines covered" while one arm of an `if` never fires; check the `Regions`
  column, not just `Lines`.

Treat the number as a **map of where to look**, not a grade. The useful workflow
is: run `make coverage-missing`, sort by the foundation layers (L0–L4 in
`crates/algebra`), and ask of each uncovered region whether a missing test or a
missing capability is the real gap.

### Coverage baseline (2026-09-19)

`make coverage-missing` on `feat/pqc` @ rustc 1.93.0, Apple M4 Pro,
cargo-llvm-cov 0.9.1 — **92.41% lines / 93.44% regions / 90.42% functions**
(14,924 instrumented lines, 1,132 uncovered). What the uncovered mass actually is:

| File | Lines | Uncovered region | Real cause |
| --- | --- | --- | --- |
| `algebra/src/matrix/matrix.rs` | 60.6% | 282–340, 370–378, 561–589 | the whole `#[cfg(feature = "parallel")]` impl block (rayon `scalar_mul` / `matrix_mul` / `vector_mul` / `Add` / `Sub` / `*Assign`) — **compiled by CI, never executed by any test** |
| `algebra/src/matrix/vector.rs` | 68.8% | 160–291 | same: the parallel operator kernels |
| `zk/src/sumcheck/mod.rs` | 65.9% | 205–264 | `prove_rayon` (the parallel sumcheck prover) has **no test at all** |
| `pqc/src/falcon/fpr.rs` | 73.5% | 486–584 | `fpr_add_trace` and friends, self-labelled *"Debug helper (test-only)"* — dead scaffolding, not a coverage hole |
| `algebra/src/ntt/ntt_core.rs` | 86.7% | 316–342 | `pointwise_mul` is public and never called |
| `algebra/src/ring/poly_ring.rs` | 83.2% | 445–466 | `Mul<&PolyRing>` ref-form operators + the `n == 0` / non-power-of-two arms |
| `algebra/src/ntt/twiddle.rs` | 72.0% | 85–112 | `stage_twiddles_ct` / `stage_twiddles_gs` accessors never called |
| `algebra/src/crypto/sampling.rs` | 94.5% | 164–172, 234–240 | `sample_rej_bounded_coeffs` never called |
| `pqc/src/error.rs` | 41.7% | 40–52 | `Display for InvalidInput` — the error *messages* are never asserted |
| `zk/src/commitment/key.rs` | 75.5% | 58–68 | the `#[cfg(feature = "parallel")]` branch of `mul_vec` — i.e. the rayon path through the Ajtai commitment multiply |

Read of the table: the uncovered mass is mostly **one thing** — the `parallel`
feature's kernels (`matrix.rs` / `vector.rs` operator blocks,
`sumcheck::prove_rayon`, `commitment::key::mul_vec`). CI compiles
`--all-features`, so those lines build, but no test ever *executes* a rayon path:
the roadmap's gate-level speedup claims therefore rest on code the merge gate
never runs. The remainder is public API without callers (`pointwise_mul`,
`stage_twiddles_*`, `sample_rej_bounded_coeffs`), unasserted `Display` text, and
`fpr_*_trace` debug scaffolding. Set the floor (`make coverage-gate FLOOR=…`)
only after the parallel kernels are covered, or the number will mostly report
how much dead scaffolding is left in tree.

- **`cfg`-exclusive arms are invisible to a single run.** Where a backend is
  selected by `#[cfg(feature = "parallel")]` / `#[cfg(not(feature = "parallel"))]`
  (e.g. `zk/src/folding/latticefold.rs:221` vs `:228`), the other arm is not
  compiled at all — so an `--all-features` percentage is only comparable with
  runs of the *same* feature set, and each backend needs its own run
  (`cargo llvm-cov --workspace` vs `--all-features`) before any trend is real.



## Project

- [Contributing](CONTRIBUTING.md) — workflow, merge gate, conventions
- [Security policy](SECURITY.md) — disclosure; claims register in the docs
- [Changelog](CHANGELOG.md) — generated with git-cliff from conventional commits
- [Research notes](docs/research/README.md) — internal study of what is still
  missing before `crates/algebra` can act as the shared algebra base service:
  requirements with acceptance criteria, the peer comparison (crates.io/GitHub
  figures measured 2026-09-19) and the gap scorecard with the P0 list
- License: Apache-2.0 ([LICENSE](LICENSE))

## Contributing

Contributions are welcome! Please read [CONTRIBUTING.md](CONTRIBUTING.md) for the workflow and open a Pull Request. For major changes, please open an issue first to discuss what you would like to change.

## License

- Apache License, Version 2.0 ([LICENSE](LICENSE) or http://www.apache.org/licenses/LICENSE-2.0)

## Acknowledgements

This project is inspired by various lattice-based cryptography implementations:
- [rustfft](https://github.com/ejmahler/RustFFT)
- [condor-rs](https://github.com/nethermindeth/condor-rs)
- [Lazarus](https://github.com/lattice-complete/Lazarus)
- [latticefold](https://github.com/NethermindEth/latticefold)
- [larkworks](https://github.com/zhenfeizhang/larkworks)
