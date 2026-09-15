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
| `lattice-zk` | [`crates/zk`](crates/zk) | Lattice zkSNARK building blocks: Ajtai/SIS commitments, Lyubashevsky Σ-protocols, batch opening, ring-sumcheck, gadget IPA, Nova-style folding / IVC |

## Usage

Depend on the crates you need (lib names: `algebra`, `pqc`, `zk`):

```toml
[dependencies]
lattice-algebra = "0.1.0"   # use algebra::ring::...
lattice-pqc     = "0.1.0"   # use pqc::mldsa::...
lattice-zk      = "0.1.0"   # use zk::protocols::...
```

```rust
use algebra::module::ModuleVector;
use pqc::mldsa::{MlDsa65, MlDsaParams};
use zk::protocols::commitment::CommitmentKey;
```

## Requirements

- Rust 1.85.0 or later (MSRV, verified in CI)
- Runtime dependencies of the foundation: `rand`, `rustfft`, `serde`, `sha3`

## Development

```sh
cargo test --workspace        # 542 tests (unit + integration + doc)
cargo clippy --workspace --all-targets -- -D warnings
cargo fmt --all --check
cargo bench --workspace       # criterion: foundation, ML-DSA, Falcon, Z1-Z4 protocols
```

Each crate carries its own `README.md` (see `crates/<name>/README.md`),
runnable `examples/`, integration tests in `crates/<name>/tests/`, and
criterion benchmarks in `crates/<name>/benches/`.

## Project

- [Contributing](CONTRIBUTING.md) — workflow, merge gate, conventions
- [Security policy](SECURITY.md) — disclosure; claims register in the docs
- [Changelog](CHANGELOG.md) — generated with git-cliff from conventional commits
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
