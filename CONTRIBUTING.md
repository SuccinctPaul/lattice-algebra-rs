# Contributing

Thanks for considering a contribution. This document describes how the
repository is organized, what the merge gates are, and the conventions that
keep the docs and the code in lockstep.

## Repository layout

```
crates/algebra   # L0-L4 foundation: ring / ntt / poly / module / crypto / matrix
crates/pqc       # NIST schemes: ML-DSA (FIPS 204)
crates/zk        # ZK line: Ajtai commitments, Sigma, batched opening, sumcheck, IPA, folding
src/             # facade crate re-exporting everything under historical paths
examples/        # workspace tour through the facade (runnable)
docs/            # the design site (vocs + mermaid) — part of the deliverable, not an afterthought
```

Dependency direction is one-way: `pqc` and `zk` depend on `algebra`; nothing
inside `algebra` depends on a scheme crate. New code lands in the module that
owns it (see the [module map](./docs/src/pages/design/module-map.mdx)).

## The merge gate

A PR is mergeable when this passes locally — CI runs the same:

```sh
make gate
# equivalent to:
#   cargo fmt --all --check
#   cargo clippy --workspace --all-targets --no-deps -- --deny warnings
#   cargo test --workspace
```

Benchmarks compile in CI but do not run; if you touch a hot path, run
`make bench` and quote before/after numbers in the PR.

## Conventions

- **English only** for docs, comments and commit messages.
- **KAT-first where applicable**: freeze vectors, then implement
  (red → green). Until official vectors land, differential tests against
  reference bit formulas are the standard (see `crypto::sampling`).
- **XOF-driven determinism**: samplers and derivations take a seed + domain
  label, never a bare RNG. If your API needs randomness, it takes bytes.
- **Docs same-day**: a new public trait/function updates the relevant design
  page and the [trait map](./docs/src/pages/reference/trait-map.mdx) in the
  same PR. The quickstart snippets are guarded by `doc_snippet_check.rs`
  tests — if you rename what they use, update the docs page too.
- **No `unsafe`** in any workspace crate.
- **No new dependencies in `crates/algebra`** without discussion
  (`rand`, `rustfft`, `serde`, `sha3` are the ceiling).
- Commit messages follow the
  [conventional commits](https://www.conventionalcommits.org/) style
  (git-cliff groups them into the CHANGELOG).

## Docs site

```sh
make docs-dev   # live-reload server
make docs       # production build
```

The site is part of review: stale claims are bugs. If your change makes a
page false, fixing the page is part of your change.

## Reporting issues

Open a GitHub issue with a minimal reproducer (a failing test is best).
Security-relevant reports: see [SECURITY.md](SECURITY.md) and the
[security status](./docs/src/pages/introduction/security-status.mdx) page
for what is in scope.
