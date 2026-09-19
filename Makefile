# Developer workflow for the lattice-algebra-rs workspace.
.DEFAULT_GOAL := help

##@ Help
.PHONY: help
help: # Display this help.
	@awk 'BEGIN {FS = ":.*#"; printf "Usage:\n  make \033[34m<target>\033[0m\n"} /^[a-zA-Z_0-9-]+:.*?#/ { printf "  \033[34m%-15s\033[0m %s\n", $$1, $$2 } /^##@/ { printf "\n\033[1m%s\033[0m\n", substr($$0, 5) }' $(MAKEFILE_LIST)

##@ Build
.PHONY: build
build: # Build all workspace crates (debug).
	@cargo build --workspace --all-targets

.PHONY: build-release
build-release: # Build all workspace crates (release).
	@cargo build --workspace --release

##@ Quality gates (CI parity)
.PHONY: test
test: # Run the full test suite (unit + integration + doc).
	@cargo test --workspace

.PHONY: lint
lint: # Run rustfmt check and clippy with warnings denied.
	cargo fmt --all --check
	cargo clippy --workspace --all-targets --no-deps -- --deny warnings

.PHONY: fix
fix: # Apply rustfmt fixes.
	cargo fmt --all

.PHONY: check
check: # Fast typecheck of every target.
	cargo check --workspace --all-targets

.PHONY: gate
gate: # The full merge gate: fmt + clippy + tests (what CI runs).
	cargo fmt --all --check
	cargo clippy --workspace --all-targets --no-deps -- --deny warnings
	cargo test --workspace

##@ Coverage (needs: brew install cargo-llvm-cov)
.PHONY: coverage
coverage: # Line/region coverage table for the whole workspace.
	cargo llvm-cov --workspace --all-features --summary-only

.PHONY: coverage-missing
coverage-missing: # Same run, plus the exact uncovered line numbers per file.
	cargo llvm-cov --workspace --all-features --show-missing-lines

.PHONY: coverage-gate
coverage-gate: # Fail below the line-coverage floor (set FLOOR to adjust).
	cargo llvm-cov --workspace --all-features --summary-only --fail-under-lines $(or $(FLOOR),80)

.PHONY: coverage-html
coverage-html: # Browsable HTML report (target/llvm-cov/html) for one crate.
	cargo llvm-cov -p lattice-algebra --all-features --html

##@ Benchmarks & docs
.PHONY: bench
bench: # Run all criterion benchmarks.
	@cargo bench --workspace

.PHONY: bench-compile
bench-compile: # Compile benchmarks without running them.
	@cargo bench --workspace --no-run

.PHONY: doc
doc: # Build rustdoc for every crate (opens in browser).
	@cargo doc --workspace --no-deps --open

.PHONY: docs
docs: # Build the design site (vocs) into docs/dist.
	cd docs && npm install && npm run build

.PHONY: docs-dev
docs-dev: # Serve the design site with live reload.
	cd docs && npm install && npm run dev

##@ KAT fixtures & audits
.PHONY: kat
kat: # Regenerate all KAT/ACVP fixtures from the official NIST sources, then run the KAT suites.
	bash scripts/regen-kat.sh
	cargo test -p lattice-pqc --test falcon_kat --test frodo_kat --test ntru_kat --test sntrup_kat

.PHONY: kat-check
kat-check: # Run the KAT suites against the committed fixtures (no downloads).
	cargo test -p lattice-pqc --test falcon_kat --test frodo_kat --test ntru_kat --test sntrup_kat

.PHONY: audit
audit: # Supply-chain audit: RustSec advisories, licenses, unsafe-code policy.
	bash scripts/audit.sh

##@ Release
.PHONY: changelog
changelog: # Regenerate CHANGELOG.md with git-cliff (cargo install git-cliff).
	@git cliff -o CHANGELOG.md

.PHONY: clean
clean: # Remove build artifacts.
	@cargo clean
