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

##@ Release
.PHONY: changelog
changelog: # Regenerate CHANGELOG.md with git-cliff (cargo install git-cliff).
	@git cliff -o CHANGELOG.md

.PHONY: clean
clean: # Remove build artifacts.
	@cargo clean
