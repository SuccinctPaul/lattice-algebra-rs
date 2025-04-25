# lattice-algebra-rs





## Feature Additions:
* Modular arithmetic traits and optimized implementations (e.g., Montgomery, Barrett reduction).
* Polynomial arithmetic (add, mul, NTT, inverse NTT, division, GCD).
* Matrix and vector operations over rings and polynomials.
* Support for cyclotomic rings and ideal lattices.
* Gaussian and uniform sampling utilities.
* Serialization/deserialization for all core types (via serde).
* Error handling with custom error types.
* Optional: SIMD acceleration for core arithmetic (via feature flag).


## Code Organization & Chore:
* Split code into clear modules: arithmetic, poly, matrix, ring, sampling, traits, utils.
* Add documentation comments for all public APIs.
* Add unit and property-based tests (e.g., with proptest).
* Add benchmarks (criterion crate).
* Add CI config (GitHub Actions or similar).
* Add examples and usage docs.


## Cargo.toml Optimizations:
* Add features for optional SIMD, serde, and parallelism.
* Add categories, keywords, and repository metadata.
* Set MSRV (minimum supported Rust version).