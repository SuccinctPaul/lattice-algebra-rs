# Lattice Algebra Rust
[![CI](https://github.com/SuccinctPaul/lattice-algebra-rs/workflows/CI/badge.svg)](https://github.com/ejmahler/RustFFT/actions?query=workflow%3ACI)
![minimum rustc 1.70](https://img.shields.io/badge/rustc-1.70+-red.svg)
[![Ask DeepWiki](https://deepwiki.com/badge.svg)](https://deepwiki.com/SuccinctPaul/lattice-algebra-rs)

A high-performance Rust library for lattice-based cryptography and algebra, providing efficient implementations of polynomial rings, matrices, and vector operations over finite fields.

## Features

- **Polynomial Rings**: Efficient implementation of polynomial rings over finite fields
  - FFT-based polynomial multiplication (O(n log n) complexity)
  - Generic polynomial operations (addition, multiplication, division)
  - Support for polynomial rings with degree bounds

- **Matrix Operations**: Generic matrix implementation supporting various element types
  - Basic matrix operations (addition, multiplication, transposition)
  - Matrix-vector operations
  - Efficient storage and computation
  - Support for different matrix types (ring matrices, polynomial matrices)

- **Vector Arithmetic**: Efficient vector operations for cryptographic applications
  - Generic vector implementation with type-safe operations
  - Support for various element types (rings, polynomials)
  - Vector operations (inner product, Hadamard product)
  - Efficient random vector generation

## Requirements

- Rust 1.70.0 or later
- Dependencies:
  - rand = "0.9.1"
  - rustfft = "6.3.0"
  - serde = { version = "1.0.216", features = ["derive"] }

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
lattice-algebra-rs = "0.1.0"
```

Basic example:

```rust
use lattice_algebra_rs::ring::Zq17;
use lattice_algebra_rs::matrix::vector_arithmatic::GenericVector;
use lattice_algebra_rs::poly::UniPolynomial;

// Create a vector over Zq17
let v = GenericVector::new(vec![Zq17::new(1), Zq17::new(2), Zq17::new(3)]);

// Perform vector operations
let a = GenericVector::new(vec![Zq17::new(1), Zq17::new(2)]);
let b = GenericVector::new(vec![Zq17::new(3), Zq17::new(4)]);
let sum = a.clone() + b.clone();
assert_eq!(sum, GenericVector::new(vec![Zq17::new(4), Zq17::new(6)]));
let dot = a.inner_product(&b);
assert_eq!(dot, Zq17::new(11));
```

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request. For major changes, please open an issue first to discuss what you would like to change.

## License
- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)


## Acknowledgements

This project is inspired by various lattice-based cryptography implementations:
- [rustfft](https://github.com/ejmahler/RustFFT)
- [condor-rs](https://github.com/nethermindeth/condor-rs)
- [Lazarus](https://github.com/lattice-complete/Lazarus)
- [latticefold](https://github.com/NethermindEth/latticefold)
- [larkworks](https://github.com/zhenfeizhang/larkworks)
