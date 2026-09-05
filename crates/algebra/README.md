# lattice-algebra

The L0–L4 algebraic foundation of the [lattice-algebra-rs](https://github.com/SuccinctPaul/lattice-algebra-rs)
workspace: one shared substrate from which the PQC schemes ([`lattice-pqc`](../pqc))
and the zkSNARK line ([`lattice-zk`](../zk)) are both derived.

## Layers

| Layer | Module | Contents |
| --- | --- | --- |
| L0 | `ring` | `Zq` scalar ring, `PolyRing` negacyclic quotient ring, capability traits `Ring` / `Field` / `TwoAdicRing` / `CenteredRing` / `PolynomialQuotientRing`, Barrett reduction, const-time number theory, uniform sampling glue |
| L1 | `ntt` | Cooley–Tukey / Gentleman–Sande transforms, negacyclic NTT for `Z_q[X]/(X^N+1)`, precomputed twiddles, `NttDomain` views |
| L2 | `poly` | `UniPolynomial` (NTT / FFT / schoolbook multiplication) and `SparsePolynomial` challenge polynomials |
| L3 | `module` | `ModuleVector` / `ModuleMatrix` (+ NTT-domain twins), seed expansion (`ExpandA`), infinity norms, FIPS-exact `power2round` / `decompose` / hints |
| L4 | `crypto` | Streaming SHAKE `Xof`, `Transcript`, reference-exact samplers (uniform / RejBounded / CBD / SampleInBall / NTT-domain), `DiscreteGaussian`, bit packing |
| — | `matrix` | Legacy generic matrix/vector containers (superseded by `module` for scheme work) |

Every scheme-facing primitive is **XOF-driven and deterministic**: samplers and
derivations take a domain-separated stream, never a bare RNG, so KATs and
reproducible signing work out of the box.

## Usage

```rust
use algebra::crypto::sampling::{sample_cbd, BitStream};
use algebra::crypto::xof::Shake256Xof;
use algebra::module::ModuleMatrixNtt;
use algebra::ntt::NttOperatorOptimized;
use algebra::poly::UniPolynomial;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::zq::Zq;

type ZqD = Zq<8380417>;

// Negacyclic multiplication in R_q via NTT.
let a = PolyRing::<ZqD, 256>::from_coefficients(vec![ZqD::new(1); 256]);
let b = PolyRing::<ZqD, 256>::from_coefficients(vec![ZqD::new(2); 256]);
let _c = a.clone() * b.clone();

// Deterministic CBD sampling from an XOF stream.
let mut xof = Shake256Xof::new(b"domain");
let mut stream = BitStream::new(&mut xof);
let _noise = sample_cbd::<ZqD>(&mut stream, 2);
```

More in [`examples/`](examples): ring & NTT basics, module-lattice arithmetic,
and a sampler tour with histograms.

## Development

```sh
cargo test -p lattice-algebra          # 398+ unit tests, incl. 15-moduli axioms
cargo test -p lattice-algebra --test algebra_integration
cargo run  -p lattice-algebra --example samplers
cargo bench -p lattice-algebra         # criterion: poly mul, matvec, samplers, XOF
```
