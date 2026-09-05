# lattice-pqc

NIST post-quantum schemes built directly on the
[`lattice-algebra`](../algebra) foundation — no bespoke arithmetic, every
scheme reuses the same rings, NTT and samplers.

## Implemented

- **ML-DSA (FIPS 204)** — `mldsa` module:
  - all three parameter sets (`MlDsa44` / `MlDsa65` / `MlDsa87`), bound
    through zero-cost per-set APIs (`mldsa_44` / `mldsa_65` / `mldsa_87`);
  - `keygen` from a 32-byte seed, deterministic **and** randomized signing,
    `verify`;
  - spec-exact encodings (`SimpleBitPack`, `(a,b)`-centered bit packs,
    packed hints), exact signature sizes 2420 / 3309 / 4627 bytes;
  - `ExpandA` runs directly in the NTT domain — the matrix is never
    transformed back.

## Planned

- ML-KEM (FIPS 203) — M4, with official KAT/ACVP vectors.
- FN-DSA / Falcon (FIPS 206) — M5; the `DiscreteGaussian` CDT sampler it
  needs already ships in `lattice-algebra`.

## Usage

```rust
use pqc::mldsa::mldsa_65;

let seed = [42u8; 32]; // ξ
let (sk, vk) = mldsa_65::keygen(&seed);

let ctx = b"";
let msg = b"hello lattice world";
let sigma = mldsa_65::sign_deterministic(&sk, ctx, msg);

assert!(mldsa_65::verify(&vk, ctx, msg, &sigma));
assert!(!mldsa_65::verify(&vk, ctx, b"tampered", &sigma));
```

Keys serialize canonically: `SigningKey::to_bytes` / `from_bytes`,
`VerifyingKey::to_bytes` / `from_bytes` (FIPS 204 `skEncode` / `pkEncode`).

See [`examples/sign_verify.rs`](examples/sign_verify.rs) for a runnable tour
across all three parameter sets.

## Development

```sh
cargo test -p lattice-pqc               # unit tests (roundtrips, tamper, sizes)
cargo test -p lattice-pqc --test scheme_contract
cargo run  -p lattice-pqc --example sign_verify
cargo bench -p lattice-pqc              # criterion: keygen / sign / verify
```

KAT/ACVP vector alignment is a tracked hardening item on the roadmap.
