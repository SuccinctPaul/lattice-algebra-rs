# lattice-pqc

NIST post-quantum schemes built directly on the
[`lattice-algebra`](../algebra) foundation — no bespoke arithmetic, every
scheme reuses the same rings, NTT and samplers.

## Implemented

- **ML-KEM (FIPS 203)** — `mlkem` module:
  - all three parameter sets (`MlKem512` / `MlKem768` / `MlKem1024`), bound
    through zero-cost per-set APIs (`mlkem_512` / `mlkem_768` / `mlkem_1024`);
  - `keygen(d, z)`, `encapsulate(ek, m)`, `decapsulate(dk, ct)` with the
    spec's implicit-rejection semantics and the augmented decapsulation-key
    format (`dk_PKE ‖ ek ‖ H(ek) ‖ z`);
  - the spec's seven-layer NTT with `BaseCaseMultiply` pair products
    (`q = 3329` has 2-adicity 7 — the generic engine cannot serve this
    scheme);
  - the optional `EncapsulationKeyCheck` / `DecapsulationKeyCheck` (length,
    modulus, hash consistency) in `from_bytes`;
  - byte-exact with the official ACVP vectors (183 cases: keyGen,
    encapsulation, decapsulation incl. implicit rejection, key checks).
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

```rust
use pqc::mlkem::mlkem_768;

let (d, z) = ([1u8; 32], [2u8; 32]);
let (dk, ek) = mlkem_768::keygen(&d, &z);

let m = [3u8; 32]; // fresh uniform randomness per encapsulation
let (ciphertext, ss) = mlkem_768::encapsulate(&ek, &m);
assert_eq!(mlkem_768::decapsulate(&dk, &ciphertext).as_bytes(), ss.as_bytes());
```

Keys serialize canonically: `SigningKey::to_bytes` / `from_bytes`,
`VerifyingKey::to_bytes` / `from_bytes` (FIPS 204 `skEncode` / `pkEncode`),
and `DecapsulationKey::to_bytes` / `from_bytes`,
`EncapsulationKey::to_bytes` / `from_bytes` (FIPS 203 `dkEncode` / `ekEncode`
with the §7 key checks).

See [`examples/sign_verify.rs`](examples/sign_verify.rs) and
[`examples/kem.rs`](examples/kem.rs) for runnable tours across all three
parameter sets.

## Development

```sh
cargo test -p lattice-pqc               # unit tests (roundtrips, tamper, sizes)
cargo test -p lattice-pqc --test scheme_contract
cargo run  -p lattice-pqc --example sign_verify
cargo run  -p lattice-pqc --example kem
cargo bench -p lattice-pqc              # criterion: keygen / sign / verify / encaps / decaps
```

KAT/ACVP vector alignment: ML-DSA (pure mode, 126 vectors) and ML-KEM
(183 vectors) match the official NIST ACVP sample vectors byte-for-byte —
see `tests/data/README.md` for provenance.
