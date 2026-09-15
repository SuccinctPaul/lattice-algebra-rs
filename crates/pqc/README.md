# lattice-pqc

NIST post-quantum schemes built on the [`lattice-algebra`](../algebra)
foundation — ML-KEM and ML-DSA flow through the foundation's rings, norms,
codecs and streaming-XOF/sampling layer, each with its spec-exact NTT
convention in its own sub-module (`mlkem::ntt`, `mldsa::ntt`), while Falcon
ships as a verbatim port of the round-3 reference implementation
(self-contained `falcon` sub-modules). The round-3 lattice alternates —
FrodoKEM, NTRU and Streamlined NTRU Prime — are likewise verbatim ports of
their submissions' reference implementations (self-contained `frodo`,
`ntru` and `sntrup` sub-modules), each byte-exact with the official
round-3 submission KAT vectors.

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
- **Falcon (round-3 specification, 2020-10-01 — the basis of the FIPS 206
  FN-DSA draft)** — `falcon` module:
  - both parameter sets (`Falcon-512` / `Falcon-1024`), bound through
    zero-cost per-set APIs (`falcon512` / `falcon1024`);
  - `keygen(seed)`, `sign(sk, msg, nonce, sig_seed)` and
    `verify(pk, msg, nonce, esig)` — `verify` mirrors `sign`, taking the
    same message / 40-byte-nonce split, so callers never pre-concatenate
    `nonce ‖ message`;
  - verbatim port of the reference implementation: integer soft-float `fpr`
    (bit-exact with the C `fpr.c`, differentially tested over 13 000 random
    operand cases), complex FFT, mod-q NTT (Montgomery), the recursive
    NTRU-solver chain with Babai reduction, the ChaCha20 sampler with the
    AVX2-interleaved output layout, LDL-tree FFT signing and the
    compressed-signature codecs;
  - canonical key serialization (`to_bytes` / `from_bytes` with
    length/modulus checks);
  - byte-exact with the official round-3 submission KAT vectors.

- **FrodoKEM (round-3 specification, 2020-09-30)** — `frodo` module:
  - all three parameter sets (FrodoKEM-640/976/1344), each in the two
    variants defined by the submission for generating the public matrix
    `A` — AES128 (the submitted default, `frodo640`/`frodo976`/`frodo1344`)
    and SHAKE128 (`frodo640_shake`/…);
  - `keygen(s, seedSE, z)`, `encapsulate(ek, mu)`, `decapsulate(dk, ct)`
    with implicit rejection;
  - a minimal AES-128 block cipher (FIPS-197, validated against the
    appendix vectors) for the `A` expansion — no external crypto deps;
  - the submission's per-set XOF (`SHAKE128` for 640, `SHAKE256` for
    976/1344) and CDF tables, `u16`-wrapping matrix arithmetic with the
    reference's transposed sampling layout;
  - byte-exact with the official round-3 submission KAT vectors (both
    variants).
- **NTRU (round-3 specification, 2020-10-16)** — `ntru` module:
  - all five round-3 parameter sets: ntruhps2048677, ntruhps2048821,
    ntruhps4096821, ntruhps40961229 and ntruhrss701, bound through
    zero-cost per-set APIs;
  - `keygen(seed, prf_key)`, `encapsulate(pk, rm_seed)`,
    `decapsulate(sk, ct)` with implicit rejection through the 32-byte PRF
    key (`SHA3-256(PRF ‖ ct)`);
  - the almost-inverse `R2`/`S3`/`Rq` polynomial inversions, the HRSS
    `x−1` lift, fixed-weight sampling via the supercop
    `crypto_sort_int32` network, and the submission's ternary/mod-q packers;
  - byte-exact with the official round-3 submission KAT vectors for
    ntruhps2048677 / ntruhps4096821 / ntruhrss701 (the official KAT
    directory covers those three sets; hps2048821 and hps40961229 share
    the same code path and are covered by round-trip tests).
- **Streamlined NTRU Prime (round-3 submission, ntruprime-20201007)** —
  `sntrup` module:
  - all six sizes (sntrup653/761/857/953/1013/1277 — sntrup761 is the
    instance deployed in OpenSSH), bound through zero-cost per-set APIs;
  - `keygen(g_random, f_random, rho)`, `encapsulate(pk, r_random)`,
    `decapsulate(sk, ct)` with implicit rejection via the stored `rho`
    and the `HashSession(1 + mask)` domain split;
  - the mixed-radix `Encode`/`Decode` ciphertext/key compressor, the
    branchless `crypto_sort_uint32`-driven `Short_fromlist` sampler, the
    constant-time `R3_recip`/`Rq_recip3` extended GCDs, and SHA-512-based
    `HashConfirm`/`HashSession`;
  - byte-exact with the official round-3 submission KAT vectors for
    sntrup761 / sntrup857 / sntrup953 / sntrup1277 (the submission ships
    no official KAT files for the 653 and 1013 sizes; those share the
    same code path and are covered by round-trip tests). The companion
    NTRU-LPRime (`ntrulpr`) variant is not implemented.

## Status: FIPS 206 (FN-DSA) tracking

FIPS 206 (FN-DSA) is still a draft — its initial public draft has not been
published and the Falcon parameter sets may shift before the freeze
(expected late 2026 / early 2027). The `falcon` module anchors to the
round-3 specification and its official KAT vectors (roadmap milestone M5,
complete), but **there is no stable release of the Falcon API before the
FIPS 206 freeze**: the parameter sets and the API surface may still change
with the draft.

## Planned

- FN-DSA migration: track the FIPS 206 draft toward its freeze and adapt
  parameters/APIs as the standard solidifies.

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
use pqc::falcon::falcon512;

let seed = [7u8; 48]; // keygen entropy
let (sk, pk) = falcon512::keygen(&seed);

let nonce = [0u8; 40]; // fresh uniform randomness per signature
let sig_seed = [1u8; 48];
let msg = b"hello lattice world";
let esig = falcon512::sign(&sk, msg, &nonce, &sig_seed);

// verify takes the same (msg, nonce) split as sign — no pre-concatenation.
assert!(falcon512::verify(&pk, msg, &nonce, &esig));
assert!(!falcon512::verify(&pk, b"tampered", &nonce, &esig));
```

```rust
use pqc::mlkem::mlkem_768;

let (d, z) = ([1u8; 32], [2u8; 32]);
let (dk, ek) = mlkem_768::keygen(&d, &z);

let m = [3u8; 32]; // fresh uniform randomness per encapsulation
let (ciphertext, ss) = mlkem_768::encapsulate(&ek, &m);
assert_eq!(mlkem_768::decapsulate(&dk, &ciphertext).as_bytes(), ss.as_bytes());
```

```rust,ignore
// FrodoKEM, NTRU and Streamlined NTRU Prime follow the same pattern —
// explicit randomness exactly as the submissions' reference
// implementations draw it (see each module's docs for the shapes):
use pqc::frodo::frodo976;
let (sk, ek) = frodo976::keygen(&s, &seed_se, &z);      // s/seedSE: 24B, z: 16B
let (ct, ss) = frodo976::encapsulate(&ek, &mu);          // mu: 24B fresh uniform
assert_eq!(frodo976::decapsulate(&sk, &ct).as_bytes(), ss.as_bytes());

use pqc::ntru::ntruhrss701;
let (sk, pk) = ntruhrss701::keygen(&seed, &prf_key);     // seed: 1400B, prf_key: 32B
let (ct, ss) = ntruhrss701::encapsulate(&pk, &rm_seed);  // rm_seed: 1400B
```

Keys serialize canonically: `SigningKey::to_bytes` / `from_bytes`,
`VerifyingKey::to_bytes` / `from_bytes` (FIPS 204 `skEncode` / `pkEncode`),
and `DecapsulationKey::to_bytes` / `from_bytes`,
`EncapsulationKey::to_bytes` / `from_bytes` (FIPS 203 `dkEncode` / `ekEncode`
with the §7 key checks).

See [`examples/sign_verify.rs`](examples/sign_verify.rs),
[`examples/sign_falcon.rs`](examples/sign_falcon.rs) and
[`examples/kem.rs`](examples/kem.rs) for runnable tours across all three
parameter sets (ML-DSA, Falcon) and the KEM line.

## Development

```sh
cargo test -p lattice-pqc               # unit tests (roundtrips, tamper, sizes)
cargo test -p lattice-pqc --test scheme_contract
cargo test -p lattice-pqc --test falcon_kat
cargo test -p lattice-pqc --test frodo_kat
cargo test -p lattice-pqc --test ntru_kat
cargo test -p lattice-pqc --test sntrup_kat
cargo run  -p lattice-pqc --example sign_verify
cargo run  -p lattice-pqc --example sign_falcon
cargo run  -p lattice-pqc --example kem
cargo bench -p lattice-pqc              # criterion: keygen / sign / verify / encaps / decaps
```

KAT/ACVP vector alignment: ML-DSA (279 vectors across pure, internal-mu
and preHash modes) and ML-KEM
(183 vectors) match the official NIST ACVP sample vectors byte-for-byte,
Falcon matches the official round-3 submission KAT vectors (10
keygen/sign/verify bundles), FrodoKEM matches the official round-3
submission KAT vectors (18 bundles across 640/976/1344 × AES/SHAKE), NTRU
matches the official round-3 submission KAT vectors (9 bundles across
hps2048677/4096821/hrss701), and Streamlined NTRU Prime matches the
official round-3 submission KAT vectors (12 bundles across
761/857/953/1277) — see `tests/data/README.md` for provenance.
