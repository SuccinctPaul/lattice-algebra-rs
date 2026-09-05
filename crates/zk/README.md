# lattice-zk

Lattice-based zkSNARK building blocks on the
[`lattice-algebra`](../algebra) foundation — the LaBRADOR / GreyHound /
LatticeFold design line, in library form. Transparent proofs of knowledge
over Ajtai/SIS commitments in two rings: `R_q = Z_q[X]/(X^256+1)` (Dilithium
modulus) and `Z_{2^32}[X]/(X^64+1)` (raw 32-bit coefficients for folding).

## Protocol stack

| Module | Milestone | What it provides |
| --- | --- | --- |
| `commitment` | Z1 | Ajtai/SIS commitments `C = A·s` with short `s` (binding from Module-SIS), `LatticeCommitment` trait, `ExpandA` commitment keys |
| `sigma` | Z1 | Lyubashevsky approximate-knowledge Σ-protocol: FS-NIZK with rejection-sampled responses, forking extractor, HVZK |
| `z2_ring` | Z2 | The `Z_{2^32}` ring instance: raw-coefficient expansion, power-of-two Barrett fast path, toy-R1CS generator (squaring gates, ring Newton inverse) |
| `z2` | Z2 | LaBRADOR-style batched opening: binding link + masked constraint consistency, gadget split with provable slack (≈ 3 KB proofs for 10⁴ ring constraints) |
| `sumcheck` | Z3 | Multilinear sumcheck over any commutative ring, transcript-bound challenges |
| `ipa` | Z3 | Gadget-IPA: inner-product arguments on Ajtai-committed vectors, approximate opening mode |
| `fold` | Z4 | Nova-style folding / IVC: relaxed R1CS instances, homomorphic commitment updates, cross-term absorption, folding verifier |

Zero-knowledge status: Z1 is honest-verifier ZK (rejection sampling); Z2/Z3
are transparent like LaBRADOR. Full ZK via blinding is deferred — see the
roadmap.

## Usage

```rust
use zk::protocols::z2::{prove, verify, Z2CommitKey};
use zk::protocols::z2_ring::gen_toy_instance;

fn seed32(tag: &[u8]) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..tag.len()].copy_from_slice(tag);
    s
}

let (r1cs, z) = gen_toy_instance(&seed32(b"toy-instance"), 512, 2);
assert!(r1cs.is_satisfied(&z));

let key_seed = seed32(b"commit-key");
let key = Z2CommitKey::setup(&key_seed);
let (c, proof) = prove(&key, &key_seed, &seed32(b"r1cs-domain"), &r1cs, &z, &[9u8; 32]);

assert!(verify(&key, &key_seed, &seed32(b"r1cs-domain"), &r1cs, &c, &proof));
```

More in [`examples/`](examples): a Σ-protocol NIZK and a folding/IVC chain.

## Development

```sh
cargo test -p lattice-zk                # unit tests (extractors, tamper, sizes)
cargo test -p lattice-zk --test protocol_contract
cargo run  -p lattice-zk --example sigma_nizk
cargo bench -p lattice-zk               # criterion: sigma, batched opening, sumcheck, fold
```
