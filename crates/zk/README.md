# lattice-zk

Lattice-based zkSNARK building blocks on the
[`lattice-algebra`](../algebra) foundation — the LaBRADOR / GreyHound /
LatticeFold design line, in library form. Transparent proofs of knowledge
over Ajtai/SIS commitments in two rings: `R_q = Z_q[X]/(X^256+1)` (Dilithium
modulus) and `Z_{2^32}[X]/(X^64+1)` (raw 32-bit coefficients for folding).

## Protocol stack

The crate is organized by **domain** — each top-level module is one domain,
layered strictly `foundation → instance → commitment → protocol domains`:

| Domain | Milestone | What it provides |
| --- | --- | --- |
| `foundation::sampling` | utils | Protocol-level samplers, generic over the ring: uniform expansion (masked rejection; raw at `q = 2^32`), centered-bounded / CBD masks, `SampleInBall` sparse challenges, non-unit linear challenges `C = X − a` (a odd), LaBRADOR hyperball challenge vectors (`‖β‖∞ ≤ b`, `‖β‖₁ ≤ B`), seed-driven vectors & matrices — all XOF-driven |
| `foundation::fs` | utils | Fiat–Shamir derivation: transcript absorption of ring vectors, domain-separated seed re-expansion |
| `foundation::encoding` | utils | Canonical ring ↔ little-endian `u32`/bytes wire encoding shared by transcripts and proof serialization |
| `instance::ring` | Z2 | The `Z_{2^32}` ring instance: ring helpers, norms, power-of-two constants, Newton inverse |
| `instance::r1cs` | Z2 | Toy-R1CS layer: squaring gates, generator, parallel gate traversal |
| `commitment::key` | — | The single Ajtai commitment key over the Z2 ring (every Z2-ring protocol commits through it) |
| `commitment::ajtai` | Z1 | Ajtai/SIS commitments `C = A·s` with short `s` (binding from Module-SIS), `LatticeCommitment` trait, `ExpandA` commitment keys |
| `sigma` | Z1 | Lyubashevsky approximate-knowledge Σ-protocol: FS-NIZK with rejection-sampled responses, forking extractor, HVZK |
| `opening` | Z2 | LaBRADOR-style batched opening: binding link + masked constraint consistency (≈ 3 KB proofs for 10⁴ ring constraints) |
| `sumcheck` | Z3 | Multilinear sumcheck over any commutative ring, transcript-bound challenges |
| `sumcheck::ipa` | Z3 | Gadget-IPA: inner-product arguments on Ajtai-committed vectors, approximate opening mode |
| `shortness::balanced` | Z5 | Digit-based projection argument (approximate shortness, the LaBRADOR `z = z₀ + b·z₁` / LNP22 decomposition flavor): exact balanced `2^γ` split of `v = w − ζ·t`, digit gates + exact commitment link certify `‖v‖∞ ≤ 2^γ·B_h + 2^{γ−1}` |
| `shortness::gadget` | Z2 | Gadget split + approximate linear check with provable slack |
| `folding::nova` | Z4 | Nova-style folding / IVC: relaxed R1CS instances, homomorphic commitment updates, cross-term absorption, folding verifier |
| `folding::latticefold` | Z5 | LatticeFold-style folding: small-norm fold challenge, exact quotient-free `b`-bit balanced decomposition of the folded vector, homomorphic digit commitments, splitting-query batched opening with a provable norm gate |

A survey mapping these primitives to the schemes that use them (LaBRADOR,
Greyhound, LatticeFold/+, LaZer, Rinocchio, …) lives in
[`docs/survey-lattice-zksnarks.zh.md`](docs/survey-lattice-zksnarks.zh.md).

Zero-knowledge status: Z1 is honest-verifier ZK (rejection sampling); Z2/Z3
are transparent like LaBRADOR. Full ZK via blinding is deferred — see the
roadmap.

## Usage

```rust
use zk::instance::r1cs::gen_toy_instance;
use zk::opening::{prove, verify, Z2CommitKey};

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
