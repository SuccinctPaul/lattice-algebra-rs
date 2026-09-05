//! A Fiat–Shamir NIZK of knowledge of a short preimage of an Ajtai/SIS
//! commitment (Z1): the Lyubashevsky Σ-protocol with rejection sampling.
//!
//! Statement: prove knowledge of `s` with `‖s‖∞ ≤ B_S` such that
//! `t = A·s` in `R_q^{K}` — the exact relation Ajtai commitments are
//! built on.
//!
//! Run with: `cargo run -p lattice-zk --example sigma_nizk`

use algebra::module::ModuleVector;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use zk::protocols::commitment::{CommitmentKey, LatticeCommitment, Z1Instance, RING_DIM};
use zk::protocols::sigma::{fs_prove, fs_verify};

type Z1Ring = Zq<8380417>;
const K: usize = 4;
const L: usize = 3;

fn seed32(tag: &[u8]) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..tag.len()].copy_from_slice(tag);
    s
}

fn main() {
    // Setup: the commitment key A ∈ R_q^{K×L}, expanded from a seed.
    let key: CommitmentKey<Z1Instance, K, L, RING_DIM> =
        CommitmentKey::setup(&seed32(b"sigma-example-key"));

    // Witness: a short secret s (coefficients in [-4, 4]).
    let s: ModuleVector<Z1Ring, L, RING_DIM> = ModuleVector::from_fn(|i| {
        PolyRing::from_coefficients(
            (0..RING_DIM)
                .map(|j| {
                    Z1Ring::new((((i as i64) * 3 + j as i64) % 9 - 4).rem_euclid(8_380_417) as u64)
                })
                .collect(),
        )
    });

    // Statement: t = A·s.
    let t = key.commit(&s);
    println!(
        "committed t = A·s  ({} polynomials of R_q, n={})",
        K, RING_DIM
    );

    // Prove in zero knowledge (HVZK): one FS challenge from a seed.
    let proof = fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s, &t, &seed32(b"sigma-coins"))
        .expect("honest witness must pass the rejection loop");
    println!("fs_prove: acceptance (rejection-sampled response ‖z‖∞ ≤ B_Z)");

    let ok = fs_verify::<Z1Instance, K, L, RING_DIM>(&key, &t, &proof);
    println!("fs_verify(t, proof) = {ok}");
    assert!(ok);

    // A proof for a different statement does not verify.
    let s_switched: ModuleVector<Z1Ring, L, RING_DIM> = ModuleVector::from_fn(|i| {
        if i == 0 {
            PolyRing::from_coefficients(vec![Z1Ring::new(3); RING_DIM])
        } else {
            s.polys()[i].clone()
        }
    });
    let t_wrong = key.commit(&s_switched);
    let ok_wrong = fs_verify::<Z1Instance, K, L, RING_DIM>(&key, &t_wrong, &proof);
    println!("fs_verify(t', same proof) = {ok_wrong}  (must be false)");
    assert!(!ok_wrong);

    println!("\nThe same machinery, keyed differently, underlies the batched");
    println!("opening and folding layers — see protocols::z2 and protocols::fold.");
}
