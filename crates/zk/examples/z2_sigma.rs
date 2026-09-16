//! Blinded HVZK Σ-response over the Z2 ring: prove knowledge of a short
//! opening of an Ajtai commitment without revealing it.
//!
//! Run with: `cargo run -p lattice-zk --example z2_sigma`

use zk::commitment::key::AjtaiKey;
use zk::foundation::encoding::{ring_from_u32, ring_to_u32};
use zk::instance::ring::{Z2Ring, D};
use zk::sigma::z2::{prove, verify};

fn main() {
    const N: usize = 8;
    const M: usize = 4;

    // Ajtai commitment key and a small secret witness (‖w‖∞ ≤ 4 ≤ B_W)
    let key_seed = [1u8; 32];
    let key = AjtaiKey::<N, M>::setup(&key_seed);
    let w: Vec<Z2Ring> = (0..M)
        .map(|j| {
            ring_from_u32(&{
                let mut c = [0u32; D];
                c[j * 7 % D] = (1 + j) as u32;
                c
            })
        })
        .collect();
    let c = key.mul_vec(&w);

    // the HVZK proof: rejection-sampled masked response, witness hidden
    let proof = prove(&key, &key_seed, &w, &c, &[9u8; 32]).expect("honest prove");
    println!(
        "proof: d = {} ring elements, z = {} ring elements (masked response)",
        proof.d.len(),
        proof.z.len()
    );
    assert!(verify(&key, &key_seed, &c, &proof));
    println!("honest proof accepted: true");

    // a different randomness gives a different (d, z) — the response
    // distribution is masked, so transcripts are not linkable
    let other = prove(&key, &key_seed, &w, &c, &[10u8; 32]).unwrap();
    println!("transcripts linkable: {}", proof == other);
    assert_ne!(proof, other);

    // a tampered response breaks the exact linear link
    let mut forged = proof.clone();
    let mut coeffs = ring_to_u32(&forged.z[0]);
    coeffs[0] ^= 1;
    forged.z[0] = ring_from_u32(&coeffs);
    println!(
        "tampered proof accepted: {}",
        verify(&key, &key_seed, &c, &forged)
    );
    assert!(!verify(&key, &key_seed, &c, &forged));
}
