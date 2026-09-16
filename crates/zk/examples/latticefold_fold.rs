//! LatticeFold-style folding: fold two committed witnesses, decompose the
//! result into balanced b-bit digits and answer the splitting query.
//!
//! Run with: `cargo run -p lattice-zk --example latticefold_fold`

use zk::folding::latticefold::{
    decompose_balanced, prove_fold_decompose, verify_fold_decompose, LfKey,
};
use zk::foundation::encoding::ring_from_u32;
use zk::instance::ring::{Z2Ring, D};

fn main() {
    const N: usize = 8;
    const M: usize = 4;

    let key = LfKey::<N, M>::setup(&[11u8; 32]);

    // two small witnesses (16-bit coefficients)
    let w = |seed: u8| -> Vec<Z2Ring> {
        (0..M)
            .map(|j| {
                ring_from_u32(&{
                    let mut c = [0u32; D];
                    c[j * 5 % D] = 0x0001_0000 + u32::from(seed) + j as u32;
                    c
                })
            })
            .collect()
    };
    let (w1, w2) = (w(1), w(2));

    // fold + decompose + splitting query, all challenges FS-derived
    let (c1, c2, proof) = prove_fold_decompose::<N, M>(&key, &[11u8; 32], &w1, &w2, 48, 48);
    println!(
        "folded commitment: {} rows; digit commitments: {} × {}; batched opening: {} elements",
        proof.c_prime.len(),
        proof.digit_comms.len(),
        proof.digit_comms[0].len(),
        proof.d_tilde.len()
    );
    assert!(verify_fold_decompose::<N, M>(
        &key,
        &[11u8; 32],
        &c1,
        &c2,
        48,
        48,
        &proof
    ));
    println!("recursive verification: true");

    // the decomposition itself is exact and quotient-free in Z_{2^32}
    let digits = decompose_balanced::<M>(&w1);
    println!(
        "decomposition: {} digits, every digit ‖·‖∞ ≤ {}",
        digits.len(),
        1 << (zk::folding::latticefold::DIGIT_BITS - 1)
    );
    assert_eq!(digits.len(), 4);
}
