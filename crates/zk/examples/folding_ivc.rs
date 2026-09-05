//! Nova-style folding over the `Z_{2^32}[X]/(X^64+1)` ring (Z4): two relaxed
//! R1CS instances are folded into one — and the result folds again, which is
//! the induction step of incrementally verifiable computation (IVC).
//!
//! Relaxed gate: `(A_k·z)∘(A_k·z) = U_k∘z_sel[k] + e_k`.
//!
//! Run with: `cargo run -p lattice-zk --example folding_ivc`

use zk::protocols::fold::{fold, verify_folded, FoldKey, RelaxedInstance};
use zk::protocols::z2::constraint_residuals;
use zk::protocols::z2_ring::{gen_toy_instance, ring_from_u32, ring_to_u32, ToyR1cs, Z2Ring};

const N: usize = 8; // commitment width
const M: usize = 4; // witness variables
const GATES: usize = 64; // ring constraints

fn seed32(tag: &[u8]) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..tag.len()].copy_from_slice(tag);
    s
}

fn make_relaxed(
    key: &FoldKey<N, M, GATES>,
    r1cs: &ToyR1cs,
    z: &[Z2Ring],
) -> RelaxedInstance<M, GATES> {
    RelaxedInstance {
        z: z.to_vec(),
        error: constraint_residuals(r1cs, z),
        c_z: key.commit_witness(z),
        c_e: key.commit_error(&constraint_residuals(r1cs, z)),
    }
}

fn fold_randomness(a: u32, b: u32) -> Z2Ring {
    let mut coeffs = [0u32; 64];
    coeffs[0] = a;
    coeffs[1] = b;
    ring_from_u32(&coeffs)
}

fn main() {
    let key = FoldKey::<N, M, GATES>::setup(&seed32(b"fold-example-key"));
    let (r1cs, z1) = gen_toy_instance(&seed32(b"fold-example-step1"), GATES, M);
    let (_r2, z2) = gen_toy_instance(&seed32(b"fold-example-step2"), GATES, M);
    let (_r3, z3) = gen_toy_instance(&seed32(b"fold-example-step3"), GATES, M);
    let (_r4, z4) = gen_toy_instance(&seed32(b"fold-example-step4"), GATES, M);

    println!("IVC chain: 4 steps, each a relaxed R1CS instance over the Z_{{2^32}} ring");

    // Step 1 ∥ Step 2 → folded₁₂
    let i1 = make_relaxed(&key, &r1cs, &z1);
    let i2 = make_relaxed(&key, &r1cs, &z2);
    let f12 = fold(
        &key,
        &r1cs,
        &i1,
        &i2,
        fold_randomness(0x1111_1111, 0x2222_2222),
    );
    assert!(verify_folded(&key, &r1cs, &f12));
    println!("fold(i1, i2) → f12        verify_folded = true");

    // The folded instance folds again: this is the IVC induction step.
    let i3 = make_relaxed(&key, &r1cs, &z3);
    let f123 = fold(
        &key,
        &r1cs,
        &f12,
        &i3,
        fold_randomness(0x3333_3333, 0x4444_4444),
    );
    assert!(verify_folded(&key, &r1cs, &f123));
    println!("fold(f12, i3) → f123      verify_folded = true");

    let i4 = make_relaxed(&key, &r1cs, &z4);
    let f1234 = fold(
        &key,
        &r1cs,
        &f123,
        &i4,
        fold_randomness(0x5555_5555, 0x6666_6666),
    );
    assert!(verify_folded(&key, &r1cs, &f1234));
    println!("fold(f123, i4) → f1234    verify_folded = true");

    // The verifier never sees the unfolded history — one folded instance
    // stands for the whole chain. Tampering with it is caught:
    let mut bad = f1234.clone();
    let mut coeffs = ring_to_u32(&bad.z[0]);
    coeffs[0] ^= 1;
    bad.z[0] = ring_from_u32(&coeffs);
    assert!(!verify_folded(&key, &r1cs, &bad));
    println!("verify_folded(tampered f1234) = false");

    println!("\n4 computation steps collapsed into 1 checkable instance.");
}
