//! Protocol-level contract tests: each ZK milestone exercised end-to-end
//! through its public API, including the negative cases verifiers must
//! reject.

use algebra::module::ModuleVector;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;
use zk::protocols::commitment::{CommitmentKey, LatticeCommitment, Z1Instance, RING_DIM};
use zk::protocols::fold::{fold, verify_folded, FoldKey, RelaxedInstance};
use zk::protocols::sigma::{fs_prove, fs_verify};
use zk::protocols::sumcheck;
use zk::protocols::z2::{prove, verify, Z2CommitKey};
use zk::protocols::z2_ring::{gen_toy_instance, ring_from_u32, ring_to_u32};

type Z1Ring = Zq<8380417>;
const K: usize = 4;
const L: usize = 3;

fn seed32(tag: &[u8]) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..tag.len()].copy_from_slice(tag);
    s
}

fn sigma_instance() -> (
    CommitmentKey<Z1Instance, K, L, RING_DIM>,
    ModuleVector<Z1Ring, L, RING_DIM>,
    ModuleVector<Z1Ring, K, RING_DIM>,
) {
    let key: CommitmentKey<Z1Instance, K, L, RING_DIM> =
        CommitmentKey::setup(&seed32(b"contract-sigma-key"));
    let s: ModuleVector<Z1Ring, L, RING_DIM> = ModuleVector::from_fn(|i| {
        PolyRing::from_coefficients(
            (0..RING_DIM)
                .map(|j| Z1Ring::new((((i * 3 + j) % 9) - 4).rem_euclid(8_380_417) as u64))
                .collect(),
        )
    });
    let t = key.commit(&s);
    (key, s, t)
}

#[test]
fn sigma_honest_proof_verifies_and_wrong_statement_fails() {
    let (key, s, t) = sigma_instance();
    let proof =
        fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s, &t, &seed32(b"sigma-coins")).unwrap();
    assert!(fs_verify::<Z1Instance, K, L, RING_DIM>(&key, &t, &proof));

    // Same witness committed under a different key ⇒ verification fails.
    let other_key: CommitmentKey<Z1Instance, K, L, RING_DIM> =
        CommitmentKey::setup(&seed32(b"contract-sigma-other"));
    let t_other = other_key.commit(&s);
    assert!(!fs_verify::<Z1Instance, K, L, RING_DIM>(
        &other_key, &t_other, &proof
    ));

    // A tampered commitment fails.
    let mut bad_t = t.clone();
    let mutated = {
        let mut coeffs = bad_t.polys()[0].coefficients();
        coeffs[0] += Z1Ring::ONE;
        coeffs
    };
    bad_t = ModuleVector::from_fn(|i| {
        if i == 0 {
            PolyRing::from_coefficients(mutated.clone())
        } else {
            bad_t.polys()[i].clone()
        }
    });
    assert!(!fs_verify::<Z1Instance, K, L, RING_DIM>(
        &key, &bad_t, &proof
    ));
}

#[test]
fn z2_batched_opening_accepts_honest_and_rejects_tampered() {
    let (r1cs, z) = gen_toy_instance(&seed32(b"contract-z2-instance"), 512, 2);
    assert!(r1cs.is_satisfied(&z));

    let key_seed = seed32(b"contract-z2-key");
    let domain = seed32(b"contract-z2-domain");
    let key = Z2CommitKey::setup(&key_seed);
    let (c, proof) = prove(&key, &key_seed, &domain, &r1cs, &z, &[9u8; 32]);
    assert!(verify(&key, &key_seed, &domain, &r1cs, &c, &proof));

    // Tamper with one response coefficient.
    let mut bad = proof.clone();
    let mut coeffs = ring_to_u32(&bad.z_prime[0]);
    coeffs[0] ^= 1;
    bad.z_prime[0] = ring_from_u32(&coeffs);
    assert!(!verify(&key, &key_seed, &domain, &r1cs, &c, &bad));

    // A different domain string must invalidate the proof.
    assert!(!verify(
        &key,
        &key_seed,
        &seed32(b"contract-z2-domair"),
        &r1cs,
        &c,
        &proof
    ));
}

#[test]
fn sumcheck_verifier_accepts_honest_claim_and_rejects_bad_rounds() {
    const G: usize = 6;
    let mut cnt = 0u64;
    let table: Vec<Z1Ring> = (0..1 << G)
        .map(|_| {
            cnt = cnt.wrapping_add(0x9E37_79B9_7F4A_7C15);
            Z1Ring::new((cnt >> 24) % 8_380_417)
        })
        .collect();
    let claimed: Z1Ring = table.iter().cloned().sum();

    let mut round = 0u64;
    let proof = sumcheck::prove::<Z1Ring, G>(&table, &mut || {
        round += 1;
        Z1Ring::new(round * 977)
    });

    let mut round = 0u64;
    let (challenges, final_eval) = sumcheck::verify(&proof, claimed, &mut || {
        round += 1;
        Z1Ring::new(round * 977)
    })
    .expect("honest sumcheck must verify");
    assert_eq!(challenges.len(), G);

    // A wrong claimed sum must be caught at the first round.
    let mut round = 0u64;
    assert!(sumcheck::verify(&proof, claimed + Z1Ring::ONE, &mut || {
        round += 1;
        Z1Ring::new(round * 977)
    })
    .is_none());

    // The final evaluation is the table at the derived point — recompute it.
    let mut eval = Z1Ring::ZERO;
    for (idx, &x) in table.iter().enumerate() {
        let mut term = Z1Ring::ONE;
        for (g, r) in challenges.iter().enumerate() {
            let bit = ((idx >> g) & 1) == 1;
            let coef = if bit { *r } else { Z1Ring::ONE - *r };
            term *= coef;
        }
        eval += term * x;
    }
    assert_eq!(eval, final_eval);
}

#[test]
fn folding_layer_accepts_honest_chain_and_rejects_tampering() {
    const N: usize = 8;
    const M: usize = 4;
    const GATES: usize = 64;

    let key = FoldKey::<N, M, GATES>::setup(&seed32(b"contract-fold-key"));
    let (r1cs, z1) = gen_toy_instance(&seed32(b"contract-fold-i1"), GATES, M);
    let (_r2, z2) = gen_toy_instance(&seed32(b"contract-fold-i2"), GATES, M);
    let (_r3, z3) = gen_toy_instance(&seed32(b"contract-fold-i3"), GATES, M);

    let make = |z: &[zk::protocols::z2_ring::Z2Ring]| RelaxedInstance {
        z: z.to_vec(),
        error: zk::protocols::z2::constraint_residuals(&r1cs, z),
        c_z: key.commit_witness(z),
        c_e: key.commit_error(&zk::protocols::z2::constraint_residuals(&r1cs, z)),
    };

    let mut r_coeffs = [0u32; 64];
    r_coeffs[0] = 0x1234_5678;
    let r1 = ring_from_u32(&r_coeffs);
    r_coeffs[0] = 0x8765_4321;
    let r2 = ring_from_u32(&r_coeffs);

    // Chain: (i1, i2) → f12, then (f12, i3) → f123.
    let f12 = fold(&key, &r1cs, &make(&z1), &make(&z2), r1);
    assert!(verify_folded(&key, &r1cs, &f12));
    let f123 = fold(&key, &r1cs, &f12, &make(&z3), r2);
    assert!(verify_folded(&key, &r1cs, &f123));

    // Tampering with the folded witness breaks verification.
    let mut bad = f12.clone();
    let mut coeffs = ring_to_u32(&bad.z[0]);
    coeffs[1] ^= 1;
    bad.z[0] = ring_from_u32(&coeffs);
    assert!(!verify_folded(&key, &r1cs, &bad));
}
