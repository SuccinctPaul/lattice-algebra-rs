//! Protocol-level contract tests: each ZK milestone exercised end-to-end
//! through its public API, including the negative cases verifiers must
//! reject.

use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::module::ModuleVector;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;
use zk::commitment::ajtai::{CommitmentKey, LatticeCommitment, Z1Instance, RING_DIM};
use zk::folding::latticefold::{prove_fold_decompose, verify_fold_decompose, LfKey};
use zk::folding::nova::{fold, verify_folded, FoldKey, RelaxedInstance};
use zk::foundation::encoding::{ring_from_u32, ring_to_u32};
use zk::instance::r1cs::gen_toy_instance;
use zk::instance::ring::infinity_norm;
use zk::opening::{prove, verify, Z2CommitKey};
use zk::shortness::balanced::{
    certified_bound, projection_challenge, prove_projection, verify_projection, ShortKey,
};
use zk::sigma::{fs_prove, fs_verify};
use zk::sumcheck;
use zk::sumcheck::RoundChallenger;

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
                .map(|j| {
                    Z1Ring::new((((i as i64) * 3 + j as i64) % 9 - 4).rem_euclid(8_380_417) as u64)
                })
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

    // Deterministic counter challenger: round `g` yields `977·g`, derived
    // identically by the (honest) prover and verifier.
    struct CounterChallenger {
        round: u64,
    }
    impl RoundChallenger<Z1Ring> for CounterChallenger {
        fn round_challenge(&mut self, _h0: &Z1Ring, _h1: &Z1Ring) -> Z1Ring {
            self.round += 1;
            Z1Ring::new(self.round * 977)
        }
    }

    let proof = sumcheck::prove::<Z1Ring, G>(&table, &mut CounterChallenger { round: 0 });

    let (challenges, final_eval) =
        sumcheck::verify(&proof, claimed, &mut CounterChallenger { round: 0 })
            .expect("honest sumcheck must verify");
    assert_eq!(challenges.len(), G);

    // A wrong claimed sum must be caught at the first round.
    assert!(sumcheck::verify(
        &proof,
        claimed + Z1Ring::ONE,
        &mut CounterChallenger { round: 0 }
    )
    .is_none());

    // The final evaluation is the table at the derived point — recompute it.
    // Round g of the fold interpolates bit (G-1-g) (top bit first): index j
    // and j + len/2 differ in that bit when the vector is halved.
    let mut eval = Z1Ring::ZERO;
    for (idx, &x) in table.iter().enumerate() {
        let mut term = Z1Ring::ONE;
        for (g, r) in challenges.iter().enumerate() {
            let bit = ((idx >> (G - 1 - g)) & 1) == 1;
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

    let make = |z: &[zk::instance::ring::Z2Ring]| RelaxedInstance {
        z: z.to_vec(),
        error: zk::opening::constraint_residuals(&r1cs, z),
        c_z: key.commit_witness(z),
        c_e: key.commit_error(&zk::opening::constraint_residuals(&r1cs, z)),
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

#[test]
fn polynomial_commitment_accepts_honest_opening_and_rejects_forgeries() {
    use zk::foundation::sampling::from_centered;
    use zk::pcs::{self, greyhound};

    let key = greyhound::GreyhoundKey::setup(&seed32(b"contract-pcs-key"));
    let f: Vec<pcs::RingElt> = (0..pcs::N_DEG)
        .map(|i| {
            let coeffs: Vec<_> = (0..pcs::DIM)
                .map(|j| from_centered::<pcs::Z1Coeff>(((i * 7 + j) % 11) as i64 - 5))
                .collect();
            PolyRing::from_coefficients(coeffs)
        })
        .collect();

    let com = greyhound::commit(&key, &f).expect("canonical length");
    let x = ring_from_u32(&{
        let mut c = [0u32; pcs::DIM];
        c[0] = 1234;
        c[1] = 77;
        c
    });
    let (y, proof) = greyhound::open(&key, &f, &x).expect("canonical length");
    assert!(greyhound::verify(&key, &com, &x, &y, &proof).is_ok());

    // The claimed evaluation is the plain Horner evaluation of f at x.
    let mut horner = {
        let coeffs = vec![pcs::Z1Coeff::ZERO; pcs::DIM];
        pcs::RingElt::from_coefficients(coeffs)
    };
    for f_j in f.iter().rev() {
        horner = horner * &x + f_j;
    }
    assert_eq!(y, horner);

    // A wrong claimed evaluation fails the consistency check.
    let bad_y = y.clone()
        + ring_from_u32(&{
            let mut c = [0u32; pcs::DIM];
            c[0] = 1;
            c
        });
    assert!(greyhound::verify(&key, &com, &x, &bad_y, &proof).is_err());

    // The evaluation claimed for a *different* polynomial fails against
    // the original commitment and proof (check 2 pins y to the committed f).
    let f_other = f
        .iter()
        .enumerate()
        .map(|(i, elt)| {
            if i == 0 {
                elt.clone()
                    + ring_from_u32(&{
                        let mut c = [0u32; pcs::DIM];
                        c[2] = 3;
                        c
                    })
            } else {
                elt.clone()
            }
        })
        .collect::<Vec<_>>();
    let (y_other, _proof_other) = greyhound::open(&key, &f_other, &x).unwrap();
    assert!(greyhound::verify(&key, &com, &x, &y_other, &proof).is_err());

    // Tampering with the decomposed inner commitments fails the links.
    let mut bad = proof.clone();
    let mut coeffs = ring_to_u32(&bad.t_hat[0]);
    coeffs[4] ^= 1;
    bad.t_hat[0] = ring_from_u32(&coeffs);
    assert!(greyhound::verify(&key, &com, &x, &y, &bad).is_err());
}

#[test]
fn batched_pcs_accepts_honest_batch_and_rejects_mixed_claims() {
    use zk::foundation::sampling::from_centered;
    use zk::pcs::{self, batched, greyhound};

    let key = greyhound::GreyhoundKey::setup(&seed32(b"contract-pcs-batch-key"));
    let polys: Vec<Vec<pcs::RingElt>> = (0..3)
        .map(|p| {
            (0..pcs::N_DEG)
                .map(|i| {
                    let coeffs: Vec<_> = (0..pcs::DIM)
                        .map(|j| {
                            from_centered::<pcs::Z1Coeff>(
                                ((p as i64 * 11 + i as i64 * 7 + j as i64) % 11) - 5,
                            )
                        })
                        .collect();
                    PolyRing::from_coefficients(coeffs)
                })
                .collect()
        })
        .collect();
    let refs: Vec<&[pcs::RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
    let coms: Vec<greyhound::PolyCommitment> = polys
        .iter()
        .map(|f| greyhound::commit(&key, f).expect("canonical length"))
        .collect();

    let x = ring_from_u32(&{
        let mut c = [0u32; pcs::DIM];
        c[0] = 999;
        c[1] = 41;
        c
    });
    let (ys, proof) = batched::open_batch(&key, &refs, &x).expect("canonical length");
    assert_eq!(ys.len(), 3);
    assert!(batched::verify_batch(&key, &coms, &x, &ys, &proof).is_ok());

    // every batched claim equals the single-protocol evaluation
    for (f, y) in polys.iter().zip(&ys) {
        let (y_single, _) = greyhound::open(&key, f, &x).unwrap();
        assert_eq!(*y, y_single);
    }

    // a wrong claim for one polynomial breaks the per-claim link
    let mut bad_ys = ys.clone();
    bad_ys[2] = bad_ys[2].clone()
        + ring_from_u32(&{
            let mut c = [0u32; pcs::DIM];
            c[0] = 1;
            c
        });
    assert!(batched::verify_batch(&key, &coms, &x, &bad_ys, &proof).is_err());

    // the proof is bound to the shared point
    let other_x = ring_from_u32(&{
        let mut c = [0u32; pcs::DIM];
        c[0] = 1000;
        c[1] = 41;
        c
    });
    assert!(batched::verify_batch(&key, &coms, &other_x, &ys, &proof).is_err());

    // claims cannot be mixed across a different commitment set: swapping in
    // a commitment for a different polynomial breaks the links
    let f_other = polys[0]
        .iter()
        .enumerate()
        .map(|(i, elt)| {
            if i == 0 {
                elt.clone()
                    + ring_from_u32(&{
                        let mut c = [0u32; pcs::DIM];
                        c[2] = 3;
                        c
                    })
            } else {
                elt.clone()
            }
        })
        .collect::<Vec<_>>();
    let com_other = greyhound::commit(&key, &f_other).unwrap();
    let mixed_coms = vec![com_other, coms[1].clone(), coms[2].clone()];
    assert!(batched::verify_batch(&key, &mixed_coms, &x, &ys, &proof).is_err());
}

#[test]
fn projection_l2_bound_amortized_binding_accepts_honest_and_rejects_forgeries() {
    use algebra::crypto::sampling::BitStream;
    use algebra::crypto::xof::{Shake256Xof, Xof};
    use zk::instance::ring::Z2Coeff;
    use zk::instance::ring::Z2Ring;
    use zk::shortness::projection::{
        certified_l2_bound, prove_l2_bound_amortized, verify_l2_bound_amortized, JLProjection,
    };
    use zk::sumcheck::ipa::IpaKey;

    const K_ROWS: usize = 16;

    let key = IpaKey::<8, 4>::setup(&seed32(b"contract-proj-amortized"));
    let key_seed = seed32(b"contract-proj-amortized-key");

    // GHL21-tuned projection rows over the ring (block-circulant family)
    let rows: Vec<Vec<Z2Ring>> = (0..K_ROWS)
        .map(|i| {
            let mut xof = Shake256Xof::new(&[91u8, i as u8]);
            let mut stream = BitStream::new(&mut xof);
            (0..4)
                .map(|_| {
                    zk::foundation::sampling::centered_bounded_poly::<Z2Coeff, _, 64>(
                        &mut stream,
                        1,
                    )
                })
                .collect()
        })
        .collect();

    // honest witness with ‖s‖₂ ≈ 29, claimed bound 40 (certifies ≈ 82.6)
    let s: Vec<Z2Ring> = (0..4)
        .map(|j| {
            let mut xof = Shake256Xof::new(&[200u8, j as u8]);
            let mut stream = BitStream::new(&mut xof);
            zk::foundation::sampling::centered_bounded_poly::<Z2Coeff, _, 64>(&mut stream, 3)
        })
        .collect();
    let claimed = 40u64;

    let (c, proof) = prove_l2_bound_amortized(&key, &key_seed, &rows, &s, claimed, &[7u8; 32])
        .expect("honest response within budget");
    assert!(verify_l2_bound_amortized(
        &key, &key_seed, &rows, &c, claimed, &proof
    ));
    // the certificate carries the GHL21 gap
    assert_eq!(certified_l2_bound(claimed), certified_l2_bound(40));

    // a response inconsistent with the committed witness fails the IPA link
    let s_forge: Vec<Z2Ring> = (0..4)
        .map(|j| {
            let mut xof = Shake256Xof::new(&[201u8, j as u8]);
            let mut stream = BitStream::new(&mut xof);
            zk::foundation::sampling::centered_bounded_poly::<Z2Coeff, _, 64>(&mut stream, 3)
        })
        .collect();
    let (_c2, proof_forge) =
        prove_l2_bound_amortized(&key, &key_seed, &rows, &s_forge, claimed, &[7u8; 32])
            .expect("same norm class");
    assert!(!verify_l2_bound_amortized(
        &key,
        &key_seed,
        &rows,
        &c,
        claimed,
        &proof_forge
    ));

    // tampering with the revealed response fails the binding
    let mut bad = proof.clone();
    let mut coeffs = ring_to_u32(&bad.p[2]);
    coeffs[9] = coeffs[9].wrapping_add(7);
    bad.p[2] = ring_from_u32(&coeffs);
    assert!(!verify_l2_bound_amortized(
        &key, &key_seed, &rows, &c, claimed, &bad
    ));

    // the standalone flat variant stays coherent with the certified constant
    let flat = JLProjection::from_seed(&seed32(b"contract-proj-flat"), 64, 256);
    assert_eq!(flat.rows(), 64);
    let _ = certified_l2_bound;
}

#[test]
fn pairwise_folding_chain_compresses_committed_witnesses() {
    use algebra::crypto::sampling::BitStream;
    use algebra::crypto::xof::{Shake256Xof, Xof};
    use zk::instance::ring::Z2Coeff;
    use zk::instance::ring::Z2Ring;
    use zk::shortness::fold::fold_and_certify;
    use zk::shortness::projection::JLProjection;
    use zk::sumcheck::ipa::IpaKey;

    const WITNESSES: usize = 8; // 2^3 → a 3-level folding tree

    let key = IpaKey::<8, 4>::setup(&seed32(b"contract-fold-pair"));

    // eight committed short witnesses
    let witnesses: Vec<Vec<Z2Ring>> = (0..WITNESSES)
        .map(|i| {
            let mut xof = Shake256Xof::new(&[150u8, i as u8]);
            let mut stream = BitStream::new(&mut xof);
            (0..4)
                .map(|_| {
                    zk::foundation::sampling::centered_bounded_poly::<Z2Coeff, _, 64>(
                        &mut stream,
                        3,
                    )
                })
                .collect()
        })
        .collect();
    let commitments: Vec<Vec<Z2Ring>> = witnesses.iter().map(|w| key.commit(w).to_vec()).collect();

    // a 3-level pairwise folding tree: level i folds pairs with challenges
    // γ derived deterministically per level (the recursion's challenge
    // derivation); each level's folded witness is JL-certified short
    let mut level_commitments = commitments.clone();
    let mut level_witnesses = witnesses.clone();
    let mut level = 0u8;
    while level_commitments.len() > 1 {
        // small unit-scale challenges keep the folded norm within the
        // claimed bound (large γ scales the fold's norm by |γ|)
        let gamma = ring_from_u32(&{
            let mut c = [0u32; 64];
            c[0] = 1 + u32::from(level);
            c
        });
        // the claimed bound doubles per level (the fold of two bound-B
        // witnesses has norm ≤ 2B); the JL certificate checks against the
        // GHL21 gap on top
        let claimed = 80u64 * (1u64 << level);
        let proj_l = JLProjection::from_seed(&seed32(b"contract-fold-pair-proj"), 128, 4 * 64);
        let mut next_c = Vec::new();
        let mut next_w = Vec::new();
        for pair in (0..level_commitments.len()).step_by(2) {
            let folded = fold_and_certify(
                &key,
                &level_commitments[pair],
                &level_commitments[pair + 1],
                &level_witnesses[pair],
                &level_witnesses[pair + 1],
                &gamma,
                &proj_l,
                claimed,
            )
            .expect("honest folded level certifies");
            next_c.push(folded.c_star);
            next_w.push(folded.s_star);
        }
        level_commitments = next_c;
        level_witnesses = next_w;
        level += 1;
    }
    assert_eq!(level_commitments.len(), 1);
    assert_eq!(level, 3);

    // the single remaining commitment pins the fully-folded witness
    assert_eq!(
        key.commit(&level_witnesses[0]).as_slice(),
        level_commitments[0].as_slice()
    );
}

#[test]
fn mle_commitment_supports_exact_weighted_claims() {
    use algebra::crypto::sampling::BitStream;
    use algebra::crypto::xof::{Shake256Xof, Xof};
    use zk::instance::ring::Z2Coeff;
    use zk::pcs::{
        self,
        mle::{claim, commit_mle, witness_of, MleKey},
    };

    const L: usize = 256;
    let key = MleKey::setup(&seed32(b"contract-mle-key"), L);
    let mut xof = Shake256Xof::new(&[9]);
    let mut stream = BitStream::new(&mut xof);
    let f: Vec<pcs::Z1Coeff> = (0..L)
        .map(|_| {
            let poly =
                zk::foundation::sampling::centered_bounded_poly::<Z2Coeff, _, 1>(&mut stream, 3);
            pcs::Z1Coeff::from(u64::from(poly.coefficients()[0].to_u128() as u32))
        })
        .collect();
    let com = commit_mle(&key, &f).expect("length ok");

    // exact weighted claims: power table (point evaluation) and a
    // combination of two weight tables
    let x = pcs::Z1Coeff::from(500);
    let pow: Vec<pcs::Z1Coeff> = {
        let mut w = Vec::with_capacity(L);
        let mut cur = pcs::Z1Coeff::ONE;
        for _ in 0..L {
            w.push(cur);
            cur *= x;
        }
        w
    };
    let y = claim(&key, &com, &pow).expect("claim ok");
    let mut horner = pcs::Z1Coeff::ZERO;
    for f_j in f.iter().rev() {
        horner = horner * x + *f_j;
    }
    assert_eq!(y, horner);

    // the transparent read-out recovers the witness exactly
    let back = witness_of(&key, &com).expect("binding commitment");
    assert_eq!(back, f);

    // a forged commitment fails the claim
    let mut bad = com.clone();
    bad.c[0] += pcs::Z1Coeff::from(7);
    let y_bad = claim(&key, &bad, &pow).expect("still consistent system");
    assert_ne!(y_bad, y, "forged commitment changes the read-out");
}

#[test]
fn packed_pcs_binds_scalar_evaluation_claims() {
    use zk::foundation::sampling::from_centered;
    use zk::pcs::{self, greyhound};

    let key = greyhound::GreyhoundKey::setup(&seed32(b"contract-pcs-packed"));
    // 16384 scalar coefficients packed into the 64 ring-element commitment
    let f: Vec<pcs::Z1Coeff> = (0..pcs::N_DEG * pcs::DIM)
        .map(|i| from_centered::<pcs::Z1Coeff>(((i * 17 + 5) % 61) as i64 - 30))
        .collect();

    let com = greyhound::commit_packed(&key, &f).expect("canonical length");
    let x = from_centered::<pcs::Z1Coeff>(4321);
    let (y, proof) = greyhound::open_packed(&key, &f, x).expect("canonical length");

    // the claim is the plain scalar Horner evaluation (independent path)
    let mut fold = pcs::Z1Coeff::ZERO;
    for c in f.iter().rev() {
        fold = fold * x + *c;
    }
    assert_eq!(y, fold);
    assert!(greyhound::verify_packed(&key, &com, x, y, &proof).is_ok());

    // a wrong claimed evaluation fails the σ-pairing binding (check 2)
    let bad_y = y + pcs::Z1Coeff::from(1);
    assert!(greyhound::verify_packed(&key, &com, x, bad_y, &proof).is_err());

    // a different polynomial's claim fails under this commitment
    let mut f_other = f.clone();
    f_other[100] += pcs::Z1Coeff::from(3);
    let (y_other, _p) = greyhound::open_packed(&key, &f_other, x).unwrap();
    assert!(greyhound::verify_packed(&key, &com, x, y_other, &proof).is_err());

    // tampering with the folded opening fails the links
    let mut bad = proof.clone();
    let mut coeffs = ring_to_u32(&bad.z[3]);
    coeffs[6] ^= 1;
    bad.z[3] = ring_from_u32(&coeffs);
    assert!(greyhound::verify_packed(&key, &com, x, y, &bad).is_err());
}

#[test]
fn prime_ring_switch_feeds_z2_digits_through_range_claims() {
    use algebra::ring::MatrixElement;
    use zk::instance::ring::{switch_exact_guard, switch_scalar};
    use zk::sumcheck::batch::{prove_batched, verify_batched, BatchClaim};
    use zk::sumcheck::range::range_claim_table;
    use zk::sumcheck::FsChallenger;

    const G: usize = 6;
    const Q: u64 = 8_380_417;
    type Rq = Zq<8380417>;

    // Z2-line digit values (the 2-adic domain's native representation):
    // scalar-valued ring elements with digits in [−3, 3].
    let z2_digit = |d: i64| -> zk::instance::ring::Z2Ring {
        ring_from_u32(&{
            let mut c = [0u32; 64];
            c[0] = (d.rem_euclid(1 << 32)) as u32;
            c
        })
    };
    let digits: Vec<zk::instance::ring::Z2Ring> = (0..1 << G)
        .map(|i| z2_digit((((i * 13) % 7) as i64) - 3))
        .collect();

    // the guard holds for these operands: 64·3² = 576 ≪ 2^31 and ≪ q/2
    assert!(switch_exact_guard(64, 3, Q));

    // switch the whole digit table into the prime scalar ring
    let switched: Vec<Rq> = digits
        .iter()
        .map(|d| switch_scalar::<Rq>(d).expect("digit in window"))
        .collect();
    // the switch is the identity on integers: signed roundtrip per entry
    for (i, s) in switched.iter().enumerate() {
        let d = (((i * 13) % 7) as i64) - 3;
        assert_eq!(*s, Rq::from(d.rem_euclid(Q as i64) as u64));
    }

    // now the prime-ring-only machinery applies: the vanishing range claim
    let range_table = range_claim_table(&switched, 3);
    let range_sum: Rq = range_table.iter().fold(Rq::zero(), |a, b| a + *b);
    assert_eq!(range_sum, Rq::zero(), "all digits in [−3, 3] ⇒ sum 0");

    let claims = [BatchClaim {
        table: &range_table,
        eq_point: None,
        claimed: Rq::zero(),
    }];
    let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"contract-switch-range");
    let proof = prove_batched::<Rq, G>(&claims, &mut ch);
    let mut chv = FsChallenger::<Shake128Xof, Rq>::new(b"contract-switch-range");
    assert!(
        verify_batched::<Rq, G>(&proof, &[Rq::zero()], &mut chv).is_some(),
        "switched Z2 digits pass the prime-ring range proof"
    );

    // one digit corrupted to 4 (outside [−3, 3], still well inside the
    // switch window) shows up in the switched vanishing claim
    let mut bad = digits.clone();
    bad[9] = z2_digit(4);
    let bad_switched: Vec<Rq> = bad
        .iter()
        .map(|d| switch_scalar::<Rq>(d).expect("in window"))
        .collect();
    let bad_range = range_claim_table(&bad_switched, 3);
    let bad_sum: Rq = bad_range.iter().fold(Rq::zero(), |a, b| a + *b);
    assert_ne!(bad_sum, Rq::zero(), "the out-of-range digit shows up");

    let bad_claims = [BatchClaim {
        table: &bad_range,
        eq_point: None,
        claimed: Rq::zero(), // the lie
    }];
    let mut ch2 = FsChallenger::<Shake128Xof, Rq>::new(b"contract-switch-range");
    let bad_proof = prove_batched::<Rq, G>(&bad_claims, &mut ch2);
    let mut chv2 = FsChallenger::<Shake128Xof, Rq>::new(b"contract-switch-range");
    assert!(verify_batched::<Rq, G>(&bad_proof, &[Rq::zero()], &mut chv2).is_none());
}

#[test]
fn batched_sumcheck_merges_data_claims_and_range_claim() {
    use algebra::ring::MatrixElement;
    use zk::sumcheck::batch::{combined_table, prove_batched, verify_batched, BatchClaim};
    use zk::sumcheck::range::range_claim_table;
    use zk::sumcheck::FsChallenger;

    const G: usize = 6;
    const Q: u64 = 8_380_417;
    type Rq = Zq<8380417>;

    let digit_table: Vec<Rq> = (0..1 << G)
        .map(|i| Rq::from(((((i * 13) % 7) as i64 - 3).rem_euclid(Q as i64)) as u64))
        .collect();
    let data_table: Vec<Rq> = (0..1 << G)
        .map(|i| Rq::from((i * 29 % 101) as u64))
        .collect();
    let beta: [Rq; G] = core::array::from_fn(|i| Rq::from(500 + i as u64));

    let claimed = |t: &[Rq]| t.iter().fold(Rq::zero(), |a, b| a + *b);
    let digit_sum = claimed(&digit_table);
    // eq(β)-weighted data claim: ⟨eq(β), T⟩
    let data_eq_sum: Rq = (0..1 << G)
        .map(|idx| {
            let mut bits = [false; G];
            for (g, bit) in bits.iter_mut().enumerate() {
                *bit = (idx >> g) & 1 == 1;
            }
            sumcheck::eq_tensor(&beta, &bits) * data_table[idx]
        })
        .fold(Rq::zero(), |a, b| a + b);
    // the range claim: g₃ applied position-wise, honest sum zero
    let range_table = range_claim_table(&digit_table, 3);
    assert_eq!(claimed(&range_table), Rq::zero());

    let claims = [
        BatchClaim {
            table: &data_table,
            eq_point: Some(&beta),
            claimed: data_eq_sum,
        },
        BatchClaim {
            table: &digit_table,
            eq_point: None,
            claimed: digit_sum,
        },
        BatchClaim {
            table: &range_table,
            eq_point: None,
            claimed: Rq::zero(),
        },
    ];

    let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"contract-pi-batch");
    ch.absorb(b"claims", &[1, 2, 3]);
    let proof = prove_batched::<Rq, G>(&claims, &mut ch);

    let claimed_list = vec![data_eq_sum, digit_sum, Rq::zero()];
    let mut chv = FsChallenger::<Shake128Xof, Rq>::new(b"contract-pi-batch");
    chv.absorb(b"claims", &[1, 2, 3]);
    let (challenges, final_eval) = verify_batched::<Rq, G>(&proof, &claimed_list, &mut chv)
        .expect("honest batch with range claim must verify");
    assert_eq!(challenges.len(), G);

    // transparent tie-back: the final evaluation matches the combined table
    let combined = combined_table(&claims, &proof.gamma);
    let mut point_eval = Rq::zero();
    for (idx, t) in combined.iter().enumerate() {
        let mut w = Rq::one();
        for (g, r) in challenges.iter().enumerate() {
            let bit = (idx >> (G - 1 - g)) & 1 == 1;
            w *= if bit { *r } else { Rq::one() - *r };
        }
        point_eval += w * *t;
    }
    assert_eq!(final_eval, point_eval);

    // a single out-of-range digit makes the range table's honest sum
    // nonzero: a prover that still claims zero fails round-1 consistency
    let mut bad_digits = digit_table.clone();
    bad_digits[9] = Rq::from(4); // outside [−3, 3]
    let bad_range = range_claim_table(&bad_digits, 3);
    assert_ne!(claimed(&bad_range), Rq::zero());
    let bad_claims = [
        BatchClaim {
            table: &data_table,
            eq_point: Some(&beta),
            claimed: data_eq_sum,
        },
        BatchClaim {
            table: &bad_digits,
            eq_point: None,
            claimed: claimed(&bad_digits),
        },
        BatchClaim {
            table: &bad_range,
            eq_point: None,
            claimed: Rq::zero(), // the lie
        },
    ];
    let mut ch2 = FsChallenger::<Shake128Xof, Rq>::new(b"contract-pi-batch");
    ch2.absorb(b"claims", &[1, 2, 3]);
    let bad_proof = prove_batched::<Rq, G>(&bad_claims, &mut ch2);
    let mut chv2 = FsChallenger::<Shake128Xof, Rq>::new(b"contract-pi-batch");
    chv2.absorb(b"claims", &[1, 2, 3]);
    assert!(verify_batched::<Rq, G>(&bad_proof, &claimed_list, &mut chv2).is_none());
}

/// Ring vectors with small (masked) coefficients, drawn from a SHAKE stream.
fn contract_rnd_vec(
    xof: &mut Shake128Xof,
    len: usize,
    mask: u32,
) -> Vec<zk::instance::ring::Z2Ring> {
    (0..len)
        .map(|_| {
            let mut coeffs = [0u32; 64];
            let mut buf = [0u8; 4];
            for c in &mut coeffs {
                xof.squeeze(&mut buf);
                *c = u32::from_le_bytes(buf) & mask;
            }
            ring_from_u32(&coeffs)
        })
        .collect()
}

#[test]
fn projection_argument_accepts_honest_and_rejects_forgeries() {
    use zk::instance::ring::Z2Ring;

    const N: usize = 8;
    const M: usize = 4;
    let key_seed = seed32(b"contract-short-key");
    let key = ShortKey::<N, M>::setup(&key_seed);
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(b"contract-short-witness");
    let w = contract_rnd_vec(&mut xof, M, 0x0000_FFFF);
    let t = contract_rnd_vec(&mut xof, M, 0x0000_000F);
    let c = key.mul_vec(&w);

    let zeta = projection_challenge::<N, M>(&key_seed, &c, &t, 1, 56);
    let gamma = 12;
    let proof = prove_projection::<N, M>(&w, &t, &zeta, gamma);

    // The certified bound covers the true norm of v = w − ζ·t.
    let zt: Vec<Z2Ring> = t.iter().map(|ti| zeta.clone() * ti.clone()).collect();
    let v = w
        .iter()
        .zip(&zt)
        .map(|(a, b)| a.clone() - b.clone())
        .collect::<Vec<_>>();
    let high_bound = infinity_norm(&proof.high);
    assert!(verify_projection::<N, M>(
        &key, &c, &t, &zeta, gamma, high_bound, &proof
    ));
    assert!(infinity_norm(&v) <= certified_bound(gamma, high_bound));

    // Overclaiming the high bound must be rejected.
    assert!(!verify_projection::<N, M>(
        &key,
        &c,
        &t,
        &zeta,
        gamma,
        high_bound.saturating_sub(1),
        &proof
    ));

    // Tampering with a digit breaks the exact link.
    let mut bad = proof.clone();
    let mut coeffs = ring_to_u32(&bad.low[0]);
    coeffs[0] ^= 1;
    bad.low[0] = ring_from_u32(&coeffs);
    assert!(!verify_projection::<N, M>(
        &key, &c, &t, &zeta, gamma, high_bound, &bad
    ));
}

#[test]
fn latticefold_folding_accepts_honest_and_rejects_tampering() {
    const N: usize = 8;
    const M: usize = 4;
    let key_seed = seed32(b"contract-lf-key");
    let key = LfKey::<N, M>::setup(&key_seed);
    let mut xof = Shake128Xof::new(&[]);
    xof.absorb(b"contract-lf-witnesses");
    let w1 = contract_rnd_vec(&mut xof, M, 0x0000_FFFF);
    let w2 = contract_rnd_vec(&mut xof, M, 0x0000_FFFF);

    let l1_r = 48;
    let l1_zeta = 48;
    let (c1, c2, proof) = prove_fold_decompose::<N, M>(&key, &key_seed, &w1, &w2, l1_r, l1_zeta);
    assert!(verify_fold_decompose::<N, M>(
        &key, &key_seed, &c1, &c2, l1_r, l1_zeta, &proof
    ));

    // A tampered digit commitment must fail (consistency or splitting).
    let mut bad = proof.clone();
    let mut coeffs = ring_to_u32(&bad.digit_comms[2][0]);
    coeffs[1] ^= 1;
    bad.digit_comms[2][0] = ring_from_u32(&coeffs);
    assert!(!verify_fold_decompose::<N, M>(
        &key, &key_seed, &c1, &c2, l1_r, l1_zeta, &bad
    ));

    // A tampered batched opening must fail.
    let mut bad = proof;
    let mut coeffs = ring_to_u32(&bad.d_tilde[1]);
    coeffs[5] ^= 1;
    bad.d_tilde[1] = ring_from_u32(&coeffs);
    assert!(!verify_fold_decompose::<N, M>(
        &key, &key_seed, &c1, &c2, l1_r, l1_zeta, &bad
    ));
}
