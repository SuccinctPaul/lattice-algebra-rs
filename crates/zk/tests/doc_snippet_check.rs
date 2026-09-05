//! Temporary guard: the quickstart snippets must compile and run verbatim.
use algebra::module::ModuleVector;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use zk::protocols::commitment::{CommitmentKey, LatticeCommitment, Z1Instance, RING_DIM};
use zk::protocols::sigma::{fs_prove, fs_verify};

type Z1Ring = Zq<8380417>;
const K: usize = 4;
const L: usize = 3;

#[test]
fn quickstart_sigma_snippet() {
    let key: CommitmentKey<Z1Instance, K, L, RING_DIM> = CommitmentKey::setup(&[7u8; 32]);

    // witness: a short secret s (coefficients in [-4, 4])
    let s: ModuleVector<Z1Ring, L, RING_DIM> = ModuleVector::from_fn(|i| {
        PolyRing::from_coefficients(
            (0..RING_DIM)
                .map(|j| {
                    Z1Ring::new((((i as i64) * 3 + j as i64) % 9 - 4).rem_euclid(8_380_417) as u64)
                })
                .collect(),
        )
    });
    let t = key.commit(&s); // statement: t = A·s

    let proof = fs_prove::<Z1Instance, K, L, RING_DIM>(&key, &s, &t, &[0x11u8; 32]).unwrap();
    assert!(fs_verify::<Z1Instance, K, L, RING_DIM>(&key, &t, &proof));
}
