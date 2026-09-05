//! A tour of the whole workspace through the `lattice-algebra-rs` facade:
//! one algebraic primitive from each layer, one ML-DSA signature, and one
//! lattice ZK proof — all under the historical single-crate paths.
//!
//! Run with: `cargo run -p lattice-algebra-rs --example workspace_overview`

use lattice_algebra_rs::crypto::sampling::{sample_rej_bounded, BitStream};
use lattice_algebra_rs::crypto::xof::{Shake128Xof, Xof};
use lattice_algebra_rs::mldsa::mldsa_65;
use lattice_algebra_rs::module::{ModuleMatrixNtt, ModuleVector};
use lattice_algebra_rs::ntt::NttOperatorOptimized;
use lattice_algebra_rs::protocols::commitment::{
    CommitmentKey, LatticeCommitment, Z1Instance, RING_DIM,
};
use lattice_algebra_rs::protocols::sigma::{fs_prove, fs_verify};
use lattice_algebra_rs::ring::poly_ring::PolyRing;
use lattice_algebra_rs::ring::zq::Zq;
use lattice_algebra_rs::ring::PolynomialQuotientRing;

type ZqD = Zq<8380417>;
type Z1Ring = Zq<8380417>;
const SIGMA_K: usize = 4;
const SIGMA_L: usize = 3;

fn seed32(tag: &[u8]) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..tag.len()].copy_from_slice(tag);
    s
}

fn main() {
    println!("== L0–L4: the algebraic foundation ==");
    let a =
        PolyRing::<ZqD, 256>::from_coefficients((0..256).map(|i| ZqD::new(i as u64 + 1)).collect());
    let b = PolyRing::<ZqD, 256>::from_coefficients(
        (0..256).map(|i| ZqD::new((i * i + 3) as u64)).collect(),
    );
    let prod = a.clone() * b.clone();

    let op = NttOperatorOptimized::<ZqD, 256>::new();
    let prod_ntt = PolyRing::from_ntt(a.to_ntt(&op).mul(&b.to_ntt(&op)), &op);
    assert_eq!(prod, prod_ntt);
    println!("negacyclic mul in R_q agrees across coefficient and NTT domains   ✓");

    let mat =
        ModuleMatrixNtt::<ZqD, 2, 2, 256>::expand_from_seed::<Shake128Xof>(&seed32(b"overview"));
    let _ = &mat;
    println!("ExpandA: deterministic module matrix from a 32-byte seed   ✓");

    let mut x = Shake128Xof::new(b"overview-sampler");
    let mut s = BitStream::new(&mut x);
    let noise = sample_rej_bounded::<ZqD>(&mut s, 2);
    println!("RejBounded(η=2) draw: {noise}");

    println!("\n== L6 PQC: an ML-DSA-65 signature ==");
    let (sk, vk) = mldsa_65::keygen(&seed32(b"overview-ml-dsa"));
    let msg = b"signed by the unified lattice stack";
    let sigma = mldsa_65::sign_deterministic(&sk, b"overview", msg);
    assert!(mldsa_65::verify(&vk, b"overview", msg, &sigma));
    println!(
        "sign/verify OK, signature = {} bytes (FIPS 204)",
        sigma.len()
    );

    println!("\n== L5–L6 ZK: a Fiat–Shamir lattice NIZK ==");
    let key: CommitmentKey<Z1Instance, SIGMA_K, SIGMA_L, RING_DIM> =
        CommitmentKey::setup(&seed32(b"overview-zk"));
    let secret: ModuleVector<Z1Ring, SIGMA_L, RING_DIM> = ModuleVector::from_fn(|i| {
        PolyRing::from_coefficients(
            (0..RING_DIM)
                .map(|j| {
                    Z1Ring::new((((i as i64) * 3 + j as i64) % 9 - 4).rem_euclid(8_380_417) as u64)
                })
                .collect(),
        )
    });
    let t = key.commit(&secret);
    let proof = fs_prove::<Z1Instance, SIGMA_K, SIGMA_L, RING_DIM>(
        &key,
        &secret,
        &t,
        &seed32(b"overview-zk-coins"),
    )
    .expect("honest witness");
    assert!(fs_verify::<Z1Instance, SIGMA_K, SIGMA_L, RING_DIM>(
        &key, &t, &proof
    ));
    println!("Σ-protocol proof verifies against the Ajtai commitment   ✓");

    println!("\nOne foundation, two scheme families: PQC and zkSNARKs.");
}
