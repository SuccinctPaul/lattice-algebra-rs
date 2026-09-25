//! The JL projection argument: certify an `l2` norm bound on a committed
//! ring vector without revealing it.
//!
//! Run with: `cargo run -p lattice-zk --example projection_argument`

use algebra::crypto::sampling::BitStream;
use algebra::crypto::xof::{Shake256Xof, Xof};
use zk::foundation::sampling::fixed_weight_poly;
use zk::instance::ring::{Z2Coeff, Z2Ring, D};
use zk::shortness::projection::{
    certified_l2_bound, prove_l2_shortness, verify_l2_shortness, JLProjection, GHL21_MIN_ROWS,
};

fn main() {
    // `K` is the reduced dimension = confidence parameter. It sits at
    // `GHL21_MIN_ROWS` deliberately: below that floor the certified tail is
    // not merely larger, it is *not provable*, and `certified_l2_bound`
    // returns `None`.
    const K: usize = GHL21_MIN_ROWS;
    const STALE_K: usize = 128;

    // a witness with exactly one ±13 coefficient per ring element:
    // ‖w‖₂ = 2·√M·13 — the prover's secret
    let mut xof = Shake256Xof::new(&[7]);
    let mut stream = BitStream::new(&mut xof);
    const M: usize = 4;
    let w: Vec<Z2Ring> = (0..M)
        .map(|_| fixed_weight_poly::<Z2Coeff, _, D>(&mut stream, 1, 13))
        .collect();

    // the verifier derives the ±1 projection from a seed (no trusted setup)
    let projection = JLProjection::from_seed(&[42; 32], K, M * D);

    // the response p = Π·w is a small vector of integers — the witness
    // itself never leaves the prover
    let p = prove_l2_shortness(&projection, &w);
    let claimed_bound = 64_u64; // ‖w‖₂ = 26 ≤ 64
    println!("response rows: {}", p.len());
    // The certified tail depends on how many rows the projection drew, and it
    // is **refused** (not merely widened) below `GHL21_MIN_ROWS`. Printed as an
    // `Option` on purpose: where the floor sits, and whether the tuned tail
    // clears it at a given `B`, is pinned by `shortness::projection`'s own
    // tests — this example is about `prove`/`verify`, so it must not fail just
    // because that certificate's arithmetic moved.
    println!(
        "certified bound: {K} rows → {:?}, {STALE_K} rows → {:?}",
        certified_l2_bound(K, claimed_bound),
        certified_l2_bound(STALE_K, claimed_bound),
    );

    let accepted = verify_l2_shortness(&projection, &p, claimed_bound);
    println!("honest certificate accepted: {accepted}");
    assert!(accepted);

    // an inflated claim is caught with probability increasing in K: claim
    // the same bound for a 4× larger witness
    let inflated: Vec<Z2Ring> = (0..M)
        .map(|_| fixed_weight_poly::<Z2Coeff, _, D>(&mut stream, 1, 52))
        .collect();
    let p_bad = prove_l2_shortness(&projection, &inflated);
    println!(
        "inflated certificate accepted: {} (β = 4 > 2 must fail)",
        verify_l2_shortness(&projection, &p_bad, claimed_bound)
    );
}
