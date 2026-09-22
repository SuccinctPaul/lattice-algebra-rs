//! The Greyhound-style polynomial commitment: transparent, two-layer Ajtai
//! commitment to a polynomial with a √N-split evaluation proof.
//!
//! Run with: `cargo run -p lattice-zk --example greyhound_pcs`

use algebra::ring::{PolynomialQuotientRing, Ring};
use zk::foundation::encoding::ring_to_u32;
use zk::foundation::sampling::from_centered;
use zk::pcs::{self, greyhound};

/// Deterministic test polynomial: `N_DEG` ring elements with small
/// coefficients (the committed object — nothing about it is public except
/// through the commitment).
fn poly(seed: u64) -> Vec<pcs::RingElt> {
    (0..pcs::N_DEG)
        .map(|i| {
            let coeffs: Vec<_> = (0..pcs::DIM)
                .map(|j| {
                    from_centered::<pcs::Z1Coeff>(
                        ((seed as i64 * 7 + i as i64 * 3 + j as i64) % 9) - 4,
                    )
                })
                .collect();
            pcs::RingElt::from_coefficients(coeffs)
        })
        .collect()
}

fn point(v: u64) -> pcs::RingElt {
    let mut coeffs = vec![pcs::Z1Coeff::ZERO; pcs::DIM];
    coeffs[0] = pcs::Z1Coeff::from(v);
    coeffs[1] = pcs::Z1Coeff::from(v / 3 + 1);
    pcs::RingElt::from_coefficients(coeffs)
}

fn main() {
    // Transparent setup: every Ajtai key expands from a public seed.
    let key = greyhound::GreyhoundKey::setup(&[0xA7u8; 32]);
    println!(
        "instance: N = {} ring-element coefficients ({} blocks × {}), δ = {}",
        pcs::N_DEG,
        pcs::R_COLS,
        pcs::M_COLS,
        pcs::DELTA
    );

    let f = poly(3);
    let com = greyhound::commit(&key, &f).expect("canonical length");
    println!(
        "commitment u: {} ring elements ({} bytes)",
        com.u.len(),
        com.u.len() * pcs::DIM * 4
    );

    // Open at two points; each proof is the O(√N) core proof (LaBRADOR
    // compression is not layered on).
    for v in [12u64, 345] {
        let x = point(v);
        let (y, proof) = greyhound::open(&key, &f, &x).expect("canonical length");
        let ok = greyhound::verify(&key, &com, &x, &y, &proof);
        println!(
            "open at x₀ = {v}: y₀ coefficient = {}, proof = {} KB, verified: {}",
            ring_to_u32::<pcs::Z1Coeff, { pcs::DIM }>(&y)[0],
            proof.to_bytes().len() / 1024,
            ok.is_ok()
        );
        assert!(ok.is_ok());

        // a claimed evaluation shifted by one is rejected
        let bad_y = y.clone() + {
            let mut c = vec![pcs::Z1Coeff::ZERO; pcs::DIM];
            c[0] = pcs::Z1Coeff::ONE;
            pcs::RingElt::from_coefficients(c)
        };
        assert!(greyhound::verify(&key, &com, &x, &bad_y, &proof).is_err());
    }

    println!("all evaluation proofs verified; wrong claims rejected");

    // Batched opening: three polynomials, one shared point, ONE folded
    // opening — (k−1)·m·δ ring elements smaller than k single proofs.
    use zk::pcs::batched;
    let polys: Vec<Vec<pcs::RingElt>> = (0..3).map(poly).collect();
    let refs: Vec<&[pcs::RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
    let coms: Vec<greyhound::PolyCommitment> = polys
        .iter()
        .map(|f| greyhound::commit(&key, f).expect("canonical length"))
        .collect();
    let shared_x = point(777);
    let (ys, batched_proof) =
        batched::open_batch(&key, &refs, &shared_x).expect("canonical length");
    let ok = batched::verify_batch(&key, &coms, &shared_x, &ys, &batched_proof);
    println!(
        "batched open k = {} at one point: {} KB total vs {} KB as singles, verified: {}",
        polys.len(),
        batched_proof.to_bytes().len() / 1024,
        polys.len() * greyhound::OpeningProof::encoded_len() / 1024,
        ok.is_ok()
    );
    assert!(ok.is_ok());

    // a wrong claim inside the batch is rejected by the per-claim link
    let mut bad_ys = ys.clone();
    bad_ys[1] = bad_ys[1].clone() + {
        let mut c = vec![pcs::Z1Coeff::ZERO; pcs::DIM];
        c[0] = pcs::Z1Coeff::ONE;
        pcs::RingElt::from_coefficients(c)
    };
    assert!(batched::verify_batch(&key, &coms, &shared_x, &bad_ys, &batched_proof).is_err());
    println!("wrong claim inside the batch rejected");
}
