//! The Greyhound-style polynomial commitment (eprint 2024/1293): a
//! transparent, two-layer Ajtai commitment to a polynomial with a √N-split
//! evaluation proof.
//!
//! This file is a **scheme assembly**: it holds no cryptographic logic and
//! only calls the capabilities `zk::pcs` exposes, through the [`Pcs`] /
//! [`BatchPcs`] traits. That is why the same twelve lines drive both the
//! ring-point mode and the σ-packed scalar mode below — and why a different
//! commitment scheme built on the same parts drops in unchanged.
//!
//! Run with: `cargo run -p lattice-zk --example greyhound_pcs`

use algebra::ring::{PolynomialQuotientRing, Ring};
use zk::foundation::encoding::ring_to_u32;
use zk::foundation::sampling::from_centered;
use zk::pcs::{self, BatchPcs, PackedGreyhound, Pcs, RingElt, Z1Coeff};

/// Deterministic test polynomial: `N_DEG` ring elements with small
/// coefficients (the committed object — nothing about it is public except
/// through the commitment).
fn poly(seed: u64) -> Vec<RingElt> {
    (0..pcs::N_DEG)
        .map(|i| {
            let coeffs: Vec<_> = (0..pcs::DIM)
                .map(|j| {
                    from_centered::<Z1Coeff>(((seed as i64 * 7 + i as i64 * 3 + j as i64) % 9) - 4)
                })
                .collect();
            RingElt::from_coefficients(coeffs)
        })
        .collect()
}

/// The same coefficients read as a scalar polynomial, for the packed mode.
fn scalar_poly(seed: u64) -> Vec<Z1Coeff> {
    poly(seed)
        .iter()
        .flat_map(|r| {
            ring_to_u32::<Z1Coeff, { pcs::DIM }>(r)
                .into_iter()
                .map(|c| Z1Coeff::from(u64::from(c)))
        })
        .collect()
}

fn point(v: u64) -> RingElt {
    let mut coeffs = vec![Z1Coeff::ZERO; pcs::DIM];
    coeffs[0] = Z1Coeff::from(v);
    coeffs[1] = Z1Coeff::from(v / 3 + 1);
    RingElt::from_coefficients(coeffs)
}

/// One committed evaluation claim, proved and re-checked through the trait.
///
/// Knows nothing about which scheme implements `P`.
fn claim_through_the_trait<P: Pcs>(label: &str, p: &P, f: &[P::Coeff], point: &P::Point)
where
    P::Error: core::fmt::Debug,
{
    let com = p.commit(f).expect("canonical length");
    let (value, proof) = p.open(f, point).expect("canonical length");
    p.verify(&com, point, &value, &proof)
        .expect("honest proof verifies");
    println!("  {label}: commit/open/verify through a generic over `impl Pcs`");
}

fn main() {
    // Transparent setup: every Ajtai key expands from a public seed.
    let key = pcs::GreyhoundKey::setup(&[0xA7u8; 32]);
    println!(
        "instance: N = {} ring-element coefficients ({} blocks × {}), δ = {}",
        pcs::N_DEG,
        pcs::R_COLS,
        pcs::M_COLS,
        pcs::DELTA
    );

    let f = poly(3);
    let com = key.commit(&f).expect("canonical length");
    println!(
        "commitment u: {} ring elements ({} bytes)",
        com.u.len(),
        com.u.len() * pcs::DIM * 4
    );

    // Open at two points; each proof is the O(√N) core proof (LaBRADOR
    // compression is not layered on).
    println!("ring-point mode (Coeff = Point = ring element):");
    for v in [12u64, 345] {
        let x = point(v);
        let (y, proof) = key.open(&f, &x).expect("canonical length");
        assert!(key.verify(&com, &x, &y, &proof).is_ok());
        let one = {
            let mut c = vec![Z1Coeff::ZERO; pcs::DIM];
            c[0] = Z1Coeff::ONE;
            RingElt::from_coefficients(c)
        };
        assert!(key.verify(&com, &x, &(y.clone() + one), &proof).is_err());
        println!(
            "  open at x₀ = {v}: y₀ = {}, {} KB proof, wrong claim rejected",
            ring_to_u32::<Z1Coeff, { pcs::DIM }>(&y)[0],
            proof.to_bytes().len() / 1024,
        );
    }

    // The σ-packed mode: same key, scalar coefficients and scalar points.
    println!("packed mode (Coeff = Point = scalar, d coefficients per element):");
    let packed = PackedGreyhound::new(pcs::GreyhoundKey::setup(&[0xA7u8; 32]));
    let sf = scalar_poly(3);
    let scom = packed.commit(&sf).expect("canonical length");
    let sx = Z1Coeff::from(3u64);
    let (sy, sproof) = packed.open(&sf, &sx).expect("canonical length");
    assert!(packed.verify(&scom, &sx, &sy, &sproof).is_ok());
    assert!(packed
        .verify(&scom, &sx, &(sy + Z1Coeff::ONE), &sproof)
        .is_err());
    println!(
        "  {} scalar coefficients committed, opened at a scalar point, {} KB proof",
        sf.len(),
        sproof.to_bytes().len() / 1024,
    );
    claim_through_the_trait("generic dispatch", &packed, &sf, &sx);

    // Batched opening: three polynomials, one shared point, ONE folded
    // opening — (k−1)·m·δ ring elements smaller than k single proofs.
    let polys: Vec<Vec<RingElt>> = (0..3).map(poly).collect();
    let refs: Vec<&[RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
    let coms = key.commit_many(&refs).expect("canonical length");
    let shared_x = point(777);
    let batch = key.open_batch(&refs, &shared_x).expect("canonical length");
    assert!(key
        .verify_batch(&coms, &shared_x, &batch.values, &batch.proof)
        .is_ok());
    let mut bad = batch.values.clone();
    bad[1] = bad[1].clone() + {
        let mut c = vec![Z1Coeff::ZERO; pcs::DIM];
        c[0] = Z1Coeff::ONE;
        RingElt::from_coefficients(c)
    };
    assert!(key
        .verify_batch(&coms, &shared_x, &bad, &batch.proof)
        .is_err());
    println!(
        "batched mode (k = {} at one point): {} KB total vs {} KB as singles, wrong claim rejected",
        polys.len(),
        batch.proof.to_bytes().len() / 1024,
        polys.len() * pcs::OpeningProof::encoded_len() / 1024,
    );

    println!("every mode drove the same traits; all wrong claims rejected");
}
