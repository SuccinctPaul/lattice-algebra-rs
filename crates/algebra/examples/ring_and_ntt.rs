//! Ring and NTT basics: scalar arithmetic in `Z_q`, negacyclic
//! multiplication in `R_q = Z_q[X]/(X^N+1)`, and the NTT-domain view.
//!
//! Run with: `cargo run -p lattice-algebra --example ring_and_ntt`

use algebra::ntt::{NttDomain, NttOperatorOptimized};
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;

type Zq17 = Zq<17>;

/// Pads a coefficient vector to length `n` with zeros for comparison.
fn padded(v: Vec<Zq17>, n: usize) -> Vec<Zq17> {
    v.into_iter()
        .chain(std::iter::repeat(Zq17::ZERO))
        .take(n)
        .collect()
}

fn main() {
    // ------------------------------------------------------------------
    // L0: scalar ring arithmetic
    // ------------------------------------------------------------------
    let a = Zq17::new(12);
    let b = Zq17::new(7);
    println!("12 + 7  = {}", (a + b).centered()); // 2
    println!("12 - 7  = {}", (a - b).centered()); // 5
    println!("12 * 7  = {}", (a * b).centered()); // 16
    println!("7^-1    = {}", b.inverse().unwrap().centered()); // 5 (7*5=35≡1)
    println!("centered(16) = {}", Zq17::new(16).centered()); // -1

    // ------------------------------------------------------------------
    // L2: negacyclic ring R_17[X]/(X^8+1), so X^8 = -1
    // ------------------------------------------------------------------
    // (1 + x) * (1 - x) = 1 - x^2
    let one_minus_x2: Vec<Zq17> = [1, 0, 16, 0, 0, 0, 0, 0]
        .iter()
        .map(|&c| Zq17::new(c))
        .collect();
    let p = PolyRing::<Zq17, 8>::from_coefficients(vec![Zq17::ONE, Zq17::ONE]);
    let q = PolyRing::from_coefficients(vec![Zq17::ONE, Zq17::new(16)]); // 1 - x
    assert_eq!(padded((p * q).coefficients(), 8), one_minus_x2);
    println!("(1+x)(1-x) = 1 - x^2   ✓");

    // x^7 * x wraps to -1 in the negacyclic ring.
    let x7 = PolyRing::<Zq17, 8>::from_coefficients(
        (0..8)
            .map(|i| if i == 7 { Zq17::ONE } else { Zq17::ZERO })
            .collect(),
    );
    let minus_one = x7 * PolyRing::from_coefficients(vec![Zq17::ZERO, Zq17::ONE]);
    assert_eq!(padded(minus_one.coefficients(), 8)[0], Zq17::new(16));
    println!("x^7 * x = -1 (negacyclic wrap)   ✓");

    // ------------------------------------------------------------------
    // L1: the NTT-domain view — transform once, multiply pointwise
    // ------------------------------------------------------------------
    type ZqD = Zq<8380417>;
    type Rq = PolyRing<ZqD, 256>;
    let op = NttOperatorOptimized::<ZqD, 256>::new();

    let f = Rq::from_coefficients((0..256).map(|i| ZqD::new(i as u64 % 941 + 1)).collect());
    let g = Rq::from_coefficients(
        (0..256)
            .map(|i| ZqD::new((i * i) as u64 % 941 + 1))
            .collect(),
    );

    let direct = f.clone() * g.clone(); // NTT under the hood

    let f_hat = f.to_ntt(&op);
    let g_hat = g.to_ntt(&op);
    let product_hat = f_hat.mul(&g_hat);
    let roundtrip = Rq::from_ntt(product_hat, &op);
    assert_eq!(direct, roundtrip);
    println!("R_q mul == NTT-domain pointwise mul (n=256, q=8380417)   ✓");

    // The transform is an involution: from_ntt(to_ntt(f)) == f.
    assert_eq!(Rq::from_ntt(f.to_ntt(&op), &op), f);
    println!("from_ntt ∘ to_ntt = identity   ✓");

    // A small NttDomain value round-trips through add/sub too.
    let u = NttDomain::<ZqD, 256>::zero();
    let _ = u.add(&u).sub(&u);
    println!("NttDomain ring ops OK");
}
