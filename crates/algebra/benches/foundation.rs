//! Criterion benchmarks for the algebraic foundation.
//!
//! Run with: `cargo bench -p lattice-algebra`
//! Select a group: `cargo bench -p lattice-algebra -- poly_mul`

use algebra::crypto::sampling::{sample_cbd, sample_rej_bounded, BitStream, DiscreteGaussian};
use algebra::crypto::xof::{shortcuts::h256, Shake128Xof, Xof};
use algebra::module::{ModuleMatrix, ModuleVector};
use algebra::ntt::NttOperatorOptimized;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use std::hint::black_box as std_black_box;

type ZqD = Zq<8380417>;
type Rq256 = PolyRing<ZqD, 256>;

fn bench_poly_mul(c: &mut Criterion) {
    let mut group = c.benchmark_group("poly_mul_n256_q8380417");

    let a: Rq256 = PolyRing::from_coefficients((0..256).map(|i| ZqD::new(i as u64 + 1)).collect());
    let b: Rq256 =
        PolyRing::from_coefficients((0..256).map(|i| ZqD::new((i * 3) as u64 + 2)).collect());

    // The production path: negacyclic NTT multiplication.
    group.bench_function("polyring_ntt", |bench| {
        bench.iter(|| black_box(&a).clone() * black_box(&b).clone())
    });

    // Reference: O(n²) schoolbook with the x^n ≡ -1 wrap.
    group.bench_function("naive_schoolbook", |bench| {
        bench.iter(|| {
            let av = a.coefficients();
            let bv = b.coefficients();
            let mut acc = vec![ZqD::ZERO; 256];
            for (i, &x) in av.iter().enumerate() {
                for (j, &y) in bv.iter().enumerate() {
                    let k = i + j;
                    let prod = x * y;
                    if k < 256 {
                        acc[k] += prod;
                    } else {
                        acc[k - 256] -= prod; // negacyclic wrap
                    }
                }
            }
            std_black_box(acc)
        })
    });

    group.finish();
}

fn bench_module_matvec(c: &mut Criterion) {
    // ML-DSA-65 shape: Â is 4×5 over R_q with n = 256.
    let mut group = c.benchmark_group("matvec_4x5_n256");

    let a: ModuleMatrix<ZqD, 4, 5, 256> = ModuleMatrix::from_fn(|i, j| {
        PolyRing::from_coefficients(vec![ZqD::new((i * 7 + j * 13 + 1) as u64); 256])
    });
    let v: ModuleVector<ZqD, 5, 256> =
        ModuleVector::from_fn(|i| PolyRing::from_coefficients(vec![ZqD::new(i as u64 + 1); 256]));

    group.bench_function("coefficient_domain", |bench| {
        bench.iter(|| black_box(&a).mul_vec(black_box(&v)))
    });

    let op = NttOperatorOptimized::<ZqD, 256>::new();
    let a_hat = a.to_ntt(&op);
    let v_hat = v.to_ntt(&op);
    group.bench_function("ntt_domain", |bench| {
        bench.iter(|| black_box(&a_hat).mul_vec_ntt(black_box(&v_hat)))
    });

    group.finish();
}

fn bench_samplers(c: &mut Criterion) {
    let mut group = c.benchmark_group("sampling");
    const N: usize = 256;

    group.bench_function("rej_bounded_eta2_x256", |bench| {
        let mut x = Shake128Xof::new(b"bench-rej");
        let mut s = BitStream::new(&mut x);
        bench.iter(|| {
            for _ in 0..N {
                std_black_box(sample_rej_bounded::<ZqD>(&mut s, 2));
            }
        })
    });

    group.bench_function("cbd_eta2_x256", |bench| {
        let mut x = Shake128Xof::new(b"bench-cbd");
        let mut s = BitStream::new(&mut x);
        bench.iter(|| {
            for _ in 0..N {
                std_black_box(sample_cbd::<ZqD>(&mut s, 2));
            }
        })
    });

    group.bench_function("gaussian_sigma3.2_x256", |bench| {
        let g = DiscreteGaussian::new(3.2);
        let mut x = Shake128Xof::new(b"bench-gauss");
        let mut s = BitStream::new(&mut x);
        bench.iter(|| g.sample_many(&mut s, N))
    });

    group.bench_function("gaussian_cdt_build", |bench| {
        bench.iter(|| DiscreteGaussian::new(black_box(3.2)))
    });

    group.finish();
}

fn bench_xof(c: &mut Criterion) {
    let mut group = c.benchmark_group("xof");

    group.bench_function("shake128_absorb32_squeeze1k", |bench| {
        bench.iter(|| {
            let mut x = Shake128Xof::new(b"bench-xof");
            x.absorb(&[7u8; 32]);
            std_black_box(x.squeeze_vec(1024))
        })
    });

    group.bench_function("shake256_h256", |bench| {
        bench.iter(|| h256(black_box(b"bench-hash-input")))
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_poly_mul,
    bench_module_matvec,
    bench_samplers,
    bench_xof
);
criterion_main!(benches);
