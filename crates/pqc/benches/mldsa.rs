//! Criterion benchmarks for ML-DSA key generation, signing and verification
//! across all three parameter sets.
//!
//! Run with: `cargo bench -p lattice-pqc`
//! One set only: `cargo bench -p lattice-pqc -- mldsa65`

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pqc::mldsa::{mldsa_44, mldsa_65, mldsa_87};

fn bench_mldsa(c: &mut Criterion) {
    let mut group = c.benchmark_group("mldsa");

    let seed = [42u8; 32];
    let ctx = b"bench";
    let msg = b"benchmark message for ML-DSA";
    let rnd = [7u8; 32];

    macro_rules! bench_set {
        ($name:literal, $api:ident) => {{
            let (sk, vk) = $api::keygen(&seed);
            let sigma = $api::sign_deterministic(&sk, ctx, msg);
            assert!($api::verify(&vk, ctx, msg, &sigma));

            group.bench_function(concat!($name, "_keygen"), |bench| {
                bench.iter(|| $api::keygen(black_box(&seed)))
            });
            group.bench_function(concat!($name, "_sign_deterministic"), |bench| {
                bench.iter(|| $api::sign_deterministic(black_box(&sk), ctx, msg))
            });
            group.bench_function(concat!($name, "_sign_randomized"), |bench| {
                bench.iter(|| $api::sign_with_randomness(black_box(&sk), ctx, msg, black_box(&rnd)))
            });
            group.bench_function(concat!($name, "_verify"), |bench| {
                bench.iter(|| $api::verify(black_box(&vk), ctx, msg, black_box(&sigma)))
            });
        }};
    }

    bench_set!("mldsa44", mldsa_44);
    bench_set!("mldsa65", mldsa_65);
    bench_set!("mldsa87", mldsa_87);

    group.finish();
}

criterion_group!(benches, bench_mldsa);
criterion_main!(benches);
