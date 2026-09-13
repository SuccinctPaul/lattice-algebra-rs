//! Criterion benchmarks for Falcon key generation, signing and verification.
//!
//! Run with: `cargo bench -p lattice-pqc -- falcon`
//!
//! Note: key generation and signing run on the reference's emulated
//! floating point (integer soft-float), which is deliberately slow but
//! bit-exact; expect multi-second benchmarks.

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pqc::falcon::{falcon1024, falcon512};

fn bench_falcon(c: &mut Criterion) {
    let mut group = c.benchmark_group("falcon");

    let d = [42u8; 48];
    let nonce = [7u8; 40];
    let sig_seed = [9u8; 48];
    let msg = b"falcon benchmark message";

    macro_rules! bench_set {
        ($name:literal, $api:ident) => {{
            let (sk, pk) = $api::keygen(&d);
            let esig = $api::sign(&sk, msg, &nonce, &sig_seed);
            assert!($api::verify(&pk, msg, &nonce, &esig));

            group.bench_function(concat!($name, "_keygen"), |bench| {
                bench.iter(|| $api::keygen(black_box(&d)))
            });
            group.bench_function(concat!($name, "_sign"), |bench| {
                bench.iter(|| $api::sign(black_box(&sk), msg, &nonce, &sig_seed))
            });
            group.bench_function(concat!($name, "_verify"), |bench| {
                bench
                    .iter(|| $api::verify(black_box(&pk), msg, black_box(&nonce), black_box(&esig)))
            });
        }};
    }

    bench_set!("falcon512", falcon512);
    bench_set!("falcon1024", falcon1024);

    group.finish();
}

criterion_group!(benches, bench_falcon);
criterion_main!(benches);
