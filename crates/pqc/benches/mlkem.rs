#![allow(missing_docs)] // benchmark harness: criterion groups need no API docs
//! Criterion benchmarks for ML-KEM key generation, encapsulation and
//! decapsulation across all three parameter sets.
//!
//! Run with: `cargo bench -p lattice-pqc`
//! One set only: `cargo bench -p lattice-pqc -- mlkem768`

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pqc::mlkem::{mlkem_1024, mlkem_512, mlkem_768};

fn bench_mlkem(c: &mut Criterion) {
    let mut group = c.benchmark_group("mlkem");

    let d = [42u8; 32];
    let z = [7u8; 32];
    let m = [9u8; 32];

    macro_rules! bench_set {
        ($name:literal, $api:ident) => {{
            let (dk, ek) = $api::keygen(&d, &z);
            let (ciphertext, ss) = $api::encapsulate(&ek, &m);
            assert_eq!(
                $api::decapsulate(&dk, &ciphertext).as_bytes(),
                ss.as_bytes()
            );

            group.bench_function(concat!($name, "_keygen"), |bench| {
                bench.iter(|| $api::keygen(black_box(&d), black_box(&z)))
            });
            group.bench_function(concat!($name, "_encaps"), |bench| {
                bench.iter(|| $api::encapsulate(black_box(&ek), black_box(&m)))
            });
            group.bench_function(concat!($name, "_decaps"), |bench| {
                bench.iter(|| $api::decapsulate(black_box(&dk), black_box(&ciphertext)))
            });
        }};
    }

    bench_set!("mlkem512", mlkem_512);
    bench_set!("mlkem768", mlkem_768);
    bench_set!("mlkem1024", mlkem_1024);

    group.finish();
}

criterion_group!(benches, bench_mlkem);
criterion_main!(benches);
