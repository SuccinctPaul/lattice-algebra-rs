#![allow(missing_docs)] // benchmark harness: criterion groups need no API docs
//! Criterion benchmarks for the [`algebra::simd`] lane kernels against plain
//! scalar loops (`simd` feature).
//!
//! Run with: `cargo bench -p lattice-algebra --features simd -- simd`

use algebra::simd::{mod_add_assign_u32, wrapping_axpy_u16, wrapping_dot_u16};
use criterion::{black_box, criterion_group, criterion_main, Criterion, Throughput};

/// Deterministic filler so every iteration sees identical (branch-free) data.
fn fill_u16(seed: u64, len: usize) -> Vec<u16> {
    let mut s = seed | 1;
    (0..len)
        .map(|_| {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s as u16
        })
        .collect()
}

fn fill_u32(seed: u64, len: usize, q: u32) -> Vec<u32> {
    fill_u16(seed, len)
        .into_iter()
        .map(|v| (v as u32) % q)
        .collect()
}

fn bench_simd(c: &mut Criterion) {
    let mut group = c.benchmark_group("simd");
    let n = 1344; // FrodoKEM-1344 row length: the heaviest in-repo consumer

    let a = fill_u16(1, n);
    let b = fill_u16(2, n);
    group.throughput(Throughput::Elements(n as u64));
    group.bench_function("wrapping_dot_u16_1344", |bench| {
        bench.iter(|| black_box(wrapping_dot_u16(black_box(&a), black_box(&b))))
    });

    let mut acc = fill_u16(3, n);
    group.bench_function("wrapping_axpy_u16_1344", |bench| {
        bench.iter(|| {
            wrapping_axpy_u16(black_box(&mut acc), black_box(&a), 0xBEEF);
        })
    });

    let q = 8380417u32;
    let x = fill_u32(4, 256, q);
    let y = fill_u32(5, 256, q);
    group.throughput(Throughput::Elements(256));
    group.bench_function("mod_add_assign_u32_256_mldsa_q", |bench| {
        let mut v = x.clone();
        bench.iter(|| mod_add_assign_u32(black_box(&mut v), black_box(&y), q))
    });

    group.finish();
}

criterion_group!(benches, bench_simd);
criterion_main!(benches);
