#![allow(missing_docs)] // benchmark harness: criterion groups need no API docs
//! Criterion benchmarks for the rayon batch APIs (`parallel` feature):
//! sequential vs batched throughput at a fixed batch size.
//!
//! Run with: `cargo bench -p lattice-pqc --features parallel -- parallel`

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pqc::mldsa::mldsa_65;
use pqc::mlkem::mlkem_768;

const BATCH: usize = 32;

fn bench_batch(c: &mut Criterion) {
    let mut group = c.benchmark_group("parallel_batch");
    group.throughput(criterion::Throughput::Elements(BATCH as u64));

    // ML-DSA signing: the dominant batching target (signing is the slowest
    // symmetric operation of the two schemes here).
    let (sk, vk) = mldsa_65::keygen(&[42u8; 32]);
    let msgs: Vec<Vec<u8>> = (0..BATCH)
        .map(|i| {
            b"batch benchmark message"
                .iter()
                .copied()
                .chain((i as u8..).take(16))
                .collect()
        })
        .collect();
    let msg_refs: Vec<&[u8]> = msgs.iter().map(Vec::as_slice).collect();
    let ctx = b"bench";

    let sigs = mldsa_65::sign_deterministic_batch(&sk, ctx, &msg_refs);
    let sig_refs: Vec<&[u8]> = sigs.iter().map(Vec::as_slice).collect();
    assert!(mldsa_65::verify_batch(&vk, ctx, &msg_refs, &sig_refs)
        .iter()
        .all(|&v| v));

    group.bench_function("mldsa65_sign_sequential", |bench| {
        bench.iter(|| {
            for msg in &msg_refs {
                black_box(mldsa_65::sign_deterministic(&sk, ctx, msg));
            }
        })
    });
    group.bench_function("mldsa65_sign_batch", |bench| {
        bench.iter(|| black_box(mldsa_65::sign_deterministic_batch(&sk, ctx, &msg_refs)))
    });
    group.bench_function("mldsa65_verify_batch", |bench| {
        bench.iter(|| black_box(mldsa_65::verify_batch(&vk, ctx, &msg_refs, &sig_refs)))
    });

    // ML-KEM encapsulation batch.
    let (dk, ek) = mlkem_768::keygen(&[43u8; 32], &[44u8; 32]);
    let ms: Vec<[u8; 32]> = (0..BATCH).map(|i| [i as u8; 32]).collect();
    group.bench_function("mlkem768_encaps_batch", |bench| {
        bench.iter(|| black_box(mlkem_768::encapsulate_batch(&ek, &ms)))
    });
    group.bench_function("mlkem768_decaps_batch", |bench| {
        let cts: Vec<_> = ms
            .iter()
            .map(|m| mlkem_768::encapsulate(&ek, m))
            .map(|(ct, _)| ct)
            .collect();
        bench.iter(|| black_box(mlkem_768::decapsulate_batch(&dk, &cts)))
    });

    group.finish();
}

criterion_group!(benches, bench_batch);
criterion_main!(benches);
