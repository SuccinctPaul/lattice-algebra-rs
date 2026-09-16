#![allow(missing_docs)] // benchmark harness: criterion groups need no API docs
//! Criterion benchmarks for FrodoKEM key generation, encapsulation and
//! decapsulation (AES128 `A` variants; the SHAKE128 variants share the
//! arithmetic and differ only in the `A` expansion).
//!
//! Run with: `cargo bench -p lattice-pqc -- frodo`

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pqc::frodo::params::FrodoParams;
use pqc::frodo::{frodo1344, frodo640, frodo976};

fn bench_frodo(c: &mut Criterion) {
    let mut group = c.benchmark_group("frodo");

    /// Deterministic pseudo-random byte fill (benchmarks need only
    /// well-sized inputs, not statistical randomness).
    fn fresh_bytes(tag: u8, len: usize) -> Vec<u8> {
        (0..len)
            .map(|i| tag.wrapping_mul(31).wrapping_add(i as u8))
            .collect()
    }

    macro_rules! bench_set {
        ($name:literal, $params:ty, $api:ident) => {{
            let ss = <$params as FrodoParams>::SS_BYTES;
            let mu_len = <$params as FrodoParams>::MU_BYTES;
            let s = fresh_bytes(1, ss);
            let seed_se = fresh_bytes(2, ss);
            let z = [3u8; 16];
            let mu = fresh_bytes(9, mu_len);

            let (sk, ek) = $api::keygen(&s, &seed_se, &z).expect("well-sized");
            let (ciphertext, k) = $api::encapsulate(&ek, &mu).expect("well-sized");
            assert_eq!($api::decapsulate(&sk, &ciphertext).as_bytes(), k.as_bytes());

            group.bench_function(concat!($name, "_keygen"), |bench| {
                bench.iter(|| $api::keygen(black_box(&s), black_box(&seed_se), black_box(&z)))
            });
            group.bench_function(concat!($name, "_encaps"), |bench| {
                bench.iter(|| $api::encapsulate(black_box(&ek), black_box(&mu)))
            });
            group.bench_function(concat!($name, "_decaps"), |bench| {
                bench.iter(|| $api::decapsulate(black_box(&sk), black_box(&ciphertext)))
            });
        }};
    }

    bench_set!("frodo640", pqc::frodo::params::Frodo640, frodo640);
    bench_set!("frodo976", pqc::frodo::params::Frodo976, frodo976);
    bench_set!("frodo1344", pqc::frodo::params::Frodo1344, frodo1344);

    group.finish();
}

criterion_group!(benches, bench_frodo);
criterion_main!(benches);
