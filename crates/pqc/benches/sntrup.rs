#![allow(missing_docs)] // benchmark harness: criterion groups need no API docs
//! Criterion benchmarks for Streamlined NTRU Prime key generation,
//! encapsulation and decapsulation across all six sizes.
//!
//! Run with: `cargo bench -p lattice-pqc -- sntrup`

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pqc::sntrup::params::SntrupParams;
use pqc::sntrup::{sntrup1013, sntrup1277, sntrup653, sntrup761, sntrup857, sntrup953};

fn bench_sntrup(c: &mut Criterion) {
    let mut group = c.benchmark_group("sntrup");

    fn fresh_bytes(tag: u8, len: usize) -> Vec<u8> {
        (0..len)
            .map(|i| tag.wrapping_mul(31).wrapping_add(i as u8))
            .collect()
    }

    macro_rules! bench_set {
        ($name:literal, $params:ty, $api:ident) => {{
            let p = <$params as SntrupParams>::P;
            let small = <$params as SntrupParams>::SMALL_BYTES;
            // A uniform ternary g is invertible with probability ≈ 2/3;
            // retry like the reference's KeyGen loop.
            let (sk, pk) = loop {
                let g_random = fresh_bytes(1, 4 * p);
                let f_random = fresh_bytes(2, 4 * p);
                let rho = fresh_bytes(3, small);
                if let Ok(keys) = $api::keygen(&g_random, &f_random, &rho) {
                    break keys;
                }
            };
            let r_random = fresh_bytes(4, 4 * p);
            let (ciphertext, k) = $api::encapsulate(&pk, &r_random).expect("well-sized");
            assert_eq!($api::decapsulate(&sk, &ciphertext).as_bytes(), k.as_bytes());

            group.bench_function(concat!($name, "_keygen"), |bench| {
                // Retry inside iter: an invertibility resample is part of
                // honest keygen cost.
                bench.iter(|| {
                    let g_random = fresh_bytes(1, 4 * p);
                    let f_random = fresh_bytes(2, 4 * p);
                    let rho = fresh_bytes(3, small);
                    loop {
                        if let Ok(keys) = $api::keygen(
                            black_box(&g_random),
                            black_box(&f_random),
                            black_box(&rho),
                        ) {
                            break keys;
                        }
                    }
                })
            });
            group.bench_function(concat!($name, "_encaps"), |bench| {
                bench.iter(|| $api::encapsulate(black_box(&pk), black_box(&r_random)))
            });
            group.bench_function(concat!($name, "_decaps"), |bench| {
                bench.iter(|| $api::decapsulate(black_box(&sk), black_box(&ciphertext)))
            });
        }};
    }

    bench_set!("sntrup653", pqc::sntrup::params::Sntrup653, sntrup653);
    bench_set!("sntrup761", pqc::sntrup::params::Sntrup761, sntrup761);
    bench_set!("sntrup857", pqc::sntrup::params::Sntrup857, sntrup857);
    bench_set!("sntrup953", pqc::sntrup::params::Sntrup953, sntrup953);
    bench_set!("sntrup1013", pqc::sntrup::params::Sntrup1013, sntrup1013);
    bench_set!("sntrup1277", pqc::sntrup::params::Sntrup1277, sntrup1277);

    group.finish();
}

criterion_group!(benches, bench_sntrup);
criterion_main!(benches);
