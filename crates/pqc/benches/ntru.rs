#![allow(missing_docs)] // benchmark harness: criterion groups need no API docs
//! Criterion benchmarks for NTRU key generation, encapsulation and
//! decapsulation across all five round-3 parameter sets.
//!
//! Run with: `cargo bench -p lattice-pqc -- ntru`

use criterion::{black_box, criterion_group, criterion_main, Criterion};
use pqc::ntru::params::NtruParams;
use pqc::ntru::{ntruhps2048677, ntruhps2048821, ntruhps40961229, ntruhps4096821, ntruhrss701};

fn bench_ntru(c: &mut Criterion) {
    let mut group = c.benchmark_group("ntru");

    fn fresh_bytes(tag: u8, len: usize) -> Vec<u8> {
        (0..len)
            .map(|i| tag.wrapping_mul(31).wrapping_add(i as u8))
            .collect()
    }

    macro_rules! bench_set {
        ($name:literal, $params:ty, $api:ident) => {{
            let fg_len = <$params as NtruParams>::SAMPLE_FG_BYTES;
            let rm_len = <$params as NtruParams>::SAMPLE_RM_BYTES;
            let seed = fresh_bytes(1, fg_len);
            let prf_key = [2u8; 32];
            let rm = fresh_bytes(3, rm_len);

            let (sk, pk) = $api::keygen(&seed, &prf_key).expect("well-sized");
            let (ciphertext, k) = $api::encapsulate(&pk, &rm).expect("well-sized");
            assert_eq!($api::decapsulate(&sk, &ciphertext).as_bytes(), k.as_bytes());

            group.bench_function(concat!($name, "_keygen"), |bench| {
                bench.iter(|| $api::keygen(black_box(&seed), black_box(&prf_key)))
            });
            group.bench_function(concat!($name, "_encaps"), |bench| {
                bench.iter(|| $api::encapsulate(black_box(&pk), black_box(&rm)))
            });
            group.bench_function(concat!($name, "_decaps"), |bench| {
                bench.iter(|| $api::decapsulate(black_box(&sk), black_box(&ciphertext)))
            });
        }};
    }

    bench_set!(
        "ntruhps2048677",
        pqc::ntru::params::NtruHps2048677,
        ntruhps2048677
    );
    bench_set!(
        "ntruhps2048821",
        pqc::ntru::params::NtruHps2048821,
        ntruhps2048821
    );
    bench_set!(
        "ntruhps4096821",
        pqc::ntru::params::NtruHps4096821,
        ntruhps4096821
    );
    bench_set!(
        "ntruhps40961229",
        pqc::ntru::params::NtruHps40961229,
        ntruhps40961229
    );
    bench_set!("ntruhrss701", pqc::ntru::params::NtruHrss701, ntruhrss701);

    group.finish();
}

criterion_group!(benches, bench_ntru);
criterion_main!(benches);
