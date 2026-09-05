//! Criterion benchmarks for the ZK protocol stack: Σ-protocol NIZK (Z1),
//! batched ring opening (Z2), multilinear sumcheck (Z3) and folding (Z4).
//!
//! Run with: `cargo bench -p lattice-zk`
//! One group only: `cargo bench -p lattice-zk -- z2`

use algebra::crypto::xof::{Shake128Xof, Xof};
use algebra::module::ModuleVector;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use criterion::{black_box, criterion_group, criterion_main, Criterion};
use zk::protocols::commitment::{CommitmentKey, LatticeCommitment, Z1Instance, RING_DIM};
use zk::protocols::fold::{fold, verify_folded, FoldKey, RelaxedInstance};
use zk::protocols::sigma::{fs_prove, fs_verify};
use zk::protocols::sumcheck;
use zk::protocols::z2::{prove, verify, Z2CommitKey};
use zk::protocols::z2_ring::{gen_toy_instance, ring_from_u32};

type Z1Ring = Zq<8380417>;
const SIGMA_K: usize = 4;
const SIGMA_L: usize = 3;

fn seed32(tag: &[u8]) -> [u8; 32] {
    let mut s = [0u8; 32];
    s[..tag.len()].copy_from_slice(tag);
    s
}

fn bench_sigma(c: &mut Criterion) {
    let mut group = c.benchmark_group("sigma_z1");

    let key: CommitmentKey<Z1Instance, SIGMA_K, SIGMA_L, RING_DIM> =
        CommitmentKey::setup(&seed32(b"zk-bench-sigma"));
    let s: ModuleVector<Z1Ring, SIGMA_L, RING_DIM> = ModuleVector::from_fn(|i| {
        PolyRing::from_coefficients(
            (0..RING_DIM)
                .map(|j| Z1Ring::new(((((i * 3 + j) % 9) as i64) - 4).rem_euclid(8_380_417) as u64))
                .collect(),
        )
    });
    let t = key.commit(&s);
    let proof = fs_prove::<Z1Instance, SIGMA_K, SIGMA_L, RING_DIM>(&key, &s, &t, &[0x11u8; 32])
        .expect("honest witness must prove");

    group.bench_function("fs_prove_4x3", |bench| {
        bench.iter(|| {
            fs_prove::<Z1Instance, SIGMA_K, SIGMA_L, RING_DIM>(
                black_box(&key),
                black_box(&s),
                black_box(&t),
                black_box(&[0x11u8; 32]),
            )
            .expect("honest witness must prove")
        })
    });
    group.bench_function("fs_verify_4x3", |bench| {
        bench.iter(|| {
            fs_verify::<Z1Instance, SIGMA_K, SIGMA_L, RING_DIM>(
                black_box(&key),
                black_box(&t),
                black_box(&proof),
            )
        })
    });

    group.finish();
}

fn bench_z2(c: &mut Criterion) {
    let mut group = c.benchmark_group("z2_batched_opening");

    let (r1cs, z) = gen_toy_instance(&seed32(b"zk-bench-instance"), 512, 2);
    let key_seed = seed32(b"zk-bench-key");
    let domain = seed32(b"zk-bench-domain");
    let key = Z2CommitKey::setup(&key_seed);
    let (c_commit, proof) = prove(&key, &key_seed, &domain, &r1cs, &z, &[9u8; 32]);
    assert!(verify(&key, &key_seed, &domain, &r1cs, &c_commit, &proof));

    group.bench_function("prove_512_gates", |bench| {
        bench.iter(|| {
            prove(
                black_box(&key),
                &key_seed,
                &domain,
                black_box(&r1cs),
                black_box(&z),
                &[9u8; 32],
            )
        })
    });
    group.bench_function("verify_512_gates", |bench| {
        bench.iter(|| {
            verify(
                black_box(&key),
                &key_seed,
                &domain,
                black_box(&r1cs),
                black_box(&c_commit),
                black_box(&proof),
            )
        })
    });

    group.finish();
}

fn bench_sumcheck(c: &mut Criterion) {
    let mut group = c.benchmark_group("sumcheck");
    const G: usize = 8;

    // A deterministic "table" the prover claims a sum over.
    let mut x = zk_bench_xof();
    let table: Vec<Z1Ring> = (0..1 << G).map(|_| x.squeeze_z1()).collect();
    let claimed: Z1Ring = table.iter().cloned().sum();

    let mut cnt = 0u64;
    let proof = sumcheck::prove::<Z1Ring, G>(&table, &mut || {
        cnt += 1;
        Z1Ring::new(cnt)
    });

    group.bench_function("prove_2pow8", |bench| {
        let mut cnt = 0u64;
        bench.iter(|| {
            sumcheck::prove::<Z1Ring, G>(black_box(&table), &mut || {
                cnt += 1;
                Z1Ring::new(cnt)
            })
        })
    });
    group.bench_function("verify_2pow8", |bench| {
        let mut cnt = 0u64;
        bench.iter(|| {
            sumcheck::verify(black_box(&proof), black_box(claimed), &mut || {
                cnt += 1;
                Z1Ring::new(cnt)
            })
        })
    });

    group.finish();
}

struct BenchXof(Shake128Xof);
impl BenchXof {
    fn squeeze_z1(&mut self) -> Z1Ring {
        let mut buf = [0u8; 4];
        self.0.squeeze(&mut buf);
        let v = u32::from_le_bytes(buf) % 8_380_417;
        Z1Ring::new(v as u64)
    }
}

fn zk_bench_xof() -> BenchXof {
    BenchXof(Shake128Xof::new(b"zk-bench-table"))
}

fn bench_fold(c: &mut Criterion) {
    let mut group = c.benchmark_group("fold_z4");
    const N: usize = 8;
    const M: usize = 4;
    const GATES: usize = 64;

    let key = FoldKey::<N, M, GATES>::setup(&seed32(b"zk-bench-fold"));
    let (r1cs, z1) = gen_toy_instance(&seed32(b"zk-bench-fold-i1"), GATES, M);
    let (_r2, z2) = gen_toy_instance(&seed32(b"zk-bench-fold-i2"), GATES, M);

    let make = |z: &[zk::protocols::z2_ring::Z2Ring]| RelaxedInstance {
        z: z.to_vec(),
        error: zk::protocols::z2::constraint_residuals(&r1cs, z),
        c_z: key.commit_witness(z),
        c_e: key.commit_error(&zk::protocols::z2::constraint_residuals(&r1cs, z)),
    };
    let i1 = make(&z1);
    let i2 = make(&z2);

    let mut r_coeffs = [0u32; 64];
    r_coeffs[0] = 0xABCD_1234;
    r_coeffs[1] = 0x5678_9ABC;
    let r = ring_from_u32(&r_coeffs);

    let folded = fold(&key, &r1cs, &i1, &i2, r.clone());
    assert!(verify_folded(&key, &r1cs, &folded));

    group.bench_function("fold_64_gates", |bench| {
        bench.iter(|| {
            fold(
                black_box(&key),
                black_box(&r1cs),
                black_box(&i1),
                black_box(&i2),
                r.clone(),
            )
        })
    });
    group.bench_function("verify_folded_64_gates", |bench| {
        bench.iter(|| verify_folded(black_box(&key), black_box(&r1cs), black_box(&folded)))
    });

    group.finish();
}

criterion_group!(benches, bench_sigma, bench_z2, bench_sumcheck, bench_fold);
criterion_main!(benches);
