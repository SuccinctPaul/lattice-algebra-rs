#![allow(missing_docs)] // benchmark harness: criterion groups need no API docs
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
use zk::commitment::ajtai::{CommitmentKey, LatticeCommitment, Z1Instance, RING_DIM};
use zk::folding::nova::{fold, verify_folded, FoldKey, RelaxedInstance};
use zk::foundation::encoding::ring_from_u32;
use zk::instance::r1cs::gen_toy_instance;
use zk::opening::{prove, verify, Z2CommitKey};
use zk::sigma::{fs_prove, fs_verify};
use zk::sumcheck::{self, RoundChallenger};

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

    // Deterministic counter challenger: identical derivation on both sides.
    struct CounterChallenger {
        cnt: u64,
    }
    impl RoundChallenger<Z1Ring> for CounterChallenger {
        fn round_challenge(&mut self, _h0: &Z1Ring, _h1: &Z1Ring) -> Z1Ring {
            self.cnt += 1;
            Z1Ring::new(self.cnt)
        }
    }

    let proof = sumcheck::prove::<Z1Ring, G>(&table, &mut CounterChallenger { cnt: 0 });

    group.bench_function("prove_2pow8", |bench| {
        bench.iter(|| {
            sumcheck::prove::<Z1Ring, G>(black_box(&table), &mut CounterChallenger { cnt: 0 })
        })
    });
    group.bench_function("verify_2pow8", |bench| {
        bench.iter(|| {
            sumcheck::verify(
                black_box(&proof),
                black_box(claimed),
                &mut CounterChallenger { cnt: 0 },
            )
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

    let make = |z: &[zk::instance::ring::Z2Ring]| RelaxedInstance {
        z: z.to_vec(),
        error: zk::opening::constraint_residuals(&r1cs, z),
        c_z: key.commit_witness(z),
        c_e: key.commit_error(&zk::opening::constraint_residuals(&r1cs, z)),
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

fn bench_pcs(c: &mut Criterion) {
    let mut group = c.benchmark_group("pcs_z7");
    use zk::foundation::sampling::from_centered;
    use zk::pcs::{self, greyhound};

    let key = greyhound::GreyhoundKey::setup(&seed32(b"zk-bench-pcs"));
    let f: Vec<pcs::RingElt> = (0..pcs::N_DEG)
        .map(|i| {
            let coeffs: Vec<_> = (0..pcs::DIM)
                .map(|j| from_centered::<pcs::Z1Coeff>(((i * 7 + j) % 9) as i64 - 4))
                .collect();
            pcs::RingElt::from_coefficients(coeffs)
        })
        .collect();
    let mut x_coeffs = [0u32; pcs::DIM];
    x_coeffs[0] = 424_242;
    let x = ring_from_u32::<pcs::Z1Coeff, { pcs::DIM }>(&x_coeffs);
    let com = greyhound::commit(&key, &f).expect("canonical length");
    let (y, proof) = greyhound::open(&key, &f, &x).expect("canonical length");
    assert!(greyhound::verify(&key, &com, &x, &y, &proof).is_ok());

    group.bench_function("commit_n64", |bench| {
        bench.iter(|| greyhound::commit(black_box(&key), black_box(&f)).expect("canonical length"))
    });
    group.bench_function("open_n64", |bench| {
        bench.iter(|| {
            greyhound::open(black_box(&key), black_box(&f), black_box(&x))
                .expect("canonical length")
        })
    });
    group.bench_function("verify_n64", |bench| {
        bench.iter(|| {
            assert!(greyhound::verify(
                black_box(&key),
                black_box(&com),
                black_box(&x),
                black_box(&y),
                black_box(&proof)
            )
            .is_ok())
        })
    });

    // Batched opening: four polynomials at one shared point.
    use zk::pcs::batched;
    let polys: Vec<Vec<pcs::RingElt>> = (0..4)
        .map(|p| {
            (0..pcs::N_DEG)
                .map(|i| {
                    let coeffs: Vec<_> = (0..pcs::DIM)
                        .map(|j| {
                            from_centered::<pcs::Z1Coeff>(
                                ((p as i64 * 11 + i as i64 * 7 + j as i64) % 9) - 4,
                            )
                        })
                        .collect();
                    pcs::RingElt::from_coefficients(coeffs)
                })
                .collect()
        })
        .collect();
    let refs: Vec<&[pcs::RingElt]> = polys.iter().map(|f| f.as_slice()).collect();
    let coms: Vec<greyhound::PolyCommitment> = polys
        .iter()
        .map(|f| greyhound::commit(&key, f).expect("canonical length"))
        .collect();
    let (ys, batched_proof) = batched::open_batch(&key, &refs, &x).expect("canonical length");
    assert!(batched::verify_batch(&key, &coms, &x, &ys, &batched_proof).is_ok());

    group.bench_function("batched_open_k4", |bench| {
        bench.iter(|| {
            batched::open_batch(black_box(&key), black_box(&refs), black_box(&x))
                .expect("canonical length")
        })
    });
    group.bench_function("batched_verify_k4", |bench| {
        bench.iter(|| {
            assert!(batched::verify_batch(
                black_box(&key),
                black_box(&coms),
                black_box(&x),
                black_box(&ys),
                black_box(&batched_proof)
            )
            .is_ok())
        })
    });

    group.finish();
}

fn bench_batched_sumcheck(c: &mut Criterion) {
    let mut group = c.benchmark_group("pi_batch_z3");
    use algebra::ring::MatrixElement;
    use zk::sumcheck::batch::{prove_batched, verify_batched, BatchClaim};
    use zk::sumcheck::FsChallenger;

    const G: usize = 10;
    type Rq = Zq<8380417>;

    let tables: Vec<Vec<Rq>> = (0..4)
        .map(|k| {
            (0..1 << G)
                .map(|i| Rq::from((k as u64 * 1000 + (i * 37 % 97) as u64) % 8_380_417))
                .collect()
        })
        .collect();
    let claims: Vec<BatchClaim<'_, Rq, G>> = tables
        .iter()
        .map(|t| BatchClaim {
            table: t,
            eq_point: None,
            claimed: t.iter().fold(Rq::zero(), |a, b| a + *b),
        })
        .collect();
    let claimed_list: Vec<Rq> = claims.iter().map(|c| c.claimed).collect();

    let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"zk-bench-pi-batch");
    let proof = prove_batched::<Rq, G>(&claims, &mut ch);
    let mut chv = FsChallenger::<Shake128Xof, Rq>::new(b"zk-bench-pi-batch");
    assert!(verify_batched::<Rq, G>(&proof, &claimed_list, &mut chv).is_some());

    group.bench_function("prove_k4_g10", |bench| {
        bench.iter(|| {
            let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"zk-bench-pi-batch");
            prove_batched::<Rq, G>(black_box(&claims), &mut ch)
        })
    });
    group.bench_function("verify_k4_g10", |bench| {
        bench.iter(|| {
            let mut ch = FsChallenger::<Shake128Xof, Rq>::new(b"zk-bench-pi-batch");
            assert!(
                verify_batched::<Rq, G>(black_box(&proof), black_box(&claimed_list), &mut ch)
                    .is_some()
            )
        })
    });

    group.finish();
}

criterion_group!(
    benches,
    bench_sigma,
    bench_z2,
    bench_sumcheck,
    bench_fold,
    bench_pcs,
    bench_batched_sumcheck
);
criterion_main!(benches);
