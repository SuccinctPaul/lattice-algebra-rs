//! Cross-module contract tests: the crate exercised from the outside, the
//! way dependent crates (`lattice-pqc`, `lattice-zk`) use it. These pin the
//! invariants that the scheme layers rely on.

use algebra::crypto::sampling::{sample_cbd, sample_rej_bounded, BitStream, DiscreteGaussian};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::{Shake128Xof, Shake256Xof, Xof};
use algebra::module::{ModuleMatrix, ModuleMatrixNtt, ModuleVector};
use algebra::ntt::NttOperatorOptimized;
use algebra::poly::sparse::SparsePolynomial;
use algebra::ring::poly_ring::PolyRing;
use algebra::ring::traits::CenteredRing;
use algebra::ring::zq::Zq;
use algebra::ring::PolynomialQuotientRing;
use algebra::ring::Ring;

type ZqD = Zq<8380417>;

fn padded(mut v: Vec<u128>, n: usize) -> Vec<u128> {
    v.resize(n, 0);
    v
}

fn centered_u128(r: &ZqD) -> u128 {
    // Centered representative, folded back to a non-negative span.
    r.centered().rem_euclid(8_380_417) as u128
}

#[test]
fn ntt_mul_matches_negacyclic_schoolbook() {
    const N: usize = 16;
    for round in 0..4u64 {
        let a = PolyRing::<Zq<3329>, N>::from_coefficients(
            (0..N)
                .map(|i| Zq::<3329>::new((round * 31 + i as u64) % 3329))
                .collect(),
        );
        let b = PolyRing::<Zq<3329>, N>::from_coefficients(
            (0..N)
                .map(|i| Zq::<3329>::new((round * 17 + i as u64 * 5 + 1) % 3329))
                .collect(),
        );
        let got = (a.clone() * b.clone()).coefficients();
        let got = padded(got.iter().map(|c| c.to_u128()).collect(), N);

        let av = a.coefficients();
        let bv = b.coefficients();
        let mut want = vec![0u128; N];
        for (i, &x) in av.iter().enumerate() {
            for (j, &y) in bv.iter().enumerate() {
                let p = (x * y).to_u128();
                if i + j < N {
                    want[i + j] = (want[i + j] + p) % 3329;
                } else {
                    // x^N ≡ -1: subtract instead of add.
                    want[i + j - N] = (want[i + j - N] + 3329 - p) % 3329;
                }
            }
        }
        assert_eq!(got, want, "round {round}");
    }
}

#[test]
fn ntt_domain_arithmetic_matches_coefficient_domain() {
    const N: usize = 64;
    let op = NttOperatorOptimized::<ZqD, N>::new();
    let mk = |tag: u64| {
        PolyRing::<ZqD, N>::from_coefficients(
            (0..N)
                .map(|i| ZqD::new(tag * 97 + i as u64 * 13 + 1))
                .collect(),
        )
    };
    let (a, b) = (mk(1), mk(2));

    let (a_hat, b_hat) = (a.to_ntt(&op), b.to_ntt(&op));
    let sum = PolyRing::from_ntt(a_hat.add(&b_hat), &op);
    let diff = PolyRing::from_ntt(a_hat.sub(&b_hat), &op);
    let prod = PolyRing::from_ntt(a_hat.mul(&b_hat), &op);

    assert_eq!(sum, a.clone() + b.clone());
    assert_eq!(diff, a.clone() - b.clone());
    assert_eq!(prod, a * b);
}

#[test]
fn polyring_negacyclic_property() {
    const N: usize = 32;
    // x^N wraps to -1: (x^{N-1}) * (x) = -1
    let x = PolyRing::<ZqD, N>::from_coefficients(vec![ZqD::ZERO, ZqD::ONE]);
    let xn1 = PolyRing::<ZqD, N>::from_coefficients(
        (0..N)
            .map(|i| if i == N - 1 { ZqD::ONE } else { ZqD::ZERO })
            .collect(),
    );
    let prod = xn1 * x;
    let coeff0 = prod.coefficients().first().copied().unwrap_or(ZqD::ZERO);
    assert_eq!(coeff0.centered(), -1);
}

#[test]
fn module_matvec_is_linear() {
    const K: usize = 3;
    const L: usize = 4;
    const N: usize = 64;
    let entry = |i: usize, j: usize| {
        PolyRing::<ZqD, N>::from_coefficients(
            (0..N)
                .map(|c| ZqD::new((i as u64 * 29 + j as u64 * 11 + c as u64) % 977 + 1))
                .collect(),
        )
    };
    let a: ModuleMatrix<ZqD, K, L, N> = ModuleMatrix::from_fn(&entry);
    let mk = |tag: u64| {
        ModuleVector::<ZqD, L, N>::from_fn(|i| {
            PolyRing::from_coefficients(
                (0..N)
                    .map(|c| ZqD::new((tag * 53 + i as u64 * 7 + c as u64) % 977 + 1))
                    .collect(),
            )
        })
    };
    let (v, w) = (mk(1), mk(2));

    // A·(v + w) == A·v + A·w
    assert_eq!(
        a.mul_vec(&(v.clone() + w.clone())),
        a.mul_vec(&v) + a.mul_vec(&w)
    );

    // (2A)·v == 2(A·v) — module-linearity in the matrix
    let two_a: ModuleMatrix<ZqD, K, L, N> = ModuleMatrix::from_fn(|i, j| {
        PolyRing::from_coefficients(entry(i, j).coefficients().iter().map(|c| *c + *c).collect())
    });
    assert_eq!(two_a.mul_vec(&v), a.mul_vec(&v) + a.mul_vec(&v));
}

#[test]
fn expand_from_seed_is_deterministic_and_separating() {
    const K: usize = 2;
    const L: usize = 2;
    const N: usize = 256;
    let m1 = ModuleMatrixNtt::<ZqD, K, L, N>::expand_from_seed::<Shake128Xof>(&[3u8; 32]);
    let m2 = ModuleMatrixNtt::<ZqD, K, L, N>::expand_from_seed::<Shake128Xof>(&[3u8; 32]);
    let m3 = ModuleMatrixNtt::<ZqD, K, L, N>::expand_from_seed::<Shake128Xof>(&[4u8; 32]);
    assert_eq!(m1, m2, "same seed → same matrix");
    assert_ne!(m1, m3, "different seed → different matrix");
}

#[test]
fn xof_streaming_absorb_is_order_preserving() {
    // Absorbing in chunks must equal absorbing the concatenation…
    let mut whole = Shake128Xof::new(b"streaming");
    whole.absorb(b"hello lattice world");

    let mut chunked = Shake128Xof::new(b"streaming");
    chunked.absorb(b"hello ");
    chunked.absorb(b"lattice world");

    assert_eq!(whole.squeeze_vec(64), chunked.squeeze_vec(64));

    // …and different domains must never collide.
    let mut other = Shake128Xof::new(b"streaming-x");
    other.absorb(b"hello lattice world");
    assert_ne!(whole.squeeze_vec(64), other.squeeze_vec(64));
}

#[test]
fn shake256_stream_agrees_with_helper_hash() {
    let mut x = Shake256Xof::new(&[]);
    x.absorb(b"determinism");
    let streamed = x.squeeze_vec(32);
    assert_eq!(
        streamed.to_vec(),
        algebra::crypto::xof::shortcuts::h256(b"determinism").to_vec()
    );
}

#[test]
fn transcript_challenges_are_domain_separated() {
    let mut t1: Transcript<Shake256Xof> = Transcript::new(b"protocol-A");
    t1.absorb(b"msg", b"payload");
    let mut t2: Transcript<Shake256Xof> = Transcript::new(b"protocol-B");
    t2.absorb(b"msg", b"payload");
    let first = t1.challenge_bytes(32);
    assert_ne!(first, t2.challenge_bytes(32));

    // Replaying the same transcript from scratch reproduces the challenge:
    // the stream advances per challenge, but the derivation is deterministic.
    let mut t3: Transcript<Shake256Xof> = Transcript::new(b"protocol-A");
    t3.absorb(b"msg", b"payload");
    assert_eq!(first, t3.challenge_bytes(32));
}

#[test]
fn samplers_are_deterministic_and_bounded() {
    fn draws() -> (Vec<i64>, Vec<i64>) {
        let mut x = Shake128Xof::new(b"sampler-contract");
        let mut s = BitStream::new(&mut x);
        let r = (0..64)
            .map(|_| sample_rej_bounded::<ZqD>(&mut s, 2))
            .collect();
        let c = (0..64).map(|_| sample_cbd::<ZqD>(&mut s, 2)).collect();
        (r, c)
    }
    let (r1, c1) = draws();
    let (r2, c2) = draws();
    assert_eq!(r1, r2);
    assert_eq!(c1, c2);
    assert!(r1.iter().all(|v| (-2..=2).contains(v)));
    assert!(c1.iter().all(|v| (-2..=2).contains(v)));

    let g = DiscreteGaussian::new(1.5);
    let mut x = Shake128Xof::new(b"gaussian-contract");
    let mut s = BitStream::new(&mut x);
    let gs = g.sample_many(&mut s, 500);
    assert!(gs.iter().all(|v| v.abs() <= g.tail));
}

#[test]
fn sparse_polynomial_mul_matches_dense() {
    const N: usize = 64;
    let signs = vec![0i8; N];
    let mut signs = signs;
    for slot in [0usize, 5, 17, 40] {
        signs[slot] = if slot % 2 == 0 { 1 } else { -1 };
    }
    let signs2 = {
        let mut s = vec![0i8; N];
        s[3] = 1;
        s[60] = -1;
        s
    };

    let sparse1 = SparsePolynomial::<ZqD>::from_sign_vector(&signs, N);
    let sparse2 = SparsePolynomial::<ZqD>::from_sign_vector(&signs2, N);
    let dense2 = PolyRing::<ZqD, N>::from_coefficients(sparse2.to_coeff_vec());
    let got = padded(
        sparse1
            .mul_dense(&dense2)
            .coefficients()
            .iter()
            .map(centered_u128)
            .collect(),
        N,
    );

    // Dense reference convolution with the negacyclic wrap.
    let mut want = vec![0u128; N];
    for (i, &si) in signs.iter().enumerate() {
        if si == 0 {
            continue;
        }
        for (j, &sj) in signs2.iter().enumerate() {
            if sj == 0 {
                continue;
            }
            let v = (si as i128 * sj as i128).rem_euclid(8_380_417) as u128;
            if i + j < N {
                want[i + j] = (want[i + j] + v) % 8_380_417;
            } else {
                want[i + j - N] = (want[i + j - N] + 8_380_417 - v) % 8_380_417;
            }
        }
    }
    assert_eq!(got, want);
}

#[test]
fn packed_bit_roundtrip_is_lossless() {
    let coeffs: Vec<u64> = (0..100).map(|i| (i * 37) % 1024).collect();
    let bytes = algebra::crypto::bits::to_packed_bytes(&coeffs, 10);
    assert_eq!(
        algebra::crypto::bits::from_packed_bytes(&bytes, 100, 10),
        coeffs
    );
}

#[test]
fn high_compression_roundtrip_stays_in_band() {
    let coeffs: Vec<u64> = (0..64).map(|i| (i * 331) % 8_380_417).collect();
    let compressed = algebra::crypto::bits::compress_high(&coeffs, 8_380_417, 4);
    let restored = algebra::crypto::bits::decompress_high(&compressed, 4);
    assert_eq!(restored.len(), coeffs.len());
    // Compression is lossy, but the reconstruction error is bounded by 2^d.
    for (orig, back) in coeffs.iter().zip(&restored) {
        let diff = (*orig as i64 - *back as i64).abs();
        assert!(diff <= 1 << 4, "compression error too large: {diff}");
    }
}
