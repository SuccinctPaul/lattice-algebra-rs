//! The sampler tour: every distribution in `crypto::sampling`, drawn from
//! domain-separated XOF streams, with ASCII histograms so the shape is
//! visible. Everything is deterministic — same seeds, same histograms.
//!
//! Run with: `cargo run -p lattice-algebra --example samplers`

use algebra::crypto::sampling::{
    sample_cbd, sample_in_ball_signs, sample_rej_bounded, sample_uniform_coeff, BitStream,
    DiscreteGaussian,
};
use algebra::crypto::transcript::Transcript;
use algebra::crypto::xof::shortcuts::h256;
use algebra::crypto::xof::{Shake128Xof, Shake256Xof, Xof};
use algebra::ring::zq::Zq;
use algebra::ring::Ring;

type ZqD = Zq<8380417>;

/// One text line per bucket, bar length proportional to the count.
fn histogram(values: &[i64], lo: i64, buckets: usize) -> String {
    let mut bins = vec![0usize; buckets];
    for &v in values {
        let idx = ((v - lo) as usize).min(buckets - 1);
        bins[idx] += 1;
    }
    let peak = bins.iter().copied().max().unwrap_or(1).max(1);
    bins.iter()
        .enumerate()
        .map(|(i, &c)| {
            let bars = c * 40 / peak;
            let label = if buckets <= 25 {
                format!("{:>3}", lo + i as i64)
            } else {
                "   ".into()
            };
            format!("{label} │{}", "#".repeat(bars))
        })
        .collect::<Vec<_>>()
        .join("\n")
}

fn main() {
    const M: usize = 2000;

    // ------------------------------------------------------------------
    // Uniform over Z_q — masked rejection on the bit stream
    // ------------------------------------------------------------------
    let mut x = Shake128Xof::new(b"uniform-demo");
    let mut s = BitStream::new(&mut x);
    let us: Vec<u128> = (0..M)
        .map(|_| sample_uniform_coeff::<ZqD>(&mut s).to_u128())
        .collect();
    println!(
        "uniform over [0, 8380417):  min={}  max={}  (deterministic)",
        us.iter().min().unwrap(),
        us.iter().max().unwrap()
    );

    // ------------------------------------------------------------------
    // RejBounded(η=2) — ML-DSA secret/mask coefficients on [-2, 2]
    // ------------------------------------------------------------------
    let mut x = Shake128Xof::new(b"rej-bounded-demo");
    let mut s = BitStream::new(&mut x);
    let rs: Vec<i64> = (0..M)
        .map(|_| sample_rej_bounded::<ZqD>(&mut s, 2))
        .collect();
    println!("\nRejBounded(η=2), counts for -2..=2:");
    println!("{}", histogram(&rs, -2, 5));

    // ------------------------------------------------------------------
    // CBD(η=2) — ML-KEM noise on [-2, 2]
    // ------------------------------------------------------------------
    let mut x = Shake128Xof::new(b"cbd-demo");
    let mut s = BitStream::new(&mut x);
    let cs: Vec<i64> = (0..M).map(|_| sample_cbd::<ZqD>(&mut s, 2)).collect();
    let mean = cs.iter().sum::<i64>() as f64 / M as f64;
    println!("\nCBD(η=2), mean={mean:+.3} (≈ 0):");
    println!("{}", histogram(&cs, -2, 5));

    // ------------------------------------------------------------------
    // DiscreteGaussian(σ=3.2) — truncated at ⌈12σ⌉, CDT inversion
    // ------------------------------------------------------------------
    let g = DiscreteGaussian::new(3.2);
    let mut x = Shake128Xof::new(b"gaussian-demo");
    let mut s = BitStream::new(&mut x);
    let gs = g.sample_many(&mut s, 4000);
    let mean = gs.iter().sum::<i64>() as f64 / gs.len() as f64;
    println!(
        "\nDiscreteGaussian(σ=3.2, tail={}), mean={mean:+.3}:",
        g.tail
    );
    println!("{}", histogram(&gs, -20, 41));

    // ------------------------------------------------------------------
    // SampleInBall — τ-sparse ±1 challenge
    // ------------------------------------------------------------------
    let mut x = Shake256Xof::new(b"in-ball-demo");
    let mut s = BitStream::new(&mut x);
    let signs = sample_in_ball_signs(&mut s, 39, 256);
    let nonzeros = signs.iter().filter(|&&v| v != 0).count();
    println!("\nSampleInBall(τ=39, n=256): {nonzeros} nonzero signs   ✓");

    // ------------------------------------------------------------------
    // Transcripts: domain-separated, fork-consistent challenges
    // ------------------------------------------------------------------
    let mut tr: Transcript<Shake256Xof> = Transcript::new(b"demo-protocol-v1");
    tr.absorb(b"statement", b"public-statement-bytes");
    let c1 = tr.challenge_bytes(32);
    let mut tr2: Transcript<Shake256Xof> = Transcript::new(b"demo-protocol-v1");
    tr2.absorb(b"statement", b"public-statement-bytes");
    assert_eq!(
        c1,
        tr2.challenge_bytes(32),
        "same transcript → same challenge"
    );
    println!("Transcript challenges are deterministic   ✓");

    // Hash helpers used across the schemes (the FIPS 203/204 one-shot shapes).
    let _h = h256(b"input");
    println!("h256 / g64 / prf / xof128_2 helpers available");
}
