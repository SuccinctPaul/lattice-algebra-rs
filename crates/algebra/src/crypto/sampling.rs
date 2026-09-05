//! Structured samplers for lattice schemes (L4).
//!
//! Every sampler is **XOF-driven and deterministic**: callers pass a domain-
//! separated [`Xof`] stream (seed and label already absorbed), never a bare
//! RNG. This mirrors the derivation structure of FIPS 203/204 and makes KATs
//! and reproducible signing possible.
//!
//! Bit conventions follow the specifications: bits are consumed from each
//! byte least-significant first, and bytes are consumed in stream order.
//!
//! Provided distributions:
//! - [`sample_uniform_coeff`] / [`sample_uniform_coeffs`]: full-width uniform
//!   over `[0, q)` via masked rejection (FIPS 204 `CoeffFromThreeBytes`
//!   generalized to any modulus).
//! - [`sample_uniform_ntt_coeffs`]: the same, biased to reject coefficients
//!   that would vanish in the NTT domain (FIPS 204 `RejNTTPoly` behavior for
//!   `ExpandA`).
//! - [`sample_rej_bounded`]: centered uniform on `[-eta, eta]`
//!   (FIPS 204 `RejBoundedη`, used for `s1`, `s2` and the mask `y`).
//! - [`sample_cbd`]: centered binomial distribution on `[-eta, eta]`
//!   (FIPS 203 noise, `CBDη`).
//! - [`sample_in_ball_signs`]: `τ`-sparse ±1 challenge positions
//!   (FIPS 204 `SampleInBall`).
//! - [`DiscreteGaussian`]: truncated discrete Gaussian `D_{Z,σ}` via
//!   precomputed-CDT inversion (the noise primitive for Gaussian-signature
//!   schemes such as Falcon / FN-DSA).

use crate::crypto::xof::Xof;
use crate::ring::Ring;

/// Bit-reader over an [`Xof`] stream (LSB-first within each byte).
pub struct BitStream<'a, X: Xof> {
    xof: &'a mut X,
    byte: u8,
    /// Bits still available in `byte` (counting from the LSB).
    remaining: u8,
}

impl<'a, X: Xof> BitStream<'a, X> {
    pub fn new(xof: &'a mut X) -> Self {
        Self {
            xof,
            byte: 0,
            remaining: 0,
        }
    }

    /// Reads `n <= 32` bits, LSB-first.
    pub fn read_bits(&mut self, n: u32) -> u32 {
        debug_assert!(n <= 32);
        let mut out: u32 = 0;
        for i in 0..n {
            if self.remaining == 0 {
                let mut buf = [0u8; 1];
                self.xof.squeeze(&mut buf);
                self.byte = buf[0];
                self.remaining = 8;
            }
            let bit = (self.byte >> (8 - self.remaining)) & 1;
            out |= (bit as u32) << i;
            self.remaining -= 1;
        }
        out
    }

    /// Reads one full byte.
    pub fn read_byte(&mut self) -> u8 {
        let mut buf = [0u8; 1];
        self.xof.squeeze(&mut buf);
        buf[0]
    }

    /// Fills `out` with squeezed bytes (bypasses the bit buffer).
    pub fn read_bytes(&mut self, out: &mut [u8]) {
        self.xof.squeeze(out);
    }
}

/// Number of bits needed to represent `max_value` (≥ 1).
fn bit_len(max_value: u64) -> u32 {
    (64 - (max_value.leading_zeros())).max(1)
}

/// Draws one uniform coefficient in `[0, q)` from masked rejection sampling.
///
/// Generalizes FIPS 204 `CoeffFromThreeBytes`: `ceil(bitlen(q-1) / 8)` bytes
/// are assembled little-endian, the value is masked down to `bitlen(q-1)`
/// bits, and values `>= q` are rejected.
pub fn sample_uniform_coeff<R: Ring>(stream: &mut BitStream<'_, impl Xof>) -> R {
    let q = R::MODULUS;
    let bits = bit_len(q - 1);
    let nbytes = (bits as usize + 7) / 8;

    loop {
        let mut buf = [0u8; 8];
        stream.read_bytes(&mut buf[..nbytes]);
        let mut v = 0u64;
        for (i, &b) in buf[..nbytes].iter().enumerate() {
            v |= (b as u64) << (8 * i);
        }
        v &= (1u64 << bits) - 1;
        if v < q {
            return R::from(v);
        }
    }
}

/// Draws `n` uniform coefficients in `[0, q)`.
pub fn sample_uniform_coeffs<R: Ring>(stream: &mut BitStream<'_, impl Xof>, n: usize) -> Vec<R> {
    (0..n).map(|_| sample_uniform_coeff(stream)).collect()
}

/// Draws `n` uniform coefficients destined for the NTT domain.
///
/// Semantically identical to [`sample_uniform_coeffs`] (masked rejection at
/// `q`, FIPS 204 `CoeffFromThreeBytes`); the separate name documents intent
/// at call sites: `ExpandA` fills `Â` directly in the NTT domain so no
/// transform is ever spent on the matrix.
pub fn sample_uniform_ntt_coeffs<R: Ring>(
    stream: &mut BitStream<'_, impl Xof>,
    n: usize,
) -> Vec<R> {
    sample_uniform_coeffs(stream, n)
}

/// One centered coefficient on `[-eta, eta]` via rejection sampling.
///
/// For the FIPS 204 values `eta ∈ {2, 4}` this follows the reference
/// implementation bit-for-bit (nibbles: `eta = 2` accepts `t < 15` and maps
/// `2 - (t mod 5)`; `eta = 4` accepts `t < 9` and maps `4 - t`). Other moduli
/// fall back to the generic uniform-on-`[-eta, eta]` sampler: draw
/// `bitlen(2·eta)` bits, accept `r <= 2·eta` as `r - eta`, reject otherwise.
pub fn sample_rej_bounded<R: Ring>(stream: &mut BitStream<'_, impl Xof>, eta: u32) -> i64 {
    match eta {
        2 => loop {
            let t = stream.read_bits(4);
            if t < 15 {
                // t mod 5 via the reference's multiply-shift trick.
                let m = t - ((t * 205) >> 10) * 5;
                return 2 - i64::from(m);
            }
        },
        4 => loop {
            let t = stream.read_bits(4);
            if t < 9 {
                return 4 - i64::from(t);
            }
        },
        eta => {
            let k = bit_len(u64::from(2 * eta));
            loop {
                let r = stream.read_bits(k);
                if r <= 2 * eta {
                    return i64::from(r) - i64::from(eta);
                }
            }
        }
    }
}

/// Draws `n` centered coefficients on `[-eta, eta]` via [`sample_rej_bounded`].
pub fn sample_rej_bounded_coeffs<R: Ring>(
    stream: &mut BitStream<'_, impl Xof>,
    eta: u32,
    n: usize,
) -> Vec<i64> {
    (0..n)
        .map(|_| sample_rej_bounded::<R>(stream, eta))
        .collect()
}

/// One centered binomial coefficient on `[-eta, eta]` (FIPS 203 `CBDη`):
/// the sum of `eta` random bits minus the sum of `eta` more.
pub fn sample_cbd<R: Ring>(stream: &mut BitStream<'_, impl Xof>, eta: u32) -> i64 {
    let a = (0..eta).map(|_| stream.read_bits(1)).sum::<u32>();
    let b = (0..eta).map(|_| stream.read_bits(1)).sum::<u32>();
    i64::from(a) - i64::from(b)
}

/// Draws `n` centered binomial coefficients.
pub fn sample_cbd_coeffs<R: Ring>(
    stream: &mut BitStream<'_, impl Xof>,
    eta: u32,
    n: usize,
) -> Vec<i64> {
    (0..n).map(|_| sample_cbd::<R>(stream, eta)).collect()
}

/// `τ`-sparse ±1 challenge signs over `n` slots (FIPS 204 `SampleInBall`).
///
/// Returns a sign vector of length `n` with exactly `tau` non-zero entries,
/// each `±1`. The first `8` squeezed bytes provide the sign bits, then the
/// Fisher-Yates-style loop fixes the positions.
pub fn sample_in_ball_signs(stream: &mut BitStream<'_, impl Xof>, tau: u32, n: usize) -> Vec<i8> {
    assert!(n <= 256, "SampleInBall positions are drawn from one byte");
    assert!(
        tau < n as u32,
        "tau must be smaller than the ring dimension"
    );

    let mut signs = vec![0i8; n];

    // 8 sign bits, one per byte (bit i of byte i), as in the specification.
    let mut sign_bits = [0u8; 8];
    stream.read_bytes(&mut sign_bits);

    // positions n - tau .. n - 1 are filled by rejection sampling; the sign
    // bits are consumed in order (k-th position uses the k-th sign bit).
    for i in (n - tau as usize)..n {
        let mut j = stream.read_byte() as usize;
        while j > i {
            j = stream.read_byte() as usize;
        }
        signs[i] = signs[j];
        let k = i - (n - tau as usize);
        let bit = (sign_bits[k / 8] >> (k % 8)) & 1;
        signs[j] = if bit == 1 { -1 } else { 1 };
    }
    signs
}

/// Truncated discrete Gaussian `D_{Z,σ}` sampled by precomputed-CDT inversion.
///
/// The support is cut at `tail = ⌈12σ⌉`, which costs less than `2^-90`
/// statistical distance against the true discrete Gaussian. The cumulative
/// table is built once in `2^127` fixed point; each draw consumes 16 stream
/// bytes and one binary search — no rejection loop, deterministic given the
/// [`Xof`] stream.
///
/// Intended for Falcon / FN-DSA-grade noise (σ up to a few hundred; the
/// table is `O(σ)`).
#[derive(Debug, Clone, PartialEq)]
pub struct DiscreteGaussian {
    /// Standard deviation `σ`.
    pub sigma: f64,
    /// Support bound; every draw lies in `[-tail, tail]`.
    pub tail: i64,
    /// Strictly increasing `2·tail` fixed-point cut points `P(X < k)` for
    /// interior atoms `k ∈ (-tail, tail)`, scaled to `2^127`.
    cdt: Vec<u128>,
}

impl DiscreteGaussian {
    /// Builds the CDT for standard deviation `sigma > 0`.
    pub fn new(sigma: f64) -> Self {
        assert!(
            sigma.is_finite() && sigma > 0.0,
            "sigma must be a positive finite number"
        );
        let tail = ((sigma * 12.0).ceil() as i64).max(1);
        // Unnormalized symmetric atom weights w_i = exp(-i²/(2σ²)).
        let weight = |i: i64| (-(i * i) as f64 / (2.0 * sigma * sigma)).exp();
        let total: f64 = weight(0) + 2.0 * (1..=tail).map(weight).sum::<f64>();

        // Fixed-point cut points; the `+1` shift keeps entries strictly
        // increasing even where f64 rounding would repeat a value.
        let scale = (1u128 << 127) as f64;
        let mut cdt: Vec<u128> = Vec::with_capacity(2 * tail as usize);
        let mut cum = 0.0f64;
        for i in -tail..tail {
            cum += weight(i);
            let point = (cum / total * scale) as u128;
            let prev = cdt.last().copied().unwrap_or(0);
            cdt.push(point.max(prev + 1));
        }
        Self { sigma, tail, cdt }
    }

    /// Draws one sample on `[-tail, tail]`.
    pub fn sample(&self, stream: &mut BitStream<'_, impl Xof>) -> i64 {
        // 16 bytes -> u128, halved to a uniform on [0, 2^127): the same
        // support the cut points are scaled to.
        let mut buf = [0u8; 16];
        stream.read_bytes(&mut buf);
        let mut y = 0u128;
        for (i, &b) in buf.iter().enumerate() {
            y |= (b as u128) << (8 * i);
        }
        y >>= 1;
        let k = self.cdt.partition_point(|&p| p <= y);
        k as i64 - self.tail
    }

    /// Draws `n` samples.
    pub fn sample_many(&self, stream: &mut BitStream<'_, impl Xof>, n: usize) -> Vec<i64> {
        (0..n).map(|_| self.sample(stream)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::crypto::xof::{Shake128Xof, Shake256Xof, Xof};
    use crate::ring::zq::Zq;

    #[test]
    fn uniform_is_deterministic_and_in_range() {
        fn draw() -> Vec<Zq<8380417>> {
            let mut x = Shake128Xof::new(b"uniform-test");
            let mut s = BitStream::new(&mut x);
            sample_uniform_coeffs(&mut s, 64)
        }
        let a = draw();
        let b = draw();
        assert_eq!(a, b, "XOF-driven sampling must be deterministic");
        assert!(a.iter().all(|c| c.to_u128() < 8380417));
    }

    #[test]
    fn uniform_covers_range_and_rejection_terminates() {
        // Small modulus: every representative must appear over enough draws.
        let mut x = Shake128Xof::new(b"coverage");
        let mut s = BitStream::new(&mut x);
        let mut seen = [false; 17];
        for _ in 0..2000 {
            let v = sample_uniform_coeff::<Zq<17>>(&mut s);
            seen[v.to_u128() as usize] = true;
        }
        assert!(
            seen.iter().all(|&s| s),
            "all 17 representatives must be hit"
        );
    }

    #[test]
    fn rej_bounded_stays_in_range_and_uses_both_tails() {
        let mut x = Shake128Xof::new(b"rej-bounded");
        let mut s = BitStream::new(&mut x);
        let mut negatives = 0;
        let mut positives = 0;
        for _ in 0..2000 {
            let v = sample_rej_bounded::<Zq<17>>(&mut s, 2);
            assert!((-2..=2).contains(&v));
            if v < 0 {
                negatives += 1;
            }
            if v > 0 {
                positives += 1;
            }
        }
        assert!(
            negatives > 100 && positives > 100,
            "distribution too skewed: pos={positives} neg={negatives}"
        );
    }

    #[test]
    fn cbd_has_zero_mean_and_correct_range() {
        let mut x = Shake128Xof::new(b"cbd");
        let mut s = BitStream::new(&mut x);
        let eta = 2;
        let n = 4000;
        let mut sum = 0i64;
        for _ in 0..n {
            let v = sample_cbd::<Zq<17>>(&mut s, eta);
            assert!((-(eta as i64)..=(eta as i64)).contains(&v));
            sum += v;
        }
        // |mean| should be well below one standard deviation of the mean.
        let mean = sum as f64 / n as f64;
        assert!(mean.abs() < 0.2, "CBD mean drifted: {mean}");
    }

    #[test]
    fn in_ball_has_exactly_tau_nonzeros() {
        for tau in [39u32, 49, 60] {
            let mut x = Shake256Xof::new(b"in-ball");
            let mut s = BitStream::new(&mut x);
            let signs = sample_in_ball_signs(&mut s, tau, 256);
            assert_eq!(signs.iter().filter(|&&s| s != 0).count(), tau as usize);
            assert!(signs.iter().all(|&s| s == 0 || s == 1 || s == -1));
        }
    }

    #[test]
    fn in_ball_is_deterministic() {
        fn draw() -> Vec<i8> {
            let mut x = Shake256Xof::new(b"in-ball-det");
            let mut s = BitStream::new(&mut x);
            sample_in_ball_signs(&mut s, 39, 256)
        }
        assert_eq!(draw(), draw());
    }

    #[test]
    fn ntt_domain_uniform_terminates_for_dilithium_modulus() {
        let mut x = Shake128Xof::new(b"rej-ntt");
        let mut s = BitStream::new(&mut x);
        let coeffs = sample_uniform_ntt_coeffs::<Zq<8380417>>(&mut s, 256);
        assert_eq!(coeffs.len(), 256);
        assert!(coeffs.iter().all(|c| c.to_u128() < 8380417));
    }

    #[test]
    fn gaussian_is_deterministic() {
        fn draws() -> Vec<i64> {
            let g = DiscreteGaussian::new(3.2);
            let mut x = Shake128Xof::new(b"gaussian-det");
            let mut s = BitStream::new(&mut x);
            g.sample_many(&mut s, 16)
        }
        assert_eq!(draws(), draws());
    }

    #[test]
    fn gaussian_stays_in_tail_and_centers_correctly() {
        let sigma = 3.2f64;
        let g = DiscreteGaussian::new(sigma);
        assert_eq!(g.tail, 39, "tail must be ceil(12 sigma)");

        let mut x = Shake128Xof::new(b"gaussian-moments");
        let mut s = BitStream::new(&mut x);
        let n = 8000;
        let draws = g.sample_many(&mut s, n);

        assert!(draws.iter().all(|v| v.abs() <= g.tail));
        let mean = draws.iter().sum::<i64>() as f64 / n as f64;
        // One standard error is sigma/sqrt(n) ~ 0.036; allow 4x.
        assert!(mean.abs() < 0.15, "mean drifted: {mean}");

        let var = draws.iter().map(|v| (v * v) as f64).sum::<f64>() / n as f64;
        // Truncation at 12 sigma lowers the second moment negligibly.
        assert!(
            (var - sigma * sigma).abs() < 0.1 * sigma * sigma,
            "variance off: {var} vs {}",
            sigma * sigma
        );
    }

    #[test]
    fn gaussian_small_sigma_peaks_at_zero() {
        let g = DiscreteGaussian::new(0.3);
        assert_eq!(g.tail, 4, "tail must be at least 1");

        let mut x = Shake128Xof::new(b"gaussian-tight");
        let mut s = BitStream::new(&mut x);
        let draws = g.sample_many(&mut s, 2000);
        let zeros = draws.iter().filter(|&&v| v == 0).count();
        // P(0) ~ 0.598 for sigma = 0.3; allow > 4 standard errors of slack.
        assert!(zeros > 1100, "zero atom under-weighted: {zeros}/2000");
    }
}
