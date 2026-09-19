//! Power-of-two complex FFT over `f64`, backing [`UniPolynomial::fft_mul`](super::UniPolynomial::fft_mul).
//!
//! Written in-tree rather than pulled from `rustfft` because that crate is
//! `std`-only, and this module's consumer (`Mul for UniPolynomial`) is part of
//! the `no_std` surface. Only a radix-2 kernel is needed: every call site pads
//! the transform length to `next_power_of_two`.
//!
//! Twiddles are read from a per-transform table computed directly from
//! [`libm::cos`] / [`libm::sin`], never by repeated multiplication of a step
//! value. Accumulating a step error over `n/2` butterflies drifts by more than
//! the half-integer slack the rounding step in [`super`] allows.

// Only the `#[cfg(test)]` children use this, so the plain lib build reports it
// unused; deleting it breaks `cargo test`.
#[allow(unused_imports)]
use alloc::vec;
use alloc::vec::Vec;
use core::ops::{Add, AddAssign, Mul, MulAssign, Sub};

/// The full circle, as the radix-2 stage angles are derived from it.
const TAU: f64 = core::f64::consts::TAU;

/// A complex `f64`. Deliberately private: it never crosses the crate boundary.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub(crate) struct C64 {
    re: f64,
    im: f64,
}

impl C64 {
    pub(crate) fn new(re: f64, im: f64) -> Self {
        Self { re, im }
    }

    pub(crate) fn re(&self) -> f64 {
        self.re
    }
}

impl Add for C64 {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self {
            re: self.re + rhs.re,
            im: self.im + rhs.im,
        }
    }
}

impl AddAssign for C64 {
    fn add_assign(&mut self, rhs: Self) {
        self.re += rhs.re;
        self.im += rhs.im;
    }
}

impl Sub for C64 {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self {
        Self {
            re: self.re - rhs.re,
            im: self.im - rhs.im,
        }
    }
}

impl Mul for C64 {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self {
        Self {
            re: self.re * rhs.re - self.im * rhs.im,
            im: self.re * rhs.im + self.im * rhs.re,
        }
    }
}

impl MulAssign for C64 {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl MulAssign<f64> for C64 {
    fn mul_assign(&mut self, rhs: f64) {
        self.re *= rhs;
        self.im *= rhs;
    }
}

/// `exp(-2*pi*i*j/n)` for `j in 0..n/2`, the forward convention.
fn twiddle_table(n: usize) -> Vec<C64> {
    let inv_n = 1.0 / (n as f64);
    (0..n / 2)
        .map(|j| {
            let angle = -TAU * (j as f64) * inv_n;
            C64::new(libm::cos(angle), libm::sin(angle))
        })
        .collect()
}

/// In-place bit-reversal permutation of `a`, whose length is a power of two.
fn bit_reverse(a: &mut [C64]) {
    let n = a.len();
    let mut j = 0usize;
    for i in 1..n {
        let mut bit = n >> 1;
        while j & bit != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j |= bit;
        if i < j {
            a.swap(i, j);
        }
    }
}

/// Iterative radix-2 Cooley-Tukey butterfly sweep; `inverse` flips the sign
/// convention by conjugating each twiddle.
fn butterflies(a: &mut [C64], table: &[C64], inverse: bool) {
    let n = a.len();
    let mut len = 2;
    while len <= n {
        let half = len / 2;
        let stride = n / len;
        for start in (0..n).step_by(len) {
            for (j, slot) in (start..start + half).enumerate() {
                let mut w = table[j * stride];
                if inverse {
                    w.im = -w.im;
                }
                let u = a[slot];
                let t = w * a[slot + half];
                a[slot] = u + t;
                a[slot + half] = u - t;
            }
        }
        len <<= 1;
    }
}

/// Forward transform of a power-of-two-length sequence, in place.
pub(crate) fn fft_forward(a: &mut [C64]) {
    let n = a.len();
    debug_assert!(n.is_power_of_two());
    if n < 2 {
        return;
    }
    let table = twiddle_table(n);
    bit_reverse(a);
    butterflies(a, &table, false);
}

/// Inverse transform, including the `1/n` scaling, in place.
pub(crate) fn fft_inverse(a: &mut [C64]) {
    let n = a.len();
    debug_assert!(n.is_power_of_two());
    if n < 2 {
        return;
    }
    let table = twiddle_table(n);
    bit_reverse(a);
    butterflies(a, &table, true);
    let scale = 1.0 / (n as f64);
    for coeff in a.iter_mut() {
        *coeff *= scale;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    fn real(v: &[f64]) -> Vec<C64> {
        v.iter().map(|&x| C64::new(x, 0.0)).collect()
    }

    fn imag(a: &[C64]) -> Vec<f64> {
        a.iter().map(|c| c.im).collect()
    }

    #[test]
    fn forward_matches_dft_definition() {
        // Cross-check the kernel against the O(n^2) definition it must
        // implement, rather than against itself.
        let xs = [1.0_f64, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0];
        let n = xs.len();
        let mut a = real(&xs);
        fft_forward(&mut a);
        for (k, got) in a.iter().enumerate() {
            let mut acc = C64::default();
            for (j, &x) in xs.iter().enumerate() {
                let angle = -TAU * ((j * k) % n) as f64 / (n as f64);
                acc += C64::new(x, 0.0) * C64::new(libm::cos(angle), libm::sin(angle));
            }
            assert!((got.re - acc.re).abs() < 1e-9, "bin {k}");
            assert!((got.im - acc.im).abs() < 1e-9, "bin {k}");
        }
    }

    #[test]
    fn roundtrip_is_identity() {
        let xs = [3.5_f64, -1.25, 0.0, 8.0, -7.75, 2.0, 0.5, 0.0];
        let mut a = real(&xs);
        fft_forward(&mut a);
        assert_ne!(imag(&a), vec![0.0; xs.len()]);
        fft_inverse(&mut a);
        for i in 0..xs.len() {
            assert!((a[i].re - xs[i]).abs() < 1e-12, "index {i}");
            assert!(a[i].im.abs() < 1e-12, "index {i}");
        }
    }

    #[test]
    fn length_one_and_two_are_degenerate() {
        let mut a = vec![C64::new(9.0, 0.0)];
        fft_forward(&mut a);
        fft_inverse(&mut a);
        assert_eq!(a[0].re, 9.0);

        let mut b = real(&[4.0, 1.0]);
        fft_forward(&mut b);
        assert_eq!((b[0].re, b[1].re), (5.0, 3.0));
        assert_eq!((b[0].im, b[1].im), (0.0, 0.0));
    }
}
