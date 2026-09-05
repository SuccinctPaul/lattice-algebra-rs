//! Extendable-output functions (XOF) with domain separation (L4).
//!
//! Every scheme-facing deterministic derivation in the crate consumes a
//! [`Xof`]: randomness is never taken from a bare RNG below the API boundary,
//! which makes KATs, fuzzing and reproducible signing possible. This mirrors
//! the derivation structure of FIPS 203/204 (SHAKE128/256 with domain
//! separators).
//!
//! Design notes:
//! - [`Xof::absorb_labeled`] prefixes variable-length data with its length so
//!   that `("ab", "c")` and `("a", "bc")` always squeeze different streams.
//! - Domain labels live with the scheme parameter sets, not with callers.

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake128, Shake128Reader, Shake256, Shake256Reader};

/// Rate (squeeze block size) of SHAKE128 in bytes.
pub const SHAKE128_RATE: usize = 168;
/// Rate (squeeze block size) of SHAKE256 in bytes.
pub const SHAKE256_RATE: usize = 136;

/// Extendable-output function with absorbing/squeezing semantics.
pub trait Xof: Clone {
    /// Starts a new XOF instance bound to a domain label.
    fn new(domain: &[u8]) -> Self;

    /// Absorbs raw bytes.
    fn absorb(&mut self, data: &[u8]);

    /// Absorbs `data` under a label, length-prefixing both parts.
    ///
    /// This is the canonical way to mix structured inputs; it prevents
    /// concatenation ambiguities between (label, data) pairs.
    fn absorb_labeled(&mut self, label: &[u8], data: &[u8]) {
        self.absorb(&(label.len() as u32).to_le_bytes());
        self.absorb(label);
        self.absorb(&(data.len() as u64).to_le_bytes());
        self.absorb(data);
    }

    /// Squeezes exactly `out.len()` bytes.
    fn squeeze(&mut self, out: &mut [u8]);

    /// Convenience wrapper around [`Xof::squeeze`].
    fn squeeze_vec(&mut self, n: usize) -> Vec<u8> {
        let mut out = vec![0u8; n];
        self.squeeze(&mut out);
        out
    }
}

/// Stream semantics: squeezing draws sequentially from the SHAKE output of
/// everything absorbed so far; absorbing invalidates the live output stream
/// and the next squeeze restarts from the updated state. This is O(1) per
/// call (no state replay) and matches the absorb-then-squeeze patterns the
/// FIPS reference code uses.
macro_rules! shake_xof {
    ($name:ident, $hasher:ty, $reader:ty, $doc:expr) => {
        #[doc = $doc]
        #[derive(Clone)]
        pub struct $name {
            hasher: $hasher,
            reader: Option<$reader>,
        }

        impl Xof for $name {
            fn new(domain: &[u8]) -> Self {
                let mut hasher = <$hasher>::default();
                hasher.update(domain);
                Self {
                    hasher,
                    reader: None,
                }
            }

            fn absorb(&mut self, data: &[u8]) {
                self.hasher.update(data);
                self.reader = None; // new input invalidates the stream
            }

            fn squeeze(&mut self, out: &mut [u8]) {
                if self.reader.is_none() {
                    self.reader = Some(self.hasher.clone().finalize_xof());
                }
                self.reader.as_mut().unwrap().read(out);
            }
        }
    };
}

shake_xof!(
    Shake128Xof,
    Shake128,
    Shake128Reader,
    "SHAKE128 (rate 168 bytes) with incremental absorb and squeeze."
);
shake_xof!(
    Shake256Xof,
    Shake256,
    Shake256Reader,
    "SHAKE256 (rate 136 bytes) with incremental absorb and squeeze."
);

/// One-shot helpers for the derivation shapes FIPS 203/204 spell out with
/// `H`, `G`, `PRF`, `J` and `XOF`.
///
/// They are deliberately free functions over concrete SHAKE instances so the
/// call sites read exactly like the specification.
pub mod shortcuts {
    use super::*;

    /// `H256(data)`: SHAKE256 squeezed to 32 bytes (FIPS 203 `H`, FIPS 204 `H`).
    pub fn h256(data: &[u8]) -> [u8; 32] {
        let mut x = Shake256Xof::new(&[]);
        x.absorb(data);
        let mut out = [0u8; 32];
        x.squeeze(&mut out);
        out
    }

    /// `G(data) = (first, second)`: SHAKE256 squeezed to 64 bytes, split in
    /// half (FIPS 203 `G`, FIPS 204 seed derivation `H` with 64-byte output).
    pub fn g64(data: &[u8]) -> ([u8; 32], [u8; 32]) {
        let mut x = Shake256Xof::new(&[]);
        x.absorb(data);
        let mut out = [0u8; 64];
        x.squeeze(&mut out);
        let mut first = [0u8; 32];
        let mut second = [0u8; 32];
        first.copy_from_slice(&out[..32]);
        second.copy_from_slice(&out[32..]);
        (first, second)
    }

    /// Squeezes `n` bytes from `SHAKE256(seed || byte)` (FIPS 203 `PRF` /
    /// FIPS 204 `ExpandMask`-style one-shot derivation).
    pub fn prf(seed: &[u8], b: u8, n: usize) -> Vec<u8> {
        let mut x = Shake256Xof::new(&[]);
        x.absorb(seed);
        x.absorb(&[b]);
        x.squeeze_vec(n)
    }

    /// Squeezes `n` bytes from `SHAKE128(seed || b1 || b2)` (the FIPS 204
    /// `ExpandA` stream shape: seed, then the two matrix indices).
    pub fn xof128_2(seed: &[u8], b1: u8, b2: u8, n: usize) -> Vec<u8> {
        let mut x = Shake128Xof::new(&[]);
        x.absorb(seed);
        x.absorb(&[b1, b2]);
        x.squeeze_vec(n)
    }
}

#[cfg(test)]
mod tests {
    use super::shortcuts::{g64, h256, prf, xof128_2};
    use super::*;

    #[test]
    fn squeeze_is_deterministic() {
        let mut a = Shake256Xof::new(b"domain");
        a.absorb(b"hello");
        let x = a.squeeze_vec(64);

        let mut b = Shake256Xof::new(b"domain");
        b.absorb(b"hello");
        let y = b.squeeze_vec(64);
        assert_eq!(x, y);
    }

    #[test]
    fn domain_separates_streams() {
        let mut a = Shake256Xof::new(b"domain-a");
        a.absorb(b"payload");
        let x = a.squeeze_vec(32);

        let mut b = Shake256Xof::new(b"domain-b");
        b.absorb(b"payload");
        let y = b.squeeze_vec(32);
        assert_ne!(x, y);
    }

    #[test]
    fn labeled_absorb_is_injective_on_pairs() {
        // ("ab", "c") must differ from ("a", "bc").
        let mut a = Shake256Xof::new(&[]);
        a.absorb_labeled(b"ab", b"c");
        let x = a.squeeze_vec(32);

        let mut b = Shake256Xof::new(&[]);
        b.absorb_labeled(b"a", b"bc");
        let y = b.squeeze_vec(32);
        assert_ne!(x, y);
    }

    #[test]
    fn squeeze_is_incremental() {
        // Squeezing 64 bytes at once must equal two 32-byte squeezes.
        let mut a = Shake256Xof::new(b"d");
        let once = a.squeeze_vec(64);

        let mut b = Shake256Xof::new(b"d");
        let first = b.squeeze_vec(32);
        let second = b.squeeze_vec(32);
        let twice = [first, second].concat();
        assert_eq!(once, twice);
    }

    #[test]
    fn shortcuts_match_explicit_construction() {
        let h = h256(b"msg");
        let mut x = Shake256Xof::new(&[]);
        x.absorb(b"msg");
        assert_eq!(h.as_slice(), &x.squeeze_vec(32)[..]);

        let (g1, g2) = g64(b"seed");
        let mut y = Shake256Xof::new(&[]);
        y.absorb(b"seed");
        let out = y.squeeze_vec(64);
        assert_eq!(g1.as_slice(), &out[..32]);
        assert_eq!(g2.as_slice(), &out[32..]);

        let p = prf(b"rho", 0x2A, 17);
        let mut z = Shake256Xof::new(&[]);
        z.absorb(b"rho");
        z.absorb(&[0x2A]);
        assert_eq!(p, z.squeeze_vec(17));

        let s = xof128_2(b"rho", 1, 2, 9);
        let mut w = Shake128Xof::new(&[]);
        w.absorb(b"rho");
        w.absorb(&[1, 2]);
        assert_eq!(s, w.squeeze_vec(9));
    }
}
