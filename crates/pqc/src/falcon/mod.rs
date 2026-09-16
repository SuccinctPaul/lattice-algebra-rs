//! Falcon (round-3 specification, 2020-10-01) — the hash-then-sign lattice
//! signature scheme underlying the future FIPS 206 (FN-DSA).
//!
//! Status notes:
//! - FIPS 206's initial public draft has not been published yet (the NIST
//!   submission entered internal approval in August 2025); this module
//!   implements the round-3 Falcon specification and is byte-exact with
//!   the official round-3 KAT vectors (`Falcon-512` / `Falcon-1024`).
//! - Like the reference implementation, signing and key generation use
//!   double-precision-style floating point. Here the reference's *integer*
//!   soft-float (`fpr`) is ported verbatim, so results are bit-identical
//!   across platforms without `f64` configuration concerns.
//! - Non-constant-time by design (documented in the Falcon spec): the
//!   FFT sampler and hash-to-point leak no secret-key-dependent branches,
//!   but the reference does not claim CT; see the security-status page.
//! - Falcon-padded is out of scope.

pub mod codec;
pub mod common;
pub mod fft;
pub mod fpr;
pub mod keygen;
pub mod mq;
pub mod prng;
pub mod sign;
mod tables;

use common::InnerShake256;

/// logn for Falcon-512.
pub const LOGN_512: u32 = 9;
/// logn for Falcon-1024.
pub const LOGN_1024: u32 = 10;

/// Decoded public key: `h` (mod q) plus the canonical encoding.
pub struct PublicKey {
    bytes: Vec<u8>,
    h: Vec<u16>,
    logn: u32,
}

/// Decoded secret key: f, g, F plus the canonical encoding. Redacted
/// `Debug`; the secret fields are zeroized when the key is dropped.
pub struct SecretKey {
    bytes: Vec<u8>,
    f: Vec<i8>,
    g: Vec<i8>,
    big_f: Vec<i8>,
    logn: u32,
}

impl std::fmt::Debug for SecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SecretKey").finish_non_exhaustive()
    }
}

impl Drop for SecretKey {
    fn drop(&mut self) {
        use zeroize::Zeroize;
        self.bytes.zeroize();
        self.f.zeroize();
        self.g.zeroize();
        self.big_f.zeroize();
    }
}

impl PublicKey {
    /// Canonical encoding (header byte 0x09+logn, then 14-bit coefficients).
    pub fn to_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Decode a public key (length and modulus checks per the reference).
    pub fn from_bytes(bytes: &[u8], logn: u32) -> Option<Self> {
        let n = 1usize << logn;
        let pk_len = 1 + (n * 14).div_ceil(8);
        if bytes.len() != pk_len || bytes[0] != logn as u8 {
            return None;
        }
        let mut h = vec![0u16; n];
        if codec::modq_decode(&mut h, &bytes[1..]) != pk_len - 1 {
            return None;
        }
        Some(Self {
            bytes: bytes.to_vec(),
            h,
            logn,
        })
    }

    /// The public polynomial h.
    pub fn h(&self) -> &[u16] {
        &self.h
    }
}

impl SecretKey {
    /// Canonical encoding (header byte 0x50+logn, then trimmed f, g, F).
    pub fn to_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Decode a secret key.
    pub fn from_bytes(bytes: &[u8], logn: u32) -> Option<Self> {
        let n = 1usize << logn;
        if bytes.len() != sk_len(logn) || bytes[0] != 0x50 + logn as u8 {
            return None;
        }
        let mut f = vec![0i8; n];
        let mut g = vec![0i8; n];
        let mut big_f = vec![0i8; n];
        let mut u = 1usize;
        for (dst, bits) in [
            (&mut f, codec::MAX_FG_BITS[logn as usize]),
            (&mut g, codec::MAX_FG_BITS[logn as usize]),
            (&mut big_f, codec::MAX_BIG_FG_BITS[logn as usize]),
        ] {
            let v = codec::trim_i8_decode(dst, bits as u32, &bytes[u..]);
            if v == 0 {
                return None;
            }
            u += v;
        }
        if u != bytes.len() {
            return None;
        }
        Some(Self {
            bytes: bytes.to_vec(),
            f,
            g,
            big_f,
            logn,
        })
    }
}

/// Encoded secret-key length for a given logn.
pub fn sk_len(logn: u32) -> usize {
    let n = 1usize << logn;
    1 + (n * codec::MAX_FG_BITS[logn as usize] as usize).div_ceil(8)
        + (n * codec::MAX_FG_BITS[logn as usize] as usize).div_ceil(8)
        + (n * 8).div_ceil(8)
}

/// Deterministic key generation: expand the 48-byte seed through SHAKE256,
/// draw the Gaussian (f, g), solve the NTRU equation for F, then build the
/// canonical encodings of both keys.
fn keygen_internal(logn: u32, seed: &[u8; 48]) -> (SecretKey, PublicKey) {
    let n = 1usize << logn;
    let mut rng = InnerShake256::inject_all(&[seed]);
    let mut f = vec![0i8; n];
    let mut g = vec![0i8; n];
    let mut big_f = vec![0i8; n];
    let mut h = vec![0u16; n];
    keygen::keygen(&mut rng, &mut f, &mut g, &mut big_f, &mut h, logn);

    // Encode sk = 0x50+logn ‖ trim(f) ‖ trim(g) ‖ trim(F); f and g use
    // max_fg_bits, F uses the wider max_FG_bits (reference codec.c).
    let mut sk_bytes = vec![0u8; sk_len(logn)];
    sk_bytes[0] = 0x50 + logn as u8;
    let mut u = 1usize;
    for (poly, bits) in [
        (&f, codec::MAX_FG_BITS[logn as usize]),
        (&g, codec::MAX_FG_BITS[logn as usize]),
        (&big_f, codec::MAX_BIG_FG_BITS[logn as usize]),
    ] {
        let v = codec::trim_i8_encode(&mut sk_bytes[u..], poly, bits as u32);
        assert!(v != 0, "key encoding failed");
        u += v;
    }
    assert_eq!(u, sk_bytes.len());

    // Encode pk = 0x09+logn ‖ modq(h).
    let mut pk_bytes = vec![0u8; 1 + (n * 14).div_ceil(8)];
    pk_bytes[0] = logn as u8;
    assert_eq!(
        codec::modq_encode(&mut pk_bytes[1..], &h),
        pk_bytes.len() - 1
    );

    (
        SecretKey {
            bytes: sk_bytes,
            f,
            g,
            big_f,
            logn,
        },
        PublicKey {
            bytes: pk_bytes,
            h,
            logn,
        },
    )
}

/// Deterministic signing: rebuild G from (f, g, F), hash nonce ‖ msg to a
/// point, run the FFT-sampling rejection loop and return the encoded
/// signature (header ‖ compressed s2).
fn sign_internal(sk: &SecretKey, msg: &[u8], nonce: &[u8; 40], sig_seed: &[u8; 48]) -> Vec<u8> {
    let logn = sk.logn;
    let n = 1usize << logn;

    // Recompute G from f, g, F.
    let mut big_g = vec![0i8; n];
    assert!(mq::complete_private(
        &mut big_g, &sk.f, &sk.g, &sk.big_f, logn
    ));

    // Hash nonce ‖ message to a point.
    let mut hm = vec![0u16; n];
    let mut sc = InnerShake256::inject_all(&[nonce, msg]);
    common::hash_to_point_vartime(&mut sc, &mut hm);

    // Signature generation (rejection loop inside sign_dyn).
    let mut rng = InnerShake256::inject_all(&[sig_seed]);
    let mut sig = vec![0i16; n];
    sign::sign_dyn(
        &mut sig, &mut rng, &sk.f, &sk.g, &sk.big_f, &big_g, &hm, logn,
    );

    // Encode: header 0x20+logn ‖ comp(s2).
    let mut esig = vec![0u8; 1 + (n * 12).div_ceil(8) + 32];
    esig[0] = 0x20 + logn as u8;
    let sig_len = codec::comp_encode(&mut esig[1..], &sig);
    assert!(sig_len != 0, "signature encoding failed");
    esig.truncate(1 + sig_len);
    esig
}

/// Verify an encoded signature over `msg` with its 40-byte nonce.
fn verify_internal(pk: &PublicKey, msg: &[u8], nonce: &[u8; 40], esig: &[u8]) -> bool {
    let logn = pk.logn;
    let n = 1usize << logn;

    // Decode the signature.
    if esig.is_empty() || esig[0] != 0x20 + logn as u8 {
        return false;
    }
    let mut sig = vec![0i16; n];
    if codec::comp_decode(&mut sig, &esig[1..]) != esig.len() - 1 {
        return false;
    }

    // The hashed point covers nonce ‖ message, mirroring sign_internal.
    let signed: Vec<u8> = nonce.iter().copied().chain(msg.iter().copied()).collect();
    false_or_ok(pk, &signed, &sig, logn)
}

/// Core verification: hash `signed` to the point c, then accept iff
/// ‖(s2·h − c mod (X^n+1, q), s2)‖² ≤ beta² (via `mq::verify_raw`).
fn false_or_ok(pk: &PublicKey, signed: &[u8], sig: &[i16], logn: u32) -> bool {
    let n = 1usize << logn;
    let mut h_ntt = pk.h.clone();
    mq::to_ntt_monty(&mut h_ntt, logn);

    let mut hm = vec![0u16; n];
    let mut sc = InnerShake256::inject_all(&[signed]);
    common::hash_to_point_vartime(&mut sc, &mut hm);

    mq::verify_raw(&hm, sig, &h_ntt, logn)
}

macro_rules! instantiate_falcon {
    ($mod_name:ident, $logn:literal, $n:literal, $sk_len:literal, $pk_len:literal) => {
        /// Falcon API bound to a specific parameter set (degree 2^logn).
        pub mod $mod_name {
            use super::{keygen_internal, sign_internal, verify_internal, PublicKey, SecretKey};

            /// Maximum signature size (unencoded message excluded): 2 (len)
            /// + 40 (nonce) + encoded signature. The reference bound for
            ///   compressed signatures is 1 + (n·12)/8 + 32 + margin.
            pub const CRYPTO_BYTES: usize = 2 + 40 + $n * 12 / 8 + 33;
            /// Secret-key size in bytes.
            pub const CRYPTO_SECRETKEYBYTES: usize = $sk_len;
            /// Public-key size in bytes.
            pub const CRYPTO_PUBLICKEYBYTES: usize = $pk_len;

            /// FIPS-style keygen: all entropy comes from the 48-byte seed
            /// (SHAKE256-expanded, exactly like the reference).
            pub fn keygen(seed: &[u8; 48]) -> (SecretKey, PublicKey) {
                keygen_internal($logn, seed)
            }

            /// Sign `msg` with the given 40-byte nonce and 48-byte signing
            /// seed (both must be fresh uniform randomness). Returns the
            /// encoded signature (header ‖ compressed s2).
            pub fn sign(
                sk: &SecretKey,
                msg: &[u8],
                nonce: &[u8; 40],
                sig_seed: &[u8; 48],
            ) -> Vec<u8> {
                assert_eq!(sk.logn, $logn);
                sign_internal(sk, msg, nonce, sig_seed)
            }

            /// Verify an encoded signature over `msg` with its 40-byte
            /// nonce.
            pub fn verify(pk: &PublicKey, msg: &[u8], nonce: &[u8; 40], esig: &[u8]) -> bool {
                assert_eq!(pk.logn, $logn);
                verify_internal(pk, msg, nonce, esig)
            }

            /// Decode a public key.
            pub fn public_key_from_bytes(bytes: &[u8]) -> Option<PublicKey> {
                PublicKey::from_bytes(bytes, $logn)
            }

            /// Decode a secret key.
            pub fn secret_key_from_bytes(bytes: &[u8]) -> Option<SecretKey> {
                SecretKey::from_bytes(bytes, $logn)
            }
        }
    };
}

instantiate_falcon!(falcon512, 9, 512, 1281, 897);
instantiate_falcon!(falcon1024, 10, 1024, 2305, 1793);

#[cfg(test)]
mod tests {
    use super::*;

    /// Scheme-level smoke test through the public API (the byte-exact
    /// KAT coverage lives in `tests/falcon_kat.rs`).
    #[test]
    fn keygen_sign_verify_roundtrip_and_serialization() {
        let seed = [42u8; 48];
        let (sk, pk) = falcon512::keygen(&seed);

        let nonce = [7u8; 40];
        let sig_seed = [9u8; 48];
        let msg = b"falcon smoke test message";
        let esig = falcon512::sign(&sk, msg, &nonce, &sig_seed);
        assert!(falcon512::verify(&pk, msg, &nonce, &esig));
        assert!(!falcon512::verify(&pk, b"tampered", &nonce, &esig));

        // Canonical key serialization roundtrips (length/header checks).
        let pk2 = falcon512::public_key_from_bytes(pk.to_bytes()).expect("well-formed pk");
        let sk2 = falcon512::secret_key_from_bytes(sk.to_bytes()).expect("well-formed sk");
        assert_eq!(pk2.to_bytes(), pk.to_bytes());
        assert_eq!(sk2.to_bytes(), sk.to_bytes());
        assert!(falcon512::verify(&pk2, msg, &nonce, &esig));

        // Truncated encodings are rejected.
        assert!(falcon512::secret_key_from_bytes(&sk.to_bytes()[..1279]).is_none());
        assert!(falcon512::public_key_from_bytes(&pk.to_bytes()[..896]).is_none());
    }
}
