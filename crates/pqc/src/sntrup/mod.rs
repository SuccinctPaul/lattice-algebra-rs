//! Streamlined NTRU Prime — the round-3 `sntrup` KEM (`ntruprime-20201007`),
//! ported from the submission's reference implementation. This is the
//! scheme deployed in OpenSSH (sntrup761).
//!
//! Ring: `R = Z[x]/(x^p − x − 1)` with `F_3` (centered −1/0/1) and `F_q`
//! (centered mod q) coefficient arithmetic; short polynomials of weight
//! `w` via `Short_fromlist`; ciphertexts are rounded polynomials plus a
//! SHA-512-based confirmation hash; decapsulation re-encrypts and, on
//! mismatch, substitutes the stored `rho` and re-hashes (implicit
//! rejection).
//!
//! Randomness is explicit and mirrors the reference's `urandom32` stream:
//! [`keygen`] takes `p` little-endian `u32` words (4·p bytes) for `g`, the
//! same for `f`, plus the raw `rho` (`(p+3)/4` bytes); [`encapsulate`]
//! takes `p` words for the encryption randomness `r`. On the unlikely
//! failure of `R3_recip` the reference resamples — here [`keygen`]
//! returns `None` and the caller resamples.

pub mod encoding;
pub mod params;
pub mod poly;

pub use params::{
    Sntrup1013, Sntrup1277, Sntrup653, Sntrup761, Sntrup857, Sntrup953, SntrupParams,
};

use encoding::small_encode;
use poly::{rq_mult3, rq_mult_small, r3_from_rq, r3_mult, r3_recip, rq_recip3, round3};
use sha2::Digest;
use std::marker::PhantomData;
use zeroize::Zeroize;

use poly::{Small, Fq};

// ===========================================================================
// Keys / shared secret
// ===========================================================================

/// Public key: the encoded `Rq` polynomial `h = f⁻¹·3g`.
pub struct PublicKey<P: SntrupParams> {
    bytes: Vec<u8>,
    _p: PhantomData<P>,
}

impl<P: SntrupParams> Clone for PublicKey<P> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            _p: PhantomData,
        }
    }
}

impl<P: SntrupParams> PartialEq for PublicKey<P> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl<P: SntrupParams> std::fmt::Debug for PublicKey<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PublicKey").finish_non_exhaustive()
    }
}

impl<P: SntrupParams> PublicKey<P> {
    /// The submission's public-key encoding (`Rq_encode(h)`).
    pub fn to_bytes(&self) -> Vec<u8> {
        self.bytes.clone()
    }

    /// Parse with a length check.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != P::RQ_BYTES {
            return None;
        }
        Some(Self {
            bytes: bytes.to_vec(),
            _p: PhantomData,
        })
    }
}

/// Secret key: `f ‖ ginv ‖ pk ‖ rho ‖ Hash₄(pk)`.
pub struct SecretKey<P: SntrupParams> {
    bytes: Vec<u8>,
    _p: PhantomData<P>,
}

impl<P: SntrupParams> std::fmt::Debug for SecretKey<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SecretKey").finish_non_exhaustive()
    }
}

impl<P: SntrupParams> Drop for SecretKey<P> {
    fn drop(&mut self) {
        self.bytes.zeroize();
    }
}

impl<P: SntrupParams> SecretKey<P> {
    /// The submission's secret-key encoding.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.bytes.clone()
    }

    /// Parse with a length check.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != P::SECRETKEY_BYTES {
            return None;
        }
        Some(Self {
            bytes: bytes.to_vec(),
            _p: PhantomData,
        })
    }
}

/// A shared secret; redacted `Debug` and zeroized on drop.
pub struct SharedSecret([u8; 32]);

impl SharedSecret {
    /// The 32 secret bytes.
    pub fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }
}

impl std::fmt::Debug for SharedSecret {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SharedSecret").finish_non_exhaustive()
    }
}

impl Drop for SharedSecret {
    fn drop(&mut self) {
        self.0.zeroize();
    }
}

// ===========================================================================
// Hashes (SHA-512-based, first 32 bytes)
// ===========================================================================

/// `Hash_prefix(b, in) = SHA512(b ‖ in)[0..32]`.
fn hash_prefix(b: u8, input: &[&[u8]]) -> [u8; 32] {
    let mut hasher = sha2::Sha512::new();
    hasher.update([b]);
    for part in input {
        hasher.update(part);
    }
    let full = hasher.finalize();
    let mut out = [0u8; 32];
    out.copy_from_slice(&full[..32]);
    out
}

// ===========================================================================
// Core
// ===========================================================================

/// `urandom32` byte stream → `p` little-endian `u32` words.
fn urandom_words<P: SntrupParams>(random: &[u8]) -> Vec<u32> {
    assert_eq!(random.len(), 4 * P::P, "randomness length");
    random
        .chunks_exact(4)
        .map(|c| u32::from_le_bytes([c[0], c[1], c[2], c[3]]))
        .collect()
}

/// `Small_random`: uniform ternary polynomial — each word masked to 30
/// bits, scaled by 3, and the top two bits dropped.
fn small_random_from_bytes<P: SntrupParams>(random: &[u8]) -> Vec<Small> {
    urandom_words::<P>(random)
        .iter()
        .map(|&word| ((((word & 0x3fff_ffff).wrapping_mul(3)) >> 30) as i8) - 1)
        .collect()
}

/// `Short_random`: random weight-`w` short polynomial via
/// `Short_fromlist`.
fn short_from_bytes<P: SntrupParams>(random: &[u8]) -> Vec<Small> {
    encoding::short_fromlist::<P>(&urandom_words::<P>(random))
}

/// `Encrypt`: `Round(h·r)` — rounded polynomial ciphertext core.
fn encrypt<P: SntrupParams>(r: &[Small], h: &[Fq]) -> Vec<Fq> {
    let hr = rq_mult_small::<P>(h, r);
    round3::<P>(&hr)
}

/// `Decrypt`: recover `r` from `c·f·3` reduced to `R3` times `ginv`,
/// forcing weight `w` (branchlessly) per the reference.
fn decrypt<P: SntrupParams>(c: &[Fq], f: &[Small], ginv: &[Small]) -> Vec<Small> {
    let cf = rq_mult_small::<P>(c, f);
    let cf3 = rq_mult3::<P>(&cf);
    let e = r3_from_rq::<P>(&cf3);
    let ev = r3_mult::<P>(&e, ginv);
    let mask = poly::weightw_mask::<P>(&ev) as i8;
    let mut r = vec![0 as Small; P::P];
    for i in 0..P::W {
        r[i] = ((ev[i] ^ 1) & !mask) ^ 1;
    }
    for (slot, &ev) in r.iter_mut().skip(P::W).zip(ev.iter().skip(P::W)) {
        *slot = ev & !mask;
    }
    r
}

/// Raw keygen material before KEM framing.
struct ZKeygen {
    pk: Vec<u8>,
    sk_core: Vec<u8>,
}

/// `ZKeyGen`: `(pk, sk_core)` from the sampled `(g, f)` randomness.
fn zkeygen<P: SntrupParams>(g_random: &[u8], f_random: &[u8]) -> Option<ZKeygen> {
    let g = small_random_from_bytes::<P>(g_random);
    let ginv = r3_recip::<P>(&g)?;
    let f = short_from_bytes::<P>(f_random);
    let finv = rq_recip3::<P>(&f);
    let h = rq_mult_small::<P>(&finv, &g);
    let pk = encoding::rq_encode::<P>(&h);
    let mut sk_core = encoding::small_encode::<P>(&f);
    sk_core.extend_from_slice(&encoding::small_encode::<P>(&ginv));
    Some(ZKeygen { pk, sk_core })
}

/// `ZEncrypt`: ciphertext core from `(r, pk)`.
fn zencrypt<P: SntrupParams>(r: &[Small], pk: &[u8]) -> Vec<u8> {
    let h = encoding::rq_decode::<P>(pk);
    let c = encrypt::<P>(r, &h);
    encoding::rounded_encode::<P>(&c)
}

/// `ZDecrypt`: ciphertext core back to `r`.
fn zdecrypt<P: SntrupParams>(ct: &[u8], sk: &[u8]) -> Vec<Small> {
    let f = encoding::small_decode::<P>(&sk[..P::SMALL_BYTES]);
    let ginv = encoding::small_decode::<P>(&sk[P::SMALL_BYTES..2 * P::SMALL_BYTES]);
    let c = encoding::rounded_decode::<P>(ct);
    decrypt::<P>(&c, &f, &ginv)
}

// ===========================================================================
// KEM
// ===========================================================================

/// SNTRU key generation. `g_random` / `f_random` are the reference's
/// `urandom32` streams (`4·p` bytes each) driving `Small_random(g)` and
/// `Short_random(f)`; `rho` is the `SMALL_BYTES`-byte random salt stored
/// for decapsulation's implicit rejection. Returns `None` when the first
/// `g` is not invertible in `R3` (probability ≈ 1/q; the reference
/// resamples — callers should do the same with fresh randomness).
pub fn keygen<P: SntrupParams>(
    g_random: &[u8],
    f_random: &[u8],
    rho: &[u8],
) -> Option<(SecretKey<P>, PublicKey<P>)> {
    assert_eq!(rho.len(), P::SMALL_BYTES, "rho length");
    let ZKeygen { pk: pk_bytes, sk_core } = zkeygen::<P>(g_random, f_random)?;

    let mut sk = sk_core;
    sk.extend_from_slice(&pk_bytes);
    sk.extend_from_slice(rho);
    let cache = hash_prefix(4, &[&pk_bytes]);
    sk.extend_from_slice(&cache);

    Some((
        SecretKey {
            bytes: sk,
            _p: PhantomData,
        },
        PublicKey {
            bytes: pk_bytes,
            _p: PhantomData,
        },
    ))
}

/// `Hide`: ciphertext core + confirmation over `(r_enc, pk, cache)`.
fn hide<P: SntrupParams>(
    r: &[Small],
    pk: &[u8],
    cache: &[u8; 32],
) -> (Vec<u8>, Vec<u8>) {
    let r_enc = small_encode::<P>(r);
    let mut ct = zencrypt::<P>(r, pk);
    let confirm = hash_prefix(2, &[&hash_prefix(3, &[&r_enc]), cache]);
    ct.extend_from_slice(&confirm);
    (ct, r_enc)
}

/// `HashSession(b, r_enc, ct)`.
fn hash_session(b: u8, r_enc: &[u8], ct_and_confirm: &[u8]) -> SharedSecret {
    let prefix = hash_prefix(3, &[r_enc]);
    SharedSecret(hash_prefix(b, &[&prefix, ct_and_confirm]))
}

/// SNTRU encapsulation. `r_random` is the reference's `urandom32` stream
/// (`4·p` bytes) driving `Short_random(r)`.
pub fn encapsulate<P: SntrupParams>(
    ek: &PublicKey<P>,
    r_random: &[u8],
) -> (Vec<u8>, SharedSecret) {
    let r = short_from_bytes::<P>(r_random);
    let pk_bytes = ek.to_bytes();
    let cache = hash_prefix(4, &[&pk_bytes]);
    let (ct, r_enc) = hide::<P>(&r, &pk_bytes, &cache);
    let k = hash_session(1, &r_enc, &ct);
    (ct, k)
}

/// SNTRU decapsulation with implicit rejection: re-encryption mismatch
/// yields `HashSession(2, rho, ct)` instead of the session key.
pub fn decapsulate<P: SntrupParams>(dk: &SecretKey<P>, ct: &[u8]) -> SharedSecret {
    let sk = &dk.bytes;
    let pk = &sk[2 * P::SMALL_BYTES..2 * P::SMALL_BYTES + P::RQ_BYTES];
    let rho = &sk[2 * P::SMALL_BYTES + P::RQ_BYTES..2 * P::SMALL_BYTES + P::RQ_BYTES + P::SMALL_BYTES];
    let cache_offset = 2 * P::SMALL_BYTES + P::RQ_BYTES + P::SMALL_BYTES;
    let cache: [u8; 32] = sk[cache_offset..cache_offset + 32].try_into().unwrap();

    // Wrong-length ciphertexts take the rejection path directly.
    if ct.len() != P::CIPHERTEXT_BYTES {
        let prefix = hash_prefix(3, &[rho]);
        let mut input = prefix.to_vec();
        input.extend_from_slice(ct);
        return SharedSecret(hash_prefix(2, &[&input]));
    }

    let ct_core = &ct[..P::ROUNDED_BYTES];
    let r = zdecrypt::<P>(ct_core, sk);
    let (cnew, r_enc_new) = hide::<P>(&r, pk, &cache);

    // Ciphertexts_diff_mask: 0 if equal, −1 if different.
    let mut different: u16 = 0;
    for (a, b) in ct.iter().zip(cnew.iter()) {
        different |= (*a ^ *b) as u16;
    }
    let diff_mask: i8 = if different == 0 { 0 } else { -1 };

    // On mismatch, substitute rho for r_enc and shift the session-hash
    // domain byte from 1 to 1+mask = 0.
    let r_enc = if diff_mask == 0 {
        r_enc_new
    } else {
        rho.to_vec()
    };
    hash_session((1 + diff_mask) as u8, &r_enc, ct)
}

/// Macro: bind the const-generic core to a concrete parameter set.
macro_rules! instantiate_sntrup {
    ($mod_name:ident, $params:ident, $doc:expr) => {
        #[doc = $doc]
        pub mod $mod_name {
            pub use super::{PublicKey, SecretKey, SharedSecret};

            /// SNTRU key generation (returns `None` if `g` is not
            /// invertible — resample with fresh randomness).
            pub fn keygen(
                g_random: &[u8],
                f_random: &[u8],
                rho: &[u8],
            ) -> Option<(
                SecretKey<super::params::$params>,
                PublicKey<super::params::$params>,
            )> {
                super::keygen::<super::params::$params>(g_random, f_random, rho)
            }

            /// SNTRU encapsulation.
            pub fn encapsulate(
                ek: &PublicKey<super::params::$params>,
                r_random: &[u8],
            ) -> (Vec<u8>, SharedSecret) {
                super::encapsulate::<super::params::$params>(ek, r_random)
            }

            /// SNTRU decapsulation with implicit rejection.
            pub fn decapsulate(
                dk: &SecretKey<super::params::$params>,
                ct: &[u8],
            ) -> SharedSecret {
                super::decapsulate::<super::params::$params>(dk, ct)
            }
        }
    };
}

instantiate_sntrup!(sntrup653, Sntrup653, "sntrup653.");
instantiate_sntrup!(sntrup761, Sntrup761, "sntrup761 (deployed in OpenSSH).");
instantiate_sntrup!(sntrup857, Sntrup857, "sntrup857.");
instantiate_sntrup!(sntrup953, Sntrup953, "sntrup953.");
instantiate_sntrup!(sntrup1013, Sntrup1013, "sntrup1013.");
instantiate_sntrup!(sntrup1277, Sntrup1277, "sntrup1277.");

#[cfg(test)]
mod tests;

