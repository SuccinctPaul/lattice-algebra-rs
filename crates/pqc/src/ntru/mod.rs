//! NTRU — the round-3 NTRU lattice-based KEM (specification of
//! 2020-10-16), ported from the submission's reference implementation.
//!
//! The core is the OWCPA (ind-CPA) scheme of [Sch18] with the standard
//! Fujisaki–Okamoto-style transform for the IND-CCA2 KEM: decapsulation
//! recovers `(r, m)`, verifies both are in the message space (avoiding
//! re-encryption, per Proposition 1 of [Sch18]) and, on any failure,
//! returns `SHA3-256(PRF key ‖ ciphertext)` instead of the session key —
//! implicit rejection without a validity oracle.
//!
//! [Sch18]: https://eprint.iacr.org/2018/1174
//!
//! Randomness is explicit: [`keygen`] takes the `SAMPLE_FG_BYTES` of DRBG
//! output the reference's `crypto_kem_keypair` draws plus the 32-byte PRF
//! key, [`encapsulate`] takes the `SAMPLE_RM_BYTES` for `(r, m)`.

pub mod params;
pub mod poly;
pub mod sampling;

pub use params::{
    NtruHps2048677, NtruHps2048821, NtruHps40961229, NtruHps4096821, NtruHrss701, NtruParams,
};

use crate::error::{InvalidInput, SchemeResult};
use sha3::digest::Digest;
use sha3::Sha3_256;
use std::marker::PhantomData;
use zeroize::Zeroize;

use poly::Poly;

// ===========================================================================
// Keys
// ===========================================================================

/// NTRU public key: `h = g / (3·f·g')` encoded with the sum-zero
/// `logq·(n−1)`-bit packing.
pub struct PublicKey<P: NtruParams> {
    bytes: Vec<u8>,
    _p: PhantomData<P>,
}

impl<P: NtruParams> Clone for PublicKey<P> {
    fn clone(&self) -> Self {
        Self {
            bytes: self.bytes.clone(),
            _p: PhantomData,
        }
    }
}

impl<P: NtruParams> PartialEq for PublicKey<P> {
    fn eq(&self, other: &Self) -> bool {
        self.bytes == other.bytes
    }
}

impl<P: NtruParams> std::fmt::Debug for PublicKey<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PublicKey").finish_non_exhaustive()
    }
}

impl<P: NtruParams> PublicKey<P> {
    /// The submission's public-key encoding.
    pub fn to_bytes(&self) -> Vec<u8> {
        self.bytes.clone()
    }

    /// Parse with a length check.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != P::PUBLICKEY_BYTES {
            return None;
        }
        Some(Self {
            bytes: bytes.to_vec(),
            _p: PhantomData,
        })
    }
}

/// NTRU secret key: `f ‖ f⁻¹ mod 3 ‖ (3f)⁻¹ mod (q, Φ_n) ‖ PRF key` in the
/// submission's packed encodings, with the 32-byte implicit-rejection PRF
/// key at the end.
pub struct SecretKey<P: NtruParams> {
    bytes: Vec<u8>,
    _p: PhantomData<P>,
}

impl<P: NtruParams> std::fmt::Debug for SecretKey<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SecretKey").finish_non_exhaustive()
    }
}

impl<P: NtruParams> Drop for SecretKey<P> {
    fn drop(&mut self) {
        self.bytes.zeroize();
    }
}

impl<P: NtruParams> SecretKey<P> {
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

/// NTRU ciphertext: the packed `c = r·h + lift(m)` (sum-zero `logq·(n−1)`
/// bits). A constructed ciphertext is always well-formed (length checked
/// in [`Ciphertext::from_bytes`]).
#[derive(Clone, PartialEq, Eq)]
pub struct Ciphertext<P: NtruParams> {
    bytes: Vec<u8>,
    _p: PhantomData<P>,
}

impl<P: NtruParams> Ciphertext<P> {
    /// The raw ciphertext bytes.
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Parse with a length check; `None` when `bytes` is not
    /// `CIPHERTEXT_BYTES` long. (Decapsulation itself never fails — the
    /// message-space validation inside catches any tampering.)
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        (bytes.len() == P::CIPHERTEXT_BYTES).then(|| Self {
            bytes: bytes.to_vec(),
            _p: PhantomData,
        })
    }
}

impl<P: NtruParams> AsRef<[u8]> for Ciphertext<P> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<P: NtruParams> AsMut<[u8]> for Ciphertext<P> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
}
impl<P: NtruParams> std::fmt::Debug for Ciphertext<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ciphertext").finish_non_exhaustive()
    }
}

// ===========================================================================
// OWCPA (ind-CPA core)
// ===========================================================================

/// `owcpa_keypair`: derive `(f, g)` from the seed, invert, and assemble
/// the packed keys. Returns the OWCPA secret-key bytes
/// (`f ‖ f⁻¹ ‖ f⁻¹h`, `2·PACK_TRINARY + PUBLICKEY` bytes).
fn owcpa_keypair<P: NtruParams>(seed: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let n = P::N;
    assert_eq!(seed.len(), P::SAMPLE_FG_BYTES, "keygen seed length");

    let (mut f, mut g) = if P::HPS {
        (
            sampling::sample_iid::<P>(&seed[..n - 1]),
            sampling::sample_fixed_type::<P>(&seed[n - 1..]),
        )
    } else {
        (
            sampling::sample_iid_plus::<P>(&seed[..n - 1]),
            sampling::sample_iid_plus::<P>(&seed[n - 1..2 * (n - 1)]),
        )
    };

    // invf_mod3 = f⁻¹ mod (3, Φ_n).
    let invf_mod3 = poly::s3_inv::<P>(&f);

    // Pack the ternary f BEFORE lifting — the secret key stores the
    // {0,1,2} representatives.
    let sk_f = poly::s3_tobytes::<P>(&f);

    // Lift f, g from Z_3 to Z_q.
    poly::z3_to_zq::<P>(&mut f);
    poly::z3_to_zq::<P>(&mut g);

    // HPS: g ← 3·g;  HRSS: g ← 3·(x−1)·g.
    let p3 = P::PLAINTEXT_MODULUS;
    if P::HPS {
        for c in g.iter_mut() {
            *c = p3.wrapping_mul(*c);
        }
    } else {
        let old = g.to_vec();
        for i in (1..n).rev() {
            g[i] = p3.wrapping_mul(old[i - 1].wrapping_sub(old[i]));
        }
        g[0] = p3.wrapping_mul(old[0]).wrapping_neg();
    }

    let gf = poly::rq_mul::<P>(&g, &f);
    let invgf = poly::rq_inv::<P>(&gf);

    let tmp = poly::rq_mul::<P>(&invgf, &f);
    let invh = poly::sq_mul::<P>(&tmp, &f);

    let tmp = poly::rq_mul::<P>(&invgf, &g);
    let h = poly::rq_mul::<P>(&tmp, &g);

    let mut sk = Vec::with_capacity(P::SECRETKEY_BYTES - 32);
    sk.extend_from_slice(&sk_f);
    sk.extend_from_slice(&poly::s3_tobytes::<P>(&invf_mod3));
    sk.extend_from_slice(&poly::sq_tobytes::<P>(&invh));

    let pk = poly::sq_tobytes::<P>(&h);
    (sk, pk)
}

/// `owcpa_enc`: `c = r·h + lift(m)` packed with the sum-zero encoding.
fn owcpa_enc<P: NtruParams>(pk: &[u8], r: &Poly, m: &Poly) -> Vec<u8> {
    let h = poly::rq_sum_zero_frombytes::<P>(pk);
    let mut ct = poly::rq_mul::<P>(r, &h);

    let liftm = if P::HPS {
        poly::lift_hps::<P>(m)
    } else {
        poly::lift_hrss::<P>(m)
    };
    for (cv, &lv) in ct.iter_mut().zip(liftm.iter()) {
        *cv = cv.wrapping_add(lv);
    }
    poly::sq_tobytes::<P>(&ct)
}

/// `owcpa_check_ciphertext`: the unused bits of the final byte are zero.
fn check_ciphertext<P: NtruParams>(ct: &[u8]) -> bool {
    let last = ct[P::PUBLICKEY_BYTES - 1] as u16;
    let unused = 0xffu16 << (8 - (7 & (P::LOGQ as usize * (P::N - 1))));
    (last & (unused & 0xff)) == 0
}

/// `owcpa_check_r`: `r ∈ {0,1,q−1}^(n−1) × {0}`.
fn check_r<P: NtruParams>(r: &[u16]) -> bool {
    let n = P::N;
    let q4 = (1 << P::LOGQ) - 4;
    let mut t: u32 = 0;
    for &c in r.iter().take(n - 1) {
        let c = c as u32;
        t |= (c + 1) & q4; // 0 iff c ∈ {−1,0,1,2}
        t |= (c + 2) & 4; // 1 iff c = 2
    }
    t |= r[n - 1] as u32;
    t == 0
}

/// `owcpa_check_m` (HPS): the counts of 1s and 2s in `m` are equal and
/// sum to the fixed weight.
fn check_m<P: NtruParams>(m: &[u16]) -> bool {
    let mut ps: u16 = 0;
    let mut ms: u16 = 0;
    for &c in m.iter() {
        ps += c & 1;
        ms += c & 2;
    }
    ps == (ms >> 1) && ms == P::WEIGHT as u16
}

/// `owcpa_dec`: recover the packed `(r, m)` pair and validate the
/// ciphertext. Returns `(rm_bytes, fail)` with `fail` true on rejection.
fn owcpa_dec<P: NtruParams>(ct: &[u8], sk: &[u8]) -> (Vec<u8>, bool) {
    let n = P::N;
    let c = poly::rq_sum_zero_frombytes::<P>(ct);
    let mut f = poly::s3_frombytes::<P>(&sk[..P::PACK_TRINARY_BYTES]);
    poly::z3_to_zq::<P>(&mut f);

    let cf = poly::rq_mul::<P>(&c, &f);
    let mf = poly::rq_to_s3::<P>(&cf);

    let finv3 = poly::s3_frombytes::<P>(&sk[P::PACK_TRINARY_BYTES..2 * P::PACK_TRINARY_BYTES]);
    let m = poly::s3_mul::<P>(&mf, &finv3);

    let mut fail = false;
    fail |= !check_ciphertext::<P>(ct);
    if P::HPS {
        fail |= !check_m::<P>(&m);
    }

    // b = c − lift(m); r = b / h mod (q, Φ_n) via the stored Sq inverse.
    let liftm = if P::HPS {
        poly::lift_hps::<P>(&m)
    } else {
        poly::lift_hrss::<P>(&m)
    };
    let mut b = c;
    for (bv, &lv) in b.iter_mut().zip(liftm.iter()) {
        *bv = bv.wrapping_sub(lv);
    }
    let invh = poly::sq_frombytes::<P>(
        &sk[2 * P::PACK_TRINARY_BYTES..2 * P::PACK_TRINARY_BYTES + P::PUBLICKEY_BYTES],
    );
    let r = poly::sq_mul::<P>(&b, &invh);

    fail |= !check_r::<P>(&r);

    let mut r = r;
    poly::zq_to_z3::<P>(&mut r);

    let mut rm = Vec::with_capacity(2 * P::PACK_TRINARY_BYTES);
    rm.extend_from_slice(&poly::s3_tobytes::<P>(&r));
    rm.extend_from_slice(&poly::s3_tobytes::<P>(&m));
    let _ = n;
    (rm, fail)
}

// ===========================================================================
// KEM
// ===========================================================================

/// NTRU key generation: `seed` is the reference's `randombytes(
/// SAMPLE_FG_BYTES)` draw and `prf_key` the trailing 32 secret bytes of
/// the decapsulation key.
pub fn keygen<P: NtruParams>(
    seed: &[u8],
    prf_key: &[u8; 32],
) -> SchemeResult<(SecretKey<P>, PublicKey<P>)> {
    InvalidInput::check_len(P::SAMPLE_FG_BYTES, seed.len())?;
    let (owcpa_sk, pk_bytes) = owcpa_keypair::<P>(seed);
    let mut sk = owcpa_sk;
    sk.extend_from_slice(prf_key);
    Ok((
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

/// NTRU encapsulation: `rm_seed` is the reference's `randombytes(
/// SAMPLE_RM_BYTES)` draw for `(r, m)`.
pub fn encapsulate<P: NtruParams>(
    ek: &PublicKey<P>,
    rm_seed: &[u8],
) -> SchemeResult<(Ciphertext<P>, SharedSecret)> {
    let n = P::N;
    InvalidInput::check_len(P::SAMPLE_RM_BYTES, rm_seed.len())?;

    let (r, m) = if P::HPS {
        (
            sampling::sample_iid::<P>(&rm_seed[..n - 1]),
            sampling::sample_fixed_type::<P>(&rm_seed[n - 1..]),
        )
    } else {
        (
            sampling::sample_iid::<P>(&rm_seed[..n - 1]),
            sampling::sample_iid::<P>(&rm_seed[n - 1..2 * (n - 1)]),
        )
    };

    // k = SHA3-256(rm).
    let mut hasher = Sha3_256::new();
    hasher.update(poly::s3_tobytes::<P>(&r));
    hasher.update(poly::s3_tobytes::<P>(&m));
    let k = hasher.finalize();

    let mut r_q = r;
    poly::z3_to_zq::<P>(&mut r_q);
    let ct = owcpa_enc::<P>(&ek.bytes, &r_q, &m);
    Ok((
        Ciphertext {
            bytes: ct,
            _p: PhantomData,
        },
        SharedSecret(k.into()),
    ))
}

/// NTRU decapsulation with implicit rejection: a ciphertext outside the
/// valid space yields `SHA3-256(PRF key ‖ ct)`.
pub fn decapsulate<P: NtruParams>(dk: &SecretKey<P>, ct: &Ciphertext<P>) -> SharedSecret {
    // A constructed ciphertext is length-validated (`Ciphertext::
    // from_bytes`); message-space violations still fold into implicit
    // rejection inside `owcpa_dec`.
    let (rm, fail) = owcpa_dec::<P>(&ct.bytes, &dk.bytes);
    let mut hasher = Sha3_256::new();
    hasher.update(&rm);
    let k_prime: [u8; 32] = hasher.finalize().into();

    // Implicit rejection: SHA3-256(prf_key ‖ ct).
    let prf_key = &dk.bytes[dk.bytes.len() - 32..];
    let mut hasher = Sha3_256::new();
    hasher.update(prf_key);
    hasher.update(&ct.bytes);
    let k_reject: [u8; 32] = hasher.finalize().into();

    SharedSecret(if fail { k_reject } else { k_prime })
}

/// Macro: bind the const-generic core to a concrete parameter set.
macro_rules! instantiate_ntru {
    ($mod_name:ident, $params:ident, $doc:expr) => {
        #[doc = $doc]
        pub mod $mod_name {
            pub use super::{Ciphertext, PublicKey, SecretKey, SharedSecret};

            /// NTRU key generation from the reference's keygen randomness
            /// plus the PRF key.
            ///
            /// # Errors
            /// [`InvalidInput::InvalidLength`](crate::InvalidInput::InvalidLength) on wrong-length `seed`.
            pub fn keygen(
                seed: &[u8],
                prf_key: &[u8; 32],
            ) -> super::SchemeResult<(
                SecretKey<super::params::$params>,
                PublicKey<super::params::$params>,
            )> {
                super::keygen::<super::params::$params>(seed, prf_key)
            }

            /// NTRU encapsulation with the reference's `(r, m)` randomness.
            ///
            /// # Errors
            /// [`InvalidInput::InvalidLength`](crate::InvalidInput::InvalidLength) on wrong-length `rm_seed`.
            pub fn encapsulate(
                ek: &PublicKey<super::params::$params>,
                rm_seed: &[u8],
            ) -> super::SchemeResult<(Ciphertext<super::params::$params>, SharedSecret)> {
                super::encapsulate::<super::params::$params>(ek, rm_seed)
            }

            /// NTRU decapsulation with implicit rejection.
            pub fn decapsulate(
                dk: &SecretKey<super::params::$params>,
                ct: &Ciphertext<super::params::$params>,
            ) -> SharedSecret {
                super::decapsulate::<super::params::$params>(dk, ct)
            }
            /// Batch keygen across the rayon pool (`parallel` feature):
            /// `seed[i]`/`prf_key[i]` drive key `i`; per-item errors
            /// (`InvalidLength`, `KeygenRetry`) are reported positionally.
            ///
            /// # Panics
            /// If the randomness slices do not pair up.
            #[cfg(feature = "parallel")]
            pub fn keygen_batch(
                seed: &[&[u8]],
                prf_key: &[[u8; 32]],
            ) -> Vec<
                super::SchemeResult<(
                    SecretKey<super::params::$params>,
                    PublicKey<super::params::$params>,
                )>,
            > {
                assert_eq!(seed.len(), prf_key.len(), "seeds and PRF keys must pair up");
                use rayon::prelude::*;

                seed.par_iter()
                    .enumerate()
                    .map(|(i, seed)| super::keygen::<super::params::$params>(seed, &prf_key[i]))
                    .collect()
            }

            /// Batch encapsulation across the rayon pool (`parallel`
            /// feature); `rm_seed[i]` must be fresh per-ciphertext
            /// randomness, per-item length errors reported positionally.
            #[cfg(feature = "parallel")]
            pub fn encapsulate_batch(
                ek: &PublicKey<super::params::$params>,
                rm_seed: &[&[u8]],
            ) -> Vec<super::SchemeResult<(Ciphertext<super::params::$params>, SharedSecret)>> {
                use rayon::prelude::*;

                rm_seed
                    .par_iter()
                    .map(|rm| super::encapsulate::<super::params::$params>(ek, rm))
                    .collect()
            }

            /// Batch decapsulation across the rayon pool (`parallel`
            /// feature), order-preserving.
            #[cfg(feature = "parallel")]
            pub fn decapsulate_batch(
                dk: &SecretKey<super::params::$params>,
                cts: &[Ciphertext<super::params::$params>],
            ) -> Vec<SharedSecret> {
                use rayon::prelude::*;

                cts.par_iter()
                    .map(|ct| super::decapsulate::<super::params::$params>(dk, ct))
                    .collect()
            }
        }
    };
}

instantiate_ntru!(ntruhps2048677, NtruHps2048677, "ntruhps2048677.");
instantiate_ntru!(ntruhps2048821, NtruHps2048821, "ntruhps2048821.");
instantiate_ntru!(ntruhps4096821, NtruHps4096821, "ntruhps4096821.");
instantiate_ntru!(ntruhps40961229, NtruHps40961229, "ntruhps40961229.");
instantiate_ntru!(ntruhrss701, NtruHrss701, "ntruhrss701.");

#[cfg(test)]
mod tests;
