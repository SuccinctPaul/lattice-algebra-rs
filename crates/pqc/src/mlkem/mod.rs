//! ML-KEM — the FIPS 203 module-lattice key-encapsulation mechanism, built
//! directly on the L0–L4 base layers.
//!
//! Scope notes:
//! - N = 256, q = 3329 (FIPS 203). The NTT is the standard's exact
//!   seven-layer transform with `BaseCaseMultiply` pair products (see
//!   [`ntt`] — `q`'s 2-adicity is 7, so the generic engine cannot serve this
//!   scheme), making the implementation byte-exact with the ACVP/KAT
//!   vectors.
//! - `Decaps` follows the spec's implicit-rejection semantics: a
//!   re-encryption mismatch yields `J(z ‖ c)` instead of an error, and
//!   ciphertexts of the wrong length are treated the same way (no validity
//!   oracle).
//! - Key checks follow the spec's optional `EncapsulationKeyCheck` /
//!   `DecapsulationKeyCheck`: `from_bytes` enforces the length and the
//!   `coefficient < q` modulus bound.
//! - All three parameter sets (ML-KEM-512/768/1024) are provided as
//!   zero-sized types behind [`MlKemParams`].

pub mod encoding;
pub mod ntt;
pub mod params;

pub use params::{MlKem1024, MlKem512, MlKem768, MlKemParams, N, Q};

use sha3::digest::{Digest, ExtendableOutput, XofReader};
use sha3::{Sha3_256, Sha3_512, Shake256};
use std::marker::PhantomData;

use algebra::crypto::xof::Shake128Xof;

// ===========================================================================
// Spec hash functions (FIPS 203, §4.1): H = SHA3-256, G = SHA3-512,
// J/PRF = SHAKE-256.
// ===========================================================================

fn sha3_256(parts: &[&[u8]]) -> [u8; 32] {
    let mut h = Sha3_256::new();
    for part in parts {
        h.update(part);
    }
    h.finalize().into()
}

/// `G(...)`: a 64-byte SHA3-512 digest split into two 32-byte halves.
fn hash_g(parts: &[&[u8]]) -> ([u8; 32], [u8; 32]) {
    let mut h = Sha3_512::new();
    for part in parts {
        h.update(part);
    }
    let out = h.finalize();
    let mut first = [0u8; 32];
    first.copy_from_slice(&out[..32]);
    let mut second = [0u8; 32];
    second.copy_from_slice(&out[32..]);
    (first, second)
}

/// SHAKE-256 squeeze over concatenated parts (shared by `PRF` and `J`).
fn shake256_squeeze(parts: &[&[u8]], out: &mut [u8]) {
    use sha3::digest::Update;
    let mut hasher = Shake256::default();
    for part in parts {
        hasher.update(part);
    }
    hasher.finalize_xof().read(out);
}

/// `PRF_η(s, b) = SHAKE256(s ‖ bytes(b))`, squeezed to `out_len` bytes
/// (`64·η` for the noise samplers).
fn prf(seed: &[u8; 32], counter: u8, out_len: usize) -> Vec<u8> {
    let mut out = vec![0u8; out_len];
    shake256_squeeze(&[seed, &[counter]], &mut out);
    out
}

/// `J(...) = SHAKE256(...)`, 32 bytes — the implicit-rejection hash.
fn j_hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut out = [0u8; 32];
    shake256_squeeze(parts, &mut out);
    out
}

// ===========================================================================
// Samplers and small polynomial helpers
// ===========================================================================

/// FIPS 203 `SamplePolyCBD_η(B)` (Algorithm 8): coefficient `i` is
/// `x − y` with `x = Σ_{j<η} b[2ηi + j]` and `y = Σ_{j<η} b[2ηi + η + j]`
/// over the LSB-first bit stream — i.e. the *first* η bits of the
/// coefficient's chunk minus the *next* η bits (note this grouping differs
/// from the C reference's interleaved `b[2j] − b[2j+1]` pairs).
fn sample_cbd(bytes: &[u8], eta: usize) -> [i64; N] {
    debug_assert_eq!(bytes.len(), 64 * eta, "PRF output length for CBD_η");
    let bit = |idx: usize| -> i64 { ((bytes[idx / 8] >> (idx % 8)) & 1) as i64 };
    let mut out = [0i64; N];
    for (i, slot) in out.iter_mut().enumerate() {
        let base = 2 * eta * i;
        let x: i64 = (0..eta).map(|j| bit(base + j)).sum();
        let y: i64 = (0..eta).map(|j| bit(base + eta + j)).sum();
        *slot = x - y;
    }
    out
}

fn poly_add(a: &mut [u64; N], b: &[u64; N]) {
    for (x, &y) in a.iter_mut().zip(b.iter()) {
        *x = (*x + y) % Q;
    }
}

/// Constant-time byte-slice equality (decapsulation compares the
/// re-encryption against the input ciphertext).
fn ct_eq(a: &[u8], b: &[u8]) -> bool {
    debug_assert_eq!(a.len(), b.len());
    let mut acc = 0u8;
    for (x, y) in a.iter().zip(b.iter()) {
        acc |= x ^ y;
    }
    acc == 0
}

// ===========================================================================
// K-PKE (FIPS 203, §5): the CPA-secure PKE inside the FO transform
// ===========================================================================

/// K-PKE public key: `t̂` (NTT domain) and the matrix seed `ρ`.
pub struct KpkePublicKey {
    pub t_hat: Vec<[u64; N]>,
    pub rho: [u8; 32],
}

/// K-PKE secret key: `ŝ` in the NTT domain.
pub struct KpkeSecretKey {
    pub s_hat: Vec<[u64; N]>,
}

/// FIPS 203 `K-PKE.KeyGen(d)` (Algorithm 13).
pub fn kpke_keygen<P: MlKemParams, const K: usize>(d: &[u8; 32]) -> (KpkePublicKey, KpkeSecretKey) {
    // (ρ, σ) ← G(d ‖ k): byte 33 is the module dimension, for domain
    // separation between parameter sets (FIPS 203, Alg. 13, footnote 1).
    let (rho, sigma) = hash_g(&[d, &[K as u8]]);
    let a_hat = ntt::expand_a::<Shake128Xof, K>(&rho);

    let s_hat: Vec<[u64; N]> = (0..K)
        .map(|i| {
            let bytes = prf(&sigma, i as u8, 64 * P::ETA1);
            ntt::ntt_coeffs(&sample_cbd(&bytes, P::ETA1))
        })
        .collect();
    let e_hat: Vec<[u64; N]> = (0..K)
        .map(|i| {
            let bytes = prf(&sigma, (K + i) as u8, 64 * P::ETA1);
            ntt::ntt_coeffs(&sample_cbd(&bytes, P::ETA1))
        })
        .collect();

    let mut t_hat: Vec<[u64; N]> = Vec::with_capacity(K);
    for (row, e) in a_hat.iter().zip(&e_hat) {
        let mut acc = [0u64; N];
        for (entry, s) in row.iter().zip(&s_hat) {
            ntt::pointwise_mul_add(&mut acc, entry, s);
        }
        poly_add(&mut acc, e);
        t_hat.push(acc);
    }

    (KpkePublicKey { t_hat, rho }, KpkeSecretKey { s_hat })
}

/// FIPS 203 `K-PKE.Encrypt(ek_PKE, m, r)` (Algorithm 14). `m` is the
/// 32-byte message; `r` the 32-byte encryption randomness.
pub fn kpke_encrypt<P: MlKemParams, const K: usize>(
    ek: &[u8],
    m: &[u8; 32],
    r: &[u8; 32],
) -> Vec<u8> {
    assert_eq!(ek.len(), 384 * K + 32, "K-PKE encapsulation-key length");
    let t_hat: Vec<[u64; N]> = (0..K)
        .map(|i| encoding::byte_decode(&ek[i * 384..(i + 1) * 384], 12))
        .collect();
    let mut rho = [0u8; 32];
    rho.copy_from_slice(&ek[384 * K..]);
    let a_hat = ntt::expand_a::<Shake128Xof, K>(&rho);

    let y_hat: Vec<[u64; N]> = (0..K)
        .map(|i| {
            // N restarts at 0 in K-PKE.Encrypt: y uses counters 0..k−1.
            let bytes = prf(r, i as u8, 64 * P::ETA1);
            ntt::ntt_coeffs(&sample_cbd(&bytes, P::ETA1))
        })
        .collect();
    let e1: Vec<[i64; N]> = (0..K)
        .map(|i| {
            let bytes = prf(r, (K + i) as u8, 64 * P::ETA2);
            sample_cbd(&bytes, P::ETA2)
        })
        .collect();
    let e2_bytes = prf(r, (2 * K) as u8, 64 * P::ETA2);
    let e2 = sample_cbd(&e2_bytes, P::ETA2);

    let mut c = Vec::with_capacity(32 * K * P::DU + 32 * P::DV);
    // u_i = InvNTT(Σ_j Â[j][i]∘ŷ_j) + e1_i — the matrix is consumed
    // transposed relative to keygen.
    for col in 0..K {
        let mut acc = [0u64; N];
        for (row, y) in a_hat.iter().zip(&y_hat) {
            ntt::pointwise_mul_add(&mut acc, &row[col], y);
        }
        let mut u = ntt::intt_coeffs(&acc);
        for (uc, &e) in u.iter_mut().zip(e1[col].iter()) {
            *uc = (*uc + e).rem_euclid(Q as i64);
        }
        let cu: [u64; N] = u.map(|val| encoding::compress(val as u64, P::DU as u32));
        c.extend_from_slice(&encoding::byte_encode(&cu, P::DU));
    }
    // v = InvNTT(Σ_i t̂_i∘ŷ_i) + e2 + μ.
    let mut acc = [0u64; N];
    for (t, y) in t_hat.iter().zip(&y_hat) {
        ntt::pointwise_mul_add(&mut acc, t, y);
    }
    let mut v = ntt::intt_coeffs(&acc);
    let mu = encoding::byte_decode(m, 1);
    for ((vc, &e), &mv) in v.iter_mut().zip(e2.iter()).zip(mu.iter()) {
        *vc = (*vc + e + encoding::decompress(mv, 1) as i64).rem_euclid(Q as i64);
    }
    let cv: [u64; N] = v.map(|val| encoding::compress(val as u64, P::DV as u32));
    c.extend_from_slice(&encoding::byte_encode(&cv, P::DV));
    c
}

/// FIPS 203 `K-PKE.Decrypt(dk_PKE, c)` (Algorithm 15): recovers the 32-byte
/// message. `dk` is `ŝ`, `384k` bytes in the `ByteEncode12` encoding.
pub fn kpke_decrypt<P: MlKemParams, const K: usize>(dk: &[u8], c: &[u8]) -> [u8; 32] {
    assert_eq!(dk.len(), 384 * K, "K-PKE decapsulation-key length");
    assert_eq!(
        c.len(),
        32 * K * P::DU + 32 * P::DV,
        "K-PKE ciphertext length"
    );
    let s_hat: Vec<[u64; N]> = (0..K)
        .map(|i| encoding::byte_decode(&dk[i * 384..(i + 1) * 384], 12))
        .collect();
    decrypt_with_s_hat::<P, K>(&s_hat, c)
}

/// Core of `K-PKE.Decrypt` over already-decoded secret rows (the ML-KEM
/// decapsulation key carries `ŝ` structurally).
fn decrypt_with_s_hat<P: MlKemParams, const K: usize>(s_hat: &[[u64; N]], c: &[u8]) -> [u8; 32] {
    let du_bytes = 32 * P::DU;
    let mut acc = [0u64; N];
    for (i, s) in s_hat.iter().enumerate() {
        let u = encoding::byte_decode(&c[i * du_bytes..(i + 1) * du_bytes], P::DU);
        let u_decompressed: [u64; N] = u.map(|v| encoding::decompress(v, P::DU as u32));
        let u_hat = ntt::ntt_coeffs(&u_decompressed.map(|v| v as i64));
        ntt::pointwise_mul_add(&mut acc, s, &u_hat);
    }
    let mut w = ntt::intt_coeffs(&acc);
    let c2 = &c[du_bytes * s_hat.len()..];
    let v = encoding::byte_decode(c2, P::DV);
    for (wc, &vd) in w.iter_mut().zip(v.iter()) {
        *wc -= encoding::decompress(vd, P::DV as u32) as i64;
    }
    let w: [u64; N] = w.map(|v| v.rem_euclid(Q as i64) as u64);
    let mbits: [u64; N] = w.map(|v| encoding::compress(v, 1));
    encoding::byte_encode(&mbits, 1)
        .try_into()
        .expect("32 bytes")
}

// ===========================================================================
// ML-KEM (FIPS 203, §6): the FO-transformed KEM
// ===========================================================================

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
        use zeroize::Zeroize;
        self.0.zeroize();
    }
}

/// Encapsulation key (FIPS 203 `ek`, `384k + 32` bytes encoded).
pub struct EncapsulationKey<P: MlKemParams> {
    t_hat: Vec<[u64; N]>,
    rho: [u8; 32],
    _p: PhantomData<P>,
}

impl<P: MlKemParams> Clone for EncapsulationKey<P> {
    fn clone(&self) -> Self {
        Self {
            t_hat: self.t_hat.clone(),
            rho: self.rho,
            _p: PhantomData,
        }
    }
}

impl<P: MlKemParams> PartialEq for EncapsulationKey<P> {
    fn eq(&self, other: &Self) -> bool {
        self.t_hat == other.t_hat && self.rho == other.rho
    }
}

impl<P: MlKemParams> EncapsulationKey<P> {
    /// FIPS 203 `ekEncode`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(P::EK_BYTES);
        for row in &self.t_hat {
            out.extend_from_slice(&encoding::byte_encode(row, 12));
        }
        out.extend_from_slice(&self.rho);
        out
    }

    /// FIPS 203 `ekDecode` combined with the (optional) modulus part of
    /// `EncapsulationKeyCheck`: wrong length or any NTT coefficient ≥ q
    /// yields `None`.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != P::EK_BYTES {
            return None;
        }
        let mut t_hat = Vec::with_capacity(P::K);
        for i in 0..P::K {
            let row = encoding::byte_decode(&bytes[i * 384..(i + 1) * 384], 12);
            if row.iter().any(|&v| v >= Q) {
                return None;
            }
            t_hat.push(row);
        }
        let mut rho = [0u8; 32];
        rho.copy_from_slice(&bytes[384 * P::K..]);
        Some(Self {
            t_hat,
            rho,
            _p: PhantomData,
        })
    }
}

impl<P: MlKemParams> std::fmt::Debug for EncapsulationKey<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EncapsulationKey").finish_non_exhaustive()
    }
}

/// Decapsulation key in the FIPS 203 augmented format:
/// `dk = dk_PKE ‖ ek ‖ H(ek) ‖ z` (`768k + 96` bytes encoded).
pub struct DecapsulationKey<P: MlKemParams> {
    s_hat: Vec<[u64; N]>,
    ek: EncapsulationKey<P>,
    h: [u8; 32],
    z: [u8; 32],
    _p: PhantomData<P>,
}

impl<P: MlKemParams> DecapsulationKey<P> {
    /// FIPS 203 `dkEncode` (the augmented decapsulation key).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(P::DK_BYTES);
        for row in &self.s_hat {
            out.extend_from_slice(&encoding::byte_encode(row, 12));
        }
        out.extend_from_slice(&self.ek.to_bytes());
        out.extend_from_slice(&self.h);
        out.extend_from_slice(&self.z);
        out
    }

    /// FIPS 203 `dkDecode` combined with the checks of
    /// `DecapsulationKeyCheck` (§7.3): length, modulus bounds on the
    /// secret rows, and the `H(ek) == h` hash-consistency check. Any
    /// violation yields `None`.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != P::DK_BYTES {
            return None;
        }
        let mut s_hat = Vec::with_capacity(P::K);
        for i in 0..P::K {
            let row = encoding::byte_decode(&bytes[i * 384..(i + 1) * 384], 12);
            if row.iter().any(|&v| v >= Q) {
                return None;
            }
            s_hat.push(row);
        }
        let ek = EncapsulationKey::<P>::from_bytes(&bytes[384 * P::K..768 * P::K + 32])?;
        // Hash check: the stored h must equal H(ek), the ek section itself.
        if sha3_256(&[&bytes[384 * P::K..768 * P::K + 32]])
            != bytes[768 * P::K + 32..768 * P::K + 64]
        {
            return None;
        }
        let mut h = [0u8; 32];
        h.copy_from_slice(&bytes[768 * P::K + 32..768 * P::K + 64]);
        let mut z = [0u8; 32];
        z.copy_from_slice(&bytes[768 * P::K + 64..]);
        Some(Self {
            s_hat,
            ek,
            h,
            z,
            _p: PhantomData,
        })
    }

    /// The matching encapsulation key (`ek` section of the augmented key).
    pub fn encapsulation_key(&self) -> &EncapsulationKey<P> {
        &self.ek
    }
}

impl<P: MlKemParams> std::fmt::Debug for DecapsulationKey<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DecapsulationKey").finish_non_exhaustive()
    }
}

impl<P: MlKemParams> Drop for DecapsulationKey<P> {
    fn drop(&mut self) {
        use zeroize::Zeroize;
        for row in &mut self.s_hat {
            row.zeroize();
        }
        self.z.zeroize();
    }
}

/// FIPS 203 `ML-KEM.KeyGen_internal(d, z)` (Algorithm 16): the 32-byte
/// coins `d` and `z` are the entropy input (pass fresh uniform bytes).
pub fn keygen_internal<P: MlKemParams, const K: usize>(
    d: &[u8; 32],
    z: &[u8; 32],
) -> (DecapsulationKey<P>, EncapsulationKey<P>) {
    let (ek_pke, dk_pke) = kpke_keygen::<P, K>(d);
    let ek = EncapsulationKey {
        t_hat: ek_pke.t_hat,
        rho: ek_pke.rho,
        _p: PhantomData,
    };
    let h = sha3_256(&[&ek.to_bytes()]);
    let dk = DecapsulationKey {
        s_hat: dk_pke.s_hat,
        ek: ek.clone(),
        h,
        z: *z,
        _p: PhantomData,
    };
    (dk, ek)
}

/// FIPS 203 `ML-KEM.Encaps_internal(ek, m)` (Algorithm 17): `m` is the
/// 32-byte randomness input (pass fresh uniform bytes).
pub fn encapsulate_internal<P: MlKemParams, const K: usize>(
    ek: &EncapsulationKey<P>,
    m: &[u8; 32],
) -> (Vec<u8>, SharedSecret) {
    let ek_bytes = ek.to_bytes();
    let h = sha3_256(&[&ek_bytes]);
    let (k_bar, r) = hash_g(&[m, &h]);
    let c = kpke_encrypt::<P, K>(&ek_bytes, m, &r);
    (c, SharedSecret(k_bar))
}

/// FIPS 203 `ML-KEM.Decaps(dk, c)` (Algorithm 18) with implicit rejection:
/// on re-encryption mismatch (or a wrong-length ciphertext) the returned
/// key is `J(z ‖ c)` — never an error, never a validity signal.
pub fn decapsulate<P: MlKemParams, const K: usize>(
    dk: &DecapsulationKey<P>,
    c: &[u8],
) -> SharedSecret {
    let k_bar = j_hash(&[&dk.z, c]);
    let m_prime = if c.len() == P::CT_BYTES {
        decrypt_with_s_hat::<P, K>(&dk.s_hat, c)
    } else {
        [0u8; 32]
    };
    let (k_prime, r_prime) = hash_g(&[&m_prime, &dk.h]);
    let c_prime = kpke_encrypt::<P, K>(&dk.ek.to_bytes(), &m_prime, &r_prime);
    if c.len() == P::CT_BYTES && ct_eq(c, &c_prime) {
        SharedSecret(k_prime)
    } else {
        SharedSecret(k_bar)
    }
}

/// Macro: bind the const-generic core to a concrete parameter set.
macro_rules! instantiate_mlkem {
    ($mod_name:ident, $params:ident, $k:literal) => {
        #[doc = concat!("ML-KEM API bound to [`", stringify!($params), "`].")]
        pub mod $mod_name {
            pub use super::{DecapsulationKey, EncapsulationKey, SharedSecret};

            /// FIPS 203 `ML-KEM.KeyGen(d, z)`.
            pub fn keygen(
                d: &[u8; 32],
                z: &[u8; 32],
            ) -> (
                DecapsulationKey<super::params::$params>,
                EncapsulationKey<super::params::$params>,
            ) {
                super::keygen_internal::<super::params::$params, $k>(d, z)
            }

            /// FIPS 203 `ML-KEM.Encaps(ek, m)` — `m` must be fresh uniform
            /// randomness.
            pub fn encapsulate(
                ek: &EncapsulationKey<super::params::$params>,
                m: &[u8; 32],
            ) -> (Vec<u8>, SharedSecret) {
                super::encapsulate_internal::<super::params::$params, $k>(ek, m)
            }

            /// FIPS 203 `ML-KEM.Decaps(dk, c)` with implicit rejection.
            pub fn decapsulate(
                dk: &DecapsulationKey<super::params::$params>,
                c: &[u8],
            ) -> SharedSecret {
                super::decapsulate::<super::params::$params, $k>(dk, c)
            }
        }
    };
}

instantiate_mlkem!(mlkem_512, MlKem512, 2);
instantiate_mlkem!(mlkem_768, MlKem768, 3);
instantiate_mlkem!(mlkem_1024, MlKem1024, 4);

#[cfg(test)]
mod tests {
    use super::*;

    macro_rules! mlkem_roundtrip_tests {
        ($mod_name:ident, $params:ty, $k:literal, $ek_len:literal, $dk_len:literal, $ct_len:literal) => {
            mod $mod_name {
                use super::*;

                fn fresh_coins(tag: u8) -> ([u8; 32], [u8; 32]) {
                    let d = [tag; 32];
                    let mut z = [0u8; 32];
                    z[..32].copy_from_slice(&d);
                    z[0] = tag.wrapping_add(0x40);
                    (d, z)
                }

                #[test]
                fn key_sizes_and_roundtrip() {
                    let (d, z) = fresh_coins(1);
                    let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                    assert_eq!(ek.to_bytes().len(), $ek_len);
                    assert_eq!(dk.to_bytes().len(), $dk_len);
                    let m = [7u8; 32];
                    let (c, ss) = encapsulate_internal::<$params, $k>(&ek, &m);
                    assert_eq!(c.len(), $ct_len);
                    assert_eq!(
                        decapsulate::<$params, $k>(&dk, &c).as_bytes(),
                        ss.as_bytes()
                    );
                }

                #[test]
                fn encaps_is_deterministic_in_m() {
                    let (d, z) = fresh_coins(2);
                    let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                    let m = [0x42u8; 32];
                    let (c1, ss1) = encapsulate_internal::<$params, $k>(&ek, &m);
                    let (c2, ss2) = encapsulate_internal::<$params, $k>(&ek, &m);
                    assert_eq!(c1, c2);
                    assert_eq!(ss1.as_bytes(), ss2.as_bytes());
                    assert_eq!(
                        decapsulate::<$params, $k>(&dk, &c1).as_bytes(),
                        ss1.as_bytes()
                    );
                }

                #[test]
                fn implicit_rejection_on_tampered_ciphertext() {
                    let (d, z) = fresh_coins(3);
                    let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                    let m = [9u8; 32];
                    let (mut c, ss) = encapsulate_internal::<$params, $k>(&ek, &m);
                    c[0] ^= 0x01;
                    let bad = decapsulate::<$params, $k>(&dk, &c);
                    assert_ne!(bad.as_bytes(), ss.as_bytes());
                    // Implicit rejection is deterministic.
                    let again = decapsulate::<$params, $k>(&dk, &c);
                    assert_eq!(bad.as_bytes(), again.as_bytes());
                    // A different tampering point yields a different rejection key.
                    let mut c2 = c;
                    c2[$ct_len - 1] ^= 0x80;
                    let other = decapsulate::<$params, $k>(&dk, &c2);
                    assert_ne!(bad.as_bytes(), other.as_bytes());
                }

                #[test]
                fn wrong_length_ciphertext_rejects_implicitly() {
                    let (d, z) = fresh_coins(4);
                    let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                    let m = [5u8; 32];
                    let (c, _) = encapsulate_internal::<$params, $k>(&ek, &m);
                    let short = decapsulate::<$params, $k>(&dk, &c[..$ct_len - 1]);
                    let again = decapsulate::<$params, $k>(&dk, &c[..$ct_len - 1]);
                    assert_eq!(short.as_bytes(), again.as_bytes());
                    let (c2, ss2) = encapsulate_internal::<$params, $k>(&ek, &m);
                    assert_ne!(
                        short.as_bytes(),
                        decapsulate::<$params, $k>(&dk, &c2).as_bytes()
                    );
                    assert_eq!(
                        decapsulate::<$params, $k>(&dk, &c2).as_bytes(),
                        ss2.as_bytes()
                    );
                }

                #[test]
                fn key_serialization_roundtrip() {
                    let (d, z) = fresh_coins(5);
                    let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                    let ek2 = EncapsulationKey::<$params>::from_bytes(&ek.to_bytes()).unwrap();
                    assert_eq!(ek2, ek);
                    let dk2 = DecapsulationKey::<$params>::from_bytes(&dk.to_bytes()).unwrap();
                    let m = [0x11u8; 32];
                    let (c, ss) = encapsulate_internal::<$params, $k>(&ek, &m);
                    assert_eq!(
                        decapsulate::<$params, $k>(&dk2, &c).as_bytes(),
                        ss.as_bytes()
                    );
                    // Encoded keys decapsulate identically.
                    assert_eq!(dk2.to_bytes(), dk.to_bytes());
                }

                #[test]
                fn key_check_rejects_bad_encodings() {
                    let (d, z) = fresh_coins(6);
                    let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                    // Wrong lengths.
                    let ek_bytes = ek.to_bytes();
                    let dk_bytes = dk.to_bytes();
                    assert!(EncapsulationKey::<$params>::from_bytes(
                        &ek_bytes[..ek_bytes.len() - 1]
                    )
                    .is_none());
                    assert!(DecapsulationKey::<$params>::from_bytes(
                        &dk_bytes[..dk_bytes.len() - 1]
                    )
                    .is_none());
                    // Coefficient ≥ q in the first t̂ row (3329 fits in 12 bits).
                    let mut bad_ek = ek_bytes.clone();
                    bad_ek[0] = 0x01; // low byte of 3329 = 0x0D01 little-endian
                    bad_ek[1] = 0x0D;
                    assert!(EncapsulationKey::<$params>::from_bytes(&bad_ek).is_none());
                    // Coefficient ≥ q in the first ŝ row of the decapsulation key.
                    let mut bad_dk = dk_bytes.clone();
                    bad_dk[0] = 0x01;
                    bad_dk[1] = 0x0D;
                    assert!(DecapsulationKey::<$params>::from_bytes(&bad_dk).is_none());
                }

                #[test]
                fn cbd_matches_spec_bit_pattern() {
                    // η = 2, coefficient 0 uses bits (b0,b1,b2,b3) as
                    // (b0+b1) − (b2+b3): 0b0000_0100 has b2 = 1 → 0 − 1 = −1;
                    // all-ones bytes give 2 − 2 = 0.
                    let bytes = [0b0000_0100u8; 128];
                    let f = sample_cbd(&bytes, 2);
                    assert_eq!(f[0], -1);
                    assert_eq!(f[1], 0);
                    let ones = [0xFFu8; 128];
                    assert!(sample_cbd(&ones, 2).iter().all(|&v| v == 0));
                    let zeros = [0x00u8; 192];
                    assert!(sample_cbd(&zeros, 3).iter().all(|&v| v == 0));
                }
            }
        };
    }

    mlkem_roundtrip_tests!(ml_kem_512, MlKem512, 2, 800, 1632, 768);
    mlkem_roundtrip_tests!(ml_kem_768, MlKem768, 3, 1184, 2400, 1088);
    mlkem_roundtrip_tests!(ml_kem_1024, MlKem1024, 4, 1568, 3168, 1568);
}
