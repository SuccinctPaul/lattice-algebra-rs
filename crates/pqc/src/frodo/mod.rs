//! FrodoKEM — the round-3 LWE-based key-encapsulation mechanism
//! (specification of 2020-09-30), a direct port of the submission's
//! reference implementation.
//!
//! Unlike the module-lattice schemes in this crate, FrodoKEM needs no NTT:
//! all arithmetic is `u16` modular (q = 2¹⁵ or 2¹⁶) and the public matrix
//! `A` is generated on the fly as AES128(seed_A, i ‖ j) — or SHAKE128 in
//! the submission's alternative variant. The two variants of each
//! parameter set are exposed separately (`frodo640` uses AES, the
//! submitted default; `frodo640_shake` uses SHAKE128).
//!
//! Layout note: the secret/noise matrices `S`, `E` are sampled into flat
//! buffers that the reference *interprets transposed* when multiplying
//! (`S` is read as an `n̄ × n` matrix) — this port keeps the same flat
//! layout so the coefficient ordering (and hence the KAT outputs) matches
//! byte-for-byte.
//!
//! Randomness is passed explicitly (as the KAT harness's DRBG outputs):
//! [`keygen`] takes the 48 keygen bytes `(s ‖ seedSE ‖ z)` split into
//! three parts, [`encapsulate`] takes the fresh `μ` — the same values the
//! reference draws from one `randombytes` call.

pub mod aes;
pub mod encoding;
pub mod params;

pub use params::{
    Frodo1344, Frodo1344Shake, Frodo640, Frodo640Shake, Frodo976, Frodo976Shake, FrodoParams,
};

use sha3::digest::{ExtendableOutput, Update, XofReader};
use sha3::{Shake128, Shake256};
use std::marker::PhantomData;

// ===========================================================================
// Hash/XOF wrappers (the reference's `shake128` over FIPS-202)
// ===========================================================================

/// The submission's per-set `shake` (SHAKE128 for 640, SHAKE256 for
/// 976/1344) over concatenated parts.
fn shake_xof<P: FrodoParams>(input: &[&[u8]], out: &mut [u8]) {
    if P::SHAKE256 {
        let mut hasher = Shake256::default();
        for part in input {
            hasher.update(part);
        }
        hasher.finalize_xof().read(out);
    } else {
        let mut hasher = Shake128::default();
        for part in input {
            hasher.update(part);
        }
        hasher.finalize_xof().read(out);
    }
}

// ===========================================================================
// Samplers and matrix arithmetic (u16 wrapping, as the C reference)
// ===========================================================================

/// `frodo_sample_n`: fill `s` with samples from the noise distribution
/// described by `cdf`, consuming the raw 16-bit input in place. Each
/// sample is the count of CDF entries strictly below the upper 15 bits,
/// sign-flipped by the least-significant bit.
fn sample_n(s: &mut [u16], cdf: &[u16]) {
    for slot in s.iter_mut() {
        let raw = *slot;
        let prnd = raw >> 1; // drop the least significant bit
        let sign = raw & 1;
        let mut sample = 0u16;
        // No need to compare against the last entry (spec: CDF ends at 2^15−1).
        for &t in &cdf[..cdf.len() - 1] {
            sample = sample.wrapping_add(t.wrapping_sub(prnd) >> 15);
        }
        // Flip the sample iff sign = 1: ((-sign) ^ sample) + sign.
        *slot = sign.wrapping_neg() ^ sample;
        *slot = slot.wrapping_add(sign);
    }
}

/// Expand the public matrix `A` (`n × n`, full 16-bit entries):
/// AES mode packs the index pairs into a buffer and encrypts it with
/// AES128-ECB; SHAKE mode derives each row from `SHAKE128(i ‖ seed_A)`.
fn expand_a<P: FrodoParams>(seed_a: &[u8; 16]) -> Vec<u16> {
    let n = P::N;
    if P::SHAKE_A {
        let mut out = vec![0u16; n * n];
        let mut row_bytes = vec![0u8; 2 * n];
        let mut input = [0u8; 2 + 16];
        input[2..].copy_from_slice(seed_a);
        for (i, row) in out.chunks_mut(n).enumerate() {
            input[0] = i as u8;
            input[1] = (i >> 8) as u8;
            // The SHAKE-A variant generates rows with fips202 SHAKE128
            // directly (independent of the per-set KEM XOF).
            let mut hasher = Shake128::default();
            hasher.update(&input);
            hasher.finalize_xof().read(&mut row_bytes);
            for (dst, chunk) in row.iter_mut().zip(row_bytes.chunks_exact(2)) {
                *dst = u16::from_le_bytes([chunk[0], chunk[1]]);
            }
        }
        out
    } else {
        // Index buffer: every PARAMS_STRIPE_STEP-th pair holds (i, j),
        // little-endian, everything else zero — then ECB-encrypt in place.
        let mut buf = vec![0u8; 2 * n * n];
        for i in 0..n {
            for j in (0..n).step_by(8) {
                buf[2 * (i * n + j)] = i as u8;
                buf[2 * (i * n + j) + 1] = (i >> 8) as u8;
                buf[2 * (i * n + j + 1)] = j as u8;
                buf[2 * (i * n + j + 1) + 1] = (j >> 8) as u8;
            }
        }
        for block in buf.chunks_exact_mut(16) {
            let pt: [u8; 16] = block.try_into().expect("16-byte block");
            block.copy_from_slice(&aes::encrypt_block(seed_a, &pt));
        }
        buf.chunks_exact(2)
            .map(|c| u16::from_le_bytes([c[0], c[1]]))
            .collect()
    }
}

/// `frodo_mul_add_as_plus_e`: `B = A·s + e` where `A` is row-indexed
/// `A[i·n + j]`, `s` is read transposed as `s[k·n + j]` (`n̄ × n`), and
/// `e`/`B` are `n × n̄` row-major. All sums wrap mod 2¹⁶.
fn mul_add_as_plus_e(b: &mut [u16], a: &[u16], s: &[u16], e: &[u16], nbar: usize, n: usize) {
    b.copy_from_slice(e);
    for i in 0..n {
        for k in 0..nbar {
            let mut sum = 0u16;
            for j in 0..n {
                sum = sum.wrapping_add(a[i * n + j].wrapping_mul(s[k * n + j]));
            }
            b[i * nbar + k] = b[i * nbar + k].wrapping_add(sum);
        }
    }
}

/// `frodo_mul_add_sa_plus_e`: `B' = s'·A + e'` with `s'`/`e'`/`B'` as
/// `n̄ × n` row-major and `A` indexed column-wise (`A[j·n + i]`).
fn mul_add_sa_plus_e(out: &mut [u16], a: &[u16], s: &[u16], e: &[u16], nbar: usize, n: usize) {
    out.copy_from_slice(e);
    for i in 0..n {
        for k in 0..nbar {
            let mut sum = 0u16;
            for j in 0..n {
                sum = sum.wrapping_add(a[j * n + i].wrapping_mul(s[k * n + j]));
            }
            out[k * n + i] = out[k * n + i].wrapping_add(sum);
        }
    }
}

/// `frodo_mul_bs`: `W = b·s` with `b` as `n̄ × n` and `s` transposed
/// (`s[j·n + k]`), result `n̄ × n̄` reduced mod q.
fn mul_bs(out: &mut [u16], b: &[u16], s: &[u16], nbar: usize, n: usize, logq: u32) {
    let mask = ((1u32 << logq) - 1) as u16;
    for i in 0..nbar {
        for j in 0..nbar {
            let mut sum = 0u16;
            for k in 0..n {
                sum = sum.wrapping_add(b[i * n + k].wrapping_mul(s[j * n + k]));
            }
            out[i * nbar + j] = sum & mask;
        }
    }
}

/// `frodo_mul_add_sb_plus_e`: `V = s·b + e` with `s` transposed
/// (`s[k·n + j]`), `b` as `n × n̄`, result mod q.
fn mul_add_sb_plus_e(
    out: &mut [u16],
    b: &[u16],
    s: &[u16],
    e: &[u16],
    nbar: usize,
    n: usize,
    logq: u32,
) {
    let mask = ((1u32 << logq) - 1) as u16;
    for k in 0..nbar {
        for i in 0..nbar {
            let mut sum = 0u16;
            for j in 0..n {
                sum = sum.wrapping_add(s[k * n + j].wrapping_mul(b[j * nbar + i]));
            }
            out[k * nbar + i] = e[k * nbar + i].wrapping_add(sum) & mask;
        }
    }
}

/// Generate the `(S ‖ E)`-style randomness block: the per-set `shake`
/// XOF over `prefix ‖ seed`, interpreted as little-endian 16-bit values.
fn shake_sample_block<P: FrodoParams>(prefix: u8, seed: &[u8], words: usize) -> Vec<u16> {
    let mut bytes = vec![0u8; 2 * words];
    shake_xof::<P>(&[&[prefix], seed], &mut bytes);
    bytes
        .chunks_exact(2)
        .map(|c| u16::from_le_bytes([c[0], c[1]]))
        .collect()
}

/// Sample `S`, `E` from the seeded block: `(S ‖ E) =
/// sample(SHAKE128(0x5F ‖ seedSE))` (keygen) — the reference samples the
/// first `n·n̄` raw words, then the following `n·n̄`.
fn split_and_sample_se<P: FrodoParams>(raw: &mut [u16], se_len: usize) -> (Vec<u16>, Vec<u16>) {
    let mut s = raw[..se_len].to_vec();
    let mut e = raw[se_len..].to_vec();
    let cdf = P::CDF;
    sample_n(&mut s, cdf);
    sample_n(&mut e, cdf);
    (s, e)
}

// ===========================================================================
// Keys and ciphertext
// ===========================================================================

/// FrodoKEM public key: the 16-byte `seed_A` plus the `n × n̄` matrix `B`
/// (values in `[0, q)`).
pub struct PublicKey<P: FrodoParams> {
    seed_a: [u8; 16],
    b: Vec<u16>,
    _p: PhantomData<P>,
}

impl<P: FrodoParams> Clone for PublicKey<P> {
    fn clone(&self) -> Self {
        Self {
            seed_a: self.seed_a,
            b: self.b.clone(),
            _p: PhantomData,
        }
    }
}

impl<P: FrodoParams> PartialEq for PublicKey<P> {
    fn eq(&self, other: &Self) -> bool {
        self.seed_a == other.seed_a && self.b == other.b
    }
}

impl<P: FrodoParams> std::fmt::Debug for PublicKey<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("PublicKey").finish_non_exhaustive()
    }
}

impl<P: FrodoParams> PublicKey<P> {
    /// The submission's public-key encoding: `seed_A ‖ pack(B)`.
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(P::EK_BYTES);
        out.extend_from_slice(&self.seed_a);
        let mut packed = vec![0u8; P::EK_BYTES - 16];
        encoding::pack(&mut packed, &self.b, P::LOGQ);
        out.extend_from_slice(&packed);
        out
    }

    /// Parse `seed_A ‖ pack(B)` (unpacked values are `< q` by
    /// construction); wrong length yields `None`.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != P::EK_BYTES {
            return None;
        }
        let mut seed_a = [0u8; 16];
        seed_a.copy_from_slice(&bytes[..16]);
        let mut b = vec![0u16; P::N * P::NBAR];
        encoding::unpack(&mut b, &bytes[16..], P::LOGQ);
        Some(Self {
            seed_a,
            b,
            _p: PhantomData,
        })
    }
}

/// FrodoKEM secret key: `s ‖ pk ‖ S ‖ pkh` — the 16-byte recovery secret,
/// the encoded public key, the raw `n·n̄`-entry `S` matrix (two's
/// complement `u16`, exactly as the reference serializes it) and the
/// `pkh = SHAKE128(pk)` hash of `SS_BYTES` bytes.
pub struct SecretKey<P: FrodoParams> {
    s: Vec<u8>,
    pk: PublicKey<P>,
    s_mat: Vec<u16>,
    pkh: Vec<u8>,
}

impl<P: FrodoParams> std::fmt::Debug for SecretKey<P> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SecretKey").finish_non_exhaustive()
    }
}

impl<P: FrodoParams> Drop for SecretKey<P> {
    fn drop(&mut self) {
        use zeroize::Zeroize;
        self.s.zeroize();
        self.s_mat.zeroize();
    }
}

impl<P: FrodoParams> SecretKey<P> {
    /// The submission's secret-key encoding (raw little-endian `S`).
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(P::DK_BYTES);
        out.extend_from_slice(&self.s);
        out.extend_from_slice(&self.pk.to_bytes());
        for &v in &self.s_mat {
            out.extend_from_slice(&v.to_le_bytes());
        }
        out.extend_from_slice(&self.pkh);
        out
    }

    /// Parse the `s ‖ pk ‖ S ‖ pkh` encoding; wrong length yields `None`.
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        if bytes.len() != P::DK_BYTES {
            return None;
        }
        let s = bytes[..P::SS_BYTES].to_vec();
        let pk = PublicKey::<P>::from_bytes(&bytes[P::SS_BYTES..P::SS_BYTES + P::EK_BYTES])?;
        let off = P::SS_BYTES + P::EK_BYTES;
        let s_mat: Vec<u16> = bytes[off..off + 2 * P::N * P::NBAR]
            .chunks_exact(2)
            .map(|c| u16::from_le_bytes([c[0], c[1]]))
            .collect();
        let pkh = bytes[off + 2 * P::N * P::NBAR..].to_vec();
        Some(Self { s, pk, s_mat, pkh })
    }

    /// The matching public key.
    pub fn public_key(&self) -> &PublicKey<P> {
        &self.pk
    }
}

/// FrodoKEM ciphertext: the packed `B'` block followed by the packed
/// `C` block.
#[derive(Clone, PartialEq, Eq)]
pub struct Ciphertext(Vec<u8>);

impl Ciphertext {
    /// The raw ciphertext bytes (`c1 ‖ c2`).
    pub fn as_bytes(&self) -> &[u8] {
        &self.0
    }

    /// Wrap raw bytes without validation (decapsulation treats any
    /// content as valid input; a wrong length fails the re-encryption
    /// check implicitly).
    pub fn from_bytes(bytes: Vec<u8>) -> Self {
        Ciphertext(bytes)
    }
}

impl std::fmt::Debug for Ciphertext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Ciphertext").finish_non_exhaustive()
    }
}

/// A shared secret; redacted `Debug` and zeroized on drop.
pub struct SharedSecret(Vec<u8>);

impl SharedSecret {
    /// The secret bytes (16 / 24 / 32 depending on the parameter set).
    pub fn as_bytes(&self) -> &[u8] {
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

// ===========================================================================
// The KEM
// ===========================================================================

/// FrodoKEM key generation. The inputs are the reference's single
/// `randombytes(2·SS + 16)` draw split as `(s ‖ seedSE ‖ z)` — `s` is the
/// SS-byte recovery secret, `seedSE`/`z` are 16 bytes each.
pub fn keygen<P: FrodoParams>(
    s: &[u8],
    seed_se: &[u8],
    z: &[u8; 16],
) -> (SecretKey<P>, PublicKey<P>) {
    // All three sections follow the reference's CRYPTO_BYTES sizing: `s`
    // and `seedSE` are SS bytes each, `z` is the 16-byte seed_A entropy.
    assert_eq!(s.len(), P::SS_BYTES, "recovery-secret length");
    assert_eq!(seed_se.len(), P::SS_BYTES, "seedSE length");
    // seed_A = SHAKE128(z).
    let mut seed_a = [0u8; 16];
    shake_xof::<P>(&[z], &mut seed_a);

    // (S ‖ E) ← sample(SHAKE128(0x5F ‖ seedSE)), raw 16-bit draws first.
    let nbar = P::NBAR;
    let se_len = P::N * nbar;
    let mut raw = shake_sample_block::<P>(0x5F, seed_se, 2 * se_len);
    let (s_mat, e) = split_and_sample_se::<P>(&mut raw, se_len);

    // B = A·s + e (S read transposed), reduced to the low LOGQ bits —
    // the encoded public key keeps only those bits, and encapsulation
    // consumes exactly the reduced values.
    let a = expand_a::<P>(&seed_a);
    let mut b = vec![0u16; se_len];
    mul_add_as_plus_e(&mut b, &a, &s_mat, &e, nbar, P::N);
    let q_mask = ((1u32 << P::LOGQ) - 1) as u16;
    for v in b.iter_mut() {
        *v &= q_mask;
    }

    let pk = PublicKey {
        seed_a,
        b,
        _p: PhantomData,
    };

    // pkh = SHAKE128(pk); sk = s ‖ pk ‖ S ‖ pkh.
    let mut pkh = vec![0u8; P::SS_BYTES];
    shake_xof::<P>(&[&pk.to_bytes()], &mut pkh);
    let sk = SecretKey {
        s: s.to_vec(),
        pk: pk.clone(),
        s_mat,
        pkh,
    };
    (sk, pk)
}

/// FrodoKEM encapsulation with fresh encapsulation randomness `mu`
/// (`EXTRACTED_BITS·n̄²/8` bytes — the reference's `randombytes(mu)`).
pub fn encapsulate<P: FrodoParams>(ek: &PublicKey<P>, mu: &[u8]) -> (Ciphertext, SharedSecret) {
    assert_eq!(mu.len(), P::MU_BYTES, "mu length");
    let nbar = P::NBAR;
    let pk_bytes = ek.to_bytes();

    // pkh ← SHAKE128(pk); (seedSE ‖ k) ← SHAKE128(pkh ‖ mu).
    let mut pkh = vec![0u8; P::SS_BYTES];
    shake_xof::<P>(&[&pk_bytes], &mut pkh);
    let mut g2 = vec![0u8; 2 * P::SS_BYTES];
    shake_xof::<P>(&[&pkh, mu], &mut g2);
    let seed_se = g2[..P::SS_BYTES].to_vec();
    let k = g2[P::SS_BYTES..].to_vec();

    // (Sp ‖ Ep ‖ Epp) ← sample(SHAKE128(0x96 ‖ seedSE)).
    let se_len = P::N * nbar;
    let raw = shake_sample_block::<P>(0x96, &seed_se, 2 * se_len + nbar * nbar);
    let cdf = P::CDF;
    let mut sp = raw[..se_len].to_vec();
    let mut ep = raw[se_len..2 * se_len].to_vec();
    let mut epp = raw[2 * se_len..].to_vec();
    sample_n(&mut sp, cdf);
    sample_n(&mut ep, cdf);
    sample_n(&mut epp, cdf);

    // B' = Sp·A + Ep (n̄ × n), packed as c1.
    let a = expand_a::<P>(&ek.seed_a);
    let mut bp = vec![0u16; se_len];
    mul_add_sa_plus_e(&mut bp, &a, &sp, &ep, nbar, P::N);
    let mut c1 = vec![0u8; P::LOGQ as usize * se_len / 8];
    encoding::pack(&mut c1, &bp, P::LOGQ);

    // V = Sp·B + Epp; C = (key_encode(mu) + V) mod q, packed as c2.
    let mut v = vec![0u16; nbar * nbar];
    mul_add_sb_plus_e(&mut v, &ek.b, &sp, &epp, nbar, P::N, P::LOGQ);
    let encoded = encoding::key_encode::<P>(mu);
    let mask = ((1u32 << P::LOGQ) - 1) as u16;
    for (cv, &ev) in v.iter_mut().zip(encoded.iter()) {
        *cv = cv.wrapping_add(ev) & mask;
    }
    let mut c2 = vec![0u8; P::LOGQ as usize * nbar * nbar / 8];
    encoding::pack(&mut c2, &v, P::LOGQ);

    // ss = SHAKE128(ct ‖ k).
    let mut ct = c1;
    ct.extend_from_slice(&c2);
    let mut ss = vec![0u8; P::SS_BYTES];
    shake_xof::<P>(&[&ct, &k], &mut ss);
    (Ciphertext(ct), SharedSecret(ss))
}

/// FrodoKEM decapsulation. A ciphertext that fails the re-encryption
/// check (including any wrong-length input) yields
/// `SHAKE128(ct ‖ s)` instead of `SHAKE128(ct ‖ k')` — implicit
/// rejection, selected without branching on the secret comparison.
pub fn decapsulate<P: FrodoParams>(dk: &SecretKey<P>, ct: &Ciphertext) -> SharedSecret {
    let nbar = P::NBAR;
    let se_len = P::N * nbar;
    let mask = ((1u32 << P::LOGQ) - 1) as u16;

    // Reject wrong-length ciphertexts up front; the reference compares
    // the unpacked blocks, so only a full-length input can match.
    if ct.0.len() != P::CT_BYTES {
        let mut ss = vec![0u8; P::SS_BYTES];
        shake_xof::<P>(&[&ct.0, &dk.s], &mut ss);
        return SharedSecret(ss);
    }
    let c1_len = P::LOGQ as usize * se_len / 8;
    let mut bp = vec![0u16; se_len];
    encoding::unpack(&mut bp, &ct.0[..c1_len], P::LOGQ);
    let mut c = vec![0u16; nbar * nbar];
    encoding::unpack(&mut c, &ct.0[c1_len..], P::LOGQ);

    // W = C − Bp·S (mod q); mu' ← key_decode(W).
    let mut w = vec![0u16; nbar * nbar];
    mul_bs(&mut w, &bp, &dk.s_mat, nbar, P::N, P::LOGQ);
    for (wv, &cv) in w.iter_mut().zip(c.iter()) {
        // frodo_sub(W, C, W): out = C − W.
        *wv = cv.wrapping_sub(*wv) & mask;
    }
    let mu_prime = encoding::key_decode::<P>(&w);

    // (seedSE' ‖ k') ← SHAKE128(pkh ‖ mu').
    let mut g2 = vec![0u8; 2 * P::SS_BYTES];
    shake_xof::<P>(&[&dk.pkh, &mu_prime], &mut g2);
    let seed_se = g2[..P::SS_BYTES].to_vec();
    let k_prime = g2[P::SS_BYTES..].to_vec();

    // Recompute B' and C from (Sp', Ep', Epp').
    let cdf = P::CDF;
    let raw = shake_sample_block::<P>(0x96, &seed_se, 2 * se_len + nbar * nbar);
    let mut sp = raw[..se_len].to_vec();
    let mut ep = raw[se_len..2 * se_len].to_vec();
    let mut epp = raw[2 * se_len..].to_vec();
    sample_n(&mut sp, cdf);
    sample_n(&mut ep, cdf);
    sample_n(&mut epp, cdf);

    let a = expand_a::<P>(&dk.pk.seed_a);
    let mut bbp = vec![0u16; se_len];
    mul_add_sa_plus_e(&mut bbp, &a, &sp, &ep, nbar, P::N);
    for v in bbp.iter_mut() {
        *v &= mask;
    }

    let mut w2 = vec![0u16; nbar * nbar];
    mul_add_sb_plus_e(&mut w2, &dk.pk.b, &sp, &epp, nbar, P::N, P::LOGQ);
    let encoded = encoding::key_encode::<P>(&mu_prime);
    let mut cc = vec![0u16; nbar * nbar];
    for ((out, &wv), &ev) in cc.iter_mut().zip(w2.iter()).zip(encoded.iter()) {
        *out = wv.wrapping_add(ev) & mask;
    }

    // If (B' == B'') and (C == C''): ss = SHAKE128(ct ‖ k'), else
    // ss = SHAKE128(ct ‖ s) — constant-time selection (`ct_select` with
    // the reference's 0 / −1 comparison normalized to a 0 / 1 mask).
    let ok = (ct_verify(&bp, &bbp) | ct_verify(&c, &cc)) == 0;
    let fin_k: Vec<u8> = k_prime
        .iter()
        .zip(dk.s.iter())
        .map(|(&k, &s)| if ok { k } else { s })
        .collect();
    let mut ss = vec![0u8; P::SS_BYTES];
    shake_xof::<P>(&[&ct.0, &fin_k], &mut ss);
    SharedSecret(ss)
}

/// `ct_verify`: 0 if the arrays are equal, 1 otherwise (the reference's
/// constant-time 0 / −1 comparison, normalized to a mask).
fn ct_verify(a: &[u16], b: &[u16]) -> u8 {
    let mut acc = 0u16;
    for (x, &y) in a.iter().zip(b.iter()) {
        acc |= x ^ y;
    }
    if acc == 0 {
        0
    } else {
        1
    }
}

/// Macro: bind the const-generic core to a concrete parameter set.
macro_rules! instantiate_frodo {
    ($mod_name:ident, $params:ident, $doc:expr) => {
        #[doc = $doc]
        pub mod $mod_name {
            pub use super::{Ciphertext, PublicKey, SecretKey, SharedSecret};

            /// FrodoKEM key generation from the reference's keygen
            /// randomness split as `(s ‖ seedSE ‖ z)` — `s`/`seedSE` are
            /// SS bytes each (the reference's `CRYPTO_BYTES`), `z` is 16
            /// bytes.
            pub fn keygen(
                s: &[u8],
                seed_se: &[u8],
                z: &[u8; 16],
            ) -> (
                SecretKey<super::params::$params>,
                PublicKey<super::params::$params>,
            ) {
                super::keygen::<super::params::$params>(s, seed_se, z)
            }

            /// FrodoKEM encapsulation with fresh randomness `mu`.
            pub fn encapsulate(
                ek: &PublicKey<super::params::$params>,
                mu: &[u8],
            ) -> (Ciphertext, SharedSecret) {
                super::encapsulate::<super::params::$params>(ek, mu)
            }

            /// FrodoKEM decapsulation with implicit rejection.
            pub fn decapsulate(
                dk: &SecretKey<super::params::$params>,
                ct: &Ciphertext,
            ) -> SharedSecret {
                super::decapsulate::<super::params::$params>(dk, ct)
            }
        }
    };
}

instantiate_frodo!(frodo640, Frodo640, "FrodoKEM-640 (matrix `A` via AES128).");
instantiate_frodo!(frodo976, Frodo976, "FrodoKEM-976 (matrix `A` via AES128).");
instantiate_frodo!(
    frodo1344,
    Frodo1344,
    "FrodoKEM-1344 (matrix `A` via AES128)."
);
instantiate_frodo!(
    frodo640_shake,
    Frodo640Shake,
    "FrodoKEM-640 with SHAKE128-generated matrix `A`."
);
instantiate_frodo!(
    frodo976_shake,
    Frodo976Shake,
    "FrodoKEM-976 with SHAKE128-generated matrix `A`."
);
instantiate_frodo!(
    frodo1344_shake,
    Frodo1344Shake,
    "FrodoKEM-1344 with SHAKE128-generated matrix `A`."
);

#[cfg(test)]
mod tests;
