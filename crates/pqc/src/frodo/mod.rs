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

mod simd;

pub use params::{
    Frodo1344, Frodo1344Shake, Frodo640, Frodo640Shake, Frodo976, Frodo976Shake, FrodoParams,
    KemXof, MatrixAExpansion, SEEDSE_ENCAPS_PREFIX, SEEDSE_KEYGEN_PREFIX, SEED_A_BYTES,
    STRIPE_STEP,
};

use crate::error::{InvalidInput, SchemeResult};
use algebra::crypto::xof::shortcuts::{shake128_parts, shake256_parts};
use std::marker::PhantomData;

use self::simd::{axpy16, dot16};

// ===========================================================================
// Hash/XOF wrappers (the reference's `shake128` over FIPS-202)
// ===========================================================================

/// The submission's per-set `shake` (SHAKE128 for 640, SHAKE256 for
/// 976/1344) over concatenated parts.
fn shake_xof<P: FrodoParams>(input: &[&[u8]], out: &mut [u8]) {
    match P::XOF {
        KemXof::Shake128 => shake128_parts(input, out),
        KemXof::Shake256 => shake256_parts(input, out),
    }
}

// ===========================================================================
// Samplers and matrix arithmetic (u16 wrapping, as the C reference)
// ===========================================================================

/// Output dimension above which independent matrix-product rows are handed
/// to the rayon pool (`parallel` feature); every real FrodoKEM parameter set
/// clears this by a wide margin.
#[cfg(feature = "parallel")]
const PAR_MIN_DIM: usize = 256;

/// Runs `f(row_index, row)` over the `len / row_len` disjoint output rows of
/// `target`, across the rayon pool when the multiplying dimension is large
/// enough to amortize task hand-off (`parallel` feature).
#[cfg(feature = "parallel")]
fn row_parallel(
    target: &mut [u16],
    row_len: usize,
    work_hint: usize,
    f: impl Fn(usize, &mut [u16]) + Sync,
) {
    if work_hint >= PAR_MIN_DIM {
        use rayon::prelude::*;

        target
            .par_chunks_exact_mut(row_len)
            .enumerate()
            .for_each(|(i, row)| f(i, row));
    } else {
        for (i, row) in target.chunks_exact_mut(row_len).enumerate() {
            f(i, row);
        }
    }
}

/// Sequential variant of [`row_parallel`] for builds without the
/// `parallel` feature.
#[cfg(not(feature = "parallel"))]
fn row_parallel(
    target: &mut [u16],
    row_len: usize,
    _work_hint: usize,
    mut f: impl FnMut(usize, &mut [u16]),
) {
    for (i, row) in target.chunks_exact_mut(row_len).enumerate() {
        f(i, row);
    }
}

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
/// AES128-ECB (blocks — and SHAKE-mode rows — are independent, so the
/// `parallel` feature distributes them across threads); SHAKE mode derives
/// each row from `SHAKE128(i ‖ seed_A)`.
fn expand_a<P: FrodoParams>(seed_a: &[u8; SEED_A_BYTES]) -> Vec<u16> {
    let n = P::N;
    match P::A_MODE {
        MatrixAExpansion::Shake128 => {
            let mut out = vec![0u16; n * n];
            let mut input = [0u8; 2 + SEED_A_BYTES];
            input[2..].copy_from_slice(seed_a);
            #[cfg(feature = "parallel")]
            {
                use rayon::prelude::*;

                if n >= PAR_MIN_DIM {
                    let row_bytes: Vec<u8> = (0..n)
                        .into_par_iter()
                        .flat_map_iter(|i| {
                            let mut row_input = input;
                            row_input[0] = i as u8;
                            row_input[1] = (i >> 8) as u8;
                            let mut row_bytes = vec![0u8; 2 * n];
                            // The SHAKE-A variant generates rows with fips202
                            // SHAKE128 directly (independent of the per-set
                            // KEM XOF).
                            shake128_parts(&[&row_input], &mut row_bytes);
                            row_bytes
                        })
                        .collect();
                    return row_bytes
                        .chunks_exact(2)
                        .map(|c| u16::from_le_bytes([c[0], c[1]]))
                        .collect();
                }
            }
            let mut row_bytes = vec![0u8; 2 * n];
            for (i, row) in out.chunks_mut(n).enumerate() {
                input[0] = i as u8;
                input[1] = (i >> 8) as u8;
                // The SHAKE-A variant generates rows with fips202 SHAKE128
                // directly (independent of the per-set KEM XOF).
                shake128_parts(&[&input], &mut row_bytes);
                for (dst, chunk) in row.iter_mut().zip(row_bytes.chunks_exact(2)) {
                    *dst = u16::from_le_bytes([chunk[0], chunk[1]]);
                }
            }
            out
        }
        MatrixAExpansion::Aes128 => {
            // Index buffer: every STRIPE_STEP-th pair holds (i, j),
            // little-endian, everything else zero — then ECB-encrypt in place.
            let mut buf = vec![0u8; 2 * n * n];
            for i in 0..n {
                for j in (0..n).step_by(STRIPE_STEP) {
                    buf[2 * (i * n + j)] = i as u8;
                    buf[2 * (i * n + j) + 1] = (i >> 8) as u8;
                    buf[2 * (i * n + j + 1)] = j as u8;
                    buf[2 * (i * n + j + 1) + 1] = (j >> 8) as u8;
                }
            }
            {
                #[cfg(feature = "parallel")]
                {
                    use rayon::prelude::*;

                    if n >= PAR_MIN_DIM {
                        buf.par_chunks_exact_mut(16).for_each(|block| {
                            let pt: [u8; 16] = block.try_into().expect("16-byte block");
                            block.copy_from_slice(&aes::encrypt_block(seed_a, &pt));
                        });
                        return buf
                            .chunks_exact(2)
                            .map(|c| u16::from_le_bytes([c[0], c[1]]))
                            .collect();
                    }
                }
                for block in buf.chunks_exact_mut(16) {
                    let pt: [u8; 16] = block.try_into().expect("16-byte block");
                    block.copy_from_slice(&aes::encrypt_block(seed_a, &pt));
                }
            }
            buf.chunks_exact(2)
                .map(|c| u16::from_le_bytes([c[0], c[1]]))
                .collect()
        }
    }
}

/// `frodo_mul_add_as_plus_e`: `B = A·s + e` where `A` is row-indexed
/// `A[i·n + j]`, `s` is read transposed as `s[k·n + j]` (`n̄ × n`), and
/// `e`/`B` are `n × n̄` row-major. All sums wrap mod 2¹⁶.
///
/// Output rows are independent (`parallel`) and each is `n̄` dot products
/// with 16-lane accumulation (`simd`).
fn mul_add_as_plus_e(b: &mut [u16], a: &[u16], s: &[u16], e: &[u16], nbar: usize, n: usize) {
    b.copy_from_slice(e);
    row_parallel(b, nbar, n, |i, row| {
        let a_row = &a[i * n..(i + 1) * n];
        for (k, slot) in row.iter_mut().enumerate() {
            *slot = slot.wrapping_add(dot16(a_row, &s[k * n..(k + 1) * n]));
        }
    });
}

/// `frodo_mul_add_sa_plus_e`: `B' = s'·A + e'` with `s'`/`e'`/`B'` as
/// `n̄ × n` row-major and `A` indexed column-wise (`A[j·n + i]`).
///
/// Reformulated as `n̄` independent row updates: row `k` accumulates
/// `s'[k, j]·A[j, ·]` over ascending `j` (an axpy chain) — the same
/// addition order as the reference triple loop, so the wrapped low bits
/// match byte-for-byte.
fn mul_add_sa_plus_e(out: &mut [u16], a: &[u16], s: &[u16], e: &[u16], nbar: usize, n: usize) {
    debug_assert_eq!(out.len(), nbar * n);
    out.copy_from_slice(e);
    row_parallel(out, n, n, |k, row| {
        for j in 0..n {
            axpy16(row, &a[j * n..(j + 1) * n], s[k * n + j]);
        }
    });
}

/// `frodo_mul_bs`: `W = b·s` with `b` as `n̄ × n` and `s` transposed
/// (`s[j·n + k]`), result `n̄ × n̄` reduced mod q.
fn mul_bs(out: &mut [u16], b: &[u16], s: &[u16], nbar: usize, n: usize, logq: u32) {
    let mask = ((1u32 << logq) - 1) as u16;
    row_parallel(out, nbar, n, |i, row| {
        let b_row = &b[i * n..(i + 1) * n];
        for (j, slot) in row.iter_mut().enumerate() {
            *slot = dot16(b_row, &s[j * n..(j + 1) * n]) & mask;
        }
    });
}

/// `frodo_mul_add_sb_plus_e`: `V = s·b + e` with `s` transposed
/// (`s[k·n + j]`), `b` as `n × n̄`, result mod q.
///
/// Row `k` accumulates `s[k, j]·b[j, ·]` over ascending `j` (axpy chain,
/// exact as [`mul_add_sa_plus_e`]) and is masked at the end.
fn mul_add_sb_plus_e(
    out: &mut [u16],
    b: &[u16],
    s: &[u16],
    e: &[u16],
    nbar: usize,
    n: usize,
    logq: u32,
) {
    out.copy_from_slice(e);
    let mask = ((1u32 << logq) - 1) as u16;
    row_parallel(out, nbar, n, |k, row| {
        for j in 0..n {
            axpy16(row, &b[j * nbar..(j + 1) * nbar], s[k * n + j]);
        }
        for v in row.iter_mut() {
            *v &= mask;
        }
    });
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
/// sample(shake(SEEDSE_KEYGEN_PREFIX ‖ seedSE))` (keygen) — the reference samples the
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
    seed_a: [u8; SEED_A_BYTES],
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
        let mut packed = vec![0u8; P::EK_BYTES - SEED_A_BYTES];
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
        let mut seed_a = [0u8; SEED_A_BYTES];
        seed_a.copy_from_slice(&bytes[..SEED_A_BYTES]);
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
/// `C` block. A constructed ciphertext is always well-formed (length
/// checked in [`Ciphertext::from_bytes`]).
#[derive(Clone, PartialEq, Eq)]
pub struct Ciphertext<P: FrodoParams> {
    bytes: Vec<u8>,
    _p: PhantomData<P>,
}

impl<P: FrodoParams> Ciphertext<P> {
    /// The raw ciphertext bytes (`c1 ‖ c2`).
    pub fn as_bytes(&self) -> &[u8] {
        &self.bytes
    }

    /// Parse with a length check; `None` when `bytes` is not
    /// `CT_BYTES` long. (Decapsulation itself never fails — the
    /// re-encryption check inside catches any tampering.)
    pub fn from_bytes(bytes: &[u8]) -> Option<Self> {
        (bytes.len() == P::CT_BYTES).then(|| Self {
            bytes: bytes.to_vec(),
            _p: PhantomData,
        })
    }
}

impl<P: FrodoParams> AsRef<[u8]> for Ciphertext<P> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl<P: FrodoParams> AsMut<[u8]> for Ciphertext<P> {
    fn as_mut(&mut self) -> &mut [u8] {
        &mut self.bytes
    }
}
impl<P: FrodoParams> std::fmt::Debug for Ciphertext<P> {
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
///
/// # Errors
/// [`InvalidInput::InvalidLength`] when `s` or `seed_se` is not
/// `SS_BYTES` long.
pub fn keygen<P: FrodoParams>(
    s: &[u8],
    seed_se: &[u8],
    z: &[u8; 16],
) -> SchemeResult<(SecretKey<P>, PublicKey<P>)> {
    // All three sections follow the reference's CRYPTO_BYTES sizing: `s`
    // and `seedSE` are SS bytes each, `z` is the 16-byte seed_A entropy.
    InvalidInput::check_len(P::SS_BYTES, s.len())?;
    InvalidInput::check_len(P::SS_BYTES, seed_se.len())?;
    // seed_A = shake(z).
    let mut seed_a = [0u8; SEED_A_BYTES];
    shake_xof::<P>(&[z], &mut seed_a);

    // (S ‖ E) ← sample(shake(SEEDSE_KEYGEN_PREFIX ‖ seedSE)), raw 16-bit draws.
    let nbar = P::NBAR;
    let se_len = P::N * nbar;
    let mut raw = shake_sample_block::<P>(SEEDSE_KEYGEN_PREFIX, seed_se, 2 * se_len);
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
    Ok((sk, pk))
}

/// FrodoKEM encapsulation with fresh encapsulation randomness `mu`
/// (`EXTRACTED_BITS·n̄²/8` bytes — the reference's `randombytes(mu)`).
///
/// # Errors
/// [`InvalidInput::InvalidLength`] when `mu` is not `MU_BYTES` long.
pub fn encapsulate<P: FrodoParams>(
    ek: &PublicKey<P>,
    mu: &[u8],
) -> SchemeResult<(Ciphertext<P>, SharedSecret)> {
    InvalidInput::check_len(P::MU_BYTES, mu.len())?;
    let nbar = P::NBAR;
    let pk_bytes = ek.to_bytes();

    // pkh ← SHAKE128(pk); (seedSE ‖ k) ← SHAKE128(pkh ‖ mu).
    let mut pkh = vec![0u8; P::SS_BYTES];
    shake_xof::<P>(&[&pk_bytes], &mut pkh);
    let mut g2 = vec![0u8; 2 * P::SS_BYTES];
    shake_xof::<P>(&[&pkh, mu], &mut g2);
    let seed_se = g2[..P::SS_BYTES].to_vec();
    let k = g2[P::SS_BYTES..].to_vec();

    // (Sp ‖ Ep ‖ Epp) ← sample(shake(SEEDSE_ENCAPS_PREFIX ‖ seedSE)).
    let se_len = P::N * nbar;
    let raw = shake_sample_block::<P>(SEEDSE_ENCAPS_PREFIX, &seed_se, 2 * se_len + nbar * nbar);
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
    Ok((
        Ciphertext {
            bytes: ct,
            _p: PhantomData,
        },
        SharedSecret(ss),
    ))
}

/// FrodoKEM decapsulation. A ciphertext that fails the re-encryption
/// check yields `SHAKE128(ct ‖ s)` instead of `SHAKE128(ct ‖ k')` —
/// implicit rejection, selected without branching on the secret
/// comparison. (Wrong-length ciphertexts cannot be constructed:
/// [`Ciphertext::from_bytes`] validates the length.)
pub fn decapsulate<P: FrodoParams>(dk: &SecretKey<P>, ct: &Ciphertext<P>) -> SharedSecret {
    let nbar = P::NBAR;
    let se_len = P::N * nbar;
    let mask = ((1u32 << P::LOGQ) - 1) as u16;

    let c1_len = P::LOGQ as usize * se_len / 8;
    let mut bp = vec![0u16; se_len];
    encoding::unpack(&mut bp, &ct.bytes[..c1_len], P::LOGQ);
    let mut c = vec![0u16; nbar * nbar];
    encoding::unpack(&mut c, &ct.bytes[c1_len..], P::LOGQ);

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
    let raw = shake_sample_block::<P>(SEEDSE_ENCAPS_PREFIX, &seed_se, 2 * se_len + nbar * nbar);
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
    shake_xof::<P>(&[&ct.bytes, &fin_k], &mut ss);
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
            ///
            /// # Errors
            /// [`InvalidInput::InvalidLength`](crate::InvalidInput::InvalidLength) on wrong-length `s` /
            /// `seed_se`.
            pub fn keygen(
                s: &[u8],
                seed_se: &[u8],
                z: &[u8; 16],
            ) -> super::SchemeResult<(
                SecretKey<super::params::$params>,
                PublicKey<super::params::$params>,
            )> {
                super::keygen::<super::params::$params>(s, seed_se, z)
            }

            /// FrodoKEM encapsulation with fresh randomness `mu`.
            ///
            /// # Errors
            /// [`InvalidInput::InvalidLength`](crate::InvalidInput::InvalidLength) on wrong-length `mu`.
            pub fn encapsulate(
                ek: &PublicKey<super::params::$params>,
                mu: &[u8],
            ) -> super::SchemeResult<(Ciphertext<super::params::$params>, SharedSecret)> {
                super::encapsulate::<super::params::$params>(ek, mu)
            }

            /// FrodoKEM decapsulation with implicit rejection.
            pub fn decapsulate(
                dk: &SecretKey<super::params::$params>,
                ct: &Ciphertext<super::params::$params>,
            ) -> SharedSecret {
                super::decapsulate::<super::params::$params>(dk, ct)
            }
            /// Batch keygen across the rayon pool (`parallel` feature):
            /// `s[i]`, `seed_se[i]` and `z[i]` drive key `i`; per-item
            /// length errors are reported positionally.
            ///
            /// # Panics
            /// If the randomness slices do not pair up.
            #[cfg(feature = "parallel")]
            pub fn keygen_batch(
                s: &[&[u8]],
                seed_se: &[&[u8]],
                z: &[[u8; 16]],
            ) -> Vec<
                super::SchemeResult<(
                    SecretKey<super::params::$params>,
                    PublicKey<super::params::$params>,
                )>,
            > {
                assert_eq!(s.len(), seed_se.len(), "s and seed_se must pair up");
                assert_eq!(s.len(), z.len(), "s and z must pair up");
                use rayon::prelude::*;

                s.par_iter()
                    .enumerate()
                    .map(|(i, s)| super::keygen::<super::params::$params>(s, seed_se[i], &z[i]))
                    .collect()
            }

            /// Batch encapsulation across the rayon pool (`parallel`
            /// feature); `mu[i]` must be fresh per-ciphertext randomness.
            #[cfg(feature = "parallel")]
            pub fn encapsulate_batch(
                ek: &PublicKey<super::params::$params>,
                mu: &[&[u8]],
            ) -> Vec<super::SchemeResult<(Ciphertext<super::params::$params>, SharedSecret)>> {
                use rayon::prelude::*;

                mu.par_iter()
                    .map(|mu| super::encapsulate::<super::params::$params>(ek, mu))
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
