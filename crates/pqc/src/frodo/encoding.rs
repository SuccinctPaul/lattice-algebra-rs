//! FrodoKEM bit-level codecs: the `PARAMS_LOGQ`-bit packing of matrix
//! entries (`frodo_pack` / `frodo_unpack`) and the
//! `PARAMS_EXTRACTED_BITS`-bit key encoding added to the ciphertext
//! (`frodo_key_encode` / `frodo_key_decode`).

/// Pack the low `lsb` bits of each `u16` of `input` into `output`
/// (most-significant bits first — the reference `frodo_pack`).
pub fn pack(output: &mut [u8], input: &[u16], lsb: u32) {
    assert_eq!(
        output.len(),
        input.len() * lsb as usize / 8,
        "packed length"
    );
    output.iter_mut().for_each(|b| *b = 0);

    let mut i = 0usize; // whole bytes already filled in
    let mut j = 0usize; // whole u16s already copied
    let mut w = 0u16; // leftover, not yet copied
    let mut bits = 0u32; // number of `lsb` bits in `w`

    while i < output.len() && (j < input.len() || bits > 0) {
        let mut b = 0u32; // bits in output[i] already filled in
        while b < 8 {
            let nbits = u32::min(8 - b, bits);
            let mask = (1u16 << nbits) - 1;
            let t = (w >> (bits - nbits)) & mask;
            // C shifts an int-promoted zero harmlessly; mirror that.
            output[i] = output[i].wrapping_add(((t as u32) << (8 - b - nbits)) as u8);
            b += nbits;
            bits -= nbits;

            if bits == 0 {
                if j < input.len() {
                    w = input[j];
                    bits = lsb;
                    j += 1;
                } else {
                    break;
                }
            }
        }
        if b == 8 {
            i += 1;
        }
    }
}

/// Inverse of [`pack`]: take `lsb` bits per element from the byte stream.
pub fn unpack(output: &mut [u16], input: &[u8], lsb: u32) {
    assert_eq!(
        input.len(),
        output.len() * lsb as usize / 8,
        "unpacked length"
    );
    output.iter_mut().for_each(|v| *v = 0);

    let mut i = 0usize; // whole u16s already filled in
    let mut j = 0usize; // whole bytes already copied
    let mut w = 0u8; // leftover, not yet copied
    let mut bits = 0u32; // number of bits in `w`

    while i < output.len() && (j < input.len() || bits > 0) {
        let mut b = 0u32; // bits in output[i] already filled in
        while b < lsb {
            let nbits = u32::min(lsb - b, bits);
            let mask = ((1u16 << nbits) - 1) as u8;
            let t = ((w >> (bits - nbits)) & mask) as u16;
            // u32 intermediate: the shift amount can reach `lsb`.
            output[i] = output[i].wrapping_add(((t as u32) << (lsb - b - nbits)) as u16);
            b += nbits;
            bits -= nbits;

            if bits == 0 {
                if j < input.len() {
                    w = input[j];
                    bits = 8;
                    j += 1;
                } else {
                    break;
                }
            }
        }
        if b == lsb {
            i += 1;
        }
    }
}

/// `frodo_key_encode`: spread each `EXTRACTED_BITS`-bit chunk of the
/// message across the top of a `q`-ranged coefficient:
/// `c = chunk << (LOGQ − EXTRACTED_BITS)`. The message is consumed as
/// little-endian `EXTRACTED_BITS`-byte words, 8 coefficients per word.
pub fn key_encode<P: super::FrodoParams>(mu: &[u8]) -> Vec<u16> {
    assert_eq!(mu.len(), P::MU_BYTES, "message length");
    let eb = P::EXTRACTED_BITS as usize;
    let mask = (1u16 << eb) - 1;
    let mut out = Vec::with_capacity(P::NBAR * P::NBAR);
    for word in mu.chunks_exact(eb) {
        let mut temp = 0u64;
        for (jj, &byte) in word.iter().enumerate() {
            temp |= (byte as u64) << (8 * jj);
        }
        for _ in 0..8 {
            let chunk = (temp & mask as u64) as u16;
            out.push(chunk << (P::LOGQ - P::EXTRACTED_BITS));
            temp >>= eb;
        }
    }
    out
}

/// `frodo_key_decode`: recover the `EXTRACTED_BITS`-bit chunks with
/// round-to-nearest: `floor((c + 2^(LOGQ−EB−1)) / 2^(LOGQ−EB))`.
pub fn key_decode<P: super::FrodoParams>(c: &[u16]) -> Vec<u8> {
    assert_eq!(c.len(), P::NBAR * P::NBAR, "decoded block length");
    let eb = P::EXTRACTED_BITS;
    let shift = P::LOGQ - eb;
    let mask_ex = (1u16 << eb) - 1;
    let mask_q = ((1u32 << P::LOGQ) - 1) as u16; // q − 1 (LOGQ ≤ 16)
    let eb_us = eb as usize;
    let mut out = vec![0u8; P::MU_BYTES];
    for (i, chunk) in out.chunks_exact_mut(eb_us).enumerate() {
        let mut templong = 0u64;
        for jj in 0..8 {
            let coef = c[8 * i + jj];
            // C promotes to int before the add; use u32 to avoid a u16
            // overflow when coef approaches q = 2^16.
            let temp = (((coef & mask_q) as u32) + (1u32 << (shift - 1))) >> shift;
            templong |= ((temp & mask_ex as u32) as u64) << (eb_us * jj);
        }
        for (jj, byte) in chunk.iter_mut().enumerate() {
            *byte = (templong >> (8 * jj)) as u8;
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frodo::params::{Frodo1344, Frodo640, FrodoParams};

    #[test]
    fn pack_roundtrip_15_and_16_bits() {
        let input: Vec<u16> = (0u32..8192)
            .map(|i| (i.wrapping_mul(2654435761) % 32768) as u16)
            .collect();
        let mut bytes = vec![0u8; input.len() * 15 / 8];
        pack(&mut bytes, &input, 15);
        let mut back = vec![0u16; input.len()];
        unpack(&mut back, &bytes, 15);
        assert_eq!(back, input);
    }

    #[test]
    fn key_encode_decode_roundtrip() {
        for _ in 0..20 {
            let mu: Vec<u8> = (0..Frodo640::MU_BYTES).map(|i| (i * 7 + 3) as u8).collect();
            let encoded = key_encode::<Frodo640>(&mu);
            assert_eq!(encoded.len(), Frodo640::NBAR * Frodo640::NBAR);
            assert_eq!(key_decode::<Frodo640>(&encoded), mu);

            let mu: Vec<u8> = (0..Frodo1344::MU_BYTES).map(|i| (i * 13) as u8).collect();
            let encoded = key_encode::<Frodo1344>(&mu);
            assert_eq!(key_decode::<Frodo1344>(&encoded), mu);
        }
    }
}
