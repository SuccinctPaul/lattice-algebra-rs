//! Shared test infrastructure: the Bassham AES-256-CTR DRBG used by every
//! NIST round-3 KAT harness (`rng.c` in the submission packages) plus
//! `.rsp` parsing helpers. The DRBG re-derives the per-test randomness so
//! the schemes' explicit-randomness APIs can be driven exactly like the
//! official `PQCgenKAT_kem.c` / `PQCtestKAT_kem.c` drivers.

use std::fmt::Write as _;

// ===========================================================================
// Minimal AES-256 (forward direction only) for the DRBG
// ===========================================================================

const SBOX: [u8; 256] = [
    0x63, 0x7C, 0x77, 0x7B, 0xF2, 0x6B, 0x6F, 0xC5, 0x30, 0x01, 0x67, 0x2B, 0xFE, 0xD7, 0xAB, 0x76,
    0xCA, 0x82, 0xC9, 0x7D, 0xFA, 0x59, 0x47, 0xF0, 0xAD, 0xD4, 0xA2, 0xAF, 0x9C, 0xA4, 0x72, 0xC0,
    0xB7, 0xFD, 0x93, 0x26, 0x36, 0x3F, 0xF7, 0xCC, 0x34, 0xA5, 0xE5, 0xF1, 0x71, 0xD8, 0x31, 0x15,
    0x04, 0xC7, 0x23, 0xC3, 0x18, 0x96, 0x05, 0x9A, 0x07, 0x12, 0x80, 0xE2, 0xEB, 0x27, 0xB2, 0x75,
    0x09, 0x83, 0x2C, 0x1A, 0x1B, 0x6E, 0x5A, 0xA0, 0x52, 0x3B, 0xD6, 0xB3, 0x29, 0xE3, 0x2F, 0x84,
    0x53, 0xD1, 0x00, 0xED, 0x20, 0xFC, 0xB1, 0x5B, 0x6A, 0xCB, 0xBE, 0x39, 0x4A, 0x4C, 0x58, 0xCF,
    0xD0, 0xEF, 0xAA, 0xFB, 0x43, 0x4D, 0x33, 0x85, 0x45, 0xF9, 0x02, 0x7F, 0x50, 0x3C, 0x9F, 0xA8,
    0x51, 0xA3, 0x40, 0x8F, 0x92, 0x9D, 0x38, 0xF5, 0xBC, 0xB6, 0xDA, 0x21, 0x10, 0xFF, 0xF3, 0xD2,
    0xCD, 0x0C, 0x13, 0xEC, 0x5F, 0x97, 0x44, 0x17, 0xC4, 0xA7, 0x7E, 0x3D, 0x64, 0x5D, 0x19, 0x73,
    0x60, 0x81, 0x4F, 0xDC, 0x22, 0x2A, 0x90, 0x88, 0x46, 0xEE, 0xB8, 0x14, 0xDE, 0x5E, 0x0B, 0xDB,
    0xE0, 0x32, 0x3A, 0x0A, 0x49, 0x06, 0x24, 0x5C, 0xC2, 0xD3, 0xAC, 0x62, 0x91, 0x95, 0xE4, 0x79,
    0xE7, 0xC8, 0x37, 0x6D, 0x8D, 0xD5, 0x4E, 0xA9, 0x6C, 0x56, 0xF4, 0xEA, 0x65, 0x7A, 0xAE, 0x08,
    0xBA, 0x78, 0x25, 0x2E, 0x1C, 0xA6, 0xB4, 0xC6, 0xE8, 0xDD, 0x74, 0x1F, 0x4B, 0xBD, 0x8B, 0x8A,
    0x70, 0x3E, 0xB5, 0x66, 0x48, 0x03, 0xF6, 0x0E, 0x61, 0x35, 0x57, 0xB9, 0x86, 0xC1, 0x1D, 0x9E,
    0xE1, 0xF8, 0x98, 0x11, 0x69, 0xD9, 0x8E, 0x94, 0x9B, 0x1E, 0x87, 0xE9, 0xCE, 0x55, 0x28, 0xDF,
    0x8C, 0xA1, 0x89, 0x0D, 0xBF, 0xE6, 0x42, 0x68, 0x41, 0x99, 0x2D, 0x0F, 0xB0, 0x54, 0xBB, 0x16,
];

const RCON: [u8; 8] = [0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40];

fn xtime(x: u8) -> u8 {
    (x << 1) ^ (((x >> 7) & 1) * 0x1B)
}

/// AES-256 encryption of one 16-byte block (FIPS-197, 14 rounds).
fn aes256_encrypt_block(key: &[u8; 32], block: &[u8; 16]) -> [u8; 16] {
    // Nk = 8 words, Nb = 4, Nr = 14 → 60 words of round-key material.
    let mut w = [[0u8; 4]; 60];
    for (i, word) in w.iter_mut().enumerate().take(8) {
        *word = [key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]];
    }
    for i in 8..60 {
        let mut temp = w[i - 1];
        if i % 8 == 0 {
            temp = [
                SBOX[temp[1] as usize],
                SBOX[temp[2] as usize],
                SBOX[temp[3] as usize],
                SBOX[temp[0] as usize],
            ];
            temp[0] ^= RCON[i / 8];
        }
        if i % 8 == 4 {
            temp = [
                SBOX[temp[0] as usize],
                SBOX[temp[1] as usize],
                SBOX[temp[2] as usize],
                SBOX[temp[3] as usize],
            ];
        }
        for j in 0..4 {
            w[i][j] = w[i - 8][j] ^ temp[j];
        }
    }

    // State is column-major: state[r + 4c]; round keys applied word-wise.
    let mut state = *block;
    let add_round_key = |state: &mut [u8; 16], round: usize| {
        for c in 0..4 {
            for r in 0..4 {
                state[4 * c + r] ^= w[4 * round + c][r];
            }
        }
    };
    add_round_key(&mut state, 0);
    for round in 1..14 {
        for b in state.iter_mut() {
            *b = SBOX[*b as usize];
        }
        let old = state;
        for r in 1..4 {
            for c in 0..4 {
                state[r + 4 * c] = old[r + 4 * ((c + r) % 4)];
            }
        }
        for c in 0..4 {
            let col = [state[4 * c], state[4 * c + 1], state[4 * c + 2], state[4 * c + 3]];
            let dbl = [xtime(col[0]), xtime(col[1]), xtime(col[2]), xtime(col[3])];
            state[4 * c] = dbl[0] ^ xtime(col[1]) ^ col[1] ^ col[2] ^ col[3];
            state[4 * c + 1] = col[0] ^ dbl[1] ^ xtime(col[2]) ^ col[2] ^ col[3];
            state[4 * c + 2] = col[0] ^ col[1] ^ dbl[2] ^ xtime(col[3]) ^ col[3];
            state[4 * c + 3] = xtime(col[0]) ^ col[0] ^ col[1] ^ col[2] ^ dbl[3];
        }
        add_round_key(&mut state, round);
    }
    for b in state.iter_mut() {
        *b = SBOX[*b as usize];
    }
    let old = state;
    for r in 1..4 {
        for c in 0..4 {
            state[r + 4 * c] = old[r + 4 * ((c + r) % 4)];
        }
    }
    add_round_key(&mut state, 14);
    state
}

// ===========================================================================
// The Bassham DRBG (submission rng.c)
// ===========================================================================

/// AES-256-CTR DRBG, byte-exact with the NIST KAT `rng.c`.
pub struct Drbg {
    key: [u8; 32],
    v: [u8; 16],
}

impl Drbg {
    /// `randombytes_init(entropy_input, NULL, 256)` — the personalization
    /// string is never used by the KAT drivers.
    pub fn new(entropy_input: &[u8; 48]) -> Self {
        let mut drbg = Drbg {
            key: [0u8; 32],
            v: [0u8; 16],
        };
        let mut temp = [0u8; 48];
        for i in 0..3 {
            drbg.increment_v();
            temp[16 * i..16 * (i + 1)].copy_from_slice(&aes256_encrypt_block(
                &drbg.key,
                &drbg.v,
            ));
        }
        for i in 0..48 {
            temp[i] ^= entropy_input[i];
        }
        drbg.key.copy_from_slice(&temp[..32]);
        drbg.v.copy_from_slice(&temp[32..]);
        drbg
    }

    fn increment_v(&mut self) {
        for j in (0..16).rev() {
            if self.v[j] == 0xFF {
                self.v[j] = 0x00;
            } else {
                self.v[j] += 1;
                break;
            }
        }
    }

    /// `randombytes(x, xlen)`: full 16-byte counter blocks, then a key
    /// update — one call, exactly as the reference consumes randomness.
    pub fn fill(&mut self, out: &mut [u8]) {
        let mut done = 0;
        while done < out.len() {
            self.increment_v();
            let block = aes256_encrypt_block(&self.key, &self.v);
            let take = (out.len() - done).min(16);
            out[done..done + take].copy_from_slice(&block[..take]);
            done += take;
        }
        let mut temp = [0u8; 48];
        for i in 0..3 {
            self.increment_v();
            temp[16 * i..16 * (i + 1)].copy_from_slice(&aes256_encrypt_block(
                &self.key,
                &self.v,
            ));
        }
        self.key.copy_from_slice(&temp[..32]);
        self.v.copy_from_slice(&temp[32..]);
    }
}

// ===========================================================================
// Hex helpers
// ===========================================================================

pub fn hex_encode(b: &[u8]) -> String {
    b.iter().fold(String::new(), |mut s, x| {
        let _ = write!(s, "{:02x}", x);
        s
    })
}

pub fn hex_decode(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).expect("valid hex"))
        .collect()
}

#[cfg(test)]
mod selftest {
    use super::*;

    /// SP 800-38A F.1.5 (AES-256 block 1) validates the cipher used by
    /// the DRBG.
    #[test]
    fn aes256_sp80038a_vector() {
        let key = [
            0x60, 0x3D, 0xEB, 0x10, 0x15, 0xCA, 0x71, 0xBE, 0x2B, 0x73, 0xAE, 0xF0, 0x85, 0x7D,
            0x77, 0x81, 0x1F, 0x35, 0x2C, 0x07, 0x3B, 0x61, 0x08, 0xD7, 0x2D, 0x98, 0x10, 0xA3,
            0x09, 0x14, 0xDF, 0xF4,
        ];
        let pt = [
            0x6B, 0xC1, 0xBE, 0xE2, 0x2E, 0x40, 0x9F, 0x96, 0xE9, 0x3D, 0x7E, 0x11, 0x73, 0x93,
            0x17, 0x2A,
        ];
        assert_eq!(
            hex_encode(&aes256_encrypt_block(&key, &pt)),
            "f3eed1bdb5d2a03c064b5a7e3db181f8"
        );
    }
}
