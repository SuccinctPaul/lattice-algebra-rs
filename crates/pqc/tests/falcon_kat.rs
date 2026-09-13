//! Official round-3 Falcon KAT vectors (NIST submission package).
//!
//! The KAT harness drives the implementation through the same byte stream
//! the official generator used: a 48-byte seed initializes an AES-256-CTR
//! DRBG (`katrng` ported below, including its AES-256); key generation
//! draws 48 bytes, signing draws a 40-byte nonce and a 48-byte seed. All
//! outputs (pk, sk, signature bundle) must match the official vectors
//! byte-for-byte.
//! Official round-3 Falcon KAT vectors (NIST submission package).
//!
//! The KAT harness drives the implementation through the same byte stream
//! the official generator used: a 48-byte seed initializes an AES-256-CTR
//! DRBG (`katrng` ported below, including its AES-256); key generation
//! draws 48 bytes, signing draws a 40-byte nonce and a 48-byte seed. All
//! outputs (pk, sk, signature bundle) must match the official vectors
//! byte-for-byte.

use serde_json::Value;

// ===================================================================
// AES-256 (ECB, single block) — standard implementation, test-only.
// ===================================================================

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

fn xtime(x: u8) -> u8 {
    (x << 1) ^ (((x >> 7) & 1) * 0x1B)
}

fn aes256_expand_key(key: &[u8; 32]) -> [[u8; 4]; 60] {
    let mut w = [[0u8; 4]; 60];
    let rcon: [u8; 7] = [0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40];
    for i in 0..8 {
        w[i] = [key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]];
    }
    let mut rc = 0usize;
    for i in 8..60 {
        let mut tmp = w[i - 1];
        if i % 8 == 0 {
            tmp = [tmp[1], tmp[2], tmp[3], tmp[0]];
            for b in tmp.iter_mut() {
                *b = SBOX[*b as usize];
            }
            tmp[0] ^= rcon[rc];
            rc += 1;
        } else if i % 8 == 4 {
            for b in tmp.iter_mut() {
                *b = SBOX[*b as usize];
            }
        }
        for j in 0..4 {
            w[i][j] = w[i - 8][j] ^ tmp[j];
        }
    }
    w
}

fn aes256_encrypt_block(w: &[[u8; 4]; 60], block: &mut [u8; 16]) {
    let add_round_key = |st: &mut [u8; 16], wk: &[[u8; 4]; 60], round: usize| {
        for c in 0..4 {
            for r in 0..4 {
                st[4 * c + r] ^= wk[round * 4 + c][r];
            }
        }
    };

    let mut st = *block;
    add_round_key(&mut st, w, 0);

    for round in 1..14 {
        // SubBytes
        for b in st.iter_mut() {
            *b = SBOX[*b as usize];
        }
        // ShiftRows
        let mut t = [0u8; 16];
        for c in 0..4 {
            for r in 0..4 {
                t[4 * c + r] = st[4 * ((c + r) % 4) + r];
            }
        }
        st = t;
        // MixColumns (full rounds 1..=13; the final round below omits it)
        for c in 0..4 {
            let a = [st[4 * c], st[4 * c + 1], st[4 * c + 2], st[4 * c + 3]];
            let x = a[0] ^ a[1] ^ a[2] ^ a[3];
            for r in 0..4 {
                st[4 * c + r] = a[r] ^ x ^ xtime(a[r] ^ a[(r + 1) % 4]);
            }
        }
        add_round_key(&mut st, w, round);
    }
    // Final round (no MixColumns): SubBytes/ShiftRows + key add.
    for b in st.iter_mut() {
        *b = SBOX[*b as usize];
    }
    let mut t = [0u8; 16];
    for c in 0..4 {
        for r in 0..4 {
            t[4 * c + r] = st[4 * ((c + r) % 4) + r];
        }
    }
    st = t;
    add_round_key(&mut st, w, 14);
    *block = st;
}

// ===================================================================
// katrng: AES-256 CTR DRBG (NIST KAT generator).
// ===================================================================

struct KatRng {
    key: [u8; 32],
    v: [u8; 16],
}

impl KatRng {
    fn drbg_update(&mut self, provided: Option<&[u8; 48]>) {
        let mut temp = [0u8; 48];
        for i in 0..3 {
            // increment V
            for j in (0..16).rev() {
                self.v[j] = self.v[j].wrapping_add(1);
                if self.v[j] != 0 {
                    break;
                }
            }
            let mut block = self.v;
            let sched = aes256_expand_key(&self.key);
            aes256_encrypt_block(&sched, &mut block);
            temp[16 * i..16 * i + 16].copy_from_slice(&block);
        }
        if let Some(prov) = provided {
            for i in 0..48 {
                temp[i] ^= prov[i];
            }
        }
        self.key.copy_from_slice(&temp[..32]);
        self.v.copy_from_slice(&temp[32..]);
    }

    fn init(entropy_input: &[u8; 48]) -> Self {
        let mut rng = KatRng {
            key: [0u8; 32],
            v: [0u8; 16],
        };
        rng.drbg_update(Some(entropy_input));
        rng
    }

    fn random_bytes(&mut self, out: &mut [u8]) {
        let mut i = 0usize;
        let mut xlen = out.len();
        while xlen > 0 {
            // increment V
            for j in (0..16).rev() {
                self.v[j] = self.v[j].wrapping_add(1);
                if self.v[j] != 0 {
                    break;
                }
            }
            let mut block = self.v;
            let sched = aes256_expand_key(&self.key);
            aes256_encrypt_block(&sched, &mut block);
            if xlen > 15 {
                out[i..i + 16].copy_from_slice(&block);
                i += 16;
                xlen -= 16;
            } else {
                out[i..i + xlen].copy_from_slice(&block[..xlen]);
                xlen = 0;
            }
        }
        self.drbg_update(None);
    }
}

// ===================================================================
// KAT harness.
// ===================================================================

fn hex_decode(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

fn run_case(set: &str, rec: &Value) {
    let seed: [u8; 48] = hex_decode(rec["seed"].as_str().unwrap())
        .try_into()
        .unwrap();
    let msg = hex_decode(rec["msg"].as_str().unwrap());
    let want_pk = hex_decode(rec["pk"].as_str().unwrap());
    let want_sk = hex_decode(rec["sk"].as_str().unwrap());
    let want_sm = hex_decode(rec["sm"].as_str().unwrap());
    let id = (set, rec["count"].as_i64().unwrap());

    let mut rng = KatRng::init(&seed);

    // keypair
    let mut keygen_seed = [0u8; 48];
    rng.random_bytes(&mut keygen_seed);
    let (sk, pk) = match set {
        "falcon512" => pqc::falcon::falcon512::keygen(&keygen_seed),
        "falcon1024" => pqc::falcon::falcon1024::keygen(&keygen_seed),
        _ => unreachable!(),
    };
    assert_eq!(pk.to_bytes(), want_pk, "pk mismatch for {id:?}");
    assert_eq!(sk.to_bytes(), want_sk, "sk mismatch for {id:?}");

    // sign: nonce (40) then signing seed (48)
    let mut nonce = [0u8; 40];
    rng.random_bytes(&mut nonce);
    let mut sig_seed = [0u8; 48];
    rng.random_bytes(&mut sig_seed);
    let esig = match set {
        "falcon512" => pqc::falcon::falcon512::sign(&sk, &msg, &nonce, &sig_seed),
        "falcon1024" => pqc::falcon::falcon1024::sign(&sk, &msg, &nonce, &sig_seed),
        _ => unreachable!(),
    };

    // Bundle: 2-byte big-endian sig length ‖ nonce ‖ msg ‖ esig.
    let sig_len = esig.len();
    let mut sm = Vec::with_capacity(2 + 40 + msg.len() + sig_len);
    sm.push((sig_len >> 8) as u8);
    sm.push((sig_len & 0xFF) as u8);
    sm.extend_from_slice(&nonce);
    sm.extend_from_slice(&msg);
    sm.extend_from_slice(&esig);
    assert_eq!(sm, want_sm, "sm mismatch for {id:?}");

    // Verify over (msg, nonce).
    let ok = match set {
        "falcon512" => pqc::falcon::falcon512::verify(&pk, &msg, &nonce, &esig),
        "falcon1024" => pqc::falcon::falcon1024::verify(&pk, &msg, &nonce, &esig),
        _ => unreachable!(),
    };
    assert!(ok, "verify failed for {id:?}");
}

/// Official round-3 Falcon KAT vectors (falcon512 + falcon1024):
/// keygen, sign, and verify must reproduce the reference byte streams.
#[test]
fn falcon_official_kat() {
    let path = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/data/falcon-kat.json");
    let doc: Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).expect("fixture JSON");
    for rec in doc["testCases"].as_array().unwrap() {
        run_case(rec["parameterSet"].as_str().unwrap(), rec);
    }
}

#[test]
#[ignore = "debug tool: compare katrng output with C"]
fn katrng_probe() {
    let entropy: [u8; 48] = [
        0x06, 0x15, 0x50, 0x23, 0x4D, 0x15, 0x8C, 0x5E, 0xC9, 0x55, 0x95, 0xFE, 0x04, 0xEF, 0x7A,
        0x25, 0x76, 0x7F, 0x2E, 0x24, 0xCC, 0x2B, 0xC4, 0x79, 0xD0, 0x9D, 0x86, 0xDC, 0x9A, 0xBC,
        0xFD, 0xE7, 0x05, 0x6A, 0x8C, 0x26, 0x6F, 0x9E, 0xF9, 0x7E, 0xD0, 0x85, 0x41, 0xDB, 0xD2,
        0xE1, 0xFF, 0xA1,
    ];
    let mut rng = KatRng::init(&entropy);
    let mut out = [0u8; 48];
    rng.random_bytes(&mut out);
    let hex: String = out.iter().map(|b| format!("{b:02X}")).collect();
    println!("katrng out = {hex}");
}

/// AES-256 core must match the FIPS-197 known answer before it feeds the
/// DRBG — a wrong round drops every KAT byte.
#[test]
fn aes256_kat() {
    let mut key = [0u8; 32];
    for (i, b) in key.iter_mut().enumerate() {
        *b = i as u8;
    }
    let mut block: [u8; 16] = [
        0x00, 0x11, 0x22, 0x33, 0x44, 0x55, 0x66, 0x77, 0x88, 0x99, 0xaa, 0xbb, 0xcc, 0xdd, 0xee,
        0xff,
    ];
    let sched = aes256_expand_key(&key);
    aes256_encrypt_block(&sched, &mut block);
    let hex: String = block.iter().map(|b| format!("{b:02X}")).collect();
    assert_eq!(
        hex, "8EA2B7CA516745BFEAFC49904B496089",
        "AES-256 known-answer mismatch"
    );
}
