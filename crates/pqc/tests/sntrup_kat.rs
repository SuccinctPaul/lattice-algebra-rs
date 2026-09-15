//! Byte-exact verification against the official Streamlined NTRU Prime
//! round-3 submission KAT vectors (NTRU-Prime-Round3.zip,
//! `KAT/kem/sntrup{761,857,953,1277}/kat_kem.rsp`).
//!
//! The official KAT driver (`nist/kat_kem.c`, djb-modified Bassham)
//! seeds the AES-256-CTR DRBG with the record's 48-byte seed. The scheme
//! then consumes randomness through `urandom32()` — each call is its own
//! 4-byte `randombytes` draw, so the DRBG produces one full 16-byte block
//! per draw and discards 12 bytes. Keygen: `p` draws for `Small_random(g)`,
//! `p` draws for `Short_random(f)`, one `(p+3)/4`-byte draw for `rho`.
//! Encapsulation: `p` draws for `Short_random(r)`. The shared DRBG in
//! `common` reproduces those draws.

mod common;

use common::{hex_decode, Drbg};
use pqc::sntrup::{self, SecretKey, SntrupParams};

fn run_case<P: SntrupParams>(
    seed: &[u8; 48],
    expected: &(Vec<u8>, Vec<u8>, Vec<u8>, Vec<u8>),
    count: usize,
    set: &str,
) {
    let mut drbg = Drbg::new(seed);
    let p = P::P;

    // keygen: the reference draws g in p 4-byte `urandom32` granules and,
    // when R3_recip rejects g, resamples (another p granules) — f is drawn
    // only after a successful g, then one (p+3)/4-byte draw for rho. The
    // window below replicates that consumption exactly.
    let mut drawn: Vec<u8> = Vec::new();
    let draw4 = |drawn: &mut Vec<u8>, drbg: &mut Drbg| {
        for _ in 0..p {
            let mut word = [0u8; 4];
            drbg.fill(&mut word);
            drawn.extend_from_slice(&word);
        }
    };
    let mut attempt_start = 0usize;
    let (sk, pk) = loop {
        while drawn.len() < attempt_start + 8 * p {
            draw4(&mut drawn, &mut drbg);
        }
        let g = &drawn[attempt_start..attempt_start + 4 * p];
        let f = &drawn[attempt_start + 4 * p..attempt_start + 8 * p];
        // rho is only drawn (one full randombytes call) after a
        // successful g; probe the attempt with a placeholder.
        let placeholder = vec![0u8; P::SMALL_BYTES];
        match sntrup::keygen::<P>(g, f, &placeholder) {
            Some((mut sk, pk)) => {
                let mut real_rho = vec![0u8; P::SMALL_BYTES];
                drbg.fill(&mut real_rho);
                let mut skb = sk.to_bytes();
                let off = 2 * P::SMALL_BYTES + P::RQ_BYTES;
                skb[off..off + P::SMALL_BYTES].copy_from_slice(&real_rho);
                sk = SecretKey::<P>::from_bytes(&skb).unwrap();
                break (sk, pk);
            }
            None => attempt_start += 4 * p,
        }
    };
    assert_eq!(pk.to_bytes(), expected.0, "{set} count {count}: pk");
    assert_eq!(sk.to_bytes(), expected.1, "{set} count {count}: sk");

    // enc: p 4-byte draws for r.
    let mut r_random = Vec::with_capacity(4 * p);
    for _ in 0..p {
        let mut word = [0u8; 4];
        drbg.fill(&mut word);
        r_random.extend_from_slice(&word);
    }
    let (ct, ss) = sntrup::encapsulate::<P>(&pk, &r_random);
    assert_eq!(ct, expected.2.as_slice(), "{set} count {count}: ct");
    assert_eq!(ss.as_bytes(), expected.3.as_slice(), "{set} count {count}: ss");

    // dec: re-derives the same shared secret.
    let ss2 = sntrup::decapsulate::<P>(&sk, &ct);
    assert_eq!(ss2.as_bytes(), expected.3.as_slice(), "{set} count {count}: decaps");
}

fn run_set(set: &str) {
    let path = format!("{}/tests/data/sntrup-kat.json", env!("CARGO_MANIFEST_DIR"));
    let doc: serde_json::Value =
        serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let cases = doc["testCases"].as_array().unwrap();

    let mut ran = 0;
    for case in cases {
        if case["parameterSet"].as_str().unwrap() != set {
            continue;
        }
        let count = case["count"].as_u64().unwrap() as usize;
        let expected = (
            hex_decode(case["pk"].as_str().unwrap()),
            hex_decode(case["sk"].as_str().unwrap()),
            hex_decode(case["ct"].as_str().unwrap()),
            hex_decode(case["ss"].as_str().unwrap()),
        );
        let seed: [u8; 48] = hex_decode(case["seed"].as_str().unwrap())
            .try_into()
            .unwrap();
        match set {
            "sntrup761" => run_case::<pqc::sntrup::Sntrup761>(&seed, &expected, count, set),
            "sntrup857" => run_case::<pqc::sntrup::Sntrup857>(&seed, &expected, count, set),
            "sntrup953" => run_case::<pqc::sntrup::Sntrup953>(&seed, &expected, count, set),
            "sntrup1277" => run_case::<pqc::sntrup::Sntrup1277>(&seed, &expected, count, set),
            _ => unreachable!(),
        }
        ran += 1;
    }
    assert_eq!(ran, 3, "{set}: expected 3 KAT cases");
}

#[test]
fn kat_sntrup761() {
    run_set("sntrup761");
}

#[test]
fn kat_sntrup857() {
    run_set("sntrup857");
}

#[test]
fn kat_sntrup953() {
    run_set("sntrup953");
}

#[test]
fn kat_sntrup1277() {
    run_set("sntrup1277");
}
