//! End-to-end tours of the round-3 lattice alternates — FrodoKEM, NTRU and
//! Streamlined NTRU Prime — through their per-set APIs: keygen, encapsulate,
//! decapsulate with implicit rejection, and canonical serialization. The
//! randomness inputs are deterministic byte fills; the APIs are typed-error
//! (`SchemeResult`), so a wrong-length input is a reported error, not a
//! panic.
//!
//! Run with: `cargo run -p lattice-pqc --example kem_alternates`

use pqc::frodo::frodo976;
use pqc::frodo::params::FrodoParams;
use pqc::ntru::ntruhrss701;
use pqc::ntru::params::{NtruHrss701, NtruParams};
use pqc::sntrup::params::{Sntrup761, SntrupParams};
use pqc::sntrup::sntrup761;

fn fresh_bytes(tag: u8, len: usize) -> Vec<u8> {
    (0..len)
        .map(|i| tag.wrapping_mul(31).wrapping_add(i as u8))
        .collect()
}

fn main() {
    // --- FrodoKEM-976 -----------------------------------------------------
    let ss = <pqc::frodo::params::Frodo976 as FrodoParams>::SS_BYTES;
    let mu_len = <pqc::frodo::params::Frodo976 as FrodoParams>::MU_BYTES;
    let (sk, ek) = frodo976::keygen(
        &fresh_bytes(1, ss),
        &fresh_bytes(2, ss),
        &[3u8; 16],
    )
    .expect("well-sized keygen randomness");
    let mu = fresh_bytes(4, mu_len);
    let (ct, k) = frodo976::encapsulate(&ek, &mu).expect("well-sized mu");
    assert_eq!(frodo976::decapsulate(&sk, &ct).as_bytes(), k.as_bytes());
    println!(
        "frodo976   ct = {} B, ss = {:02X?}",
        ct.as_bytes().len(),
        &k.as_bytes()[..8]
    );

    // --- NTRU hrss701 -----------------------------------------------------
    let fg_len = <NtruHrss701 as NtruParams>::SAMPLE_FG_BYTES;
    let rm_len = <NtruHrss701 as NtruParams>::SAMPLE_RM_BYTES;
    let (sk, pk) = ntruhrss701::keygen(&fresh_bytes(5, fg_len), &[6u8; 32])
        .expect("well-sized keygen randomness");
    let (ct, k) = ntruhrss701::encapsulate(&pk, &fresh_bytes(7, rm_len))
        .expect("well-sized encapsulation randomness");
    assert_eq!(ntruhrss701::decapsulate(&sk, &ct).as_bytes(), k.as_bytes());
    println!(
        "ntruhrss701 ct = {} B, ss = {:02X?}",
        ct.as_bytes().len(),
        &k.as_bytes()[..8]
    );

    // --- Streamlined NTRU Prime sntrup761 (the OpenSSH instance) ----------
    let p = <Sntrup761 as SntrupParams>::P;
    let small = <Sntrup761 as SntrupParams>::SMALL_BYTES;
    // A uniform ternary g is invertible with probability ≈ 2/3; the
    // reference's KeyGen resamples — so does this loop.
    let (sk, pk) = loop {
        let g_random = fresh_bytes(8, 4 * p);
        let f_random = fresh_bytes(9, 4 * p);
        let rho = fresh_bytes(10, small);
        match sntrup761::keygen(&g_random, &f_random, &rho) {
            Ok(keys) => break keys,
            Err(pqc::InvalidInput::KeygenRetry) => continue,
            Err(e) => panic!("unexpected keygen error: {e}"),
        }
    };
    let (ct, k) = sntrup761::encapsulate(&pk, &fresh_bytes(11, 4 * p))
        .expect("well-sized encapsulation randomness");
    assert_eq!(sntrup761::decapsulate(&sk, &ct).as_bytes(), k.as_bytes());
    println!(
        "sntrup761  ct = {} B, ss = {:02X?}",
        ct.as_bytes().len(),
        &k.as_bytes()[..8]
    );

    // A wrong-length randomness input is a typed error, never a panic.
    let err = frodo976::encapsulate(&ek, &fresh_bytes(12, mu_len - 1))
        .expect_err("short mu must be rejected");
    println!("wrong-length mu → {err}");

    println!("frodo / ntru / sntrup roundtrips ✓");
}
