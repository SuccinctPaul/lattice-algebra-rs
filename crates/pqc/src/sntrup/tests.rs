//! Unit tests for this scheme, split out of `mod.rs`.

use super::*;
use alloc::vec::Vec;

/// Deterministic pseudo-random byte fill (round-trip tests don't need
/// statistical randomness — only independence between test cases).
fn fresh_bytes(tag: u8, len: usize) -> Vec<u8> {
    (0..len)
        .map(|i| tag.wrapping_mul(31).wrapping_add(i as u8))
        .collect()
}

macro_rules! sntrup_roundtrip_tests {
    ($mod_name:ident, $params:ty) => {
        mod $mod_name {
            use super::*;

            fn keygen_pair(tag: u8) -> (SecretKey<$params>, PublicKey<$params>) {
                let p = <$params as SntrupParams>::P;
                // A uniform ternary g is invertible in R3 with probability
                // ≈ 2/3; retry with fresh randomness like the reference's
                // KeyGen loop.
                for attempt in 0.. {
                    let t = tag.wrapping_add(attempt as u8);
                    let g_random = fresh_bytes(t, 4 * p);
                    let f_random = fresh_bytes(t.wrapping_add(1), 4 * p);
                    let rho =
                        fresh_bytes(t.wrapping_add(2), <$params as SntrupParams>::SMALL_BYTES);
                    if let Ok(keys) = keygen(&g_random, &f_random, &rho) {
                        return keys;
                    }
                }
                unreachable!()
            }

            #[test]
            fn key_sizes_and_roundtrip() {
                let (sk, pk) = keygen_pair(1);
                assert_eq!(pk.to_bytes().len(), <$params as SntrupParams>::RQ_BYTES);
                assert_eq!(
                    sk.to_bytes().len(),
                    <$params as SntrupParams>::SECRETKEY_BYTES
                );
                let r = fresh_bytes(9, 4 * <$params as SntrupParams>::P);
                let (ct, ss) = encapsulate(&pk, &r).expect("well-sized r");
                assert_eq!(
                    ct.as_bytes().len(),
                    <$params as SntrupParams>::CIPHERTEXT_BYTES
                );
                assert_eq!(decapsulate(&sk, &ct).as_bytes(), ss.as_bytes());
            }

            #[test]
            fn serialization_roundtrip() {
                let (sk, pk) = keygen_pair(2);
                let pk2 = PublicKey::<$params>::from_bytes(&pk.to_bytes()).unwrap();
                assert_eq!(pk, pk2);
                let sk2 = SecretKey::<$params>::from_bytes(&sk.to_bytes()).unwrap();
                let r = fresh_bytes(8, 4 * <$params as SntrupParams>::P);
                let (ct, ss) = encapsulate(&pk2, &r).expect("well-sized r");
                assert_eq!(decapsulate(&sk2, &ct).as_bytes(), ss.as_bytes());
                let mut short_pk = pk.to_bytes();
                short_pk.pop();
                assert!(PublicKey::<$params>::from_bytes(&short_pk).is_none());
            }

            #[test]
            fn implicit_rejection_on_tampered_ciphertext() {
                let (sk, pk) = keygen_pair(3);
                let r = fresh_bytes(7, 4 * <$params as SntrupParams>::P);
                let (mut ct, ss) = encapsulate(&pk, &r).expect("well-sized r");
                ct.as_mut()[0] ^= 0x01;
                let bad = decapsulate(&sk, &ct);
                assert_ne!(bad.as_bytes(), ss.as_bytes());
                // Implicit rejection is deterministic.
                let again = decapsulate(&sk, &ct);
                assert_eq!(bad.as_bytes(), again.as_bytes());
                // A wrong-length ciphertext cannot be constructed at all.
                assert!(Ciphertext::<$params>::from_bytes(
                    &ct.as_bytes()[..<$params as SntrupParams>::CIPHERTEXT_BYTES - 1]
                )
                .is_none());
            }
        }
    };
}

sntrup_roundtrip_tests!(sntrup653, params::Sntrup653);
sntrup_roundtrip_tests!(sntrup761, params::Sntrup761);
sntrup_roundtrip_tests!(sntrup857, params::Sntrup857);
sntrup_roundtrip_tests!(sntrup953, params::Sntrup953);
sntrup_roundtrip_tests!(sntrup1013, params::Sntrup1013);
sntrup_roundtrip_tests!(sntrup1277, params::Sntrup1277);
