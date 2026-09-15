//! Unit tests for this scheme, split out of `mod.rs`.
//! `use super::*` keeps `pub(crate)` helpers reachable.

use super::*;

/// Deterministic pseudo-random byte fill (round-trip tests don't need
/// statistical randomness — only independence between test cases).
fn fresh_bytes(tag: u8, len: usize) -> Vec<u8> {
    (0..len)
        .map(|i| tag.wrapping_mul(31).wrapping_add(i as u8))
        .collect()
}

macro_rules! ntru_roundtrip_tests {
    ($mod_name:ident, $params:ty, $pk_len:literal, $sk_len:literal) => {
        mod $mod_name {
            use super::*;

            fn keygen_pair(tag: u8) -> (SecretKey<$params>, PublicKey<$params>) {
                let seed_len = <$params as NtruParams>::SAMPLE_FG_BYTES;
                let seed = fresh_bytes(tag, seed_len);
                let prf_key = fresh_bytes(tag.wrapping_add(0x40), 32).try_into().unwrap();
                keygen(&seed, &prf_key)
            }

            #[test]
            fn key_sizes_and_roundtrip() {
                let (sk, pk) = keygen_pair(1);
                assert_eq!(pk.to_bytes().len(), $pk_len);
                assert_eq!(sk.to_bytes().len(), $sk_len);
                let rm = fresh_bytes(9, <$params as NtruParams>::SAMPLE_RM_BYTES);
                let (ct, ss) = encapsulate(&pk, &rm);
                assert_eq!(ct.len(), $pk_len, "ciphertext length equals pk length");
                assert_eq!(decapsulate(&sk, &ct).as_bytes(), ss.as_bytes());
            }

            #[test]
            fn serialization_roundtrip() {
                let (sk, pk) = keygen_pair(2);
                let pk2 = PublicKey::<$params>::from_bytes(&pk.to_bytes()).unwrap();
                assert_eq!(pk, pk2);
                let sk2 = SecretKey::<$params>::from_bytes(&sk.to_bytes()).unwrap();
                let rm = fresh_bytes(8, <$params as NtruParams>::SAMPLE_RM_BYTES);
                let (ct, ss) = encapsulate(&pk2, &rm);
                assert_eq!(decapsulate(&sk2, &ct).as_bytes(), ss.as_bytes());
                let mut too_long = pk.to_bytes();
                too_long.push(0);
                assert!(PublicKey::<$params>::from_bytes(&too_long).is_none());
                assert!(SecretKey::<$params>::from_bytes(&sk.to_bytes()[..$sk_len - 1]).is_none());
            }

            #[test]
            fn implicit_rejection_on_tampered_ciphertext() {
                let (sk, pk) = keygen_pair(3);
                let rm = fresh_bytes(7, <$params as NtruParams>::SAMPLE_RM_BYTES);
                let (mut ct, ss) = encapsulate(&pk, &rm);
                ct[0] ^= 0x01;
                let bad = decapsulate(&sk, &ct);
                assert_ne!(bad.as_bytes(), ss.as_bytes());
                // Implicit rejection is deterministic.
                let again = decapsulate(&sk, &ct);
                assert_eq!(bad.as_bytes(), again.as_bytes());
                // A wrong-length ciphertext is rejected the same way.
                let short = decapsulate(&sk, &ct[..ct.len() - 1]);
                assert_ne!(short.as_bytes(), ss.as_bytes());
            }
        }
    };
}

ntru_roundtrip_tests!(ntruhps2048677, params::NtruHps2048677, 930, 1234);
ntru_roundtrip_tests!(ntruhps2048821, params::NtruHps2048821, 1128, 1488);
ntru_roundtrip_tests!(ntruhps4096821, params::NtruHps4096821, 1230, 1590);
ntru_roundtrip_tests!(ntruhps40961229, params::NtruHps40961229, 1842, 2366);
ntru_roundtrip_tests!(ntruhrss701, params::NtruHrss701, 1138, 1450);
