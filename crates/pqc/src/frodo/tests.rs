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

macro_rules! frodo_roundtrip_tests {
    ($mod_name:ident, $params:ty, $ek_len:literal, $dk_len:literal, $ct_len:literal, $ss_len:literal) => {
        mod $mod_name {
            use super::*;

            fn keygen_pair(tag: u8) -> (SecretKey<$params>, PublicKey<$params>) {
                let ss_len = <$params as FrodoParams>::SS_BYTES;
                let s = fresh_bytes(tag, ss_len);
                let seed_se = fresh_bytes(tag.wrapping_add(1), ss_len);
                let z = fresh_bytes(tag.wrapping_add(2), 16).try_into().unwrap();
                keygen(&s, &seed_se, &z)
            }

            #[test]
            fn key_sizes_and_roundtrip() {
                let (sk, pk) = keygen_pair(1);
                assert_eq!(pk.to_bytes().len(), $ek_len);
                assert_eq!(sk.to_bytes().len(), $dk_len);
                let mu = fresh_bytes(9, <$params as FrodoParams>::MU_BYTES);
                let (ct, ss) = encapsulate(&pk, &mu);
                assert_eq!(ct.as_bytes().len(), $ct_len);
                assert_eq!(decapsulate(&sk, &ct).as_bytes(), ss.as_bytes());
            }

            #[test]
            fn serialization_roundtrip() {
                let (sk, pk) = keygen_pair(2);
                let pk2 = PublicKey::<$params>::from_bytes(&pk.to_bytes()).unwrap();
                assert_eq!(pk, pk2);
                let sk2 = SecretKey::<$params>::from_bytes(&sk.to_bytes()).unwrap();
                let mu = fresh_bytes(8, <$params as FrodoParams>::MU_BYTES);
                let (ct, ss) = encapsulate(&pk2, &mu);
                assert_eq!(decapsulate(&sk2, &ct).as_bytes(), ss.as_bytes());
                // Truncated / padded inputs are rejected.
                let mut too_long = pk.to_bytes();
                too_long.push(0);
                assert!(PublicKey::<$params>::from_bytes(&too_long).is_none());
                assert!(SecretKey::<$params>::from_bytes(&sk.to_bytes()[..$dk_len - 1]).is_none());
            }

            #[test]
            fn encaps_is_deterministic_in_mu() {
                let (sk, pk) = keygen_pair(3);
                let mu = fresh_bytes(7, <$params as FrodoParams>::MU_BYTES);
                let (ct1, ss1) = encapsulate(&pk, &mu);
                let (ct2, ss2) = encapsulate(&pk, &mu);
                assert_eq!(ct1, ct2);
                assert_eq!(ss1.as_bytes(), ss2.as_bytes());
                assert_eq!(decapsulate(&sk, &ct1).as_bytes(), ss1.as_bytes());
            }

            #[test]
            fn implicit_rejection_on_tampered_ciphertext() {
                let (sk, pk) = keygen_pair(4);
                let mu = fresh_bytes(6, <$params as FrodoParams>::MU_BYTES);
                let (mut ct, ss) = encapsulate(&pk, &mu);
                ct.0[0] ^= 0x01;
                let bad = decapsulate(&sk, &ct);
                assert_ne!(bad.as_bytes(), ss.as_bytes());
                // Implicit rejection is deterministic.
                let again = decapsulate(&sk, &ct);
                assert_eq!(bad.as_bytes(), again.as_bytes());
                // Tampering c2 (the second block) is also rejected.
                let (mut ct2, _) = encapsulate(&pk, &mu);
                let last = ct2.as_bytes().len() - 1;
                ct2.0[last] ^= 0x80;
                let bad2 = decapsulate(&sk, &ct2);
                assert_ne!(bad2.as_bytes(), ss.as_bytes());
            }

            #[test]
            fn wrong_length_ciphertext_is_rejected() {
                let (sk, _pk) = keygen_pair(5);
                let raw = vec![0u8; $ct_len - 1];
                let ct = Ciphertext::from_bytes(raw.clone());
                let ss = decapsulate(&sk, &ct);
                // Implicit rejection hash over the raw input bytes ‖ s.
                fn rejection_hash<P: FrodoParams>(ct: &[u8], s: &[u8]) -> Vec<u8> {
                    let mut input = ct.to_vec();
                    input.extend_from_slice(s);
                    let mut out = vec![0u8; P::SS_BYTES];
                    shake_xof::<P>(&[&input], &mut out);
                    out
                }
                assert_eq!(
                    ss.as_bytes(),
                    rejection_hash::<$params>(&raw, &sk_s_bytes(&sk)).as_slice()
                );
            }
        }
    };
}

/// The recovery secret `s` of a secret key (test helper).
fn sk_s_bytes<P: FrodoParams>(sk: &SecretKey<P>) -> Vec<u8> {
    sk.to_bytes()[..<P as FrodoParams>::SS_BYTES].to_vec()
}

frodo_roundtrip_tests!(frodo640, params::Frodo640, 9616, 19888, 9720, 16);
frodo_roundtrip_tests!(frodo976, params::Frodo976, 15632, 31296, 15744, 24);
frodo_roundtrip_tests!(frodo1344, params::Frodo1344, 21520, 43088, 21632, 32);
