//! Unit tests for this scheme, split out of `mod.rs`.
//! `use super::*` keeps `pub(crate)` helpers reachable.

use super::*;

macro_rules! mlkem_roundtrip_tests {
    ($mod_name:ident, $params:ty, $k:literal, $ek_len:literal, $dk_len:literal, $ct_len:literal) => {
        mod $mod_name {
            use super::*;

            fn fresh_coins(tag: u8) -> ([u8; 32], [u8; 32]) {
                let d = [tag; 32];
                let mut z = [0u8; 32];
                z[..32].copy_from_slice(&d);
                z[0] = tag.wrapping_add(0x40);
                (d, z)
            }

            #[test]
            fn key_sizes_and_roundtrip() {
                let (d, z) = fresh_coins(1);
                let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                assert_eq!(ek.to_bytes().len(), $ek_len);
                assert_eq!(dk.to_bytes().len(), $dk_len);
                let m = [7u8; 32];
                let (c, ss) = encapsulate_internal::<$params, $k>(&ek, &m);
                assert_eq!(c.len(), $ct_len);
                assert_eq!(
                    decapsulate::<$params, $k>(&dk, &c).as_bytes(),
                    ss.as_bytes()
                );
            }

            #[test]
            fn encaps_is_deterministic_in_m() {
                let (d, z) = fresh_coins(2);
                let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                let m = [0x42u8; 32];
                let (c1, ss1) = encapsulate_internal::<$params, $k>(&ek, &m);
                let (c2, ss2) = encapsulate_internal::<$params, $k>(&ek, &m);
                assert_eq!(c1, c2);
                assert_eq!(ss1.as_bytes(), ss2.as_bytes());
                assert_eq!(
                    decapsulate::<$params, $k>(&dk, &c1).as_bytes(),
                    ss1.as_bytes()
                );
            }

            #[test]
            fn implicit_rejection_on_tampered_ciphertext() {
                let (d, z) = fresh_coins(3);
                let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                let m = [9u8; 32];
                let (mut c, ss) = encapsulate_internal::<$params, $k>(&ek, &m);
                c[0] ^= 0x01;
                let bad = decapsulate::<$params, $k>(&dk, &c);
                assert_ne!(bad.as_bytes(), ss.as_bytes());
                // Implicit rejection is deterministic.
                let again = decapsulate::<$params, $k>(&dk, &c);
                assert_eq!(bad.as_bytes(), again.as_bytes());
                // A different tampering point yields a different rejection key.
                let mut c2 = c;
                c2[$ct_len - 1] ^= 0x80;
                let other = decapsulate::<$params, $k>(&dk, &c2);
                assert_ne!(bad.as_bytes(), other.as_bytes());
            }

            #[test]
            fn wrong_length_ciphertext_rejects_implicitly() {
                let (d, z) = fresh_coins(4);
                let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                let m = [5u8; 32];
                let (c, _) = encapsulate_internal::<$params, $k>(&ek, &m);
                let short = decapsulate::<$params, $k>(&dk, &c[..$ct_len - 1]);
                let again = decapsulate::<$params, $k>(&dk, &c[..$ct_len - 1]);
                assert_eq!(short.as_bytes(), again.as_bytes());
                let (c2, ss2) = encapsulate_internal::<$params, $k>(&ek, &m);
                assert_ne!(
                    short.as_bytes(),
                    decapsulate::<$params, $k>(&dk, &c2).as_bytes()
                );
                assert_eq!(
                    decapsulate::<$params, $k>(&dk, &c2).as_bytes(),
                    ss2.as_bytes()
                );
            }

            #[test]
            fn key_serialization_roundtrip() {
                let (d, z) = fresh_coins(5);
                let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                let ek2 = EncapsulationKey::<$params>::from_bytes(&ek.to_bytes()).unwrap();
                assert_eq!(ek2, ek);
                let dk2 = DecapsulationKey::<$params>::from_bytes(&dk.to_bytes()).unwrap();
                let m = [0x11u8; 32];
                let (c, ss) = encapsulate_internal::<$params, $k>(&ek, &m);
                assert_eq!(
                    decapsulate::<$params, $k>(&dk2, &c).as_bytes(),
                    ss.as_bytes()
                );
                // Encoded keys decapsulate identically.
                assert_eq!(dk2.to_bytes(), dk.to_bytes());
            }

            #[test]
            fn key_check_rejects_bad_encodings() {
                let (d, z) = fresh_coins(6);
                let (dk, ek) = keygen_internal::<$params, $k>(&d, &z);
                // Wrong lengths.
                let ek_bytes = ek.to_bytes();
                let dk_bytes = dk.to_bytes();
                assert!(
                    EncapsulationKey::<$params>::from_bytes(&ek_bytes[..ek_bytes.len() - 1])
                        .is_none()
                );
                assert!(
                    DecapsulationKey::<$params>::from_bytes(&dk_bytes[..dk_bytes.len() - 1])
                        .is_none()
                );
                // Coefficient ≥ q in the first t̂ row (3329 fits in 12 bits).
                let mut bad_ek = ek_bytes.clone();
                bad_ek[0] = 0x01; // low byte of 3329 = 0x0D01 little-endian
                bad_ek[1] = 0x0D;
                assert!(EncapsulationKey::<$params>::from_bytes(&bad_ek).is_none());
                // Coefficient ≥ q in the first ŝ row of the decapsulation key.
                let mut bad_dk = dk_bytes.clone();
                bad_dk[0] = 0x01;
                bad_dk[1] = 0x0D;
                assert!(DecapsulationKey::<$params>::from_bytes(&bad_dk).is_none());
            }

            #[test]
            fn cbd_matches_spec_bit_pattern() {
                // η = 2, coefficient 0 uses bits (b0,b1,b2,b3) as
                // (b0+b1) − (b2+b3): 0b0000_0100 has b2 = 1 → 0 − 1 = −1;
                // all-ones bytes give 2 − 2 = 0.
                let bytes = [0b0000_0100u8; 128];
                let f = sample_cbd(&bytes, 2);
                assert_eq!(f[0], -1);
                assert_eq!(f[1], 0);
                let ones = [0xFFu8; 128];
                assert!(sample_cbd(&ones, 2).iter().all(|&v| v == 0));
                let zeros = [0x00u8; 192];
                assert!(sample_cbd(&zeros, 3).iter().all(|&v| v == 0));
            }
        }
    };
}

mlkem_roundtrip_tests!(ml_kem_512, MlKem512, 2, 800, 1632, 768);
mlkem_roundtrip_tests!(ml_kem_768, MlKem768, 3, 1184, 2400, 1088);
mlkem_roundtrip_tests!(ml_kem_1024, MlKem1024, 4, 1568, 3168, 1568);
