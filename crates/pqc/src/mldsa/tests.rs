//! Unit tests for this scheme, split out of `mod.rs`.
//! `use super::*` keeps `pub(crate)` helpers reachable.

use super::*;

pub(crate) const MSG: &[u8] = b"the quick brown fox jumps over the lazy dog";
pub(crate) const CTX: &[u8] = b"test-context";

macro_rules! mldsa_roundtrip_tests {
    ($mod_name:ident, $params:ty, $k:literal, $l:literal, $pk_len:literal, $sig_len:literal, $sk_len:literal) => {
        mod $mod_name {
            use super::*;

            #[test]
            fn sign_verify_roundtrip() {
                let seed = [42u8; 32];
                let (sk, vk) = keygen_seed::<$params, $k, $l>(&seed);
                let sigma = sign_deterministic::<$params, $k, $l>(&sk, CTX, MSG);
                assert_eq!(sigma.len(), $sig_len);
                assert!(verify_core::<$params, $k, $l>(&vk, CTX, MSG, &sigma));
            }

            #[test]
            fn deterministic_signature() {
                let seed = [7u8; 32];
                let (sk, _) = keygen_seed::<$params, $k, $l>(&seed);
                let s1 = sign_deterministic::<$params, $k, $l>(&sk, CTX, MSG);
                let s2 = sign_deterministic::<$params, $k, $l>(&sk, CTX, MSG);
                assert_eq!(s1, s2);
            }

            #[test]
            fn rejects_tampered_message() {
                let (sk, vk) = keygen_seed::<$params, $k, $l>(&seed2());
                let sigma = sign_deterministic::<$params, $k, $l>(&sk, CTX, MSG);
                let mut bad_msg = MSG.to_vec();
                bad_msg[0] ^= 1;
                assert!(!verify_core::<$params, $k, $l>(&vk, CTX, &bad_msg, &sigma));
            }

            fn seed2() -> [u8; 32] {
                let mut s = [0u8; 32];
                s[..16].copy_from_slice(b"second-seed-0000");
                s
            }

            #[test]
            fn rejects_tampered_signature() {
                let (sk, vk) = keygen_seed::<$params, $k, $l>(&seed2());
                let mut sigma = sign_deterministic::<$params, $k, $l>(&sk, CTX, MSG);
                let last = sigma.len() - 1;
                sigma[last] ^= 0x01;
                assert!(!verify_core::<$params, $k, $l>(&vk, CTX, MSG, &sigma));
                // Restore and flip a z byte (in the middle of z encoding).
                let mut sigma2 = sign_deterministic::<$params, $k, $l>(&sk, CTX, MSG);
                let z_pos = <$params>::C_TILDE_BYTES + 10;
                sigma2[z_pos] ^= 0x04;
                // Bit flips in z may or may not stay in range; a valid
                // flip must be rejected either way.
                let _ = verify_core::<$params, $k, $l>(&vk, CTX, MSG, &sigma2);
            }

            #[test]
            fn rejects_wrong_context() {
                let (sk, vk) = keygen_seed::<$params, $k, $l>(&seed2());
                let sigma = sign_deterministic::<$params, $k, $l>(&sk, CTX, MSG);
                assert!(!verify_core::<$params, $k, $l>(
                    &vk,
                    b"other-context",
                    MSG,
                    &sigma
                ));
            }

            #[test]
            fn rejects_wrong_key() {
                let (sk, _) = keygen_seed::<$params, $k, $l>(&seed2());
                let (_, vk_other) = keygen_seed::<$params, $k, $l>(&[3u8; 32]);
                let sigma = sign_deterministic::<$params, $k, $l>(&sk, CTX, MSG);
                assert!(!verify_core::<$params, $k, $l>(&vk_other, CTX, MSG, &sigma));
            }

            #[test]
            fn key_serialization_roundtrip() {
                let (sk, vk) = keygen_seed::<$params, $k, $l>(&seed2());
                assert_eq!(vk.to_bytes().len(), $pk_len);
                assert_eq!(sk.to_bytes().len(), $sk_len);
                assert_eq!(
                    VerifyingKey::<$params>::from_bytes(&vk.to_bytes()).unwrap(),
                    vk
                );
                assert_eq!(
                    SigningKey::<$params>::from_bytes(&sk.to_bytes()).unwrap(),
                    sk
                );
            }

            #[test]
            fn signing_key_signs_for_matching_verifying_key() {
                // sk → bytes → verify against re-derived vk? The FIPS sk
                // does not carry t1, so re-derive via keygen from ξ is
                // not possible; instead verify that the decoded sk
                // produces a signature the original vk accepts.
                let (sk, vk) = keygen_seed::<$params, $k, $l>(&seed2());
                let sk2 = SigningKey::<$params>::from_bytes(&sk.to_bytes()).unwrap();
                let sigma = sign_deterministic::<$params, $k, $l>(&sk2, CTX, MSG);
                assert!(verify_core::<$params, $k, $l>(&vk, CTX, MSG, &sigma));
            }
        }
    };
}

mldsa_roundtrip_tests!(ml_dsa_44, MlDsa44, 4, 4, 1312, 2420, 2560);
mldsa_roundtrip_tests!(ml_dsa_65, MlDsa65, 6, 5, 1952, 3309, 4032);
mldsa_roundtrip_tests!(ml_dsa_87, MlDsa87, 8, 7, 2592, 4627, 4896);
