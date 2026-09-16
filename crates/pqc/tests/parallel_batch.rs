//! Batch-API equivalence tests for the `parallel` feature.
//!
//! Every `*_batch` entry point must produce exactly the same outputs as
//! calling the single-shot API item by item: the batch wrappers only
//! redistribute independent operations across the rayon pool, so results
//! are order-preserving and bit-identical.

// The whole file is meaningless without the feature; `#![cfg]` keeps the
// test target empty (and passing) on default builds.
#![cfg(feature = "parallel")]

/// Deterministic xorshift so failures are reproducible.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut s = self.0;
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        self.0 = s;
        s
    }

    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len).map(|_| self.next() as u8).collect()
    }
}

const BATCH: usize = 8;

#[test]
fn mlkem768_batch_matches_sequential() {
    use pqc::mlkem::mlkem_768;

    let mut rng = Rng(0xA11C_E500);
    let d: Vec<[u8; 32]> = (0..BATCH)
        .map(|_| rng.bytes(32).try_into().unwrap())
        .collect();
    let z: Vec<[u8; 32]> = (0..BATCH)
        .map(|_| rng.bytes(32).try_into().unwrap())
        .collect();
    let m: Vec<[u8; 32]> = (0..BATCH)
        .map(|_| rng.bytes(32).try_into().unwrap())
        .collect();

    let keys = mlkem_768::keygen_batch(&d, &z);
    assert_eq!(keys.len(), BATCH);

    for i in 0..BATCH {
        // Sequential reference for the same inputs.
        let (_dk_ref, ek_ref) = mlkem_768::keygen(&d[i], &z[i]);
        let (ct_ref, ss_ref) = mlkem_768::encapsulate(&ek_ref, &m[i]);

        let (dk_b, ek_b) = &keys[i];
        let enc = mlkem_768::encapsulate_batch(ek_b, std::slice::from_ref(&m[i]));
        let (ct, ss) = &enc[0];
        assert_eq!(ct.as_bytes(), ct_ref.as_bytes(), "ct {i}");
        assert_eq!(ss.as_bytes(), ss_ref.as_bytes(), "ss {i}");

        let ss_dec = mlkem_768::decapsulate_batch(dk_b, std::slice::from_ref(&ct_ref));
        assert_eq!(ss_dec[0].as_bytes(), ss_ref.as_bytes(), "decaps {i}");
    }
}

#[test]
fn mldsa65_batch_matches_sequential() {
    use pqc::mldsa::mldsa_65;

    let mut rng = Rng(0xB22D_F611);
    let (sk, vk) = mldsa_65::keygen(&rng.bytes(32).try_into().unwrap());
    let msgs: Vec<Vec<u8>> = (0..BATCH).map(|i| rng.bytes(64 + i * 13)).collect();
    let msg_refs: Vec<&[u8]> = msgs.iter().map(Vec::as_slice).collect();
    let ctx = b"batch test context";

    let sigs = mldsa_65::sign_deterministic_batch(&sk, ctx, &msg_refs);
    assert_eq!(sigs.len(), BATCH);
    for (i, sig) in sigs.iter().enumerate() {
        assert_eq!(
            sig,
            &mldsa_65::sign_deterministic(&sk, ctx, &msgs[i]),
            "sig {i}"
        );
    }

    let sig_refs: Vec<&[u8]> = sigs.iter().map(Vec::as_slice).collect();
    let verdicts = mldsa_65::verify_batch(&vk, ctx, &msg_refs, &sig_refs);
    assert_eq!(verdicts, vec![true; BATCH]);

    // One tampered signature must flip exactly its own verdict.
    let mut tampered = sigs.clone();
    tampered[3][10] ^= 0x40;
    let tampered_refs: Vec<&[u8]> = tampered.iter().map(Vec::as_slice).collect();
    let verdicts = mldsa_65::verify_batch(&vk, ctx, &msg_refs, &tampered_refs);
    assert!(!verdicts[3]);
    assert_eq!(verdicts.iter().filter(|&&v| v).count(), BATCH - 1);
}

#[test]
fn falcon512_batch_matches_sequential() {
    use pqc::falcon::falcon512;

    let mut rng = Rng(0xC33E_0722);
    let (sk, pk) = falcon512::keygen(&rng.bytes(48).try_into().unwrap());
    let msgs: Vec<Vec<u8>> = (0..BATCH).map(|i| rng.bytes(32 + i * 7)).collect();
    let msg_refs: Vec<&[u8]> = msgs.iter().map(Vec::as_slice).collect();
    let nonces: Vec<[u8; 40]> = (0..BATCH)
        .map(|_| rng.bytes(40).try_into().unwrap())
        .collect();
    let seeds: Vec<[u8; 48]> = (0..BATCH)
        .map(|_| rng.bytes(48).try_into().unwrap())
        .collect();

    let sigs = falcon512::sign_batch(&sk, &msg_refs, &nonces, &seeds);
    assert_eq!(sigs.len(), BATCH);
    for (i, sig) in sigs.iter().enumerate() {
        assert_eq!(
            sig,
            &falcon512::sign(&sk, &msgs[i], &nonces[i], &seeds[i]),
            "sig {i}"
        );
    }

    let sig_refs: Vec<&[u8]> = sigs.iter().map(Vec::as_slice).collect();
    let verdicts = falcon512::verify_batch(&pk, &msg_refs, &nonces, &sig_refs);
    assert_eq!(verdicts, vec![true; BATCH]);
}

#[test]
fn frodo640_batch_matches_sequential() {
    use pqc::frodo::{frodo640, params::Frodo640, FrodoParams};

    let mut rng = Rng(0xD44F_1833);
    let ss_len = <Frodo640 as FrodoParams>::SS_BYTES;
    let mu_len = <Frodo640 as FrodoParams>::MU_BYTES;

    let s_seeds: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(ss_len)).collect();
    let se_seeds: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(ss_len)).collect();
    let z_seeds: Vec<[u8; 16]> = (0..BATCH)
        .map(|_| rng.bytes(16).try_into().unwrap())
        .collect();
    let mus: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(mu_len)).collect();

    let s_refs: Vec<&[u8]> = s_seeds.iter().map(Vec::as_slice).collect();
    let se_refs: Vec<&[u8]> = se_seeds.iter().map(Vec::as_slice).collect();
    let mu_refs: Vec<&[u8]> = mus.iter().map(Vec::as_slice).collect();

    let keys = frodo640::keygen_batch(&s_refs, &se_refs, &z_seeds);
    assert!(
        keys.iter().all(Result::is_ok),
        "frodo keygen is infallible on fixed-length seeds"
    );

    for i in 0..BATCH {
        let (_dk_ref, ek_ref) = frodo640::keygen(&s_seeds[i], &se_seeds[i], &z_seeds[i]).unwrap();
        let (ct_ref, ss_ref) = frodo640::encapsulate(&ek_ref, &mus[i]).unwrap();

        let (dk_b, ek_b) = keys[i].as_ref().unwrap();
        let enc = frodo640::encapsulate_batch(ek_b, &mu_refs[i..i + 1]);
        let (ct, ss) = enc[0].as_ref().unwrap();
        assert_eq!(ct.as_bytes(), ct_ref.as_bytes(), "ct {i}");
        assert_eq!(ss.as_bytes(), ss_ref.as_bytes(), "ss {i}");

        let ss_dec = frodo640::decapsulate_batch(dk_b, std::slice::from_ref(&ct_ref));
        assert_eq!(ss_dec[0].as_bytes(), ss_ref.as_bytes(), "decaps {i}");
    }
}

#[test]
fn ntru_batch_matches_sequential() {
    use pqc::ntru::{ntruhps2048677, params::NtruHps2048677, NtruParams};

    let seed_len = <NtruHps2048677 as NtruParams>::SAMPLE_FG_BYTES;
    let mut rng = Rng(0xE550_2944);
    let seeds: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(seed_len)).collect();
    let prf_keys: Vec<[u8; 32]> = (0..BATCH)
        .map(|_| rng.bytes(32).try_into().unwrap())
        .collect();
    let rm_seeds: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(seed_len)).collect();
    let seed_refs: Vec<&[u8]> = seeds.iter().map(Vec::as_slice).collect();
    let rm_refs: Vec<&[u8]> = rm_seeds.iter().map(Vec::as_slice).collect();

    let keys = ntruhps2048677::keygen_batch(&seed_refs, &prf_keys);
    assert!(keys.iter().all(Result::is_ok));

    for i in 0..BATCH {
        let (_dk_ref, ek_ref) = ntruhps2048677::keygen(&seeds[i], &prf_keys[i]).unwrap();
        let (ct_ref, ss_ref) = ntruhps2048677::encapsulate(&ek_ref, &rm_seeds[i]).unwrap();

        let (dk_b, ek_b) = keys[i].as_ref().unwrap();
        let enc = ntruhps2048677::encapsulate_batch(ek_b, &rm_refs[i..i + 1]);
        let (ct, ss) = enc[0].as_ref().unwrap();
        assert_eq!(ct.as_bytes(), ct_ref.as_bytes(), "ct {i}");
        assert_eq!(ss.as_bytes(), ss_ref.as_bytes(), "ss {i}");

        let ss_dec = ntruhps2048677::decapsulate_batch(dk_b, std::slice::from_ref(&ct_ref));
        assert_eq!(ss_dec[0].as_bytes(), ss_ref.as_bytes(), "decaps {i}");
    }
}

#[test]
fn sntrup761_batch_matches_sequential() {
    use pqc::sntrup::{params::Sntrup761, sntrup761, SntrupParams};

    const URANDOM32_BYTES: usize = 4;
    let stream_len = URANDOM32_BYTES * <Sntrup761 as SntrupParams>::P;
    let rho_len = <Sntrup761 as SntrupParams>::SMALL_BYTES;
    let mut rng = Rng(0xF661_3A55);

    let g: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(stream_len)).collect();
    let f: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(stream_len)).collect();
    let rho: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(rho_len)).collect();
    let r_rand: Vec<Vec<u8>> = (0..BATCH).map(|_| rng.bytes(stream_len)).collect();
    let g_refs: Vec<&[u8]> = g.iter().map(Vec::as_slice).collect();
    let f_refs: Vec<&[u8]> = f.iter().map(Vec::as_slice).collect();
    let rho_refs: Vec<&[u8]> = rho.iter().map(Vec::as_slice).collect();
    let r_refs: Vec<&[u8]> = r_rand.iter().map(Vec::as_slice).collect();

    let keys = sntrup761::keygen_batch(&g_refs, &f_refs, &rho_refs);
    assert!(
        keys.iter().all(Result::is_ok),
        "deterministic randomness chosen to avoid the ~1/q retry"
    );

    for i in 0..BATCH {
        let (_dk_ref, ek_ref) = sntrup761::keygen(&g[i], &f[i], &rho[i]).unwrap();
        let (ct_ref, ss_ref) = sntrup761::encapsulate(&ek_ref, &r_rand[i]).unwrap();

        let (dk_b, ek_b) = keys[i].as_ref().unwrap();
        let enc = sntrup761::encapsulate_batch(ek_b, &r_refs[i..i + 1]);
        let (ct, ss) = enc[0].as_ref().unwrap();
        assert_eq!(ct.as_bytes(), ct_ref.as_bytes(), "ct {i}");
        assert_eq!(ss.as_bytes(), ss_ref.as_bytes(), "ss {i}");

        let ss_dec = sntrup761::decapsulate_batch(dk_b, std::slice::from_ref(&ct_ref));
        assert_eq!(ss_dec[0].as_bytes(), ss_ref.as_bytes(), "decaps {i}");
    }
}
