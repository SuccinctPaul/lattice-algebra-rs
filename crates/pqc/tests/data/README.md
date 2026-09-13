# KAT fixtures (ML-DSA / FIPS 204, ML-KEM / FIPS 203, Falcon round-3)

These JSON files hold byte-exact known-answer tests extracted from the
**official NIST ACVP-Server sample vectors**:

- ML-DSA source: <https://github.com/usnistgov/ACVP-Server>, `gen-val/json-files/`
  (`ML-DSA-keyGen-FIPS204`, `ML-DSA-sigGen-FIPS204`, `ML-DSA-sigVer-FIPS204`)
  — revision `master@975de31eb83d87039ec88934fdc47d8c312b892d` (fetched
  2026-09-05, re-extracted 2026-09-14 for the internal/preHash modes);
- ML-KEM source: same repo/layout (`ML-KEM-keyGen-FIPS203`,
  `ML-KEM-encapDecap-FIPS203`) — same revision (fetched 2026-09-11).

The `_meta` header of each fixture repeats this provenance. The harnesses
that consume them live in `crates/pqc/tests/acvp_kat.rs` (ML-DSA) and
`crates/pqc/tests/acvp_mlkem_kat.rs` (ML-KEM).

## Files

| file | cases | coverage |
| --- | --- | --- |
| `acvp-keygen.json` | 75 | all 25 keyGen vectors for each of ML-DSA-44/65/87 (seed → pk, sk) |
| `acvp-siggen.json` | 27 | pure-mode sigGen: 6 per deterministic group and 3 per randomized group (fixed `rnd`) for all parameter sets |
| `acvp-sigver.json` | 24 | pure-mode sigVer accept **and** reject cases (first 8 of every group) |
| `acvp-siggen-internal.json` | 54 | internal-interface sigGen: external-μ groups (precomputed 64-byte μ) and μ = H(tr ‖ M) groups, deterministic + randomized |
| `acvp-sigver-internal.json` | 48 | internal-interface sigVer: external-μ and μ = H(tr' ‖ M) accept/reject cases |
| `acvp-siggen-prehash.json` | 27 | external preHash sigGen (OID-separated M', ACVP draft variant), deterministic + randomized |
| `acvp-sigver-prehash.json` | 24 | external preHash sigVer (OID-separated M') accept/reject cases |
| `acvp-mlkem.json` | 183 | ML-KEM: keyGen 75 (all sets), encaps 24, decaps 24 (incl. implicit rejection), keyCheck 60 (accept + reject) |
| `falcon-kat.json` | 10 | Falcon round-3 submission KAT: falcon512 × 5, falcon1024 × 5 — full keygen/sign/verify bundles (the official `.rsp` files have 100 tests per set) |

ML-DSA scope: pure mode (the `ML-DSA.Sign/Verify(message, context)` API)
**plus the internal interfaces** — external-μ signing/verification
(`sign_mu`/`verify_mu`, the `Sign_internal`/`Verify_internal` signing-loop
primitive), internal groups whose μ is `H(tr ‖ M)` **without** the pure-mode
`(0x00, ctxLen, ctx)` prefix (confirmed against the ACVP-Server reference,
`Dilithium.Sign(sk, m, rnd)`; exercised through `sign_mu`/`verify_mu` with
the μ composed in the harness), and the external preHash groups. The
preHash groups are the ACVP *draft* OID-separated variant — the tested
composition is `M' = 1 ‖ |ctx| ‖ ctx ‖ OID ‖ PH(M)` (per the ACVP-Server
`ExternalSignatureBase.ExternalPreHashSign`, PH lengths fixed by its
`ShaAttributes`: digest size for SHA-2/SHA-3, 256 bits for SHAKE-128,
512 bits for SHAKE-256). That is deliberately **not** the final FIPS 204
HashML-DSA composition (no OID): the crate implements the final one
(`sign_hash_mldsa`/`verify_hash_mldsa`), and the harness composes the ACVP
M' through the `sign_m_prime`/`verify_m_prime` internal interfaces.

## Regenerating

```sh
# Falcon: from the round-3 submission package (Falcon-Round3.zip), place the
# two .rsp files in /tmp/falcon-kat:
#   KAT/falcon512-KAT.rsp  KAT/falcon1024-KAT.rsp
python3 extract_falcon_kat.py /tmp/falcon-kat .

# ML-DSA: from the ACVP-Server repo (or via raw.githubusercontent.com), place in /tmp/acvp:
#   ML-DSA-{keyGen,sigGen,sigVer}-FIPS204-{prompt,expectedResults}.json
python3 extract_acvp.py /tmp/acvp .

# ML-KEM: place in /tmp/acvp-mlkem:
#   ML-KEM-{keyGen,encapDecap}-FIPS203-{prompt,expectedResults}.json
python3 extract_mlkem_acvp.py /tmp/acvp-mlkem .
```

The extractors keep the committed payload small by capping per-group
selections (ML-KEM: keyGen all 25/set, encaps + decaps first 8/set,
keyCheck all); edit the filters to embed more (or all) vectors.
