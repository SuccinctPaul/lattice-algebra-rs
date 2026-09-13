# KAT fixtures (ML-DSA / FIPS 204, ML-KEM / FIPS 203, Falcon round-3)

These JSON files hold byte-exact known-answer tests extracted from the
**official NIST ACVP-Server sample vectors**:

- ML-DSA source: <https://github.com/usnistgov/ACVP-Server>, `gen-val/json-files/`
  (`ML-DSA-keyGen-FIPS204`, `ML-DSA-sigGen-FIPS204`, `ML-DSA-sigVer-FIPS204`)
  — revision `master@975de31eb83d87039ec88934fdc47d8c312b892d` (fetched 2026-09-05);
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
| `acvp-mlkem.json` | 183 | ML-KEM: keyGen 75 (all sets), encaps 24, decaps 24 (incl. implicit rejection), keyCheck 60 (accept + reject) |
| `falcon-kat.json` | 10 | Falcon round-3 submission KAT: falcon512 × 5, falcon1024 × 5 — full keygen/sign/verify bundles (the official `.rsp` files have 100 tests per set) |

ML-DSA scope: **pure mode, external interface** — the `ML-DSA.Sign/Verify(message,
context)` API this crate implements. The official dataset also contains
`preHash` groups (HashML-DSA), `internal` groups with an externally supplied
`mu`, and `internal` groups whose message is hashed *without* the pure-mode
`(0x00, ctxLen, ctx)` prefix (confirmed against the reference
implementation); those exercise different variants/APIs and are excluded.
They become in-scope when the corresponding APIs are added.

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
