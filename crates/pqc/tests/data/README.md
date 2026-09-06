# ACVP KAT fixtures (ML-DSA / FIPS 204)

These JSON files hold byte-exact known-answer tests extracted from the
**official NIST ACVP-Server sample vectors**:

- source: <https://github.com/usnistgov/ACVP-Server>, `gen-val/json-files/`
  (`ML-DSA-keyGen-FIPS204`, `ML-DSA-sigGen-FIPS204`, `ML-DSA-sigVer-FIPS204`)
- revision: `master@975de31eb83d87039ec88934fdc47d8c312b892d` (fetched 2026-09-05)

The `_meta` header of each fixture repeats this provenance. The harness that
consumes them lives in `crates/pqc/tests/acvp_kat.rs`.

## Files

| file | cases | coverage |
| --- | --- | --- |
| `acvp-keygen.json` | 75 | all 25 keyGen vectors for each of ML-DSA-44/65/87 (seed → pk, sk) |
| `acvp-siggen.json` | 27 | pure-mode sigGen: 6 per deterministic group and 3 per randomized group (fixed `rnd`) for all parameter sets |
| `acvp-sigver.json` | 24 | pure-mode sigVer accept **and** reject cases (first 8 of every group) |

Scope: **pure mode, external interface** — the `ML-DSA.Sign/Verify(message,
context)` API this crate implements. The official dataset also contains
`preHash` groups (HashML-DSA), `internal` groups with an externally supplied
`mu`, and `internal` groups whose message is hashed *without* the pure-mode
`(0x00, ctxLen, ctx)` prefix (confirmed against the reference
implementation); those exercise different variants/APIs and are excluded.
They become in-scope when the corresponding APIs are added.

## Regenerating

```sh
# from the ACVP-Server repo (or via raw.githubusercontent.com), place in /tmp/acvp:
#   ML-DSA-{keyGen,sigGen,sigVer}-FIPS204-{prompt,expectedResults}.json
python3 extract_acvp.py /tmp/acvp .
```

The extractor keeps the committed payload small (~2.6 MB) by capping
per-group selections; edit the `cap`/`pos` filters to embed more (or all)
vectors. The full official datasets are ~9 MB.
