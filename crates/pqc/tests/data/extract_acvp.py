#!/usr/bin/env python3
"""Extract the committed ACVP KAT fixtures for ML-DSA from the official
NIST ACVP-Server sample vectors.

Source of truth
---------------
https://github.com/usnistgov/ACVP-Server — `gen-val/json-files/`:
  ML-DSA-keyGen-FIPS204, ML-DSA-sigGen-FIPS204, ML-DSA-sigVer-FIPS204
Each directory holds `prompt.json` (inputs) and `expectedResults.json`
(outputs), joined by `tgId`/`tcId`.

Usage
-----
    # 1. download the three directories (prompt + expectedResults each)
    #    into a scratch dir, keeping the file names
    #    ML-DSA-<op>-FIPS204-{prompt,expectedResults}.json
    # 2. run:  extract_acvp.py <scratch_dir> <this_dir>

Scope
-----
ML-DSA *pure mode, external interface* — the mode and API this crate
implements (`ML-DSA.Sign/Verify(message, context)`). The ACVP dataset also
contains `preHash` groups (HashML-DSA, `PH(M)` with OID separation),
`internal` groups with an externally supplied `mu`, and `internal` groups
whose message is hashed without the pure-mode `(0x00, ctxLen, ctx)` prefix
(verified against the reference implementation); those exercise different
scheme variants/APIs and are deliberately excluded.

Selection rules (keeps the committed fixtures small while covering every
parameter set, deterministic and randomized signing, and accept+reject
verification):
  - keyGen:   every test (25 per parameter set);
  - sigGen:   first 6 tests of every deterministic pure group and first 3 of
              every randomized pure group (the randomized ones fix `rnd`);
  - sigVer:   first 8 tests of every pure group (accept and reject cases).
"""

import json
import sys
from pathlib import Path


def load(scratch: Path, name: str, part: str):
    return json.loads((scratch / f"ML-DSA-{name}-FIPS204-{part}.json").read_text())


def is_pure_group(g):
    """Pure-mode groups: external interface with preHash='pure', or the
    internal interface without an external mu (message + context inputs)."""
    return (g.get("signatureInterface") == "external"
            and g.get("preHash") == "pure")


def join(prompt, expected, group_filter=None):
    by_tg = {g["tgId"]: g for g in expected["testGroups"]}
    for g in prompt["testGroups"]:
        if group_filter and not group_filter(g):
            continue
        eg = by_tg[g["tgId"]]
        et = {t["tcId"]: t for t in eg["tests"]}
        for pos, t in enumerate(g["tests"]):
            yield g, pos, {**t, **et[t["tcId"]]}


def main(scratch: Path, out: Path) -> None:
    # ---- keyGen: all -----------------------------------------------------
    records = []
    for g, _pos, t in join(load(scratch, "keyGen", "prompt"),
                           load(scratch, "keyGen", "expectedResults")):
        records.append({
            "parameterSet": g["parameterSet"],
            "tcId": t["tcId"],
            "seed": t["seed"],
            "pk": t["pk"],
            "sk": t["sk"],
        })
    keygen = records

    # ---- sigGen: 4 per deterministic group, 2 per randomized group -------
    records = []
    for g, pos, t in join(load(scratch, "sigGen", "prompt"),
                          load(scratch, "sigGen", "expectedResults"),
                          group_filter=is_pure_group):
        cap = 6 if g["deterministic"] else 3
        if pos >= cap:
            continue
        rec = {
            "parameterSet": g["parameterSet"],
            "tcId": t["tcId"],
            "deterministic": g["deterministic"],
            "message": t.get("message", ""),
            "context": t.get("context", ""),
            "sk": t["sk"],
            "signature": t["signature"],
        }
        if not g["deterministic"]:
            rec["rnd"] = t["rnd"]
        records.append(rec)
    siggen = records

    # ---- sigVer: first 6 of every group ----------------------------------
    records = []
    for g, pos, t in join(load(scratch, "sigVer", "prompt"),
                          load(scratch, "sigVer", "expectedResults"),
                          group_filter=is_pure_group):
        if pos >= 8:
            continue
        records.append({
            "parameterSet": g["parameterSet"],
            "tcId": t["tcId"],
            "pk": t["pk"],
            "message": t.get("message", ""),
            "context": t.get("context", ""),
            "signature": t["signature"],
            "testPassed": t["testPassed"],
        })
    sigver = records

    meta = {
        "_meta": {
            "source": "usnistgov/ACVP-Server gen-val/json-files (official ACVP sample vectors)",
            "revision": "master@975de31eb83d87039ec88934fdc47d8c312b892d",
            "fetched": "2026-09-05",
            "algorithm": "ML-DSA (FIPS 204), pure mode, external interface",
            "extractor": "crates/pqc/tests/data/extract_acvp.py",
        }
    }
    for name, data in [("acvp-keygen", keygen), ("acvp-siggen", siggen),
                       ("acvp-sigver", sigver)]:
        doc = {**meta, "testCases": data}
        dest = out / f"{name}.json"
        dest.write_text(json.dumps(doc, indent=1) + "\n")
        print(f"{dest.name}: {len(data)} test cases, {dest.stat().st_size} bytes")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
