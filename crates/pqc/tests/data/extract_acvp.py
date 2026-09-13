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
ML-DSA pure mode (external interface, `ML-DSA.Sign/Verify(message, context)`)
plus the internal interfaces added for FIPS 204 §5.4 alignment:

  - pure sigGen/sigVer (external interface, `preHash = "pure"`);
  - internal sigGen/sigVer with an externally supplied `mu` (the
    `Sign_internal`/`Verify_internal` signing-loop primitive — the ACVP
    "external mu" mode), and internal groups without one, whose message
    representative is mu = H(tr ‖ message) with **no** pure-mode
    `(0x00, ctxLen, ctx)` prefix (confirmed against the ACVP-Server
    reference, `Dilithium.Sign(sk, m, rnd)`);
  - preHash sigGen/sigVer (external interface). NOTE: the ACVP dataset's
    preHash mode is the *OID-separated* pre-hash variant — the tested
    construction is M' = 1 ‖ |ctx| ‖ ctx ‖ OID ‖ PH(M) (per the
    ACVP-Server `ExternalSignatureBase.ExternalPreHashSign`), with PH
    output lengths fixed by `ShaAttributes` (digest size for SHA-2/SHA-3,
    256 bits for SHAKE-128, 512 bits for SHAKE-256). That is *not* the
    final FIPS 204 HashML-DSA composition (no OID); the crate exposes the
    final one (`sign_hash_mldsa`/`verify_hash_mldsa`) while the test
    harness composes the ACVP M' via `sign_m_prime`/`verify_m_prime`.

Selection rules (keeps the committed fixtures small while covering every
parameter set, deterministic and randomized signing, and accept+reject
verification):
  - keyGen:         every test (25 per parameter set);
  - sigGen (all):   first 6 tests of every deterministic group and first 3
                    of every randomized group (the randomized ones fix `rnd`);
  - sigVer (all):   first 8 tests of every group (accept and reject cases).
"""

import json
import sys
from pathlib import Path


def load(scratch: Path, name: str, part: str):
    return json.loads((scratch / f"ML-DSA-{name}-FIPS204-{part}.json").read_text())


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

    # ---- sigGen (pure + internal + preHash) ------------------------------
    pure, internal, prehash = [], [], []
    for g, pos, t in join(load(scratch, "sigGen", "prompt"),
                          load(scratch, "sigGen", "expectedResults")):
        is_pure = (g.get("signatureInterface") == "external"
                   and g.get("preHash") == "pure")
        is_prehash = (g.get("signatureInterface") == "external"
                      and g.get("preHash") == "preHash")
        is_internal = g.get("signatureInterface") == "internal"
        if not (is_pure or is_prehash or is_internal):
            continue
        cap = 6 if g["deterministic"] else 3
        if pos >= cap:
            continue
        rec = {
            "parameterSet": g["parameterSet"],
            "tcId": t["tcId"],
            "deterministic": g["deterministic"],
            "sk": t["sk"],
            "signature": t["signature"],
        }
        if not g["deterministic"]:
            rec["rnd"] = t["rnd"]
        if is_pure:
            rec["message"] = t.get("message", "")
            rec["context"] = t.get("context", "")
            pure.append(rec)
        elif is_internal:
            rec["externalMu"] = g["externalMu"]
            if g["externalMu"]:
                rec["mu"] = t["mu"]
            else:
                rec["message"] = t["message"]
            internal.append(rec)
        else:
            rec["hashAlg"] = t["hashAlg"]
            rec["message"] = t["message"]
            rec["context"] = t.get("context", "")
            prehash.append(rec)
    siggen_pure, siggen_internal, siggen_prehash = pure, internal, prehash

    # ---- sigVer (pure + internal + preHash) ------------------------------
    pure, internal, prehash = [], [], []
    for g, pos, t in join(load(scratch, "sigVer", "prompt"),
                          load(scratch, "sigVer", "expectedResults")):
        is_pure = (g.get("signatureInterface") == "external"
                   and g.get("preHash") == "pure")
        is_prehash = (g.get("signatureInterface") == "external"
                      and g.get("preHash") == "preHash")
        is_internal = g.get("signatureInterface") == "internal"
        if not (is_pure or is_prehash or is_internal):
            continue
        if pos >= 8:
            continue
        rec = {
            "parameterSet": g["parameterSet"],
            "tcId": t["tcId"],
            "pk": t["pk"],
            "signature": t["signature"],
            "testPassed": t["testPassed"],
        }
        if is_pure:
            rec["message"] = t.get("message", "")
            rec["context"] = t.get("context", "")
            pure.append(rec)
        elif is_internal:
            rec["externalMu"] = g["externalMu"]
            if g["externalMu"]:
                rec["mu"] = t["mu"]
            else:
                rec["message"] = t["message"]
            internal.append(rec)
        else:
            rec["hashAlg"] = t["hashAlg"]
            rec["message"] = t["message"]
            rec["context"] = t.get("context", "")
            prehash.append(rec)
    sigver_pure, sigver_internal, sigver_prehash = pure, internal, prehash

    meta = {
        "_meta": {
            "source": "usnistgov/ACVP-Server gen-val/json-files (official ACVP sample vectors)",
            "revision": "master@975de31eb83d87039ec88934fdc47d8c312b892d",
            "fetched": "2026-09-14",
            "extractor": "crates/pqc/tests/data/extract_acvp.py",
        }
    }
    files = [
        ("acvp-keygen", keygen, "ML-DSA keyGen (all parameter sets)"),
        ("acvp-siggen", siggen_pure, "ML-DSA sigGen, pure mode (external interface)"),
        ("acvp-siggen-internal", siggen_internal,
         "ML-DSA sigGen, internal interface (external mu and mu = H(tr||M) groups)"),
        ("acvp-siggen-prehash", siggen_prehash,
         "ML-DSA sigGen, external preHash groups (OID-separated M', ACVP draft variant)"),
        ("acvp-sigver", sigver_pure, "ML-DSA sigVer, pure mode (external interface)"),
        ("acvp-sigver-internal", sigver_internal,
         "ML-DSA sigVer, internal interface (external mu and mu = H(tr'||M) groups)"),
        ("acvp-sigver-prehash", sigver_prehash,
         "ML-DSA sigVer, external preHash groups (OID-separated M', ACVP draft variant)"),
    ]
    for name, data, algo in files:
        doc = {**meta, "algorithm": algo, "testCases": data}
        dest = out / f"{name}.json"
        dest.write_text(json.dumps(doc, indent=1) + "\n")
        print(f"{dest.name}: {len(data)} test cases, {dest.stat().st_size} bytes")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
