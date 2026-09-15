#!/usr/bin/env python3
"""Extract FrodoKEM round-3 KAT vectors into a compact JSON fixture.

Source: the NIST PQC round-3 FrodoKEM submission package
(FrodoKEM-Round3.zip), directory `FrodoKEM/FrodoKEM-20200930/KAT/`:
`PQCkemKAT_<sklen>.rsp` (matrix A via AES128) and `PQCkemKAT_<sklen>_shake.rsp`
(matrix A via SHAKE128) for FrodoKEM-640/976/1344 — 100 tests each.

We keep the first PER_SET tests per variant: the KAT driver is deterministic
(Bassham DRBG seeded per count -> keygen draw -> encapsulation mu), so a
handful of byte-exact bundles catch divergence. The Rust harness re-derives
the DRBG outputs (tests/common/drbg.rs) and drives keygen/encapsulate with
them — matching PQCtestKAT_kem.c exactly.

Usage: python3 extract_frodokem_kat.py <dir-with-rsp-files> <output-dir>
"""
import json
import sys
from pathlib import Path

# (parameterSet label, rsp filename, sk length selector)
SETS = [
    ("FrodoKEM-640-AES", "PQCkemKAT_19888.rsp"),
    ("FrodoKEM-640-SHAKE", "PQCkemKAT_19888_shake.rsp"),
    ("FrodoKEM-976-AES", "PQCkemKAT_31296.rsp"),
    ("FrodoKEM-976-SHAKE", "PQCkemKAT_31296_shake.rsp"),
    ("FrodoKEM-1344-AES", "PQCkemKAT_43088.rsp"),
    ("FrodoKEM-1344-SHAKE", "PQCkemKAT_43088_shake.rsp"),
]
PER_SET = 3


def parse_rsp(path: Path):
    cases = []
    cur = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, _, value = line.partition("=")
        cur[key.strip()] = value.strip()
        if key.strip() == "ss":  # last field of a KEM record
            cases.append(cur)
            cur = {}
    return cases


def main() -> None:
    src_dir, out_dir = Path(sys.argv[1]), Path(sys.argv[2])
    test_cases = []
    for set_name, rsp_name in SETS:
        for case in parse_rsp(src_dir / rsp_name)[:PER_SET]:
            test_cases.append(
                {
                    "parameterSet": set_name,
                    "count": int(case["count"]),
                    "seed": case["seed"],
                    "pk": case["pk"],
                    "sk": case["sk"],
                    "ct": case["ct"],
                    "ss": case["ss"],
                }
            )
    doc = {
        "_meta": {
            "source": "NIST PQC round-3 submission package (FrodoKEM-Round3.zip), "
            "FrodoKEM/FrodoKEM-20200930/KAT/PQCkemKAT_*.rsp (AES and _shake "
            "variants)",
            "note": f"first {PER_SET} tests per parameter set/variant; full official "
            "files have 100 tests each. The KAT randomness is the Bassham "
            "AES-256-CTR DRBG seeded per count (see tests/common/drbg.rs); "
            "keygen consumes one 2*SS+16-byte draw, encapsulation one MU-byte draw.",
        },
        "testCases": test_cases,
    }
    out = out_dir / "frodo-kat.json"
    out.write_text(json.dumps(doc, indent=2) + "\n")
    print(f"wrote {out} ({len(test_cases)} cases)")


if __name__ == "__main__":
    main()
