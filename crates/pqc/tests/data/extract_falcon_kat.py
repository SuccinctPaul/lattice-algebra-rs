#!/usr/bin/env python3
"""Extract Falcon round-3 KAT vectors into a compact JSON fixture.

Source: the NIST PQC round-3 Falcon submission package (Falcon-Round3.zip),
files `KAT/falcon512-KAT.rsp` and `KAT/falcon1024-KAT.rsp` (100 tests each).
We keep the first 5 tests per parameter set — the suite exercises the whole
keygen/sign/verify pipeline, so a handful of byte-exact bundles suffice to
catch divergence (the KAT driver is deterministic: katrng -> keygen seed ->
nonce -> signing seed).

Usage: python3 extract_falcon_kat.py <dir-with-rsp-files> <output-dir>
"""
import json
import sys
from pathlib import Path

SETS = {
    "falcon512": "falcon512-KAT.rsp",
    "falcon1024": "falcon1024-KAT.rsp",
}
PER_SET = 5


def parse_rsp(path: Path):
    cases = []
    cur = {}
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        key, _, value = line.partition("=")
        cur[key.strip()] = value.strip()
        if key.strip() == "sm":  # last field of a record
            cases.append(cur)
            cur = {}
    return cases


def main() -> None:
    src_dir, out_dir = Path(sys.argv[1]), Path(sys.argv[2])
    test_cases = []
    for set_name, rsp_name in SETS.items():
        for case in parse_rsp(src_dir / rsp_name)[:PER_SET]:
            test_cases.append(
                {
                    "parameterSet": set_name,
                    "count": int(case["count"]),
                    "seed": case["seed"],
                    "mlen": int(case["mlen"]),
                    "msg": case["msg"],
                    "pk": case["pk"],
                    "sk": case["sk"],
                    "smlen": int(case["smlen"]),
                    "sm": case["sm"],
                }
            )
    doc = {
        "_meta": {
            "source": "NIST PQC round-3 submission package (Falcon-Round3.zip), "
            "KAT/falcon{512,1024}-KAT.rsp",
            "note": f"first {PER_SET} tests per parameter set; full official "
            "files have 100 tests each",
        },
        "testCases": test_cases,
    }
    out = out_dir / "falcon-kat.json"
    out.write_text(json.dumps(doc, indent=2) + "\n")
    print(f"wrote {out} ({len(test_cases)} cases)")


if __name__ == "__main__":
    main()
