#!/usr/bin/env python3
"""Extract Streamlined NTRU Prime round-3 KAT vectors into a JSON fixture.

Source: the NIST PQC round-3 NTRU Prime submission package
(NTRU-Prime-Round3.zip), directory `ntruprime-20201007/KAT/kem/`:
`sntrup{653,761,857,953,1013,1277}/kat_kem.rsp`. The 653 and 1013 sizes
carry no official KAT files in the round-3 package (the KAT directory
covers 761/857/953/1277) and are not extracted here.

We keep the first PER_SET tests per parameter set; the KAT driver is
deterministic (Bassham AES-256-CTR DRBG seeded per count -> keygen
urandom32 stream -> rho -> encapsulation urandom32 stream), so a handful
of byte-exact bundles catch divergence. The Rust harness re-derives the
DRBG outputs (tests/common/mod.rs) and drives keygen/encapsulate with
them — matching ntruprime's kat_kem.c exactly.

Usage: python3 extract_sntrup_kat.py <dir-with-set-subdirs> <output-dir>
"""
import json
import sys
from pathlib import Path

SETS = ["sntrup761", "sntrup857", "sntrup953", "sntrup1277"]
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
    for set_name in SETS:
        rsp = src_dir / set_name / "kat_kem.rsp"
        for case in parse_rsp(rsp)[:PER_SET]:
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
            "source": "NIST PQC round-3 submission package (NTRU-Prime-Round3.zip), "
            "ntruprime-20201007/KAT/kem/sntrup{761,857,953,1277}/kat_kem.rsp",
            "note": f"first {PER_SET} tests per parameter set; full official files have "
            "100 tests each (the package carries no official KAT for the 653/1013 "
            "sizes). KAT randomness is the Bassham AES-256-CTR DRBG seeded per "
            "count: keygen consumes p 4-byte urandom32 draws for g, then p for f, "
            "then one (p+3)/4-byte rho draw; encapsulation consumes p 4-byte draws "
            "for r (see tests/common/mod.rs).",
        },
        "testCases": test_cases,
    }
    out = out_dir / "sntrup-kat.json"
    out.write_text(json.dumps(doc, indent=2) + "\n")
    print(f"wrote {out} ({len(test_cases)} cases)")


if __name__ == "__main__":
    main()
