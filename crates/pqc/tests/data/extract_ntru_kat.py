#!/usr/bin/env python3
"""Extract NTRU round-3 KAT vectors into a compact JSON fixture.

Source: the NIST PQC round-3 NTRU submission package (NTRU-Round3.zip),
directory `NIST-PQ-Submission-NTRU-20201016/KAT/`: `ntruhps2048677/
PQCkemKAT_1234.rsp`, `ntruhps4096821/PQCkemKAT_1590.rsp` and
`ntruhrss701/PQCkemKAT_1450.rsp` — 100 tests each. (The KAT directory also
carries a round-2 leftover for ntruhps2048509, which is not a round-3
parameter set and is not extracted.)

We keep the first PER_SET tests per parameter set; the KAT driver is
deterministic (Bassham AES-256-CTR DRBG seeded per count -> keygen draw ->
PRF key -> encapsulation draw), so a handful of byte-exact bundles catch
divergence. The Rust harness re-derives the DRBG outputs
(tests/common/mod.rs) and drives keygen/encapsulate with them — matching
PQCgenKAT_kem.c exactly.

Usage: python3 extract_ntru_kat.py <dir-with-param-subdirs> <output-dir>
"""
import json
import sys
from pathlib import Path

SETS = [
    ("ntruhps2048677", "ntruhps2048677/PQCkemKAT_1234.rsp"),
    ("ntruhps4096821", "ntruhps4096821/PQCkemKAT_1590.rsp"),
    ("ntruhrss701", "ntruhrss701/PQCkemKAT_1450.rsp"),
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
    for set_name, rel in SETS:
        for case in parse_rsp(src_dir / rel)[:PER_SET]:
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
            "source": "NIST PQC round-3 submission package (NTRU-Round3.zip), "
            "NIST-PQ-Submission-NTRU-20201016/KAT/{ntruhps2048677,ntruhps4096821,"
            "ntruhrss701}/PQCkemKAT_*.rsp",
            "note": f"first {PER_SET} tests per parameter set; full official files "
            "have 100 tests each. KAT randomness is the Bassham AES-256-CTR "
            "DRBG seeded per count: keypair draws SAMPLE_FG_BYTES then a "
            "32-byte PRF key, encapsulation draws SAMPLE_RM_BYTES "
            "(see tests/common/mod.rs).",
        },
        "testCases": test_cases,
    }
    out = out_dir / "ntru-kat.json"
    out.write_text(json.dumps(doc, indent=2) + "\n")
    print(f"wrote {out} ({len(test_cases)} cases)")


if __name__ == "__main__":
    main()
