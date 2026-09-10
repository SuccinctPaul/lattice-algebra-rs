#!/usr/bin/env python3
"""Extract the committed ACVP KAT fixtures for ML-KEM from the official
NIST ACVP-Server sample vectors.

Source of truth
---------------
https://github.com/usnistgov/ACVP-Server — `gen-val/json-files/`:
  ML-KEM-keyGen-FIPS203, ML-KEM-encapDecap-FIPS203
Each directory holds `prompt.json` (inputs) and `expectedResults.json`
(outputs), joined by `tgId`/`tcId`.

Usage
-----
    # 1. download the two directories (prompt + expectedResults each) into
    #    a scratch dir, keeping the file names
    #    ML-KEM-<op>-FIPS203-{prompt,expectedResults}.json
    # 2. run:  extract_mlkem_acvp.py <scratch_dir> <this_dir>

Selection rules (keeps the committed fixtures small while covering every
parameter set, encapsulation, valid decapsulation, implicit rejection and
the optional key checks):
  - keyGen:        every test (25 per parameter set);
  - encapsulation: first 8 tests of every group;
  - decapsulation: first 8 tests of every group;
  - decapsulationKeyCheck / encapsulationKeyCheck: every test (10 per group).
"""

import json
import sys
from pathlib import Path


def load(scratch: Path, name: str, part: str):
    return json.loads((scratch / f"ML-KEM-{name}-FIPS203-{part}.json").read_text())


def join(prompt, expected, group_filter=None):
    by_tg = {g["tgId"]: g for g in expected["testGroups"]}
    for g in prompt["testGroups"]:
        if group_filter and not group_filter(g):
            continue
        eg = by_tg[g["tgId"]]
        et = {t["tcId"]: t for t in eg["tests"]}
        for pos, t in enumerate(g["tests"]):
            yield g, pos, t, et[t["tcId"]]


def main(scratch: Path, out_dir: Path) -> None:
    cases = []

    # keyGen: all tests, all parameter sets.
    kg_prompt = load(scratch, "keyGen", "prompt")
    kg_expected = load(scratch, "keyGen", "expectedResults")
    for g, _, t, e in join(kg_prompt, kg_expected):
        cases.append(
            {
                "kind": "keyGen",
                "parameterSet": g["parameterSet"],
                "tcId": t["tcId"],
                "d": t["d"],
                "z": t["z"],
                "ek": e["ek"],
                "dk": e["dk"],
            }
        )

    ed_prompt = load(scratch, "encapDecap", "prompt")
    ed_expected = load(scratch, "encapDecap", "expectedResults")
    for g, pos, t, e in join(
        ed_prompt,
        ed_expected,
        lambda g: g["function"] == "encapsulation",
    ):
        if pos >= 8:
            continue
        cases.append(
            {
                "kind": "encaps",
                "parameterSet": g["parameterSet"],
                "tcId": t["tcId"],
                "ek": t["ek"],
                "m": t["m"],
                "c": e["c"],
                "k": e["k"],
            }
        )
    for g, pos, t, e in join(
        ed_prompt,
        ed_expected,
        lambda g: g["function"] == "decapsulation",
    ):
        if pos >= 8:
            continue
        cases.append(
            {
                "kind": "decaps",
                "parameterSet": g["parameterSet"],
                "tcId": t["tcId"],
                "dk": t["dk"],
                "c": t["c"],
                "k": e["k"],
            }
        )
    for kind in ("decapsulationKeyCheck", "encapsulationKeyCheck"):
        for g, _, t, e in join(ed_prompt, ed_expected, lambda g: g["function"] == kind):
            cases.append(
                {
                    "kind": "keyCheck",
                    "check": "dk" if kind.startswith("decapsulation") else "ek",
                    "parameterSet": g["parameterSet"],
                    "tcId": t["tcId"],
                    "key": t["dk"] if kind.startswith("decapsulation") else t["ek"],
                    "testPassed": e["testPassed"],
                }
            )

    order = {"keyGen": 0, "encaps": 1, "decaps": 2, "keyCheck": 3}
    cases.sort(key=lambda c: (order[c["kind"]], c["parameterSet"], c["tcId"]))
    doc = {
        "_meta": {
            "source": "https://github.com/usnistgov/ACVP-Server gen-val/json-files/"
            "(ML-KEM-keyGen-FIPS203, ML-KEM-encapDecap-FIPS203)",
            "revision": "master@975de31eb83d87039ec88934fdc47d8c312b892d (fetched 2026-09-11)",
            "selection": "keyGen: all 25/set; encaps+decaps: first 8/set; "
            "keyCheck: all",
        },
        "testCases": cases,
    }
    out = out_dir / "acvp-mlkem.json"
    out.write_text(json.dumps(doc, indent=1))
    kinds = {}
    for c in cases:
        kinds[c["kind"]] = kinds.get(c["kind"], 0) + 1
    print(f"wrote {out} ({out.stat().st_size} bytes): {kinds}")


if __name__ == "__main__":
    main(Path(sys.argv[1]), Path(sys.argv[2]))
