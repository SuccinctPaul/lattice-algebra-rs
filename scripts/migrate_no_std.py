#!/usr/bin/env python3
"""One-shot no_std import migration for the lattice-algebra-rs workspace.

Two line-local rewrites, no multiline matching:
  1. `use std::<X>` / inline `std::<prefix>..` -> `core::` for a fixed list of
     prefixes that exist in core. `std::time::`, `std::panic::` and friends are
     deliberately NOT rewritten: they live in `#[cfg(test)]` code, where the
     crate roots pull `extern crate std`.
  2. Insert `use alloc::{..}` for the heap names a file mentions (Vec, vec!,
     format!, String), before the first line of real code so that inner
     attributes and `//!` doc comments stay at the top.

Idempotent: a file that already has the alloc line is skipped.
"""
import re
import sys

# prefixes that exist under `core::` with the same path
CORE_PREFIXES = [
    "array", "cmp", "clone", "convert", "default", "error", "fmt", "hash",
    "iter", "marker", "mem", "ops", "ptr", "slice", "f64", "f32", "u64", "u32",
]
PREFIX_RE = re.compile(r"\bstd::(" + "|".join(CORE_PREFIXES) + r")::")

# which alloc import each token requires
NEEDS = [
    (re.compile(r"\bVec\b"), "vec::Vec"),
    (re.compile(r"\bvec!\s*[\[(]"), "vec"),
    (re.compile(r"\bformat!\s*[(]"), "format"),
    (re.compile(r"(?<![\w.])String\b"), "string::String"),
]


def first_code_line(lines):
    for i, line in enumerate(lines):
        s = line.strip()
        if not s:
            continue
        if s.startswith("//!") or s.startswith("#!["):
            continue
        return i
    return 0


def migrate(path):
    with open(path, encoding="utf-8") as fh:
        src = fh.read()
    original = src

    src = PREFIX_RE.sub(r"core::\1::", src)
    # Only `use std::<something that also lives in core>`. A blanket rewrite
    # here would silently corrupt the deliberate `use std::println;` that test
    # modules need.
    src = re.sub(
        r"^(\s*(?:pub )?)use std::(" + "|".join(CORE_PREFIXES) + r")",
        r"\1use core::\2",
        src,
        flags=re.M,
    )

    lines = src.split("\n")
    used = {item for rx, item in NEEDS if rx.search(src)}
    if used:
        stmt = "use alloc::{" + ", ".join(sorted(used)) + "};"
        if stmt not in src:
            at = first_code_line(lines)
            lines.insert(at, stmt)
    src = "\n".join(lines)

    if src != original:
        with open(path, "w", encoding="utf-8") as fh:
            fh.write(src)
        return True
    return False


def main(paths):
    # paths given as a newline-separated file on argv[1]
    with open(paths, encoding="utf-8") as fh:
        files = [l.strip() for l in fh if l.strip() and not l.startswith("#")]
    changed = 0
    for f in files:
        if migrate(f):
            changed += 1
            print(f"migrated {f}")
    print(f"{changed}/{len(files)} files changed")


if __name__ == "__main__":
    main(sys.argv[1])
