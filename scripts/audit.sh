#!/usr/bin/env bash
# Supply-chain and license audit for the workspace.
#
# Wraps cargo-audit (RustSec advisories) and cargo-deny (licenses, bans,
# sources) when either tool is installed, and always runs a plain
# grep-based no-unsafe policy scan. Exits non-zero on failure so it can
# gate CI or release.
#
# Usage: scripts/audit.sh [--strict]
#   default: advisory/deny tools are best-effort — a missing tool or an
#            unreachable advisory-db degrades to a warning (offline runs).
#   --strict: any tool failure fails the audit (CI semantics).
set -euo pipefail

cd "$(dirname "${BASH_SOURCE[0]}")/.."
STRICT=0
[[ "${1:-}" == "--strict" ]] && STRICT=1
RC=0

note_fail() { # note_fail <label>  — degrade unless strict
  if [[ "$STRICT" -eq 1 ]]; then
    echo "  ERROR: $1"; RC=1
  else
    echo "  WARN: $1 (re-run with --strict to fail on this)"
  fi
}

echo "▸ cargo audit (RustSec advisories)"
if command -v cargo-audit >/dev/null 2>&1; then
  if ! cargo audit; then note_fail "cargo audit reported findings or could not fetch the advisory database"; fi
else
  echo "  cargo-audit not installed — skipping (cargo install cargo-audit)"
fi

echo "▸ cargo deny (licenses / bans / sources)"
if command -v cargo-deny >/dev/null 2>&1; then
  if ! cargo deny check; then note_fail "cargo deny reported policy violations or could not fetch"; fi
else
  echo "  cargo-deny not installed — skipping (cargo install cargo-deny)"
fi

echo "▸ duplicate dependency versions"
cargo tree --workspace --duplicates 2>/dev/null | grep -E '^[a-z]' | head -20 \
  && echo "  (informational: duplicates above; revisit on dependency bumps)" \
  || echo "  clean: no duplicated dependency versions"

echo "▸ unsafe code scan (the workspace is no-unsafe by policy)"
if grep -rn --include='*.rs' -E '\bunsafe\s+(fn|impl|\{)' crates/*/src; then
  echo "  ERROR: unsafe block found — the workspace policy forbids it"
  RC=1
else
  echo "  clean: no unsafe blocks in any crate"
fi

exit "$RC"
