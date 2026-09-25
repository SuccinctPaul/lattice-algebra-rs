#!/bin/bash
# Integration gate for the §1 comparison-table objective.
# Distinguishes a BLOCKED tree from a genuinely failing scheme: during concurrent
# work a broken lib makes every example fail, and recording those 14 as failures
# misreports good work as bad.
cd /Users/paul/zkp/lattice_based/lattice-algebra-rs || exit 2

echo "== 1. lib must compile =="
if ! cargo check -p lattice-zk --lib --message-format=short 2>/tmp/gate_lib.err; then
  echo "TREE BLOCKED — lib does not compile; per-scheme results below would be meaningless."
  grep -E ": error" /tmp/gate_lib.err | sed 's|crates/zk/src/||' | cut -c1-100 | head -10
  echo "owning files: $(grep -oE '^[^ ]+\.rs' /tmp/gate_lib.err | sed 's|.*/||' | sort -u | tr '\n' ' ')"
  exit 3
fi
echo "lib OK"

echo
echo "== 2. per-scheme examples (one row per §1 scheme) =="
declare -A EX=( [Greyhound]=greyhound_pcs [LaBRADOR]=labrador [CMNW]=cmnw [CELPC]=celpc \
  [Rinocchio]=rinocchio [Orbweaver]=orbweaver [Hachi]=hachi [Jindo]=jindo [Maltese]=maltese \
  [GrandDanois]=grand_danois [Serval]=serval [Akita]=akita [SLAP]=slap [FMN]=fmn )
ORDER=(Greyhound LaBRADOR CMNW CELPC Rinocchio Orbweaver Hachi Jindo Maltese GrandDanois Serval Akita SLAP FMN)
pass=0; fail=0
for s in "${ORDER[@]}"; do
  x=${EX[$s]}
  if [ ! -f "crates/zk/examples/$x.rs" ]; then echo "MISSING  $s (no examples/$x.rs)"; fail=$((fail+1)); continue; fi
  # Maltese's shape is forced by its own arithmetic (b = 2 needs k ≥ 7 before the
  # folding cycle shrinks, so ℓ = 8 and every verifier touches a 2^15-entry êq
  # table): measured 2026-09-24, cycle assembly 84.3 s debug vs 10.0 s optimized,
  # and the 30-case battery scales with it. Run that one in release.
  prof=""
  [ "$x" = maltese ] && prof="--release"
  if cargo run -q $prof -p lattice-zk --example "$x" > /tmp/gate_$x.out 2>&1; then
    printf "PASS     %-12s %s\n" "$s" "$(grep -iE 'bytes|verifies|rejected|total' /tmp/gate_$x.out | tail -1 | cut -c1-100)"
    pass=$((pass+1))
  else
    printf "FAIL     %-12s %s\n" "$s" "$(grep -m1 -E '^error|panicked' /tmp/gate_$x.out | cut -c1-100)"
    fail=$((fail+1))
  fi
done
echo "examples: $pass PASS / $fail FAIL of 14"

echo
echo "== 3. lib + integration tests =="
# Sum every test binary's tally: `tail -1` reports only the last binary, which is
# how this script once printed "7 passed" for a workspace run of a thousand tests.
tally() {
  awk '/^test result/{p+=$4; f+=$6} END{printf "passed %d / failed %d across %d binaries\n", p, f, NR}'
}
cargo test -p lattice-zk --lib --no-fail-fast --message-format=short 2>&1 | grep -E "^test result" | tally
cargo test -p lattice-zk --test protocol_contract 2>&1 | grep -E "^test result" | tally

echo
echo "== 4. feature lanes CI runs =="
for f in "--features simd" "--features parallel" "--no-default-features" ""; do
  if cargo check -p lattice-zk --lib $f --message-format=short >/tmp/gate_f.log 2>&1; then
    echo "OK    cargo check -p lattice-zk --lib $f"
  else
    echo "FAIL  cargo check -p lattice-zk --lib $f  -> $(grep -cE ': error' /tmp/gate_f.log) errors"
  fi
done

echo
echo "== 5. workspace-wide =="
cargo test --workspace --no-fail-fast --message-format=short 2>&1 | grep -E "^test result|^error" | tee /tmp/gate_ws.log | tally
grep -c "^error" /tmp/gate_ws.log | sed 's/^/compile-error lines: /'

echo
echo "== 6. clippy (advisory) =="
cargo clippy -p lattice-zk --lib --message-format=short 2>&1 | grep -cE ": warning" | sed 's/^/warnings: /'
