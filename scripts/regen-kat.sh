#!/usr/bin/env bash
# Regenerate every committed KAT/ACVP fixture in crates/pqc/tests/data from
# the official NIST sources, end to end:
#
#   1. round-3 submission packages (Falcon / FrodoKEM / NTRU / NTRU Prime)
#      from csrc.nist.gov;
#   2. ACVP-Server sample vectors (ML-DSA / ML-KEM) from the revision pinned
#      in tests/data/README.md.
#
# Each extractor rewrites only its own fixture, so the pipeline is
# re-runnable at any time; afterwards `make test` (or the kat test filter)
# proves the implementation still matches byte-for-byte.
#
# Usage: scripts/regen-kat.sh [--skip-download] [--only <suite>]
#        suites: falcon frodo ntru sntrup acvp-mldsa acvp-mlkem
set -euo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
DATA_DIR="$REPO_ROOT/crates/pqc/tests/data"
SCRATCH="${TMPDIR:-/tmp}/lattice-kat-regen"
# ACVP-Server revision pinned in tests/data/README.md (provenance).
ACVP_REV="975de31eb83d87039ec88934fdc47d8c312b892d"
ACVP_RAW="https://raw.githubusercontent.com/usnistgov/ACVP-Server/$ACVP_REV/gen-val/json-files"
ROUND3="https://csrc.nist.gov/CSRC/media/Projects/post-quantum-cryptography/documents/round-3/submissions"

SKIP_DOWNLOAD=0
ONLY="all"
while [[ $# -gt 0 ]]; do
  case "$1" in
    --skip-download) SKIP_DOWNLOAD=1; shift ;;
    --only) ONLY="${2:?--only requires a suite name}"; shift 2 ;;
    --only=*) ONLY="${1#--only=}"; shift ;;
    *) echo "unknown arg: $1" >&2; exit 2 ;;
  esac
done

want() { [[ "$ONLY" == "all" || "$ONLY" == "$1" ]]; }

fetch() { # fetch <url> <dest>
  echo "  GET $1"
  curl -sSL --fail --max-time 600 -o "$2" "$1"
}

# ---------------------------------------------------------------------------
# Round-3 submission packages: <package>.zip → per-suite .rsp files.
# ---------------------------------------------------------------------------
declare -A RSP_SRC   # suite -> source .rsp paths inside the unpacked tree
declare -a PACKAGES=(
  "Falcon|Falcon-Round3.zip|falcon"
  "FrodoKEM|FrodoKEM-Round3.zip|frodo"
  "NTRU|NTRU-Round3.zip|ntru"
  "NTRU-Prime|NTRU-Prime-Round3.zip|sntrup"
)

collect_rsp() { # collect_rsp <unpacked-root> <dest-dir> <glob...>
  local root="$1" dest="$2"; shift 2
  local found=0
  for glob in "$@"; do
    while IFS= read -r -d '' f; do
      cp "$f" "$dest/$(basename "$f")"
      found=1
    done < <(find "$root" -type f -path "$glob" -print0)
  done
  return "$found"
}

download_round3() {
  mkdir -p "$SCRATCH"
  for entry in "${PACKAGES[@]}"; do
    IFS='|' read -r name zip suite <<< "$entry"
    want "$suite" || continue
    local dir="$SCRATCH/${suite}"
    mkdir -p "$dir/pkg" "$dir"
    if [[ -s "$dir/pkg/${zip}" ]]; then
      echo "• $name package cached at $dir/pkg/${zip}"
    else
      echo "• downloading $name round-3 package"
      fetch "$ROUND3/${zip}" "$dir/pkg/${zip}"
    fi
    echo "  unpacking ${zip}"
    unzip -qo "$dir/pkg/${zip}" -d "$dir/pkg/unpacked"
  done
}

prepare_rsp() {
  local suite="$1"; shift
  local dir="$SCRATCH/${suite}"
  echo "• collecting $suite KAT .rsp files"
  case "$suite" in
    falcon)
      find "$dir/pkg/unpacked" -type f \( \
        -name 'falcon512-KAT.rsp' -o -name 'falcon1024-KAT.rsp' \) \
        -exec cp {} "$dir/" \;
      ;;
    frodo)
      find "$dir/pkg/unpacked" -type f -name 'PQCkemKAT_*.rsp' \
        -exec cp {} "$dir/" \;
      ;;
    ntru)
      # Official round-3 KATs: hps2048677 / hps4096821 / hrss701 (the
      # directory also carries a round-2 hps2048509 leftover — skipped).
      for set in ntruhps2048677 ntruhps4096821 ntruhrss701; do
        find "$dir/pkg/unpacked" -type f -path "*/KAT/${set}/*.rsp" \
          -exec cp {} "$dir/" \;
      done
      ;;
    sntrup)
      # Official KATs cover sntrup761/857/953/1277 (653/1013 ship none).
      for set in sntrup761 sntrup857 sntrup953 sntrup1277; do
        find "$dir/pkg/unpacked" -type f -path "*/KAT/kem/${set}/*.rsp" \
          -exec cp {} "$dir/" \;
      done
      ;;
  esac
}

# ---------------------------------------------------------------------------
# ACVP-Server sample vectors: <dir>/{prompt,expectedResults}.json →
# <dir>-{prompt,expectedResults}.json in one flat scratch dir.
# ---------------------------------------------------------------------------
ACVP_DIRS=(
  ML-DSA-keyGen-FIPS204  ML-DSA-sigGen-FIPS204   ML-DSA-sigVer-FIPS204
  ML-KEM-keyGen-FIPS203  ML-KEM-encapDecap-FIPS203
)

download_acvp() {
  mkdir -p "$SCRATCH/acvp"
  for dir in "${ACVP_DIRS[@]}"; do
    echo "• fetching ACVP $dir @ $ACVP_REV"
    fetch "$ACVP_RAW/$dir/prompt.json"          "$SCRATCH/acvp/$dir-prompt.json"
    fetch "$ACVP_RAW/$dir/expectedResults.json" "$SCRATCH/acvp/$dir-expectedResults.json"
  done
}

# ---------------------------------------------------------------------------
# Extraction
# ---------------------------------------------------------------------------
extract() {
  cd "$DATA_DIR"
  want falcon      && { echo "• extract falcon";  python3 extract_falcon_kat.py "$SCRATCH/falcon" .; }
  want frodo       && { echo "• extract frodo";   python3 extract_frodokem_kat.py "$SCRATCH/frodo" .; }
  want ntru        && { echo "• extract ntru";    python3 extract_ntru_kat.py "$SCRATCH/ntru" .; }
  want sntrup      && { echo "• extract sntrup";  python3 extract_sntrup_kat.py "$SCRATCH/sntrup" .; }
  want acvp-mldsa  && { echo "• extract ML-DSA ACVP"; python3 extract_acvp.py "$SCRATCH/acvp" .; }
  want acvp-mlkem  && { echo "• extract ML-KEM ACVP"; python3 extract_mlkem_acvp.py "$SCRATCH/acvp" .; }
  cd "$REPO_ROOT"
}

# ---------------------------------------------------------------------------
main() {
  if [[ "$SKIP_DOWNLOAD" -eq 0 ]]; then
    download_round3
    download_acvp
  fi
  if [[ "$SKIP_DOWNLOAD" -eq 0 ]]; then
    for entry in "${PACKAGES[@]}"; do
      IFS='|' read -r _ _ suite <<< "$entry"
      want "$suite" && prepare_rsp "$suite"
    done
  fi
  extract
  echo "• fixtures regenerated in $DATA_DIR"
  echo "  verify with: cargo test -p lattice-pqc --test falcon_kat --test frodo_kat --test ntru_kat --test sntrup_kat"
}

main "$@"
