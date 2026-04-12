#!/bin/bash
# Phase 3 check: verify that the committed bn254_safe_tower.rs matches
# the output of the Coq-verified btranslate translator.
#
# This script:
# 1. Runs the verified driver (which calls the Coq-extracted btranslate)
# 2. Compares the output against the committed generated .rs
# 3. Fails if they differ
#
# Prerequisites:
#   - bn254_safe_tower_verified binary built (src/Bedrock/)
#   - bn254_rust_extracted.ml up to date (from ExtractSafeRust.v)

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
ROOT="$SCRIPT_DIR/.."
DRIVER="$ROOT/src/Bedrock/bn254_safe_tower_verified"
COMMITTED="$ROOT/bn254-safe-rust/generated/bn254_safe_tower.rs"
TMPFILE="$(mktemp /tmp/bn254_safe_tower_check.XXXXXX.rs)"

trap "rm -f $TMPFILE" EXIT

if [ ! -x "$DRIVER" ]; then
    echo "ERROR: $DRIVER not found. Build it first:"
    echo "  cd src/Bedrock && ocamlfind ocamlopt -package zarith -linkpkg bn254_rust_extracted.ml bn254_safe_tower_verified.ml -o bn254_safe_tower_verified"
    exit 2
fi

echo "[verify_safe_tower] Generating fresh .rs from verified translator..."
"$DRIVER" "$TMPFILE"

echo "[verify_safe_tower] Comparing against committed version..."
if diff -q "$COMMITTED" "$TMPFILE" >/dev/null 2>&1; then
    echo "[verify_safe_tower] PASS: committed .rs matches verified btranslate output"
    exit 0
else
    echo "[verify_safe_tower] FAIL: committed .rs differs from verified output"
    echo "Diff (first 30 lines):"
    diff "$COMMITTED" "$TMPFILE" | head -30
    exit 1
fi
