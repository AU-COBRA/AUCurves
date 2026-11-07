#!/usr/bin/env bash
#
# Structural constant-time check of emitted Rust functions:
#   scripts/check_ct_emitted.sh FILE.rs FN...
# For each FN, the body of `pub fn FN(` in FILE.rs must contain no `if`,
# no `match`, no `else`, and its only `while` conditions must be the
# counters `v_i != 0` (scalar bit loop) and
# `((v__gs_from0 < v__gs_to0) as u64) != 0` (ct_cswap word loop).
# This re-checks, on the printed text, the property stated in
# src/Bedrock/BLS12_G1_ScalarMulCT.v; it is a syntactic check, not a proof.
set -euo pipefail
FILE="$1"; shift
fail=0
for fn in "$@"; do
  body=$(awk -v f="pub fn $fn(" 'index($0, f) == 1 {p = 1} p {print} p && /^}/ {exit}' "$FILE")
  if [ -z "$body" ]; then echo "[FAIL] $fn not found in $FILE"; fail=1; continue; fi
  if grep -nE '(^|[^a-z_])(if|match|else)([^a-z_]|$)' <<<"$body"; then
    echo "[FAIL] $fn: branch keyword in body"; fail=1
  fi
  bad=$(grep -E '^\s*while ' <<<"$body" | grep -vE '^\s*while v_i != 0 \{$|^\s*while \(\(v__gs_from0 < v__gs_to0\) as u64\) != 0 \{$' || true)
  if [ -n "$bad" ]; then echo "[FAIL] $fn: unexpected loop condition: $bad"; fail=1; fi
  [ $fail -eq 0 ] && echo "[OK] $fn: no branch, loop conditions on counters only"
done
exit $fail
