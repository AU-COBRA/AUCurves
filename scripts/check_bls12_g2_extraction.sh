#!/usr/bin/env bash
#
# Byte-identical regeneration check for
# bls12-381-safe-rust/src/g2_extracted.rs (sibling of
# check_bls12_extraction.sh, which checks the tower).
# Exit 0 iff the regenerated file equals the committed one.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
TMPRS=$(mktemp /tmp/g2_regen.XXXXXX.rs)
trap 'rm -f "$TMPRS"' EXIT
bash scripts/emit_bls12_g2_rust.sh "$TMPRS"
COMMITTED="$ROOT/bls12-381-safe-rust/src/g2_extracted.rs"
if cmp -s "$TMPRS" "$COMMITTED"; then
  echo "[OK] Regenerated g2_extracted.rs matches the committed file byte for byte."
else
  echo "[FAIL] Regenerated g2_extracted.rs differs from $COMMITTED"
  diff "$TMPRS" "$COMMITTED" | head -40
  exit 1
fi
# The constant-time functions: no branch, loops on counters only.
bash scripts/check_ct_emitted.sh "$COMMITTED" g2_scalar_mul_ct ct_cswap \
  g2_curve_add g2_curve_double_ip bls12_Fp2_three_b
