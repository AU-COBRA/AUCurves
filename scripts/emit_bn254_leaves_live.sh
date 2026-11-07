#!/usr/bin/env bash
#
# Emit bn254-safe-rust/generated/bn254_leaves_live.jazz: the BN254 Fp
# leaves (add, sub, mul, square, select_znz, felem_copy) through
# Core.tr_func_sized 4 / AdcChain.polish_func_adc / CtSelect.ct_func (no
# branch left), printed by SpillLiveness.pp_module_live_b (liveness-chosen
# #[spill] hints) at the budget bn254_leaf_ct_budget, the functions
# bn254_leaves_jasmin_ct of src/Bedrock/Jasmin/ExtractBN254LeavesLive.v.
#
#   scripts/emit_bn254_leaves_live.sh [OUT.jazz]
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
OUT="${1:-$ROOT/bn254-safe-rust/generated/bn254_leaves_live.jazz}"
if ! command -v rocq >/dev/null 2>&1; then
  eval "$(opam env --switch=rocq-9 --set-switch)"
fi
ulimit -s unlimited 2>/dev/null || true

echo "[1/3] dune build src/Bedrock/Jasmin/ExtractBN254LeavesLive.vo"
dune build -j2 src/Bedrock/Jasmin/ExtractBN254LeavesLive.vo

echo "[2/3] Printing pp_module_live_b bn254_leaf_ct_budget bn254_leaves_jasmin_ct"
TMP=$(mktemp -d /tmp/bn254_leaves_live.XXXXXX)
trap 'rm -rf "$TMP"' EXIT
cp scripts/EmitBN254LeavesLive.v "$TMP/"
( cd "$TMP" && rocq compile -R "$ROOT/_build/default/src" "" \
    -Q "$ROOT/_build/default/fiat-crypto/src" Crypto \
    -w -all -native-compiler no EmitBN254LeavesLive.v )

echo "[3/3] Stripping the Rocq string quoting"
python3 scripts/strip_rocq_string.py "$TMP/bn254_leaves_live.out" "$OUT"
