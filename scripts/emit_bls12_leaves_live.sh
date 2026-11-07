#!/usr/bin/env bash
#
# Emit bls12-381-safe-rust/generated/bls12_leaves_live.jazz: the BLS12-381 Fp
# leaves (add, sub, mul, square, select_znz, felem_copy) through
# Core.tr_func_sized 6 / AdcChain.polish_func_adc / CtSelect.ct_func (no
# branch left), printed by SpillLiveness.pp_module_live_b (liveness-chosen
# #[spill] hints) at the budget bls12_leaf_ct_budget, the functions
# bls12_leaves_jasmin_ct of src/Bedrock/Jasmin/ExtractBLS12LeavesLive.v.
#
#   scripts/emit_bls12_leaves_live.sh [OUT.jazz]
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
OUT="${1:-$ROOT/bls12-381-safe-rust/generated/bls12_leaves_live.jazz}"
if ! command -v rocq >/dev/null 2>&1; then
  eval "$(opam env --switch=rocq-9 --set-switch)"
fi
ulimit -s unlimited 2>/dev/null || true

echo "[1/3] dune build src/Bedrock/Jasmin/ExtractBLS12LeavesLive.vo"
dune build -j2 src/Bedrock/Jasmin/ExtractBLS12LeavesLive.vo

echo "[2/3] Printing pp_module_live_b bls12_leaf_ct_budget bls12_leaves_jasmin_ct"
TMP=$(mktemp -d /tmp/bls12_leaves_live.XXXXXX)
trap 'rm -rf "$TMP"' EXIT
cp scripts/EmitBLS12LeavesLive.v "$TMP/"
( cd "$TMP" && rocq compile -R "$ROOT/_build/default/src" "" \
    -Q "$ROOT/_build/default/fiat-crypto/src" Crypto \
    -w -all -native-compiler no EmitBLS12LeavesLive.v )

echo "[3/3] Stripping the Rocq string quoting"
python3 scripts/strip_rocq_string.py "$TMP/bls12_leaves_live.out" "$OUT"
