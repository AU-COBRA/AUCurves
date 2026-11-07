#!/usr/bin/env bash
#
# Emit bls12-381-safe-rust/generated/bls12_group_regptr.jazz: the BLS12-381
# G1/G2 group law, scalar multiplications and G1 MSM (bls12_g1_funcs ++
# bls12_g2_funcs and the field functions they call) through
# Core.tr_func_sized 6 / Core.polish_func, printed by
# src/Bedrock/Jasmin/RegPtrSized.v (pp_module_sized) with the configuration
# of src/Bedrock/ExtractBLS12GroupJasmin.v.
#
#   scripts/emit_bls12_group_jasmin.sh [OUT.jazz [VARIANT]]
#
# VARIANT selects the definition printed, bls12_group_jazz_regptr<VARIANT>:
#   ""       mul/square as local functions, liveness hints, direct slices (default)
#   _ffi     the same with mul/square through #randombytes (CryptOpt or the live leaves)
#   _pr20    the configuration of PR #20
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
OUT="${1:-$ROOT/bls12-381-safe-rust/generated/bls12_group_regptr.jazz}"
VARIANT="${2:-}"
if ! command -v rocq >/dev/null 2>&1; then
  eval "$(opam env --switch=rocq-9 --set-switch)"
fi
ulimit -s unlimited 2>/dev/null || true

echo "[1/3] dune build src/Bedrock/ExtractBLS12GroupJasmin.vo"
dune build -j2 src/Bedrock/ExtractBLS12GroupJasmin.vo

echo "[2/3] Printing bls12_group_jazz_regptr"
TMP=$(mktemp -d /tmp/bls12_group_jasmin.XXXXXX)
trap 'rm -rf "$TMP"' EXIT
sed -e "s/Eval vm_compute in bls12_group_jazz_regptr\./Eval vm_compute in bls12_group_jazz_regptr$VARIANT./" \
  scripts/EmitBLS12GroupJasmin.v > "$TMP/EmitBLS12GroupJasmin.v"
( cd "$TMP" && rocq compile -R "$ROOT/_build/default/src" "" \
    -Q "$ROOT/_build/default/fiat-crypto/src" Crypto \
    -w -all -native-compiler no EmitBLS12GroupJasmin.v )

echo "[3/3] Stripping the Rocq string quoting"
python3 scripts/strip_rocq_string.py "$TMP/bls12_group_regptr.out" "$OUT"
