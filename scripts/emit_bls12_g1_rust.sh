#!/usr/bin/env bash
#
# Emit bls12-381-safe-rust/src/g1_msm_extracted.rs from the bedrock2
# functions listed in src/Bedrock/BLS12_G1ArenaRust.v (Pippenger MSM
# msm_bls12, scalar multiplication g1_scalar_mul, RCB complete addition
# and doubling, store_zero, the 3b loader, felem_copy, two copy-out
# wrappers), printed by
# src/Bedrock/ToSafeRustArena.v.
#
#   scripts/emit_bls12_g1_rust.sh [OUT.rs]
#
# Default OUT: bls12-381-safe-rust/src/g1_msm_extracted.rs.
# Uses the rocq/dune on PATH; falls back to `opam env` when rocq is not
# on PATH.
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
OUT="${1:-$ROOT/bls12-381-safe-rust/src/g1_msm_extracted.rs}"
if ! command -v rocq >/dev/null 2>&1; then
  eval "$(opam env --switch=rocq-9 --set-switch)"
fi
ulimit -s unlimited 2>/dev/null || true

echo "[1/3] dune build src/Bedrock/BLS12_G1ArenaRust.vo"
dune build -j2 src/Bedrock/BLS12_G1ArenaRust.vo

echo "[2/3] Printing bls12_g1_rs"
TMP=$(mktemp -d /tmp/bls12_g1_emit.XXXXXX)
trap 'rm -rf "$TMP"' EXIT
cp scripts/EmitBLS12G1Rust.v "$TMP/"
( cd "$TMP" && rocq compile -R "$ROOT/_build/default/src" "" \
    -Q "$ROOT/_build/default/fiat-crypto/src" Crypto \
    -w -all -native-compiler no EmitBLS12G1Rust.v )

echo "[3/3] Stripping the Rocq string quoting"
python3 scripts/strip_rocq_string.py "$TMP/bls12_g1.out" "$OUT"
