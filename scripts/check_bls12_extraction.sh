#!/usr/bin/env bash
#
# Bit-exact verification of the BLS12-381 safe-Rust tower extraction.
#
# 1. Build BLS12_Pairing.vo (the source of bls12_all_pairing_funcs).
# 2. Compile ExtractSafeTowerBLS12.v manually (excluded from dune
#    because it runs Coq's Extraction "..." command at compile time).
# 3. Build the OCaml driver from extracted .ml.
# 4. Run the driver, write to a temp file.
# 5. diff -q against bls12-381-safe-rust/generated/bls12_safe_tower.rs.
#
# Exits 0 iff the regenerated tower matches the committed file byte
# for byte.

set -euo pipefail

cd "$(dirname "$0")/.."
ROOT="$PWD"

eval "$(opam env --switch=rocq-9 --set-switch)"

ulimit -s unlimited
export OCAMLRUNPARAM="b,l=1000000000"

echo "[1/4] Building BLS12_Pairing.vo (cached if up-to-date)"
stdbuf -oL -eL dune build src/Bedrock/Field/Synthesis/Examples/BLS12_Pairing.vo

echo "[2/4] Re-extracting bls12_rust_extracted.{ml,mli}"
# ExtractSafeTowerBLS12.v is dune-excluded; invoke rocq compile by hand
rocq compile \
  -R _build/default/src "" \
  -Q _build/default/fiat-crypto/src Crypto \
  -w -all -native-compiler ondemand \
  src/Bedrock/ExtractSafeTowerBLS12.v

echo "[3/4] Compiling OCaml driver"
cd src/Bedrock
rm -f bls12_rust_extracted.cmi bls12_rust_extracted.cmx \
      bls12_rust_extracted.o bls12_safe_tower_main \
      bls12_safe_tower_main.cmi bls12_safe_tower_main.cmx \
      bls12_safe_tower_main.o
ocamlfind ocamlopt -c bls12_rust_extracted.mli
ocamlfind ocamlopt -c bls12_rust_extracted.ml
ocamlfind ocamlopt bls12_rust_extracted.cmx bls12_safe_tower_main.ml \
  -o bls12_safe_tower_main

echo "[4/4] Running driver and diffing against committed .rs"
TMPRS=$(mktemp /tmp/bls12_safe_tower_regen.XXXXXX.rs)
trap 'rm -f "$TMPRS"' EXIT
./bls12_safe_tower_main "$TMPRS"

COMMITTED="$ROOT/bls12-381-safe-rust/generated/bls12_safe_tower.rs"
if diff -q "$TMPRS" "$COMMITTED" >/dev/null; then
  echo "[OK] Regenerated tower matches committed bls12_safe_tower.rs byte for byte."
  exit 0
else
  echo "[FAIL] Regenerated tower differs from committed file."
  echo "       Committed:    $COMMITTED"
  echo "       Regenerated:  $TMPRS"
  echo "       Run:  diff $TMPRS $COMMITTED"
  exit 1
fi
