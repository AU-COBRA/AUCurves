#!/usr/bin/env bash
#
# Generate the verified MSM safe-Rust from the bedrock2 msm_bls12 program.
#
# 1. Build BLS12_MSM_Extract.vo (already dune-built via the main tree).
# 2. Compile the OCaml driver.
# 3. Run it, emitting bls12-jasmin-rs/src/msm_extracted.rs.
#
# Exit 0 iff the .rs file is produced and non-empty.

set -euo pipefail

cd "$(dirname "$0")/.."
ROOT="$PWD"

eval "$(opam env --switch=rocq-native --set-switch)"

ulimit -s unlimited
export OCAMLRUNPARAM="b,l=1000000000"

echo "[1/3] Building BLS12_MSM_Extract.vo (cached if up-to-date)"
stdbuf -oL -eL dune build src/Bedrock/BLS12_MSM_Extract.vo

echo "[2/3] Compiling OCaml driver"
cd src/Bedrock
# Refresh extracted .ml/.mli from the build artefact (dune drops them in
# _build/default/src/Bedrock/, but the ocamlfind build expects them here).
cp ../../_build/default/src/Bedrock/bls12_msm_extracted.ml .
cp ../../_build/default/src/Bedrock/bls12_msm_extracted.mli .

rm -f bls12_msm_extracted.cmi bls12_msm_extracted.cmx \
      bls12_msm_extracted.o bls12_msm_main \
      bls12_msm_main.cmi bls12_msm_main.cmx bls12_msm_main.o

ocamlfind ocamlopt -c bls12_msm_extracted.mli
ocamlfind ocamlopt -c bls12_msm_extracted.ml
ocamlfind ocamlopt bls12_msm_extracted.cmx bls12_msm_main.ml \
  -o bls12_msm_main

echo "[3/3] Running driver"
OUT="$ROOT/../bls12-jasmin-rs/src/msm_extracted.rs"
./bls12_msm_main "$OUT"

if [ -s "$OUT" ]; then
  echo "[OK] Wrote $(wc -c < "$OUT") bytes to $OUT"
else
  echo "[FAIL] $OUT empty or missing"; exit 1
fi
