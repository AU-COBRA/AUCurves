#!/bin/bash
# Build the per-curve OCaml drivers.
#
# Run after `dune build src/Bedrock/Jasmin/extractions/<curve>.vo` produces
# the *_jasmin_extracted.ml files in _build/default/.
#
# Usage:
#   ./build_drivers.sh bls12       # builds bls12_main
#   ./build_drivers.sh x25519_64   # builds x25519_64_main
#   ./build_drivers.sh all         # builds both
set -e

CURVE="${1:-all}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
BUILD_DIR="$(cd "$SCRIPT_DIR/../../../.." && pwd)/_build/default"
EXTRACTED_DIR="$BUILD_DIR/src/Bedrock/Jasmin/extractions"
OUT_DIR="${OUT_DIR:-/tmp}"

build_one () {
  local curve="$1"
  local extracted_ml=""
  case "$curve" in
    bls12)
      extracted_ml="bls12_jasmin_extracted.ml"
      ;;
    x25519_64)
      extracted_ml="x25519_64_jasmin_extracted.ml"
      # X25519 driver also needs bls12_jasmin_extracted.ml (Obj.magic source type)
      ;;
    *) echo "unknown curve: $curve"; exit 2 ;;
  esac

  echo "[$curve] building driver..."
  cd "$SCRIPT_DIR"

  # Dependencies in order
  local deps=()
  if [ -f "$EXTRACTED_DIR/$extracted_ml" ]; then
    deps+=("$EXTRACTED_DIR/$extracted_ml")
  else
    echo "  ERROR: $extracted_ml not found in $EXTRACTED_DIR"
    echo "  Run: dune build src/Bedrock/Jasmin/extractions/${curve^^}.vo"
    return 1
  fi

  if [ "$curve" = "x25519_64" ]; then
    deps+=("$EXTRACTED_DIR/bls12_jasmin_extracted.ml")
  fi

  ocamlfind ocamlopt -package jasmin -linkpkg \
    "${deps[@]}" \
    ocaml_compile.ml \
    "${curve}_main.ml" \
    -o "$OUT_DIR/${curve}_main"
  echo "[$curve] built $OUT_DIR/${curve}_main"
}

case "$CURVE" in
  all)
    build_one bls12
    build_one x25519_64
    ;;
  *)
    build_one "$CURVE"
    ;;
esac
