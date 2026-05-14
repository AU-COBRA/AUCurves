#!/bin/bash
# Build the per-curve OCaml drivers.
#
# Run after `dune build src/Bedrock/Jasmin/extractions/<curve>.vo` produces
# the *_jasmin_extracted.ml files in _build/default/.
#
# Usage:
#   ./build_drivers.sh bls12          # builds bls12_main
#   ./build_drivers.sh x25519_64      # builds x25519_64_main
#   ./build_drivers.sh ed25519_sign   # builds ed25519_sign_main
#   ./build_drivers.sh all            # builds all three
set -e

CURVE="${1:-all}"
SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd)"
BUILD_DIR="$REPO_ROOT/_build/default"
# Extractions land in _build/default/ (cwd during dune build), NOT in
# _build/default/src/Bedrock/Jasmin/extractions/ — Coq's [Extraction "name"]
# writes to the current working directory.
EXTRACTED_DIR="$BUILD_DIR"
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
    ed25519_sign)
      extracted_ml="ed25519_sign_jasmin_extracted.ml"
      # Same trick: needs bls12_jasmin_extracted.ml (or a rename of the
      # ed25519 extraction under that name) for Obj.magic source-type.
      ;;
    ed25519_sign_stubbed)
      # Tier-4 path (b): sign body PLUS empty-body stubs for the 14
      # FFI leaves so jasminc's MakeReferenceArguments (pass 16/30)
      # finds every callee.
      extracted_ml="ed25519_sign_jasmin_extracted.ml"
      ;;
    ed25519_sign_hoist)
      # Blocker A consumer: sign body whose stack-array JCdecls have
      # been hoisted into jf_locals by the Rocq-side
      # hoist_stack_decls_func pass (src/Bedrock/Jasmin/Core.v).
      # Driver materializes each (name, JTstack n) entry as a
      # Stack-kind, Arr(U64,n)-typed Jasmin var.
      extracted_ml="ed25519_sign_hoist_jasmin_extracted.ml"
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
  if [ "$curve" = "ed25519_sign" ]; then
    # If BLS12 has not been extracted, alias our own extraction under the
    # BLS12 module name so Obj.magic can bridge the types.  Standalone
    # path: avoids the 100+ min first-build cost of bls12_prime.vo.
    if [ ! -f "$EXTRACTED_DIR/bls12_jasmin_extracted.ml" ]; then
      cp "$EXTRACTED_DIR/$extracted_ml" "$EXTRACTED_DIR/bls12_jasmin_extracted.ml"
      cp "$EXTRACTED_DIR/${extracted_ml%.ml}.mli" "$EXTRACTED_DIR/bls12_jasmin_extracted.mli"
    fi
    deps=("$EXTRACTED_DIR/bls12_jasmin_extracted.ml" "$EXTRACTED_DIR/$extracted_ml")
  fi
  if [ "$curve" = "ed25519_sign_stubbed" ]; then
    # Same BLS12 alias trick as ed25519_sign.
    if [ ! -f "$EXTRACTED_DIR/bls12_jasmin_extracted.ml" ]; then
      cp "$EXTRACTED_DIR/$extracted_ml" "$EXTRACTED_DIR/bls12_jasmin_extracted.ml"
      cp "$EXTRACTED_DIR/${extracted_ml%.ml}.mli" "$EXTRACTED_DIR/bls12_jasmin_extracted.mli"
    fi
    # Order matters: bls12 first (source type), then sign extraction
    # (referenced by Ed25519_sign_jasmin_extracted in driver), then
    # the stubs extraction.
    deps=("$EXTRACTED_DIR/bls12_jasmin_extracted.ml"
          "$EXTRACTED_DIR/$extracted_ml"
          "$EXTRACTED_DIR/ed25519_sign_stubs_jasmin_extracted.ml")
  fi
  if [ "$curve" = "ed25519_sign_hoist" ]; then
    # Same BLS12 alias trick as ed25519_sign.
    if [ ! -f "$EXTRACTED_DIR/bls12_jasmin_extracted.ml" ]; then
      cp "$EXTRACTED_DIR/$extracted_ml" "$EXTRACTED_DIR/bls12_jasmin_extracted.ml"
      cp "$EXTRACTED_DIR/${extracted_ml%.ml}.mli" "$EXTRACTED_DIR/bls12_jasmin_extracted.mli"
    fi
    # Blocker B: load FFI leaf stubs alongside the hoisted sign body so
    # jasminc's MakeReferenceArguments pass can resolve every JCcall.
    # Order: bls12 (source type) first, then sign-hoist extraction, then
    # the stubs extraction.
    deps=("$EXTRACTED_DIR/bls12_jasmin_extracted.ml"
          "$EXTRACTED_DIR/$extracted_ml"
          "$EXTRACTED_DIR/ed25519_sign_stubs_jasmin_extracted.ml")
  fi

  # Stage all .ml/.mli into a temp dir so ocamlfind can compile .mli first.
  local stage; stage="$(mktemp -d)"
  for dep in "${deps[@]}"; do
    cp "$dep" "$stage/"
    [ -f "${dep%.ml}.mli" ] && cp "${dep%.ml}.mli" "$stage/"
  done
  cp "$SCRIPT_DIR/ocaml_compile.ml" "$stage/"
  cp "$SCRIPT_DIR/${curve}_main.ml" "$stage/"

  ( cd "$stage" && \
    for mli in *.mli; do
      ocamlfind ocamlopt -package jasmin.uint63-native -linkpkg -w -a -c "$mli"
    done && \
    ocamlfind ocamlopt -package jasmin.uint63-native,jasmin.jasmin -linkpkg -w -a \
      $(basename -a "${deps[@]}") \
      ocaml_compile.ml \
      "${curve}_main.ml" \
      -o "$OUT_DIR/${curve}_main"
  )
  rm -rf "$stage"
  echo "[$curve] built $OUT_DIR/${curve}_main"
}

case "$CURVE" in
  all)
    build_one bls12
    build_one x25519_64
    build_one ed25519_sign
    ;;
  *)
    build_one "$CURVE"
    ;;
esac
