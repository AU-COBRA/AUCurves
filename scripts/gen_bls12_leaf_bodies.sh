#!/usr/bin/env bash
# Regenerate src/Bedrock/JasminAst/BLS12LeafBodies.v: the bedrock2 bodies of fiat-crypto's
# BLS12-381 Fp add/sub/mul/square (bls12_prime.v), printed so that the Jasmin side can load
# them without fiat's synthesis pipeline.  BLS12LeafSpecsProof.bls12_*_eq checks the result
# against bls12_prime by vm_compute, so a stale file fails the build of that proof.
#   scripts/gen_bls12_leaf_bodies.sh [OUT.v]
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT="$PWD"
OUT="${1:-$ROOT/src/Bedrock/JasminAst/BLS12LeafBodies.v}"
ulimit -s unlimited 2>/dev/null || true
dune build -j2 src/Bedrock/Field/Synthesis/Examples/bls12_prime.vo
TMP=$(mktemp -d /tmp/bls12_leaf_bodies.XXXXXX)
trap 'rm -rf "$TMP"' EXIT
cp scripts/GenBLS12LeafBodies.v "$TMP/"
( cd "$TMP" && rocq compile -R "$ROOT/_build/default/src" "" \
    -Q "$ROOT/_build/default/fiat-crypto/src" Crypto \
    -w -all -native-compiler no GenBLS12LeafBodies.v )
python3 scripts/gen_bls12_leaf_bodies.py "$TMP" "$OUT"
