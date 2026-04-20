#!/bin/sh
# Regenerate and run all per-curve cross-check examples.
set -e
cd "$(dirname "$0")/.."

echo "[1/4] regenerating BN254 multilin example"
python3 tests/generate_bn254_multilin.py

echo "[2/4] regenerating BLS12-381 multilin example"
python3 tests/generate_bls12_381_multilin.py

echo "[3/4] running BN254 cross-check"
( cd bn254-safe-rust && cargo run --release --example multilin_test )

echo "[4/4] running BLS12-381 cross-check"
( cd bls12-381-safe-rust && cargo run --release --example multilin_test )

echo
echo "All cross-checks passed."
