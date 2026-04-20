#!/usr/bin/env bash
# Build BLS12_MSM.vo at window size c=N and extract the Rust variant.
#
# Usage: build_msm_variant.sh <c>
#   c ∈ {5, 7, 9, 11}
#
# Side effect: mutates src/Bedrock/BLS12_MSM.v (both `Let c` bindings)
# for the duration, restores c=9 at exit.
#
# Outputs:
#   /tmp/BLS12_MSM_c{c}.vo                      (renamed after compile)
#   /tmp/BLS12_MSM_c{c}_assumptions.txt         (Print Assumptions output)
#   .../bls12-jasmin-rs/src/msm_extracted_c{c}.rs  (re-extracted Rust)

set -euo pipefail

C=$1
if [[ ! "$C" =~ ^(5|7|9|11)$ ]]; then
    echo "c must be 5, 7, 9, or 11" >&2; exit 1
fi

cd "$(dirname "$0")/.."
ROOT="$PWD"

eval "$($HOME/.local/bin/opam env --switch=rocq-9)"
ulimit -s unlimited
export OCAMLRUNPARAM="b,l=1000000000"

SRC=src/Bedrock/BLS12_MSM.v
BACKUP=/tmp/BLS12_MSM.v.bak.$$
cp "$SRC" "$BACKUP"
restore() { cp "$BACKUP" "$SRC"; rm -f "$BACKUP"; }
trap restore EXIT

# Substitute BOTH `Let c : Z := 9` lines (PippengerBedrock2 + PippengerSpec).
sed -i "s/  Let c            : Z := 9\.$/  Let c            : Z := ${C}./g" "$SRC"

echo "[1/3] Compiling BLS12_MSM.v at c=${C}"
rocq compile -native-compiler ondemand \
  -R $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Stdlib Stdlib \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/coqutil coqutil \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/bedrock2 bedrock2 \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Rupicola Rupicola \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Rewriter Rewriter \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Coqprime Coqprime \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Bignums Bignums \
  -R _build/default/fiat-crypto/src Crypto \
  -R fiat-crypto/src Crypto \
  -Q src/Theory Theory -Q src/Implementations Implementations \
  -R _build/default/src/Bedrock Bedrock \
  -R src/Bedrock Bedrock \
  -o /tmp/BLS12_MSM.vo \
  "$SRC" 2>&1 | tail -20

cp /tmp/BLS12_MSM.vo "/tmp/BLS12_MSM_c${C}.vo"
echo "[OK] Wrote /tmp/BLS12_MSM_c${C}.vo ($(wc -c < /tmp/BLS12_MSM_c${C}.vo) bytes)"

echo "[2/3] Print Assumptions msm_bls12_ok"
echo 'Require Import Bedrock.BLS12_MSM. Print Assumptions BLS12_MSM.msm_bls12_ok.' | \
  rocq top -native-compiler ondemand \
  -R $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Stdlib Stdlib \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/coqutil coqutil \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/bedrock2 bedrock2 \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Rupicola Rupicola \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Rewriter Rewriter \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Coqprime Coqprime \
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Bignums Bignums \
  -R _build/default/fiat-crypto/src Crypto \
  -R fiat-crypto/src Crypto \
  -Q src/Theory Theory -Q src/Implementations Implementations \
  -R _build/default/src/Bedrock Bedrock \
  -R src/Bedrock Bedrock \
  2>&1 | tee "/tmp/BLS12_MSM_c${C}_assumptions.txt"

echo "[3/3] Done.  c=9 source restored on exit."
