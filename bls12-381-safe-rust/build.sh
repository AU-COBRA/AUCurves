#!/bin/sh
#
# Build the BLS12-381 leaf object library (and, with BLS12_JASMIN=1, the
# Jasmin tower and group modules).
#
# Inputs (committed, generated/):
#   bls12_mul_cryptopt.asm     - CryptOpt SMT-validated Montgomery multiply
#   bls12_square_cryptopt.asm  - CryptOpt SMT-validated Montgomery square
#   jasmin_aliases.s           - _bls12_mul/_bls12_square -> CryptOpt jumps, and
#                                __jasmin_syscall_randombytes__, the dispatcher
#                                the Jasmin modules call their leaves through
#   shake128.s (optional)      - libjade SHAKE-128, assembled when present
#   bls12_tower_regptr.jazz    - pairing tower, src/Bedrock/ExtractBLS12TowerJasmin.v
#   bls12_group_regptr.jazz    - G1/G2 group law, scalar mult, MSM,
#                                src/Bedrock/ExtractBLS12GroupJasmin.v
#
# Output: $OUT_DIR/libbls12_leaves.a
#
# Tools: nasm, as, ar; jasminc (2026.09.0) when BLS12_JASMIN=1.

set -e

OUT_DIR="${OUT_DIR:-$PWD/generated/build}"
mkdir -p "$OUT_DIR"

GEN="$PWD/generated"
JASMINC="${JASMINC:-jasminc}"
OBJS=""

# 1-2. nasm assembles CryptOpt's SMT-validated multiply and square
nasm -f elf64 "$GEN/bls12_mul_cryptopt.asm" -o "$OUT_DIR/bls12_mul_cryptopt.o"
nasm -f elf64 "$GEN/bls12_square_cryptopt.asm" -o "$OUT_DIR/bls12_square_cryptopt.o"
OBJS="$OUT_DIR/bls12_mul_cryptopt.o $OUT_DIR/bls12_square_cryptopt.o"

# 3. libjade's verified SHAKE-128 (Jasmin -> AT&T asm), when it is present
if [ -f "$GEN/shake128.s" ]; then
  as "$GEN/shake128.s" -o "$OUT_DIR/shake128.o"
  OBJS="$OBJS $OUT_DIR/shake128.o"
fi

# 4. the alias shim and the system-call dispatcher
as "$GEN/jasmin_aliases.s" -o "$OUT_DIR/jasmin_aliases.o"
OBJS="$OBJS $OUT_DIR/jasmin_aliases.o"

# 5. jasminc -> AT&T assembly -> object, for each Jasmin module
if [ "${BLS12_JASMIN:-0}" = 1 ]; then
  for m in bls12_tower_regptr bls12_group_regptr; do
    if [ -f "$GEN/$m.jazz" ]; then
      "$JASMINC" -auto-spill "$GEN/$m.jazz" -o "$OUT_DIR/$m.s" 2> "$OUT_DIR/$m.jasminc.log" \
        || { tail -20 "$OUT_DIR/$m.jasminc.log" >&2; exit 1; }
      as "$OUT_DIR/$m.s" -o "$OUT_DIR/$m.o"
      OBJS="$OBJS $OUT_DIR/$m.o"
    fi
  done
fi

# 6. ar bundles the objects into a static archive
rm -f "$OUT_DIR/libbls12_leaves.a"
# shellcheck disable=SC2086
ar rcs "$OUT_DIR/libbls12_leaves.a" $OBJS

echo "Built: $OUT_DIR/libbls12_leaves.a"
