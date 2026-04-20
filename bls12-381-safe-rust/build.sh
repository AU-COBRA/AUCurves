#!/bin/sh
#
# Build the BLS12-381 CryptOpt leaf object library.
#
# Inputs (committed):
#   generated/bls12_mul_cryptopt.asm    - CryptOpt SMT-validated mul (ratio 18433)
#   generated/bls12_square_cryptopt.asm - CryptOpt SMT-validated square (ratio 18772)
#   generated/jasmin_aliases.s          - thin _bls12_mul/square → CryptOpt symbol jumps
#
# Output:
#   $OUT_DIR/libbls12_leaves.a
#
# Tools: nasm, as, ar

set -e

OUT_DIR="${OUT_DIR:-$PWD/generated/build}"
mkdir -p "$OUT_DIR"

GEN="$PWD/generated"

# 1. nasm assembles CryptOpt's SMT-validated mul (NASM intel syntax)
nasm -f elf64 "$GEN/bls12_mul_cryptopt.asm" \
    -o "$OUT_DIR/bls12_mul_cryptopt.o"

# 2. nasm assembles CryptOpt's SMT-validated square
nasm -f elf64 "$GEN/bls12_square_cryptopt.asm" \
    -o "$OUT_DIR/bls12_square_cryptopt.o"

# 3. as assembles libjade's verified SHAKE-128 (Jasmin → AT&T asm)
as "$GEN/shake128.s" -o "$OUT_DIR/shake128.o"

# 4. as on the alias shim
as "$GEN/jasmin_aliases.s" -o "$OUT_DIR/jasmin_aliases.o"

# 5. ar bundles into a static archive
ar rcs "$OUT_DIR/libbls12_leaves.a" \
    "$OUT_DIR/bls12_mul_cryptopt.o" \
    "$OUT_DIR/bls12_square_cryptopt.o" \
    "$OUT_DIR/shake128.o" \
    "$OUT_DIR/jasmin_aliases.o"

echo "Built: $OUT_DIR/libbls12_leaves.a"
