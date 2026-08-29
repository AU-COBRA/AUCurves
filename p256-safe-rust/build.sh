#!/bin/sh
#
# Assemble the CryptOpt P-256 field leaves into a static archive.
#
# Inputs (committed):
#   generated/p256_mul_cryptopt.asm     - CryptOpt mul,    seed ...78046135, ratio 1.7247
#   generated/p256_square_cryptopt.asm  - CryptOpt square, seed ...60870535, ratio 1.5522
#
# CryptOpt ships ten seeds per operation, each tuned on a different CPU.
# All twenty were assembled under distinct symbols, checked against the fiat
# reference on random inputs, and timed on this machine (Zen 4, Ryzen 7 PRO
# 7840U); these two were the fastest.  Serial-chain ns/op, fiat = 1.00:
#
#   mul     fiat 30.0 | v2 19.7 (this one) | v0 19.8 | v3 20.2 | ... | v9 23.0
#   square  fiat 27.6 | v7 19.9 (this one) | v8 20.3 | v1 20.5 | ... | v3 22.3
#
# The winning mul was itself produced on a Ryzen 9 7950X, the same
# microarchitecture.  On a different CPU another seed may win; the choice is
# a tuning decision, not a correctness one -- all twenty compute the same
# function.
#
# Output:
#   $OUT_DIR/libp256_cryptopt.a
#
# Tools: nasm, ar

set -e

OUT_DIR="${OUT_DIR:-$PWD/generated/build}"
mkdir -p "$OUT_DIR"

GEN="$PWD/generated"

nasm -f elf64 "$GEN/p256_mul_cryptopt.asm"    -o "$OUT_DIR/p256_mul_cryptopt.o"
nasm -f elf64 "$GEN/p256_square_cryptopt.asm" -o "$OUT_DIR/p256_square_cryptopt.o"

ar rcs "$OUT_DIR/libp256_cryptopt.a" \
    "$OUT_DIR/p256_mul_cryptopt.o" \
    "$OUT_DIR/p256_square_cryptopt.o"

echo "Built: $OUT_DIR/libp256_cryptopt.a"
