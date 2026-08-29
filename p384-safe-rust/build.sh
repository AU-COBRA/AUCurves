#!/bin/sh
#
# Assemble the CryptOpt P-384 field leaves into a static archive.
#
# Inputs (committed):
#   generated/p384_mul_cryptopt.asm     - CryptOpt mul,    seed ...671992404, ratio 1.7232
#   generated/p384_square_cryptopt.asm  - CryptOpt square, seed ...497150072, ratio 1.4874
#
# CryptOpt ships ten seeds per operation, each tuned on a different CPU.
# All twenty were assembled under distinct symbols, checked against the fiat
# reference on 240k random and edge-case inputs (all twenty matched), and
# timed on this machine (Zen 4, Ryzen 7 PRO 7840U); these two were the
# fastest.  Measurements are interleaved round-robin across variants, because
# the clock drifts by more over a sequential 22-variant sweep than the
# variants differ from each other.  Serial-chain ns/op, fiat = 1.00:
#
#   mul     fiat 48.5 | v5 38.0 (this one) | v9 37.8 | v7 38.4 | ... | v4 41.7
#   square  fiat 45.6 | v6 38.7 (this one) | v7 39.4 | v1 39.5 | ... | v4 40.9
#
# mul v5 and v9 are within 1% of each other; v5 won four of the five
# interleaved runs.  On a different CPU another seed may win; the choice is
# a tuning decision, not a correctness one -- all twenty compute the same
# function.
#
# Output:
#   $OUT_DIR/libp384_cryptopt.a
#
# Tools: nasm, ar

set -e

OUT_DIR="${OUT_DIR:-$PWD/generated/build}"
mkdir -p "$OUT_DIR"

GEN="$PWD/generated"

nasm -f elf64 "$GEN/p384_mul_cryptopt.asm"    -o "$OUT_DIR/p384_mul_cryptopt.o"
nasm -f elf64 "$GEN/p384_square_cryptopt.asm" -o "$OUT_DIR/p384_square_cryptopt.o"

ar rcs "$OUT_DIR/libp384_cryptopt.a" \
    "$OUT_DIR/p384_mul_cryptopt.o" \
    "$OUT_DIR/p384_square_cryptopt.o"

echo "Built: $OUT_DIR/libp384_cryptopt.a"
