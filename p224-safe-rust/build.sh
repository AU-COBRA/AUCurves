#!/bin/sh
#
# Assemble the CryptOpt P-224 field leaves into a static archive.
#
# Inputs (committed):
#   generated/p224_mul_cryptopt.asm     - CryptOpt mul,    seed ...230781590, ratio 1.6447
#   generated/p224_square_cryptopt.asm  - CryptOpt square, seed ...385297777, ratio 1.4178
#
# CryptOpt ships ten seeds per operation, each tuned on a different CPU.
# All twenty were assembled under distinct symbols, checked against the fiat
# reference on 230k random and edge-case inputs (all twenty matched), and
# timed on this machine (Zen 4, Ryzen 7 PRO 7840U); these two were the
# fastest.  Measurements are interleaved round-robin across variants, because
# the clock drifts by more over a sequential 22-variant sweep than the
# variants differ from each other.  Serial-chain ns/op, fiat = 1.00:
#
#   mul     fiat 27.6 | v2 20.1 (this one) | v4 20.6 | v5 20.8 | ... | v0 22.1
#   square  fiat 26.3 | v2 20.2 (this one) | v7 20.9 | v4 21.0 | ... | v0 22.4
#
# Both winners were first in every run, sequential and interleaved.  On a
# different CPU another seed may win; the choice is a tuning decision, not a
# correctness one -- all twenty compute the same function.
#
# Output:
#   $OUT_DIR/libp224_cryptopt.a
#
# Tools: nasm, ar

set -e

OUT_DIR="${OUT_DIR:-$PWD/generated/build}"
mkdir -p "$OUT_DIR"

GEN="$PWD/generated"

nasm -f elf64 "$GEN/p224_mul_cryptopt.asm"    -o "$OUT_DIR/p224_mul_cryptopt.o"
nasm -f elf64 "$GEN/p224_square_cryptopt.asm" -o "$OUT_DIR/p224_square_cryptopt.o"

ar rcs "$OUT_DIR/libp224_cryptopt.a" \
    "$OUT_DIR/p224_mul_cryptopt.o" \
    "$OUT_DIR/p224_square_cryptopt.o"

echo "Built: $OUT_DIR/libp224_cryptopt.a"
