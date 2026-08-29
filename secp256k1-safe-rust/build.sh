#!/bin/sh
#
# Assemble the CryptOpt secp256k1 field leaves into a static archive.
#
# Inputs (committed):
#   generated/secp256k1_mul_cryptopt.asm     - CryptOpt mul,    seed ...296317198, ratio 1.7262
#   generated/secp256k1_square_cryptopt.asm  - CryptOpt square, seed ...529382333, ratio 1.8803
#
# These come from CryptOpt's `fiat_secp256k1_montgomery_*` directories, not
# from `fiat_secp256k1_dettman_*`: this crate's field type is the fiat-rust
# `secp256k1_montgomery_64` word-by-word Montgomery 4x64 representation, and
# the Dettman leaves implement a different (unsaturated) representation that
# is not interchangeable with it.
#
# CryptOpt ships ten seeds per operation, each tuned on a different CPU.
# All twenty were assembled under distinct symbols, checked against the fiat
# reference on 240k random and edge-case inputs (all twenty matched), and
# timed on this machine (Zen 4, Ryzen 7 PRO 7840U); these two were the
# fastest.  Measurements are interleaved round-robin across variants, because
# the clock drifts by more over a sequential 22-variant sweep than the
# variants differ from each other.  Serial-chain ns/op, fiat = 1.00:
#
#   mul     fiat 29.2 | v1 20.0 (this one) | v6 20.1 | v0 20.7 | ... | v2 22.5
#   square  fiat 28.6 | v6 20.9 (this one) | v5 21.2 | v7 21.3 | ... | v3 22.4
#
# Both winners were first in both interleaved runs.  On a different CPU
# another seed may win; the choice is a tuning decision, not a correctness
# one -- all twenty compute the same function.
#
# Output:
#   $OUT_DIR/libsecp256k1_cryptopt.a
#
# Tools: nasm, ar

set -e

OUT_DIR="${OUT_DIR:-$PWD/generated/build}"
mkdir -p "$OUT_DIR"

GEN="$PWD/generated"

nasm -f elf64 "$GEN/secp256k1_mul_cryptopt.asm"    -o "$OUT_DIR/secp256k1_mul_cryptopt.o"
nasm -f elf64 "$GEN/secp256k1_square_cryptopt.asm" -o "$OUT_DIR/secp256k1_square_cryptopt.o"

ar rcs "$OUT_DIR/libsecp256k1_cryptopt.a" \
    "$OUT_DIR/secp256k1_mul_cryptopt.o" \
    "$OUT_DIR/secp256k1_square_cryptopt.o"

echo "Built: $OUT_DIR/libsecp256k1_cryptopt.a"
