#!/bin/bash
# bench.sh LABEL:asmfile ...   (each asm defines bls12_{add,sub,mul,square}; System V, out-first)
# Builds the reference (AUCurves main generated/bls12_leaves_live.jazz, jasminc 2026.09.0
# -auto-spill, as bls12-381-safe-rust/build.sh) + CryptOpt, tests every variant against the
# reference (10^4 random + edge inputs), big-integer check, objdump stats; "bench" as first arg: cycles.
set -euo pipefail
B=${JAST_TOOLS:-$HOME/tools}/jast2; cd $B
GEN=${AUCURVES:-$HOME/AUCurves}/bls12-381-safe-rust/generated
mode=check; if [ "${1:-}" = bench ]; then mode=bench; shift; elif [ "${1:-}" = check ]; then shift; fi
mkdir -p ref obj
${JAST_TOOLS:-$HOME/tools}/bin/jasminc -auto-spill $GEN/bls12_leaves_live.jazz -o ref/jz2609.s 2> ref/jz2609.log
as ref/jz2609.s -o ref/jz2609.o && objcopy --prefix-symbols=jz_ ref/jz2609.o
nasm -f elf64 -o ref/co_mul.o $GEN/bls12_mul_cryptopt.asm
nasm -f elf64 -o ref/co_square.o $GEN/bls12_square_cryptopt.asm
OBJS="ref/jz2609.o ref/co_mul.o ref/co_square.o"; AOBJS=""; V=""
for a in "$@"; do
  lab=${a%%:*}; s=${a#*:}; o=obj/$lab.o
  as $s -o $o
  for f in add sub mul square; do objcopy --redefine-sym bls12_$f=${lab}_bls12_$f $o; done
  OBJS="$OBJS $o"; AOBJS="$AOBJS $o"
done
for f in add sub mul square; do
  V="$V $f:jazz-main(jasminc2609):jz_bls12_$f"
  case $f in mul|square) V="$V $f:CryptOpt:fiat_bls12_381_p_$f";; esac
  for a in "$@"; do lab=${a%%:*}; V="$V $f:$lab:${lab}_bls12_$f"; done
done
python3 bench/gen_variants.py bench/variants.h $V
gcc -O2 -I bench -o bench/test_variants bench/test_variants.c $OBJS -z noexecstack
gcc -O2 -I bench -o bench/bench_variants bench/bench_variants.c $OBJS -z noexecstack
bench/test_variants check 10000 > bench/test_variants.out; tail -1 bench/test_variants.out
grep -c ' ok$' bench/test_variants.out | sed 's/^/variants ok: /'
bench/test_variants dump 300 | python3 bench/check_bigint.py > bench/check_bigint.out; tail -1 bench/check_bigint.out
python3 objstats.py $AOBJS ref/jz2609.o > bench/objstats.out; cat bench/objstats.out
if [ $mode = bench ]; then python3 bench/med3v.py bench/bench_variants | tee bench/cycles.out; fi
