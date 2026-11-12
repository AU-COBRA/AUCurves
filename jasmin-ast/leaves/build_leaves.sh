#!/bin/bash
# Build all BLS12-381 leaves variants, run the tests and objdump statistics, optionally cycles.
#   ${JAST_TOOLS:-$HOME/tools}/jast/build_leaves.sh          sweep K + reference builds + tests + stats
#   ${JAST_TOOLS:-$HOME/tools}/jast/build_leaves.sh bench    ... + cycles (bench/med3v.py, 3 runs)
# Prerequisites: build_leaves_extraction.sh, the jast294c driver build (run_all.sh does both).
set -euo pipefail
. $HOME/rocq92-env.sh
J=${JAST_TOOLS:-$HOME/tools}/jast
JAST=${JAST_TOOLS:-$HOME/tools}/bin/jast294c
JASMINC=${JAST_TOOLS:-$HOME/tools}/bin/jasminc
GEN=${AUCURVES:-$HOME/AUCurves}/bls12-381-safe-rust/generated
cd $J

# 1. AST builds: bls12_leaves_prog ... K, one leaf at a time (-leaves-only), K sweep
$J/sweep_k.sh > /dev/null
echo "== K sweep (sweep/summary.tsv)"; awk -F'\t' '{printf "%-14s %-7s %-5s %-6s %s\n", $1, $2, $3, $4, substr($5, 1, 90)}' sweep/summary.tsv
# whole program (no -leaves-only filter): default K=8, K=15 (largest K at which add, hence all
# four, compiles), K=100000 (no spills)
ALLK=""
for k in 8 15 100000; do
  if $JAST -bls12-leaves -spill-K $k -o sweep/all_K$k.s > sweep/all_K$k.err 2>&1; then echo "all four, K=$k: compiled"; ALLK="$ALLK $k"
  else rm -f sweep/all_K$k.s; echo "all four, K=$k: FAILED: $(sed -n 2,3p sweep/all_K$k.err | tr -s ' \n' ' ')"; fi
done

# 2. references: #21 emission with jasminc 2026.09.0 -auto-spill (as run_bls12.sh) and jast294c -auto-spill;
#    CryptOpt (nasm, System V, out-first: rdi = out, rsi = x, rdx = y)
mkdir -p ref sweep/obj
cp ${AUCURVES:-$HOME/AUCurves}/bls12-381-safe-rust/generated/bls12_leaves_live.jazz ref/bls12_leaves_live.jazz
$JASMINC -auto-spill ref/bls12_leaves_live.jazz -o ref/jz2609.s 2> ref/jz2609.log
$JAST -auto-spill ref/bls12_leaves_live.jazz -o ref/jz294.s 2> ref/jz294.log
as ref/jz2609.s -o ref/jz2609.o && objcopy --prefix-symbols=jz_ ref/jz2609.o
as ref/jz294.s -o ref/jz294.o && objcopy --prefix-symbols=j294_ ref/jz294.o
nasm -f elf64 -o ref/co_mul.o $GEN/bls12_mul_cryptopt.asm
nasm -f elf64 -o ref/co_square.o $GEN/bls12_square_cryptopt.asm

# 3. variant table: reference (.jazz, jasminc 2026.09) first for each op
V=""; OBJS="ref/jz2609.o ref/jz294.o ref/co_mul.o ref/co_square.o"; AOBJS=""
for f in add sub mul square; do
  V="$V $f:jasminc2609-autospill:jz_bls12_$f $f:jast294c-autospill:j294_bls12_$f"
  case $f in mul|square) V="$V $f:CryptOpt:fiat_bls12_381_p_$f";; esac
  for s in $(ls sweep/bls12_${f}_K*.s 2>/dev/null | sort -t K -k2 -n); do
    k=${s##*_K}; k=${k%.s}; o=sweep/obj/bls12_${f}_K$k.o
    as $s -o $o && objcopy --redefine-sym bls12_$f=ast_k${k}_bls12_$f $o
    V="$V $f:AST-K$k:ast_k${k}_bls12_$f"; OBJS="$OBJS $o"; AOBJS="$AOBJS $o"
  done
done
for k in $ALLK; do   # the whole-program builds: all four functions from one Compile.compile
  o=sweep/obj/all_K$k.o; as sweep/all_K$k.s -o $o
  for f in add sub mul square; do objcopy --redefine-sym bls12_$f=astall_k${k}_bls12_$f $o; done
  OBJS="$OBJS $o"; AOBJS="$AOBJS $o"
done
V2=""
for f in add sub mul square; do
  V2="$V2 $(echo $V | tr ' ' '\n' | grep "^$f:" | tr '\n' ' ')"
  for k in $ALLK; do V2="$V2 $f:AST-all-K$k:astall_k${k}_bls12_$f"; done
done
V=$V2
python3 bench/gen_variants.py bench/variants.h $V
gcc -O2 -I bench -o bench/test_variants bench/test_variants.c $OBJS -z noexecstack
gcc -O2 -I bench -o bench/bench_variants bench/bench_variants.c $OBJS -z noexecstack 2>/dev/null

# 4. tests
echo "== differential test (vs .jazz/jasminc 2026.09; 10^4 random + 64 edge inputs per op)"
bench/test_variants check 10000 | tee bench/test_variants.out | tail -1
grep -c ' ok$' bench/test_variants.out | sed 's/^/variants ok: /'
echo "== big-integer reference (300 random + 64 edge inputs per variant)"
bench/test_variants dump 300 | python3 bench/check_bigint.py > bench/check_bigint.out; tail -1 bench/check_bigint.out
# 5. objdump statistics
python3 $J/objstats.py $AOBJS ref/jz2609.o ref/co_mul.o ref/co_square.o > bench/objstats.out
echo "== objdump statistics (bench/objstats.out)"; cat bench/objstats.out
# 6. cycles
if [ "${1:-}" = bench ]; then
  echo "== cycles (bench/cycles.out)"; python3 bench/med3v.py bench/bench_variants | tee bench/cycles.out
fi
