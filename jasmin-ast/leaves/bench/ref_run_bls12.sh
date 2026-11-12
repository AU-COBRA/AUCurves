#!/bin/bash
# usage: run_bls12.sh FILE.jazz LABEL [ONLYNEW]
set -e
B=${BENCH_DIR:-$(pwd)/bench}
J=$(readlink -f "$1"); cd $B
jasminc -auto-spill "$J" -o newb.s 2>/dev/null
as newb.s -o newb.o && objcopy --prefix-symbols=jn_ newb.o
gcc -O2 -DNEW="\"$2\"" ${3:+-DONLYNEW} -o bench_newb bench_bls12.c co_bls12_mul.o co_bls12_square.o bls12_c_gcc.o bls12_c_clang.o bls12_pp.o shipped_bls12.o newb.o 2>/dev/null
taskset -c 3 ./bench_newb
