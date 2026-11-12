#!/bin/bash
# dune build BLS12Leaves2 -> extract -> driver -> compile (args: K values) -> bench
set -euo pipefail
. $HOME/rocq92-env.sh
cd ${AUCURVES:-$HOME/AUCurves} && dune build -j2 src/Jasmin/Ast/BLS12Leaves2.vo 2>&1 | grep -E '^Error|Error:' -A5 | head -20 || true
${JAST_TOOLS:-$HOME/tools}/jast2/extract.sh | tail -1
(cd ${JAST_TOOLS:-$HOME/tools}/ws294 && DUNE_CACHE=disabled dune build -j4 driver/jast294c.exe 2>&1 | head -20)
cd ${JAST_TOOLS:-$HOME/tools}/jast2; T=${TAG:-v}; mkdir -p $T; V=""
for K in "$@"; do
  if ${JAST_TOOLS:-$HOME/tools}/bin/jast294c -bls12-leaves ${OPTS:-} -spill-K $K -o $T/all_K$K.s > $T/all_K$K.err 2>&1; then V="$V ${T}K$K:$T/all_K$K.s"; echo "K=$K ok"
  else echo "K=$K FAIL: $(sed -n 2,3p $T/all_K$K.err | tr '\n' ' ')"; fi
done
./bench.sh ${BENCH:-check} $V 2>&1 | tail -40
