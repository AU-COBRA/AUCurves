#!/bin/bash
# Everything for the BLS12-381 leaves from the Rocq AST (each stage well under 9 min):
#   Rocq snapshot compile + extraction + CIL identity check      (build_leaves_extraction.sh, ~1 min)
#   jast294c driver build                                         (dune, ws294)
#   K sweep, whole-program builds, .jazz / CryptOpt references,
#   tests, objdump statistics, cycles                             (build_leaves.sh bench, ~4 min)
set -euo pipefail
. $HOME/rocq92-env.sh
${JAST_TOOLS:-$HOME/tools}/jast/build_leaves_extraction.sh
(cd ${JAST_TOOLS:-$HOME/tools}/ws294 && DUNE_CACHE=disabled dune build -j4 driver/jast294c.exe)
${JAST_TOOLS:-$HOME/tools}/jast/build_leaves.sh ${1:-bench}
