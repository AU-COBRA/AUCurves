#!/bin/bash
# Constant-time check of the theorem-covered program: print it after parameter expansion with the
# 294b46e compiler, sanitize names, run jasmin-ct 2026.09.0 with explicit contracts (no --infer).
set -euo pipefail
B=${JAST_TOOLS:-$HOME/tools}/jast2; mkdir -p $B/ct; cd $B/ct
for K in "${@:-13}"; do
  ${JAST_TOOLS:-$HOME/tools}/bin/jast294c -bls12-leaves -spill-K $K -pcstexp -o /dev/null > pcstexp_K$K.out 2>&1
  python3 ${AUCURVES:-$HOME/AUCurves}/jasmin-ast/jast2/ct_sanitize.py pcstexp_K$K.out leaves_K${K}_annot.jazz
  ${JAST_TOOLS:-$HOME/tools}/bin/jasmin-ct leaves_K${K}_annot.jazz && echo "budget $K: jasmin-ct ok"
done
