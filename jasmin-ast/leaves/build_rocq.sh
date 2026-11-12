#!/bin/bash
# Compile the frozen snapshot of the leaves sources in ${JAST_TOOLS:-$HOME/tools}/jast/rocq in dependency order.
set -euo pipefail
. $HOME/rocq92-env.sh
R=${JAST_TOOLS:-$HOME/tools}/jast/rocq
F="-boot $(${JAST_TOOLS:-$HOME/tools}/jast/rocqflags.sh) -w -all -native-compiler no"
cd $R
for f in Bedrock/JasminAst/BLS12LeafBodies JasminBridge/Ast/Base JasminBridge/Ast/Trans JasminBridge/Ast/Comp \
         JasminBridge/Ast/Sim JasminBridge/Ast/Fun JasminBridge/Ast/BLS12Leaves; do
  if [ $f.vo -nt $f.v ] && [ "${FORCE:-0}" = 0 ]; then continue; fi
  echo "== $f"
  python3 ${JAST_TOOLS:-$HOME/tools}/jast/measure.py rocq compile $F $f.v
done
