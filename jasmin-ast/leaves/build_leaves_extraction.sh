#!/bin/bash
# 1. compile the frozen Rocq snapshot (build_rocq.sh)
# 2. generate extract/extract_leaves_sep.v: 294b46e's extraction.v (same prelude, same
#    Extract/Inline directives), Separate Extraction list + BLS12Leaves.bls12_leaves_prog,
#    Extraction Blacklist + "Syntax Fun" (bedrock2.Syntax / JasminBridge.Ast.Fun would
#    otherwise be extracted to Syntax.ml / Fun.ml: Jasmin's own OCaml parser-AST module Syntax
#    (used by the driver through -open Jasmin) and OCaml's Stdlib.Fun)
# 3. extract, 4. check that every other generated file is byte-identical to the library's CIL
#    and that no CIL file is missing, 5. copy the new modules to the jast294c driver.
set -euo pipefail
. $HOME/rocq92-env.sh
export OCAMLPATH=${JAST_TOOLS:-$HOME/tools}/opt/rocq-extraction-patched/lib${OCAMLPATH:+:$OCAMLPATH}
J=${JAST_TOOLS:-$HOME/tools}/jast
CIL=${JAST_TOOLS:-$HOME/tools}/src/jasmin-git/compiler/src/CIL
NEW="BLS12LeafBodies BLS12Leaves Byte Comp Fun0 Syntax0 Trans"
$J/build_rocq.sh
$J/mk_extract_leaves_v.sh "Syntax Fun"
cd $J/extract
rm -rf out_sep && mkdir out_sep
python3 $J/measure.py rocq compile -boot $($J/rocqflags.sh) -w -all -native-compiler no extract_leaves_sep.v
same=0; new=""
for f in out_sep/*.ml out_sep/*.mli; do
  b=$(basename $f)
  if [ -e $CIL/$b ]; then cmp -s $f $CIL/$b || { echo "MISMATCH with CIL: $b"; exit 1; }; same=$((same+1))
  else new="$new ${b%.*}"; fi
done
for f in $CIL/*.ml $CIL/*.mli; do [ -e out_sep/$(basename $f) ] || { echo "missing: $(basename $f)"; exit 1; }; done
new=$(echo $new | tr ' ' '\n' | sort -u | tr '\n' ' ')
echo "$same generated files identical to $CIL; new modules: $new"
[ "$(echo $new)" = "$(echo $NEW | tr ' ' '\n' | sort | tr '\n' ' ' | sed 's/ $//')" ] || { echo "unexpected new module set"; exit 1; }
for m in $NEW; do cp out_sep/$m.ml out_sep/$m.mli ${JAST_TOOLS:-$HOME/tools}/ws294/driver/; done
