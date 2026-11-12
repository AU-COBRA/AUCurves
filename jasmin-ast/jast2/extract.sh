#!/bin/bash
# Extract BLS12Leaves.bls12_leaves_prog (from the AUCurves _build .vo) with 294b46e's extraction.v
# directives; check the shared modules are byte-identical to the CIL; copy new modules to the driver.
set -euo pipefail
. $HOME/rocq92-env.sh
export OCAMLPATH=${JAST_TOOLS:-$HOME/tools}/opt/rocq-extraction-patched/lib${OCAMLPATH:+:$OCAMLPATH}
A=${AUCURVES:-$HOME/AUCurves}/_build/default/src
E=${JAST_TOOLS:-$HOME/tools}/extraction294/jasmin294_extraction.v
CIL=${JAST_TOOLS:-$HOME/tools}/src/jasmin-git/compiler/src/CIL
D=${JAST_TOOLS:-$HOME/tools}/ws294/driver
cd ${JAST_TOOLS:-$HOME/tools}/jast2/extract
n=$(grep -n '^Set Extraction Output Directory "lang/ocaml".$' $E | cut -d: -f1)
{
  sed -n "1,$((n-1))p" $E
  echo 'From JasminBridge.Ast Require BLS12Leaves BLS12Leaves2.'
  echo 'Set Extraction Output Directory "out_sep".'
  sed -n "$((n+1)),\$p" $E | sed "s/^  wint_int\\.$/  wint_int\\n  BLS12Leaves.bls12_leaves_prog\\n  BLS12Leaves2.bls12_leaves2_prog./" |
    sed "s/^Extraction Blacklist String List Nat Uint63 Utils Var Array\.$/Extraction Blacklist String List Nat Uint63 Utils Var Array Syntax Fun./"
} > extract_leaves_sep.v
rm -rf out_sep && mkdir out_sep
rocq compile -Q $A/Jasmin JasminBridge -Q $A/Bedrock/JasminAst Bedrock.JasminAst -w -all -native-compiler no extract_leaves_sep.v
same=0; new=""
for f in out_sep/*.ml out_sep/*.mli; do
  b=$(basename $f)
  if [ -e $CIL/$b ]; then cmp -s $f $CIL/$b || { echo "MISMATCH with CIL: $b"; exit 1; }; same=$((same+1))
  else new="$new ${b%.*}"; fi
done
for f in $CIL/*.ml $CIL/*.mli; do [ -e out_sep/$(basename $f) ] || { echo "missing: $(basename $f)"; exit 1; }; done
new=$(echo $new | tr ' ' '\n' | sort -u | tr '\n' ' ')
echo "$same generated files identical to the CIL; new modules: $new"
rm -f $D/NEWMODS; for m in $new; do cp out_sep/$m.ml out_sep/$m.mli $D/; echo $m >> $D/NEWMODS; done
