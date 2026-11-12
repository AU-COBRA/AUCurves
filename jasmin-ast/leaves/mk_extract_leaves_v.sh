#!/bin/bash
# Generates ${JAST_TOOLS:-$HOME/tools}/jast/extract/extract_leaves_sep.v from
# ${JAST_TOOLS:-$HOME/tools}/extraction294/jasmin294_extraction.v: same prelude and exactly the same
# Extract / Inline / Blacklist directives as 294b46e's extraction.v, output directory out_sep,
# and BLS12Leaves.bls12_leaves_prog appended to 294b46e's Separate Extraction list.
# Optional $1: extra names for the Extraction Blacklist line (workaround for module-name clashes).
set -euo pipefail
cd ${JAST_TOOLS:-$HOME/tools}/jast/extract
E=${JAST_TOOLS:-$HOME/tools}/extraction294/jasmin294_extraction.v
EXTRA_BL="${1:-}"
n=$(grep -n '^Set Extraction Output Directory "lang/ocaml".$' $E | cut -d: -f1)
{
  sed -n "1,$((n-1))p" $E
  echo 'From JasminBridge.Ast Require BLS12Leaves.'
  echo 'Set Extraction Output Directory "out_sep".'
  sed -n "$((n+1)),\$p" $E | sed 's/^  wint_int\.$/  wint_int\n  BLS12Leaves.bls12_leaves_prog./' |
    if [ -n "$EXTRA_BL" ]; then
      sed "s/^Extraction Blacklist String List Nat Uint63 Utils Var Array\.$/Extraction Blacklist String List Nat Uint63 Utils Var Array $EXTRA_BL./"
    else cat; fi
} > extract_leaves_sep.v
