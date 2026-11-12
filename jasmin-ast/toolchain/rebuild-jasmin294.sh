#!/bin/bash
# Rebuild the jasmin 294b46e toolchain whose CIL is extracted from the Rocq 9.2
# switch's Jasmin .vo files.  See ${JAST_TOOLS:-$HOME/tools}/toolchain.md.
#
#   rebuild-jasmin294.sh [stage ...]     stages: plugin cil lib test driver smoke
#                                        (default: all, in this order)
# Every stage takes well under a minute (whole run ~1.5 min, peak RSS ~1.5 GB).
set -euo pipefail
. $HOME/rocq92-env.sh
T=${JAST_TOOLS:-$HOME/tools}
JL=$OPAM_SWITCH_PREFIX/lib/coq/user-contrib/Jasmin
CIL=$T/src/jasmin-git/compiler/src/CIL
PLUGIN_PREFIX=$T/opt/rocq-extraction-patched
export OCAMLPATH=$PLUGIN_PREFIX/lib${OCAMLPATH:+:$OCAMLPATH}
STAGES=${*:-plugin cil lib test driver smoke}
t0=$SECONDS
stamp() { echo "== $1: $((SECONDS - t0)) s"; }

for stage in $STAGES; do case $stage in

plugin)
  # Rocq V9.2.0 plugins/extraction sources (== the .ml installed in the switch;
  # cached copy of https://raw.githubusercontent.com/rocq-prover/rocq/V9.2.0/plugins/extraction/)
  S=$T/src/rocq-extraction-patched
  mkdir -p $S/src/plugins/extraction
  cp $T/src/rocq-extraction-9.2.0-orig/*.ml $T/src/rocq-extraction-9.2.0-orig/*.mli \
     $T/src/rocq-extraction-9.2.0-orig/*.mlg $S/src/plugins/extraction/
  (cd $S/src && patch -p1 --quiet < $T/extraction-plugin.patch)
  cp $S/src/plugins/extraction/*.ml* $S/src/
  rm -f $S/src/plugins/extraction/*.ml $S/src/plugins/extraction/*.mli $S/src/plugins/extraction/*.mlg
  rmdir $S/src/plugins/extraction $S/src/plugins
  (cd $S && DUNE_CACHE=disabled dune build -j4 @install \
         && DUNE_CACHE=disabled dune install --prefix $PLUGIN_PREFIX 2>/dev/null)
  ocamlfind query rocq-extraction-patched.plugin
  stamp plugin ;;

cil)
  # 294b46e proofs/lang/extraction.v, with the Stdlib extraction preludes
  # inlined and the patched plugin loaded (see extraction294/mk_extraction_v.sh)
  cd $T/extraction294
  ./mk_extraction_v.sh
  rm -f lang/ocaml/*.ml lang/ocaml/*.mli
  mkdir -p lang/ocaml
  s=$SECONDS
  rocq compile -R $JL Jasmin -w -all -native-compiler no jasmin294_extraction.v
  echo "extraction: $((SECONDS - s)) s, $(ls lang/ocaml | wc -l) files"
  # as compiler/Makefile's CIL target
  rm -f $CIL/*.ml $CIL/*.mli
  cp lang/ocaml/*.ml $CIL/
  cp lang/ocaml/*.mli $CIL/
  stamp cil ;;

lib)
  cd $T/ws294
  DUNE_CACHE=disabled dune build -j4 jasmin/src/jasmin.cmxa
  stamp lib ;;

test)
  # Rocq-built test program -> only jast_test_prog.ml/.mli into the driver
  $T/rocqtest/build_test_extraction.sh
  stamp test ;;

driver)
  cd $T/ws294
  DUNE_CACHE=disabled dune build -j4 driver/jast294c.exe
  ln -sfn $T/ws294/_build/default/driver/jast294c.exe $T/bin/jast294c
  stamp driver ;;

smoke)
  J=$T/bin/jast294c
  # B: Rocq term -> asm -> C test
  cd $T/smoke/B
  $J -rocq-test -o f.s
  as -o f.o f.s
  gcc -O1 -o test_f test_f.c f.o
  ./test_f
  # A: bn254 leaves, jast294c vs jasminc 2026.09.0 (copies of the AUCurves files)
  cd $T/smoke/A
  for f in bn254_leaves_live bn254_leaves bn254_leaves_nospill; do
    $J -auto-spill $f.jazz -o $f.j294.s > $f.j294.log 2>&1
    $T/bin/jasminc -auto-spill $f.jazz -o $f.jn.s > $f.jn.log 2>&1
  done
  ./check.sh || true
  ./difftest.sh
  stamp smoke ;;

*) echo "unknown stage $stage"; exit 2 ;;
esac; done
