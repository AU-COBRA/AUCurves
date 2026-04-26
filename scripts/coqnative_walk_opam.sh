#!/bin/bash
# Fixed-point coqnative on opam-installed Rewriter (no .cmxs cached there).
# Then re-run on fiat-crypto AbstractInterpretation cluster.

set -u
ulimit -s unlimited
export OCAMLRUNPARAM="b,l=1000000000"
eval $(opam env --switch=rocq-9)

cd $WORKSPACE/AUCurves

FLAGS=(
  -boot
  -R $OPAM_ROOT/rocq-9/lib/coq/theories Coq
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Stdlib Stdlib
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Ltac2 Ltac2
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/coqutil coqutil
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/bedrock2 bedrock2
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Rupicola Rupicola
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Rewriter Rewriter
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Coqprime Coqprime
  -Q $OPAM_ROOT/rocq-9/lib/coq/user-contrib/Bignums Bignums
  -Q _build/default/fiat-crypto/src Crypto
)

cmxs_path_for_opam() {
  local vo="$1"
  local dir="$(dirname "$vo")"
  local base="$(basename "$vo" .vo)"
  local rel="${vo#$OPAM_ROOT/rocq-9/lib/coq/user-contrib/}"
  rel="${rel%.vo}"
  local logical="${rel%/*}"
  local name="N${logical//\//_}_${base}"
  if [[ "$rel" != */* ]]; then
    name="N${base}"
  fi
  echo "${dir}/.coq-native/${name}.cmxs"
}

OPAM_TARGETS=(
  "$OPAM_ROOT/rocq-9/lib/coq/user-contrib/Rewriter"
  # Coqprime and Bignums also lack .cmxs probably, but Rewriter is the one fiat-crypto blocks on.
)

for target in "${OPAM_TARGETS[@]}"; do
  echo "=========================="
  echo "Target: $target"
  echo "=========================="
  ALL_VOS=$(find "$target" -name "*.vo" | sort)
  total=$(echo "$ALL_VOS" | wc -l)
  echo "Total .vo files: $total"

  round=0
  prev_skipped=999999
  while true; do
    round=$((round + 1))
    echo "--- Round $round ---"
    ok=0
    skipped=0
    already=0
    for vo in $ALL_VOS; do
      cmxs=$(cmxs_path_for_opam "$vo")
      if [[ -f "$cmxs" ]]; then
        already=$((already + 1))
        continue
      fi
      if coqnative "${FLAGS[@]}" "$vo" >/dev/null 2>&1; then
        ok=$((ok + 1))
      else
        if [[ -f "$cmxs" ]]; then
          ok=$((ok + 1))
        else
          skipped=$((skipped + 1))
        fi
      fi
    done
    echo "  round $round: ok=$ok, skipped=$skipped, already=$already"
    free -m | head -2 | tail -1 | awk '{print "  mem: free="$4"MB avail="$7"MB"}'
    if [[ "$skipped" == "0" ]]; then
      echo "  Target DONE"
      break
    fi
    if [[ "$skipped" == "$prev_skipped" ]]; then
      echo "  Target STUCK at $skipped"
      break
    fi
    prev_skipped=$skipped
  done
done

echo ""
echo "=== Now re-run fiat-crypto loop (should unblock 131 stuck) ==="
exec /tmp/coqnative_loop.sh
