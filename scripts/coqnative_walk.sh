#!/bin/bash
# Fixed-point coqnative iteration over all fiat-crypto .vo files.
# Each round: try coqnative on every .vo without an existing .cmxs.
# Stop when a round makes zero progress.

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

# Compute the .cmxs path for a given .vo path.
# For _build/default/fiat-crypto/src/A/B/C.vo with logical path Crypto.A.B.C,
# the cmxs lives at _build/default/fiat-crypto/src/A/B/.coq-native/NCrypto_A_B_C.cmxs.
cmxs_path_for() {
  local vo="$1"
  local dir="$(dirname "$vo")"
  local base="$(basename "$vo" .vo)"
  # Strip the prefix "_build/default/fiat-crypto/src/" → ""
  # The remaining dir part with / → _ gives the logical path tail.
  local rel="${vo#_build/default/fiat-crypto/src/}"
  rel="${rel%.vo}"
  local logical="Crypto/${rel%/*}"
  # Build N<Crypto_X_Y_Z> name
  local name="N${logical//\//_}_${base}"
  # Special case: if the .vo is directly in src/ (no subdir), logical is just "Crypto"
  if [[ "$rel" != */* ]]; then
    name="NCrypto_${base}"
  fi
  echo "${dir}/.coq-native/${name}.cmxs"
}

ALL_VOS=$(find _build/default/fiat-crypto/src -name "*.vo" | sort)
total=$(echo "$ALL_VOS" | wc -l)
echo "Total .vo files: $total"

round=0
prev_skipped=999999
while true; do
  round=$((round + 1))
  echo "=== Round $round ==="
  ok=0
  skipped=0
  failed=0
  already=0
  for vo in $ALL_VOS; do
    cmxs=$(cmxs_path_for "$vo")
    if [[ -f "$cmxs" ]]; then
      already=$((already + 1))
      continue
    fi
    if coqnative "${FLAGS[@]}" "$vo" >/dev/null 2>&1; then
      ok=$((ok + 1))
    else
      # Verify the failure left the .cmxs unwritten
      if [[ -f "$cmxs" ]]; then
        # Coqnative wrote partial then errored — count as ok
        ok=$((ok + 1))
      else
        skipped=$((skipped + 1))
      fi
    fi
  done
  echo "  round $round: ok=$ok, skipped=$skipped, already=$already"
  free -m | head -2 | tail -1 | awk '{print "  mem: free="$4"MB avail="$7"MB"}'
  if [[ "$skipped" == "0" ]]; then
    echo "DONE — all .vo files have .cmxs (or coqnative succeeded)"
    break
  fi
  if [[ "$skipped" == "$prev_skipped" ]]; then
    echo "STUCK — round made no progress; $skipped files cannot be coqnative'd"
    echo "Sample of remaining:"
    count=0
    for vo in $ALL_VOS; do
      cmxs=$(cmxs_path_for "$vo")
      if [[ ! -f "$cmxs" ]]; then
        echo "  $vo"
        count=$((count + 1))
        if [[ "$count" -ge 5 ]]; then break; fi
      fi
    done
    break
  fi
  prev_skipped=$skipped
done

echo ""
echo "Final .cmxs count:"
find _build/default/fiat-crypto/src -name "*.cmxs" 2>/dev/null | wc -l
echo "Total .cmxs disk:"
find _build/default/fiat-crypto/src -name "*.cmxs" -exec du -ch {} + 2>/dev/null | tail -1
