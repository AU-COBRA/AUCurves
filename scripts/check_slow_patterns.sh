#!/usr/bin/env bash
# Count the slow-proof patterns of docs/slow-proofs.md in src/, and fail if a count exceeds its baseline.
# usage: scripts/check_slow_patterns.sh [--list PATTERN | --update]
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
BASE=scripts/slow_patterns_baseline.txt

hits() {
  case "$1" in
    rewrite-at) git grep -nE 'rewrite [^.]* at [0-9]' -- 'src/*.v' ;;
    inversion-exec)
      git grep -lE 'rust_exec_ed' -- 'src/*.v' | xargs -r grep -nHE 'inversion (H|Hexec|Hcall|Hrest)[A-Za-z0-9_]*' ;;
    destruct-head-abstract) git grep -nE "abstract \(destruct_head'" -- 'src/*.v' ;;
    axiom-large) git grep -nE '^ *Axiom [^:]*:.*(l_pos|smult_pos)' -- 'src/*.v' ;;
  esac
}
PATTERNS="rewrite-at inversion-exec destruct-head-abstract axiom-large"

case "${1:-}" in
  --list) hits "$2" || true; exit 0 ;;
  --update) for p in $PATTERNS; do echo "$p $(hits "$p" | wc -l)"; done > "$BASE"; cat "$BASE"; exit 0 ;;
esac

rc=0
for p in $PATTERNS; do
  n=$(hits "$p" | wc -l)
  b=$(awk -v p="$p" '$1 == p { print $2 }' "$BASE")
  echo "$p: $n (baseline ${b:-none})"
  if [ "$n" -gt "${b:-0}" ]; then
    echo "  more than the baseline: see docs/slow-proofs.md; list with --list $p"
    rc=1
  fi
done
exit $rc
