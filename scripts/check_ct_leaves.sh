#!/usr/bin/env bash
#
# Jasmin's constant-time type checker (jasmin-ct, jasminc 2026.09.0) on the
# separately compiled Fp leaves modules printed by
# SpillLiveness.pp_module_live_b:
#
#   scripts/check_ct_leaves.sh [LEAVES.jazz ...]
#
# (default: bls12-381-safe-rust/generated/bls12_leaves_live.jazz and
# bn254-safe-rust/generated/bn254_leaves_live.jazz).
#
# The emitted modules carry no security annotations.  This script copies a
# module and puts one `#[ct = ...]` annotation on every export (an annotation
# does not change the program; jasminc compiles the unannotated file):
#
#   - a parameter used as a memory base ([p + k]) is an address: public.  The
#     words it points to are the field operands; jasmin-ct gives every value
#     loaded from memory the level secret, so the operands are secret;
#   - every other parameter (the selector of select_znz) is secret.
#
# No result (the leaves return through memory): "... -> ()".  Each export is
# then checked alone (--slice) at the default pass (after typing), after
# lowering (--compile=lowering), and in --doit mode (secrets only in operands
# of Intel's data-operand-independent-timing instructions, checked after
# instruction selection).  The checker requires every branch condition, loop
# condition, array index and memory address to be public.
#
# Passes iff every export of every module is accepted in all three runs.
set -euo pipefail
cd "$(dirname "$0")/.."
CT="${JASMIN_CT:-jasmin-ct}"
if [ $# -eq 0 ]; then
  set -- bls12-381-safe-rust/generated/bls12_leaves_live.jazz \
         bn254-safe-rust/generated/bn254_leaves_live.jazz
fi
TMP=$(mktemp -d /tmp/check_ct_leaves.XXXXXX)
trap 'rm -rf "$TMP"' EXIT
fail=0
for SRC in "$@"; do
  echo "== $SRC ($(sha256sum "$SRC" | cut -c1-16))"
  python3 - "$SRC" "$TMP/l.jazz" "$TMP/exports" <<'PY'
import re, sys
s = open(sys.argv[1]).read()
out, names = [], []
pos = 0
for m in re.finditer(r'^export fn (\w+)\(([^)]*)\) \{\n', s, re.M):
    name, params = m.group(1), m.group(2)
    end = s.index('\n}\n', m.end())
    body = s[m.end():end]
    levels = []
    for p in params.split(','):
        v = p.split()[-1]
        is_ptr = re.search(r'\[\(*' + re.escape(v) + r' \+', body) is not None
        levels.append('public' if is_ptr else 'secret')
    out.append(s[pos:m.start()])
    out.append('#[ct = "%s -> ()"]\n' % ' × '.join(levels))
    pos = m.start()
    names.append('%s %s' % (name, ','.join(levels)))
out.append(s[pos:])
open(sys.argv[2], 'w').write(''.join(out))
open(sys.argv[3], 'w').write('\n'.join(names) + '\n')
PY
  while read -r f levels; do
    for mode in default lowering doit; do
      case $mode in
        default)  args=() ;;
        lowering) args=(--compile=lowering) ;;
        doit)     args=(--doit) ;;
      esac
      r=0
      "$CT" "${args[@]}" --slice="$f" "$TMP/l.jazz" > "$TMP/out" 2>&1 || r=$?
      if [ $r -eq 0 ]; then
        echo "[OK]   $f ($levels) $mode: accepted"
      else
        msg=$(grep -B1 "constant type checker\|error" "$TMP/out" | tr '\n' ' ' | sed 's|"[^"]*l.jazz", ||' || true)
        echo "[FAIL] $f ($levels) $mode: exit $r $msg"
        fail=1
      fi
    done
  done < "$TMP/exports"
done
exit $fail
