#!/usr/bin/env bash
#
# Jasmin's constant-time type checker (jasmin-ct, jasminc 2026.09.0) on the
# constant-time G1 / G2 scalar multiplications of the Jasmin path:
#
#   scripts/check_ct_jasmin.sh [GROUP.jazz]   (default: the emitted
#                                              bls12-381-safe-rust/generated/bls12_group_regptr.jazz)
#
# The emitted module carries no security annotations.  This script copies it
# and puts one `#[ct = ...]` annotation on each export checked (an annotation
# does not change the program; jasminc compiles the unannotated file):
#
#   jasmin_bls12_g{1,2}_scalar_mul_ct(out, t, k, p)
#       "public × public × secret × public -> secret × secret"
#       out / t: the output and scratch points (written), k: the scalar
#       (secret), p: the input point (public); both written arrays secret.
#   jasmin_bls12_g{1,2}_scalar_mul(out, k, p)      (negative controls)
#       "public × secret × public -> secret"
#
# For a `reg ptr` argument the level is that of the array's contents; the
# addresses themselves are public.  The checker then requires every branch
# condition, loop bound, array index and memory address in the export and in
# every function it calls (the field leaves bls12_mul / bls12_square /
# bls12_add / bls12_sub, curve_add, msm_curve_double, store_zero, ct_cswap,
# ...: all local functions of the module) to be public.
#
# Passes iff both constant-time exports type-check (also with --doit: secrets
# only in data-operand-independent-timing instructions) and both variable-time
# exports are rejected.
set -euo pipefail
cd "$(dirname "$0")/.."
SRC="${1:-bls12-381-safe-rust/generated/bls12_group_regptr.jazz}"
CT="${JASMIN_CT:-jasmin-ct}"
TMP=$(mktemp -d /tmp/check_ct_jasmin.XXXXXX)
trap 'rm -rf "$TMP"' EXIT
python3 - "$SRC" "$TMP/g.jazz" <<'PY'
import sys
s = open(sys.argv[1]).read()
ann = {
    'jasmin_bls12_g1_scalar_mul_ct': 'public × public × secret × public -> secret × secret',
    'jasmin_bls12_g2_scalar_mul_ct': 'public × public × secret × public -> secret × secret',
    'jasmin_bls12_g1_scalar_mul': 'public × secret × public -> secret',
    'jasmin_bls12_g2_scalar_mul': 'public × secret × public -> secret',
}
for f, t in ann.items():
    old = 'export fn %s(' % f
    assert s.count(old) == 1, f
    s = s.replace(old, '#[ct = "%s"]\n%s' % (t, old))
open(sys.argv[2], 'w').write(s)
PY
fail=0
run() {  # run EXPECT LABEL ARGS...: EXPECT = pass | fail
  local expect=$1 label=$2; shift 2
  local r=0
  "$CT" "$@" "$TMP/g.jazz" > "$TMP/out" 2>&1 || r=$?
  local msg
  msg=$(grep -B1 "constant type checker" "$TMP/out" | tr '\n' ' ' | sed 's|"[^"]*g.jazz", ||' || true)
  if [ "$expect" = pass ] && [ $r -eq 0 ]; then echo "[OK] $label: accepted"
  elif [ "$expect" = fail ] && [ $r -ne 0 ] && [ -n "$msg" ]; then echo "[OK] $label: rejected, as expected: $msg"
  else echo "[FAIL] $label: exit $r $msg"; fail=1; fi
}
for g in g1 g2; do
  run pass "jasmin_bls12_${g}_scalar_mul_ct (k secret)" --slice="jasmin_bls12_${g}_scalar_mul_ct"
  run pass "jasmin_bls12_${g}_scalar_mul_ct (k secret, --doit)" --doit --slice="jasmin_bls12_${g}_scalar_mul_ct"
  run fail "jasmin_bls12_${g}_scalar_mul (variable time, k secret)" --slice="jasmin_bls12_${g}_scalar_mul"
done
exit $fail
