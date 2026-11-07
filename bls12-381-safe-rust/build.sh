#!/bin/sh
#
# Build the BLS12-381 leaf object library (and, with BLS12_JASMIN=1, the
# Jasmin tower and group modules).
#
# Inputs (committed, generated/):
#   bls12_mul_cryptopt.asm     - CryptOpt SMT-validated Montgomery multiply
#   bls12_square_cryptopt.asm  - CryptOpt SMT-validated Montgomery square
#   jasmin_aliases.s           - _bls12_mul/_bls12_square -> CryptOpt jumps, and
#                                __jasmin_syscall_randombytes__, the dispatcher
#                                the Jasmin modules call their leaves through
#   shake128.s (optional)      - libjade SHAKE-128, assembled when present
#   bls12_tower_regptr.jazz    - pairing tower, src/Bedrock/ExtractBLS12TowerJasmin.v
#   bls12_group_regptr.jazz    - G1/G2 group law, scalar mult, MSM,
#                                src/Bedrock/ExtractBLS12GroupJasmin.v
#   bls12_leaves_live.jazz     - the Fp leaves through polish_func_adc and
#                                CtSelect.ct_func (no branch) with
#                                liveness-chosen #[spill] hints,
#                                src/Bedrock/Jasmin/ExtractBLS12LeavesLive.v
#                                (scripts/emit_bls12_leaves_live.sh;
#                                scripts/check_ct_leaves.sh: jasmin-ct)
#
#   bls12_{tower,group}_regptr_ffi.jazz
#                              - the same modules with mul/square behind the
#                                #randombytes dispatcher (emit scripts, variant _ffi)
#
# BLS12_JASMIN_LEAVES (with BLS12_JASMIN=1; default jasmin):
#   jasmin    the Jasmin modules contain mul and square (local functions printed
#             from the same polish_func_adc bodies); the safe-Rust path and the
#             dispatcher's inverse use the Jasmin leaves of bls12_leaves_live.jazz
#             (jasmin_aliases.s assembled with JASMIN_LEAVES); no CryptOpt object
#             is built or linked
#   cryptopt  the *_ffi modules, whose mul and square calls go through the
#             dispatcher to CryptOpt's, as do the safe-Rust path's
# Without BLS12_JASMIN=1 the leaves are CryptOpt's, as before.
#
# Output: $OUT_DIR/libbls12_leaves.a
#
# Tools: nasm, as, ar; jasminc (2026.09.0) when BLS12_JASMIN=1.

set -e

OUT_DIR="${OUT_DIR:-$PWD/generated/build}"
mkdir -p "$OUT_DIR"

GEN="$PWD/generated"
JASMINC="${JASMINC:-jasminc}"
OBJS=""

LEAVES=cryptopt
if [ "${BLS12_JASMIN:-0}" = 1 ]; then LEAVES="${BLS12_JASMIN_LEAVES:-jasmin}"; fi
case "$LEAVES" in jasmin|cryptopt) ;; *) echo "BLS12_JASMIN_LEAVES=$LEAVES: jasmin or cryptopt" >&2; exit 1;; esac

# 1-2. nasm assembles CryptOpt's SMT-validated multiply and square, or
#      jasminc compiles the Jasmin leaves
if [ "$LEAVES" = cryptopt ]; then
  nasm -f elf64 "$GEN/bls12_mul_cryptopt.asm" -o "$OUT_DIR/bls12_mul_cryptopt.o"
  nasm -f elf64 "$GEN/bls12_square_cryptopt.asm" -o "$OUT_DIR/bls12_square_cryptopt.o"
  OBJS="$OUT_DIR/bls12_mul_cryptopt.o $OUT_DIR/bls12_square_cryptopt.o"
  ASFLAGS=""
else
  "$JASMINC" -auto-spill "$GEN/bls12_leaves_live.jazz" -o "$OUT_DIR/bls12_leaves_live.s" \
      2> "$OUT_DIR/bls12_leaves_live.jasminc.log" \
    || { tail -20 "$OUT_DIR/bls12_leaves_live.jasminc.log" >&2; exit 1; }
  as "$OUT_DIR/bls12_leaves_live.s" -o "$OUT_DIR/bls12_leaves_live.o"
  OBJS="$OUT_DIR/bls12_leaves_live.o"
  ASFLAGS="--defsym JASMIN_LEAVES=1"
fi

# 3. libjade's verified SHAKE-128 (Jasmin -> AT&T asm), when it is present
if [ -f "$GEN/shake128.s" ]; then
  as "$GEN/shake128.s" -o "$OUT_DIR/shake128.o"
  OBJS="$OBJS $OUT_DIR/shake128.o"
fi

# 4. the alias shim and the system-call dispatcher
# shellcheck disable=SC2086
as $ASFLAGS "$GEN/jasmin_aliases.s" -o "$OUT_DIR/jasmin_aliases.o"
OBJS="$OBJS $OUT_DIR/jasmin_aliases.o"

# 5. jasminc -> AT&T assembly -> object, for each Jasmin module
if [ "${BLS12_JASMIN:-0}" = 1 ]; then
  if [ "$LEAVES" = cryptopt ]; then SFX=_ffi; else SFX=; fi
  for m in bls12_tower_regptr$SFX bls12_group_regptr$SFX; do
    if [ -f "$GEN/$m.jazz" ]; then
      "$JASMINC" -auto-spill "$GEN/$m.jazz" -o "$OUT_DIR/$m.s" 2> "$OUT_DIR/$m.jasminc.log" \
        || { tail -20 "$OUT_DIR/$m.jasminc.log" >&2; exit 1; }
      as "$OUT_DIR/$m.s" -o "$OUT_DIR/$m.o"
      OBJS="$OBJS $OUT_DIR/$m.o"
    fi
  done
fi

# 6. ar bundles the objects into a static archive
rm -f "$OUT_DIR/libbls12_leaves.a"
# shellcheck disable=SC2086
ar rcs "$OUT_DIR/libbls12_leaves.a" $OBJS

echo "Built: $OUT_DIR/libbls12_leaves.a (mul/square: $LEAVES)"
