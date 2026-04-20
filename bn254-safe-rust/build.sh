#!/bin/sh
#
# Build the BN254 leaf object library.
#
# Trusted code: this script + the four input artifacts in generated/.
# Run from the crate root. OUT_DIR is set by Cargo when called from build.rs;
# defaults to ./generated/build for standalone runs.
#
# Inputs (committed):
#   generated/bn254_leaves.jazz       - bedrock2 → ToJasmin.v output
#   generated/bn254_mul_cryptopt.asm  - CryptOpt SMT-validated mul
#   generated/jasmin_aliases.s        - thin _bn254_* → bn254_* alias jumps
#
# Output:
#   $OUT_DIR/libbn254_leaves.a
#
# Tools (trusted, version-pinned in tools.lock):
#   jasminc (verified Coq compiler), nasm, as, ar, sed
#
# No build.rs Rust code. No objcopy. No symbol surgery.
# Each step is one tool invocation that a reviewer can read in 30 seconds.

# Fail on the first error. Note: relying on the shebang -e flag is unreliable
# (sh build.sh bypasses the shebang flags), so we set it explicitly here.
set -e

OUT_DIR="${OUT_DIR:-$PWD/generated/build}"
mkdir -p "$OUT_DIR"

GEN="$PWD/generated"
JASMINC="${JASMINC:-jasminc}"

# 1. Rename bn254_mul → bn254_mul_jasmin in the .jazz source so it doesn't
#    collide with the CryptOpt-supplied bn254_mul. This is the cleanest
#    way to handle the symbol split: a textual substitution on a .jazz
#    file the reviewer can diff against the original.
sed 's/\bbn254_mul\b/bn254_mul_jasmin/g' \
    "$GEN/bn254_leaves.jazz" > "$OUT_DIR/bn254_leaves_renamed.jazz"

# 2. jasminc → AT&T assembly (verified register allocation)
"$JASMINC" -auto-spill "$OUT_DIR/bn254_leaves_renamed.jazz" \
    -o "$OUT_DIR/bn254_leaves.s"

# 3. as → ELF object
as "$OUT_DIR/bn254_leaves.s" -o "$OUT_DIR/bn254_leaves.o"

# 4. nasm assembles CryptOpt's SMT-validated mul (NASM intel syntax)
nasm -f elf64 "$GEN/bn254_mul_cryptopt.asm" \
    -o "$OUT_DIR/bn254_mul_cryptopt.o"

# 5. as on the alias shim: maps the safe-tower's _bn254_* extern names
#    to the actual symbols (bn254_add → bn254_add via jmp, and
#    bn254_mul → fiat_bn254_mul to pull in CryptOpt's implementation)
as "$GEN/jasmin_aliases.s" -o "$OUT_DIR/jasmin_aliases.o"

# 6. ar bundles all four .o files into a static archive
ar rcs "$OUT_DIR/libbn254_leaves.a" \
    "$OUT_DIR/bn254_leaves.o" \
    "$OUT_DIR/bn254_mul_cryptopt.o" \
    "$OUT_DIR/jasmin_aliases.o"

echo "Built: $OUT_DIR/libbn254_leaves.a"
