#!/bin/bash
set -e
export PATH="$OPAM_ROOT/rocq-native/bin:$PATH"
eval $(opam env)

PATCHES="$WORKSPACE/AUCurves/patches"
PATCHED="$PATCHES/coqutil-unipoly"

echo "[$(date)] Universe polymorphism rebuild via opam pin"

# Step 1: Get compatible coqutil source from opam
if [ ! -d "$PATCHED" ]; then
  echo "[$(date)] Downloading coqutil source..."
  opam source coq-coqutil --dir="$PATCHED"
fi

# Step 2: Patch
for f in src/coqutil/Map/Interface.v src/coqutil/Word/Interface.v; do
  if ! grep -q "Set Universe Polymorphism" "$PATCHED/$f"; then
    sed -i '1s/^/Set Universe Polymorphism.\n/' "$PATCHED/$f"
    echo "Patched $f"
  fi
done

# Step 3: opam pin (cascade rebuild)
echo "[$(date)] opam pin (triggers cascade rebuild)..."
opam pin add coq-coqutil "$PATCHED" --yes 2>&1 | tail -20

# Step 4: Test
echo "[$(date)] Testing combined import..."
cd $WORKSPACE/AUCurves/fiat-crypto
JASMIN="$WORKSPACE/jasmin/proofs"
cat > "$PATCHES/TestUniPoly.v" << 'EOF'
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Field.FieldExtensions.JasminBridgeReal.
Check bls12_add.
EOF

rocq compile -R src Crypto \
  -R "$JASMIN/lang" Jasmin -R "$JASMIN/arch" Jasmin \
  -R "$JASMIN/compiler" Jasmin -R "$JASMIN/3rdparty" Jasmin \
  -R "$JASMIN/ssrmisc" Jasmin -R "$JASMIN/itrees" Jasmin \
  -w "-all" "$PATCHES/TestUniPoly.v" 2>&1 | tail -5

echo "[$(date)] Done"
