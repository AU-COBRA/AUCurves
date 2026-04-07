#!/usr/bin/env bash
# Build the fiat-crypto dependencies needed for the Bignum/FElem bridges.
#
# The bridges require:
#   - Crypto.Bedrock.Secp256k1.Field256k1.vo  (for secp256k1 wired specs)
#   - Crypto.Bedrock.Field.Synthesis.Examples.p256_prime.vo  (for P-256 wired specs)
#
# Both are part of the standard fiat-crypto build but not present in this
# checkout's compiled state. To build them, this script invokes `make` on
# the targeted .vo files in the fiat-crypto submodule.
#
# Usage:
#   ./scripts/build_p256_secp256k1_deps.sh
#
# This may take ~30-60 minutes depending on the machine, since it pulls
# in much of the fiat-crypto bedrock2 layer (WordByWordMontgomery
# synthesis pipeline, computed-op derivation, etc.).
#
# Alternative: skip this script and `Admit` the FieldRepresentation
# instances locally. The bridge proofs in BignumFElemBridge.v are
# parameterized over [field_representation : FieldRepresentation] so
# they don't actually need the .vo to typecheck — only the
# per-curve _Bignum_Specs.v / _Wired_Specs.v files do.

set -e

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
FIAT="$ROOT/fiat-crypto"

cd "$FIAT"

echo "Building fiat-crypto dependencies for P-256 / secp256k1 bridges..."
echo "Working dir: $FIAT"
echo

# Build secp256k1 field representation
echo "==> Building Field256k1.vo (secp256k1 field representation)"
make -j4 src/Bedrock/Secp256k1/Field256k1.vo

# Build p256 prime + field representation
echo "==> Building p256_prime.vo (P-256 field representation)"
make -j4 src/Bedrock/Field/Synthesis/Examples/p256_prime.vo

echo
echo "Done. The fiat-crypto bridge dependencies are now compiled."
echo "You can now build the AUCurves bridge files:"
echo "  cd $ROOT && make src/Bedrock/Curve/Secp256k1_Wired_Specs.vo"
echo "  cd $ROOT && make src/Bedrock/Curve/P256_Wired_Specs.vo"
