#!/usr/bin/env bash
# print_assumptions_audit.sh — drive `Print Assumptions` (Rocq) and
# `#print axioms` (Lean) across the headline end-to-end theorems in
# the verified Signal pipeline, then aggregate the union of axioms
# used into a single report.
#
# Invocation:
#   bash scripts/print_assumptions_audit.sh             # full run
#   bash scripts/print_assumptions_audit.sh rocq        # Rocq side only
#   bash scripts/print_assumptions_audit.sh lean        # Lean side only
#
# Output:
#   /tmp/aucurves_audit/rocq_<theorem>.txt   per-theorem Print Assumptions
#   /tmp/aucurves_audit/lean_<theorem>.txt   per-theorem #print axioms
#   /tmp/aucurves_audit/SUMMARY.txt          aggregated union
#
# The script regenerates a small Rocq driver and a small Lean driver
# for each theorem, then invokes the respective compiler.  Failures
# are recorded with their stderr but DO NOT abort the loop.

set -u
set -o pipefail

WHICH="${1:-all}"

ROCQ_REPO="$WORKSPACE/AUCurves"
LEAN_REPO="$WORKSPACE/../SSProve-lean"
OUT_DIR="/tmp/aucurves_audit"
mkdir -p "$OUT_DIR"

# ---------------------------------------------------------------- Rocq

# Format: <module>:<theorem_or_axiom>
# Module path is what `Require Import` accepts.
ROCQ_TARGETS=(
  # The sole bridge axiom.
  "Bedrock.RustCmdToRustSimulates:RustcExec_correct"
  # libjade axioms (each is itself an axiom; Print Assumptions self-references).
  "Bedrock.LibjadeAxioms:jade_hash_sha256_correct"
  "Bedrock.LibjadeAxioms:jade_hash_sha512_correct"
  "Bedrock.LibjadeAxioms:jade_curve25519_x25519_correct"
  "Bedrock.LibjadeAxioms:jade_curve25519_x25519_base_correct"
  "Bedrock.LibjadeAxioms:jade_mlkem768_keypair_derand_correct"
  "Bedrock.LibjadeAxioms:jade_mlkem768_enc_derand_correct"
  "Bedrock.LibjadeAxioms:jade_mlkem768_dec_correct"
  # Top-level functional-correctness theorems.
  "Bedrock.RustCmdToRustSimulates:print_module_preserves_semantics"
  "Bedrock.End2End.Ed25519.Fe25519InvertCorrect:fe25519_invert_correct"
  "Bedrock.End2End.Ed25519.MontToEdwardsCorrect:mont_to_edwards_correct"
  "Bedrock.End2End.Ed25519.Scalar25519FromWideCorrect:from_wide_correct"
  "Bedrock.End2End.Ed25519.BuildCombTableCorrect:build_comb_table_correct"
  "Bedrock.End2End.Ed25519.Fe25519AddSubCorrect:fe25519_add_body_correct"
  "Bedrock.End2End.Ed25519.Fe25519AddSubCorrect:fe25519_sub_body_correct"
  "Bedrock.End2End.Ed25519.Sign_Strong_Correctness:ed25519_sign_strong_correct"
  "Bedrock.End2End.Ed25519.Sign_Strong_Correctness:ed25519_sign_gallina_lifted_clean"
  "Bedrock.End2End.XEdDSA.Sign_Strong_Correctness:xeddsa_sign_strong_correct"
  "Bedrock.InlineCallFn:inline_callfn_n_preserves_semantics_fwd"
)

run_rocq_audit() {
  echo "=== Rocq Print Assumptions audit ==="
  eval "$(opam env --switch=rocq-9 2>/dev/null)" || true
  ulimit -s unlimited
  export OCAMLRUNPARAM="b,l=1000000000"

  # Load the -R/-Q flags from _CoqProject so this script tracks any
  # future path additions automatically.
  local FLAGS
  FLAGS=$(grep -E '^-[RQ] ' "$ROCQ_REPO/_CoqProject" | tr '\n' ' ')

  : > "$OUT_DIR/rocq_axiom_union.txt"
  : > "$OUT_DIR/rocq_failures.txt"

  for entry in "${ROCQ_TARGETS[@]}"; do
    local mod="${entry%:*}"
    local thm="${entry##*:}"
    local tmpv="/tmp/aucurves_audit/rocq_${thm}.v"
    local out="$OUT_DIR/rocq_${thm}.txt"

    cat > "$tmpv" <<EOF
From $mod Require Import $(basename "$mod").
Print Assumptions $thm.
EOF
    # The `From $mod Require` line is wrong: Rocq's `From X Require` expects
    # X to be a library *prefix*.  Use simple `Require Import <mod>` instead.
    cat > "$tmpv" <<EOF
Require Import $mod.
Print Assumptions $thm.
EOF

    echo "  [rocq] $mod : $thm"
    if timeout 180 rocq compile $FLAGS -native-compiler no "$tmpv" \
         > "$out" 2>&1 ; then
      # Extract axiom names referenced in the Print Assumptions output.
      grep -E '^[A-Za-z_][A-Za-z0-9_.]* *:' "$out" \
        | grep -v '^Closed under' \
        | awk -F: '{print $1}' \
        | sort -u \
        >> "$OUT_DIR/rocq_axiom_union.txt"
    else
      echo "$mod:$thm" >> "$OUT_DIR/rocq_failures.txt"
    fi
  done

  sort -u -o "$OUT_DIR/rocq_axiom_union.txt" "$OUT_DIR/rocq_axiom_union.txt"
}

# ---------------------------------------------------------------- Lean

# Format: <module>:<theorem>.  Module is the Lean import path.
LEAN_TARGETS=(
  "CatCrypt.Crypto.Jasmin.RustCmdCTAnalysis:cmdCT_sound"
  "CatCrypt.Crypto.Jasmin.RustCmdToJasmin:rustExecSimulates_withCalls"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:fe25519InvertBody_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:combTableInitArrV2Body_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:montUToEdwardsBody_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:mulBody_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:addBody_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:subBody_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:negateBody_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:fromBytesModOrderBody_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.EmittedASTCorrectness:toBytesBody_memory_safe"
  "CatCrypt.Crypto.Jasmin.Examples.XEdDSAVerify:xeddsaVerifyBody_memory_safe"
  "CatCrypt.Crypto.Pedersen.SurfaceDeps:pedersen_extracted_uc_secure"
  "CatCrypt.Crypto.AEAD.AESCBC_HMAC_Reduction:aescbc_hmac_realizes_faead_full"
  "CatCrypt.Crypto.Signal.X3DH:x3dh_uc_secure"
  "CatCrypt.Crypto.Signal.PQXDHPipelineUC:pqxdh_pipeline_uc_secure"
  "CatCrypt.Crypto.Signal.SenderKeys.Security:sender_keys_security"
  "CatCrypt.Crypto.Signal.SPQR.SecurityTheorem:spqr_uc_secure"
  "CatCrypt.Crypto.Jasmin.JasminToRustEmitSimulates:RustcExec_correct"
)

run_lean_audit() {
  echo "=== Lean #print axioms audit ==="
  cd "$LEAN_REPO" || { echo "Lean repo missing"; return 1; }
  : > "$OUT_DIR/lean_axiom_union.txt"
  : > "$OUT_DIR/lean_failures.txt"

  for entry in "${LEAN_TARGETS[@]}"; do
    local mod="${entry%:*}"
    local thm="${entry##*:}"
    local tmplean="/tmp/aucurves_audit/lean_${thm}.lean"
    local out="$OUT_DIR/lean_${thm}.txt"

    cat > "$tmplean" <<EOF
import $mod
#print axioms $mod.$thm
EOF

    echo "  [lean] $mod : $thm"
    if timeout 300 lake env lean "$tmplean" > "$out" 2>&1 ; then
      # `#print axioms X` outputs lines like:
      #   'X' depends on axioms: [a, b, c]
      # Extract identifiers from the bracketed list, plus follow-on lines.
      sed -n 's/.*depends on axioms: \[\(.*\)\].*/\1/p; s/.*depends on axioms:[ \t]*$//p' "$out" \
        | tr ',' '\n' \
        | sed 's/^[ \t]*//; s/[ \t]*$//' \
        | grep -v '^$' \
        | sort -u \
        >> "$OUT_DIR/lean_axiom_union.txt"
    else
      echo "$mod:$thm" >> "$OUT_DIR/lean_failures.txt"
    fi
  done

  sort -u -o "$OUT_DIR/lean_axiom_union.txt" "$OUT_DIR/lean_axiom_union.txt"
}

# -------------------------------------------------------------- Driver

cd "$ROCQ_REPO" || exit 1

case "$WHICH" in
  rocq) run_rocq_audit ;;
  lean) run_lean_audit ;;
  all)  run_rocq_audit; run_lean_audit ;;
  *) echo "Usage: $0 [rocq|lean|all]" ; exit 1 ;;
esac

# Summary report
{
  echo "# AUCurves / SSProve-lean trust-axiom audit"
  echo
  echo "Date: $(date -Iseconds)"
  echo
  echo "## Rocq axioms (union across audited Print Assumptions output)"
  echo
  if [[ -s "$OUT_DIR/rocq_axiom_union.txt" ]]; then
    cat "$OUT_DIR/rocq_axiom_union.txt"
  else
    echo "(none — Rocq pass not run or all empty)"
  fi
  echo
  echo "## Lean axioms (union across audited #print axioms output)"
  echo
  if [[ -s "$OUT_DIR/lean_axiom_union.txt" ]]; then
    cat "$OUT_DIR/lean_axiom_union.txt"
  else
    echo "(none — Lean pass not run or all empty)"
  fi
  echo
  echo "## Failures"
  echo
  echo "### Rocq"
  if [[ -s "$OUT_DIR/rocq_failures.txt" ]]; then
    cat "$OUT_DIR/rocq_failures.txt"
  else
    echo "(none)"
  fi
  echo
  echo "### Lean"
  if [[ -s "$OUT_DIR/lean_failures.txt" ]]; then
    cat "$OUT_DIR/lean_failures.txt"
  else
    echo "(none)"
  fi
} > "$OUT_DIR/SUMMARY.txt"

echo
echo "Done.  See $OUT_DIR/SUMMARY.txt and per-theorem files in $OUT_DIR/"
