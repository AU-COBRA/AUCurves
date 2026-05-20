#!/usr/bin/env bash
# bench_all_variants.sh — run rustcmd_vs_dalek bench across all 5
# Ed25519 sign/verify variants and dump the per-variant timings.
#
# Variants (cargo features, mutually exclusive at the leaves
# `ed25519_scalarmult{,_base}` + `ed25519_xyzt_add`):
#   1. dalek          — `dalek_leaves` (dalek's `EdwardsPoint` arith)
#   2. decomposed     — `decomposed_leaves` (B1: Hisil-Wong-Carter-Dawson)
#   3. inline         — `inline_leaves` (typed slot inline shim)
#   4. wnaf_comb      — `wnaf_comb_leaves` (signed-window-5 NAF + comb)
#   5. jasminc        — `jasminc_leaves`  (NEW: + jasminc-emitted
#                                          fe25519_xyzt_copy leaf)
#
# Each variant runs ed25519_sign/framework + ed25519_verify/framework.
# The dalek-side numbers ("ed25519_sign/dalek") are identical across
# variants and reported once.

set -euo pipefail

export JASMINC="${JASMINC:-$OPAM_ROOT/rocq-9/bin/jasminc}"
export PATH="$OPAM_ROOT/rocq-9/bin:$PATH"

cd "$(dirname "$0")/.."

VARIANTS=(
  "dalek_leaves"
  "decomposed_leaves"
  "inline_leaves"
  "wnaf_comb_leaves"
  "jasminc_leaves"
)

OUT="/tmp/bench_results_$(date +%s).txt"
echo "Bench results — $(date)" | tee "$OUT"
echo | tee -a "$OUT"

for v in "${VARIANTS[@]}"; do
  echo "=== Variant: $v ===" | tee -a "$OUT"
  cargo bench --features "$v" --bench rustcmd_vs_dalek \
        -- --noplot --measurement-time 2 --sample-size 30 \
        2>/dev/null \
    | awk '
        /^ed25519_(sign|verify)\/(framework|dalek)/ {
          if ($0 ~ /time:/) { print; label="" }
          else              { label=$1 }
          next
        }
        /time:/ && label!="" {
          # The previous line was a bare label; this is the timing.
          gsub(/^[[:space:]]+/, "", $0)
          print label "  " $0
          label=""
        }
      ' \
    | tee -a "$OUT"
  echo | tee -a "$OUT"
done

echo "Results written to $OUT"
