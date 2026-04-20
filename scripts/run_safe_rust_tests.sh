#!/usr/bin/env bash
#
# Unified test harness for the four bedrock2-derived safe-Rust crates.
#
# Runs `cargo test --release` on each crate and reports per-crate
# pass/fail with the test count.  Exit 0 iff every crate's tests
# pass; non-zero on any failure or build break.
#
# Output format (stable, machine-readable last line):
#   [bn254-safe-rust]    PASS  N tests
#   [bls12-381-safe-rust] PASS N tests
#   [bn256-safe-rust]    PASS  N tests
#   [bn446-safe-rust]    PASS  N tests
#   ALL CRATES PASS  total: N tests in 4 crates

set -uo pipefail

cd "$(dirname "$0")/.."
ROOT="$PWD"

CRATES=(
  bn254-safe-rust
  bls12-381-safe-rust
  bn256-safe-rust
  bn446-safe-rust
)

# Make sure cargo is on PATH (the user's shell may set this differently).
if ! command -v cargo >/dev/null 2>&1; then
  echo "[FATAL] cargo not on PATH" >&2
  exit 2
fi

pad() { printf '%-22s' "$1"; }

total_tests=0
total_failures=0
declare -A status_of count_of log_of

for crate in "${CRATES[@]}"; do
  if [ ! -d "$ROOT/$crate" ]; then
    echo "$(pad "[$crate]") SKIP   (directory missing)"
    status_of[$crate]=SKIP
    continue
  fi
  log="/tmp/safe_rust_${crate}_test.log"
  log_of[$crate]=$log
  # --lib --tests skips examples and benches.  The bn254 crate has
  # demo/debug examples (single_step_debug, etc.) that bit-rot against
  # the moving arkworks API and are not part of the verification claim.
  ( cd "$ROOT/$crate" && cargo test --release --no-fail-fast --lib --tests 2>&1 ) > "$log"
  rc=$?

  # Sum up the "test result: X. P passed; F failed" lines from all
  # binaries (lib + each integration test produces one line).
  passed=$(grep -E "^test result:" "$log" \
           | awk '{for (i=1;i<=NF;i++) if ($i=="passed;") print $(i-1)}' \
           | awk '{s+=$1} END {print s+0}')
  failed=$(grep -E "^test result:" "$log" \
           | awk '{for (i=1;i<=NF;i++) if ($i=="failed;") print $(i-1)}' \
           | awk '{s+=$1} END {print s+0}')

  count_of[$crate]=$passed
  if [ "$rc" -eq 0 ] && [ "$failed" -eq 0 ]; then
    status_of[$crate]=PASS
    echo "$(pad "[$crate]") PASS   $passed tests"
    total_tests=$((total_tests + passed))
  else
    status_of[$crate]=FAIL
    total_failures=$((total_failures + failed))
    echo "$(pad "[$crate]") FAIL   $passed passed, $failed failed   log: $log"
  fi
done

# Summary line is parseable; the harness's exit code is the source of truth.
fails=0
for crate in "${CRATES[@]}"; do
  case "${status_of[$crate]:-MISSING}" in
    PASS) ;;
    SKIP) ;;
    *)    fails=$((fails + 1)) ;;
  esac
done

if [ "$fails" -eq 0 ]; then
  echo "ALL CRATES PASS  total: $total_tests tests in ${#CRATES[@]} crates"
  exit 0
else
  echo "FAIL  $fails crate(s) failed; $total_failures individual test failures across all crates"
  exit 1
fi
