#!/bin/bash
# Generate checkpoint files for the parallelized certificate computation.
# This runs serially but each checkpoint is saved as a .v/.vo file.
# After this, the SLURM array job verifies each segment independently.
#
# Usage: ./generate_checkpoints.sh [K] [N]
#   K = steps per segment (default 50)
#   N = total steps (default 1075)

set -e
cd "$(dirname "$0")"

K=${1:-50}
N=${2:-1075}

if command -v rocq >/dev/null 2>&1; then
  COQC="rocq compile"
else
  COQC="coqc"
fi

echo "=== Generating checkpoints: K=$K, N=$N ==="
echo "Compiler: $($COQC --version 2>&1 | head -1)"

# Build framework first
echo "Building framework..."
$COQC -R . '' divsteps_def.v
$COQC -R . '' divsteps_base.v
$COQC -R . '' divsteps_convexhull.v
$COQC -R . '' divsteps_theory.v

# Generate checkpoint_0 = state0
cat > checkpoint_0.v << 'EOF'
Require Import ZArith.
Require Import divsteps_base.
Open Scope Z_scope.

Definition bls12_p : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition checkpoint_0 := state0.
EOF
$COQC -R . '' checkpoint_0.v
echo "Checkpoint 0: state0 (instant)"

# Generate each subsequent checkpoint
STEP=0
SEG=0
while [ $STEP -lt $N ]; do
  NEXT=$((STEP + K))
  if [ $NEXT -gt $N ]; then NEXT=$N; fi
  STEPS=$((NEXT - STEP))

  echo -n "Checkpoint $NEXT ($STEPS steps from $STEP)... "

  cat > checkpoint_${NEXT}.v << EOF
Require Import ZArith.
Require Import divsteps_base.
Require Import checkpoint_${STEP}.

Definition checkpoint_${NEXT} :=
  Eval native_compute in N.iter ${STEPS} (processDivstep bls12_p) checkpoint_${STEP}.
EOF

  time $COQC -R . '' checkpoint_${NEXT}.v 2>&1 | grep "real" || true
  SIZE=$(ls -lh checkpoint_${NEXT}.vo 2>/dev/null | awk '{print $5}')
  echo "  -> ${SIZE}"

  STEP=$NEXT
  SEG=$((SEG + 1))
done

# Check if final state is empty
echo ""
echo "Checking ZMap.Empty at step $N..."
cat > check_empty.v << EOF
Require Import ZArith.
Require Import divsteps_base.
Require Import checkpoint_${N}.

Lemma final_empty : ZMap.is_empty checkpoint_${N} = true.
Proof. native_compute. reflexivity. Qed.
EOF

if $COQC -R . '' check_empty.v 2>&1 | grep -q "Error"; then
  echo "FAIL: State is NOT empty at step $N."
  echo "Try increasing N (up to 1101)."
  exit 1
else
  echo "SUCCESS: State is empty at step $N!"
  echo "Checkpoints generated. Run 'sbatch slurm_checkpoint.sh' to verify in parallel."
fi
