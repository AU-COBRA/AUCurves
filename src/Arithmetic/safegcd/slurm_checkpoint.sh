#!/bin/bash
#SBATCH --job-name=bls12-divstep-cp
#SBATCH --output=checkpoint_%A_%a.log
#SBATCH --error=checkpoint_%A_%a.err
#SBATCH --time=2:00:00
#SBATCH --mem=8G
#SBATCH --cpus-per-task=2
#SBATCH --partition=cpu
#SBATCH --array=0-21
#
# Checkpointed divstep certificate computation.
# Runs 22 segments of 50 steps each (total 1100 steps, covers 1075).
# Each segment is independent — runs as a SLURM array job.
#
# Usage:
#   # Step 1: Generate checkpoints (serial, ~20 min)
#   ./generate_checkpoints.sh
#
#   # Step 2: Verify segments (parallel array job)
#   sbatch slurm_checkpoint.sh
#
#   # Step 3: Chain results (fast)
#   ./chain_checkpoints.sh

set -e

SEGMENT=$SLURM_ARRAY_TASK_ID
K=50  # steps per segment
START=$((SEGMENT * K))
END=$((START + K))

# Adjust last segment
TOTAL=1075
if [ $END -gt $TOTAL ]; then
  END=$TOTAL
fi
STEPS=$((END - START))

echo "=== Segment $SEGMENT: steps $START to $END ($STEPS steps) ==="

# Detect compiler
if command -v rocq >/dev/null 2>&1; then
  COQC="rocq compile"
elif command -v coqc >/dev/null 2>&1; then
  COQC="coqc"
else
  echo "ERROR: no compiler"; exit 1
fi

cd "$(dirname "$0")"

# Each segment verifies: N.iter $STEPS f checkpoint_$START = checkpoint_$END
cat > seg_${SEGMENT}.v << EOF
Require Import ZArith.
Require Import divsteps_base.
Require Import checkpoint_${START}.

Lemma seg_${SEGMENT} :
  N.iter ${STEPS} (processDivstep bls12_p) checkpoint_${START} = checkpoint_${END}.
Proof. native_compute. reflexivity. Time Qed.
EOF

time $COQC -R . '' seg_${SEGMENT}.v
echo "Segment $SEGMENT: done"
