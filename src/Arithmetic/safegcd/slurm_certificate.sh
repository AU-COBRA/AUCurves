#!/bin/bash
#SBATCH --job-name=bls12-divstep-cert
#SBATCH --output=certificate_%j.log
#SBATCH --error=certificate_%j.err
#SBATCH --time=7-00:00:00          # 7 days wall time
#SBATCH --mem=16G                   # 16GB RAM
#SBATCH --cpus-per-task=4           # native compiler spawns workers
#SBATCH --partition=cpu             # CPU partition (no GPU needed)
#SBATCH --mail-type=END,FAIL
#
# BLS12-381 divstep convergence certificate computation.
# Uses O'Connor's convex hull framework + native_compute.
#
# Measured: 2h35m on AMD Ryzen 7 PRO 7840U (killed before completion).
# Expected: 3-8 hours with native_compute, several days with vm_compute.
#
# Usage:
#   sbatch slurm_certificate.sh [N]
#   N = iteration count (default 1075, guaranteed max 1101)

set -e

N=${1:-1075}

# --- Configure environment ---
# UNCOMMENT ONE of these for your cluster:
# eval $(opam env --switch=rocq-native)
# export PATH=~/.opam/rocq-native/bin:$PATH
# module load coq/9.0

# Detect compiler
if command -v rocq >/dev/null 2>&1; then
  COQC="rocq compile"
elif command -v coqc >/dev/null 2>&1; then
  COQC="coqc"
else
  echo "ERROR: no Coq/Rocq compiler found"; exit 1
fi

echo "=== BLS12-381 Divstep Certificate ==="
echo "N=$N"
echo "Compiler: $($COQC --version 2>&1 | head -1)"
echo "Host: $(hostname), CPUs: ${SLURM_CPUS_PER_TASK:-$(nproc)}"
echo "Started: $(date)"

cd "$(dirname "$0")"
rm -f *.vo *.vos *.glob *.vok

# Step 1: Framework
echo "Building framework..."
$COQC -R . '' divsteps_def.v
$COQC -R . '' divsteps_base.v
$COQC -R . '' divsteps_convexhull.v
$COQC -R . '' divsteps_theory.v
echo "Framework built: $(date)"

# Step 2: Generate certificate with native_compute
cat > divsteps_bls12.v << EOF
Require Import ZArith.
Require Import divsteps_base.

Definition bls12_p : Z :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Lemma bls12_certificate : ZMap.Empty (N.iter $N (processDivstep bls12_p) state0).
Proof. apply ZMap.is_empty_2. native_compute. reflexivity. Time Qed.
Definition bls12_iters : N := $N.
EOF

# Step 3: Compute (THE LONG STEP)
echo "Computing certificate N=$N with native_compute..."
echo "Expected: 3-8 hours. Monitor with: tail -f certificate_\$SLURM_JOB_ID.log"
time $COQC -R . '' divsteps_bls12.v
echo "Certificate computed: $(date)"

# Step 4: Proof
$COQC -R . '' divsteps_bls12_proof.v
echo ""
echo "=== SUCCESS ==="
echo "N=$N iterations, zero axioms (except bls12_p_prime)."
echo "Files: divsteps_bls12.vo, divsteps_bls12_proof.vo"
echo "Finished: $(date)"
