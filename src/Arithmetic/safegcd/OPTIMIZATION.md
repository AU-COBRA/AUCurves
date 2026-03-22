# Optimizing the O'Connor Certificate Computation

The naive `vm_cast_no_check (refl_equal true)` on `N.iter 1075 (processDivstep p) state0`
takes 2-7 days. Here are strategies to reduce this.

## Strategy 1: Checkpointing (moderate speedup, parallelizable)

Break the computation into K-step segments with intermediate checkpoints:

```coq
Definition s0   := state0.
Definition s50  := Eval native_compute in N.iter 50 (processDivstep p) s0.
Definition s100 := Eval native_compute in N.iter 50 (processDivstep p) s50.
...

Lemma seg_0_50 : N.iter 50 (processDivstep p) s0 = s50.
Proof. native_compute. reflexivity. Qed.
```

**Measured data** (Rocq 9.0, native, AMD Ryzen 7):
- 10 steps: 0.3s, 23KB state
- 50 steps: 43s, 539KB state

With K=50, there would be ~22 segments. Each is independently verifiable
(~43s). Total serial time: ~22 × 43s = ~16 minutes. Parallelizable on SLURM.

**Issue**: State size grows. At later steps the convex hull may be larger.
Need to check: does the state shrink near convergence?

## Strategy 2: OCaml extraction (fastest, recommended)

1. Extract `processDivstep` to OCaml using Coq's extraction mechanism
2. Run the extracted code natively to compute all intermediate states
3. Serialize states back as Coq terms
4. Verify each transition in Coq (fast — single step)

```bash
# Step 1: Extract
cat > extract_divstep.v << 'EOF'
Require Import ExtrOcamlBasic ExtrOcamlString ExtrOcamlZBigInt.
Require Import divsteps_base.
Extraction "divstep_extracted.ml" processDivstep state0.
EOF
coqc -R . '' extract_divstep.v

# Step 2: Run in OCaml (fast!)
ocamlfind ocamlopt -package zarith -linkpkg divstep_extracted.ml driver.ml -o compute_checkpoints
./compute_checkpoints > checkpoints.v

# Step 3: Verify in Coq (parallel, fast)
for seg in seg_*.v; do coqc -R . '' $seg; done
```

## Strategy 3: Jump divsteps (fewest iterations)

The Hvass fork's `JumpDivstep.v` processes 62 divsteps at once (one word
at a time). This reduces 1075 individual steps to ceil(1075/62) = 18 "jump"
steps. Each jump step is more complex but there are far fewer.

Adapting O'Connor's framework to use jump divsteps would require:
- Proving `processDivstep^62 ≈ processJumpDivstep`
- Rewriting the convex hull to track jump-step transitions
- This is research-level work but would make the certificate ~60x smaller

## Strategy 4: Binary search on N (finding tight bound)

The tight bound might be significantly less than 1075. If N=1050 works,
the computation is ~5% faster. Binary search:

```bash
# Each test takes ~2.5 hours, so 10 binary search steps = ~25 hours
# But tests can be parallelized: run N=1050,1060,1070,1080 simultaneously
for N in 1050 1060 1070 1080; do
  sbatch --job-name=divstep-$N slurm_certificate.sh $N
done
```

## Recommended approach

Combine strategies 1 + 4:
1. Binary search for tight N (parallel SLURM jobs)
2. Once N is known, use checkpointing with K=50 segments
3. Run segments in parallel on SLURM (each ~1 min)
4. Chain the results

**Expected total time**: ~1 hour parallel, vs days serial.
