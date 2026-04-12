# AUCurves Build Guidelines

## Dune Build Rules

1. **Check for existing builds before starting new ones:**
   ```bash
   ps aux | grep "dune build" | grep -v grep
   ```
   Only ONE `dune build` can hold the `_build/.lock` at a time. Multiple builds serialize and waste time waiting.

2. **Use `-j 1` for heavy files.** BignumShift (4GB), MakeLineBridge (6GB), Secp256k1_G1_Add_Spec (5GB) etc. cannot coexist with `-j 2` on 14GB RAM.

3. **Kill orphan workers** from killed builds:
   ```bash
   ps aux | grep rocqworker | grep -v grep
   ```
   Orphaned `rocqworker` processes eat RAM/swap even after their parent `dune` is killed.

4. **Monitor swap** during builds: `free -h`. If swap exceeds 25GB, kill the heaviest worker immediately.

5. **Don't create `dune-workspace`** at the BLS root — it merges all sub-projects into one lock, causing massive contention between sessions.

## Fast Sep Tactics

All files importing `Crypto.Bedrock.Field.FieldExtensions.WPTactics` automatically use `ecancel_assumption_fast` (O(n) sep solver). If a proof breaks, add locally:
```coq
Local Ltac ecancel_assumption ::= SeparationLogic.ecancel_assumption.
```

## Stack Size

Some proofs need unlimited stack (kernel WHNF-reduces Z.pow on 380-bit exponents):
```bash
ulimit -s unlimited
```
Add before `dune build` if you see "Stack overflow" errors.
