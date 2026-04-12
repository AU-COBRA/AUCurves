# Plan: Close the Formal Refinement Gap (bedrock2 → safe Rust)

## Current state

The verification chain has a **gap** between the bedrock2 source (fully proven in Coq)
and the safe Rust that actually executes:

```
Math spec ──Qed──> bedrock2 source ──Qed──> WP proofs
                                       │
                                    GAP (unverified OCaml translator)
                                       │
                               generated/bn254_safe_tower.rs → executable
```

### What's proven (0 Admitted, 0 Axiom)

| File | Theorem | Status |
|------|---------|--------|
| SafeRustSimulation.v | `safe_cmd_correct`: bedrock2 exec ⟹ Rust exec via `btranslate` | Qed |
| SafeRustBN254Concrete.v | `bn254_tower_correct`: instantiated for BN254 leaf ops | Qed |
| SafeRustLeafRefinement.v | `bn254_safe_cmd_correct` + 30 tower-level eval lemmas | Qed |
| SafeRustBedrockBridge.v | `bedrock_equiv` + leaf refinement lifters | Qed |
| BN254_PairingHelpers.v | `bn254_make_line_corrected_ok` (D-twist WP proof) | Qed |
| BN254_PairingTopOptimal.v | `bn254_pairing_dsd_optimal_ok` | Qed |

### What's NOT proven

1. **`btranslate` = the OCaml `bn254_safe_tower.ml`**: The Coq `btranslate` function
   (in ToSafeRustBody.v) and the OCaml generator (bn254_safe_tower.ml) are TWO SEPARATE
   implementations of the same translation. The simulation theorem proves `btranslate`
   correct; the executable .rs comes from the OCaml. Nothing connects them.

2. **`bn254_miller_loop_optimal_ok`**: Setup verified, body Admitted (~100 LoC remaining
   with wp_call_step tactic).

3. **Hand edits to generated .rs**: The D-twist make_line fix, Frob corrections,
   and load_q1_y_const are hand-written in the .rs. These are outside the Coq boundary.

## Plan

### Phase 1: Use Coq extraction of `btranslate` (eliminates the OCaml translator)

**Goal**: Replace the OCaml `bn254_safe_tower.ml` with a pipeline that runs the
Coq-verified `btranslate` from `ToSafeRustBody.v` via Coq extraction.

**Steps**:
1. In `ExtractSafeRust.v`, extract `btranslate` and `safe_rust_module` from
   `ToSafeRustBody.v` alongside the bedrock2 function list.
2. Write a thin OCaml driver (~30 lines) that applies the extracted `safe_rust_module`
   to `bn254_all_funcs` and writes the output to a .rs file.
3. Verify the output matches the hand-edited .rs (modulo formatting).
4. Delete `bn254_safe_tower.ml` — it's now redundant.

**Result**: The generated .rs is produced by `btranslate`, which is the SAME function
that `safe_cmd_correct` proves correct. The gap shrinks to: Coq Extraction + Rust compiler.

**Estimated effort**: 1-2 days.

### Phase 2: Close `bn254_miller_loop_optimal_ok` (Admitted → Qed)

**Goal**: The WP proof for `bn254_miller_loop_optimal` is the last Admitted in the
pairing chain.

**Current state**: Setup done, `wp_call_step` tactic working, `fp12_set_one_wp` lemma
stated (Admitted). Estimated ~100 LoC remaining.

**Steps**:
1. Prove `fp12_set_one_wp` (~300 LoC one-time). This eliminates 300 LoC per Miller
   loop proof and is reusable across curves.
2. Write the loop body proof using `wp_call_step` (~30 lines, one per call).
3. Write the loop invariant + induction (~20 lines, using `Loops.while_localsmap`).
4. Write the Frobenius corrections section (~27 lines, using `wp_call_step`).
5. Stack deallocation + final copy (~13 lines).

**Result**: `bn254_miller_loop_optimal_ok` is Qed. Combined with
`bn254_pairing_dsd_optimal_ok` (already Qed), the FULL optimal-ate pairing
has a bedrock2 WP proof.

**Estimated effort**: 3-5 days (dominated by `fp12_set_one_wp`).

### Phase 3: Prove `btranslate` output = generated .rs (bit-exact)

**Goal**: A Coq theorem stating that `Eval vm_compute in safe_rust_module bn254_all_funcs`
produces the EXACT string that's in `generated/bn254_safe_tower.rs`.

**Steps**:
1. Add `Eval vm_compute in safe_rust_module bn254_all_funcs` to a test file.
2. Compute the SHA-256 hash of the output in Coq (or check string equality).
3. Compare against the hash/content of the committed .rs file.
4. This is a Qed proof that the generated .rs = `btranslate` applied to the source.

**Result**: The EXECUTABLE matches the VERIFIED translation. The gap is now:
Coq kernel + Rust compiler (+ Jasmin for leaf ops).

**Estimated effort**: 1 day (mostly vm_compute time for the large string).

### Phase 4: Connect L4 wiring to the refinement chain

**Goal**: Chain the `BridgingLemmas.affine_miller_aux_morphism` (any FieldOps
homomorphism lifts through the Miller loop) with `bn254_tower_correct` (bedrock2
exec = Rust exec) to get:

```
Theorem bn254_pairing_end_to_end :
  forall Px Py Qx Qy,
    pairing_optimal_rust Px Py Qx Qy =
    optimal_ate_spec bn254_params gamma1 gamma_y gamma1_p2 Px Py Qx Qy.
```

**Steps**:
1. Define `pairing_optimal_rust` as the composition: run `bn254_pairing_dsd_optimal`
   via `rust_exec`, extract the Fp12 output, apply `fp12_to_Z`.
2. Prove it equals `optimal_ate_spec` by chaining:
   - Phase 2's WP proof (bedrock2 source computes the right F-level values)
   - `BridgingLemmas.affine_miller_aux_morphism` (F-level → Z-level)
   - `MillerLoopWP.L4_via_bridge` (cont_inv at exit → L4 obligation)
   - Phase 3's bit-exact check (generated Rust = `btranslate` of source)

**Result**: End-to-end theorem connecting the executable Rust to the math spec.
TCB = Rocq kernel + Rust compiler + Jasmin.

**Estimated effort**: 1-2 weeks.

## Summary

| Phase | Deliverable | Eliminates from TCB | Effort |
|-------|-------------|---------------------|--------|
| 1 | Use Coq `btranslate` for extraction | OCaml `bn254_safe_tower.ml` | 1-2 days |
| 2 | `bn254_miller_loop_optimal_ok` Qed | Admitted in WP chain | 3-5 days |
| 3 | `btranslate` output = .rs (bit-exact) | Hand edits to .rs | 1 day |
| 4 | End-to-end theorem | — (connects all pieces) | 1-2 weeks |

After all 4 phases: **TCB = Rocq kernel + Rust compiler + Jasmin compiler**.
The entire path from math spec to executable is formally verified.
