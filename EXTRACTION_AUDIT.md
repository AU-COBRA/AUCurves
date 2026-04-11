# Extraction Audit — BN254 Safe-Rust

**Date:** 2026-04-11

## Finding: Drift between Rocq extraction and generated Rust

The Rocq extraction of `safe_cmd` from `ToSafeRustBody.v` (captured in `bn254_safe_tower_rocq.rs.out` on 2026-04-09) differs from the actual `bn254-safe-rust/generated/bn254_safe_tower.rs` by 99 lines across 3 regions.

### Drift #1: `bn254_make_line` function rewritten

**Rocq extraction (buggy):**
```rust
bn254_Fp2_mul(&mut out.c0.c0, &lam, &x_t);
let __ac0 = out.c0.c0.clone();
bn254_Fp2_sub(&mut out.c0.c0, &__ac0, &y_t);
bn254_Fp2_mul_fp(&mut tmp, &lam, &x_p);
bn254_Fp2_opp(&mut out.c0.c1, &tmp);
// ...
bn254_from_word(&mut out.c1.c0.c0, 0u64);
bn254_from_word(&mut out.c1.c0.c1, 0u64);
bn254_felem_copy(&mut out.c1.c1.c0, &y_p);
bn254_from_word(&mut out.c1.c1.c1, 0u64);
```

**Generated Rust (hand-fixed):**
```rust
// Sparse line in Fp12 with basis (1, v, v^2, w, vw, v^2w):
//   line = y_p + (-lam*x_p)*w + (lam*x_t - y_t)*w^3
// c0.c0 = (y_p, 0)  -- w^0 (constant term)
bn254_felem_copy(&mut out.c0.c0.c0, &y_p);
bn254_from_word(&mut out.c0.c0.c1, 0u64);
// c0.c1 = 0, c0.c2 = 0  -- w^2 and w^4 terms
// c1.c0 = -lam*x_p  -- w^1
bn254_Fp2_mul_fp(&mut tmp, &lam, &x_p);
bn254_Fp2_opp(&mut out.c1.c0, &tmp);
// c1.c1 = lam*x_t - y_t  -- w^3
bn254_Fp2_mul(&mut out.c1.c1, &lam, &x_t);
let __ml0 = out.c1.c1.clone();
bn254_Fp2_sub(&mut out.c1.c1, &__ml0, &y_t);
```

**Root cause:** The bedrock2 source `BN254_Pairing.v` has `make_line` with incorrect Fp12 basis ordering. The `(w^0, w^2, w^4)` vs `(w^1, w^3, w^5)` components are swapped.

### Drift #2: `bn254_load_q1_y_const` function added

**Generated Rust (new, not in Rocq extraction):**
```rust
// xi^((p-1)/2) in F_{p^2}, Montgomery form
pub fn bn254_load_q1_y_const(mut out: &mut Fp2) {
    out.c0.0[0] = 16482010305593259561u64;
    // ...
}
```

### Drift #3: Optimal-ate Miller loop Frobenius corrections added

**Generated Rust (new, not in Rocq extraction):**
After the main Miller loop (`T = [6u+2]*Q`), two additional line evaluations:
- At `Q1 = pi_p(Q)`
- At `-pi_p^2(Q)`

These correspond to the Frobenius corrections for the BN254 optimal ate pairing.

**Root cause:** `BN254_Pairing.v` implements the naive Miller loop but omits the optimal-ate corrections.

## Impact on the verification chain

The `SafeRustSimulation.v` → `SafeRustBN254Concrete.v` chain proves:
> For any `cmd_clean` bedrock2 source program `c`, `bn254_safe_cmd_correct` shows `rust_exec (btranslate c)` mirrors `bedrock_exec c` when using the concrete BN254 leaf_spec.

**What this DOES NOT guarantee:** that the bedrock2 source `c` itself is mathematically correct for the BN254 optimal-ate pairing. The chain verifies that the Rust translation preserves whatever the source says; if the source is buggy, the Rust is equivalently buggy.

**Current state:**
- The chain correctly proves that the Rocq-extracted Rust (buggy `make_line`, missing corrections) = the bedrock2 source `BN254_Pairing.v`.
- The actual `bn254-safe-rust/generated/bn254_safe_tower.rs` has been MANUALLY EDITED to fix these bugs. It does NOT match what the Coq chain proves correct.
- The bilinearity tests pass on the hand-edited version.

## Next steps

1. **Fix `BN254_Pairing.v` source:**
   - Correct the `make_line` basis ordering in the bedrock2 source.
   - Add optimal-ate Frobenius corrections to the Miller loop source.
2. **Rebuild `BN254_Pairing.vo` and re-extract:**
   - `dune build fiat-crypto/src/Bedrock/Field/Synthesis/Examples/BN254_Pairing.vo`
   - Run the `ExtractSafeTower.v` to regenerate `bn254_safe_tower_rocq.rs.out`.
3. **Diff against `bn254-safe-rust/generated/bn254_safe_tower.rs`:**
   - After the fix, the diff should be empty (or only cosmetic whitespace).
   - If empty, the Coq chain fully blesses the generated Rust.
4. **Remove hand-edits:**
   - Replace the hand-edited generated Rust with the Coq-extracted version.

## Cross-references

- Related memory: `project_safe_rust_pairing_bugs.md` (known issue from 2026-04 session)
- Chain files: `src/Bedrock/SafeRust{Simulation,LeafRefinement,BedrockBridge,BN254Instance,Concrete}.v`
- Extraction driver: `src/Bedrock/ExtractSafeTower.v`
- Bedrock2 BN254 pairing source: `fiat-crypto/src/Bedrock/Field/Synthesis/Examples/BN254_Pairing.v`
