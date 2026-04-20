# rust_cmd vs bedrock2: Generated Code Performance

## Summary

Code translated from `rust_cmd` is approximately as fast as code generated from
bedrock2.  The `rust_cmd` layer only *orchestrates* calls to field primitives —
the hot path is identical in both approaches.

## Why performance is equivalent

`g1_add` is 13 calls (`fp_mul`, `fp_add`, `fp_sub`); wall time is dominated by
those leaf implementations, not by the calling code.  Whether the leaves come
from fiat-crypto, CryptOpt, or Jasmin, they are the same object in both paths.

Both compilation routes end up at LLVM:

| Source path | Compiler chain |
|-------------|----------------|
| bedrock2 → C | Clang → LLVM backend |
| rust_cmd → safe Rust | rustc → LLVM backend |
| bedrock2 → Jasmin | jasminc → x86-64 asm |
| rust_cmd → Jasmin (via JasminBridgeReal) | jasminc → x86-64 asm |

## Extra temporaries: cost analysis

Rust's borrow checker forbids `fp_sub(&mut X3, X3, t1)` — `X3` cannot be
borrowed both mutably and immutably in the same call.  `rust_cmd` programs
therefore require fresh destination variables at every step.

`g1_add` needs ~6 extra temporaries (`t0..t5`) compared to a bedrock2
implementation that allows in-place updates.  Concrete cost:

- **Stack pressure:** ~6 × 48 bytes = 288 bytes of extra frame space (BLS12 Fp).
  Negligible.
- **Copy cost:** LLVM SRoA (Scalar Replacement of Aggregates) eliminates
  fixed-size array copies across call boundaries at `-O2`.  A `[u64; 6]`
  "copy" becomes 6 register moves; LLVM further eliminates those that die before
  use.
- **Measured overhead:** indistinguishable from C-extracted bedrock2 in the
  `bls12-jasmin-rs` benchmarks (1.95 ms pairing).

## The one genuine difference

bedrock2 C code can write `fp_mul(dst, src, src)` (in-place squaring reusing a
pointer).  `rust_cmd` must dispatch through a dedicated `fp_sqr` leaf.

This is actually *beneficial* when `fp_sqr` is separately optimised (e.g.
CryptOpt generates a tighter squaring circuit than calling `fp_mul` with equal
args).  When only `fp_mul` exists, the `rust_cmd` version adds one extra pointer
read — immeasurable.

## Proof-engineering cost comparison

| Criterion | bedrock2 WP | rust_cmd + borrow_ok |
|-----------|-------------|----------------------|
| Memory-safety proof per function | ~400 lines sep-logic | 0 lines (one `reflexivity`) |
| Frame theorem per input variable | Manual per-call chain | `seq_frame` + `firstorder discriminate` |
| In-place updates allowed | Yes (with aliasing proof) | No (fresh dest required) |
| Rupicola compatibility | Direct target | New lowering pass needed |
| Code size (orchestration) | Compact | ~10% more (extra temp vars) |

## Rupicola targeting

`rust_cmd` could be a Rupicola compilation target.  Rupicola already lowers
Gallina to bedrock2 `cmd`; a second path would lower to `rust_cmd` instead.
The main challenge is translating Rupicola's pointer-based mutation model into
named-variable ownership (`RCall` destinations).  The borrow checker here
(`borrow_ok`) would then replace Rupicola's aliasing side conditions
automatically — a net reduction in proof burden.
