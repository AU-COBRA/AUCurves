# TFp25519_64 plumbing plan

Closes the ~3.5× per-field-op overhead documented in
`perf-gap-analysis.md`.  The rust_cmd_ed AST currently stores Ed25519
field-element intermediates as `TBytes 40` (40-byte canonical encoding)
slots; every `fe25519_*` leaf round-trips through `fiat_25519_from_bytes`
→ carry op → `fiat_25519_to_bytes`.  Retyping those intermediates to
`TFp25519` (5×u64 limb tuples) eliminates the conversion at every step.

Both `TFp25519` (5×u64 radix-2^51) and `TFp25519_64` (4×u64 saturated)
already exist in `AUCurves/src/Bedrock/SafeRustEd25519Tower.v`.  The
`RustCmdToRust.v` emitter already maps them to `[u64; 5]` / `[u64; 4]`
Rust array types.  The plumbing gap is on the AST side: bodies still
use `TBytes 40`.

## Pieces

### 1. Rust leaf shim — `fe25519_limbs.rs` (this commit)

Parallel `fe25519_*_limbs(out: *mut u64, ...)` exports for the 9 field
ops used by `XyztAddBodyDecomposed.v` + `XyztDoubleBodyDecomposed.v`.
Skip `read_tight`/`write_tight`.  Activated by `--features tfp25519_limbs`.

Predicted per-op cost (Zen 4): ~12 ns for `mul`, matching the
`fe25519_micro/fiat5x51_carry_mul_bare` row.  Saves ~30 ns per op vs
the byte shim.

No callers in tree yet — the AST still emits `*mut u8`.  This shim is
inert under default features.

### 2. rust_cmd_ed body retyping (Rocq side, ~1 week)

Files to touch:

  - `End2End/Ed25519/XyztAddBodyDecomposed.v` — 23 `TBytes 40` slots → `TFp25519`.
    The `LE40` helper (line 80) becomes `LE_TFp25519`.  All 18 `REdCall`
    sites and 2 `REdCallN "fe25519_unpack_xyzt5"` + 1 `REdCallN
    "fe25519_pack_xyzt5"` keep their structure; only the slot types change.

  - `End2End/Ed25519/XyztDoubleBodyDecomposed.v` — same pattern, 7 field-op
    slots.

  - Leaf specs in `End2End/Ed25519/CurveBodies.v` (or wherever the
    `function_table_ed` fnspecs for `fe25519_mul` etc. live): change
    input/output slot types from `TBytes 40` to `TFp25519`, and update
    the semantic post-condition to relate `VFp25519 limbs` values
    rather than `VBytes 40 bs` byte arrays.

  - Semantic correctness proofs in `*BodyDecomposed.v`: the algebraic
    arguments are unchanged (operations are still field mul/add/sub/sqr
    on `F p`), but the bedrock2-level intermediate state mapping needs
    to use `VFp25519`-shaped `slot_holds` predicates.  Estimated ~200
    LoC of proof updates per body.

### 3. unpack_xyzt5 / pack_xyzt5 retyping

These two leaves bridge the 200-byte XYZT point slot (`TBytes 200`)
with the 5 field-element slots.  Today both endpoints are `TBytes 40`;
post-retype, the field-element side becomes `TFp25519`.

The leaf body must therefore parse 200 bytes into 5×u64 limb arrays
(currently it's just `memcpy` 5×40 bytes).  Equivalent to inlining 5×
`fiat_25519_from_bytes` into `unpack_xyzt5`, and 5× `fiat_25519_to_bytes`
into `pack_xyzt5`.  Same total work as before, just relocated from
per-op to per-add.

Net savings: 18 ops × 30 ns per add saved at the per-op layer, minus
5 from_bytes + 5 to_bytes added per add at the unpack/pack layer
(≈ 200 ns added).  Net per-add savings: 18×30 − 200 = **340 ns**
(63% reduction in per-add FFI conversion overhead).

### 4. Extraction + Rust shim wire-up

  - `AUCurves/src/Bedrock/ExtractCurveBodies.v` re-runs against the
    retyped bodies; emits `decomposed_bodies.rs` with `[u64; 5]` arrays
    and `*mut u64 / *const u64` extern signatures.

  - `curve25519-jasmin-rs/src/ed25519_rustcmd/decomposed_bodies.rs`
    rewritten on AST re-extraction.  Calls `fe25519_*_limbs` (this
    commit's shim).

  - `curve25519-jasmin-rs/src/ed25519_rustcmd/fe25519_portable.rs`
    deprecated for the field-op exports (kept only for unpack/pack/copy).

### 5. Predicted bench impact

Per `perf-gap-analysis.md`:

  - `wnaf_comb_leaves` sign 70 µs → ~25 µs (eliminates ~35 µs of FFI shim cost).
  - `wnaf_comb_leaves` verify 200 µs → ~70 µs (same factor, 3× more adds).

This lands the framework at parity with `dalek_leaves` (27/59 µs).
Closing the remaining gap to dalek-native (13/22 µs) requires keeping
points unpacked across calls too — i.e., retiring the 200-byte XYZT
slot in favour of a typed `XYZT { X, Y, Z, T : TFp25519 }` slot — that's
a follow-on track.

## Order of operations

1. **(this commit)** Rust leaf shim + Cargo feature `tfp25519_limbs`.  Inert.
2. Hand-write a parallel `decomposed_bodies_limbs.rs` (no AST re-extraction
   yet) — proves the integration via KAT + bench.  Builds confidence
   that the perf hypothesis carries through at the full-protocol level.
3. AST retyping + proofs (the heavy lift, ~1 week of Rocq).
4. Re-extract Rust + wire under `tfp25519_limbs`.
5. Update bench analysis once numbers land.
