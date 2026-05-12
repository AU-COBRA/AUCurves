# Architectural gap inventory: Ed25519 sign perf vs dalek

Audit of AUCurves and catcrypt-bench for assets that could close the
architectural gap between the framework-extracted Ed25519 sign path
(~527 µs at B1) and dalek (~20 µs). Research only; no code changes.

Three classes of asset are surveyed: (1) wNAF windowing, (2) precomputed
base-point tables, (3) cross-leaf inlining infrastructure. For each:
what exists, what is reusable for Ed25519 specifically, and what would
have to be ported or written. The report ends with a recommendation
between body-level fixes (B3-B5) and committing to the Option C
(Jasmin extraction) path.

## §1. wNAF inventory

### Files

All Rocq-side wNAF assets are concentrated under `src/Bedrock/Field/Synthesis/Examples/`:

```
wNAF.v                                — generic wNAF expansion / weighted sum / correctness
wNAF_ScalarMult.v                     — GLV-style scalarmult spec (two scalars)
wNAF_SingleScalar.v                   — single-scalar Horner-form spec
wNAF_Single_HornerAlgebra.v           — Horner step lemmas (generic)
wNAF_Single_LoadAndProcess.v          — bedrock2 sep bullet load+process (Qed)
wNAF_Single_LoopBody.v                — bedrock2 single iteration body (Qed)
wNAF_Single_Proof.v                   — single-scalar bedrock2 top theorem (Qed)
wNAF_GLV_Func.v                       — GLV functional spec
BLS12_wNAF_HornerAlgebra.v            — BLS12-specialised Horner
BLS12_wNAF_LoadAndProcess.v           — BLS12 sep bullet (Qed)
BLS12_wNAF_ProcessDigits.v            — BLS12 digit-processing (Qed)
BLS12_wNAF_PointOppInverse.v          — table-entry negation (Qed)
BLS12_wNAF_GLV_LoopBody.v             — BLS12 GLV iteration body (Qed)
BLS12_wNAF_GLV_Closed.v               — BLS12 GLV closure lemma (Qed)
BLS12_wNAF_GLV_Proof.v                — BLS12 GLV top theorem (Qed)
BLS12_wNAF_GLV_Instance.v             — BLS12 instance (Qed)
BLS12_wNAF_GLV_Instance_Final.v       — concrete-R0 upper-chain (Qed)
BLS12_wNAF_Extract.v                  — BLS12 extraction
BLS12_377_wNAF_Extract.v              — BLS12-377 extraction
BN254_wNAF_Instance.v / _CurveOps.v   — BN254 single-scalar instance (Qed)
BN256_wNAF_Instance.v / _CurveOps.v   — BN256 single-scalar (Qed)
BN446_wNAF_Instance.v / _CurveOps.v   — BN446 single-scalar (Qed)
BN254_wNAF_Extract.v                  — BN254 OCaml extraction
src/Bedrock/Group/CurveAdd/WNAFTable.v — generic table spec (precompute_w4,
                                          table_select, table_lookup, w=4 plumbing)
src/Bedrock/Group/CurveAdd/PointNegate.v — generic point negation for table flip
```

`bench_ed25519_wnaf.c` in catcrypt-bench is a hand-ported C realisation
of the AUCurves spec; its header literally cites
`AUCurves/src/Bedrock/.../wNAF.v`.  `bench_ed25519_sign.c` also has a
self-contained wNAF (lines 706–745) plus a Straus double-scalar
variant for verify (lines 747+).

### Curve coverage

- **All Rocq wNAF infrastructure targets BN/BLS-family curves over
  short-Weierstrass G1.** The bedrock2 sep predicates (`Point3`,
  `Table4`, `DigitArray`) and the leaf calls (`curve_add_inplace`)
  refer to Jacobian XYZ coordinates and to leaf functions that
  presume the BN254-shaped projective adder.
- **Nothing is specialised to Edwards XYZT** (the Ed25519 coordinate
  system).  The framework would need at least: a `Point4` sep predicate
  (XYZT not XYZ); a `Table_xyzt` analogue; an Edwards version of the
  generic `wNAF.v` table-build (`precompute_w4` doubling + 3 adds — the
  algebra carries over but the leaf-call typing does not).
- Scalar field: `wNAF.v` is generic in `k : Z`, so it does not bake in
  any modulus.  Reduction mod L_curve_order is *not* part of the wNAF
  layer — it happens upstream of `wnaf_digits`. Ed25519 scalars are
  already reduced mod L = 2^252 + 27742317777372353535851937790883648493
  before reaching the scalarmult leaf, so feeding the 32-byte reduced
  scalar to `wnaf_digits` is correct without further changes.

### Reusable today

- **`wNAF.v` (generic expansion)** — 100% reusable for Ed25519. No
  curve-specific assumptions.
- **`wNAF_SingleScalar.v` (Horner-form spec)** — reusable; abstract in
  group `G`.
- **`WNAFTable.v` (table spec, precompute_w4, table_select, negation
  semantics)** — reusable. The `curve_negate` it parameterises over
  must be instantiated with the Edwards negation (negate X and T,
  leave Y and Z).
- **All `BN254_wNAF_Instance`-class files** — *not* reusable. They
  bind to the BN254 G1 leaf surface and the W-form `Point3` sep
  predicate.

### Effort to port

Porting `BN254_wNAF_Instance` → `Ed25519_wNAF_Instance` is **not** a
mechanical `s/BN254/Ed25519/` rename (which worked for BN256/BN446 per
the memory log). The leaf functions differ (`curve_add_inplace` is BN
Jacobian; Ed25519 uses XYZT m1add) and the field representation differs
(short-Weierstrass uses one `Felem`; XYZT carries five 40-byte slots
unpacked into limbs). Realistic effort: ~5–8 agent-days, dominated by
recreating the `Point3`-equivalent sep predicate over the 200-byte
`xyzt` slot and proving the analogue of `wnaf_single_loop_body_ok` over
it.

### Critical answer

The wrapper does *not* reuse byte-for-byte — Ed25519 needs a new
`xyzt`-shaped instance file.  The generic spine (`wNAF.v`,
`wNAF_SingleScalar.v`, `WNAFTable.v`) is fully reusable.

## §2. Base-point table inventory

### Rocq-side assets

- `src/Bedrock/End2End/Ed25519/B_precomputed_64.v` — materialises the
  Ed25519 base point B in *Precomputed* form (3 felems: `half_ypx`,
  `half_ymx`, `xyd`), encoded as a 96-byte LE blob, packed as 12 u64.
  `vm_compute`-derived; round-trip lemmas Qed; `bytes_in_bounds`
  proofs split out for kernel-check hygiene. **This is a single point,
  not a table.**
- `fiat-crypto/src/Curves/Edwards/XYZT/Precomputed.v` — the
  abstract Precomputed-form module: `of_twisted`, `to_projective`,
  `m1add_precomputed_coordinates`, and the soundness lemma
  `m1add_precomputed_coordinates_correct` (a m1add against a Precomputed
  point is equal to a regular m1add against `XYZT_of_twisted`). This
  is the Coq foundation any base-point table would build on.

**There is no analogue of dalek's `ED25519_BASEPOINT_TABLE` (32 KB,
radix-16 over 64 windows, ~8 Precomputed points per window) anywhere
in AUCurves.** No `g_bp_table`, no `bp_radix16`, no Coq-level
materialisation of `[16^i · B][j]` for i ∈ [0,64), j ∈ [1,8].

### catcrypt-bench-side assets

`bench_ed25519_sign.c` (lines 274–315) defines:

- `g_bp_table[64][8]`   — radix-16 fixed-base table, 80 KB, full `Pt`
  form.
- `g_bp_table32[52][16]` — radix-32 variant.
- `g_bp_niels[64][8]`   — Niels-form radix-16, 60 KB.
- `g_bp_table256[32][256]` — radix-256 variant (1.25 MiB) behind
  `USE_RADIX_256_BASEPOINT`.
- `g_bp_odd[WNAF_TBL]` + Niels mirrors — odd-multiple table for Straus
  verify path.

All four are *hand-written C* filled at init time using `ed_scalarmult`
as an oracle. They are not the output of any verified extraction — the
oracle is correct, so the tables are correct, but there is no Rocq
proof that this in-memory blob equals `[k · 16^i · B]`.

### What would need to be generated

To match dalek's `ED25519_BASEPOINT_TABLE` *as a verified artifact*:

1. A Rocq definition `Ed25519_basepoint_table : list (list precomputed_point) :=
   Eval vm_compute in
     map (fun i => map (fun j => of_twisted ((j+1) · 16^i · B)) (seq 0 8)) (seq 0 64)`.
   This is a single `vm_compute` call. Expected wall time: minutes to
   tens of minutes (the inner `B^(big_scalar)` chains through Fermat
   inversion as in `B_precomputed_64.v`).
2. A Rocq lemma that the byte serialisation of this table equals the
   in-memory layout dalek uses.
3. The `Precomputed.m1add_precomputed_coordinates_correct` lemma
   *already proved in fiat-crypto* discharges the per-table-add
   soundness obligation.

So step (1) is mechanical, step (2) is a tedious round-trip lemma, and
step (3) is already done.  Effort: **~3 agent-days** for the verified
table; the `vm_compute` walltime is the main risk and may need
`native_compute` after preheat.

A complementary asset: dalek's table uses *radix-16 signed digits*
(scalar split into 64 nibbles in [-8, 8]), with negation done at table
lookup time. The Rocq side does not yet have a digit-splitter or a
constant-time table-select for the Edwards Niels form; both would have
to be added (~1 day each).

### Critical answer

The framework has the *single-point* Precomputed encoding
(`B_precomputed_64.v`) and the fiat-crypto soundness lemmas, but
*nothing* corresponding to the 32 KB table. The C bench has hand-coded
tables outside the proof chain. Generating a verified table is small
work but currently absent.

## §3. Cross-leaf inlining

### Framework-level (`REdCallFn`)

`SafeRustEd25519Sim.v:446–453` defines `rexec_callfn`: a `REdCallFn fname
dest args` step *looks up the body in `function_table`* and executes the
body's `rust_exec_ed` inline. The proof tactic `safe_cmd_correct_ed`
(file §5) unfolds this lookup at verification time, so for soundness
purposes there is *no boundary* between caller and `REdCallFn` callee —
the body's correctness witness composes directly into the caller's.

This is genuine inlining **at the simulation / proof level**. It is what
makes `safe_cmd_correct_ed` close end-to-end across the 21 REdCall sites
in `ed25519_sign_rs`.

### Emit-level (`RustCmdToRust.v`)

`RustCmdToRust.v:221–230` shows `REdCallFn` and `REdCall` emit
**identical Rust**:

```
indent ++ "unsafe { " ++ fname ++ "(" ++
  join ", " (rs_dest_arg dest :: ...) ++ ") }"
```

with `fname` declared in the `extern "C"` prelude block (lines
~370–420). There is *no `#[inline]` annotation*, no body-paste option,
no per-callsite distinction. The comment at line 221–225 confirms this
is deliberate: "the emitted Rust crate links the helper symbol; the
verification side just tracks whether the body was externally
axiomatized (REdCall) or Rocq-verified (REdCallFn)."

Consequence: LLVM sees 21 `extern "C"` calls in `ed25519_sign`, with
opaque bodies (they're either in `leaves.rs` behind dalek/decomposed
features, or in a separate compilation unit). No inlining across these
boundaries unless LTO is enabled *and* the bodies are in a Rust crate
LLVM can see *and* the boundary type signatures don't break alias
analysis.

The 200-byte raw-pointer signatures used in `decomposed_bodies.rs`
defeat the second condition: every body starts with
`unsafe { &mut *(out_raw as *mut [u8; 200]) }`, which is an opaque
pointer cast LLVM cannot reason through.

### Jasmin-level (Option C)

jasminc's `inline fn` keyword causes the call site to be replaced by
the function body during compilation, **before LLVM IR is generated**.
For a whole-protocol Jasmin extraction of Ed25519 sign:

- All curve / field leaves would be `inline fn` and pasted into the
  caller's basic block.
- LLVM (or jasminc's own asm backend, depending on path) sees the
  flattened body, can perform CSE across what used to be call
  boundaries, can pick MULX vs IFMA tactically based on register
  pressure, can eliminate the `unpack`/`pack` round-trip that the
  decomposed-leaf bodies currently spend per leaf.
- This is essentially how dalek inlines — but enforced by the tool
  rather than relying on `#[inline]` and LTO.

The reference notes `reference_path2_falsified.md` and
`reference_ifma_zen4_falsified.md` already point at whole-protocol
Jasmin as the realistic win path; D4 (whole-protocol Jasmin) is
identified as the "live path" after F4/F5 inline-drop-in approaches
were falsified.

### Critical answer

Framework-level inlining exists (and is what makes the Qed close);
emit-level inlining does **not** exist — `REdCall` and `REdCallFn`
produce identical `extern "C"` Rust today.  Jasmin extraction would
inherit inlining for free via `inline fn`. Adding an
emit-level option to `RustCmdToRust.v` (e.g.
`rs_emit_inline : function_table_ed -> rust_cmd_ed -> string` that
substitutes `REdCallFn` bodies textually) is feasible but requires
re-running the entire proof chain over the inlined AST or proving
`rs_emit_inline_correct`.

## §4. Cost analysis

### Dalek architecture (for reference)

- **wNAF.** Width-5 (signed digits in {±1, ±3, …, ±15}), 8 odd
  multiples per table. Used for variable-base. Width-8 for verify's
  Straus double-scalar (256 odd multiples, only feasible because B has
  its own table).
- **Base-point table.** `ED25519_BASEPOINT_TABLE` is 32 KB: 32 windows
  × 8 Affine-Niels multiples per window, radix-256 (one byte of scalar
  per window). Constant-time lookup with conditional negation.
- **Inlining.** `#[inline]` everywhere through `dalek-cryptography`
  plus LLVM LTO; the radix-256 inner loop becomes one large flattened
  function. Plus AVX2 backend (`Scalar52`, `FieldElement51` carry
  patterns).

### Effort per asset

| Item | Effort (agent-days) | Risk |
|---|---:|---|
| wNAF Ed25519 instance | 5–8 | medium: needs new XYZT sep predicate |
| Base-point table (verified) | 3 | low: `vm_compute` + serialisation |
| Niels lookup + digit split | 2 | low: ports cleanly from C bench |
| Emit-level inlining option | 4–6 | medium: re-prove emit chain |
| Whole-protocol Jasmin (Option C) | 15–25 | high: new build, new Qed chain |

## §5. Projected sign performance and recommendation

### Multiplicative model (rough, optimistic)

- B1 baseline: 527 µs.
- + verified base-point table (skips ~256 doublings on `s·B`):
  expected ~0.3× off → **~370 µs**.
- + wNAF on variable-base side (verify only; sign's variable-base
  cost is small): negligible for sign, ~1.4× for verify.
- + emit-level inlining or LTO bridge (eliminates per-leaf
  pack/unpack of 5×40-byte limbs into the working representation):
  ~0.5× → **~130–180 µs**.
- vs dalek 20 µs → still ~7–9×.

The remaining gap after all three is the *field-arithmetic backend*:
dalek uses hand-tuned `FieldElement51` with AVX2 carry chains; the
framework uses fiat-crypto's portable `unsaturated_solinas` for
`fe25519`. That alone is ~3× on the inner mul/sqr loop, and the
framework can only close it by switching to a different field backend
(libjade's amd64-mulx Jasmin would be the obvious choice).

### Option C (whole-protocol Jasmin)

A whole-protocol Jasmin extraction would inherit:

- `inline fn` for every leaf — automatic cross-leaf inlining, no
  emit-level work needed.
- Direct AVX2 / mulx asm — no field-backend gap.
- Existing Jasmin formosa-25519 X25519 ref5/mulx implementations
  reusable for the field layer (already verified for CT and partial
  functional correctness in formosa-25519/proof).

What Jasmin does **not** inherit: a base-point table. That's a
Jasmin-source-level data structure that has to be written by hand
either way, and the verified-Rocq version of the table generation
above is the same work regardless of whether the consumer is
emitted-Rust or extracted-Jasmin.

### Effort comparison

Sum of "land all three in framework": 14–19 agent-days.
Sum of Option C (Jasmin extraction): 15–25 agent-days.
**Plus** Option C is the only path that closes the field-backend gap;
the body-level fixes do not. After body-level fixes plateau at ~150 µs
(7.5× dalek), Option C is still required to reach parity.

### Recommendation

**Commit to Option C.** The three body-level items together cost
roughly the same as Option C, deliver only ~3.5× of dalek's gap, and
leave the field-backend bottleneck untouched. Option C closes the
field-backend gap as a side effect of using Jasmin sources and gets
cross-leaf inlining "for free" via `inline fn`.

The one body-level item worth landing *anyway* — because it's cheap and
useful to either path — is the verified base-point table (§2). 3
agent-days, low risk, drops sign from ~527 µs to ~370 µs on the
current emit path, and is reusable as a static data table for either
Rust or Jasmin output.

The wNAF Ed25519 instance and the emit-level inlining work are
**not** worth pursuing in isolation: their cost is comparable to
Option C, and Option C subsumes them.

If staffing forces a body-level path (Option C is too disruptive), the
ranking is: base-point table → emit-level inlining → wNAF instance.
The first gives the largest win per agent-day; the last gives the
smallest (~30% of sign cost is variable-base scalarmult, but variable-
base is already optimised in sign because `s·B` is the dominant cost,
not the message-derived scalar).
