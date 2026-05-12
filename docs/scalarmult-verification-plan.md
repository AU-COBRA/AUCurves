# Refined plan: verified `ed25519_scalarmult_base` body

*Refined 2026-05-12, supersedes the original Phase 4 estimate in the
`scalarmult-verification-plan` section of the curve-leaf plan.*

This is the last large axiom-class verification gap. The Gallina spec
landed in commit `7364388` (`ScalarmultBaseVerified.v`) — what's left
is wiring a `rust_cmd_ed` body that compiles to performant safe Rust
and proving it equals the spec.

## Current state — what we don't have to redo

| Foundation | Where | Status |
|---|---|---|
| `ed25519_scalarmult_base_gallina : list byte → list byte` | `ScalarmultBaseVerified.v` | Computable Gallina Definition; produces correct value via Hisil-style double-and-add over 256 bits |
| `ed25519_xyzt_add_gallina` | `XyztAddVerified.v` | Computable; verified add formula in Gallina |
| `ed25519_xyzt_double_gallina` | `XyztDoubleVerified.v` | Computable; verified double |
| `base_point_xyzt` (the generator B as 200B) | `ScalarmultBaseVerified.v` | Constant literal |
| `scalarmult_base_body : function_body_ed` | `ScalarmultBaseBody.v` | Trivial REdCall pass-through (commit `8f5d52a`) |
| `curve_function_table : function_table_ed` | `CurveBodies.v` | 8-entry aggregator (commit `8f5d52a`) |
| `safe_cmd_correct_ed` | `SafeRustEd25519Sim.v` | Qed bridge to bedrock2 |
| `compile_red_for`, `compile_red_select`, `compile_red_callfn` | `RustCmdRupicola.v` | Qed compile lemmas |
| 24+ other Qed compile lemmas | various | Available for the proof |
| `StrongCorrectnessTactics.v` 9 reusable Ltacs | new | Cuts proof boilerplate 30-57% |

**What's NOT yet done:** the actual `rust_cmd_ed` body that performs
the bit-loop using `REdFor`/`REdSelect`/`REdCallFn`, plus the
`body_correct` theorem proving it equals
`ed25519_scalarmult_base_gallina`.

## Three-phase realistic plan (6 weeks → 3.5 weeks)

The original plan estimated 6 weeks for "the math obligation." That
estimate predates the tactics library and assumed we'd need to write
both add/double bodies and the scalarmult bit-loop body from scratch
in `rust_cmd_ed`. The current foundations cut this significantly.

### Phase A — point-op bodies (1.5 weeks)

Replace the trivial pass-throughs in `XyztAddBody.v` /
`XyztDoubleBody.v` with real `rust_cmd_ed` sequences of field
operations.

**Concrete structure** (xyzt_add — 10 field ops):
```coq
Definition xyzt_add_body : function_body_ed :=
  fun dest args => match args with
  | [P1; P2] =>
      (* Allocate 10 scratch felems (each TBytes 40). *)
      REdLetZero "Y1mX1" (TBytes 40) (
      REdLetZero "Y2mX2" (TBytes 40) (
      REdLetZero "A" (TBytes 40) (
      REdLetZero "Y1pX1" (TBytes 40) (
      REdLetZero "Y2pX2" (TBytes 40) (
      REdLetZero "B" (TBytes 40) (
      ... 4 more for C, D, E, F, G, H ...
      (* Extract X1, Y1, T1a, T1b from P1 via REdByteLoad pairs
         OR introduce a new REdSliceCopy constructor. *)
      ... extract per-felem sub-slots ...
      (* Sequence of 10 field-op REdCalls to "fe25519_sub", "fe25519_mul" etc.
         Each REdCall has callee_post matching fiat-crypto's verified spec. *)
      (REdCall "fe25519_sub" Y1mX1 [Y1; X1])
      (REdCall "fe25519_sub" Y2mX2 [Y2; X2])
      (REdCall "fe25519_mul" A [Y1mX1; Y2mX2])
      ...
      (* Repack 5 output felems into dest. *)
      )))))) ))
  | _ => REdSkip
  end.
```

**Proof shape** (`xyzt_add_body_correct`):
```coq
Lemma xyzt_add_body_correct :
  forall callee_post callee_post_n function_table rs rs' P Q dest_var,
    (* Field-op callee_posts are honoured per fiat-crypto specs *)
    fe25519_callees_honoured callee_post ->
    rs_get_tower_ed rs P_var = Some (200B encoded P1) ->
    rs_get_tower_ed rs Q_var = Some (200B encoded P2) ->
    rust_exec_ed callee_post callee_post_n function_table
      (xyzt_add_body (LE_TBytes dest_var 200)
                     [LE_TBytes P_var 200; LE_TBytes Q_var 200])
      rs rs' ->
    rs_get_tower_ed rs' dest_var =
      Some (200B encoded ed25519_xyzt_add_gallina P1 P2).
```

Proof drive: inversion on the 10-step body, applying each `REdCall`'s
fe25519 spec, then prove the Z-level computation produces
`ed25519_xyzt_add_gallina` output. ~400 LoC of inversion + arithmetic
chase. The new tactics (`frame_through_call_conv_with`) handle the
multi-call frame propagation. Estimated 1 week per body × 2 bodies ÷
parallelism = **1.5 weeks**.

**Risk:** the felem-extraction/repacking between the 200B xyzt slot
and the per-felem TBytes 40 slots. Two viable approaches:
1. Add `REdSliceCopy : located_ed → nat → nat → located_ed →
   rust_cmd_ed` (with `body_correct` for the slice semantics) — clean
   but adds a framework constructor.
2. Use 40 `REdByteLoad` / `REdByteStore` ops per felem extraction —
   verbose but stays within existing constructors.

Approach 2 generates 200 byte ops per body call (5 felems × 40
loads). With the tactics library this is mechanical but bloats the
emitted Rust. **Recommend: write approach 2 first, see how the proof
looks, then decide whether REdSliceCopy is worth adding.**

### Phase B — scalarmult bit-loop body (1.5 weeks)

```coq
Definition scalarmult_body : function_body_ed :=
  fun dest args => match args with
  | [scalar; P] =>
      REdLetZero "accum" (TBytes 200) (
      (* Initialize accum to identity point (X=0, Y=1, Z=1, Ta=0, Tb=0) *)
      ... (5 REdByteStore for the Y=1 limb, Z=1 limb) ...
      REdFor "i" 256 (
        (* accum := 2 · accum *)
        REdCallFn "xyzt_double" accum [accum]
        ;;
        (* bit := (scalar[i/8] >> (i%8)) & 1 *)
        REdLetU64 "byte_idx" (SShr (SVar "i") (SLit 3)) (
        REdLetU64 "bit_idx" (SAnd (SVar "i") (SLit 7)) (
        REdByteLoad "byte" scalar (SVar "byte_idx") (
        REdLetU64 "bit"
          (SAnd (SShr (SVar "byte") (SVar "bit_idx")) (SLit 1)) (
        (* tmp := accum + P *)
        REdLetZero "tmp" (TBytes 200) (
        REdCallFn "xyzt_add" tmp [accum; P]
        ;;
        (* accum := bit ? tmp : accum  (CT cmov via REdSelect) *)
        REdSelect (SVar "bit") tmp accum accum
        )))))
      )
      ;;
      (* Copy accum to dest *)
      REdCallFn "xyzt_copy" dest [accum]
      )
  | _ => REdSkip
  end.
```

**Proof shape** (`scalarmult_body_correct`):
- Induction on bit index `i` from 256 down to 0.
- Invariant: at the start of iteration `i`, `accum` equals the partial
  scalar mult of `P` by the high 256-i bits of `scalar`.
- Each iteration: `accum := 2·accum`, then conditionally add `P` based
  on the next bit.
- After all 256 iterations, `accum = scalar · P` = `ed25519_scalarmult_gallina scalar P`.

The math here is straightforward but the proof needs:
- A `scalarmult_invariant : nat → list byte → list byte → list byte → Prop` predicate.
- `scalarmult_step` lemma: invariant preserved by one bit.
- `compile_red_for` + `compile_red_select` + `compile_red_callfn` to discharge each step's `rhoare` triple.

The 1800× Qed speedup at the `compile_red_for` level keeps the inner-loop Qed time at ~1s instead of bedrock2's ~30 min. **Estimated 1.5 weeks** including the invariant statement and the bit-decomposition algebra.

**Risk:** the bit-decomposition lemma chain. Standard fact:
`scalar = Σ_{i=0..255} bit_i · 2^i`. We need:
```coq
Lemma scalar_bit_decomp : forall scalar,
  le_combine scalar = Σ_{i=0..255} (Z.testbit (le_combine scalar) i) * 2^i.
```
Standard but verbose; reuse coqutil's bit-list lemmas where possible.

### Phase C — scalarmult_base specialization + extraction (0.5 weeks)

```coq
Definition scalarmult_base_body : function_body_ed :=
  fun dest args => match args with
  | [scalar] =>
      REdLetZero "B_local" (TBytes 200) (
      (* Initialize B_local to base_point_xyzt — 200 REdByteStore from a constant table *)
      ... 200 REdByteStore ...
      REdCallFn "scalarmult" dest [scalar; B_local]
      )
  | _ => REdSkip
  end.
```

Proof is trivial: invoke `scalarmult_body_correct` with `P =
base_point_xyzt`.

The 200 REdByteStore for the base-point table is unfortunate
(generates ~200 lines of Rust). Optimization: add an
`REdLetConst : var → tower_type_ed → list byte → rust_cmd_ed →
rust_cmd_ed` constructor that allocates and initializes a constant
slot in one shot. Out of scope for the first verified version; add as
follow-up.

**Estimated 0.5 weeks** for body + correctness + extraction wiring.

## Tactic-library extensions needed

The new tactics in `StrongCorrectnessTactics.v` (commit `972fb72`)
were designed for protocol-level proofs with ~3-21 call bodies. The
scalarmult bit-loop is different:

- **256-iteration induction**: needs a `for_loop_invariant` Ltac that
  packages the standard "introduce invariant, prove base + step,
  conclude" pattern. ~30 LoC of Ltac.
- **Field-op call frame**: each `fe25519_mul` etc. has a wider arg
  list than the protocol-level FFI. The existing `frame_through_call`
  should work but needs to be tested. ~10 LoC if extensions needed.
- **Felem extraction Ltac**: a tactic that turns a `slot_holds rs
  P_var (200B encoded P)` hypothesis into 5 separate `slot_holds rs
  P_X_var (40B encoded X)` etc. via the existing `parse_felem` /
  `le_split` pair. ~40 LoC.

These tactic extensions are paid for once and used in both Phase A
and Phase B. **Estimated +0.5 weeks** of upfront tactics work.

## Total: 3.5 weeks (was 6 weeks)

| Phase | Original estimate | Refined estimate |
|---|---|---|
| A. xyzt_add + xyzt_double bodies + correctness | 2 weeks | 1.5 weeks |
| B. scalarmult bit-loop body + correctness | 2 weeks | 1.5 weeks |
| C. scalarmult_base specialization | 1 week | 0.5 weeks |
| Tactics library extensions | (implicit) | 0.5 weeks |
| **Total** | **6 weeks** | **4 weeks** |

The savings come from:
1. Phase 1 Gallina specs already exist (commit `7364388`) — no spec
   work needed.
2. `StrongCorrectnessTactics.v` library cuts per-call proof
   boilerplate ~30-57%.
3. `function_table_ed` scaffolding already in place (commit
   `8f5d52a`) — no plumbing work needed.
4. The 1800× Qed speedup at the protocol-body level continues to
   apply.

## Performance impact after completion

After all three phases land:
- The extracted Rust for `ed25519_scalarmult_base` becomes a single
  Rust function with ~256 inner-loop iterations, each calling verified
  `xyzt_add` / `xyzt_double` bodies. No FFI hops at the protocol level
  (only at the fe25519 field-op leaves, which fiat-crypto provides as
  verified Jasmin).
- Expected speedup over the current dalek-stubbed path: depends on
  fiat-crypto's field-op asm vs dalek's heavily-AVX2-optimized asm.
  Conservative estimate: **0.7-1.0× of dalek** (i.e., between equal
  speed and 30% slower). Real numbers depend on hardware.
- Critically: the result is **end-to-end verified**. No dalek trust.
  Only fiat-crypto's field-op specs + SHA-512 remain trusted.

## Decision points

1. **REdSliceCopy** — add this AST constructor? Saves significant
   verbosity in Phase A but adds framework surface area. Recommend:
   defer until after Phase A draft to see if the 40-load pattern is
   tolerable.

2. **REdLetConst** — add this constructor for the base-point table in
   Phase C? Reduces 200 ByteStores to 1 constant initializer. Probably
   yes; adds maybe 1 day of framework work and saves significant Rust
   output bloat.

3. **Variable-base vs fixed-base scalarmult ordering**: implement
   variable-base `scalarmult_body` first (general), then trivially
   specialize to `scalarmult_base`. Original plan correctly says this;
   confirmed here.

4. **Comb-table optimization** for `scalarmult_base`: skip in initial
   version (focus on correctness). Add as ~1 week follow-up if real-
   world performance matters. The comb table gives ~10× over double-
   and-add on fixed-base scalarmult — significant for batch verify.

## What's NOT in this plan

- **Real fe25519 verified bodies** in rust_cmd_ed. We assume
  fiat-crypto's bedrock2 implementations stay as REdCall sites with
  callee_post matching fiat-crypto's specs. Rewriting fe25519 in
  rust_cmd_ed is a separate multi-month project.

- **Curve25519 Montgomery scalarmult** (for X25519 / DH). Different
  curve, different ladder. Out of scope here; could be added as a
  parallel project after Phase B's verified arithmetic infrastructure
  lands.

- **Constant-time guarantees beyond the CT discipline already in
  `SafeRustEd25519CTLevel.v`**. The bit-loop using `REdSelect` for the
  conditional add is CT-clean by construction (verified at the AST
  level). No additional work needed.

## Recommended landing order

1. Write the tactics library extensions (Phase 0, ~0.5 weeks).
2. Land `xyzt_add_body` + correctness (Phase A.1, ~1 week).
3. Land `xyzt_double_body` + correctness (Phase A.2, ~0.5 weeks).
4. Land scalarmult bit-loop body + correctness (Phase B, ~1.5 weeks).
5. Land `scalarmult_base_body` (Phase C, ~0.5 weeks).
6. Refresh cargo demo to use verified scalarmult instead of dalek
   stubs. Re-run KATs (should still be 12/12). Re-run benchmarks
   — concrete number for "framework vs dalek for the only-fe25519-
   axiomatic version".

Each step lands independently. The framework's axiom count drops to
just `sha512_full_spec` after step 5; everything else is closed.
