# Generalizing the WP bridge — one file, all primitives

Today the `SafeRustEd25519*.v` files (and their BLS12 counterpart
`SafeRustSimulation.v`) embed the per-primitive type system
directly:

```coq
Inductive tower_type_ed := TFp25519 | TFp25519_64 | TFpL25519 | TBytes (n:nat) | TU64.
Inductive rust_val_ed : tower_type_ed -> Type := ...
Definition tval_ed := { t : tower_type_ed & rust_val_ed t }.
Definition rust_state_ed := ...
Inductive rust_cmd_ed := REdSkip | ... | REdCall (fname : String.string) (dst : located_ed) (args : list located_ed) | ...
Inductive rust_exec_ed (callee_post : ...) : rust_cmd_ed -> rust_state -> rust_state -> Prop := ...
Inductive bedrock_cmd_ed := BEdSkip | ... | BEdCall ...
Inductive bedrock_exec_ed (callee_post : ...) : bedrock_cmd_ed -> rust_state -> rust_state -> Prop := ...
Theorem safe_cmd_correct_ed : ...
Definition state_refine_ed : ...
```

For BLS12, the same shape but with `tower_type_bls12` over Fp/Fp2/Fp6/Fp12.
For ML-KEM, would need polynomial slot types.
For each new primitive: ~2000 LoC of duplicated infrastructure.

## Generalized design

Move the parts that don't depend on the type system into a shared
file `src/Bedrock/RustCmd/Generic.v` parameterized over a
`SLOT_TYPES` module signature.

### `SLOT_TYPES` module signature

```coq
Module Type SLOT_TYPES.
  Parameter type : Type.
  Parameter val : type -> Type.

  (** Each typed slot has a known byte width (used by the
      bedrock2 stackalloc translation). *)
  Parameter type_bytes : type -> nat.

  (** Zero-initialized value for fresh stackalloc slots. *)
  Parameter zero_val : forall t, val t.

  (** Well-formedness predicate (e.g. for [TBytes n], says
      [length bs = n]). *)
  Parameter well_formed : forall t, val t -> Prop.

  Parameter zero_val_well_formed : forall t, well_formed t (zero_val t).

  (** Refinement of a slot's value to a memory region rooted
      at a word-pointer.  For TBytes n: the memory region
      contains the n bytes verbatim. *)
  Parameter slot_refine : forall t, val t -> word -> mem -> Prop.
End SLOT_TYPES.
```

Each primitive instantiates:

```coq
Module Ed25519Slots <: SLOT_TYPES.
  Definition type := tower_type_ed.
  Definition val := rust_val_ed.
  Definition type_bytes (t : tower_type_ed) : nat :=
    match t with
    | TFp25519 => 40 | TFp25519_64 => 32 | TFpL25519 => 32
    | TBytes n => n | TU64 => 8
    end.
  Definition zero_val := tt_zero_ed.
  Definition well_formed := @well_formed_ed.
  Definition zero_val_well_formed := tt_zero_well_formed_ed.
  Definition slot_refine := slot_refine_ed.   (* from BedrockBridge *)
End Ed25519Slots.

Module Bls12Slots <: SLOT_TYPES.
  (* TFp_bls12 | TFp2 | TFp6 | TFp12 with sizes 48/96/288/576 *)
  ...
End Bls12Slots.
```

### Generic command + execution + bridge

```coq
Module RustCmd (T : SLOT_TYPES).
  Inductive type_or_u64 := TyVal (t : T.type) | TyU64.

  Definition tval := { t : T.type & T.val t }.

  Record located := { loc_var : var; loc_type : T.type }.

  Inductive rust_cmd := RSkip | RSeq | ... .   (* unchanged shape *)
  Inductive bedrock_cmd := BSkip | BSeq | ... .

  (* generic state_refine, generic rust_exec, generic bedrock_exec *)

  Theorem safe_cmd_correct :
    forall callee_post c rs1 rs2,
      bedrock_exec callee_post c rs1 rs2 ->
      rust_exec callee_post (btranslate c) rs1 rs2.
  Proof. ... Qed.   (* same proof as today's safe_cmd_correct_ed *)

  Definition wp_bridge_for functions callee_post bc : Prop := ... .

  Theorem bridge_complete :
    forall functions callee_post bc, wp_bridge_for functions callee_post bc.
  Proof. ... Qed.   (* prove once for all primitives *)
End RustCmd.

(* Per-primitive instances are now thin wrappers: *)
Module Ed25519 := RustCmd Ed25519Slots.
Module Bls12 := RustCmd Bls12Slots.
```

Each primitive then has the typed-slot machinery with **zero
boilerplate** — only the protocol-specific `rust_cmd`s and
`strong_callee_post`s.

## What's NOT shared

- **`strong_callee_post` per protocol**: each protocol has its
  own per-leaf Gallina specs (e.g., `sha512_full_spec`,
  `ed25519_compress_spec`).  These stay per-primitive.
- **The protocol's own `rust_cmd` AST** (e.g., `ed25519_sign_rs`).
- **Per-leaf bridges** (`bridge_sha512_64_concrete` etc.) — these
  connect bedrock2 fnspecs to protocol-level callee_post and are
  inherently per-leaf.

## Migration cost

| File | Today | After |
|---|---|---|
| `SafeRustEd25519Tower.v` | ~250 LoC | Replaced by `Ed25519Slots` (~50 LoC). |
| `SafeRustEd25519Sim.v` | ~600 LoC | Replaced by instantiation + `RustCmd` import (~10 LoC). |
| `SafeRustEd25519BedrockBridge.v` | ~400 LoC | Replaced by `state_refine` from `RustCmd` (~10 LoC). |
| `SafeRustEd25519WPBridge.v` | ~250 LoC + 8 axioms | Replaced by `bridge_complete` from `RustCmd` (~10 LoC). |
| `RustCmdToC.v` | ~520 LoC | ~half (emitter is per-primitive due to `c_type_of`, but `bedrock_cmd_ed_to_syntax` etc. become generic). |
| `RustCmdToRust.v` | ~390 LoC | ~half similarly. |

Total per-primitive savings: ~1500 LoC.  For N primitives:
~1500 × (N-1) LoC saved.

## When to do it

Now is the time, before adding the third primitive (BLS12-381
already has its own `SafeRustSimulation.v`, but it's structurally
different enough that retroactive migration is also a reasonable
direction).  ML-KEM, X3DH, Schnorr etc. are downstream candidates;
each would benefit from the generic version.

The migration can be done incrementally:
1. Create `RustCmd/Generic.v` with the module signature and
   stubbed `RustCmd` functor.
2. Migrate Ed25519 first; ensure all existing theorems still go through.
3. Migrate BLS12 (verify the BLS12-specific simulation theorem
   still works).
4. New primitives use the generic functor directly.

Estimate: 1-2 weeks for the full migration; ~1 day for step 1
(infrastructure + Ed25519 mostly working).

## Trade-off vs. doing nothing

Today's per-primitive duplication costs ~2000 LoC and a few hours
of refactoring time per new primitive.  The generic functor pays
~1 week up-front, then ~10 LoC per new primitive.  Break-even at
~2 additional primitives (3 total).

For AUCurves' roadmap (Ed25519 + BLS12 + maybe BLS24 + ML-KEM
+ X3DH bridge + ...), the generic version pays back quickly.

Last updated: 2026-05-09.
