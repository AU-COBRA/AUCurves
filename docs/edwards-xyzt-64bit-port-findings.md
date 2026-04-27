# EdwardsXYZT64.v port — accumulated findings

Session log capturing the technical discoveries from porting upstream's
32-bit Edwards XYZT atoms to AUCurves' 64-bit field representation.
Pairs with `SSProve-lean/docs/option-b-64bit-port-plan.md` (which has
the strategic plan) and serves as the practical "what to know" guide
for whoever picks this up next.

**File:** `AUCurves/src/Bedrock/End2End/Ed25519/EdwardsXYZT64.v` +
loader `EdwardsXYZT64_Imports.v`

**Status (2026-04-27):** Sub-tasks 1.1 – 1.4 closed. Sub-task 1.5
(four `_ok` proofs) at 5-of-7 calls in `to_cached64_ok`. See bottom
for the marker.

---

## Discoveries (in approximate order they were hit)

### 1. MCP times out on heavy-import files → file-split pattern

PET (rocq-mcp's Coq backend) has a 600-second file-load timeout.
EdwardsXYZT64.v's full import chain (fiat-crypto Rewriter +
AbstractInterpretation + Translation + bedrock2 ProgramLogic +
upstream EdwardsXYZT.vo at 3.8 MB) hits it.

**Fix:** split into a heavy-imports loader (`EdwardsXYZT64_Imports.v`)
that uses `Require Export`, plus a thin content file
(`EdwardsXYZT64.v`) that only `Require Import`s the loader. Once the
loader's `.vo` is built once, MCP loads the content file in seconds.

Memory: `feedback_mcp_timeout_heavy_imports.md`

### 2. `program_logic_goal_for_function!` macro silently fails on Section-local instances

The macro extracts callee specs via `instance_of (spec_of $f)`
typeclass search. Upstream's `spec_of_fe25519_sub` etc. are declared as
`Local Instance` inside a `Section`. After section close the constants
survive but the typeclass *hints* die.

**Symptom:** `Failed to recurse into the following command, consider
reducing it before calling program_logic_goal_for: bedrock_func_body:(...)`.
Misleading — the real cause is the inner `instance_of` failing inside
`callee_specs`, and Ltac2's match fall-through gives this confusing
error.

**Fix:** `Existing Instance Crypto.Bedrock.End2End.X25519.EdwardsXYZT.spec_of_fe25519_sub.`
(once per callee). For 64-bit specifically, see point 5 below — the
upstream specs are width-locked at 32-bit, so re-Existing them isn't
enough; you need fresh declarations.

Memory: `reference_program_logic_section_instances.md`

### 3. `firstn`/`skipn` shadowing between `Stdlib.ListDef` and `coqutil.Map.SeparationLogic`

Stdlib's `firstn_skipn` lemma (`firstn n l ++ skipn n l = l`) rewrites
the goal using `ListDef.firstn` and `ListDef.skipn`. But bare
`firstn`/`skipn` in our scope resolves to coqutil's versions (also in
scope via the bedrock2 stack).

**Symptom:** `seprewrite_in` of a sep-equality built using bare
`firstn` fails with "failed to find ... in ...", and the printed forms
look identical because the pretty-printer hides the qualifier.

**Fix:** in helper Ltac (`split_stack_at_n_in`), use fully-qualified
`ListDef.firstn` / `ListDef.skipn` when constructing the term to
seprewrite. The helper now takes both `n_nat : nat` and `n_z : Z`
explicitly because `map.of_list_word_at_app_n` needs Z while `firstn`
needs nat (no automatic coercion in this scope).

Memory: `reference_firstn_skipn_shadowing.md`

### 4. `seprewrite_in` rejects direct lemma applications

Calling `seprewrite_in (felem_from_bytes p bs HL) H6` directly fails
with "No matching clauses for match". The `multimatch`/`unshelve` in
seprewrite_in's implementation can't process a lemma application that
already has its side conditions discharged.

**Fix:** two-step: `pose proof (felem_from_bytes p bs HL) as Hiff;
seprewrite_in Hiff H6.`

### 5. Upstream `spec_of_fe25519_*` are 32-bit-only

`fiat-crypto/.../X25519/EdwardsXYZT.v`'s section sets `Bitwidth32` +
`Naive.word32`. All `Local Instance spec_of_fe25519_*` baked under
that context have `word.rep 32` types. They cannot type-check against
our 64-bit `p_out : @word.rep 64 word`.

**Symptom:** spec instantiation fails with "p_out has type @word.rep
64 word while expected @word.rep 32 word32".

**Fix:** declare fresh 64-bit instances using `Crypto.Bedrock.Specs.Field`'s
`spec_of_BinOp` / `spec_of_UnOp` / `spec_of_felem_copy` / `spec_of_from_word`
combinators. These pick up `frep25519` (the 64-bit FieldRepresentation)
from our loader's `Existing Instance` and produce 64-bit specs.

For `fe25519_half`, no synthesized impl exists in fiat-crypto; we
mirror upstream's spec shape verbatim except width-polymorphic, as
`spec_of_fe25519_half64`.

### 6. The byte-array precondition recipe

`spec_of_BinOp` (Crypto.Bedrock.Specs.Field line 113) has precondition
`(out$@pout * Rr)%sep mem` where `out : list byte`. After
`split_output_stack`, our `H6` has `(firstn 40 out)$@p_out` etc.
Extensionally these match, but the unifier picks `?x : felem` for the
output evar (because the postcondition has `FElem pout out * Rr`
shadowing back).

**Recipe to bridge it (verified for first 5 calls of to_cached64_ok):**

```coq
(* Step 1: split bytes *)
split_output_stack out p_out 4.
repeat straightline.

(* Step 2: per-chunk pre-conversion *)
assert (HL_k : length bs_k = Z.to_nat felem_size_in_bytes) by
  (rewrite firstn_length(, skipn_length); change felem_size_in_bytes with 40%Z; listZnWords).
pose proof (felem_from_bytes p_offset_k bs_k HL_k) as Hiff_k.
seprewrite_in Hiff_k H6.
(* repeat for all 4 chunks *)

(* Step 3: per-call discharge *)
single_step;
  try (use_sep_assumption; cancel; cancel_seps_at_indices 0%nat 0%nat;
       [reflexivity|]; cancel).
```

`bs2felem` and `felem_from_bytes` are in `Crypto.Bedrock.Specs.Field`
(line 382 / 413).

### 7. The remaining blocker: nested-seps Hint Extern

The Hint Extern at `Specs/Field.v:525`:

```coq
Hint Extern 1 (Lift1Prop.impl1 (FElem ?px ?x) (sepclause_of_map (map.of_list_word_at ?px _)))
  => (rewrite felem_to_bytes; exact impl1_refl) : ecancel_impl.
```

fires only when the WHOLE goal is `Lift1Prop.impl1 (FElem ...)
(sepclause_of_map ...)`. After the first 5 calls of `to_cached64_ok`
succeed, calls 6-7 (`fe25519_mul` writing to `p_out.+120`,
`fe25519_copy` writing to `p_out.+80`) hit a discharge where the
goal is in nested-sep form:

```
Lift1Prop.impl1 (seps [FElem (p_out.+120) x3 :: ... ]) (seps [sepclause_of_map ... :: ?Rr :: nil])
```

The hint doesn't fire on this shape, and `cancel_seps_at_indices 0%nat 0%nat;
reflexivity` fails because the FElem→bytes rewrite isn't applied.

**Investigated but not solved:** `use_sep_assumption_impl` (not in
scope without qualifier we couldn't find), `setoid_rewrite` of
felem_to_bytes (timeout), `cbv [FElem]` to unfold then ecancel
(introduces `array scalar` form that doesn't match either).

**Suggested next angle:** `Crypto.Bedrock.Field.Interface.Compilation2.v`
line 84 has `prove_field_compilation := repeat straightline'; handle_call;
lazymatch goal with | sep _ _ _ => ecancel_assumption_impl | _ => idtac
end; ...`. The `ecancel_assumption_impl` and `handle_call` are likely
the right tools — they're used for Rupicola compilation but the
underlying Hint database is the same. Worth importing those into our
scope and trying the discharge with them.

---

## Reusable patterns (for the other 3 _ok lemmas)

`add_precomputed64_ok`, `double64_ok`, `readd64_ok` should each share
this skeleton once 1.5 is unblocked:

```coq
Lemma <foo>_ok : program_logic_goal_for_function! <foo>.
Proof.
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub
      bin_carry_sub un_outbounds bin_outbounds].
  repeat straightline.
  pose proof (<implies_coords_valid> (<m1_op> (coords_to_point a))) as HPost.
  destruct_points.
  split_output_stack out p_out <4|5>.
  repeat straightline.
  (* per-chunk felem_from_bytes pre-rewrite, see recipe above *)
  (* repeat single_step + discharge *)
  (* postcondition: unshelve eexists; ... ; congruence *)
Qed.
```

The variable `a` (not `a0` like upstream) — our `Local Notation a := Curve25519.E.a`
doesn't bind a hypothesis, so straightline names the projective_coords
parameter `a` directly.

---

## Open work checklist

1. [ ] Solve discharge for nested-seps Hint Extern (Section 7 above).
2. [ ] Close `to_cached64_ok` end-to-end.
3. [ ] Apply same recipe to `add_precomputed64_ok` (5 chunks, more calls — possibly more side conditions).
4. [ ] Apply to `double64_ok`.
5. [ ] Apply to `readd64_ok`.
6. [ ] Move on to Step 2 of the plan: `ed25519_scalarmult_base` (the big one).
