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

1. [x] Solve discharge for nested-seps Hint Extern — DONE via
   `Local Ltac ecancel_assumption ::= ecancel_assumption_impl.`
2. [x] Close `to_cached64_ok` end-to-end — Qed (commit `30621c4`).
3. [ ] Apply recipe to `add_precomputed64_ok`, `double64_ok`,
   `readd64_ok` — BLOCKED on **finding 9** below.
4. [ ] Move on to Step 2 of the plan: `ed25519_scalarmult_base`.

---

## 9. NEW BLOCKER (2026-04-27): stackalloc → `array ptsto` slows single_step

### Symptom

Even ONE `single_step` times out (>120s) on the first call of
`double64_ok`. Not cumulative — the very first call is the slow one.
to_cached64_ok closes in 1.3s; double/add_precomputed/readd hang.

### Difference

`to_cached`'s body has zero `stackalloc`. The other three have many:
double has 8, add_precomputed has 9, readd has 7.

After a `stackalloc`, `straightline` introduces an `anybytes` →
`array ptsto (word.of_Z 1) a stack` clause into the current sep
hypothesis. The next call's spec wants `(?out$@a * ?Rr)%sep` —
but H has the `array` form, not the `$@` (of_list_word_at) form.

The Hint Extern at `Specs/Field.v:525` covers `FElem ↔ $@` but NOT
`array ptsto ↔ $@`. ecancel can't bridge the gap, so it walks the
hint database exhaustively and times out.

### Fix (recipe extension)

`Crypto.Bedrock.Specs.Field` line ~372 has
`array1_iff_eq_of_list_word_at`:

    Lemma array1_iff_eq_of_list_word_at p bs n :
      Z.of_nat (length bs) = Z.of_nat n ->
      Lift1Prop.iff1 (array ptsto (word.of_Z 1) p bs)
                     (sepclause_of_map (bs $@ p)).

This is the missing bridge. Recipe extension:

```coq
Ltac convert_stack_to_byte a stack H :=
  let HL := fresh "HL_stack" in
  let Hiff := fresh "Hiff_stack" in
  assert (HL : Z.of_nat (Datatypes.length stack) = Z.of_nat (Z.to_nat 40)) by lia;
  pose proof (array1_iff_eq_of_list_word_at a stack (Z.to_nat 40) HL) as Hiff;
  seprewrite_in Hiff H.
```

Then call once per `stackalloc` straightline, BEFORE the next
`single_step`. Should restore single_step performance to to_cached64_ok
levels (~1s per call, ~15s total per lemma).

### Status

Diagnosed but not implemented. Adding the helper Ltac + threading it
through the proof per stackalloc is straightforward (~15 LoC of helper
Ltac + ~10 LoC per `_ok` lemma to thread).

---

## 10. UPDATE (2026-04-27, second pass): single_step works → discharge tail blocks

### What worked

The conversion-to-byte-form approach (`convert_stack_to_byte` Ltac
helper) turned out to be unnecessary once we tracked down the root
causes:

1. **Extended `solve_length` for 2^64 bound.** `array1_iff_eq_of_list_word_at`
   has side condition `Z.of_nat (length _) <= 2^width`. At width=32
   `lia` materializes `2^32`; at width=64 it can't materialize `2^64`
   and chains stall. Fix: add a branch chaining through `2^7 = 128`
   (which trivially bounds any 40-byte stackalloc):

   ```coq
   try (match goal with
        | |- (Z.of_nat (Datatypes.length ?l) <= 2 ^ _)%Z =>
            apply Z.le_trans with (Z.pow 2 7);
              [ change felem_size_in_bytes with 40 in *;
                rewrite ?length_firstn, ?length_skipn;
                try (match goal with
                     | H : Datatypes.length l = _ |- _ => rewrite H
                     end);
                try listZnWords; try lia
              | apply Z.pow_le_mono_r; lia ]
        end);
   ```

2. **`first [iff1-form | impl1-form]` for `ecancel_assumption`.**
   The `Local Ltac ecancel_assumption ::= ecancel_assumption_impl.`
   override (needed for to_cached64_ok's nested-seps) is "much slower
   especially when it fails" (per `SeparationLogic.v:524`). Replacing
   the override with a `first [...]` puts the fast iff1-form first
   and the slow impl1-form as fallback. Result: `repeat single_step`
   for double64_ok (12 calls + 8 stackallocs, fully automated via the
   inline `ecancel_assumption_preprocess_with` array→bytes/FElem
   rewrites) closes in **42-97 seconds** of wall time.

   ```coq
   Local Ltac ecancel_assumption_fast :=
     multimatch goal with
     | |- _ ?m1 =>
       multimatch goal with
       | H: _ ?m2 |- _ =>
         syntactic_unify_deltavar m1 m2;
         refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
         solve [ecancel]
       end
     end.
   Local Ltac ecancel_assumption ::=
     first [ecancel_assumption_fast | ecancel_assumption_impl].
   ```

   Note: `Require Import coqutil.Tactics.syntactic_unify` is needed
   in the content file (the Tactic Notation doesn't propagate via
   loader's `Require Export bedrock2.Map.SeparationLogic`).

### New blocker: postcondition discharge

After `Time repeat single_step. repeat straightline. solve_deallocation.`,
the focused goal is `exists _ : map.rep, _` (a pending memory evar
from the WP frame), NOT `exists _ : projective_coords, _` as upstream's
32-bit version expects. Trying upstream's verbatim
`unshelve eexists. eexists (_, _, _, _, _).` fails with:

```
Unable to unify "(?A * ?B2 * ?B1 * ?B0 * ?B)%type"
          with "list (SortedList.parameters.key * SortedList.parameters.value)"
```

(That `list (key * value)` is the locals/memory map representation.)

Tried so far (both fail same way):
- `unshelve eexists; eexists (_, _, _, _, _)` (verbatim upstream)
- `lazy delta [projective_coords]; unshelve eexists; eexists (_, _, _, _, _)`
- `eexists (exist _ (_, _, _, _, _) _)` (skip unshelve, provide witness)

**Path forward (MCP, fast iteration):**
Load EdwardsXYZT64.v in MCP and dump the goal between `solve_deallocation`
and the discharge:

```coq
solve_deallocation.
match goal with |- ?G => idtac "GOAL:" G end. fail.
```

Inspect what `m'` evar is pending and what memory variable it should
bind. Likely fix is one of:
  (a) `eexists last_a_N. split; [ecancel_assumption|]` first,
      then the projective_coords witness, OR
  (b) Extend `solve_deallocation` to also dispatch the m' evar via
      `repeat straightline; eexists; ecancel_assumption` style.

### Status (2026-04-27 EOD)

All three `_ok` lemmas (`double64_ok`, `add_precomputed64_ok`,
`readd64_ok`) committed with `Admitted.` at the discharge tail. The
~150 LoC scaffolding (recipe, helpers, solve_length extension, ecancel
override, single_step through 12-13 calls + 7-9 stackallocs) is all
green for all three. `repeat single_step` timings: double 64s,
add_precomputed 97s, readd 82s. Just the final ~10 LoC of postcondition
discharge is open — same blocker for all three, fix once.

### Working 64-bit pattern from secp256k1 JacobianCoZ.v

Found at `fiat-crypto/src/Bedrock/Secp256k1/JacobianCoZ.v:604` —
`secp256k1_zaddc_ok` is the closest 64-bit analog with stackalloc and
similar postcondition discharge:

```coq
do 25 single_step.
do 4 single_step.
repeat straightline.
dealloc_preprocess. repeat straightline.
exists x11,x23,x7,x19,x0; ssplit. 3-7:solve_bounds.
1,2: cbv [bin_model bin_mul bin_add bin_carry_add bin_sub
          bin_carry_sub un_model un_square] in *.
1,2: cbv match beta delta [zaddc proj1_sig fst snd].
1,2: destruct P; destruct Q; cbv [proj1_sig] in H28, H29.
1,2: rewrite H28, H29; cbv match zeta.
1,2: rewrite F.pow_2_r in *; congruence.
ecancel_assumption.
```

**KEY structural difference**: secp256k1's spec uses **5 separate
`exists` at the top level** (`exists (OX1' OY1' OX2' OY2' OZ' : felem),
... /\ ...`), NOT a single `exists a_double : sigma_type` like our
spec follows upstream EdwardsXYZT.v.

That's why `exists v1,v2,v3,v4,v5` works directly for them and
`unshelve eexists; eexists (_,_,_,_,_)` fails for us — our `unshelve
eexists` introduces an evar of type `projective_coords` (the sigma),
not 5 felem evars. When the goal becomes `?proj : projective_coords`,
`eexists (_,_,_,_,_)` tries to apply a 5-tuple as the witness for the
sigma — but the unifier sees the goal type as `map.rep` (because our
`solve_deallocation` left a pending m' evar at the front).

### Two paths to fix (in priority order)

**Path A: change spec to 5-separate-exists (~30 LoC, fits the working
secp256k1 pattern):** Modify `spec_of_double64`, `spec_of_add_precomputed64`,
`spec_of_readd64` (and re-do `spec_of_to_cached64`) to use:

```coq
ensures t' m' :=
  t = t' /\
  exists (X Y Z Ta Tb : felem),
    bounded_by tight_bounds X /\ ... bounded_by loose_bounds Tb /\
    valid_projective_coords X Y Z Ta Tb /\
    m' =* FElem p_out X * FElem (p_out.+40) Y * ... * a p5@ p_a * R /\
    proj1_sig (m1<op> (coords_to_point a)) = (feval X, feval Y, feval Z, feval Ta, feval Tb)
```

Then discharge follows secp256k1's pattern verbatim. Drawback: upstream-
incompatible (our `_ok` lemmas would have a different shape than
upstream EdwardsXYZT.v). Acceptable — we only need them as `_ok`
witnesses for our scalarmult proof, downstream callers don't care
about the spec shape.

**Path B: keep sigma spec, find the right discharge for it (~5 LoC):**
The blocker is `unshelve eexists` introducing the wrong evar (m' first,
not projective_coords first). Use explicit refine: `refine (ex_intro _
_ (conj eq_refl _)). exists x9, x10, x11, x7, x5; ...` — provide the
m' evar implicitly while the `exists ...` lifts the inner sigma's tuple
witnesses. Cleaner if it works, single-file change.

Recommended: try Path B first (smaller change), fall back to Path A
if Path B fights us.

### Estimate to close

15-20 min at next MCP-friendly session, NOT a heavy build session.
All three `_ok` lemmas should close in one swoop once the discharge
tail is figured out. Then Step 1 of `option-b-64bit-port-plan.md` is
done and we can move to `ed25519_scalarmult_base` (Step 2, multi-day).
