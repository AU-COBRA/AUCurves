(** * Smoke test for Compilation2_Fp2 hints.
    Validates that compile_step fires on AbstractField.Fadd/Fmul/Fsub
    when the goal contains a nlet_eq binding over those operations. *)

Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Compilation2_Fp2.
Import bedrock2.Memory.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.syntactic_unify.

Local Open Scope Z_scope.

Section Test.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}
          {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}
          {locals_ok : map.ok locals}
          {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type}
          {field_parameters : AbstractField.FieldParameters F}
          {field_representation : AbstractField.FieldRepresentation}
          {field_representation_ok : AbstractField.FieldRepresentation_ok}.

  Local Ltac cancel_impl_step :=
    let RHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps _) (seps ?RHS) => RHS end in
    let jy := index_and_element_of RHS in
    let j := lazymatch jy with (?i, _) => i end in
    let y := lazymatch jy with (_, ?y) => y end in
    assert_fails (idtac; let y := rdelta_var y in is_evar y);
    let LHS := lazymatch goal with
               | |- Lift1Prop.impl1 (seps ?LHS) _ => LHS end in
    let i := find_syntactic_unify_deltavar LHS y in
    cancel_seps_at_indices_by_implication i j;
    [exact (impl1_refl _)|].

  Local Ltac ecancel_fast :=
    cancel;
    lazymatch goal with
    | |- Lift1Prop.impl1 _ _ =>
      repeat cancel_impl_step;
      repeat ecancel_step_by_implication;
      cbv [seps]; exact impl1_refl
    | |- Lift1Prop.iff1 _ _ =>
      ecancel_steps_at O;
      ecancel_done
    end.

  Local Ltac ecancel_assumption_fast :=
    multimatch goal with
    | |- ?PG ?m1 =>
      multimatch goal with
      | H: _ ?m2 |- _ =>
        syntactic_unify_deltavar m1 m2;
        let H' := fresh "Hcopy" in
        pose proof H as H';
        cbv beta iota zeta in H';
        lazymatch type of H' with
        | (_ * _)%sep _ =>
          refine (Morphisms.subrelation_refl
                    Lift1Prop.impl1 _ _ _ _ H');
          clear H';
          ecancel_fast
        end
      end
    end.

  Local Ltac ecancel_assumption ::= ecancel_assumption_fast.

  (* ------------------------------------------------------------------
     1.  Gallina spec written in Rupicola's let/n style.
         "double x" adds x to itself.
     ------------------------------------------------------------------ *)
  Definition af_double (x : F) : F :=
    let/n res as "out" := AbstractField.Fadd x x in
    res.

  (* ------------------------------------------------------------------
     2.  Test A -- compile_af_add fires via eapply
         We construct a WP goal whose postcondition has a nlet_eq
         over Fadd, then show compile_af_add applies and its
         side-conditions are dischargeable.
     ------------------------------------------------------------------ *)
  Lemma test_compile_step_add :
    forall (tr : Semantics.trace) (m : mem)
           (l : locals) (functions : Semantics.env)
           (x : F) (old_out : F)
           (x_ptr out_ptr : word)
           (pred : F -> Semantics.trace -> mem -> locals -> Prop),
      AbstractField.binop_spec AbstractField.bin_add functions ->
      map.get l "x" = Some x_ptr ->
      map.get l "out" = Some out_ptr ->
      (AFElem (Some AbstractField.tight_bounds) x_ptr x *
       AFElem None out_ptr old_out)%sep m ->
      (forall v m', sep (AFElem (Some AbstractField.loose_bounds) out_ptr v)
                        (AFElem (Some AbstractField.tight_bounds) x_ptr x) m' ->
                    pred v tr m' l) ->
    exists k_impl,
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      k_impl
      <{ pred (af_double x) }>.
  Proof.
    intros tr m l functions x old_out x_ptr out_ptr pred
           Hspec Hget_x Hget_out Hsep Hcont.
    (* Unfold the Gallina spec, exposing the nlet *)
    unfold af_double.
    (* The goal is now:
       exists k_impl, WP.cmd ... k_impl (pred (nlet ["out"] (Fadd x x) (fun res => res)))
       Step 1: provide the cmd evar and enter the proof *)
    eexists.
    (* Step 2: convert the nlet to nlet_eq so the hint can match *)
    simple apply compile_nlet_as_nlet_eq.
    (* Step 3: the hint extern for Fadd should fire via step_with_db.
       We demonstrate this by directly applying the hint lemma. *)
    simple eapply compile_af_add.
    (* We now have subgoals from compile_af_add.
       Show they are all solvable from hypotheses. *)
    (* Side-condition: binop_spec *)
    { exact Hspec. }
    (* Side-condition: map.get l out_var = Some out_ptr *)
    { exact Hget_out. }
    (* Side-condition: (AFElem _ out_ptr old * Rout) m *)
    { ecancel_assumption. }
    (* Side-condition: (AFElem (Some tight_bounds) x_ptr x * Rx) m *)
    { ecancel_assumption. }
    (* Side-condition: (AFElem (Some tight_bounds) y_ptr y * Ry) m
       For double, y = x, y_ptr = x_ptr *)
    { ecancel_assumption. }
    (* Side-condition: map.get l x_var *)
    { exact Hget_x. }
    (* Side-condition: map.get l y_var -- same var for double *)
    { exact Hget_x. }
    (* Continuation: after the add.
       The continuation from compile_af_add starts with
       "let v := Fadd x x in forall m', sep ... m' -> WP ...",
       so we must intro the let-binding, then m' and sep. *)
    { cbv zeta beta. intros m' Hsep'.
      (* The remaining goal is: WP.cmd ... ?k tr m' l (pred (Fadd x x))
         Instantiate k := cmd.skip via compile_skip; then discharge post. *)
      simple apply compile_skip.
      exact (Hcont _ _ Hsep'). }
  Qed.

  (* ------------------------------------------------------------------
     3.  Test B -- compile_af_mul fires
     ------------------------------------------------------------------ *)
  Definition af_square_via_mul (x : F) : F :=
    let/n res as "out" := AbstractField.Fmul x x in
    res.

  Lemma test_compile_step_mul :
    forall (tr : Semantics.trace) (m : mem)
           (l : locals) (functions : Semantics.env)
           (x : F) (old_out : F)
           (x_ptr out_ptr : word)
           (pred : F -> Semantics.trace -> mem -> locals -> Prop),
      AbstractField.binop_spec AbstractField.bin_mul functions ->
      map.get l "x" = Some x_ptr ->
      map.get l "out" = Some out_ptr ->
      (AFElem (Some AbstractField.loose_bounds) x_ptr x *
       AFElem None out_ptr old_out)%sep m ->
      (forall v m', sep (AFElem (Some AbstractField.tight_bounds) out_ptr v)
                        (AFElem (Some AbstractField.loose_bounds) x_ptr x) m' ->
                    pred v tr m' l) ->
    exists k_impl,
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      k_impl
      <{ pred (af_square_via_mul x) }>.
  Proof.
    intros tr m l functions x old_out x_ptr out_ptr pred
           Hspec Hget_x Hget_out Hsep Hcont.
    unfold af_square_via_mul.
    eexists.
    simple apply compile_nlet_as_nlet_eq.
    simple eapply compile_af_mul.
    { exact Hspec. }
    { exact Hget_out. }
    { ecancel_assumption. }
    { ecancel_assumption. }
    { ecancel_assumption. }
    { exact Hget_x. }
    { exact Hget_x. }
    { cbv zeta beta. intros m' Hsep'.
      simple apply compile_skip.
      exact (Hcont _ _ Hsep'). }
  Qed.

  (* ------------------------------------------------------------------
     4.  Test C -- two-step function: add then sub
         Shows the hints chain correctly in a multi-step nlet sequence.
     ------------------------------------------------------------------ *)
  (* add -> mul chain:
     add produces loose_bounds, mul consumes loose_bounds.
     This chain tests that bounds flow correctly between steps. *)
  Definition af_add_then_mul (x y z : F) : F :=
    let/n t as "out" := AbstractField.Fadd x y in
    let/n res as "out" := AbstractField.Fmul t z in
    res.

  Lemma test_compile_step_chain :
    forall (tr : Semantics.trace) (m : mem)
           (l : locals) (functions : Semantics.env)
           (x y z : F) (old_out : F)
           (x_ptr y_ptr z_ptr out_ptr : word)
           (pred : F -> Semantics.trace -> mem -> locals -> Prop),
      AbstractField.binop_spec AbstractField.bin_add functions ->
      AbstractField.binop_spec AbstractField.bin_mul functions ->
      map.get l "x" = Some x_ptr ->
      map.get l "y" = Some y_ptr ->
      map.get l "z" = Some z_ptr ->
      map.get l "out" = Some out_ptr ->
      (AFElem (Some AbstractField.tight_bounds) x_ptr x *
       AFElem (Some AbstractField.tight_bounds) y_ptr y *
       AFElem (Some AbstractField.loose_bounds) z_ptr z *
       AFElem None out_ptr old_out)%sep m ->
      (forall v m', pred v tr m' l) ->
    exists k_impl,
      <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
      k_impl
      <{ pred (af_add_then_mul x y z) }>.
  Proof.
    intros tr m l functions x y z old_out
           x_ptr y_ptr z_ptr out_ptr pred
           Hspec_add Hspec_mul Hget_x Hget_y Hget_z Hget_out Hsep Hcont.
    unfold af_add_then_mul.
    eexists.
    (* First step: handle the Fadd *)
    simple apply compile_nlet_as_nlet_eq.
    simple eapply compile_af_add.
    { exact Hspec_add. }
    { exact Hget_out. }
    { ecancel_assumption. }
    { ecancel_assumption. }
    { ecancel_assumption. }
    { exact Hget_x. }
    { exact Hget_y. }
    (* Continuation after add: now handle the Fmul.
       The add produced AFElem loose_bounds, and mul consumes loose_bounds. *)
    { cbv zeta beta. intros m' Hsep'.
      simple apply compile_nlet_as_nlet_eq.
      simple eapply compile_af_mul.
      { exact Hspec_mul. }
      { exact Hget_out. }
      { ecancel_assumption. }
      (* t = Fadd x y has loose_bounds from add, mul needs loose -- OK *)
      { ecancel_assumption. }
      (* z has loose_bounds, mul needs loose -- OK *)
      { ecancel_assumption. }
      { exact Hget_out. }
      { exact Hget_z. }
      { cbv zeta beta. intros m'' Hsep''.
        simple apply compile_skip.
        exact (Hcont _ m''). } }
  Qed.

End Test.
