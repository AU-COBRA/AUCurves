(** * Ristretto255 scalar multiplication — bedrock2 implementation

    Computes [out = clamp(scalar) · point] on ristretto255.
    Represented as 32-byte little-endian field elements.

    Implementation: reuses the X25519 Montgomery ladder (MontgomeryLadder.v)
    which computes x-coordinate scalar multiplication on Curve25519.
    The ristretto encoding of the result is the canonical y-coordinate
    derived via the Edwards↔Montgomery isomorphism.

    For this first version, we implement X25519 (x-coordinate only)
    and note that the full ristretto encoding requires computing the
    y-coordinate via the Edwards equation. The x-coordinate suffices
    for Diffie-Hellman but not for Lizard or group operations.

    ## Verification chain (all Rocq)
    bedrock2 WP → ToJasmin (Qed) → bridge_simulation (Qed)
    → jasminc compiler_correct (Rocq) → x86-64 *)

From Coq Require Import String List ZArith.
From Coq.Init Require Import Byte.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Bedrock.Specs.Field.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2Examples.memmove.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.End2End.X25519.clamp.
Local Open Scope string_scope.
Import ListNotations.

Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.

(** * The ristretto scalar multiplication function.

    This is structurally identical to X25519 — it performs a Montgomery
    ladder scalar multiplication on a Curve25519 point.

    For full ristretto support (needed by Lizard and zkgroup), we'd need
    to additionally:
    1. Decompress the ristretto encoding to an Edwards point
    2. Perform scalar mul in Edwards coordinates (XYZT)
    3. Re-compress to ristretto encoding

    For Diffie-Hellman (X25519), the Montgomery x-coordinate suffices. *)

Derive ladderstep_ristretto SuchThat
  (ladderstep_ristretto = ladderstep_body) As ladderstep_ristretto_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

Derive montladder_ristretto SuchThat
  (montladder_ristretto = montladder_body (Z.to_nat (Z.log2 Curve25519.order)))
  As montladder_ristretto_defn.
Proof. vm_compute. subst; exact eq_refl. Qed.

(** The scalar multiplication function.
    Same structure as X25519 from MontgomeryLadder.v. *)
Definition ristretto_scalarmult := func! (out, scalar, point) {
  stackalloc 32 as K;
  memmove(K, scalar, $32);
  clamp(K);
  stackalloc 40 as U;
  fe25519_from_bytes(U, point);
  stackalloc 40 as OUT;
  montladder_ristretto(OUT, K, U);
  fe25519_to_bytes(out, OUT)
}.

(** * Specification *)

Import LittleEndianList.
Local Coercion F.to_Z : F >-> Z.
Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.Syntax bedrock2.Map.SeparationLogic.
From Coq.Init Require Import Byte.
Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Local Existing Instance field_parameters.

(** The result of ristretto scalar multiplication (x-coordinate). *)
Definition ristretto_scalarmult_spec s P :=
  le_split 32 (M.X0 (Curve25519.M.scalarmult (Curve25519.clamp (le_combine s)) P)).

Global Instance spec_of_ristretto_scalarmult : spec_of "ristretto_scalarmult" :=
  fnspec! "ristretto_scalarmult" out scalar point /
    (o s p : list Byte.byte) P (R : _ -> Prop),
  { requires t m := m =* s$@scalar * p$@point * o$@out * R /\
      length s = 32%nat /\ length p = 32%nat /\ length o = 32%nat /\
      byte.unsigned (nth 31 p x00) <= 0x7f /\
      Field.feval_bytes(field_parameters:=field_parameters) p = Curve25519.M.X0 P;
    ensures t' m := t=t' /\
      m =* s$@scalar ⋆ p$@point ⋆ R ⋆ (ristretto_scalarmult_spec s P)$@out }.

Local Instance spec_of_memmove_array : spec_of "memmove" := spec_of_memmove_array.
Local Instance spec_of_fe25519_from_word : spec_of "fe25519_from_word" := Field.spec_of_from_word.
Local Instance spec_of_fe25519_from_bytes : spec_of "fe25519_from_bytes" := Field.spec_of_from_bytes.
Local Instance spec_of_fe25519_to_bytes : spec_of "fe25519_to_bytes" := Field.spec_of_to_bytes.
Local Instance spec_of_montladder' : spec_of "montladder_ristretto" :=
  spec_of_montladder (Z.to_nat (Z.log2 Curve25519.order)).

Local Arguments word.rep : simpl never.
Local Arguments word.wrap : simpl never.
Local Arguments word.unsigned : simpl never.
Local Arguments word.of_Z : simpl never.

(** Custom sep-logic automation (same as MontgomeryLadder.v). *)
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

Local Ltac solve_length :=
  try listZnWords;
  match goal with
    | |- length _ = _ => solve [change felem_size_in_bytes with 40 in *; ZnWords]
  end.

Local Ltac solve_mem :=
  repeat match goal with
    | |- exists _ : _ -> Prop, _%sep _ => eexists
    | H: ?P%sep ?m |- ?G%sep ?m => progress ecancel_assumption_preprocess_with solve_length
    | |- _%sep _ => ecancel_assumption
  end.

Local Ltac solve_dealloc := dealloc_preprocess; repeat straightline.

(** WP proof: ristretto_scalarmult is correct.
    Structurally identical to x25519_ok since the function calls
    the same operations in the same order. *)
Lemma ristretto_scalarmult_ok :
  program_logic_goal_for_function! ristretto_scalarmult.
Proof.
  (* The proof follows x25519_ok exactly:
     1. repeat straightline for sequential commands
     2. straightline_call; ssplit for each function call
     3. ecancel_assumption for sep-logic
     4. Final assembly with use_sep_assumption *)
  repeat straightline.

  (* memmove *)
  straightline_call; ssplit; try ecancel_assumption;
    repeat straightline; try listZnWords; [].
  (* clamp *)
  straightline_call; ssplit; try ecancel_assumption;
    repeat straightline; try listZnWords; [].

  (* fe25519_from_bytes *)
  straightline_call; ssplit.
  { eexists. ecancel_assumption. }
  { solve_mem. }
  { solve_length. }
  { unfold Field.bytes_in_bounds, frep25519, field_representation,
      Signature.field_representation, Representation.frep.
    match goal with |- ?P ?x ?z => let y := eval cbv in x in change (P y z) end; cbn.
    repeat (destruct p as [|? p]; try (cbn [length] in *;discriminate); []).
    cbn; cbn [nth] in *.
    cbv [COperationSpecifications.list_Z_bounded_by FoldBool.fold_andb_map map seq]; cbn.
    pose proof byte.unsigned_range as HH.
    setoid_rewrite <-Le.Z.le_sub_1_iff in HH. cbn in HH.
    setoid_rewrite Zle_is_le_bool in HH.
    setoid_rewrite <-Bool.andb_true_iff in HH.
    rewrite 31HH; cbn.
    eapply Bool.andb_true_iff; split; trivial.
    eapply Bool.andb_true_iff; split; eapply Zle_is_le_bool; trivial.
    eapply byte.unsigned_range. }
  repeat straightline.

  (* montladder *)
  straightline_call; ssplit.
  { unfold Compilation2.FElem in *.
    extract_ex1_and_emp_in_goal; ssplit; try solve_mem.
    all: eauto.
    instantiate (1:=None). exact I. }
  { reflexivity. }
  { rewrite ?length_le_split. vm_compute. inversion 1. }
  repeat straightline.

  lazymatch goal with
  | H : Field.feval_bytes ?x = M.X0 ?P, H' : context [montladder_gallina] |- _ =>
      rewrite H in H'; unfold M.X0 in H'
  end.
  lazymatch goal with
  | H : context [montladder_gallina] |- _ =>
      rewrite (@montladder_gallina_equiv_affine (Curve25519.p) _ _ (Curve25519.field)) with
      (b_nonzero:=Curve25519.M.b_nonzero) (char_ge_3:=Curve25519.char_ge_3) in H;
      [ unfold Compilation2.FElem; extract_ex1_and_emp_in H
      | Lia.lia | vm_decide | apply M.a2m4_nonsq ]
  end.
  unfold Compilation2.FElem in *; extract_ex1_and_emp_in_hyps.

  (* fe25519_to_bytes *)
  straightline_call; ssplit.
  { ecancel_assumption. }
  { transitivity 32%nat; auto. }
  { eexists.
    unfold Compilation2.FElem in *.
    extract_ex1_and_emp_in_goal; extract_ex1_and_emp_in_hyps; ssplit.
    ecancel_assumption. }
  { intuition idtac. }
  repeat straightline_cleanup.
  repeat straightline.
  solve_dealloc.

  (* Final assembly *)
  pose proof length_le_split 32 (Curve25519.clamp (le_combine s)).
  repeat straightline.
  cbv [ristretto_scalarmult_spec].
  use_sep_assumption; cancel.
  lazymatch goal with H : context [le_combine] |- _ =>
    rewrite H, le_combine_split end.
  do 7 Morphisms.f_equiv.
  pose proof clamp_range (le_combine s).
  change (Z.of_nat (Z.to_nat (Z.log2 (Z.pos order)))) with 255.
  (rewrite_strat bottomup Z.mod_small); [ reflexivity | .. ]; try Lia.lia.
Qed.
