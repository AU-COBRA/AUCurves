(** * P-256 constant-loader proofs for the Rupicola general-a RCB
      addition.

    Discharges the two loader-spec hypotheses of
    [CurveAddGeneralA_P256.p256_curve_add_general_ok]:
      [spec_of_three_b_loader p256_three_b_felem "p256_three_b"]
      [spec_of_a_loader       p256_a_felem      "p256_a_const"]
    for the bedrock2 functions [p256_three_b_func] /
    [p256_a_const_func] (4 stores of the precomputed Montgomery limbs
    each).  Proof pattern: bls12_three_b_ok
    (Examples/bls12_three_b.v), adapted to 4 limbs and to the
    bounds-annotated [Compilation2.FElem] of the CurveAddGeneralA
    loader specs.

    Honesty ledger (this file): 0 Admitted. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.Semantics.
Require Import bedrock2.Memory.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.
Require Import bedrock2.BasicC64Semantics.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Curve.P256Curve_G1.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256.

Import Syntax ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section P256_Loaders.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p256_field_parameters
    p256_field_parameters_ok
    p256_frep
    p256_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  Lemma p256_three_b_loader_ok :
    forall functions,
      map.get functions "p256_three_b" = Some p256_three_b_func ->
      spec_of_three_b_loader p256_three_b_felem "p256_three_b" functions.
  Proof.
    intros functions EnvContains.
    cbv [spec_of_three_b_loader].
    intros pout outold Rout tr mem0 Hpre.
    (* 1. Decompose the input FElem into four scalars. *)
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded]
      in Hpre.
    extract_ex1_and_emp_in Hpre.
    lazymatch type of Hpre with
    | context [Field.FElem _ ?v] =>
        let ws := fresh "ws" in
        let Hlen := fresh "Hlen" in
        destruct v as [ws Hlen];
        cbv [Field.FElem] in Hpre;
        vm_compute in Hlen;
        do 4 (destruct ws as [|? ws]; [cbn in Hlen; lia|]);
        destruct ws as [|? ws]; [|cbn in Hlen; lia];
        cbn [array proj1_sig] in Hpre
    end.
    change (Memory.bytes_per_word 64) with 8 in Hpre.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) in Hpre by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) in Hpre by ring.
    (* 2. Enter the function body and execute the four stores. *)
    eapply WeakestPreconditionProperties.start_func;
      [ exact EnvContains | ].
    cbv match beta delta
      [WeakestPrecondition.func p256_three_b_func p256_three_b_loader_body].
    repeat straightline.
    (* 3. Postcondition. *)
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    (* The goal-side extraction leaves the ex1 witness as an evar
       (extract_ex1_in_goal_at_index) and pulls the emp contents out
       as conjuncts; supply the witness explicitly. *)
    extract_ex1_and_emp_in_goal.
    instantiate (1 := p256_three_b_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact p256_three_b_words_bounded
      | |- _ => idtac
      end.
    (* remaining: the separation goal for the stored limbs *)
    cbv [p256_three_b_felem p256_three_b_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  Lemma p256_a_loader_ok :
    forall functions,
      map.get functions "p256_a_const" = Some p256_a_const_func ->
      spec_of_a_loader p256_a_felem "p256_a_const" functions.
  Proof.
    intros functions EnvContains.
    cbv [spec_of_a_loader].
    intros pout outold Rout tr mem0 Hpre.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded]
      in Hpre.
    extract_ex1_and_emp_in Hpre.
    lazymatch type of Hpre with
    | context [Field.FElem _ ?v] =>
        let ws := fresh "ws" in
        let Hlen := fresh "Hlen" in
        destruct v as [ws Hlen];
        cbv [Field.FElem] in Hpre;
        vm_compute in Hlen;
        do 4 (destruct ws as [|? ws]; [cbn in Hlen; lia|]);
        destruct ws as [|? ws]; [|cbn in Hlen; lia];
        cbn [array proj1_sig] in Hpre
    end.
    change (Memory.bytes_per_word 64) with 8 in Hpre.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) in Hpre by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) in Hpre by ring.
    eapply WeakestPreconditionProperties.start_func;
      [ exact EnvContains | ].
    cbv match beta delta
      [WeakestPrecondition.func p256_a_const_func p256_a_const_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := p256_a_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact p256_a_words_bounded
      | |- _ => idtac
      end.
    cbv [p256_a_felem p256_a_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  (** End-to-end: with the two loader functions and the three field
      ops in the table, the derived body meets its FElem-level spec. *)
  Lemma p256_curve_add_general_full :
    forall functions,
      map.get functions "curve_add_general"
        = Some p256_curve_add_general_func ->
      map.get functions "p256_three_b" = Some p256_three_b_func ->
      map.get functions "p256_a_const" = Some p256_a_const_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_rcb_add_general p256_three_b_felem p256_a_felem functions.
  Proof.
    intros functions Hadd_env Htb_env Ha_env Hmul Hadd Hsub.
    (* Explicit discharge.  The former [eapply p256_curve_add_general_ok;
       eauto using p256_three_b_loader_ok, p256_a_loader_ok] measured 88 s
       (scripts/logs/dbl_chain_0829_0934.log); the six-limb P-384 analogue
       of the same sentence measured 853 s.  Naming the two loader facts
       and supplying every argument removes the search; the environment
       premise is the single hole, discharged by the following [exact]. *)
    pose proof (p256_three_b_loader_ok functions Htb_env) as Htb.
    pose proof (p256_a_loader_ok functions Ha_env) as Ha.
    refine (p256_curve_add_general_ok functions _ Hmul Hadd Hsub Htb Ha).
    exact Hadd_env.
  Qed.

End P256_Loaders.
