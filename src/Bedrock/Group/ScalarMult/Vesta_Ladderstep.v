(** * Discharge of [CurveAdd.spec_of_ladderstep] for Vesta.

    Vesta is y^2 = x^3 + 5 over
    0x40000000000000000000000000000000224698fc0994a8dd8c46eb2100000001,
    so a = 0 and the RCB 2015 Algorithm 7 complete addition applies
    unchanged.  That algorithm is already proved, parametrically in the
    field, by the Rupicola derivation [CurveAdd.ladderstep_correct]:

      loose_bounds = tight_bounds ->
      forall three_b three_b_name,
        __rupicola_program_marker _ ->
        forall functions,
          map.get functions "curve_add" = Some (ladderstep_body three_b_name) ->
          spec_of_BinOp bin_mul functions ->
          spec_of_BinOp bin_add functions ->
          spec_of_BinOp bin_sub functions ->
          spec_of_three_b_loader three_b three_b_name functions ->
          spec_of_ladderstep three_b functions

    so what an instance has to supply is (a) the bounds equality, (b) a
    concrete bounded [three_b] felem holding the Montgomery encoding of
    3b = 15, and (c) a bedrock2 function realising
    [spec_of_three_b_loader] at the name "vesta_three_b" that
    [vesta_G1_add] passes to [ladderstep_body].

    (b) reuses [VestaCurve_G1.vesta_three_b_mont], the vm_computed
    Montgomery encoding of 15 that the Montgomery-curve instantiation
    already carries.  (c) is the four-store loader body and the proof
    script of [CurveAddGeneralA_P256_Loaders.v], unchanged: Vesta is a
    4-limb 64-bit word-by-word Montgomery representation too.  Only the
    target spec differs -- [CurveAdd.spec_of_three_b_loader] rather than
    [CurveAddGeneralA.spec_of_three_b_loader].

    This file is the Vesta twin of [BN254_Ladderstep.v]. *)

From Stdlib Require Import ZArith Lia List.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.vesta_prime.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Bedrock.Curve.VestaCurve_G1.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section Vesta_Ladderstep.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    vesta_field_parameters
    vesta_field_parameters_ok
    vesta_frep
    vesta_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  Lemma vesta_ls_bounds_eq :
    loose_bounds (FieldRepresentation:=vesta_frep)
    = tight_bounds (FieldRepresentation:=vesta_frep).
  Proof. reflexivity. Qed.

  (* ============================================================== *)
  (* 1. The constant 3b = 15 as a bounded felem.                     *)
  (* ============================================================== *)

  Definition vesta_ls_tb0 : Z :=
    Eval vm_compute in nth 0 VestaCurve_G1.vesta_three_b_mont 0.
  Definition vesta_ls_tb1 : Z :=
    Eval vm_compute in nth 1 VestaCurve_G1.vesta_three_b_mont 0.
  Definition vesta_ls_tb2 : Z :=
    Eval vm_compute in nth 2 VestaCurve_G1.vesta_three_b_mont 0.
  Definition vesta_ls_tb3 : Z :=
    Eval vm_compute in nth 3 VestaCurve_G1.vesta_three_b_mont 0.

  Definition vesta_ls_three_b_words : list word :=
    [word.of_Z vesta_ls_tb0; word.of_Z vesta_ls_tb1;
     word.of_Z vesta_ls_tb2; word.of_Z vesta_ls_tb3].

  Lemma vesta_ls_three_b_words_length :
    length vesta_ls_three_b_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Definition vesta_ls_three_b_felem : felem :=
    exist _ vesta_ls_three_b_words vesta_ls_three_b_words_length.

  Lemma vesta_ls_three_b_words_bounded :
    bounded_by loose_bounds vesta_ls_three_b_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma vesta_ls_three_b_feval :
    feval (proj1_sig vesta_ls_three_b_felem) = F.of_Z M_pos 15.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* 2. The constant-loader bedrock2 function "vesta_three_b".      *)
  (* ============================================================== *)

  Definition vesta_ls_three_b_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal vesta_ls_tb0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal vesta_ls_tb1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal vesta_ls_tb2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal vesta_ls_tb3)))).

  Definition vesta_ls_three_b_func : Syntax.func :=
    (["out"], [], vesta_ls_three_b_loader_body).

  Lemma vesta_ls_three_b_loader_ok :
    forall functions,
      map.get functions "vesta_three_b" = Some vesta_ls_three_b_func ->
      CurveAdd.spec_of_three_b_loader vesta_ls_three_b_felem "vesta_three_b" functions.
  Proof.
    intros functions EnvContains.
    cbv [CurveAdd.spec_of_three_b_loader].
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
      [WeakestPrecondition.func vesta_ls_three_b_func vesta_ls_three_b_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := vesta_ls_three_b_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact vesta_ls_three_b_words_bounded
      | |- _ => idtac
      end.
    cbv [vesta_ls_three_b_felem vesta_ls_three_b_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  (* ============================================================== *)
  (* 3. [CurveAdd.spec_of_ladderstep] at Vesta.                     *)
  (* ============================================================== *)

  (* Vesta curve: y^2 = x^3 + 5, so 3b = 15 *)
  Definition vesta_G1_add : function_t :=
    ("curve_add", ladderstep_body "vesta_three_b").

  Definition vesta_three_b_F : F := ModularArithmetic.F.of_Z M_pos 15.

  Definition vesta_G1_spec_statement
    (three_b : Crypto.Bedrock.Specs.Field.felem)
    (functions : Semantics.env) : Prop :=
    @CurveAdd.spec_of_ladderstep _ _ _ _ _ _
      vesta_field_parameters vesta_frep three_b functions.

  (** The premises are exactly the ones the bedrock2 call protocol
      supplies: the two table entries [vesta_G1_add] and the 3b loader,
      and the three field leaves that [ladderstep_body] calls.  Fully
      applied rather than [eapply]d: the conclusion is a [fnspec!], and
      unification against it is the slow pattern. *)
  Theorem vesta_G1_ladderstep_ok :
    forall functions,
      map.get functions "curve_add" = Some (snd vesta_G1_add) ->
      map.get functions "vesta_three_b" = Some vesta_ls_three_b_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      vesta_G1_spec_statement vesta_ls_three_b_felem functions.
  Proof.
    intros functions Hca Htb Hmul Hadd Hsub.
    exact (@ladderstep_correct _ _ _ _ _ _ _ _ _ _
             vesta_field_parameters vesta_frep vesta_frep_ok
             vesta_ls_bounds_eq vesta_ls_three_b_felem "vesta_three_b" I
             functions Hca Hmul Hadd Hsub
             (vesta_ls_three_b_loader_ok functions Htb)).
  Qed.

  (** The constant the discharged spec runs at is Vesta's: the curve is
      y^2 = x^3 + 5, so 3b = 15. *)
  Lemma vesta_ladderstep_three_b_val :
    CurveAdd.three_b_val vesta_ls_three_b_felem = vesta_three_b_F.
  Proof. exact vesta_ls_three_b_feval. Qed.

  (* ============================================================== *)
  (* 4. A function table that carries both required entries.         *)
  (* ============================================================== *)

  Definition vesta_ladderstep_funcs
    : list (String.string * Syntax.func) :=
    [ vesta_G1_add; ("vesta_three_b", vesta_ls_three_b_func) ].

  Lemma vesta_ladderstep_funcs_curve_add :
    map.get (map.of_list vesta_ladderstep_funcs) "curve_add"
    = Some (snd vesta_G1_add).
  Proof. reflexivity. Qed.

  Lemma vesta_ladderstep_funcs_three_b :
    map.get (map.of_list vesta_ladderstep_funcs) "vesta_three_b"
    = Some vesta_ls_three_b_func.
  Proof. reflexivity. Qed.

End Vesta_Ladderstep.

Print Assumptions vesta_G1_ladderstep_ok.
Print Assumptions vesta_ls_three_b_loader_ok.
Print Assumptions vesta_ladderstep_three_b_val.
