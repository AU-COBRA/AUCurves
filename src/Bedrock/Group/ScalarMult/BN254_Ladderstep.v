(** * Discharge of [CurveAdd.spec_of_ladderstep] for BN254.

    [BN254_G1.bn254_G1_spec_statement] states the ladderstep
    (combined doubling + addition, RCB 2015 Algorithm 7) correctness
    for BN254 as a [Definition ... : Prop] and delegates the proof.
    This file discharges it.

    The route is the one [BN254_CurveOps.bn254_point_double_correct]
    takes for the doubling: the Rupicola derivation
    [CurveAdd.ladderstep_correct] already proves

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

    so what is missing at BN254 is (a) the bounds equality, (b) a
    concrete bounded [three_b] felem holding the Montgomery encoding
    of 3b = 9, and (c) a bedrock2 function realising
    [spec_of_three_b_loader] at the name "bn254_three_b" that
    [BN254_G1.bn254_G1_add] passes to [ladderstep_body].

    (b) and (c) are the same constants and the same four-store loader
    body that [BN254_wNAF_Callees.v] builds for the general-a route;
    they are rebuilt here rather than imported so that this file does
    not depend on the wNAF/BLS12 chain.  The loader proof script is
    that of [CurveAddGeneralA_P256_Loaders.v], unchanged: BN254 is a
    4-limb 64-bit word-by-word Montgomery representation too.  Only
    the target spec differs -- [CurveAdd.spec_of_three_b_loader]
    rather than [CurveAddGeneralA.spec_of_three_b_loader]. *)

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
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.BN254_G1.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Bedrock.Field.Synthesis.Examples.bn254_three_b.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import bedrock2.ProgramLogic.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section BN254_Ladderstep.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    bn254_field_parameters
    bn254_field_parameters_ok
    bn254_frep
    bn254_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  Lemma bn254_ls_bounds_eq :
    loose_bounds (FieldRepresentation:=bn254_frep)
    = tight_bounds (FieldRepresentation:=bn254_frep).
  Proof. reflexivity. Qed.

  (* ============================================================== *)
  (* 1. The constant 3b = 9 as a bounded felem.                      *)
  (* ============================================================== *)

  Definition bn254_ls_tb0 : Z := Eval vm_compute in nth 0 bn254_three_b.three_b_mont 0.
  Definition bn254_ls_tb1 : Z := Eval vm_compute in nth 1 bn254_three_b.three_b_mont 0.
  Definition bn254_ls_tb2 : Z := Eval vm_compute in nth 2 bn254_three_b.three_b_mont 0.
  Definition bn254_ls_tb3 : Z := Eval vm_compute in nth 3 bn254_three_b.three_b_mont 0.

  Definition bn254_ls_three_b_words : list word :=
    [word.of_Z bn254_ls_tb0; word.of_Z bn254_ls_tb1;
     word.of_Z bn254_ls_tb2; word.of_Z bn254_ls_tb3].

  Lemma bn254_ls_three_b_words_length :
    length bn254_ls_three_b_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Definition bn254_ls_three_b_felem : felem :=
    exist _ bn254_ls_three_b_words bn254_ls_three_b_words_length.

  Lemma bn254_ls_three_b_words_bounded :
    bounded_by loose_bounds bn254_ls_three_b_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma bn254_ls_three_b_feval :
    feval (proj1_sig bn254_ls_three_b_felem) = F.of_Z M_pos 9.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* 2. The constant-loader bedrock2 function "bn254_three_b".       *)
  (* ============================================================== *)

  Definition bn254_ls_three_b_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal bn254_ls_tb0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal bn254_ls_tb1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal bn254_ls_tb2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal bn254_ls_tb3)))).

  Definition bn254_ls_three_b_func : Syntax.func :=
    (["out"], [], bn254_ls_three_b_loader_body).

  Lemma bn254_ls_three_b_loader_ok :
    forall functions,
      map.get functions "bn254_three_b" = Some bn254_ls_three_b_func ->
      CurveAdd.spec_of_three_b_loader bn254_ls_three_b_felem "bn254_three_b" functions.
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
      [WeakestPrecondition.func bn254_ls_three_b_func bn254_ls_three_b_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := bn254_ls_three_b_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact bn254_ls_three_b_words_bounded
      | |- _ => idtac
      end.
    cbv [bn254_ls_three_b_felem bn254_ls_three_b_words].
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
  (* 3. [CurveAdd.spec_of_ladderstep] at BN254.                      *)
  (* ============================================================== *)

  (** [BN254_G1.bn254_G1_spec_statement], discharged.  The premises are
      exactly the ones the bedrock2 call protocol supplies: the two
      table entries [BN254_G1.bn254_G1_add] and the 3b loader, and the
      three field leaves that [ladderstep_body] calls.  Fully applied
      rather than [eapply]d: the conclusion is a [fnspec!], and
      unification against it is the slow pattern. *)
  Theorem bn254_G1_ladderstep_ok :
    forall functions,
      map.get functions "curve_add" = Some (snd bn254_G1_add) ->
      map.get functions "bn254_three_b" = Some bn254_ls_three_b_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      bn254_G1_spec_statement bn254_ls_three_b_felem functions.
  Proof.
    intros functions Hca Htb Hmul Hadd Hsub.
    exact (@ladderstep_correct _ _ _ _ _ _ _ _ _ _
             bn254_field_parameters bn254_frep bn254_frep_ok
             bn254_ls_bounds_eq bn254_ls_three_b_felem "bn254_three_b" I
             functions Hca Hmul Hadd Hsub
             (bn254_ls_three_b_loader_ok functions Htb)).
  Qed.

  (** The constant the discharged spec runs at is BN254's: the curve is
      y^2 = x^3 + 3, so 3b = 9, and [BN254_G1.three_b_F] is that value. *)
  Lemma bn254_ladderstep_three_b_val :
    CurveAdd.three_b_val bn254_ls_three_b_felem = three_b_F.
  Proof. exact bn254_ls_three_b_feval. Qed.

  (* ============================================================== *)
  (* 4. A function table that carries both required entries.         *)
  (* ============================================================== *)

  Definition bn254_ladderstep_funcs
    : list (String.string * Syntax.func) :=
    [ bn254_G1_add; ("bn254_three_b", bn254_ls_three_b_func) ].

  Lemma bn254_ladderstep_funcs_curve_add :
    map.get (map.of_list bn254_ladderstep_funcs) "curve_add"
    = Some (snd bn254_G1_add).
  Proof. reflexivity. Qed.

  Lemma bn254_ladderstep_funcs_three_b :
    map.get (map.of_list bn254_ladderstep_funcs) "bn254_three_b"
    = Some bn254_ls_three_b_func.
  Proof. reflexivity. Qed.

End BN254_Ladderstep.
