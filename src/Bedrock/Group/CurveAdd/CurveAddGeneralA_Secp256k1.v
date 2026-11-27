(** * secp256k1 instantiation of the Rupicola general-a RCB addition.

    Instantiates [CurveAddGeneralA] (the derived 40-operation
    Renes-Costello-Batina complete addition with two stack-loaded curve
    constants) at fiat-crypto's secp256k1 field representation
    [Crypto.Bedrock.Secp256k1.Field256k1.frep256k1] (word-by-word
    Montgomery, 4 limbs of 64 bits, callee prefix "secp256k1_").  The curve
    is y^2 = x^3 + 7: a = 0, b = 7, so 3b = 21.  Algorithm 1 of RCB is
    complete for every short Weierstrass curve; with a = 0 the four
    multiplications by [a_const] compute 0.

    This is the route that the comment on [Curve.Secp256k1_G1_Add_Spec] in
    src/Bedrock/dune names as the principled one: the hand-written
    Bignum-level pathfinder [Secp256k1_G1_Add_Spec.v] (Admitted, excluded from
    the build) is bypassed, not repaired.

    Contents (the P-256 files [CurveAddGeneralA_P256.v] §1-§4 and
    [CurveAddGeneralA_P256_Loaders.v], at secp256k1):
      §0  [secp256k1_field_parameters_ok]: [FieldParameters_ok] for
          [Field256k1.field_parameters], from the Pocklington certificate
          [Secp256k1_prime_certif.prime_secp256k1].
      §1  Montgomery-encoded constants 3b = 21 and a = 0 as felems, with
          [vm_compute] proofs (length, bounds, [feval] value).
      §2  [secp256k1_bounds_eq] : loose_bounds = tight_bounds.
      §3  The loader functions "secp256k1_three_b", "secp256k1_a_const".
      §4  [secp256k1_curve_add_general_func] (the derived body at secp256k1)
          and [secp256k1_curve_add_general_ok] (its spec, from
          [rcb_add_general_correct]).
      §5  The loader proofs and [secp256k1_curve_add_general_full].

    Honesty ledger (this file): 0 Admitted, 0 Axiom. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Strings.String.
Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Properties.
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
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Curve.Secp256k1_prime_certif.
Require Import Bedrock.Curve.Secp256k1Curve_G1.

Import Syntax ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ============================================================== *)
(* §0. Primality of the modulus of [Field256k1.field_parameters]   *)
(* ============================================================== *)

Lemma secp256k1_M_eq :
  Z.pos (@M_pos Field256k1.field_parameters) = secp256k1_modulus.
Proof. vm_compute. reflexivity. Qed.

Lemma secp256k1_field_parameters_ok :
  @FieldParameters_ok Field256k1.field_parameters.
Proof.
  constructor. pose proof prime_secp256k1 as H.
  rewrite <- secp256k1_M_eq in H. exact H.
Qed.

Section Secp256k1_GeneralA.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    Field256k1.field_parameters
    secp256k1_field_parameters_ok
    Field256k1.frep256k1
    Field256k1.frep256k1_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  (* ============================================================== *)
  (* §1. Curve constants                                             *)
  (* ============================================================== *)

  Definition secp256k1_m : Z := Eval vm_compute in (2^256 - 2^32 - 977).
  Definition secp256k1_b : Z := 7.
  Definition secp256k1_a_Z : Z := 0.
  Definition secp256k1_three_b_Z : Z := 21.

  (** Montgomery limbs of 3b and a, from [Secp256k1Curve_G1]
      ([secp256k1_three_b_mont] / [secp256k1_a_mont_list]). *)
  Definition secp256k1_tb0 : Z := Eval vm_compute in nth 0 Secp256k1Curve_G1.secp256k1_three_b_mont 0.
  Definition secp256k1_tb1 : Z := Eval vm_compute in nth 1 Secp256k1Curve_G1.secp256k1_three_b_mont 0.
  Definition secp256k1_tb2 : Z := Eval vm_compute in nth 2 Secp256k1Curve_G1.secp256k1_three_b_mont 0.
  Definition secp256k1_tb3 : Z := Eval vm_compute in nth 3 Secp256k1Curve_G1.secp256k1_three_b_mont 0.
  Definition secp256k1_ac0 : Z := Eval vm_compute in nth 0 Secp256k1Curve_G1.secp256k1_a_mont_list 0.
  Definition secp256k1_ac1 : Z := Eval vm_compute in nth 1 Secp256k1Curve_G1.secp256k1_a_mont_list 0.
  Definition secp256k1_ac2 : Z := Eval vm_compute in nth 2 Secp256k1Curve_G1.secp256k1_a_mont_list 0.
  Definition secp256k1_ac3 : Z := Eval vm_compute in nth 3 Secp256k1Curve_G1.secp256k1_a_mont_list 0.

  (** 3b R mod p = 21 (2^32 + 977) fits in the low limb. *)
  Example secp256k1_three_b_limbs :
    [secp256k1_tb0; secp256k1_tb1; secp256k1_tb2; secp256k1_tb3] = [90194333733; 0; 0; 0].
  Proof. vm_compute. reflexivity. Qed.

  Example secp256k1_a_limbs :
    [secp256k1_ac0; secp256k1_ac1; secp256k1_ac2; secp256k1_ac3] = [0; 0; 0; 0].
  Proof. vm_compute. reflexivity. Qed.

  Definition secp256k1_three_b_words : list word :=
    [word.of_Z secp256k1_tb0; word.of_Z secp256k1_tb1;
     word.of_Z secp256k1_tb2; word.of_Z secp256k1_tb3].
  Definition secp256k1_a_words : list word :=
    [word.of_Z secp256k1_ac0; word.of_Z secp256k1_ac1;
     word.of_Z secp256k1_ac2; word.of_Z secp256k1_ac3].

  Lemma secp256k1_three_b_words_length :
    length secp256k1_three_b_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Lemma secp256k1_a_words_length :
    length secp256k1_a_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Definition secp256k1_three_b_felem : felem :=
    exist _ secp256k1_three_b_words secp256k1_three_b_words_length.
  Definition secp256k1_a_felem : felem :=
    exist _ secp256k1_a_words secp256k1_a_words_length.

  Lemma secp256k1_three_b_words_bounded :
    bounded_by loose_bounds secp256k1_three_b_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma secp256k1_a_words_bounded :
    bounded_by loose_bounds secp256k1_a_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  (** feval of the stored felems: the Montgomery decoding of the limb
      lists is the curve constant. *)
  Lemma secp256k1_three_b_feval :
    feval (proj1_sig secp256k1_three_b_felem) = F.of_Z M_pos secp256k1_three_b_Z.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma secp256k1_a_feval :
    feval (proj1_sig secp256k1_a_felem) = F.of_Z M_pos secp256k1_a_Z.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* §2. Hbounds_eq for frep256k1                                    *)
  (* ============================================================== *)

  (** For the New-pipeline word-by-word Montgomery representation both
      bounds are the constructor [wordlist] of [bounds_type], as for
      [p256_frep] ([CurveAddGeneralA_P256.p256_bounds_eq]). *)
  Lemma secp256k1_bounds_eq :
    loose_bounds (FieldRepresentation:=Field256k1.frep256k1)
    = tight_bounds (FieldRepresentation:=Field256k1.frep256k1).
  Proof. reflexivity. Qed.

  (* ============================================================== *)
  (* §3. Constant-loader bedrock2 functions                          *)
  (* ============================================================== *)

  Definition secp256k1_three_b_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal secp256k1_tb0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal secp256k1_tb1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal secp256k1_tb2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal secp256k1_tb3)))).

  Definition secp256k1_a_const_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal secp256k1_ac0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal secp256k1_ac1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal secp256k1_ac2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal secp256k1_ac3)))).

  Definition secp256k1_three_b_func : Syntax.func :=
    (["out"], [], secp256k1_three_b_loader_body).
  Definition secp256k1_a_const_func : Syntax.func :=
    (["out"], [], secp256k1_a_const_loader_body).

  (* ============================================================== *)
  (* §4. The derived body at secp256k1, and its spec                 *)
  (* ============================================================== *)

  Definition secp256k1_curve_add_general_func : Syntax.func :=
    rcb_add_general_body "secp256k1_three_b" "secp256k1_a_const".

  (** [spec_of_rcb_add_general] for the instantiated body, from the
      generic derivation correctness [rcb_add_general_correct].  The
      loader-spec hypotheses are discharged in §5. *)
  Lemma secp256k1_curve_add_general_ok :
    forall functions,
      map.get functions "curve_add_general"
      = Some secp256k1_curve_add_general_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_three_b_loader secp256k1_three_b_felem "secp256k1_three_b" functions ->
      spec_of_a_loader secp256k1_a_felem "secp256k1_a_const" functions ->
      spec_of_rcb_add_general secp256k1_three_b_felem secp256k1_a_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Htb Ha.
    unfold secp256k1_curve_add_general_func in Henv.
    Timeout 300 refine
      (rcb_add_general_correct secp256k1_bounds_eq
         secp256k1_three_b_felem "secp256k1_three_b"
         secp256k1_a_felem "secp256k1_a_const"
         I functions _ Hmul Hadd Hsub Htb Ha).
    Timeout 120 exact Henv.
  Qed.

  (* ============================================================== *)
  (* §5. Loader proofs                                               *)
  (* ============================================================== *)

  Lemma secp256k1_three_b_loader_ok :
    forall functions,
      map.get functions "secp256k1_three_b" = Some secp256k1_three_b_func ->
      spec_of_three_b_loader secp256k1_three_b_felem "secp256k1_three_b" functions.
  Proof.
    intros functions EnvContains.
    cbv [spec_of_three_b_loader].
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
      [WeakestPrecondition.func secp256k1_three_b_func secp256k1_three_b_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := secp256k1_three_b_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact secp256k1_three_b_words_bounded
      | |- _ => idtac
      end.
    cbv [secp256k1_three_b_felem secp256k1_three_b_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  Lemma secp256k1_a_loader_ok :
    forall functions,
      map.get functions "secp256k1_a_const" = Some secp256k1_a_const_func ->
      spec_of_a_loader secp256k1_a_felem "secp256k1_a_const" functions.
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
      [WeakestPrecondition.func secp256k1_a_const_func secp256k1_a_const_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := secp256k1_a_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact secp256k1_a_words_bounded
      | |- _ => idtac
      end.
    cbv [secp256k1_a_felem secp256k1_a_words].
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
  Lemma secp256k1_curve_add_general_full :
    forall functions,
      map.get functions "curve_add_general"
        = Some secp256k1_curve_add_general_func ->
      map.get functions "secp256k1_three_b" = Some secp256k1_three_b_func ->
      map.get functions "secp256k1_a_const" = Some secp256k1_a_const_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_rcb_add_general secp256k1_three_b_felem secp256k1_a_felem functions.
  Proof.
    intros functions Hadd_env Htb_env Ha_env Hmul Hadd Hsub.
    pose proof (secp256k1_three_b_loader_ok functions Htb_env) as Htb.
    pose proof (secp256k1_a_loader_ok functions Ha_env) as Ha.
    refine (secp256k1_curve_add_general_ok functions _ Hmul Hadd Hsub Htb Ha).
    exact Hadd_env.
  Qed.

End Secp256k1_GeneralA.
