(** * P-224 instantiation of the Rupicola general-a RCB addition.

    Parallel to [CurveAddGeneralA_P256.v] /
    [CurveAddGeneralA_P256_Loaders.v], at the P-224 field
    representation [p224_frep] from
    [Bedrock.Field.Synthesis.Examples.p224_field]
    (prefix "p224_coord_", 4 limbs of 64 bits, m = 2^224 - 2^96 + 1,
    m' = 2^64 - 1).

    COMPILE-DEFERRED: this file's build needs p224_field.vo (never
    built; its [make_computed_op] synthesis is the expensive step),
    which in turn needs a rebuild of the stale p224_prime.vo
    (2026-05-22, pre-dating the 2026-08-11 stdlib install; dune
    rebuilds it on demand).  P224Curve_G1.vo is built.  The file is
    written so that it compiles unchanged once p224_field.vo is in
    place.

    Honesty ledger (this file): 1 Admitted —
    [p224_curve_add_general_bignum_bridge] (spec bridge, same
    deferral as the P-256 one). *)

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
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Field.Synthesis.Examples.p224_field.
Require Import Bedrock.Curve.P224Curve_G1.

Import Syntax ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section P224_GeneralA.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p224_field_parameters
    p224_field_parameters_ok
    p224_frep
    p224_frep_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).

  (* ============================================================== *)
  (* §1. Curve constants                                             *)
  (* ============================================================== *)

  Definition p224_m : Z := Eval vm_compute in (2^224 - 2^96 + 1).
  Definition p224_b : Z :=
    0xb4050a850c04b3abf54132565044b0b7d7bfd8ba270b39432355ffb4.
  Definition p224_a_Z : Z := Eval vm_compute in ((-3) mod p224_m).
  Definition p224_three_b_Z : Z := Eval vm_compute in ((3 * p224_b) mod p224_m).

  Definition p224_tb0 : Z := Eval vm_compute in nth 0 P224Curve_G1.p224_three_b_mont 0.
  Definition p224_tb1 : Z := Eval vm_compute in nth 1 P224Curve_G1.p224_three_b_mont 0.
  Definition p224_tb2 : Z := Eval vm_compute in nth 2 P224Curve_G1.p224_three_b_mont 0.
  Definition p224_tb3 : Z := Eval vm_compute in nth 3 P224Curve_G1.p224_three_b_mont 0.
  Definition p224_ac0 : Z := Eval vm_compute in nth 0 P224Curve_G1.p224_a_mont_list 0.
  Definition p224_ac1 : Z := Eval vm_compute in nth 1 P224Curve_G1.p224_a_mont_list 0.
  Definition p224_ac2 : Z := Eval vm_compute in nth 2 P224Curve_G1.p224_a_mont_list 0.
  Definition p224_ac3 : Z := Eval vm_compute in nth 3 P224Curve_G1.p224_a_mont_list 0.

  Definition p224_three_b_words : list word :=
    [word.of_Z p224_tb0; word.of_Z p224_tb1;
     word.of_Z p224_tb2; word.of_Z p224_tb3].
  Definition p224_a_words : list word :=
    [word.of_Z p224_ac0; word.of_Z p224_ac1;
     word.of_Z p224_ac2; word.of_Z p224_ac3].

  Example p224_three_b_words_eq :
    p224_three_b_words
    = List.map (@word.of_Z 64 word) P224Curve_G1.p224_three_b_mont.
  Proof. vm_compute. reflexivity. Qed.

  Example p224_a_words_eq :
    p224_a_words
    = List.map (@word.of_Z 64 word) P224Curve_G1.p224_a_mont_list.
  Proof. vm_compute. reflexivity. Qed.

  Example p224_three_b_mont_is_encoding :
    P224Curve_G1.p224_three_b_mont
    = MontgomeryCurveSpecs.three_b_mont_list p224_m 64 4%nat
        18446744073709551615 p224_three_b_Z.
  Proof. vm_compute. reflexivity. Qed.

  Example p224_a_mont_is_encoding :
    P224Curve_G1.p224_a_mont_list
    = MontgomeryCurveSpecs.a_mont_list p224_m 64 4%nat
        18446744073709551615 p224_a_Z.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p224_three_b_words_length :
    length p224_three_b_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p224_a_words_length :
    length p224_a_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Definition p224_three_b_felem : felem :=
    exist _ p224_three_b_words p224_three_b_words_length.
  Definition p224_a_felem : felem :=
    exist _ p224_a_words p224_a_words_length.

  Lemma p224_three_b_words_unsigned :
    List.map word.unsigned p224_three_b_words = P224Curve_G1.p224_three_b_mont.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p224_a_words_unsigned :
    List.map word.unsigned p224_a_words = P224Curve_G1.p224_a_mont_list.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p224_three_b_words_bounded :
    bounded_by loose_bounds p224_three_b_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma p224_a_words_bounded :
    bounded_by loose_bounds p224_a_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  Lemma p224_three_b_feval :
    feval (proj1_sig p224_three_b_felem) = F.of_Z M_pos p224_three_b_Z.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma p224_a_feval :
    feval (proj1_sig p224_a_felem) = F.of_Z M_pos p224_a_Z.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* §2. Hbounds_eq for p224_frep                                    *)
  (* ============================================================== *)

  Lemma p224_bounds_eq :
    loose_bounds (FieldRepresentation:=p224_frep)
    = tight_bounds (FieldRepresentation:=p224_frep).
  Proof. reflexivity. Qed.

  (* ============================================================== *)
  (* §3. Constant-loader bedrock2 functions (4 limbs)                *)
  (* ============================================================== *)

  Definition p224_three_b_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal p224_tb0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal p224_tb1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal p224_tb2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal p224_tb3)))).

  Definition p224_a_const_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal p224_ac0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal p224_ac1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal p224_ac2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal p224_ac3)))).

  Definition p224_three_b_func : Syntax.func :=
    (["out"], [], p224_three_b_loader_body).
  Definition p224_a_const_func : Syntax.func :=
    (["out"], [], p224_a_const_loader_body).

  (** Loader-spec proofs: the 4-limb P-256 loader script
      (CurveAddGeneralA_P256_Loaders.v), verbatim modulo names. *)
  Lemma p224_three_b_loader_ok :
    forall functions,
      map.get functions "p224_three_b" = Some p224_three_b_func ->
      spec_of_three_b_loader p224_three_b_felem "p224_three_b" functions.
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
      [WeakestPrecondition.func p224_three_b_func p224_three_b_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := p224_three_b_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact p224_three_b_words_bounded
      | |- _ => idtac
      end.
    cbv [p224_three_b_felem p224_three_b_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  Lemma p224_a_loader_ok :
    forall functions,
      map.get functions "p224_a_const" = Some p224_a_const_func ->
      spec_of_a_loader p224_a_felem "p224_a_const" functions.
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
      [WeakestPrecondition.func p224_a_const_func p224_a_const_loader_body].
    repeat straightline.
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := p224_a_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact p224_a_words_bounded
      | |- _ => idtac
      end.
    cbv [p224_a_felem p224_a_words].
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
  (* §4. The derived body at P-224, and its spec                     *)
  (* ============================================================== *)

  Definition p224_curve_add_general_func : Syntax.func :=
    rcb_add_general_body "p224_three_b" "p224_a_const".

  Lemma p224_curve_add_general_ok :
    forall functions,
      map.get functions "curve_add_general"
      = Some p224_curve_add_general_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_three_b_loader p224_three_b_felem "p224_three_b" functions ->
      spec_of_a_loader p224_a_felem "p224_a_const" functions ->
      spec_of_rcb_add_general p224_three_b_felem p224_a_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Htb Ha.
    unfold p224_curve_add_general_func in Henv.
    Timeout 300 refine
      (rcb_add_general_correct p224_bounds_eq
         p224_three_b_felem "p224_three_b" p224_a_felem "p224_a_const"
         I functions _ Hmul Hadd Hsub Htb Ha).
    Timeout 120 exact Henv.
  Qed.

  (* ============================================================== *)
  (* §5. Spec bridge toward the Bignum-level specification           *)
  (* ============================================================== *)

  Local Notation toZ ws := (List.map word.unsigned ws).
  Local Notation p224_valid := (WordByWordMontgomery.valid 64 4%nat p224_m).

  Definition spec_of_p224_curve_add_general_bignum
    : spec_of "curve_add_general" :=
    fun functions =>
      forall (wX1 wY1 wZ1 wX2 wY2 wZ2
              wold_outx wold_outy wold_outz : list word)
             (pX1 pY1 pZ1 pX2 pY2 pZ2 poutx pouty poutz : word)
             (tr : Semantics.trace) (m0 : BasicC64Semantics.mem)
             (Rout : BasicC64Semantics.mem -> Prop),
        p224_valid (toZ wX1) /\ p224_valid (toZ wY1) /\
        p224_valid (toZ wZ1) /\ p224_valid (toZ wX2) /\
        p224_valid (toZ wY2) /\ p224_valid (toZ wZ2) ->
        (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
         Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
         Bignum 4 poutx wold_outx * Bignum 4 pouty wold_outy *
         Bignum 4 poutz wold_outz * Rout)%sep m0 ->
        WeakestPrecondition.call functions "curve_add_general" tr m0
          [poutx; pouty; poutz; pX1; pY1; pZ1; pX2; pY2; pZ2]
          (fun tr' m' rets =>
             tr = tr' /\ rets = nil /\
             exists woutx wouty woutz : list word,
               (P224_add_Gallina_spec
                  (toZ wX1) (toZ wY1) (toZ wZ1)
                  (toZ wX2) (toZ wY2) (toZ wZ2)
                  (toZ woutx) (toZ wouty) (toZ woutz)
                /\ p224_valid (toZ woutx)
                /\ p224_valid (toZ wouty)
                /\ p224_valid (toZ woutz)) /\
               (Bignum 4 pX1 wX1 * Bignum 4 pY1 wY1 * Bignum 4 pZ1 wZ1 *
                Bignum 4 pX2 wX2 * Bignum 4 pY2 wY2 * Bignum 4 pZ2 wZ2 *
                Bignum 4 poutx woutx * Bignum 4 pouty wouty *
                Bignum 4 poutz woutz * Rout)%sep m').

  (** Same bridge shape and proof path as the P-256 one
      (CurveAddGeneralA_P256.v §5). *)
  Theorem p224_curve_add_general_bignum_bridge :
    forall functions,
      spec_of_rcb_add_general p224_three_b_felem p224_a_felem functions ->
      spec_of_p224_curve_add_general_bignum functions.
  Proof.
  Admitted.

End P224_GeneralA.
