(** * P-256 instantiation of the a = -3 RCB addition and doubling.

    Mirrors [CurveAddGeneralA_P256.v] §1-§4 and
    [CurveAddGeneralA_P256_Loaders.v], with ONE constant instead of
    two: Algorithm 4 / Algorithm 6 multiply by [b], never by [a] and
    never by [3b].

    What this file contains:
      §1  the Montgomery limbs of b, as a felem, with bounds and feval
      §2  the "p256_b" loader function and its [spec_of_b_loader] proof
      §3  the two derived bodies at P-256 and their FElem-level specs
          ([..._ok] from the generic derivation, [..._full] with the
          loader function in the table)

    What this file does NOT contain: the Bignum-level bridge
    ([spec_of_p256_curve_add_general_bignum_valid_out] and friends,
    CurveAddGeneralA_P256.v §5).  That bridge is stated against the
    Z-level chain spec of the GENERAL chain, and
    [CurveA3Equiv.rcb_add_a3_is_general] rewrites the a = -3 chain
    into the general one at (a, 3b) := (-3, 3b) — so the existing
    bridge applies after one rewrite rather than needing a second
    forty-premise Z-level chain lemma.  Wiring that rewrite through
    the bridge is the next step and is deliberately not attempted in
    the same compile.

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
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Bedrock.Group.CurveAdd.CurveAddA3.
Require Import Bedrock.Group.CurveAdd.CurveDoubleA3.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_P256.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Curve.P256Curve_G1.

Import Syntax ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Section P256_A3.

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

  (* ============================================================== *)
  (* §1. The constant b, Montgomery-encoded                          *)
  (* ============================================================== *)

  (** [MontgomeryCurveSpecs.three_b_mont_list] is the generic encoder
      "partition the Z into n limbs, then to_montgomerymod"
      (MontgomeryCurveSpecs.v:52-53); applied to [p256_b] it gives the
      limbs of b, not of 3b.  Same shape as
      [CurveAddGeneralA_P256.p256_three_b_mont_is_encoding], which is
      the same call at [p256_three_b_Z].

      [p256_b] and [p256_m] are the literals of
      CurveAddGeneralA_P256.v §1. *)
  Definition p256_b_mont : list Z := Eval vm_compute in
    MontgomeryCurveSpecs.three_b_mont_list p256_m 64 4%nat 1 p256_b.

  Definition p256_bc0 : Z := Eval vm_compute in nth 0 p256_b_mont 0.
  Definition p256_bc1 : Z := Eval vm_compute in nth 1 p256_b_mont 0.
  Definition p256_bc2 : Z := Eval vm_compute in nth 2 p256_b_mont 0.
  Definition p256_bc3 : Z := Eval vm_compute in nth 3 p256_b_mont 0.

  Definition p256_b_words : list word :=
    [word.of_Z p256_bc0; word.of_Z p256_bc1;
     word.of_Z p256_bc2; word.of_Z p256_bc3].

  Example p256_b_words_eq :
    p256_b_words = List.map (@word.of_Z 64 word) p256_b_mont.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_b_words_length :
    length p256_b_words = felem_size_in_words.
  Proof. vm_compute. reflexivity. Qed.

  Definition p256_b_felem : felem :=
    exist _ p256_b_words p256_b_words_length.

  Lemma p256_b_words_unsigned :
    List.map word.unsigned p256_b_words = p256_b_mont.
  Proof. vm_compute. reflexivity. Qed.

  Lemma p256_b_words_bounded :
    bounded_by loose_bounds p256_b_words.
  Proof. vm_compute. repeat split; congruence. Qed.

  (** The Montgomery decoding of the stored limbs is b. *)
  Lemma p256_b_feval :
    feval (proj1_sig p256_b_felem) = F.of_Z M_pos p256_b.
  Proof. apply ModularArithmeticTheorems.F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* §2. The "p256_b" loader function                                *)
  (* ============================================================== *)

  Definition p256_b_loader_body : Syntax.cmd :=
    cmd.seq (cmd.store access_size.word (expr.var "out")
               (expr.literal p256_bc0))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 8))
               (expr.literal p256_bc1))
    (cmd.seq (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 16))
               (expr.literal p256_bc2))
             (cmd.store access_size.word
               (expr.op bopname.add (expr.var "out") (expr.literal 24))
               (expr.literal p256_bc3)))).

  Definition p256_b_func : Syntax.func :=
    (["out"], [], p256_b_loader_body).

  (** Script copied from [p256_three_b_loader_ok]
      (CurveAddGeneralA_P256_Loaders.v), which is Qed; only the
      constant names change.  It uses nothing about the stored value
      beyond its four-limb shape and its [bounded_by]. *)
  Lemma p256_b_loader_ok :
    forall functions,
      map.get functions "p256_b" = Some p256_b_func ->
      CurveAddA3.spec_of_b_loader p256_b_felem "p256_b" functions.
  Proof.
    intros functions EnvContains.
    cbv [CurveAddA3.spec_of_b_loader].
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
      [WeakestPrecondition.func p256_b_func p256_b_loader_body].
    repeat straightline.
    (* 3. Postcondition. *)
    cbv [CompilationAbstract.FElem Compilation2.FElem
         CompilationAbstract.maybe_bounded Compilation2.maybe_bounded
         Field.FElem].
    ssplit; try reflexivity.
    extract_ex1_and_emp_in_goal.
    instantiate (1 := p256_b_felem).
    ssplit;
      lazymatch goal with
      | |- feval _ = _ => reflexivity
      | |- bounded_by _ _ => exact p256_b_words_bounded
      | |- _ => idtac
      end.
    cbv [p256_b_felem p256_b_words].
    cbn [array proj1_sig].
    change (Memory.bytes_per_word 64) with 8.
    replace (word.add (word.add pout (word.of_Z 8)) (word.of_Z 8))
      with (word.add pout (word.of_Z 16)) by ring.
    replace (word.add (word.add pout (word.of_Z 16)) (word.of_Z 8))
      with (word.add pout (word.of_Z 24)) by ring.
    repeat match goal with x := _ |- _ => subst x end.
    ecancel_assumption.
  Qed.

  (** [CurveDoubleA3.spec_of_b_loader] is a verbatim copy of
      [CurveAddA3.spec_of_b_loader]; applied to the same felem and
      name the two unfold to the same fnspec, so the addition loader
      proof is a proof of the doubling copy by conversion.
      PORT-CHECK (L): if [exact] does not see them as convertible,
      replay the script of [p256_b_loader_ok] against the doubling
      spec (it uses only the fnspec shape).  The attested analogue is
      [p256_three_b_loader_ok_dbl] (CurveDoubleGeneralA_P256.v:105). *)
  Lemma p256_b_loader_ok_dbl :
    forall functions,
      map.get functions "p256_b" = Some p256_b_func ->
      CurveDoubleA3.spec_of_b_loader p256_b_felem "p256_b" functions.
  Proof.
    intros functions Henv.
    Timeout 300 exact (p256_b_loader_ok functions Henv).
  Qed.

  (* ============================================================== *)
  (* §3. The derived bodies at P-256, and their specs                *)
  (* ============================================================== *)

  Definition p256_curve_add_a3_func : Syntax.func :=
    rcb_add_a3_body "p256_b".

  Definition p256_curve_double_a3_func : Syntax.func :=
    rcb_double_a3_body "p256_b".

  (** Argument order of the section-discharged derivation correctness,
      read off [p256_curve_add_general_ok] (CurveAddGeneralA_P256.v:
      263) with the [a_const] pair deleted:
        Hbounds_eq  b_const  b_name  marker  functions  Henv
        Hmul  Hadd  Hsub  Hb
      [Hb_bounds] is unused by the derivation and so is not discharged
      (the attested general-a case drops [Hb_bounds]/[Ha_bounds] the
      same way; see PORT-CHECK (C) of CurveDoubleGeneralA.v).
      PORT-CHECK (R): if the arity differs, the [Timeout 300 refine]
      reports it as a mismatch rather than searching. *)
  Lemma p256_curve_add_a3_ok :
    forall functions,
      map.get functions "curve_add_a3"
      = Some p256_curve_add_a3_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      CurveAddA3.spec_of_b_loader p256_b_felem "p256_b" functions ->
      spec_of_rcb_add_a3 p256_b_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Hb.
    unfold p256_curve_add_a3_func in Henv.
    Timeout 300 refine
      (rcb_add_a3_correct p256_bounds_eq p256_b_felem "p256_b"
         I functions _ Hmul Hadd Hsub Hb).
    Timeout 120 exact Henv.
  Qed.

  Lemma p256_curve_double_a3_ok :
    forall functions,
      map.get functions "curve_double_a3"
      = Some p256_curve_double_a3_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      CurveDoubleA3.spec_of_b_loader p256_b_felem "p256_b" functions ->
      spec_of_rcb_double_a3 p256_b_felem functions.
  Proof.
    intros functions Henv Hmul Hadd Hsub Hb.
    unfold p256_curve_double_a3_func in Henv.
    Timeout 300 refine
      (rcb_double_a3_correct p256_bounds_eq p256_b_felem "p256_b"
         I functions _ Hmul Hadd Hsub Hb).
    Timeout 120 exact Henv.
  Qed.

  (** End-to-end: with the loader function and the three field ops in
      the table, each derived body meets its FElem-level spec.
      Explicit discharge (no [eauto], no [eapply] against the
      [spec_of_*] conclusion): the search form of this sentence
      measured 88 s at four limbs and 853 s at six
      (scripts/logs/p256_g1_add_debug_notes.md). *)
  Lemma p256_curve_add_a3_full :
    forall functions,
      map.get functions "curve_add_a3" = Some p256_curve_add_a3_func ->
      map.get functions "p256_b" = Some p256_b_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_rcb_add_a3 p256_b_felem functions.
  Proof.
    intros functions Hadd_env Hb_env Hmul Hadd Hsub.
    pose proof (p256_b_loader_ok functions Hb_env) as Hb.
    refine (p256_curve_add_a3_ok functions _ Hmul Hadd Hsub Hb).
    exact Hadd_env.
  Qed.

  Lemma p256_curve_double_a3_full :
    forall functions,
      map.get functions "curve_double_a3" = Some p256_curve_double_a3_func ->
      map.get functions "p256_b" = Some p256_b_func ->
      spec_of_BinOp bin_mul functions ->
      spec_of_BinOp bin_add functions ->
      spec_of_BinOp bin_sub functions ->
      spec_of_rcb_double_a3 p256_b_felem functions.
  Proof.
    intros functions Hdbl_env Hb_env Hmul Hadd Hsub.
    pose proof (p256_b_loader_ok_dbl functions Hb_env) as Hb.
    refine (p256_curve_double_a3_ok functions _ Hmul Hadd Hsub Hb).
    exact Hdbl_env.
  Qed.

End P256_A3.
