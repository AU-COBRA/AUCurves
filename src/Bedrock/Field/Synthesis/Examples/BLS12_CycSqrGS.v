(** * BLS12-381: the Granger-Scott squaring [bls12_Fp12_cyclotomic_square] at the tower instances.

    [BLS12_Pairing.bls12_Fp12_cyclotomic_square] is [CycSqrAF.af_cyc_sqr_body] at the Fp2
    representation, with multiplication by xi = [bls12_Fp2_mul_xi].  Here, in the instance terms
    of [BLS12_CycExp] (those of the cyclotomic exponentiations):

      spec_of_cyc_sqr_gs        the Rupicola contract ([CycSqrAF.spec_of_af_cyc_sqr]) at Fp2
      cyc_sqr_gs_ok             from [CycSqrAF.af_cyc_sqr_correct], the environment entry and the
                                Fp2 leaf contracts (mul, add, sub, square, mul_xi)
      cyc_sqr_gallina_fp12      the Gallina chain at Fp2 is [CyclotomicGS.fp12_cyclotomic_square]
      cyc_sqr_gs_call           the call on the six Fp2 slots of one Fp12 element: the result is
                                tight and its feval is [fp12_cyclotomic_square] of the input
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.
Require Import bedrock2.SepAutoArray.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.


Require Import Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Bedrock.Field.FieldExtensions.CycSqrAF.
Require Import Theory.BLS12Pairing.CyclotomicGS.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp2Feval.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.CycExpModel.
Require Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.Fp6.
Require Theory.BLS12Pairing.Fp12.
Require Bedrock.Field.Synthesis.Examples.BLS12_Fp6Feval.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFevalInst.
Module P := Theory.BLS12Pairing.Pairing.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.


Section BLS12_CycSqrGS.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Existing Instance BLS12_CycExp.bls12_pf_params.
    Existing Instance BLS12_CycExp.bls12_pf_params_ok.
    Existing Instance prime_field_parameters.
    Existing Instance BLS12_CycExp.bls12_Fp_rep.
    Existing Instance BLS12_CycExp.bls12_Fp_rep_ok.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Existing Instance BLS12_CycExp.bls12_Fp2_params'.
    Existing Instance BLS12_CycExp.bls12_Fp2_rep'.
    Existing Instance BLS12_CycExp.bls12_Fp6_params'.
    Existing Instance BLS12_CycExp.bls12_Fp6_rep'.
    Existing Instance BLS12_CycExp.bls12_Fp12_params'.
    Existing Instance BLS12_CycExp.bls12_Fp12_rep'.

    Local Notation bls12_Fp_rep := BLS12_CycExp.bls12_Fp_rep.
    Local Notation bls12_pf_params := BLS12_CycExp.bls12_pf_params.
    Local Notation bls12_Fp2_params' := BLS12_CycExp.bls12_Fp2_params'.
    Local Notation bls12_Fp2_rep' := BLS12_CycExp.bls12_Fp2_rep'.
    Local Notation bls12_Fp6_params' := BLS12_CycExp.bls12_Fp6_params'.
    Local Notation bls12_Fp6_rep' := BLS12_CycExp.bls12_Fp6_rep'.
    Local Notation bls12_Fp12_params' := BLS12_CycExp.bls12_Fp12_params'.
    Local Notation bls12_Fp12_rep' := BLS12_CycExp.bls12_Fp12_rep'.

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_bounded := (@AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_felem := (@AbstractField.felem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_feval := (@AbstractField.feval _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    Local Instance bls12_Fp12_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep' :=
      BLS12_CycExp.bls12_Fp12_rep_ok'.
    Local Instance bls12_Fp6_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep' :=
      BLS12_CycExp.bls12_Fp6_rep_ok'.
    Local Instance bls12_Fp2_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep' :=
      BLS12_CycExp.bls12_Fp2_rep_ok'.

    Local Notation Fp_fsw := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep).
    Local Notation Fp2_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp6_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep)).
    Local Notation fp6_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')).
    Local Notation fst_felem := (@QuadraticFieldExtensionsSpecs.fst_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation snd_felem := (@QuadraticFieldExtensionsSpecs.snd_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c0_felem := (@CubicFieldExtensionsSpecs.c0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c1_felem := (@CubicFieldExtensionsSpecs.c1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation c2_felem := (@CubicFieldExtensionsSpecs.c2_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation d0_felem := (@DodecicFieldExtensionsSpecs.d0_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation d1_felem := (@DodecicFieldExtensionsSpecs.d1_felem _ _ _ _ bls12_pf_params bls12_Fp_rep).
    Local Notation fp6_c1_off :=
      (@CubicFieldExtensions.fp6_c1_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).
    Local Notation fp6_c2_off :=
      (@CubicFieldExtensions.fp6_c2_offset _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix).


    Local Notation AFElem2 :=
      (@Compilation2_Fp2.AFElem _ _ _ _ Fp2 bls12_Fp2_params' bls12_Fp2_rep').

    (* ================================================================ *)
    (* The contract and its proof from the Rupicola derivation          *)
    (* ================================================================ *)

    (** Multiplication by xi: the model of [CubicFieldExtensions.spec_of_Fp2_mul_xi]. *)
    Definition gs_mulxi : Fp2 -> Fp2 :=
      Theory.BLS12Pairing.Fp6.fp2_mul_xi PrimeField.M_pos bls12_beta bls12_xi_re bls12_xi_im.

    Definition spec_of_cyc_sqr_gs : spec_of "bls12_Fp12_cyclotomic_square" :=
      @CycSqrAF.spec_of_af_cyc_sqr _ _ _ _ _ _ Fp2 bls12_Fp2_params' bls12_Fp2_rep' gs_mulxi.

    Lemma cyc_sqr_gs_ok : forall functions,
      map.get functions "bls12_Fp12_cyclotomic_square" =
        Some (snd BLS12_Pairing.bls12_Fp12_cyclotomic_square) ->
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_mul functions ->
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_add functions ->
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_sub functions ->
      AbstractField.unop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.un_square functions ->
      @CycSqrAF.spec_of_af_mulxi _ _ _ _ _ _ Fp2 bls12_Fp2_params' bls12_Fp2_rep'
        gs_mulxi "bls12_Fp2_mul_xi" functions ->
      spec_of_cyc_sqr_gs functions.
    Proof.
      intros functions E Hmul Hadd Hsub Hsq Hxi.
      exact (@CycSqrAF.af_cyc_sqr_correct _ _ _ _ _ _ _ _ _ _ Fp2 bls12_Fp2_params' bls12_Fp2_rep' _
               eq_refl gs_mulxi "bls12_Fp2_mul_xi" I functions E Hmul Hadd Hsub Hsq Hxi).
    Qed.

    (* ================================================================ *)
    (* The Gallina chain at Fp2 is fp12_cyclotomic_square              *)
    (* ================================================================ *)

    Add Ring Fp_ring_gs : (@Fp12Ring.Fp_ring_theory PrimeField.M_pos).

    Lemma beta_opp_one : bls12_beta = F.opp F.one.
    Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

    Lemma cyc_sqr_gallina_fp12 (x0 x1 x2 x3 x4 x5 : Fp2) :
      @CycSqrAF.af_cyc_sqr_gallina Fp2 bls12_Fp2_params' gs_mulxi x0 x1 x2 x3 x4 x5 =
      let r := fp12_cyclotomic_square (p:=PrimeField.M_pos) ((x0, x1, x2), (x3, x4, x5)) in
      \< fst (fst (fst r)), snd (fst (fst r)), snd (fst r),
         fst (fst (snd r)), snd (fst (snd r)), snd (snd r) \>.
    Proof.
      destruct x0, x1, x2, x3, x4, x5.
      cbv [CycSqrAF.af_cyc_sqr_gallina nlet stack fp12_cyclotomic_square cyc_sqr6 gs_mulxi
           AbstractField.Fadd AbstractField.Fsub AbstractField.Fmul BLS12_CycExp.bls12_Fp2_params'
           Fp2_field_parameters
           QuadraticExtensions.addp2 QuadraticExtensions.subp2 QuadraticExtensions.mulp2
           Theory.BLS12Pairing.Fp6.fp2_mul_xi
           P.fp2_add P.fp2_sub P.fp2_mul P.fp2_mul_xi fst snd bls12_xi_re bls12_xi_im].
      repeat match goal with
             | |- context [F.of_Z ?m (-1)] =>
               replace (F.of_Z m (-1)) with (F.opp (@F.one m))
                 by (apply F.eq_to_Z_iff; vm_compute; reflexivity)
             end.
      rewrite ?beta_opp_one.
      repeat match goal with
             | |- P2.pair _ _ = P2.pair _ _ => apply f_equal2
             | |- (_, _) = (_, _) => apply f_equal2
             end; ring.
    Qed.

    (* ================================================================ *)
    (* The call on one Fp12 element                                     *)
    (* ================================================================ *)

    Lemma Fp12_feval_app6 (a b : Fp6_felem) :
      List.length a = Fp6_fsw -> Fp12_feval (a ++ b) = (Fp6_feval a, Fp6_feval b).
    Proof.
      intros Ha.
      change (Fp12_feval (a ++ b)) with
        (Fp6_feval (firstn Fp6_fsw (a ++ b)), Fp6_feval (skipn Fp6_fsw (a ++ b))).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      reflexivity.
    Qed.

    Lemma Fp6_feval_app3 (a b c : Fp2_felem) :
      List.length a = Fp2_fsw -> List.length b = Fp2_fsw ->
      Fp6_feval (a ++ b ++ c) = ((Fp2_feval a, Fp2_feval b), Fp2_feval c).
    Proof.
      intros Ha Hb.
      change (Fp6_feval (a ++ b ++ c)) with
        ((Fp2_feval (firstn Fp2_fsw (a ++ b ++ c)),
          Fp2_feval (firstn Fp2_fsw (skipn Fp2_fsw (a ++ b ++ c)))),
         Fp2_feval (skipn (2 * Fp2_fsw) (a ++ b ++ c))).
      assert (Hab : List.length (a ++ b) = (2 * Fp2_fsw)%nat).
      { rewrite length_app, Ha, Hb. lia. }
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Ha).
      rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hb).
      rewrite (app_assoc a b c).
      rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hab).
      reflexivity.
    Qed.

    Lemma Fp12_feval_six (x : Fp12_felem) :
      Fp12_feval x =
      ((Fp2_feval (c0_felem (d0_felem x)), Fp2_feval (c1_felem (d0_felem x)),
        Fp2_feval (c2_felem (d0_felem x))),
       (Fp2_feval (c0_felem (d1_felem x)), Fp2_feval (c1_felem (d1_felem x)),
        Fp2_feval (c2_felem (d1_felem x)))).
    Proof. reflexivity. Qed.

    Lemma FElem_to_AFElem2 (pt : word) (w : Fp2_felem) :
      Fp2_bounded Fp2_tight w ->
      Lift1Prop.impl1 (FElem_Fp2 pt w) (AFElem2 (Some Fp2_tight) pt (Fp2_feval w)).
    Proof.
      intros Hb m H. exists w. apply sep_emp_l.
      split; [split; [reflexivity | exact Hb] | exact H].
    Qed.

    Lemma sep6_impl (A0 A1 A2 A3 A4 A5 B0 B1 B2 B3 B4 B5 R : mem -> Prop) m :
      Lift1Prop.impl1 A0 B0 -> Lift1Prop.impl1 A1 B1 -> Lift1Prop.impl1 A2 B2 ->
      Lift1Prop.impl1 A3 B3 -> Lift1Prop.impl1 A4 B4 -> Lift1Prop.impl1 A5 B5 ->
      (A0 ⋆ (A1 ⋆ (A2 ⋆ (A3 ⋆ (A4 ⋆ (A5 ⋆ R)))))) m ->
      (B0 ⋆ (B1 ⋆ (B2 ⋆ (B3 ⋆ (B4 ⋆ (B5 ⋆ R)))))) m.
    Proof.
      intros H0 H1 H2 H3 H4 H5 H.
      eapply Proper_sep_impl1; [exact H0 | | exact H]. intros m1 G1.
      eapply Proper_sep_impl1; [exact H1 | | exact G1]. intros m2 G2.
      eapply Proper_sep_impl1; [exact H2 | | exact G2]. intros m3 G3.
      eapply Proper_sep_impl1; [exact H3 | | exact G3]. intros m4 G4.
      eapply Proper_sep_impl1; [exact H4 | | exact G4]. intros m5 G5.
      eapply Proper_sep_impl1; [exact H5 | | exact G5]. intros m6 G6. exact G6.
    Qed.

    Local Ltac felem_len2 :=
      match goal with
      | |- Datatypes.length ?x = _ =>
        let Ht := fresh in
        lazymatch goal with Hp : (_ ⋆ _) ?mm |- _ =>
        eassert (Ht : (FElem_Fp2 _ x ⋆ _) mm) by ecancel_assumption end;
        let Hfe := fresh in
        destruct Ht as [? [? [_ [Hfe _]]]];
        let Hl := fresh in
        destruct Hfe as [? [? [_ [[_ Hl] _]]]];
        exact Hl
      end.

    Lemma cyc_sqr_gs_call : forall functions,
      spec_of_cyc_sqr_gs functions ->
      forall (a : word) (x : Fp12_felem) R tr m,
        Fp12_bounded Fp12_tight x ->
        (FElem_Fp12 a x ⋆ R) m ->
        WeakestPrecondition.call functions "bls12_Fp12_cyclotomic_square" tr m
          [a; word.add a fp6_c1_off; word.add a fp6_c2_off;
           word.add a (word.of_Z fp6_felem_offset);
           word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c1_off;
           word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c2_off]
          (fun tr' m' rets =>
             rets = [] /\ tr = tr' /\
             exists y : Fp12_felem,
               Fp12_bounded Fp12_tight y /\
               Fp12_feval y = fp12_cyclotomic_square (p:=PrimeField.M_pos) (Fp12_feval x) /\
               (FElem_Fp12 a y ⋆ R) m').
    Proof.
      intros functions HGS a x R tr m Hb Hm.
      change Fp12_bounded with
        (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')
             (felem : list word) =>
          Fp6_bounded b (d0_felem felem) /\ Fp6_bounded b (d1_felem felem)) in Hb.
      cbv beta in Hb. destruct Hb as [Hb0 Hb1].
      change Fp6_bounded with
        (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep')
             (felem : list word) =>
          Fp2_bounded b (c0_felem felem) /\ Fp2_bounded b (c1_felem felem) /\
          Fp2_bounded b (c2_felem felem)) in Hb0, Hb1.
      cbv beta in Hb0, Hb1. destruct Hb0 as (B0 & B1 & B2). destruct Hb1 as (B3 & B4 & B5).
      pose proof (FElem_Fp12_split6 a x R m Hm) as H6.
      eapply sep6_impl in H6;
        [| exact (FElem_to_AFElem2 _ _ B0) | exact (FElem_to_AFElem2 _ _ B1)
         | exact (FElem_to_AFElem2 _ _ B2) | exact (FElem_to_AFElem2 _ _ B3)
         | exact (FElem_to_AFElem2 _ _ B4) | exact (FElem_to_AFElem2 _ _ B5)].
      eapply Semantics.weaken_call.
      { unfold spec_of_cyc_sqr_gs, CycSqrAF.spec_of_af_cyc_sqr in HGS.
        eapply HGS. ecancel_assumption. }
      cbv beta.
      intros tr' m' rets (Hr & Htr & y0 & y1 & y2 & y3 & y4 & y5 & Hgal & Hpost).
      split; [exact Hr |]. split; [exact Htr |].
      clear Hm H6.
      unfold Compilation2_Fp2.AFElem in Hpost.
      extract_ex1_and_emp_in Hpost.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      repeat match goal with H : Fp2_feval _ = ?y |- _ => is_var y; subst y end.
      rewrite cyc_sqr_gallina_fp12, <- Fp12_feval_six in Hgal. cbv zeta in Hgal.
      set (r := fp12_cyclotomic_square (p:=PrimeField.M_pos) (Fp12_feval x)) in *.
      clearbody r. destruct r as [[[r0 r1] r2] [[r3 r4] r5]]. cbn [fst snd] in Hgal.
      injection Hgal as E0 E1 E2 E3 E4 E5.
      lazymatch type of Hpost with
      | context [FElem_Fp2 a ?w0] =>
      lazymatch type of Hpost with
      | context [FElem_Fp2 (word.add a fp6_c1_off) ?w1] =>
      lazymatch type of Hpost with
      | context [FElem_Fp2 (word.add a fp6_c2_off) ?w2] =>
      lazymatch type of Hpost with
      | context [FElem_Fp2 (word.add a (word.of_Z fp6_felem_offset)) ?w3] =>
      lazymatch type of Hpost with
      | context [FElem_Fp2 (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c1_off) ?w4] =>
      lazymatch type of Hpost with
      | context [FElem_Fp2 (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c2_off) ?w5] =>
        rename w0 into W0; rename w1 into W1; rename w2 into W2;
        rename w3 into W3; rename w4 into W4; rename w5 into W5
      end end end end end end.
      assert (L0 : Datatypes.length W0 = Fp2_fsw) by felem_len2.
      assert (L1 : Datatypes.length W1 = Fp2_fsw) by felem_len2.
      assert (L2 : Datatypes.length W2 = Fp2_fsw) by felem_len2.
      assert (L3 : Datatypes.length W3 = Fp2_fsw) by felem_len2.
      assert (L4 : Datatypes.length W4 = Fp2_fsw) by felem_len2.
      assert (L5 : Datatypes.length W5 = Fp2_fsw) by felem_len2.
      assert (L6 : Datatypes.length (W0 ++ W1 ++ W2) = Fp6_fsw)
        by (rewrite !length_app, L0, L1, L2; reflexivity).
      exists ((W0 ++ W1 ++ W2) ++ (W3 ++ W4 ++ W5)).
      split.
      { apply Fp12_bounded_join6; assumption. }
      split.
      { refine (eq_trans (Fp12_feval_app6 _ _ L6) _).
        refine (f_equal2 pair (eq_trans (Fp6_feval_app3 _ _ _ L0 L1) _)
                              (eq_trans (Fp6_feval_app3 _ _ _ L3 L4) _)).
        all: refine (f_equal2 pair (f_equal2 pair _ _) _).
        all: symmetry.
        - exact E0.
        - exact E1.
        - exact E2.
        - exact E3.
        - exact E4.
        - exact E5. }
      apply FElem_Fp12_join6; [exact L0 | exact L1 | exact L2 | exact L3 | exact L4 | exact L5 |].
      ecancel_assumption.
    Qed.

End BLS12_CycSqrGS.
