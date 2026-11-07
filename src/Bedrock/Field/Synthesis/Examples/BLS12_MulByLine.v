(** * BLS12-381: the sparse multiplication [bls12_Fp12_mul_by_line] at the tower instances.

    [BLS12_Pairing.bls12_Fp12_mul_by_line] is [MulByLineAF.af_mul_by_line_body] at the Fp2
    representation (multiplication by xi = [bls12_Fp2_mul_xi]).  In the instance terms of
    [BLS12_CycExp]:

      spec_of_mul_by_line      the Rupicola contract ([MulByLineAF.spec_of_af_mul_by_line]) at Fp2
      mul_by_line_ok           from [MulByLineAF.af_mul_by_line_correct], the environment entry and
                               the Fp2 leaf contracts (mul, add, sub, mul_xi)
      mul_by_line_gallina_fp12 the Gallina chain at Fp2 is [SparseLine.mul_by_line6]
      mul_by_line_call         the call on the six slots of f and three slots of a line buffer:
                               feval f' = fp12_mul (feval f) (sparse_part (feval line)); the line
                               buffer keeps its feval and bounds
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
Require Bedrock.Field.FieldExtensions.MulByLineAF.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycSqrGS.
Require Import Theory.BLS12Pairing.SparseLine.
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


Section BLS12_MulByLine.

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
    Local Notation gs_mulxi := BLS12_CycSqrGS.gs_mulxi.

    Definition spec_of_mul_by_line : spec_of "bls12_Fp12_mul_by_line" :=
      @MulByLineAF.spec_of_af_mul_by_line _ _ _ _ _ _ Fp2 bls12_Fp2_params' bls12_Fp2_rep' gs_mulxi.

    Lemma mul_by_line_ok : forall functions,
      map.get functions "bls12_Fp12_mul_by_line" =
        Some (snd BLS12_Pairing.bls12_Fp12_mul_by_line) ->
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_mul functions ->
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_add functions ->
      AbstractField.binop_spec (F:=Fp2) (field_representation:=bls12_Fp2_rep') AbstractField.bin_sub functions ->
      @CycSqrAF.spec_of_af_mulxi _ _ _ _ _ _ Fp2 bls12_Fp2_params' bls12_Fp2_rep'
        gs_mulxi "bls12_Fp2_mul_xi" functions ->
      spec_of_mul_by_line functions.
    Proof.
      intros functions E Hmul Hadd Hsub Hxi.
      exact (@MulByLineAF.af_mul_by_line_correct _ _ _ _ _ _ _ _ _ _ Fp2 bls12_Fp2_params' bls12_Fp2_rep' _
               eq_refl gs_mulxi "bls12_Fp2_mul_xi" I functions E Hmul Hadd Hsub Hxi).
    Qed.

    Add Ring Fp_ring_mbl : (@Fp12Ring.Fp_ring_theory PrimeField.M_pos).

    Lemma mul_by_line_gallina_fp12 (x0 x1 x2 x3 x4 x5 b0 b1 b4 : Fp2) :
      @MulByLineAF.af_mul_by_line_gallina Fp2 bls12_Fp2_params' gs_mulxi x0 x1 x2 x3 x4 x5 b0 b1 b4 =
      let r := mul_by_line6 (p:=PrimeField.M_pos) x0 x1 x2 x3 x4 x5 b0 b1 b4 in
      \< fst (fst (fst r)), snd (fst (fst r)), snd (fst r),
         fst (fst (snd r)), snd (fst (snd r)), snd (snd r) \>.
    Proof.
      destruct x0, x1, x2, x3, x4, x5, b0, b1, b4.
      cbv [MulByLineAF.af_mul_by_line_gallina nlet stack mul_by_line6 gs_mulxi BLS12_CycSqrGS.gs_mulxi
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
      rewrite ?BLS12_CycSqrGS.beta_opp_one.
      repeat match goal with
             | |- P2.pair _ _ = P2.pair _ _ => apply f_equal2
             | |- (_, _) = (_, _) => apply f_equal2
             end; ring.
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

    Local Ltac split_bounds12 Hb B0 B1 B2 B3 B4 B5 :=
      change Fp12_bounded with
        (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')
             (felem : list word) =>
          Fp6_bounded b (d0_felem felem) /\ Fp6_bounded b (d1_felem felem)) in Hb;
      cbv beta in Hb;
      let H0 := fresh in let H1 := fresh in
      destruct Hb as [H0 H1];
      change Fp6_bounded with
        (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep')
             (felem : list word) =>
          Fp2_bounded b (c0_felem felem) /\ Fp2_bounded b (c1_felem felem) /\
          Fp2_bounded b (c2_felem felem)) in H0, H1;
      cbv beta in H0, H1;
      destruct H0 as (B0 & B1 & B2); destruct H1 as (B3 & B4 & B5).

    Lemma mul_by_line_call : forall functions,
      spec_of_mul_by_line functions ->
      forall (a pl : word) (x l : Fp12_felem) R tr m,
        Fp12_bounded Fp12_tight x ->
        Fp12_bounded Fp12_tight l ->
        (FElem_Fp12 a x ⋆ (FElem_Fp12 pl l ⋆ R)) m ->
        WeakestPrecondition.call functions "bls12_Fp12_mul_by_line" tr m
          [a; word.add a fp6_c1_off; word.add a fp6_c2_off;
           word.add a (word.of_Z fp6_felem_offset);
           word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c1_off;
           word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c2_off;
           pl; word.add pl fp6_c1_off;
           word.add (word.add pl (word.of_Z fp6_felem_offset)) fp6_c1_off]
          (fun tr' m' rets =>
             rets = [] /\ tr = tr' /\
             exists y : Fp12_felem,
               Fp12_feval y = P.fp12_mul PrimeField.M_pos (Fp12_feval x) (sparse_part (Fp12_feval l)) /\
               Fp12_bounded Fp12_tight y /\
               exists l' : Fp12_felem,
                 Fp12_feval l' = Fp12_feval l /\ Fp12_bounded Fp12_tight l' /\
                 (FElem_Fp12 a y ⋆ (FElem_Fp12 pl l' ⋆ R)) m').
    Proof.
      intros functions HM a pl x l R tr m Hbx Hbl Hm.
      split_bounds12 Hbx X0 X1 X2 X3 X4 X5.
      pose proof Hbl as Hbl'.
      split_bounds12 Hbl' L0 L1 L2 L3 L4 L5.
      pose proof (FElem_Fp12_split6 a x _ m Hm) as H6.
      eapply BLS12_CycSqrGS.sep6_impl in H6;
        [| exact (BLS12_CycSqrGS.FElem_to_AFElem2 _ _ X0) | exact (BLS12_CycSqrGS.FElem_to_AFElem2 _ _ X1)
         | exact (BLS12_CycSqrGS.FElem_to_AFElem2 _ _ X2) | exact (BLS12_CycSqrGS.FElem_to_AFElem2 _ _ X3)
         | exact (BLS12_CycSqrGS.FElem_to_AFElem2 _ _ X4) | exact (BLS12_CycSqrGS.FElem_to_AFElem2 _ _ X5)].
      assert (Hl6 : (FElem_Fp12 pl l ⋆
                     (AFElem2 (Some Fp2_tight) a (Fp2_feval (c0_felem (d0_felem x))) ⋆
                      (AFElem2 (Some Fp2_tight) (word.add a fp6_c1_off) (Fp2_feval (c1_felem (d0_felem x))) ⋆
                       (AFElem2 (Some Fp2_tight) (word.add a fp6_c2_off) (Fp2_feval (c2_felem (d0_felem x))) ⋆
                        (AFElem2 (Some Fp2_tight) (word.add a (word.of_Z fp6_felem_offset))
                           (Fp2_feval (c0_felem (d1_felem x))) ⋆
                         (AFElem2 (Some Fp2_tight)
                            (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c1_off)
                            (Fp2_feval (c1_felem (d1_felem x))) ⋆
                          (AFElem2 (Some Fp2_tight)
                             (word.add (word.add a (word.of_Z fp6_felem_offset)) fp6_c2_off)
                             (Fp2_feval (c2_felem (d1_felem x))) ⋆ R))))))) m)
        by ecancel_assumption.
      clear H6 Hm.
      apply (FElem_Fp12_split6 pl l _ m) in Hl6.
      eapply Semantics.weaken_call.
      { unfold spec_of_mul_by_line, MulByLineAF.spec_of_af_mul_by_line in HM.
        eapply HM.
        pose proof (BLS12_CycSqrGS.FElem_to_AFElem2 pl _ L0) as I0.
        pose proof (BLS12_CycSqrGS.FElem_to_AFElem2 (word.add pl fp6_c1_off) _ L1) as I1.
        pose proof (BLS12_CycSqrGS.FElem_to_AFElem2
          (word.add (word.add pl (word.of_Z fp6_felem_offset)) fp6_c1_off) _ L4) as I4.
        eassert (Hl6' : (AFElem2 (Some Fp2_tight) pl (Fp2_feval (c0_felem (d0_felem l))) ⋆
                         (AFElem2 (Some Fp2_tight) (word.add pl fp6_c1_off)
                            (Fp2_feval (c1_felem (d0_felem l))) ⋆
                          (FElem_Fp2 (word.add pl fp6_c2_off) (c2_felem (d0_felem l)) ⋆
                           (FElem_Fp2 (word.add pl (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem l)) ⋆
                            (AFElem2 (Some Fp2_tight)
                               (word.add (word.add pl (word.of_Z fp6_felem_offset)) fp6_c1_off)
                               (Fp2_feval (c1_felem (d1_felem l))) ⋆
                             (FElem_Fp2 (word.add (word.add pl (word.of_Z fp6_felem_offset)) fp6_c2_off)
                                (c2_felem (d1_felem l)) ⋆ _)))))) m).
        { eapply BLS12_CycSqrGS.sep6_impl;
            [exact I0 | exact I1 | intros ? H; exact H | intros ? H; exact H | exact I4
            | intros ? H; exact H | exact Hl6]. }
        ecancel_assumption. }
      cbv beta.
      intros tr' m' rets (Hr & Htr & y0 & y1 & y2 & y3 & y4 & y5 & Hgal & Hpost).
      split; [exact Hr |]. split; [exact Htr |].
      clear Hl6.
      unfold Compilation2_Fp2.AFElem in Hpost.
      extract_ex1_and_emp_in Hpost.
      repeat match goal with H : _ /\ _ |- _ => destruct H end.
      repeat match goal with H : Fp2_feval _ = ?y |- _ => is_var y; subst y end.
      rewrite mul_by_line_gallina_fp12 in Hgal. cbv zeta in Hgal.
      set (r := mul_by_line6 (p:=PrimeField.M_pos) _ _ _ _ _ _ _ _ _) in Hgal.
      assert (Hr6 : r = P.fp12_mul PrimeField.M_pos (Fp12_feval x) (sparse_part (Fp12_feval l))).
      { subst r. rewrite (BLS12_CycSqrGS.Fp12_feval_six x), (BLS12_CycSqrGS.Fp12_feval_six l).
        exact (fp12_mul_by_line_eq
                 ((Fp2_feval (c0_felem (d0_felem x)), Fp2_feval (c1_felem (d0_felem x)),
                   Fp2_feval (c2_felem (d0_felem x))),
                  (Fp2_feval (c0_felem (d1_felem x)), Fp2_feval (c1_felem (d1_felem x)),
                   Fp2_feval (c2_felem (d1_felem x))))
                 (Fp2_feval (c0_felem (d0_felem l))) (Fp2_feval (c1_felem (d0_felem l)))
                 (Fp2_feval (c1_felem (d1_felem l)))). }
      clearbody r. subst r.
      set (r := P.fp12_mul PrimeField.M_pos (Fp12_feval x) (sparse_part (Fp12_feval l))) in *.
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
      lazymatch type of Hpost with
      | context [FElem_Fp2 pl ?v0] =>
      lazymatch type of Hpost with
      | context [FElem_Fp2 (word.add pl fp6_c1_off) ?v1] =>
      lazymatch type of Hpost with
      | context [FElem_Fp2 (word.add (word.add pl (word.of_Z fp6_felem_offset)) fp6_c1_off) ?v4] =>
        rename w0 into W0; rename w1 into W1; rename w2 into W2;
        rename w3 into W3; rename w4 into W4; rename w5 into W5;
        rename v0 into V0; rename v1 into V1; rename v4 into V4
      end end end end end end end end end.
      assert (LW0 : Datatypes.length W0 = Fp2_fsw) by felem_len2.
      assert (LW1 : Datatypes.length W1 = Fp2_fsw) by felem_len2.
      assert (LW2 : Datatypes.length W2 = Fp2_fsw) by felem_len2.
      assert (LW3 : Datatypes.length W3 = Fp2_fsw) by felem_len2.
      assert (LW4 : Datatypes.length W4 = Fp2_fsw) by felem_len2.
      assert (LW5 : Datatypes.length W5 = Fp2_fsw) by felem_len2.
      assert (LV0 : Datatypes.length V0 = Fp2_fsw) by felem_len2.
      assert (LV1 : Datatypes.length V1 = Fp2_fsw) by felem_len2.
      assert (LV4 : Datatypes.length V4 = Fp2_fsw) by felem_len2.
      assert (LU2 : Datatypes.length (c2_felem (d0_felem l)) = Fp2_fsw) by felem_len2.
      assert (LU3 : Datatypes.length (c0_felem (d1_felem l)) = Fp2_fsw) by felem_len2.
      assert (LU5 : Datatypes.length (c2_felem (d1_felem l)) = Fp2_fsw) by felem_len2.
      assert (L6 : Datatypes.length (W0 ++ W1 ++ W2) = Fp6_fsw)
        by (rewrite !length_app, LW0, LW1, LW2; reflexivity).
      assert (L6' : Datatypes.length (V0 ++ V1 ++ c2_felem (d0_felem l)) = Fp6_fsw)
        by (rewrite !length_app, LV0, LV1, LU2; reflexivity).
      exists ((W0 ++ W1 ++ W2) ++ (W3 ++ W4 ++ W5)).
      split.
      { refine (eq_trans (BLS12_CycSqrGS.Fp12_feval_app6 _ _ L6) _).
        refine (f_equal2 pair (eq_trans (BLS12_CycSqrGS.Fp6_feval_app3 _ _ _ LW0 LW1) _)
                              (eq_trans (BLS12_CycSqrGS.Fp6_feval_app3 _ _ _ LW3 LW4) _)).
        all: refine (f_equal2 pair (f_equal2 pair _ _) _).
        all: symmetry.
        - exact E0.
        - exact E1.
        - exact E2.
        - exact E3.
        - exact E4.
        - exact E5. }
      split.
      { apply Fp12_bounded_join6;
          lazymatch goal with
          | H : Datatypes.length ?w = _ |- Datatypes.length ?w = _ => exact H
          | H : Fp2_bounded _ ?w |- Fp2_bounded _ ?w => exact H
          end. }
      exists ((V0 ++ V1 ++ c2_felem (d0_felem l)) ++ (c0_felem (d1_felem l) ++ V4 ++ c2_felem (d1_felem l))).
      split.
      { refine (eq_trans (BLS12_CycSqrGS.Fp12_feval_app6 _ _ L6') _).
        refine (eq_trans _ (eq_sym (BLS12_CycSqrGS.Fp12_feval_six l))).
        refine (f_equal2 pair (eq_trans (BLS12_CycSqrGS.Fp6_feval_app3 _ _ _ LV0 LV1) _)
                              (eq_trans (BLS12_CycSqrGS.Fp6_feval_app3 _ _ _ LU3 LV4) _)).
        all: refine (f_equal2 pair (f_equal2 pair _ _) _).
        all: lazymatch goal with
             | H : Fp2_feval ?V = _ |- Fp2_feval ?V = _ => exact H
             | |- _ => reflexivity
             end. }
      split.
      { apply Fp12_bounded_join6;
          lazymatch goal with
          | H : Datatypes.length ?w = _ |- Datatypes.length ?w = _ => exact H
          | H : Fp2_bounded _ ?w |- Fp2_bounded _ ?w => exact H
          end. }
      eassert (Hj : (FElem_Fp12 pl ((V0 ++ V1 ++ c2_felem (d0_felem l)) ++
                                     (c0_felem (d1_felem l) ++ V4 ++ c2_felem (d1_felem l))) ⋆ _) m').
      { apply FElem_Fp12_join6; [exact LV0 | exact LV1 | exact LU2 | exact LU3 | exact LV4 | exact LU5 |].
        ecancel_assumption. }
      eassert (Hj2 : (FElem_Fp12 a ((W0 ++ W1 ++ W2) ++ (W3 ++ W4 ++ W5)) ⋆ _) m').
      { apply FElem_Fp12_join6; [exact LW0 | exact LW1 | exact LW2 | exact LW3 | exact LW4 | exact LW5 |].
        ecancel_assumption. }
      ecancel_assumption.
    Qed.

End BLS12_MulByLine.
