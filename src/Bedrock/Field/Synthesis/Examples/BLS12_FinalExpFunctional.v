(** * BLS12-381 final exponentiation: functional WP proof

    Functional version of [bls12_final_exp_ok] (BLS12_FinalExp.v).
    Callee specs are hypotheses with their feval equalities; the hard part is
    [bls12_final_exp_hard_dsd], whose functional spec is proved in
    BLS12_FinalExpHardDSDFunctional.v.

      bls12_final_exp_functional_ok : post (besides bounds and frame)
        feval gamma1_p2 = frob_gamma1_p2 -> feval gamma2_p2 = frob_gamma2_p2 ->
        feval w_frob_p2_c1 = frob_coeff_fp12_p2_c1 ->
        fp12_mul F (fp12_inv F) = fp12_one ->                    (F = feval f)
        feval out = Pairing.final_exponentiation_dsd p gamma1_381 gamma2_381
                      gamma1_p2_381 gamma2_p2_381 c1_381 c1_p2_381 F
        /\ feval out = Pairing.final_exponentiation p frob_gamma1_p2 frob_gamma2_p2
                      frob_coeff_fp12_p2_c1 F
      (frob_* : BLS12_FrobConstants.v = Commitments' constants; *_381 : Frob381.v.)
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

Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.Frob381.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExpModel381.
Require Import Theory.BLS12Pairing.Fp12Field381.
Require Theory.BLS12Pairing.CyclotomicGS.
Require Theory.BLS12Pairing.Pairing.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFevalInst.
Module P := Theory.BLS12Pairing.Pairing.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Record hidden (P : Prop) : Prop := hide { unhide : P }.

Section BLS12_FinalExpFunctional.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Existing Instance BLS12_FinalExp.bls12_pf_params.
    Existing Instance BLS12_FinalExp.bls12_pf_params_ok.
    Existing Instance prime_field_parameters.
    Existing Instance BLS12_FinalExp.bls12_Fp_rep.
    Existing Instance BLS12_FinalExp.bls12_Fp_rep_ok.

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

    Existing Instance BLS12_FinalExp.bls12_Fp2_params'.
    Existing Instance BLS12_FinalExp.bls12_Fp2_rep'.
    Existing Instance BLS12_FinalExp.bls12_Fp6_params'.
    Existing Instance BLS12_FinalExp.bls12_Fp6_rep'.
    Existing Instance BLS12_FinalExp.bls12_Fp12_params'.
    Existing Instance BLS12_FinalExp.bls12_Fp12_rep'.

    Local Notation bls12_Fp_rep := BLS12_FinalExp.bls12_Fp_rep.
    Local Notation bls12_pf_params := BLS12_FinalExp.bls12_pf_params.
    Local Notation bls12_Fp2_params' := BLS12_FinalExp.bls12_Fp2_params'.
    Local Notation bls12_Fp2_rep' := BLS12_FinalExp.bls12_Fp2_rep'.
    Local Notation bls12_Fp12_params' := BLS12_FinalExp.bls12_Fp12_params'.
    Local Notation bls12_Fp12_rep' := BLS12_FinalExp.bls12_Fp12_rep'.

    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').
    Local Notation Fp2_feval := (@AbstractField.feval _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep').

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque BLS12_FinalExp.bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    Local Instance bls12_Fp12_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep' :=
      BLS12_FinalExp.bls12_Fp12_rep_ok'.
    Local Instance bls12_Fp2_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep' :=
      BLS12_FinalExp.bls12_Fp2_rep_ok'.

    (* ================================================================ *)
    (* Functional callee specs                                          *)
    (* ================================================================ *)

    Let fp12_frobenius_p2_name : string := (fp12_prefix ++ "frobenius_p2")%string.
    Definition spec_of_Fp12_frobenius_p2_functional : spec_of fp12_frobenius_p2_name :=
      fnspec! fp12_frobenius_p2_name
        (pout px pgamma1_p2 pgamma2_p2 pw_frob_p2_c1 : word)
        / (old_out x : Fp12_felem) (gamma1_p2 gamma2_p2 w_frob_p2_c1 : Fp2_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight x /\
          Fp2_bounded Fp2_loose gamma1_p2 /\
          Fp2_bounded Fp2_loose gamma2_p2 /\
          Fp2_bounded Fp2_loose w_frob_p2_c1 /\
          (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
             (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_feval out = P.fp12_frobenius_p2 PrimeField.M_pos
              (Fp2_feval gamma1_p2) (Fp2_feval gamma2_p2) (Fp2_feval w_frob_p2_c1) (Fp12_feval x) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 px x ⋆
              (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
               (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
                (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))) mem' }.

    (* The functional spec of the hard part (BLS12_FinalExpHardDSDFunctional.v) *)
    Definition spec_of_bls12_final_exp_hard_dsd_functional : spec_of "bls12_final_exp_hard_dsd" :=
      fnspec! "bls12_final_exp_hard_dsd"
        (pout pf pg1p2 pg2p2 pwp2 : word)
        / (old_out f_val : Fp12_felem) (g1p2 g2p2 wp2 : Fp2_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight f_val /\
          Fp2_bounded Fp2_loose g1p2 /\
          Fp2_bounded Fp2_loose g2p2 /\
          Fp2_bounded Fp2_loose wp2 /\
          (FElem_Fp12 pf f_val ⋆ (FElem_Fp2 pg1p2 g1p2 ⋆
            (FElem_Fp2 pg2p2 g2p2 ⋆
             (FElem_Fp2 pwp2 wp2 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            (CyclotomicGS.gs (Fp12_feval f_val) ->
             Fp12_feval out = P.final_exp_hard_dsd PrimeField.M_pos gamma1_381 gamma2_381
               (Fp2_feval g1p2) (Fp2_feval g2p2) c1_381 (Fp2_feval wp2) (Fp12_feval f_val)) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f_val ⋆
              (FElem_Fp2 pg1p2 g1p2 ⋆
               (FElem_Fp2 pg2p2 g2p2 ⋆
                (FElem_Fp2 pwp2 wp2 ⋆ Rr))))) mem' }.

    Definition spec_of_bls12_final_exp_functional : spec_of "bls12_final_exp" :=
      fnspec! "bls12_final_exp"
        (pout pf p_gamma1_p2 p_gamma2_p2 p_w_frob_p2_c1 : word)
        / (old_out f : Fp12_felem) (gamma1_p2 gamma2_p2 w_frob_p2_c1 : Fp2_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight f /\
          Fp2_bounded Fp2_tight gamma1_p2 /\
          Fp2_bounded Fp2_tight gamma2_p2 /\
          Fp2_bounded Fp2_tight w_frob_p2_c1 /\
          (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
             (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            (Fp2_feval gamma1_p2 = BLS12_381_Frob.frob_gamma1_p2 ->
             Fp2_feval gamma2_p2 = BLS12_381_Frob.frob_gamma2_p2 ->
             Fp2_feval w_frob_p2_c1 = BLS12_381_Frob.frob_coeff_fp12_p2_c1 ->
             P.fp12_mul PrimeField.M_pos (Fp12_feval f) (P.fp12_inv PrimeField.M_pos (Fp12_feval f)) =
               P.fp12_one PrimeField.M_pos ->
             Fp12_feval out = P.final_exponentiation_dsd PrimeField.M_pos gamma1_381 gamma2_381
               gamma1_p2_381 gamma2_p2_381 c1_381 c1_p2_381 (Fp12_feval f) /\
             Fp12_feval out = P.final_exponentiation PrimeField.M_pos BLS12_381_Frob.frob_gamma1_p2
               BLS12_381_Frob.frob_gamma2_p2 BLS12_381_Frob.frob_coeff_fp12_p2_c1 (Fp12_feval f)) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f ⋆
              (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
               (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
                (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))) mem' }.

    Lemma F12mul_eq' (o a b : Fp12) :
      o = @AbstractField.Fmul _ bls12_Fp12_params' a b -> o = P.fp12_mul PrimeField.M_pos a b.
    Proof. intros ->. exact (BLS12_PairingFevalInst.fp12_mul_eq_closed PrimeField.M_pos a b). Qed.

    Lemma F12inv_eq' (o a : Fp12) :
      o = @AbstractField.Finv _ bls12_Fp12_params' a -> o = P.fp12_inv PrimeField.M_pos a.
    Proof. intros ->. exact (BLS12_PairingFevalInst.fp12_inv_eq_closed PrimeField.M_pos a). Qed.

    Lemma F12conj_eq' (o a : Fp12) :
      o = @AbstractField.un_model _ _ _ _ _ bls12_Fp12_params' bls12_Fp12_rep' _
            (@DodecicFieldExtensions.un_Fp12_conjugate _ _ _ _
               bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix) a ->
      o = P.fp12_conjugate PrimeField.M_pos a.
    Proof. intros ->. destruct a as [a0 a1]. reflexivity. Qed.

    Local Ltac dealloc_with P :=
      match goal with
      | |- exists _ _, Memory.anybytes ?a _ _ /\ _ =>
        let H := fresh in
        eassert (H : (_ ⋆ P a _) _) by ecancel_assumption;
        destruct H as [? [? [[? ?] [? ?]]]];
        eexists _, _;
        split; [eapply AbstractField.FElem_to_bytes; eassumption|];
        split; [split; [eassumption | eassumption]|]
      end.

    Lemma bls12_final_exp_functional_ok :
      forall functions
        (EnvContains : map.get functions "bls12_final_exp" = Some (snd bls12_final_exp))
        (HFp12mul : BLS12_FinalExp.spec_of_Fp12_mul functions)
        (HFp12inv : BLS12_FinalExp.spec_of_Fp12_inv functions)
        (HFp12conj : BLS12_FinalExp.spec_of_Fp12_conjugate functions)
        (HFp12frob : spec_of_Fp12_frobenius_p2_functional functions)
        (HFhard : spec_of_bls12_final_exp_hard_dsd_functional functions),
      spec_of_bls12_final_exp_functional functions.
    Proof.
      intros. unfold spec_of_bls12_final_exp_functional.
      intros pout pf p_gamma1_p2 p_gamma2_p2 p_w_frob_p2_c1
        old_out f gamma1_p2 gamma2_p2 w_frob_p2_c1 Rr tr mem0
        [Hbf [Hbg1 [Hbg2 [Hbw Hsep]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_final_exp. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }

      straightline. split. { apply Z_mod_mult. }
      intros a_result mSr mCr HaSr HmSr.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_result mSr) HaSr) as [ri Hri].
      straightline. split. { apply Z_mod_mult. }
      intros a_tmp mSt mCt HaSt HmSt.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_tmp mSt) HaSt) as [ti Hti].

      unfold BLS12_Pairing.final_exp_full_body, BLS12_Pairing.cmd_seq_list.

      pose proof (proj1 (map.split_comm mCr mem0 mSr) HmSr) as HmSr'.
      assert (Hsep1 :
        (FElem_Fp12 a_result ri ⋆
         (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
           (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
             (FElem_Fp12 pout old_out ⋆ Rr)))))) mCr).
      { exists mSr, mem0. exact (conj HmSr' (conj Hri Hsep)). }
      pose proof (proj1 (map.split_comm mCt mCr mSt) HmSt) as HmSt'.
      assert (Hsep_all :
        (FElem_Fp12 a_tmp ti ⋆
         (FElem_Fp12 a_result ri ⋆
          (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr))))))) mCt).
      { exists mSt, mCr. exact (conj HmSt' (conj Hti Hsep1)). }
      clear Hsep Hsep1 HmSr HmSt HmSr' HmSt' HaSr HaSt Hri Hti.

      (* Call 1: fp12_conjugate(result, f) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets1 [Htr1 [conj_out [E1 [Hbound_conj Hsep_conj]]]]].
      subst. apply F12conj_eq' in E1. apply hide in E1.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 2: fp12_inv(tmp, f) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12inv.
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets2 [Htr2 [inv_out [E2 [Hbound_inv Hsep_inv]]]]].
      subst. apply F12inv_eq' in E2. apply hide in E2.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 3: fp12_mul(result, result, tmp) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hbound_conj |].
           split; [exact Hbound_inv |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets3 [Htr3 [mul1_out [E3 [Hbound_mul1 Hsep_mul1]]]]].
      subst. apply F12mul_eq' in E3. apply hide in E3.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 4: fp12_frobenius_p2(tmp, result, g1, g2, w) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hbound_mul1 |].
           split; [exact Hbg1 |].
           split; [exact Hbg2 |].
           split; [exact Hbw |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets4 [Htr4 [frob_out [E4 [Hbound_frob Hsep_frob]]]]].
      subst. apply hide in E4.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 5: fp12_mul(result, tmp, result) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hbound_frob |].
           split; [exact Hbound_mul1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets5 [Htr5 [mul2_out [E5 [Hbound_mul2 Hsep_mul2]]]]].
      subst. apply F12mul_eq' in E5. apply hide in E5.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 6: bls12_final_exp_hard_dsd(out, result, g1, g2, w) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFhard.
           split; [exact Hbound_mul2 |].
           split; [exact Hbg1 |].
           split; [exact Hbg2 |].
           split; [exact Hbw |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets6 [Htr6 [hard_out [E6 [Hbound_hard Hsep_hard]]]]].
      subst. apply hide in E6.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      do 2 dealloc_with constr:(FElem_Fp12).

      cbv [list_map list_map_body WeakestPrecondition.get].
      split. { reflexivity. }
      split. { reflexivity. }
      exists hard_out.
      split.
      { intros Hg1 Hg2 Hw Hinv.
        apply unhide in E1, E2, E3, E4, E5, E6.
        rewrite frob_gamma1_p2_381 in Hg1. rewrite frob_gamma2_p2_381 in Hg2.
        rewrite frob_coeff_fp12_p2_c1_381 in Hw.
        rewrite Hg1, Hg2, Hw in E4. rewrite Hg1, Hg2, Hw in E6.
        pose proof (CyclotomicGS.easy_gs_381 _ _ _ _ _ _ Hinv E1 E2 E3 E4 E5) as C5.
        specialize (E6 C5).
        pose proof (easy_chain _ _ _ _ _ _ _ _ _ _ E1 E2 E3 E4 E5 E6) as Hdsd.
        split; [exact Hdsd |].
        rewrite Hdsd. exact (final_exponentiation_dsd_381_frob _ Hinv). }
      split. { exact Hbound_hard. }
      ecancel_assumption.
    Qed.

    (** With (d): the invertibility hypothesis is [feval f <> 0] (Fp12Field381.fp12_inv_ok). *)
    Definition spec_of_bls12_final_exp_nonzero : spec_of "bls12_final_exp" :=
      fnspec! "bls12_final_exp"
        (pout pf p_gamma1_p2 p_gamma2_p2 p_w_frob_p2_c1 : word)
        / (old_out f : Fp12_felem) (gamma1_p2 gamma2_p2 w_frob_p2_c1 : Fp2_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight f /\
          Fp2_bounded Fp2_tight gamma1_p2 /\
          Fp2_bounded Fp2_tight gamma2_p2 /\
          Fp2_bounded Fp2_tight w_frob_p2_c1 /\
          (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
             (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            (Fp2_feval gamma1_p2 = BLS12_381_Frob.frob_gamma1_p2 ->
             Fp2_feval gamma2_p2 = BLS12_381_Frob.frob_gamma2_p2 ->
             Fp2_feval w_frob_p2_c1 = BLS12_381_Frob.frob_coeff_fp12_p2_c1 ->
             Fp12_feval f <> P.fp12_zero PrimeField.M_pos ->
             Fp12_feval out = P.final_exponentiation PrimeField.M_pos BLS12_381_Frob.frob_gamma1_p2
               BLS12_381_Frob.frob_gamma2_p2 BLS12_381_Frob.frob_coeff_fp12_p2_c1 (Fp12_feval f)) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f ⋆
              (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
               (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
                (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))) mem' }.

    Lemma bls12_final_exp_nonzero_of_functional : forall functions,
      spec_of_bls12_final_exp_functional functions -> spec_of_bls12_final_exp_nonzero functions.
    Proof.
      intros functions H.
      intros pout pf pg1 pg2 pw old_out f g1 g2 w Rr tr mem Hpre.
      eapply Semantics.weaken_call; [exact (H pout pf pg1 pg2 pw old_out f g1 g2 w Rr tr mem Hpre) |].
      intros tr' mem' rets [Hr [Ht [out [Hf Hrest]]]].
      split; [exact Hr |]. split; [exact Ht |]. exists out. split; [| exact Hrest].
      intros Hg1 Hg2 Hw Hnz.
      exact (proj2 (Hf Hg1 Hg2 Hw (fp12_inv_ok _ Hnz))).
    Qed.

End BLS12_FinalExpFunctional.
