(** * BLS12-381: functional correctness of the bedrock2 [bls12_pairing].

    [bls12_pairing] = stackalloc tmp, gamma1_p2, gamma2_p2, w_frob_p2_c1;
      bls12_load_gamma1_p2; bls12_load_gamma2_p2; bls12_load_w_frob_p2_c1;
      bls12_miller_loop(tmp, P, Q); bls12_final_exp(out, tmp, gamma1_p2, gamma2_p2, w_frob_p2_c1).

    [bls12_pairing_functional_ok] is a copy of [BLS12_PairingTop.bls12_pairing_ok] (same
    stackalloc / dealloc bookkeeping) with functional callee specs:
      - loaders: [BLS12_LoadersFeval.bls12_load_*_p2_feval_ok] (feval = frob_* constants);
      - Miller loop: the statement of [BLS12_MillerLoopPairingTransfer.bls12_miller_loop_pairing_ok_helpers]
        (feval out = Pairing.miller_loop P Q);
      - final exp: [BLS12_FinalExpFunctional.spec_of_bls12_final_exp_nonzero];
      - the invertibility side condition: [MillerLoopNonzero.miller_loop_nonzero_on_curve].
    All statements use the instance terms of BLS12_PairingHelpers (= those of BLS12_PairingTop);
    the transfers from the LoadersFeval / FinalExp instance terms are by conversion.
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
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.
Require Bedrock.Field.Synthesis.Examples.BLS12_LoadersFeval.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExpFunctional.
Require Theory.BLS12Pairing.Pairing.
Require Theory.BLS12Pairing.MillerLoopNonzero.
Module H := Bedrock.Field.Synthesis.Examples.BLS12_PairingHelpers.
Module P := Theory.BLS12Pairing.Pairing.
Module Frob := Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.BLS12_381_Frob.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Record hidden (Q : Prop) : Prop := hide { unhide : Q }.

Section BLS12_PairingFunctional.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Existing Instance H.bls12_pf_params.
    Existing Instance H.bls12_pf_params_ok.
    Existing Instance prime_field_parameters.
    Existing Instance H.bls12_Fp_rep.
    Existing Instance H.bls12_Fp_rep_ok.
    Existing Instance H.bls12_Fp2_params'.
    Existing Instance H.bls12_Fp2_rep'.
    Existing Instance H.bls12_Fp6_params'.
    Existing Instance H.bls12_Fp6_rep'.
    Existing Instance H.bls12_Fp12_params'.
    Existing Instance H.bls12_Fp12_rep'.

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp_feval := (@AbstractField.feval _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation Fp2_feval := (@AbstractField.feval _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ H.bls12_Fp2_params' _ _ _ _ H.bls12_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ H.bls12_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ H.bls12_Fp12_params' _ _ _ _ H.bls12_Fp12_rep').

    Local Typeclasses Opaque H.bls12_Fp12_params'.
    Local Typeclasses Opaque H.bls12_Fp6_params'.
    Local Typeclasses Opaque H.bls12_Fp2_params'.

    Local Notation G1 := (P.G1Affine Frob.p).
    Local Notation G2 := (P.G2Affine Frob.p).

    (* ============================================================ *)
    (* Callee statements in the PairingHelpers instance terms         *)
    (* ============================================================ *)

    Local Notation loader_post Rr tr pout c :=
      (fun tr' mem' rets =>
         rets = [] /\ tr = tr' /\
         exists out,
           Fp2_feval out = c /\ Fp2_bounded Fp2_tight out /\ (FElem_Fp2 pout out ⋆ Rr) mem')
      (only parsing).

    Lemma load_gamma1_p2_H : forall functions,
      map.get functions "bls12_load_gamma1_p2" = Some (snd bls12_load_gamma1_p2) ->
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_gamma1_p2" tr mem [pout]
          (loader_post Rr tr pout Frob.frob_gamma1_p2).
    Proof. exact BLS12_LoadersFeval.bls12_load_gamma1_p2_feval_ok. Qed.

    Lemma load_gamma2_p2_H : forall functions,
      map.get functions "bls12_load_gamma2_p2" = Some (snd bls12_load_gamma2_p2) ->
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_gamma2_p2" tr mem [pout]
          (loader_post Rr tr pout Frob.frob_gamma2_p2).
    Proof. exact BLS12_LoadersFeval.bls12_load_gamma2_p2_feval_ok. Qed.

    Lemma load_w_frob_p2_c1_H : forall functions,
      map.get functions "bls12_load_w_frob_p2_c1" = Some (snd bls12_load_w_frob_p2_c1) ->
      forall pout (old_out : Fp2_felem) Rr tr mem,
        (FElem_Fp2 pout old_out ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls12_load_w_frob_p2_c1" tr mem [pout]
          (loader_post Rr tr pout Frob.frob_coeff_fp12_p2_c1).
    Proof. exact BLS12_LoadersFeval.bls12_load_w_frob_p2_c1_feval_ok. Qed.

    (** [BLS12_FinalExpFunctional.spec_of_bls12_final_exp_nonzero] in the PairingHelpers instance terms. *)
    Definition spec_of_bls12_final_exp_nonzero_H : spec_of "bls12_final_exp" :=
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
            (Fp2_feval gamma1_p2 = Frob.frob_gamma1_p2 ->
             Fp2_feval gamma2_p2 = Frob.frob_gamma2_p2 ->
             Fp2_feval w_frob_p2_c1 = Frob.frob_coeff_fp12_p2_c1 ->
             Fp12_feval f <> P.fp12_zero PrimeField.M_pos ->
             Fp12_feval out = P.final_exponentiation PrimeField.M_pos Frob.frob_gamma1_p2
               Frob.frob_gamma2_p2 Frob.frob_coeff_fp12_p2_c1 (Fp12_feval f)) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f ⋆
              (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
               (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
                (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))) mem' }.

    Lemma final_exp_nonzero_H : forall functions,
      BLS12_FinalExpFunctional.spec_of_bls12_final_exp_nonzero functions ->
      spec_of_bls12_final_exp_nonzero_H functions.
    Proof. intros functions Hfe. exact Hfe. Qed.

    (** The conclusion of [BLS12_MillerLoopPairingTransfer.bls12_miller_loop_pairing_ok_helpers]. *)
    Definition miller_loop_functional_H functions : Prop :=
      forall (pout p_px p_py p_qx p_qy : word)
        (old_out : Fp12_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem) Rr tr mem
        (P0 : G1) (Q0 : G2),
        P.g1_infinity _ P0 = false ->
        P.g2_infinity _ Q0 = false ->
        Fp_feval p_x = P.g1_x _ P0 ->
        Fp_feval p_y = P.g1_y _ P0 ->
        Fp2_feval q_x = P.g2_x _ Q0 ->
        Fp2_feval q_y = P.g2_y _ Q0 ->
        Fp2_bounded Fp2_tight q_x /\
        Fp2_bounded Fp2_tight q_y /\
        Fp_bounded Fp_loose p_x /\
        Fp_bounded Fp_loose p_y /\
        (FElem_Fp12 pout old_out ⋆
         (FElem_Fp p_px p_x ⋆
          (FElem_Fp p_py p_y ⋆
           (FElem_Fp2 p_qx q_x ⋆
            (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem ->
        WeakestPrecondition.call functions "bls12_miller_loop" tr mem
          [pout; p_px; p_py; p_qx; p_qy]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp12_feval out = P.miller_loop Frob.p P0 Q0 /\
              Fp12_bounded Fp12_loose out /\
              (FElem_Fp12 pout out ⋆
               (FElem_Fp p_px p_x ⋆
                (FElem_Fp p_py p_y ⋆
                 (FElem_Fp2 p_qx q_x ⋆
                  (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem').

    (* ============================================================ *)
    (* Spec                                                          *)
    (* ============================================================ *)

    Definition spec_of_bls12_pairing_functional : spec_of "bls12_pairing" :=
      fnspec! "bls12_pairing" (pout p_px p_py p_qx p_qy : word)
        / (old_out : Fp12_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem)
          (P0 : G1) (Q0 : G2) Rr,
      { requires tr mem :=
          P.g1_infinity _ P0 = false /\
          P.g2_infinity _ Q0 = false /\
          MillerLoopNonzero.g1_on_curve P0 /\
          Fp_feval p_x = P.g1_x _ P0 /\
          Fp_feval p_y = P.g1_y _ P0 /\
          Fp2_feval q_x = P.g2_x _ Q0 /\
          Fp2_feval q_y = P.g2_y _ Q0 /\
          Fp2_bounded Fp2_tight q_x /\
          Fp2_bounded Fp2_tight q_y /\
          Fp_bounded Fp_loose p_x /\
          Fp_bounded Fp_loose p_y /\
          (FElem_Fp12 pout old_out ⋆
           (FElem_Fp p_px p_x ⋆
            (FElem_Fp p_py p_y ⋆
             (FElem_Fp2 p_qx q_x ⋆
              (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp12_feval out = P.pairing Frob.p Frob.frob_gamma1_p2 Frob.frob_gamma2_p2
                               Frob.frob_coeff_fp12_p2_c1 P0 Q0 /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp p_px p_x ⋆
              (FElem_Fp p_py p_y ⋆
               (FElem_Fp2 p_qx q_x ⋆
                (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem' }.

    Local Lemma sep_stack_extend (A B : mem -> Prop) (mC mPrev mStack : mem) :
      map.split mC mPrev mStack -> A mPrev -> B mStack -> (B ⋆ A) mC.
    Proof.
      intros Hs HA HB.
      apply Properties.map.split_comm in Hs.
      exists mStack, mPrev. exact (conj Hs (conj HB HA)).
    Qed.

    (** Pure composition of the callee facts. *)
    Local Lemma pairing_chain (ml fe : ((F Frob.p * F Frob.p) * (F Frob.p * F Frob.p) * (F Frob.p * F Frob.p)) *
                               ((F Frob.p * F Frob.p) * (F Frob.p * F Frob.p) * (F Frob.p * F Frob.p))) (P0 : G1) (Q0 : G2) :
      MillerLoopNonzero.g1_on_curve P0 ->
      ml = P.miller_loop Frob.p P0 Q0 ->
      (ml <> P.fp12_zero PrimeField.M_pos ->
       fe = P.final_exponentiation PrimeField.M_pos Frob.frob_gamma1_p2
              Frob.frob_gamma2_p2 Frob.frob_coeff_fp12_p2_c1 ml) ->
      fe = P.pairing Frob.p Frob.frob_gamma1_p2 Frob.frob_gamma2_p2 Frob.frob_coeff_fp12_p2_c1 P0 Q0.
    Proof.
      intros Hc Hml Hfe. subst ml.
      exact (Hfe (MillerLoopNonzero.miller_loop_nonzero_on_curve P0 Q0 Hc)).
    Qed.

    (* ============================================================ *)
    (* Main WP proof (copy of BLS12_PairingTop.bls12_pairing_ok)     *)
    (* ============================================================ *)

    Lemma bls12_pairing_functional_ok :
      forall functions
        (EnvContains : map.get functions "bls12_pairing" = Some (snd bls12_pairing))
        (HLoadG1 : map.get functions "bls12_load_gamma1_p2" = Some (snd bls12_load_gamma1_p2))
        (HLoadG2 : map.get functions "bls12_load_gamma2_p2" = Some (snd bls12_load_gamma2_p2))
        (HLoadW : map.get functions "bls12_load_w_frob_p2_c1" = Some (snd bls12_load_w_frob_p2_c1))
        (HMillerLoop : miller_loop_functional_H functions)
        (HFinalExp : spec_of_bls12_final_exp_nonzero_H functions),
      spec_of_bls12_pairing_functional functions.
    Proof.
      intros.
      unfold spec_of_bls12_pairing_functional.
      intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y P0 Q0 Rr tr mem0
        [HPinf [HQinf [Hcurve [Hpx [Hpy [Hqx [Hqy [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]]]]]]]]].
      (* the ghost facts are not needed by the bookkeeping below *)
      pose proof (hide _ (conj HPinf (conj HQinf (conj Hpx (conj Hpy (conj Hqx Hqy)))))) as Hghost.
      pose proof (hide _ Hcurve) as Hcurve'.
      clear HPinf HQinf Hpx Hpy Hqx Hqy Hcurve.
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_pairing. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }

      (* === Stackalloc 1: tmp (Fp12-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_tmp mStack_tmp mComb_tmp HstackTmp Hm_split_tmp.
      pose proof (@AbstractField.FElem_from_bytes _ H.bls12_Fp12_params' _ _ _ _
        H.bls12_Fp12_rep' wordok mapok a_tmp) as Hfb_tmp.
      unfold AbstractField.Placeholder in Hfb_tmp.
      pose proof (proj1 (Hfb_tmp mStack_tmp) HstackTmp) as [tmp_val Htmp_felem].
      clear Hfb_tmp HstackTmp.

      (* === Stackalloc 2: gamma1_p2 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_g1 mStack_g1 mComb_g1 HstackG1 Hm_split_g1.
      pose proof (@AbstractField.FElem_from_bytes _ H.bls12_Fp2_params' _ _ _ _
        H.bls12_Fp2_rep' wordok mapok a_g1) as Hfb_g1.
      unfold AbstractField.Placeholder in Hfb_g1.
      pose proof (proj1 (Hfb_g1 mStack_g1) HstackG1) as [g1_val Hg1_felem].
      clear Hfb_g1 HstackG1.

      (* === Stackalloc 3: gamma2_p2 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_g2 mStack_g2 mComb_g2 HstackG2 Hm_split_g2.
      pose proof (@AbstractField.FElem_from_bytes _ H.bls12_Fp2_params' _ _ _ _
        H.bls12_Fp2_rep' wordok mapok a_g2) as Hfb_g2.
      unfold AbstractField.Placeholder in Hfb_g2.
      pose proof (proj1 (Hfb_g2 mStack_g2) HstackG2) as [g2_val Hg2_felem].
      clear Hfb_g2 HstackG2.

      (* === Stackalloc 4: w_frob_p2_c1 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_w mStack_w mComb_w HstackW Hm_split_w.
      pose proof (@AbstractField.FElem_from_bytes _ H.bls12_Fp2_params' _ _ _ _
        H.bls12_Fp2_rep' wordok mapok a_w) as Hfb_w.
      unfold AbstractField.Placeholder in Hfb_w.
      pose proof (proj1 (Hfb_w mStack_w) HstackW) as [w_val Hw_felem].
      clear Hfb_w HstackW.

      (* === Build combined sep on mComb_w === *)
      pose proof (sep_stack_extend _ _ _ _ _ Hm_split_tmp Hsep Htmp_felem) as Hcomb_tmp.
      pose proof (sep_stack_extend _ _ _ _ _ Hm_split_g1 Hcomb_tmp Hg1_felem) as Hcomb_g1.
      pose proof (sep_stack_extend _ _ _ _ _ Hm_split_g2 Hcomb_g1 Hg2_felem) as Hcomb_g2.
      pose proof (sep_stack_extend _ _ _ _ _ Hm_split_w Hcomb_g2 Hw_felem) as Hcomb_w.
      clear Hcomb_tmp Hcomb_g1 Hcomb_g2.
      clear Htmp_felem Hg1_felem Hg2_felem Hw_felem.
      clear Hsep.

      unfold BLS12_Pairing.pairing_full_body, BLS12_Pairing.cmd_seq_list.

      (* === Call 1: bls12_load_gamma1_p2(gamma1_p2) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply load_gamma1_p2_H; [exact HLoadG1 | ecancel_assumption]. }
      intros t1 m1 rets1 [Hrets1 [Htr1 [g1_out [Hfg1 [Hbg1_out Hsep_g1]]]]].
      subst rets1. symmetry in Htr1. subst t1.
      apply hide in Hfg1.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 2: bls12_load_gamma2_p2(gamma2_p2) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply load_gamma2_p2_H; [exact HLoadG2 | ecancel_assumption]. }
      intros t2 m2 rets2 [Hrets2 [Htr2 [g2_out [Hfg2 [Hbg2_out Hsep_g2]]]]].
      subst rets2. symmetry in Htr2. subst t2.
      apply hide in Hfg2.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 3: bls12_load_w_frob_p2_c1(w_frob_p2_c1) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply load_w_frob_p2_c1_H; [exact HLoadW | ecancel_assumption]. }
      intros t3 m3 rets3 [Hrets3 [Htr3 [w_out [Hfw [Hbw_out Hsep_w]]]]].
      subst rets3. symmetry in Htr3. subst t3.
      apply hide in Hfw.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 4: bls12_miller_loop(tmp, p_x, p_y, q_x, q_y) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        destruct Hghost as [[HPinf [HQinf [Hpx [Hpy [Hqx Hqy]]]]]].
        eapply (HMillerLoop _ _ _ _ _ _ _ _ _ _ _ _ _ P0 Q0 HPinf HQinf Hpx Hpy Hqx Hqy).
        split; [exact Hbqx |]. split; [exact Hbqy |].
        split; [exact Hbpx |]. split; [exact Hbpy |].
        ecancel_assumption.
      }
      intros t4 m4 rets4 [Hrets4 [Htr4 [ml_out [Hfml [Hbml_out Hsep_ml]]]]].
      subst rets4. symmetry in Htr4. subst t4.
      apply hide in Hfml.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 5: bls12_final_exp(out, tmp, g1, g2, w) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply (HFinalExp pout a_tmp a_g1 a_g2 a_w old_out ml_out g1_out g2_out w_out).
        split; [exact Hbml_out |]. split; [exact Hbg1_out |].
        split; [exact Hbg2_out |]. split; [exact Hbw_out |].
        ecancel_assumption.
      }
      intros t5 m5 rets5 [Hrets5 [Htr5 [fe_out [Hffe [Hbfe_out Hsep_fe]]]]].
      subst rets5. symmetry in Htr5. subst t5.
      apply hide in Hffe.

      (* === Stack deallocation (4 levels) + final postcondition === *)
      eexists. split. { exact eq_refl. }

      (* --- Dealloc level 1: w (Fp2-sized) --- *)
      eassert (Hw_sep : (_ ⋆ FElem_Fp2 a_w w_out) m5).
      { pose proof Hsep_fe as H'. ecancel_assumption. }
      destruct Hw_sep as [m_rest_w [m_w [[Heq_w Hd_w] [Hrest_w Hfw_m]]]].
      exists m_rest_w, m_w.
      split. { exact (AbstractField.FElem_to_bytes a_w w_out m_w Hfw_m). }
      split. { split; [exact Heq_w | exact Hd_w]. }

      (* --- Dealloc level 2: g2 (Fp2-sized) --- *)
      eassert (Hg2_sep : (_ ⋆ FElem_Fp2 a_g2 g2_out) m_rest_w).
      { pose proof Hrest_w as H'. ecancel_assumption. }
      destruct Hg2_sep as [m_rest_g2 [m_g2 [[Heq_g2 Hd_g2] [Hrest_g2 Hfg2_m]]]].
      exists m_rest_g2, m_g2.
      split. { exact (AbstractField.FElem_to_bytes a_g2 g2_out m_g2 Hfg2_m). }
      split. { split; [exact Heq_g2 | exact Hd_g2]. }

      (* --- Dealloc level 3: g1 (Fp2-sized) --- *)
      eassert (Hg1_sep : (_ ⋆ FElem_Fp2 a_g1 g1_out) m_rest_g2).
      { pose proof Hrest_g2 as H'. ecancel_assumption. }
      destruct Hg1_sep as [m_rest_g1 [m_g1 [[Heq_g1 Hd_g1] [Hrest_g1 Hfg1_m]]]].
      exists m_rest_g1, m_g1.
      split. { exact (AbstractField.FElem_to_bytes a_g1 g1_out m_g1 Hfg1_m). }
      split. { split; [exact Heq_g1 | exact Hd_g1]. }

      (* --- Dealloc level 4: tmp (Fp12-sized) --- *)
      eassert (Htmp_sep : (_ ⋆ FElem_Fp12 a_tmp ml_out) m_rest_g1).
      { pose proof Hrest_g1 as H'. ecancel_assumption. }
      destruct Htmp_sep as [m_rest_tmp [m_tmp [[Heq_tmp Hd_tmp] [Hrest_tmp Hftmp]]]].
      exists m_rest_tmp, m_tmp.
      split. { exact (AbstractField.FElem_to_bytes a_tmp ml_out m_tmp Hftmp). }
      split. { split; [exact Heq_tmp | exact Hd_tmp]. }

      (* --- Final postcondition --- *)
      cbv [list_map list_map_body].
      split. { exact eq_refl. }
      split. { exact eq_refl. }
      exists fe_out.
      split.
      { destruct Hcurve' as [Hcurve]. destruct Hfml as [Hfml]. destruct Hffe as [Hffe].
        destruct Hfg1 as [Hfg1]. destruct Hfg2 as [Hfg2]. destruct Hfw as [Hfw].
        exact (pairing_chain (Fp12_feval ml_out) (Fp12_feval fe_out) P0 Q0 Hcurve Hfml
                 (Hffe Hfg1 Hfg2 Hfw)). }
      split. { exact Hbfe_out. }
      exact Hrest_tmp.
    Qed.

End BLS12_PairingFunctional.

Print Assumptions bls12_pairing_functional_ok.
