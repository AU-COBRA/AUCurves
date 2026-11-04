(** * BLS12-381 Final Exponentiation WP Proof
    Standalone WP correctness proof for bls12_final_exp from BLS12_Pairing.v.
    Easy part: conjugate + inv + mul + frobenius_p2 + mul
    Hard part: a call of bls12_final_exp_hard_dsd (f^{h3}), whose spec is a
    hypothesis like the other callee specs; it is proved in
    BLS12_FinalExpHardDSD.v (bls12_final_exp_hard_dsd_ok).
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

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_FinalExp.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls12_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls12_mul"; PrimeField.add := "bls12_add";
      PrimeField.sub := "bls12_sub"; PrimeField.opp := "bls12_opp";
      PrimeField.square := "bls12_square"; PrimeField.scmula24 := "bls12_scmula24";
      PrimeField.inv := "bls12_inv"; PrimeField.from_bytes := "bls12_from_bytes";
      PrimeField.to_bytes := "bls12_to_bytes"; PrimeField.select_znz := "bls12_select_znz";
      PrimeField.felem_copy := "bls12_felem_copy"; PrimeField.from_word := "bls12_from_word";
      PrimeField.from_list := "bls12_from_list";
    |}.

    Instance bls12_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_381. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Instance bls12_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls12_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls12_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls12_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls12_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls12_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls12_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls12_frep |}.

    Instance bls12_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls12_Fp_rep] in *.
      cbv [Field.bounded_by bls12_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".

    (* β = -1 for BLS12-381 (p ≡ 3 mod 4) *)
    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* ξ = 1+u for BLS12-381 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Instance bls12_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bls12_beta "bls12_") in exact v).
    Instance bls12_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bls12_beta "bls12_") in exact v).
    Instance bls12_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bls12_beta bls12_xi_re bls12_xi_im "bls12_") in exact v).
    Instance bls12_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bls12_beta bls12_xi_re bls12_xi_im "bls12_") in exact v).
    Instance bls12_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bls12_beta bls12_xi_re bls12_xi_im "bls12_") in exact v).
    Instance bls12_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bls12_beta bls12_xi_re bls12_xi_im "bls12_") in exact v).

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp_rep).
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
    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep') AbstractField.bin_mul.
    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep') AbstractField.un_square.
    Instance spec_of_Fp12_inv : spec_of (AbstractField.inv (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep') AbstractField.un_inv.
    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bls12_Fp12_rep').

    Let fp12_conjugate_name : string := (fp12_prefix ++ "conjugate")%string.
    Instance spec_of_Fp12_conjugate : spec_of fp12_conjugate_name :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep')
        (@DodecicFieldExtensions.un_Fp12_conjugate _ _ _ _
          bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix).

    Let fp12_frobenius_p2_name : string := (fp12_prefix ++ "frobenius_p2")%string.
    Instance spec_of_Fp12_frobenius_p2 : spec_of fp12_frobenius_p2_name :=
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
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 px x ⋆
              (FElem_Fp2 pgamma1_p2 gamma1_p2 ⋆
               (FElem_Fp2 pgamma2_p2 gamma2_p2 ⋆
                (FElem_Fp2 pw_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))) mem' }.

    (* Spec of the hard part, proved in BLS12_FinalExpHardDSD.v
       (bls12_final_exp_hard_dsd_ok); the same statement as there. *)
    Instance spec_of_bls12_final_exp_hard_dsd : spec_of "bls12_final_exp_hard_dsd" :=
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
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f_val ⋆
              (FElem_Fp2 pg1p2 g1p2 ⋆
               (FElem_Fp2 pg2p2 g2p2 ⋆
                (FElem_Fp2 pwp2 wp2 ⋆ Rr))))) mem' }.

    Instance spec_of_bls12_final_exp : spec_of "bls12_final_exp" :=
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
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f ⋆
              (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
               (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
                (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))) mem' }.

    Local Instance bls12_Fp12_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep' :=
      DodecicFieldExtensionsSpecs.Fp12_field_representation_ok bls12_beta bls12_xi_re bls12_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Local Instance bls12_Fp2_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep' :=
      @QuadraticFieldExtensionsSpecs.Fp2_field_representation_ok _ _ _ _
        bls12_pf_params bls12_Fp_rep bls12_Fp_rep_ok bls12_beta fp2_prefix.

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

    Lemma bls12_final_exp_ok :
      forall functions
        (EnvContains : map.get functions "bls12_final_exp" = Some (snd bls12_final_exp))
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12inv : spec_of_Fp12_inv functions)
        (HFp12conj : spec_of_Fp12_conjugate functions)
        (HFp12frob : spec_of_Fp12_frobenius_p2 functions)
        (HFhard : spec_of_bls12_final_exp_hard_dsd functions),
      spec_of_bls12_final_exp functions.
    Proof.
      intros. unfold spec_of_bls12_final_exp.
      intros pout pf p_gamma1_p2 p_gamma2_p2 p_w_frob_p2_c1
        old_out f gamma1_p2 gamma2_p2 w_frob_p2_c1 Rr tr mem0
        [Hbf [Hbg1 [Hbg2 [Hbw Hsep]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls12_final_exp. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }

      (* 2 stackallocs *)
      straightline. split. { apply Z_mod_mult. }
      intros a_result mSr mCr HaSr HmSr.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_result mSr) HaSr) as [ri Hri].

      straightline. split. { apply Z_mod_mult. }
      intros a_tmp mSt mCt HaSt HmSt.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_tmp mSt) HaSt) as [ti Hti].

      unfold BLS12_Pairing.final_exp_full_body, BLS12_Pairing.cmd_seq_list.

      (* ================================================================ *)
      (* Combined sep on mCh from nested map.split + input sep            *)
      (* ================================================================ *)
      (* Strategy: lift Hsep from mem0 through four stackalloc layers,
         adding one FElem (or anybytes) at each step.
         Each map.split mC mStack mPrev gives (Q * P) mC from Q mStack, P mPrev. *)

      (* Step 1: lift Hsep from mem0 to mCr, adding FElem_Fp12 a_result ri *)
      pose proof (proj1 (map.split_comm mCr mem0 mSr) HmSr) as HmSr'.
      assert (Hsep1 :
        (FElem_Fp12 a_result ri ⋆
         (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
           (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
             (FElem_Fp12 pout old_out ⋆ Rr)))))) mCr).
      { exists mSr, mem0. exact (conj HmSr' (conj Hri Hsep)). }

      (* Step 2: lift to mCt, adding FElem_Fp12 a_tmp ti *)
      pose proof (proj1 (map.split_comm mCt mCr mSt) HmSt) as HmSt'.
      assert (Hsep2 :
        (FElem_Fp12 a_tmp ti ⋆
         (FElem_Fp12 a_result ri ⋆
          (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr))))))) mCt).
      { exists mSt, mCr. exact (conj HmSt' (conj Hti Hsep1)). }

      assert (Hsep_all :
        (FElem_Fp12 a_tmp ti ⋆
         (FElem_Fp12 a_result ri ⋆
          (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr))))))) mCt) by exact Hsep2.

      (* Clear intermediate sep facts *)
      clear Hsep Hsep1 Hsep2 HmSr HmSt HmSr' HmSt' HaSr HaSt Hri Hti.

      (* ================================================================ *)
      (* Easy part: 6 function calls via wp_call                          *)
      (* ================================================================ *)

      (* Call 1: fp12_conjugate(result, f) — unop_spec, loose→loose *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets1 [Htr1 [conj_out [Hfeval_conj [Hbound_conj Hsep_conj]]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 2: fp12_inv(tmp, f) — unop_spec, loose→loose *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12inv.
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets2 [Htr2 [inv_out [Hfeval_inv [Hbound_inv Hsep_inv]]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 3: fp12_mul(result, result, tmp) — binop_spec, loose*loose→tight *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hbound_conj |].
           split; [exact Hbound_inv |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets3 [Htr3 [mul1_out [Hfeval_mul1 [Hbound_mul1 Hsep_mul1]]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 4: fp12_frobenius_p2(tmp, result, g1, g2, w) — custom fnspec! *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hbound_mul1 |].
           split; [exact Hbg1 |].
           split; [exact Hbg2 |].
           split; [exact Hbw |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets4 [Htr4 [frob_out [Hbound_frob Hsep_frob]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Call 5: fp12_mul(result, tmp, result) — binop_spec *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hbound_frob |].
           split; [exact Hbound_mul1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets5 [Htr5 [mul2_out [Hfeval_mul2 [Hbound_mul2 Hsep_mul2]]]]].
      subst. cbv [map.putmany_of_list_zip].
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
      intros ? ? ? [Hrets6 [Htr6 [hard_out [Hbound_hard Hsep_hard]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* Stack deallocation: tmp, then result *)
      do 2 dealloc_with constr:(FElem_Fp12).

      (* Postcondition *)
      cbv [list_map list_map_body WeakestPrecondition.get].
      split. { reflexivity. }
      split. { reflexivity. }
      exists hard_out.
      split. { exact Hbound_hard. }
      ecancel_assumption.
    Qed.

End BLS12_FinalExp.
