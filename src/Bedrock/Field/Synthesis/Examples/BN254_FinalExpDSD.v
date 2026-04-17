(** * BN254 DSD Final Exponentiation WP Proof
    Proves bn254_final_exp_dsd (6 calls) satisfies its spec.
    Easy part: conjugate + inv + mul + frobenius_p2 + mul
    Hard part: call final_exp_hard_dsd
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
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BN254_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BN254_FinalExpDSD.

    (* === BN254 Instance Boilerplate === *)
    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bn254_M_pos : positive := Eval vm_compute in (Z.to_pos bn254_prime.m).

    Instance bn254_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn254_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn254_mul"; PrimeField.add := "bn254_add";
      PrimeField.sub := "bn254_sub"; PrimeField.opp := "bn254_opp";
      PrimeField.square := "bn254_square"; PrimeField.scmula24 := "bn254_scmula24";
      PrimeField.inv := "bn254_inv"; PrimeField.from_bytes := "bn254_from_bytes";
      PrimeField.to_bytes := "bn254_to_bytes"; PrimeField.select_znz := "bn254_select_znz";
      PrimeField.felem_copy := "bn254_felem_copy"; PrimeField.from_word := "bn254_from_word";
      PrimeField.from_list := "bn254_from_list";
    |}.

    Instance bn254_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn254. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Instance bn254_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn254_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn254_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn254_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn254_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn254_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn254_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn254_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn254_frep |}.

    Instance bn254_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn254_Fp_rep] in *.
      cbv [Field.bounded_by bn254_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bn254_Fp2_".
    Let fp6_prefix := "bn254_Fp6_".
    Let fp12_prefix := "bn254_Fp12_".

    Let bn254_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
    Let bn254_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 9.
    Let bn254_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    (* === Extension field instances from factory === *)
    Instance bn254_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ext_Fp2_params bn254_beta "bn254_".
    Instance bn254_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ext_Fp2_rep bn254_beta "bn254_".
    Instance bn254_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ext_Fp6_params bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ext_Fp6_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ext_Fp12_params bn254_beta bn254_xi_re bn254_xi_im "bn254_".
    Instance bn254_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ext_Fp12_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_".

    (* === Abbreviations === *)
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bn254_Fp12_params'.
    Local Typeclasses Opaque bn254_Fp6_params'.
    Local Typeclasses Opaque bn254_Fp2_params'.

    (* === Operation specs === *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bn254_Fp12_rep') AbstractField.bin_mul.
    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn254_Fp12_rep') AbstractField.un_square.
    Instance spec_of_Fp12_inv : spec_of (AbstractField.inv (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn254_Fp12_rep') AbstractField.un_inv.
    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bn254_Fp12_rep').

    Let fp12_conjugate_name : string := (fp12_prefix ++ "conjugate")%string.
    Instance spec_of_Fp12_conjugate : spec_of fp12_conjugate_name :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn254_Fp12_rep')
        (@DodecicFieldExtensions.un_Fp12_conjugate _ _ _ _
          bn254_pf_params bn254_Fp_rep bn254_beta bn254_xi_re bn254_xi_im fp12_prefix fp6_prefix fp2_prefix).

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

    (* Spec for the DSD hard part — assumed as a hypothesis *)
    Instance spec_of_bn254_final_exp_hard_dsd : spec_of "bn254_final_exp_hard_dsd" :=
      fnspec! "bn254_final_exp_hard_dsd" (pout pf : word)
        / (old_out f_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight f_val /\
          (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f_val ⋆ Rr)) mem' }.

    (* Spec for the whole DSD final exponentiation *)
    Instance spec_of_bn254_final_exp_dsd : spec_of "bn254_final_exp_dsd" :=
      fnspec! "bn254_final_exp_dsd"
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

    Local Instance bn254_Fp12_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep' :=
      DodecicFieldExtensionsSpecs.Fp12_field_representation_ok bn254_beta bn254_xi_re bn254_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

    Lemma bn254_final_exp_dsd_ok :
      forall functions
        (EnvContains : map.get functions "bn254_final_exp_dsd" =
          Some (snd BN254_Pairing.bn254_final_exp_dsd))
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12inv : spec_of_Fp12_inv functions)
        (HFp12conj : spec_of_Fp12_conjugate functions)
        (HFp12frob : spec_of_Fp12_frobenius_p2 functions)
        (HFhard : spec_of_bn254_final_exp_hard_dsd functions),
      spec_of_bn254_final_exp_dsd functions.
    Proof.
      intros. unfold spec_of_bn254_final_exp_dsd.
      intros pout pf p_gamma1_p2 p_gamma2_p2 p_w_frob_p2_c1
        old_out f gamma1_p2 gamma2_p2 w_frob_p2_c1 Rr tr mem0
        [Hbf [Hbg1 [Hbg2 [Hbw Hsep]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold BN254_Pairing.bn254_final_exp_dsd. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }

      (* Stackalloc 1: result *)
      straightline. split. { apply Z_mod_mult. }
      intros a_result mSr mCr HaSr HmSr.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn254_Fp12_params' _ _ _ _
        bn254_Fp12_rep' wordok mapok a_result mSr) HaSr) as [ri Hri].

      (* Stackalloc 2: tmp *)
      straightline. split. { apply Z_mod_mult. }
      intros a_tmp mSt mCt HaSt HmSt.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn254_Fp12_params' _ _ _ _
        bn254_Fp12_rep' wordok mapok a_tmp mSt) HaSt) as [ti Hti].

      unfold BN254_Pairing.final_exp_dsd_body, BN254_Pairing.cmd_seq_list.

      (* Build master sep from stackalloc layers *)
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

      clear Hsep Hsep1.

      (* ================================================================ *)
      (* Call 1: fp12_conjugate(result, f) — unop_spec, tight->loose      *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets1 [Htr1 [conj_out [Hfeval_conj [Hbound_conj Hsep_conj]]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 2: fp12_inv(tmp, f) — unop_spec, tight->loose               *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12inv.
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets2 [Htr2 [inv_out [Hfeval_inv [Hbound_inv Hsep_inv]]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 3: fp12_mul(result, result, tmp) — binop, loose*loose->tight *)
      (* ================================================================ *)
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

      (* ================================================================ *)
      (* Call 4: fp12_frobenius_p2(tmp, result, g1p2, g2p2, wfp2)        *)
      (* ================================================================ *)
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

      (* ================================================================ *)
      (* Call 5: fp12_mul(result, tmp, result) — binop                    *)
      (* ================================================================ *)
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

      (* ================================================================ *)
      (* Call 6: final_exp_hard_dsd(out, result) — custom spec            *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFhard.
           split; [exact Hbound_mul2 |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets6 [Htr6 [hard_out [Hbound_hard Hsep_hard]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Stack deallocation: tmp then result                              *)
      (* ================================================================ *)

      (* Step 1: Reorder sep to isolate FElem_Fp12 a_tmp at front *)
      assert (Hsep_tmp_front :
        (FElem_Fp12 a_tmp frob_out ⋆
         (FElem_Fp12 pout hard_out ⋆
          (FElem_Fp12 a_result mul2_out ⋆
           (FElem_Fp12 pf f ⋆
            (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
             (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
              (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆ Rr))))))) m'4).
      { ecancel_assumption. }
      clear Hsep_hard.
      destruct Hsep_tmp_front as [mStack_tmp [m_after_tmp [Hsp_tmp [Hfe_tmp Hrest_tmp]]]].

      (* Convert FElem a_tmp to anybytes *)
      assert (Hab_tmp : Memory.anybytes a_tmp (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_tmp).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn254_Fp12_rep')
                      a_tmp frob_out mStack_tmp Hfe_tmp) as Htmp_bytes.
        cbv [Placeholder] in Htmp_bytes. exact Htmp_bytes. }

      exists m_after_tmp, mStack_tmp.
      split. { exact Hab_tmp. }
      split. { apply map.split_comm. exact Hsp_tmp. }

      (* Step 2: Reorder sep on m_after_tmp to isolate FElem_Fp12 a_result *)
      assert (Hsep_res_front :
        (FElem_Fp12 a_result mul2_out ⋆
         (FElem_Fp12 pout hard_out ⋆
          (FElem_Fp12 pf f ⋆
           (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
             (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆ Rr)))))) m_after_tmp).
      { ecancel_assumption. }
      clear Hrest_tmp.
      destruct Hsep_res_front as [mStack_res [m_final [Hsp_res [Hfe_res Hrest_final]]]].

      assert (Hab_res : Memory.anybytes a_result (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_res).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn254_Fp12_rep')
                      a_result mul2_out mStack_res Hfe_res) as Hres_bytes.
        cbv [Placeholder] in Hres_bytes. exact Hres_bytes. }

      exists m_final, mStack_res.
      split. { exact Hab_res. }
      split. { apply map.split_comm. exact Hsp_res. }

      (* Step 3: Final postcondition *)
      cbv [list_map list_map_body WeakestPrecondition.get].
      split. { reflexivity. }
      split. { reflexivity. }
      exists hard_out.
      split. { exact Hbound_hard. }
      exact Hrest_final.
    Qed.

End BN254_FinalExpDSD.
