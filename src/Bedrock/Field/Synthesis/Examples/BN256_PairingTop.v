(** * BN256 Top-Level Pairing WP Proof
    Standalone WP correctness proof for bn256_pairing_dsd from BN256_Pairing.v,
    plus the top-level bn256_pairing_dsd_correct_standalone theorem.
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
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bn256_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BN256_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BN256_PairingTop.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bn256_M_pos : positive := Eval vm_compute in (Z.to_pos bn256_prime.m).

    Instance bn256_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn256_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn256_mul";
      PrimeField.add := "bn256_add";
      PrimeField.sub := "bn256_sub";
      PrimeField.opp := "bn256_opp";
      PrimeField.square := "bn256_square";
      PrimeField.scmula24 := "bn256_scmula24";
      PrimeField.inv := "bn256_inv";
      PrimeField.from_bytes := "bn256_from_bytes";
      PrimeField.to_bytes := "bn256_to_bytes";
      PrimeField.select_znz := "bn256_select_znz";
      PrimeField.felem_copy := "bn256_felem_copy";
      PrimeField.from_word := "bn256_from_word";
      PrimeField.from_list := "bn256_from_list";
    |}.

    Instance bn256_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bn256. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Instance bn256_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bn256_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn256_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn256_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn256_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn256_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bn256_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn256_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn256_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn256_frep |}.

    Instance bn256_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bn256_Fp_rep] in *.
      cbv [Field.bounded_by bn256_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bn256_Fp2_".
    Let fp6_prefix := "bn256_Fp6_".
    Let fp12_prefix := "bn256_Fp12_".

    (* beta = -1 for BN256 (p = 3 mod 4) *)
    Let bn256_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).

    (* xi = (3, 1) for BN256 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bn256_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 3.
    Let bn256_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Instance bn256_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bn256_beta "bn256_") in exact v).
    Instance bn256_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bn256_beta "bn256_") in exact v).
    Instance bn256_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bn256_beta bn256_xi_re bn256_xi_im "bn256_") in exact v).
    Instance bn256_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bn256_beta bn256_xi_re bn256_xi_im "bn256_") in exact v).
    Instance bn256_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bn256_beta bn256_xi_re bn256_xi_im "bn256_") in exact v).
    Instance bn256_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bn256_beta bn256_xi_re bn256_xi_im "bn256_") in exact v).

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bn256_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bn256_Fp6_params' _ _ _ _ bn256_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bn256_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bn256_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bn256_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bn256_Fp12_params'.
    Local Typeclasses Opaque bn256_Fp6_params'.
    Local Typeclasses Opaque bn256_Fp2_params'.

    Local Lemma sep_stack_extend (P Q : mem -> Prop) (mC mPrev mStack : mem) :
      map.split mC mPrev mStack -> P mPrev -> Q mStack -> (Q ⋆ P) mC.
    Proof.
      intros Hs HP HQ.
      apply Properties.map.split_comm in Hs.
      exists mStack, mPrev. exact (conj Hs (conj HQ HP)).
    Qed.

    Local Ltac solve_putmany_eq_aux n :=
      match n with
      | O => fail "solve_putmany_eq: out of fuel"
      | S ?n' =>
        first [
          reflexivity
        | match goal with
          | |- map.putmany ?a _ = map.putmany ?a _ =>
            apply (f_equal (map.putmany a)); solve_putmany_eq_aux n'
          end
        | match goal with
          | |- _ = map.putmany ?target _ =>
            match goal with
            | |- context [map.putmany ?a (map.putmany target ?rest)] =>
              rewrite (map.putmany_assoc a target rest);
              rewrite (map.putmany_comm a target) by map_disjoint_auto;
              rewrite <- (map.putmany_assoc target a rest);
              solve_putmany_eq_aux n'
            end
          end
        | match goal with
          | |- _ = map.putmany ?target _ =>
            match goal with
            | |- context [map.putmany ?a (map.putmany ?b target)] =>
              rewrite (map.putmany_assoc a b);
              rewrite (map.putmany_comm (map.putmany a b) target) by map_disjoint_auto;
              rewrite <- ?map.putmany_assoc;
              solve_putmany_eq_aux n'
            end
          end
        | match goal with
          | |- map.putmany ?a ?b = map.putmany ?b ?a =>
            apply map.putmany_comm; map_disjoint_auto
          end
        ]
      end.
    Local Ltac solve_putmany_eq :=
      rewrite <- ?map.putmany_assoc;
      solve_putmany_eq_aux 50%nat.

    (* ============================================================ *)
    (* Spec                                                          *)
    (* ============================================================ *)

    Instance spec_of_bn256_pairing_dsd : spec_of "bn256_pairing_dsd" :=
      fnspec! "bn256_pairing_dsd" (pout p_px p_py p_qx p_qy : word)
        / (old_out : Fp12_felem) (p_x p_y : Fp_felem) (q_x q_y : Fp2_felem)
          Rr,
      { requires tr mem :=
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
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp p_px p_x ⋆
              (FElem_Fp p_py p_y ⋆
               (FElem_Fp2 p_qx q_x ⋆
                (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem' }.

    (* ============================================================ *)
    (* Main WP proof                                                 *)
    (* ============================================================ *)

    Lemma bn256_pairing_dsd_ok :
      forall functions
        (EnvContains : map.get functions "bn256_pairing_dsd" =
          Some (snd bn256_pairing_dsd))
        (* Loader hypotheses: provide Semantics.call directly *)
        (HLoadG1 : forall pout (old_out : Fp2_felem) R tr m,
          (FElem_Fp2 pout old_out ⋆ R) m ->
          Semantics.call functions "bn256_load_gamma1_p2" tr m [pout]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists out,
                Fp2_bounded Fp2_tight out /\
                (FElem_Fp2 pout out ⋆ R) m'))
        (HLoadG2 : forall pout (old_out : Fp2_felem) R tr m,
          (FElem_Fp2 pout old_out ⋆ R) m ->
          Semantics.call functions "bn256_load_gamma2_p2" tr m [pout]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists out,
                Fp2_bounded Fp2_tight out /\
                (FElem_Fp2 pout out ⋆ R) m'))
        (HLoadW : forall pout (old_out : Fp2_felem) R tr m,
          (FElem_Fp2 pout old_out ⋆ R) m ->
          Semantics.call functions "bn256_load_w_frob_p2_c1" tr m [pout]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists out,
                Fp2_bounded Fp2_tight out /\
                (FElem_Fp2 pout out ⋆ R) m'))
        (* Callee hypotheses for miller_loop and final_exp.
           These encapsulate the full call chain including all
           transitive dependencies (Fp2/Fp12 arithmetic). *)
        (HMillerLoop : forall ptmp ppx ppy pqx pqy
          (old_tmp : Fp12_felem) (px py : Fp_felem) (qx qy : Fp2_felem) R tr m,
          Fp2_bounded Fp2_tight qx ->
          Fp2_bounded Fp2_tight qy ->
          Fp_bounded Fp_loose px ->
          Fp_bounded Fp_loose py ->
          (FElem_Fp12 ptmp old_tmp ⋆
           (FElem_Fp ppx px ⋆
            (FElem_Fp ppy py ⋆
             (FElem_Fp2 pqx qx ⋆
              (FElem_Fp2 pqy qy ⋆ R))))) m ->
          Semantics.call functions "bn256_miller_loop" tr m
            [ptmp; ppx; ppy; pqx; pqy]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists ml_out,
                Fp12_bounded Fp12_tight ml_out /\
                (FElem_Fp12 ptmp ml_out ⋆
                 (FElem_Fp ppx px ⋆
                  (FElem_Fp ppy py ⋆
                   (FElem_Fp2 pqx qx ⋆
                    (FElem_Fp2 pqy qy ⋆ R))))) m'))
        (HFinalExp : forall po pf pg1 pg2 pw
          (old_o : Fp12_felem) (f : Fp12_felem)
          (g1 g2 w : Fp2_felem) R tr m,
          Fp12_bounded Fp12_tight f ->
          Fp2_bounded Fp2_tight g1 ->
          Fp2_bounded Fp2_tight g2 ->
          Fp2_bounded Fp2_tight w ->
          (FElem_Fp12 pf f ⋆
           (FElem_Fp2 pg1 g1 ⋆
            (FElem_Fp2 pg2 g2 ⋆
             (FElem_Fp2 pw w ⋆
              (FElem_Fp12 po old_o ⋆ R))))) m ->
          Semantics.call functions "bn256_final_exp_dsd" tr m
            [po; pf; pg1; pg2; pw]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists fe_out,
                Fp12_bounded Fp12_loose fe_out /\
                (FElem_Fp12 po fe_out ⋆
                 (FElem_Fp12 pf f ⋆
                  (FElem_Fp2 pg1 g1 ⋆
                   (FElem_Fp2 pg2 g2 ⋆
                    (FElem_Fp2 pw w ⋆ R))))) m')),
      spec_of_bn256_pairing_dsd functions.
    Proof.
      intros.
      unfold spec_of_bn256_pairing_dsd.
      intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
        [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bn256_pairing_dsd. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }

      (* === Stackalloc 1: tmp (Fp12-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_tmp mStack_tmp mComb_tmp HstackTmp Hm_split_tmp.

      pose proof (@AbstractField.FElem_from_bytes _ bn256_Fp12_params' _ _ _ _
        bn256_Fp12_rep' wordok mapok a_tmp) as Hfb_tmp.
      unfold AbstractField.Placeholder in Hfb_tmp.
      pose proof (proj1 (Hfb_tmp mStack_tmp) HstackTmp) as [tmp_val Htmp_felem].
      clear Hfb_tmp HstackTmp.

      (* === Stackalloc 2: gamma1_p2 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_g1 mStack_g1 mComb_g1 HstackG1 Hm_split_g1.

      pose proof (@AbstractField.FElem_from_bytes _ bn256_Fp2_params' _ _ _ _
        bn256_Fp2_rep' wordok mapok a_g1) as Hfb_g1.
      unfold AbstractField.Placeholder in Hfb_g1.
      pose proof (proj1 (Hfb_g1 mStack_g1) HstackG1) as [g1_val Hg1_felem].
      clear Hfb_g1 HstackG1.

      (* === Stackalloc 3: gamma2_p2 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_g2 mStack_g2 mComb_g2 HstackG2 Hm_split_g2.

      pose proof (@AbstractField.FElem_from_bytes _ bn256_Fp2_params' _ _ _ _
        bn256_Fp2_rep' wordok mapok a_g2) as Hfb_g2.
      unfold AbstractField.Placeholder in Hfb_g2.
      pose proof (proj1 (Hfb_g2 mStack_g2) HstackG2) as [g2_val Hg2_felem].
      clear Hfb_g2 HstackG2.

      (* === Stackalloc 4: w_frob_p2_c1 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_w mStack_w mComb_w HstackW Hm_split_w.

      pose proof (@AbstractField.FElem_from_bytes _ bn256_Fp2_params' _ _ _ _
        bn256_Fp2_rep' wordok mapok a_w) as Hfb_w.
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

      unfold BN256_Pairing.pairing_dsd_body, BN256_Pairing.cmd_seq_list.

      (* === Call 1: bn256_load_gamma1_p2(gamma1_p2) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply HLoadG1.
        ecancel_assumption.
      }
      intros t1 m1 rets1 [Hrets1 [Htr1 [g1_out [Hbg1_out Hsep_g1]]]].
      subst rets1. symmetry in Htr1. subst t1.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 2: bn256_load_gamma2_p2(gamma2_p2) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply HLoadG2.
        ecancel_assumption.
      }
      intros t2 m2 rets2 [Hrets2 [Htr2 [g2_out [Hbg2_out Hsep_g2]]]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 3: bn256_load_w_frob_p2_c1(w_frob_p2_c1) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply HLoadW.
        ecancel_assumption.
      }
      intros t3 m3 rets3 [Hrets3 [Htr3 [w_out [Hbw_out Hsep_w]]]].
      subst rets3. symmetry in Htr3. subst t3.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 4: bn256_miller_loop(tmp, p_x, p_y, q_x, q_y) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply HMillerLoop; [exact Hbqx | exact Hbqy | exact Hbpx | exact Hbpy |].
        ecancel_assumption.
      }
      intros t4 m4 rets4 [Hrets4 [Htr4 [ml_out [Hbml_out Hsep_ml]]]].
      subst rets4. symmetry in Htr4. subst t4.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 5: bn256_final_exp_dsd(out, tmp, g1, g2, w) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply (HFinalExp pout a_tmp a_g1 a_g2 a_w
          old_out ml_out g1_out g2_out w_out);
        [exact Hbml_out | exact Hbg1_out | exact Hbg2_out | exact Hbw_out |].
        ecancel_assumption.
      }
      intros t5 m5 rets5 [Hrets5 [Htr5 [fe_out [Hbfe_out Hsep_fe]]]].
      subst rets5. symmetry in Htr5. subst t5.

      (* === Stack deallocation (4 levels) + final postcondition === *)
      (* Handle return value list *)
      eexists. split. { exact eq_refl. }

      (* --- Dealloc level 1: w (Fp2-sized) --- *)
      eassert (Hw_sep : (_ ⋆ FElem_Fp2 a_w w_out) m5).
      { pose proof Hsep_fe as H'. ecancel_assumption. }
      destruct Hw_sep as [m_rest_w [m_w [[Heq_w Hd_w] [Hrest_w Hfw]]]].
      exists m_rest_w, m_w.
      split. { exact (AbstractField.FElem_to_bytes a_w w_out m_w Hfw). }
      split. { split; [exact Heq_w | exact Hd_w]. }

      (* --- Dealloc level 2: g2 (Fp2-sized) --- *)
      eassert (Hg2_sep : (_ ⋆ FElem_Fp2 a_g2 g2_out) m_rest_w).
      { pose proof Hrest_w as H'. ecancel_assumption. }
      destruct Hg2_sep as [m_rest_g2 [m_g2 [[Heq_g2 Hd_g2] [Hrest_g2 Hfg2]]]].
      exists m_rest_g2, m_g2.
      split. { exact (AbstractField.FElem_to_bytes a_g2 g2_out m_g2 Hfg2). }
      split. { split; [exact Heq_g2 | exact Hd_g2]. }

      (* --- Dealloc level 3: g1 (Fp2-sized) --- *)
      eassert (Hg1_sep : (_ ⋆ FElem_Fp2 a_g1 g1_out) m_rest_g2).
      { pose proof Hrest_g2 as H'. ecancel_assumption. }
      destruct Hg1_sep as [m_rest_g1 [m_g1 [[Heq_g1 Hd_g1] [Hrest_g1 Hfg1]]]].
      exists m_rest_g1, m_g1.
      split. { exact (AbstractField.FElem_to_bytes a_g1 g1_out m_g1 Hfg1). }
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
      split. { exact Hbfe_out. }
      exact Hrest_tmp.
    Qed.

    (* ============================================================ *)
    (* Top-level standalone theorem                                  *)
    (* ============================================================ *)

    Theorem bn256_pairing_dsd_correct_standalone :
      forall functions tr mem pout p_px p_py p_qx p_qy
        (old_out : Fp12_felem) (p_x p_y : Fp_felem)
        (q_x q_y : Fp2_felem) Rr,
        map.get functions "bn256_pairing_dsd" = Some (snd bn256_pairing_dsd) ->
        (* Loader hypotheses *)
        (forall pout0 (old_out0 : Fp2_felem) R tr0 m0,
          (FElem_Fp2 pout0 old_out0 ⋆ R) m0 ->
          Semantics.call functions "bn256_load_gamma1_p2" tr0 m0 [pout0]
            (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
              exists out,
                Fp2_bounded Fp2_tight out /\
                (FElem_Fp2 pout0 out ⋆ R) m')) ->
        (forall pout0 (old_out0 : Fp2_felem) R tr0 m0,
          (FElem_Fp2 pout0 old_out0 ⋆ R) m0 ->
          Semantics.call functions "bn256_load_gamma2_p2" tr0 m0 [pout0]
            (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
              exists out,
                Fp2_bounded Fp2_tight out /\
                (FElem_Fp2 pout0 out ⋆ R) m')) ->
        (forall pout0 (old_out0 : Fp2_felem) R tr0 m0,
          (FElem_Fp2 pout0 old_out0 ⋆ R) m0 ->
          Semantics.call functions "bn256_load_w_frob_p2_c1" tr0 m0 [pout0]
            (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
              exists out,
                Fp2_bounded Fp2_tight out /\
                (FElem_Fp2 pout0 out ⋆ R) m')) ->
        (* Callee chain hypotheses *)
        (forall ptmp ppx ppy pqx pqy
          (old_tmp : Fp12_felem) (px py : Fp_felem) (qx qy : Fp2_felem) R tr0 m0,
          Fp2_bounded Fp2_tight qx ->
          Fp2_bounded Fp2_tight qy ->
          Fp_bounded Fp_loose px ->
          Fp_bounded Fp_loose py ->
          (FElem_Fp12 ptmp old_tmp ⋆
           (FElem_Fp ppx px ⋆
            (FElem_Fp ppy py ⋆
             (FElem_Fp2 pqx qx ⋆
              (FElem_Fp2 pqy qy ⋆ R))))) m0 ->
          Semantics.call functions "bn256_miller_loop" tr0 m0
            [ptmp; ppx; ppy; pqx; pqy]
            (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
              exists ml_out,
                Fp12_bounded Fp12_tight ml_out /\
                (FElem_Fp12 ptmp ml_out ⋆
                 (FElem_Fp ppx px ⋆
                  (FElem_Fp ppy py ⋆
                   (FElem_Fp2 pqx qx ⋆
                    (FElem_Fp2 pqy qy ⋆ R))))) m')) ->
        (forall po pf pg1 pg2 pw
          (old_o : Fp12_felem) (f : Fp12_felem)
          (g1 g2 w : Fp2_felem) R tr0 m0,
          Fp12_bounded Fp12_tight f ->
          Fp2_bounded Fp2_tight g1 ->
          Fp2_bounded Fp2_tight g2 ->
          Fp2_bounded Fp2_tight w ->
          (FElem_Fp12 pf f ⋆
           (FElem_Fp2 pg1 g1 ⋆
            (FElem_Fp2 pg2 g2 ⋆
             (FElem_Fp2 pw w ⋆
              (FElem_Fp12 po old_o ⋆ R))))) m0 ->
          Semantics.call functions "bn256_final_exp_dsd" tr0 m0
            [po; pf; pg1; pg2; pw]
            (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
              exists fe_out,
                Fp12_bounded Fp12_loose fe_out /\
                (FElem_Fp12 po fe_out ⋆
                 (FElem_Fp12 pf f ⋆
                  (FElem_Fp2 pg1 g1 ⋆
                   (FElem_Fp2 pg2 g2 ⋆
                    (FElem_Fp2 pw w ⋆ R))))) m')) ->
        (* Memory preconditions *)
        Fp2_bounded Fp2_tight q_x ->
        Fp2_bounded Fp2_tight q_y ->
        Fp_bounded Fp_loose p_x ->
        Fp_bounded Fp_loose p_y ->
        (FElem_Fp12 pout old_out ⋆
         (FElem_Fp p_px p_x ⋆
          (FElem_Fp p_py p_y ⋆
           (FElem_Fp2 p_qx q_x ⋆
            (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem ->
        WeakestPrecondition.call functions "bn256_pairing_dsd" tr mem
          [pout; p_px; p_py; p_qx; p_qy]
          (fun tr' mem' rets => rets = [] /\ tr = tr').
    Proof.
      intros functions tr mem pout p_px p_py p_qx p_qy
        old_out p_x p_y q_x q_y Rr
        HEnv HLG1 HLG2 HLW HML HFE
        Hbqx Hbqy Hbpx Hbpy Hsep.
      pose proof (bn256_pairing_dsd_ok functions HEnv HLG1 HLG2 HLW HML HFE
        pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem
        (conj Hbqx (conj Hbqy (conj Hbpx (conj Hbpy Hsep))))) as Hcall.
      eapply Semantics.weaken_call. { exact Hcall. }
      intros tr' mem' rets [Hrets [Htr _]].
      split; [exact Hrets | exact Htr].
    Qed.

End BN256_PairingTop.
