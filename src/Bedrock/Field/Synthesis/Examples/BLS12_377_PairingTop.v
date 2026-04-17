(** * BLS12-377 Top-Level Pairing WP Proof
    Standalone WP correctness proof for bls377_pairing_dsd from BLS12_377_Pairing.v,
    plus the top-level bls377_pairing_dsd_correct_standalone theorem.
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
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime_certif.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_PairingHelpers.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_377_PairingTop.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bls377_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_377_prime.m).

    Instance bls377_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls377_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls377_mul";
      PrimeField.add := "bls377_add";
      PrimeField.sub := "bls377_sub";
      PrimeField.opp := "bls377_opp";
      PrimeField.square := "bls377_square";
      PrimeField.scmula24 := "bls377_scmula24";
      PrimeField.inv := "bls377_inv";
      PrimeField.from_bytes := "bls377_from_bytes";
      PrimeField.to_bytes := "bls377_to_bytes";
      PrimeField.select_znz := "bls377_select_znz";
      PrimeField.felem_copy := "bls377_felem_copy";
      PrimeField.from_word := "bls377_from_word";
      PrimeField.from_list := "bls377_from_list";
    |}.

    Instance bls377_pf_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_377. Qed.

    Existing Instance prime_field_parameters.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Instance bls377_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls377_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls377_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls377_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls377_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls377_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls377_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls377_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls377_frep |}.

    Instance bls377_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls377_Fp_rep] in *.
      cbv [Field.bounded_by bls377_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let fp2_prefix := "bls377_Fp2_".
    Let fp6_prefix := "bls377_Fp6_".
    Let fp12_prefix := "bls377_Fp12_".

    (* β = -1 for BLS12-377 (p ≡ 3 mod 4) *)
    Let bls377_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-5).

    (* ξ = 1+u for BLS12-377 (cubic non-residue in Fp2 for Fp6 tower) *)
    Let bls377_xi_re : F PrimeField.M_pos := @F.zero PrimeField.M_pos.
    Let bls377_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Instance bls377_Fp2_params' : AbstractField.FieldParameters Fp2 :=
      ltac:(let v := eval cbv [ext_Fp2_params append] in (ext_Fp2_params bls377_beta "bls377_") in exact v).
    Instance bls377_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
      ltac:(let v := eval cbv [ext_Fp2_rep append] in (ext_Fp2_rep bls377_beta "bls377_") in exact v).
    Instance bls377_Fp6_params' : AbstractField.FieldParameters Fp6 :=
      ltac:(let v := eval cbv [ext_Fp6_params append] in (ext_Fp6_params bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
      ltac:(let v := eval cbv [ext_Fp6_rep append] in (ext_Fp6_rep bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp12_params' : AbstractField.FieldParameters Fp12 :=
      ltac:(let v := eval cbv [ext_Fp12_params append] in (ext_Fp12_params bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).
    Instance bls377_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
      ltac:(let v := eval cbv [ext_Fp12_rep append] in (ext_Fp12_rep bls377_beta bls377_xi_re bls377_xi_im "bls377_") in exact v).

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls377_Fp6_params' _ _ _ _ bls377_Fp6_rep').
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls377_Fp_rep).
    Local Notation Fp12_felem := (@AbstractField.felem _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').

    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bls377_Fp12_params'.
    Local Typeclasses Opaque bls377_Fp6_params'.
    Local Typeclasses Opaque bls377_Fp2_params'.

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

    Instance spec_of_bls377_pairing_dsd : spec_of "bls377_pairing_dsd" :=
      fnspec! "bls377_pairing_dsd" (pout p_px p_py p_qx p_qy : word)
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

    Lemma bls377_pairing_dsd_ok :
      forall functions
        (EnvContains : map.get functions "bls377_pairing_dsd" =
          Some (snd bls377_pairing_dsd))
        (HLoadG1 : map.get functions "bls377_load_gamma1_p2" =
          Some (snd bls377_load_gamma1_p2))
        (HLoadG2 : map.get functions "bls377_load_gamma2_p2" =
          Some (snd bls377_load_gamma2_p2))
        (HLoadW : map.get functions "bls377_load_w_frob_p2_c1" =
          Some (snd bls377_load_w_frob_p2_c1))
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
          Semantics.call functions "bls377_miller_loop" tr m
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
          Semantics.call functions "bls377_final_exp_dsd" tr m
            [po; pf; pg1; pg2; pw]
            (fun tr' m' rets => rets = [] /\ tr = tr' /\
              exists fe_out,
                Fp12_bounded Fp12_loose fe_out /\
                (FElem_Fp12 po fe_out ⋆
                 (FElem_Fp12 pf f ⋆
                  (FElem_Fp2 pg1 g1 ⋆
                   (FElem_Fp2 pg2 g2 ⋆
                    (FElem_Fp2 pw w ⋆ R))))) m')),
      spec_of_bls377_pairing_dsd functions.
    Proof.
      intros.
      unfold spec_of_bls377_pairing_dsd.
      intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
        [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls377_pairing_dsd. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }

      (* === Stackalloc 1: tmp (Fp12-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_tmp mStack_tmp mComb_tmp HstackTmp Hm_split_tmp.

      pose proof (@AbstractField.FElem_from_bytes _ bls377_Fp12_params' _ _ _ _
        bls377_Fp12_rep' wordok mapok a_tmp) as Hfb_tmp.
      unfold AbstractField.Placeholder in Hfb_tmp.
      pose proof (proj1 (Hfb_tmp mStack_tmp) HstackTmp) as [tmp_val Htmp_felem].
      clear Hfb_tmp HstackTmp.

      (* === Stackalloc 2: gamma1_p2 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_g1 mStack_g1 mComb_g1 HstackG1 Hm_split_g1.

      pose proof (@AbstractField.FElem_from_bytes _ bls377_Fp2_params' _ _ _ _
        bls377_Fp2_rep' wordok mapok a_g1) as Hfb_g1.
      unfold AbstractField.Placeholder in Hfb_g1.
      pose proof (proj1 (Hfb_g1 mStack_g1) HstackG1) as [g1_val Hg1_felem].
      clear Hfb_g1 HstackG1.

      (* === Stackalloc 3: gamma2_p2 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_g2 mStack_g2 mComb_g2 HstackG2 Hm_split_g2.

      pose proof (@AbstractField.FElem_from_bytes _ bls377_Fp2_params' _ _ _ _
        bls377_Fp2_rep' wordok mapok a_g2) as Hfb_g2.
      unfold AbstractField.Placeholder in Hfb_g2.
      pose proof (proj1 (Hfb_g2 mStack_g2) HstackG2) as [g2_val Hg2_felem].
      clear Hfb_g2 HstackG2.

      (* === Stackalloc 4: w_frob_p2_c1 (Fp2-sized) === *)
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_w mStack_w mComb_w HstackW Hm_split_w.

      pose proof (@AbstractField.FElem_from_bytes _ bls377_Fp2_params' _ _ _ _
        bls377_Fp2_rep' wordok mapok a_w) as Hfb_w.
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

      unfold BLS12_377_Pairing.pairing_dsd_body, BLS12_377_Pairing.cmd_seq_list.

      Local Ltac solve_loader_sep :=
        try change BLS12_377_PairingHelpers.bls377_Fp2_params' with bls377_Fp2_params';
        try change BLS12_377_PairingHelpers.bls377_Fp2_rep' with bls377_Fp2_rep';
        try change BLS12_377_PairingHelpers.bls377_Fp12_params' with bls377_Fp12_params';
        try change BLS12_377_PairingHelpers.bls377_Fp12_rep' with bls377_Fp12_rep';
        try change BLS12_377_PairingHelpers.bls377_Fp_rep with bls377_Fp_rep;
        try change BLS12_377_PairingHelpers.bls377_pf_params with bls377_pf_params;
        ecancel_assumption.

      (* === Call 1: bls377_load_gamma1_p2(gamma1_p2) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply BLS12_377_PairingHelpers.bls377_load_gamma1_p2_ok.
        - exact HLoadG1.
        - solve_loader_sep.
      }
      intros t1 m1 rets1 [Hrets1 [Htr1 [g1_out [Hbg1_out Hsep_g1]]]].
      subst rets1. symmetry in Htr1. subst t1.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 2: bls377_load_gamma2_p2(gamma2_p2) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply BLS12_377_PairingHelpers.bls377_load_gamma2_p2_ok.
        - exact HLoadG2.
        - solve_loader_sep.
      }
      intros t2 m2 rets2 [Hrets2 [Htr2 [g2_out [Hbg2_out Hsep_g2]]]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 3: bls377_load_w_frob_p2_c1(w_frob_p2_c1) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        eapply BLS12_377_PairingHelpers.bls377_load_w_frob_p2_c1_ok.
        - exact HLoadW.
        - solve_loader_sep.
      }
      intros t3 m3 rets3 [Hrets3 [Htr3 [w_out [Hbw_out Hsep_w]]]].
      subst rets3. symmetry in Htr3. subst t3.
      cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* === Call 4: bls377_miller_loop(tmp, p_x, p_y, q_x, q_y) === *)
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

      (* === Call 5: bls377_final_exp_dsd(out, tmp, g1, g2, w) === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: {
        (* Call 5: provide Semantics.call for final_exp.
           The sep hypothesis Hsep_ml has the right FElems but in a different
           order than HFinalExp expects. Use eapply + ecancel_assumption. *)
        eapply (HFinalExp pout a_tmp a_g1 a_g2 a_w
          old_out ml_out g1_out g2_out w_out);
        [exact Hbml_out | exact Hbg1_out | exact Hbg2_out | exact Hbw_out |].
        (* The sep hypothesis from Call 4 has FElem with Helpers' instances
           (embedded when ecancel_assumption unified the frame for loaders).
           Convert Helpers' instances to local ones, then ecancel. *)
        try change BLS12_377_PairingHelpers.bls377_Fp2_params' with bls377_Fp2_params' in *;
        try change BLS12_377_PairingHelpers.bls377_Fp2_rep' with bls377_Fp2_rep' in *;
        try change BLS12_377_PairingHelpers.bls377_Fp12_params' with bls377_Fp12_params' in *;
        try change BLS12_377_PairingHelpers.bls377_Fp12_rep' with bls377_Fp12_rep' in *;
        try change BLS12_377_PairingHelpers.bls377_Fp_rep with bls377_Fp_rep in *;
        try change BLS12_377_PairingHelpers.bls377_pf_params with bls377_pf_params in *;
        ecancel_assumption.
      }
      intros t5 m5 rets5 [Hrets5 [Htr5 [fe_out [Hbfe_out Hsep_fe]]]].
      subst rets5. symmetry in Htr5. subst t5.

      (* Normalize instances in Hsep_fe: the frame R from ecancel may embed
         PairingHelpers instances. Convert them to local ones. *)
      try change BLS12_377_PairingHelpers.bls377_Fp2_params' with bls377_Fp2_params' in Hsep_fe;
      try change BLS12_377_PairingHelpers.bls377_Fp2_rep' with bls377_Fp2_rep' in Hsep_fe;
      try change BLS12_377_PairingHelpers.bls377_Fp12_params' with bls377_Fp12_params' in Hsep_fe;
      try change BLS12_377_PairingHelpers.bls377_Fp12_rep' with bls377_Fp12_rep' in Hsep_fe;
      try change BLS12_377_PairingHelpers.bls377_Fp_rep with bls377_Fp_rep in Hsep_fe;
      try change BLS12_377_PairingHelpers.bls377_pf_params with bls377_pf_params in Hsep_fe.

      (* === Stack deallocation (4 levels) + final postcondition === *)
      (* The remaining obligation: from the sep on m5 containing 9 FElems,
         extract the 4 stack FElems (w, g2, g1, tmp), convert each to anybytes
         via FElem_to_bytes, and provide map.split witnesses for each of the
         4 nested stackalloc levels. Then prove the final postcondition.

         This requires careful sep decomposition + map.putmany rearrangement.
         The mechanical pattern (wp_destruct_sep + split_all_disjointness +
         solve_putmany_eq + map_disjoint_auto) works but needs instance
         normalization to match FElem patterns across modules. *)
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

    Theorem bls377_pairing_dsd_correct_standalone :
      forall functions tr mem pout p_px p_py p_qx p_qy
        (old_out : Fp12_felem) (p_x p_y : Fp_felem)
        (q_x q_y : Fp2_felem) Rr,
        map.get functions "bls377_pairing_dsd" = Some (snd bls377_pairing_dsd) ->
        map.get functions "bls377_load_gamma1_p2" =
          Some (snd bls377_load_gamma1_p2) ->
        map.get functions "bls377_load_gamma2_p2" =
          Some (snd bls377_load_gamma2_p2) ->
        map.get functions "bls377_load_w_frob_p2_c1" =
          Some (snd bls377_load_w_frob_p2_c1) ->
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
          Semantics.call functions "bls377_miller_loop" tr0 m0
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
          Semantics.call functions "bls377_final_exp_dsd" tr0 m0
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
        WeakestPrecondition.call functions "bls377_pairing_dsd" tr mem
          [pout; p_px; p_py; p_qx; p_qy]
          (fun tr' mem' rets => rets = [] /\ tr = tr').
    Proof.
      intros functions tr mem pout p_px p_py p_qx p_qy
        old_out p_x p_y q_x q_y Rr
        HEnv HLG1 HLG2 HLW HML HFE
        Hbqx Hbqy Hbpx Hbpy Hsep.
      (* spec_of_bls377_pairing_dsd uses fnspec! with `ensures tr' mem' :=`
         which auto-includes `rets = nil /\` in the postcondition.
         So the spec postcondition is: fun tr' mem' rets =>
           rets = nil /\ (tr = tr' /\ exists out, ...).
         We weaken to just: rets = [] /\ tr = tr'. *)
      pose proof (bls377_pairing_dsd_ok functions HEnv HLG1 HLG2 HLW HML HFE
        pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem
        (conj Hbqx (conj Hbqy (conj Hbpx (conj Hbpy Hsep))))) as Hcall.
      eapply Semantics.weaken_call. { exact Hcall. }
      intros tr' mem' rets [Hrets [Htr _]].
      split; [exact Hrets | exact Htr].
    Qed.

End BLS12_377_PairingTop.
