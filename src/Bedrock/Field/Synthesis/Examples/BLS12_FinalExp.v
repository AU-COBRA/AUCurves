(** * BLS12-381 Final Exponentiation WP Proof
    Standalone WP correctness proof for bls12_final_exp from BLS12_Pairing.v.
    Easy part: conjugate + inv + mul + frobenius_p2 + mul
    Hard part: square-and-multiply with 1268-bit h3 exponent
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
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExpH3.
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

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bls12_Fp_rep).

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

    (* For from_word snd calls, use impl-based ecancel which handles
       definitional equality between BLS12_Pairing/PairingHelpers/FinalExp instances *)
    Local Ltac snd_from_word_ecancel H :=
      let H' := fresh "H" in
      pose proof H as H';
      ecancel_assumption_impl.

    (* h3_limbs, h3_store_cmd, h3_store_limbs_wp imported from BLS12_FinalExpH3 *)
    Local Notation h3_limbs := BLS12_FinalExpH3.h3_limbs.
    Local Notation h3_store_cmd := BLS12_FinalExpH3.h3_store_cmd.

    (* Loop invariant for the final exponentiation square-and-multiply loop.
       The measure v counts down from 1280 to 0. *)
    Definition final_exp_loop_inv
      (a_result a_tmp a_base a_h3 : word)
      (pout pf p_gamma1_p2 p_gamma2_p2 p_w_frob_p2_c1 : word)
      (f : Fp12_felem)
      (gamma1_p2 gamma2_p2 w_frob_p2_c1 : Fp2_felem)
      (old_out : Fp12_felem)
      (Rr : mem -> Prop) (tr : Semantics.trace)
      (v : nat) (t : Semantics.trace) (m : mem) (l : locals) : Prop :=
      t = tr /\ (v <= 1280)%nat /\
      exists (result_val tmp_val base_val : Fp12_felem)
             (started_w : word),
        Fp12_bounded Fp12_tight result_val /\
        Fp12_bounded Fp12_tight base_val /\
        (FElem_Fp12 a_result result_val ⋆
         (FElem_Fp12 a_tmp tmp_val ⋆
          (FElem_Fp12 a_base base_val ⋆
           (array scalar (word.of_Z 8) a_h3 h3_limbs ⋆
            (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
             (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
              (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
               (FElem_Fp12 pf f ⋆
                (FElem_Fp12 pout old_out ⋆ Rr))))))))) m /\
        map.get l "i" = Some (word.of_Z (Z.of_nat v)) /\
        map.get l "started" = Some started_w /\
        map.get l "result" = Some a_result /\
        map.get l "tmp" = Some a_tmp /\
        map.get l "base" = Some a_base /\
        map.get l "h3" = Some a_h3 /\
        map.get l "out" = Some pout /\
        map.get l "f" = Some pf.

    Local Notation h3_store_limbs_wp := BLS12_FinalExpH3.h3_store_limbs_wp.

    (* Local bridge lemma: weaken h3_store_limbs_wp for use in cmd.seq context.
       Defined locally to avoid depending on FinalExpH3.vo recompilation. *)
    Local Lemma h3_stores_then_rest :
      forall call t (m : mem) l (a_h3 : word) (oldws : list word) R
             (post : Semantics.trace -> mem -> locals -> Prop),
        length oldws = 20%nat ->
        map.get l "h3" = Some a_h3 ->
        (array scalar (word.of_Z 8) a_h3 oldws ⋆ R) m ->
        (forall m', (array scalar (word.of_Z 8) a_h3 h3_limbs ⋆ R) m' ->
          post t m' l) ->
        WeakestPrecondition.cmd call h3_store_cmd t m l post.
    Proof.
      intros call t m l a_h3 oldws R post Hlen Hget Hsep Hpost.
      pose proof (h3_store_limbs_wp call t m l a_h3 oldws R Hlen Hget Hsep) as Hwp.
      eapply WeakestPreconditionProperties.Proper_cmd in Hwp.
      { exact Hwp. }
      cbv [Morphisms.pointwise_relation Basics.impl].
      intros t' m' l' [Ht' [Hl' Hsep']]. subst. exact (Hpost m' Hsep').
    Qed.

    (* Load from h3 array at symbolic index via shift arithmetic *)
    Local Lemma h3_array_load (a_h3 i_val : word) (m : mem) (R : mem -> Prop)
      (Hsep : (array scalar (word.of_Z 8) a_h3 h3_limbs ⋆ R) m) :
      let idx := Z.to_nat (word.unsigned (word.sru i_val (word.of_Z 6))) in
      let addr := word.add a_h3 (word.slu (word.sru i_val (word.of_Z 6)) (word.of_Z 3)) in
      (idx < length h3_limbs)%nat ->
      Memory.load access_size.word m addr = Some (nth idx h3_limbs (word.of_Z 0)).
    Proof.
      intros idx addr Hbound.
      pose proof (Scalars.array_load_of_sep a_h3 addr idx h3_limbs
        (word.of_Z 8) access_size.word R m Hsep) as Hload.
      assert (Haddr : addr = word.add a_h3
        (word.of_Z (word.unsigned (word.of_Z (width:=64) 8) * Z.of_nat idx))).
      { subst addr idx. f_equal.
        apply word.unsigned_inj.
        rewrite word.unsigned_slu_shamtZ by lia.
        rewrite Z.shiftl_mul_pow2 by lia. change (2^3) with 8.
        rewrite word.unsigned_of_Z.
        unfold word.wrap. f_equal.
        rewrite Z2Nat.id
          by (pose proof (word.unsigned_range (word.sru i_val (word.of_Z 6))); lia).
        (* Goal: u * 8 = word.unsigned(of_Z 8) * u (where u = unsigned(sru ...)) *)
        (* word.unsigned(of_Z 8) reduces to 8 mod 2^64 = 8 *)
        change (word.unsigned (word.of_Z (width:=64) 8)) with 8.
        lia. }
      rewrite Hload by assumption.
      f_equal. unfold Scalars.truncate_word, Scalars.truncate_Z.
      apply word.unsigned_inj. rewrite word.unsigned_of_Z.
      unfold word.wrap. rewrite Z.land_ones by lia.
      pose proof (word.unsigned_range (nth idx h3_limbs (word.of_Z 0))).
      rewrite Zmod_mod. rewrite Z.mod_small by lia. reflexivity.
    Qed.

    Lemma bls12_final_exp_ok :
      forall functions
        (EnvContains : map.get functions "bls12_final_exp" = Some (snd bls12_final_exp))
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HFp12inv : spec_of_Fp12_inv functions)
        (HFp12copy : spec_of_Fp12_felem_copy functions)
        (HFp12conj : spec_of_Fp12_conjugate functions)
        (HFp12frob : spec_of_Fp12_frobenius_p2 functions)
        (HFfromword : spec_of_Fp_from_word functions),
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

      (* 4 stackallocs *)
      straightline. split. { apply Z_mod_mult. }
      intros a_result mSr mCr HaSr HmSr.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_result mSr) HaSr) as [ri Hri].

      straightline. split. { apply Z_mod_mult. }
      intros a_tmp mSt mCt HaSt HmSt.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_tmp mSt) HaSt) as [ti Hti].

      straightline. split. { apply Z_mod_mult. }
      intros a_base mSb mCb HaSb HmSb.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_base mSb) HaSb) as [bi Hbi].

      straightline. split. { reflexivity. }
      intros a_h3 mSh mCh HaSh HmSh.

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

      (* Step 3: lift to mCb, adding FElem_Fp12 a_base bi *)
      pose proof (proj1 (map.split_comm mCb mCt mSb) HmSb) as HmSb'.
      assert (Hsep3 :
        (FElem_Fp12 a_base bi ⋆
         (FElem_Fp12 a_tmp ti ⋆
          (FElem_Fp12 a_result ri ⋆
           (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
             (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
               (FElem_Fp12 pout old_out ⋆ Rr)))))))) mCb).
      { exists mSb, mCt. exact (conj HmSb' (conj Hbi Hsep2)). }

      (* Step 4: lift to mCh, adding Memory.anybytes a_h3 160 *)
      pose proof (proj1 (map.split_comm mCh mCb mSh) HmSh) as HmSh'.
      assert (Hsep_all :
        (Memory.anybytes a_h3 160 ⋆
         (FElem_Fp12 a_base bi ⋆
          (FElem_Fp12 a_tmp ti ⋆
           (FElem_Fp12 a_result ri ⋆
            (FElem_Fp12 pf f ⋆ (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
              (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆ (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
                (FElem_Fp12 pout old_out ⋆ Rr))))))))) mCh).
      { exists mSh, mCb. exact (conj HmSh' (conj HaSh Hsep3)). }

      (* Clear intermediate sep facts *)
      clear Hsep Hsep1 Hsep2 Hsep3.

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

      (* Call 6: fp12_copy(base, result) — felem_copy spec *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12copy.
           split; ecancel_assumption_with_copy. }
      intros ? ? ? [Hrets6 [Htr6 [copy_out [Hbound_copy Hsep_copy]]]].
      subst. cbv [map.putmany_of_list_zip].
      eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* D2: fp12_set_one + h3_stores + loop + final copy + dealloc       *)
      (*                                                                   *)
      (* The remaining program body consists of:                           *)
      (*   1. fp12_set_one "result" — 12 from_word calls                   *)
      (*   2. h3_store_limbs — 20 word stores                              *)
      (*   3. set started=0, set i=1280                                    *)
      (*   4. while(i) { h3_loop_body } — 1280 iter square-and-multiply   *)
      (*   5. fp12_copy(out, result)                                       *)
      (*   6. 4 stack deallocations + postcondition                        *)
      (*                                                                   *)
      (* Proof strategy:                                                   *)
      (*   - Reconstruct combined sep on m'4 from copy postcondition       *)
      (*   - Convert FElem_Fp12 a_result to fresh value via Placeholder    *)
      (*   - Decompose FElem_Fp12 → 2×Fp6 → 6×Fp2                         *)
      (*   - Build master sep with 6 FElem_Fp2 + rest                     *)
      (*   - For each Fp2 pair: split → 2 from_word → join                *)
      (*   - repeat straightline handles stores + sets                     *)
      (*   - Loops.while_localsmap with invariant for the loop             *)
      (*   - Post-loop: fp12_copy + 4 stack deallocs                       *)
      (* ================================================================ *)

      (* Reconstruct combined sep on m'4 *)
      destruct Hsep_copy as [Hsplit6 [Hbase6 Hrest6]].
      assert (Hsep_m4 :
        (FElem_Fp12 a_base mul2_out ⋆
         (FElem_Fp12 a_result mul2_out ⋆
          (FElem_Fp12 a_tmp frob_out ⋆
           (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
             (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
              (Memory.anybytes a_h3 160 ⋆
               (FElem_Fp12 pf f ⋆
                (FElem_Fp12 pout old_out ⋆ Rr))))))))) m'4).
      { exists copy_out, Hbound_copy.
        exact (conj Hsplit6 (conj Hbase6 Hrest6)). }
      clear Hsplit6 Hbase6 Hrest6 Hsep_mul2.

      (* ================================================================ *)
      (* Local notation block for offset/accessor names                   *)
      (* ================================================================ *)
      Local Notation fp_felem_offset :=
        (Memory.bytes_per_word 64 * Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep)).
      Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls12_Fp_rep).
      Local Notation FElem_Fp6 := (@AbstractField.FElem _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').
      Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls12_Fp_rep).
      Local Notation Fp_tight := (@AbstractField.tight_bounds _ _ _ _ _ _ bls12_Fp_rep).
      Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls12_Fp_rep).
      Local Notation Fp_fsw := (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_Fp_rep).
      Local Notation Fp2_felem_size := (@AbstractField.felem_size_in_words _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep').
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

      (* ================================================================ *)
      (* Split FElem_Fp12 a_result into 6 FElem_Fp2 sub-components       *)
      (* ================================================================ *)

      (* Split Fp12 into 2 Fp6 halves *)
      pose proof (DodecicFieldExtensions.Fp12_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp12_prefix fp6_prefix fp2_prefix a_result mul2_out) as Hfp12_split.
      eassert (Hresult_sep : (FElem_Fp12 a_result mul2_out ⋆ _) m'4).
      { pose proof Hsep_m4 as H'. ecancel_assumption. }
      destruct Hresult_sep as [m_result [m_rest_r [[Heq_r Hd_r] [Hfe_result Hrest_r]]]].
      pose proof (Hfp12_split m_result Hfe_result) as [m_fp6_0 [m_fp6_1 [Hsep_fp12 [Hfe_fp6_0 Hfe_fp6_1]]]].
      destruct Hsep_fp12 as [Heq_fp12 Hd_fp12]. subst m_result.
      clear Hfp12_split.

      (* Split each Fp6 into 3 Fp2 *)
      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix a_result _ m_fp6_0 Hfe_fp6_0)
        as [m_r00 [m_r01_02 [Hsep_d0 [Hr00 Hr01_02]]]].
      destruct Hr01_02 as [m_r01 [m_r02 [Hsep_d0_12 [Hr01 Hr02]]]].
      destruct Hsep_d0 as [Heq_d0 Hd_d0]. destruct Hsep_d0_12 as [Heq_d0_12 Hd_d0_12].
      subst m_fp6_0 m_r01_02.

      pose proof (CubicFieldExtensions.Fp6_raw_FElem_split bls12_beta bls12_xi_re bls12_xi_im
        fp6_prefix fp2_prefix
        (word.add a_result (word.of_Z fp6_felem_offset)) _ m_fp6_1 Hfe_fp6_1)
        as [m_r10 [m_r11_12 [Hsep_d1 [Hr10 Hr11_12]]]].
      destruct Hr11_12 as [m_r11 [m_r12 [Hsep_d1_12 [Hr11 Hr12]]]].
      destruct Hsep_d1 as [Heq_d1 Hd_d1]. destruct Hsep_d1_12 as [Heq_d1_12 Hd_d1_12].
      subst m_fp6_1 m_r11_12.

      (* Build 6-way Fp2 sep on m'4 *)
      split_all_disjointness.

      assert (Hsep_6fp2 :
        (FElem_Fp2 a_result (c0_felem (d0_felem mul2_out)) ⋆
         (FElem_Fp2 (word.add a_result fp6_c1_off) (c1_felem (d0_felem mul2_out)) ⋆
          (FElem_Fp2 (word.add a_result fp6_c2_off) (c2_felem (d0_felem mul2_out)) ⋆
           (FElem_Fp2 (word.add a_result (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem mul2_out)) ⋆
            (FElem_Fp2 (word.add (word.add a_result (word.of_Z fp6_felem_offset)) fp6_c1_off)
               (c1_felem (d1_felem mul2_out)) ⋆
             (FElem_Fp2 (word.add (word.add a_result (word.of_Z fp6_felem_offset)) fp6_c2_off)
                (c2_felem (d1_felem mul2_out)) ⋆
              (FElem_Fp12 a_base mul2_out ⋆
               (FElem_Fp12 a_tmp frob_out ⋆
                (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
                 (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
                  (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
                   (Memory.anybytes a_h3 160 ⋆
                    (FElem_Fp12 pf f ⋆
                     (FElem_Fp12 pout old_out ⋆ Rr)))))))))))))) m'4).
      { (* Rebuild the sep from destructed parts *)
        subst m'4.
        pose proof Hrest_r as Hrest_r'.
        rewrite <- ?map.putmany_assoc.
        exists m_r00, (map.putmany m_r01 (map.putmany m_r02
          (map.putmany m_r10 (map.putmany m_r11 (map.putmany m_r12 m_rest_r))))).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hr00 |].
        exists m_r01, (map.putmany m_r02
          (map.putmany m_r10 (map.putmany m_r11 (map.putmany m_r12 m_rest_r)))).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hr01 |].
        exists m_r02, (map.putmany m_r10 (map.putmany m_r11 (map.putmany m_r12 m_rest_r))).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hr02 |].
        exists m_r10, (map.putmany m_r11 (map.putmany m_r12 m_rest_r)).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hr10 |].
        exists m_r11, (map.putmany m_r12 m_rest_r).
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hr11 |].
        exists m_r12, m_rest_r.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hr12 |].
        exact Hrest_r'. }

      clear Hsep_m4 Hrest_r Hr00 Hr01 Hr02 Hr10 Hr11 Hr12 Hfe_fp6_0 Hfe_fp6_1.

      (* ================================================================ *)
      (* Unfold fp12_set_one + expression helpers                         *)
      (* ================================================================ *)
      unfold BLS12_Pairing.fp12_set_one, BLS12_Pairing.cmd_seq_list.
      unfold BLS12_Pairing.expr_fp12_c0, BLS12_Pairing.expr_fp12_c1,
             BLS12_Pairing.expr_fp6_c0, BLS12_Pairing.expr_fp6_c1,
             BLS12_Pairing.expr_fp6_c2, BLS12_Pairing.expr_fp_snd.

      (* ================================================================ *)
      (* 12 from_word calls on a_result sub-components                    *)
      (* ================================================================ *)

      (* --- from_word 1: result.d0.c0.fst = 1 --- *)
      repeat straightline.
      eassert (Hsplit_fw1 :
        (FElem_Fp2 a_result (c0_felem (d0_felem mul2_out)) ⋆ _) _).
      { pose proof Hsep_6fp2 as H'. ecancel_assumption. }
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hsplit_fw1.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c0_felem (d0_felem mul2_out)))).
           exact Hsplit_fw1. }
      intros ? ? ? [? [? [fw1 [? [Hb_fw1 Hsep_fw1]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- from_word 2: result.d0.c0.snd = 0 --- *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c0_felem (d0_felem mul2_out)))).
           snd_from_word_ecancel Hsep_fw1. }
      intros ? ? ? [? [? [fw2 [? [Hb_fw2 Hsep_fw2]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- from_word 3-4: result.d0.c1 fst/snd = 0 --- *)
      repeat straightline.
      eassert (Hsplit_fw3 :
        (FElem_Fp2 (word.add a_result fp6_c1_off) (c1_felem (d0_felem mul2_out)) ⋆ _) _).
      { pose proof Hsep_fw2 as H'. ecancel_assumption. }
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hsplit_fw3.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c1_felem (d0_felem mul2_out)))).
           exact Hsplit_fw3. }
      intros ? ? ? [? [? [fw3 [? [Hb_fw3 Hsep_fw3]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c1_felem (d0_felem mul2_out)))).
           snd_from_word_ecancel Hsep_fw3. }
      intros ? ? ? [? [? [fw4 [? [Hb_fw4 Hsep_fw4]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- from_word 5-6: result.d0.c2 fst/snd = 0 --- *)
      repeat straightline.
      eassert (Hsplit_fw5 :
        (FElem_Fp2 (word.add a_result fp6_c2_off) (c2_felem (d0_felem mul2_out)) ⋆ _) _).
      { pose proof Hsep_fw4 as H'. ecancel_assumption. }
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hsplit_fw5.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d0_felem mul2_out)))).
           exact Hsplit_fw5. }
      intros ? ? ? [? [? [fw5 [? [Hb_fw5 Hsep_fw5]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d0_felem mul2_out)))).
           snd_from_word_ecancel Hsep_fw5. }
      intros ? ? ? [? [? [fw6 [? [Hb_fw6 Hsep_fw6]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- from_word 7-8: result.d1.c0 fst/snd = 0 --- *)
      repeat straightline.
      eassert (Hsplit_fw7 :
        (FElem_Fp2 (word.add a_result (word.of_Z fp6_felem_offset)) (c0_felem (d1_felem mul2_out)) ⋆ _) _).
      { pose proof Hsep_fw6 as H'. ecancel_assumption. }
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hsplit_fw7.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c0_felem (d1_felem mul2_out)))).
           exact Hsplit_fw7. }
      intros ? ? ? [? [? [fw7 [? [Hb_fw7 Hsep_fw7]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c0_felem (d1_felem mul2_out)))).
           snd_from_word_ecancel Hsep_fw7. }
      intros ? ? ? [? [? [fw8 [? [Hb_fw8 Hsep_fw8]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- from_word 9-10: result.d1.c1 fst/snd = 0 --- *)
      repeat straightline.
      eassert (Hsplit_fw9 :
        (FElem_Fp2 (word.add (word.add a_result (word.of_Z fp6_felem_offset)) fp6_c1_off)
           (c1_felem (d1_felem mul2_out)) ⋆ _) _).
      { pose proof Hsep_fw8 as H'. ecancel_assumption. }
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hsplit_fw9.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c1_felem (d1_felem mul2_out)))).
           exact Hsplit_fw9. }
      intros ? ? ? [? [? [fw9 [? [Hb_fw9 Hsep_fw9]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c1_felem (d1_felem mul2_out)))).
           snd_from_word_ecancel Hsep_fw9. }
      intros ? ? ? [? [? [fw10 [? [Hb_fw10 Hsep_fw10]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* --- from_word 11-12: result.d1.c2 fst/snd = 0 --- *)
      repeat straightline.
      eassert (Hsplit_fw11 :
        (FElem_Fp2 (word.add (word.add a_result (word.of_Z fp6_felem_offset)) fp6_c2_off)
           (c2_felem (d1_felem mul2_out)) ⋆ _) _).
      { pose proof Hsep_fw10 as H'. ecancel_assumption. }
      apply BLS12_PairingHelpers.FElem_Fp2_split_in_sep in Hsplit_fw11.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (fst_felem (c2_felem (d1_felem mul2_out)))).
           exact Hsplit_fw11. }
      intros ? ? ? [? [? [fw11 [? [Hb_fw11 Hsep_fw11]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _
             (snd_felem (c2_felem (d1_felem mul2_out)))).
           snd_from_word_ecancel Hsep_fw11. }
      intros ? ? ? [? [? [fw12 [? [Hb_fw12 Hsep_fw12]]]]].
      subst. cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Step 1: Extract Fp-level lengths === *)
      pose proof fun p v m (H : FElem_Fp p v m) =>
        @QuadraticFieldExtensions.AbstractFElem_length _ _ _ _
          bls12_pf_params bls12_Fp_rep p v m H
        as FpLen.

      (* Use match to name the current memory from Hsep_fw12 *)
      match type of Hsep_fw12 with
      | (_ ⋆ _) ?m => set (m_fw := m) in *
      end.

      assert (Hlen_fw1 : length fw1 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw1 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw2 : length fw2 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw2 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw3 : length fw3 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw3 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw4 : length fw4 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw4 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw5 : length fw5 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw5 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw6 : length fw6 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw6 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw7 : length fw7 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw7 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw8 : length fw8 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw8 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw9 : length fw9 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw9 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw10 : length fw10 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw10 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw11 : length fw11 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw11 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      assert (Hlen_fw12 : length fw12 = Fp_fsw).
      { assert (Htmp : (FElem_Fp _ fw12 ⋆ _) m_fw) by
          (pose proof Hsep_fw12 as H'; ecancel_assumption).
        destruct Htmp as [msub [_ [_ [Hfe _]]]]. exact (FpLen _ _ _ Hfe). }
      clear FpLen.

      (* === Step 2: Chain-join Fp pairs into Fp2 === *)

      (* Join d0.c0: fw1 + fw2 *)
      eassert (Hsep_j1 : (FElem_Fp _ fw1 ⋆ (FElem_Fp _ fw2 ⋆ _)) m_fw).
      { pose proof Hsep_fw12 as H'. ecancel_assumption. }
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in Hsep_j1;
        [| exact Hlen_fw1 | exact Hlen_fw2].

      (* Join d0.c1: fw3 + fw4 *)
      eassert (Hsep_j2 : (FElem_Fp _ fw3 ⋆ (FElem_Fp _ fw4 ⋆ _)) m_fw).
      { pose proof Hsep_j1 as H'. ecancel_assumption. }
      eassert (Hsep_j2' : (FElem_Fp _ fw3 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw4 ⋆ _)) m_fw).
      { exact Hsep_j2. }
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in Hsep_j2';
        [| exact Hlen_fw3 | exact Hlen_fw4].

      (* Join d0.c2: fw5 + fw6 *)
      eassert (Hsep_j3 : (FElem_Fp _ fw5 ⋆ (FElem_Fp _ fw6 ⋆ _)) m_fw).
      { pose proof Hsep_j2' as H'. ecancel_assumption. }
      eassert (Hsep_j3' : (FElem_Fp _ fw5 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw6 ⋆ _)) m_fw).
      { exact Hsep_j3. }
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in Hsep_j3';
        [| exact Hlen_fw5 | exact Hlen_fw6].

      (* Join d1.c0: fw7 + fw8 *)
      eassert (Hsep_j4 : (FElem_Fp _ fw7 ⋆ (FElem_Fp _ fw8 ⋆ _)) m_fw).
      { pose proof Hsep_j3' as H'. ecancel_assumption. }
      eassert (Hsep_j4' : (FElem_Fp _ fw7 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw8 ⋆ _)) m_fw).
      { exact Hsep_j4. }
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in Hsep_j4';
        [| exact Hlen_fw7 | exact Hlen_fw8].

      (* Join d1.c1: fw9 + fw10 *)
      eassert (Hsep_j5 : (FElem_Fp _ fw9 ⋆ (FElem_Fp _ fw10 ⋆ _)) m_fw).
      { pose proof Hsep_j4' as H'. ecancel_assumption. }
      eassert (Hsep_j5' : (FElem_Fp _ fw9 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw10 ⋆ _)) m_fw).
      { exact Hsep_j5. }
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in Hsep_j5';
        [| exact Hlen_fw9 | exact Hlen_fw10].

      (* Join d1.c2: fw11 + fw12 *)
      eassert (Hsep_j6 : (FElem_Fp _ fw11 ⋆ (FElem_Fp _ fw12 ⋆ _)) m_fw).
      { pose proof Hsep_j5' as H'. ecancel_assumption. }
      eassert (Hsep_j6' : (FElem_Fp _ fw11 ⋆ (FElem_Fp (word.add _ (word.of_Z fp_felem_offset)) fw12 ⋆ _)) m_fw).
      { exact Hsep_j6. }
      apply BLS12_PairingHelpers.FElem_Fp_join_in_sep in Hsep_j6';
        [| exact Hlen_fw11 | exact Hlen_fw12].

      (* === Steps 3-6: Join Fp2→Fp6→Fp12 and rebuild sep === *)

      Local Notation Fp6_fsw := (@AbstractField.felem_size_in_words _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep').

      (* Rearrange into [d0_3 * (d1_3 * rest)] to extract sub-memories *)
      eassert (Hsep_d0_ext :
        ((FElem_Fp2 a_result (fw1 ++ fw2) ⋆
          (FElem_Fp2 (word.add a_result fp6_c1_off) (fw3 ++ fw4) ⋆
           FElem_Fp2 (word.add a_result fp6_c2_off) (fw5 ++ fw6))) ⋆ _) m_fw).
      { pose proof Hsep_j6' as H'. ecancel_assumption_impl. }
      destruct Hsep_d0_ext as [m_d0_3 [m_d0_rest [Hsplit_d0 [Hfe_d0_3 Hd0_rest]]]].

      eassert (Hd1_3_ext :
        ((FElem_Fp2 (word.add a_result (word.of_Z fp6_felem_offset)) (fw7 ++ fw8) ⋆
          (FElem_Fp2 (word.add (word.add a_result (word.of_Z fp6_felem_offset)) fp6_c1_off) (fw9 ++ fw10) ⋆
           FElem_Fp2 (word.add (word.add a_result (word.of_Z fp6_felem_offset)) fp6_c2_off) (fw11 ++ fw12))) ⋆ _) m_d0_rest).
      { pose proof Hd0_rest as H'. ecancel_assumption_impl. }
      destruct Hd1_3_ext as [m_d1_3 [m_rest [Hsplit_d1 [Hfe_d1_3 Hrest]]]].

      (* Length facts for Fp2 *)
      assert (Hlen_d0c0_fp2 : length (fw1 ++ fw2) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw1, Hlen_fw2. reflexivity. }
      assert (Hlen_d0c1_fp2 : length (fw3 ++ fw4) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw3, Hlen_fw4. reflexivity. }
      assert (Hlen_d0c2_fp2 : length (fw5 ++ fw6) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw5, Hlen_fw6. reflexivity. }
      assert (Hlen_d1c0_fp2 : length (fw7 ++ fw8) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw7, Hlen_fw8. reflexivity. }
      assert (Hlen_d1c1_fp2 : length (fw9 ++ fw10) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw9, Hlen_fw10. reflexivity. }
      assert (Hlen_d1c2_fp2 : length (fw11 ++ fw12) = Fp2_felem_size).
      { rewrite length_app, Hlen_fw11, Hlen_fw12. reflexivity. }

      (* Build Fp6 for d0 *)
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix
        a_result (fw1 ++ fw2) (fw3 ++ fw4) (fw5 ++ fw6) m_d0_3
        Hlen_d0c0_fp2 Hlen_d0c1_fp2 Hlen_d0c2_fp2 Hfe_d0_3)
        as Hfe_d0'.

      (* Build Fp6 for d1 *)
      pose proof (@CubicFieldExtensions.Fp6_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_beta bls12_xi_re bls12_xi_im bls12_Fp_rep fp6_prefix fp2_prefix
        (word.add a_result (word.of_Z fp6_felem_offset))
        (fw7 ++ fw8) (fw9 ++ fw10) (fw11 ++ fw12) m_d1_3
        Hlen_d1c0_fp2 Hlen_d1c1_fp2 Hlen_d1c2_fp2 Hfe_d1_3)
        as Hfe_d1'.

      (* Build Fp12 from d0 and d1 *)
      assert (Hlen_d0_fp6 : length ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) = Fp6_fsw).
      { rewrite !length_app, Hlen_fw1, Hlen_fw2, Hlen_fw3, Hlen_fw4, Hlen_fw5, Hlen_fw6.
        reflexivity. }
      assert (Hlen_d1_fp6 : length ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12)) = Fp6_fsw).
      { rewrite !length_app, Hlen_fw7, Hlen_fw8, Hlen_fw9, Hlen_fw10, Hlen_fw11, Hlen_fw12.
        reflexivity. }

      (* Build 2-way Fp6 sep *)
      destruct Hsplit_d0 as [Heq_d0' Hd_d0'].
      destruct Hsplit_d1 as [Heq_d1' Hd_d1'].
      set (m_fp12_j := map.putmany m_d0_3 m_d1_3).
      assert (Hsep_2fp6 : (FElem_Fp6 a_result ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) ⋆
        FElem_Fp6 (word.add a_result (word.of_Z fp6_felem_offset))
          ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))) m_fp12_j).
      { subst m_fp12_j. exists m_d0_3, m_d1_3.
        split; [split; [reflexivity |] |].
        { subst m_d0_rest.
          exact (proj1 (proj1 (map.disjoint_putmany_r _ _ _) Hd_d0')). }
        split; [exact Hfe_d0' | exact Hfe_d1']. }

      pose proof (@DodecicFieldExtensions.Fp12_raw_FElem_join _ _ _ _
        wordok mapok bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix
        a_result ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
        ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12)) m_fp12_j
        Hlen_d0_fp6 Hlen_d1_fp6 Hsep_2fp6)
        as Hfe_fp12_j.

      (* Rebuild full sep *)
      set (result_new := ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6)) ++
                          ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12))).
      eassert (Hsep_rejoined :
        (FElem_Fp12 a_result result_new ⋆
         (FElem_Fp12 a_base mul2_out ⋆
          (FElem_Fp12 a_tmp frob_out ⋆
           (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
            (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
             (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
              (Memory.anybytes a_h3 160 ⋆
               (FElem_Fp12 pf f ⋆
                (FElem_Fp12 pout old_out ⋆ Rr))))))))) m_fw).
      { subst m_fp12_j m_d0_rest.
        (* Goal: ... m_fw. m_fw is a set-definition for the anonymous memory.
           Heq_d0' : m_fw = putmany m_d0_3 (putmany m_d1_3 m_rest) *)
        rewrite Heq_d0'.
        exists (map.putmany m_d0_3 m_d1_3), m_rest.
        split; [split |].
        { rewrite map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_l. split.
          { exact (proj2 (proj1 (map.disjoint_putmany_r _ _ _) Hd_d0')). }
          { exact Hd_d1'. } }
        split; [exact Hfe_fp12_j | exact Hrest]. }

      (* === Handle remaining: h3 stores + set started + set i + while loop +
             fp12_copy(out, result) + 4 stack deallocs === *)

      (* Step 1: Convert anybytes a_h3 160 to array scalar (20 words) *)
      eassert (Hany_ext : (Memory.anybytes a_h3 160 ⋆ _) m_fw).
      { pose proof Hsep_rejoined as H'. ecancel_assumption. }
      destruct Hany_ext as [m_h3 [m_rest_h3 [[Heq_h3s Hd_h3s] [Hany_h3 Hrest_h3]]]].

      destruct (Array.anybytes_to_array_1 m_h3 a_h3 160 Hany_h3)
        as [bs_h3 [Harr_bs_h3 Hlen_bs_h3]].
      assert (Hlen160 : length bs_h3 = (20 * Z.to_nat (Memory.bytes_per_word 64))%nat)
        by (rewrite Hlen_bs_h3; reflexivity).
      pose proof (proj1 (Bignum.Bignum_of_bytes 20 a_h3 bs_h3 Hlen160 m_h3) Harr_bs_h3) as Hbn.
      unfold Bignum.Bignum in Hbn.
      set (h3ws := ArrayCasts.bs2ws (Z.to_nat (Memory.bytes_per_word 64)) bs_h3) in *.
      destruct Hbn as [m_e [m_a [Hsplit_e [[Hme_empty Hlen_h3ws] Harr_h3ws]]]].
      subst m_e. apply Properties.map.split_empty_l in Hsplit_e. subst m_a.

      (* Build sep with array scalar replacing anybytes *)
      assert (Hsep_h3arr :
        (array scalar (word.of_Z 8) a_h3 h3ws ⋆
         (FElem_Fp12 a_result result_new ⋆
          (FElem_Fp12 a_base mul2_out ⋆
           (FElem_Fp12 a_tmp frob_out ⋆
            (FElem_Fp2 p_gamma1_p2 gamma1_p2 ⋆
             (FElem_Fp2 p_gamma2_p2 gamma2_p2 ⋆
              (FElem_Fp2 p_w_frob_p2_c1 w_frob_p2_c1 ⋆
               (FElem_Fp12 pf f ⋆
                (FElem_Fp12 pout old_out ⋆ Rr))))))))) m_fw).
      { exists m_h3, m_rest_h3.
        exact (conj (conj Heq_h3s Hd_h3s) (conj Harr_h3ws Hrest_h3)). }

      clear Hsep_rejoined Hrest_h3 Harr_h3ws Hany_h3 Harr_bs_h3.
      clear Hlen_bs_h3 Hlen160 Heq_h3s Hd_h3s.

      (* === Step 2: h3 stores via bridge lemma === *)
      change BLS12_Pairing.h3_store_limbs with h3_store_cmd.
      eapply h3_stores_then_rest;
        [ exact Hlen_h3ws
        | subst l2; repeat (try (rewrite map.get_put_same; reflexivity);
            rewrite map.get_put_diff by congruence)
        | exact Hsep_h3arr
        | ].
      intros m_h3_new Hsep_h3_new.

      (* === Step 3: set started = 0; set i = 1280 === *)
      cbv [cmd_body]. fold @WeakestPrecondition.cmd.
      repeat straightline.

      (* === Step 4: while loop === *)
      eapply Loops.while_localsmap
        with (v0 := 1280%nat)
             (lt := Nat.lt)
             (invariant := final_exp_loop_inv a_result a_tmp a_base a_h3
                      pout pf p_gamma1_p2 p_gamma2_p2 p_w_frob_p2_c1
                      f gamma1_p2 gamma2_p2 w_frob_p2_c1 old_out Rr t'0).

      (* well_founded *)
      { exact lt_wf. }

      (* Initial invariant *)
      { unfold final_exp_loop_inv.
        split; [reflexivity |]. split; [lia |].
        exists result_new, frob_out, mul2_out, (word.of_Z 0).
        split; [| split; [exact Hbound_mul2 |]].
        2: { split; [ecancel_assumption |].
             repeat split; subst l4 l3 v0 v;
             repeat (try (rewrite map.get_put_same; reflexivity);
                     rewrite map.get_put_diff by congruence). }
        (* Fp12_bounded Fp12_tight result_new — from 12 from_word tight bounds *)
        subst result_new.
        change Fp12_bounded with
          (fun (b : @AbstractField.bounds _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep')
               (felem : list word) =>
            @AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep' b (d0_felem felem) /\
            @AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep' b (d1_felem felem));
          cbv beta.
        rewrite (@d0_felem_app _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix
          ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
          ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12)) Hlen_d0_fp6).
        rewrite (@d1_felem_app _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix
          ((fw1 ++ fw2) ++ (fw3 ++ fw4) ++ (fw5 ++ fw6))
          ((fw7 ++ fw8) ++ (fw9 ++ fw10) ++ (fw11 ++ fw12)) Hlen_d0_fp6).
        change (@AbstractField.bounded_by _ bls12_Fp6_params' _ _ _ _ bls12_Fp6_rep') with
          (fun (b : @AbstractField.bounds _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep')
               (felem : list word) =>
            Fp2_bounded b (c0_felem felem) /\
            Fp2_bounded b (c1_felem felem) /\
            Fp2_bounded b (c2_felem felem));
          cbv beta.
        rewrite (@c0_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
          (fw1++fw2) (fw3++fw4) (fw5++fw6) Hlen_d0c0_fp2).
        rewrite (@c1_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
          (fw1++fw2) (fw3++fw4) (fw5++fw6) Hlen_d0c0_fp2 Hlen_d0c1_fp2).
        rewrite (@c2_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
          (fw1++fw2) (fw3++fw4) (fw5++fw6) Hlen_d0c0_fp2 Hlen_d0c1_fp2).
        rewrite (@c0_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
          (fw7++fw8) (fw9++fw10) (fw11++fw12) Hlen_d1c0_fp2).
        rewrite (@c1_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
          (fw7++fw8) (fw9++fw10) (fw11++fw12) Hlen_d1c0_fp2 Hlen_d1c1_fp2).
        rewrite (@c2_felem_app _ _ _ _ bls12_pf_params bls12_beta bls12_Fp_rep fp2_prefix
          (fw7++fw8) (fw9++fw10) (fw11++fw12) Hlen_d1c0_fp2 Hlen_d1c1_fp2).
        change Fp2_bounded with
          (fun (b : @AbstractField.bounds _ _ _ _ _ _ bls12_Fp_rep)
               (ws : list word) =>
            Fp_bounded b (fst_felem ws) /\ Fp_bounded b (snd_felem ws));
          cbv beta.
        unfold fst_felem, snd_felem,
          QuadraticFieldExtensionsSpecs.fst_felem,
          QuadraticFieldExtensionsSpecs.snd_felem.
        rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw1).
        rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw1).
        rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw3).
        rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw3).
        rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw5).
        rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw5).
        rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw7).
        rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw7).
        rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw9).
        rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw9).
        rewrite !(QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_fw11).
        rewrite !(QuadraticFieldExtensions.skipn_app _ _ _ Hlen_fw11).
        split; [split; [split; [exact Hb_fw1 | exact Hb_fw2] |
          split; [split; [exact Hb_fw3 | exact Hb_fw4] |
            split; [exact Hb_fw5 | exact Hb_fw6]]] |
          split; [split; [exact Hb_fw7 | exact Hb_fw8] |
            split; [split; [exact Hb_fw9 | exact Hb_fw10] |
              split; [exact Hb_fw11 | exact Hb_fw12]]]]. }

      (* Loop body + exit *)
      { intros vi t_vi m_vi l_vi Hinv.
        unfold final_exp_loop_inv in Hinv.
        destruct Hinv as [Ht_vi [Hvi_le (result_vi & tmp_vi & base_vi & started_vi &
          Hbr & Hbb & Hsep_vi &
          Hget_i & Hget_started & Hget_result & Hget_tmp &
          Hget_base & Hget_h3i & Hget_out & Hget_f)]].
        subst t_vi.

        (* Evaluate the condition: expr.var "i" *)
        eexists. cbv [Markers.split]. split.
        { cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
               WeakestPrecondition.get].
          eexists. split; [exact Hget_i | reflexivity]. }

        split.
        { (* TRUE branch: i <> 0, loop body *)
          intro Hne_zero.
          unfold BLS12_Pairing.h3_loop_body, BLS12_Pairing.cmd_seq_list.

          (* Helper lemma: word subtraction for nat counter *)
          assert (Hvi_pos : (0 < vi)%nat).
          { destruct vi; [exfalso; apply Hne_zero; reflexivity | lia]. }
          assert (word_nat_sub1 : @word.sub 64 word (word.of_Z (Z.of_nat vi)) (word.of_Z 1) =
            word.of_Z (Z.of_nat (vi - 1))).
          { rewrite <- word.ring_morph_sub. f_equal. zify. lia. }

          (* Helper: resolve map.get through put layers *)
          Local Ltac resolve_get :=
            repeat (try (rewrite map.get_put_same; reflexivity);
                    rewrite map.get_put_diff by discriminate).
          Local Ltac solve_cond_expr :=
            cbv [WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get];
            eexists; split; [resolve_get; eassumption |]; exact eq_refl.
          (* Solve map.get conjunction for invariant locals.
             Uses plain discriminate (not cbv;discriminate which is slow). *)
          (* Fast map.get resolution: use get_put_dec + cbn on String.eqb.
             This avoids slow discriminate on string terms. *)
          Local Ltac solve_one_mapget :=
            repeat rewrite map.get_put_dec;
            cbn [String.eqb Ascii.eqb Bool.eqb];
            first [ exact eq_refl
                  | assumption
                  | f_equal; assumption ].
          Local Ltac solve_loop_mapgets :=
            split; [solve_one_mapget |];
            split; [solve_one_mapget |];
            split; [solve_one_mapget |];
            split; [solve_one_mapget |];
            split; [solve_one_mapget |];
            split; [solve_one_mapget |];
            split; [solve_one_mapget |];
            solve_one_mapget.

          (* === Tactic: wp_cond === *)
          (* Handles cmd.cond: unfold, evaluate condition, split branches *)
          Local Ltac wp_cond :=
            unfold1_cmd_goal; cbv beta match delta [cmd_body];
            letexists; split; [solve_cond_expr |]; split.

          (* === Tactic: wp_call === *)
          (* Resolves dexprs for 2- or 3-argument function calls *)
          Local Ltac solve_dexprs :=
            cbv [dexprs list_map list_map_body
                 WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get];
            repeat (eexists; split; [resolve_get; eassumption |]);
            exact eq_refl.
          Local Ltac wp_call :=
            unfold1_cmd_goal; cbv beta match delta [cmd_body];
            letexists; split; [solve_dexprs |].

          (* === Tactic: word_shift_to_mul === *)
          (* Proves: word.slu (word.sru x (of_Z s)) (of_Z t) = of_Z (2^t * Z.of_nat n)
             where n = Z.to_nat (unsigned (sru x (of_Z s))). *)
          Local Ltac word_shift_to_mul :=
            (* Caller must subst set-definitions before calling *)
            apply word.unsigned_inj;
            rewrite word.unsigned_slu_shamtZ by (lia);
            rewrite Z.shiftl_mul_pow2 by lia;
            rewrite word.unsigned_of_Z;
            f_equal;
            match goal with |- context [Z.of_nat (Z.to_nat (word.unsigned ?w))] =>
              rewrite (Z2Nat.id (word.unsigned w))
                by (pose proof (word.unsigned_range w); lia)
            end;
            ring.

          (* === Step 1: i = i - 1 === *)
          repeat straightline.
          eexists; refine (conj _ _).
          { cbv [DEXPR dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get].
            eexists; split; [exact Hget_i |].
            cbv [literal]. exact eq_refl. }
          cbv [Semantics.interp_binop]. unfold dlet.dlet; cbv beta.
          set (i_new := word.sub (word.of_Z (Z.of_nat vi)) (word.of_Z 1)) in *.

          (* === Step 2: word = load(h3 + (i >> 6) << 3) === *)
          straightline. straightline.
          set (load_addr := word.add a_h3
            (word.slu (word.sru i_new (word.of_Z 6)) (word.of_Z 3))).
          set (n := Z.to_nat (word.unsigned (word.sru i_new (word.of_Z 6)))).
          set (loaded_word := nth n h3_limbs (word.of_Z 0)).
          assert (Hn_bound : (n < length h3_limbs)%nat).
          { subst n. cbv [h3_limbs]. simpl length.
            (* n = Z.to_nat (unsigned (sru i_new 6))
               i_new = vi - 1,  0 < vi <= 1280
               unsigned i_new = vi - 1  (in range, no wrap)
               sru i_new 6 = (vi-1) / 64
               n = Z.to_nat ((vi-1) / 64)
               Need: (vi-1)/64 < 20, i.e. vi-1 < 1280, i.e. vi <= 1280 ✓ *)
            pose proof (word.unsigned_range (word.sru i_new (word.of_Z 6))).
            enough (word.unsigned (word.sru i_new (word.of_Z 6)) < 20)
              by (change 20%nat with (Z.to_nat 20); lia).
            rewrite word.unsigned_sru_shamtZ by lia.
            rewrite Z.shiftr_div_pow2 by lia. change (2^6) with 64.
            subst i_new. rewrite word_nat_sub1.
            rewrite word.unsigned_of_Z.
            unfold word.wrap. rewrite Z.mod_small by lia.
            apply Z.div_lt_upper_bound; lia. }
          assert (Hload : Memory.load access_size.word m_vi load_addr =
            Some loaded_word).
          { subst loaded_word load_addr.
            eapply h3_array_load; [ecancel_assumption | exact Hn_bound]. }
          eexists; refine (conj _ _).
          { cbv [DEXPR dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get WeakestPrecondition.load].
            eexists; split; [resolve_get; exact Hget_h3i |].
            eexists; split; [rewrite map.get_put_same; exact eq_refl |].
            cbv [literal Semantics.interp_binop]. unfold dlet.dlet; cbv beta.
            subst load_addr.
            eexists; split; [exact Hload | exact eq_refl]. }
          unfold dlet.dlet; cbv beta.

          (* === Step 3: bit = (word >> (i & 63)) & 1 === *)
          eexists; refine (conj _ _).
          { cbv [DEXPR dexpr WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get].
            eexists; split; [rewrite map.get_put_same; exact eq_refl |].
            eexists; split; [rewrite map.get_put_diff by discriminate;
                             rewrite map.get_put_same; exact eq_refl |].
            cbv [literal Semantics.interp_binop]. exact eq_refl. }
          unfold dlet.dlet; cbv beta.
          set (bit_val := word.and (word.sru loaded_word
            (word.and i_new (word.of_Z 63))) (word.of_Z 1)) in *.

          (* === Step 4: if started { sqr(result, result) } === *)
          wp_cond.

          { (* started != 0: do sqr then handle bit *)
            intro Hstarted_ne.
            wp_call.
            eapply Semantics.weaken_call.
            { eapply HFp12sqr.
              split; [| split]; [| | ecancel_assumption].
              - exact Hbr.
              - eexists; ecancel_assumption. }
            cbv beta.
            intros ? ? ? [Hrets_sqr [Htr_sqr [sqr_out [Hfeval_sqr [Hb_sqr Hs_sqr]]]]].
            subst.
            eexists; split; [cbv [map.putmany_of_list_zip]; exact eq_refl |].

            (* if bit { ... } *)
            unfold1_cmd_goal; cbv beta match delta [cmd_body].
            letexists; split; [solve_cond_expr |]; split.

            { (* bit != 0, started != 0: inner if started *)
              intro Hbit_ne.
              unfold1_cmd_goal; cbv beta match delta [cmd_body].
              letexists; split; [solve_cond_expr |]; split.

              { (* started != 0: mul(result, result, base) *)
                intro Hstarted_ne2.
                wp_call.
                eapply Semantics.weaken_call.
                { eapply HFp12mul.
                  split; [| split; [| split; [| split]]].
                  - exact Hb_sqr.
                  - exact Hbb.
                  - eexists; ecancel_assumption.
                  - eexists; ecancel_assumption.
                  - ecancel_assumption. }
                cbv beta.
                intros ? ? ? [? [? [mul_out [? [Hb_mul Hs_mul]]]]]. subst.
                eexists; split; [cbv [map.putmany_of_list_zip]; exact eq_refl |].
                exists (Nat.sub vi 1). split; [| lia].
                unfold final_exp_loop_inv. split; [exact eq_refl |]. split; [lia |].
                exists mul_out, tmp_vi, base_vi, started_vi.
                split; [exact Hb_mul |]. split; [exact Hbb |].
                split; [exact Hs_mul |]. solve_loop_mapgets. }

              { (* !started contradiction *)
                intro Hstarted_eq2. subst v1.
                exfalso. exact (Hstarted_ne Hstarted_eq2). } }

            { (* bit = 0, started != 0: just sqr, no mul *)
              intro Hbit_eq.
              repeat straightline.
              exists (Nat.sub vi 1). split; [| lia].
              unfold final_exp_loop_inv. split; [exact eq_refl |]. split; [lia |].
              exists sqr_out, tmp_vi, base_vi, started_vi.
              split; [exact Hb_sqr |]. split; [exact Hbb |].
              split; [exact Hs_sqr |].
              solve_loop_mapgets. } }

          { (* started = 0: skip sqr, handle bit *)
            intro Hstarted_eq.
            repeat straightline.

            (* if bit { ... } *)
            unfold1_cmd_goal; cbv beta match delta [cmd_body].
            letexists; split; [solve_cond_expr |]; split.

            { (* bit != 0, started = 0 *)
              intro Hbit_ne.
              unfold1_cmd_goal; cbv beta match delta [cmd_body].
              letexists; split; [solve_cond_expr |]; split.

              { (* started != 0 contradiction *)
                intro Hstarted_ne. subst v1.
                exfalso. exact (Hstarted_ne Hstarted_eq). }

              { (* !started: copy(result, base); set started=1 *)
                intro Hstarted_eq2.
                (* Unwrap cmd.seq for copy; set *)
                wp_call.
                eapply Semantics.weaken_call.
                { eapply HFp12copy.
                  split; [| ecancel_assumption]. ecancel_assumption. }
                cbv beta. intros ? ? ? [Htr_copy Hsep_copy].
                subst.
                eexists; split; [cbv [map.putmany_of_list_zip]; exact eq_refl |].
                (* set started = 1 *)
                repeat straightline.
                exists (Nat.sub vi 1). split; [| lia].
                unfold final_exp_loop_inv. split; [exact eq_refl |]. split; [lia |].
                exists base_vi, tmp_vi, base_vi, started.
                split; [exact Hbb |]. split; [exact Hbb |].
                split; [exact H10 |].
                subst l. solve_loop_mapgets. } }

            { (* bit = 0, started = 0: skip *)
              intro Hbit_eq.
              repeat straightline.
              exists (Nat.sub vi 1). split; [| lia].
              unfold final_exp_loop_inv. split; [exact eq_refl |]. split; [lia |].
              exists result_vi, tmp_vi, base_vi, started_vi.
              split; [exact Hbr |]. split; [exact Hbb |].
              split; [exact Hsep_vi |].
              solve_loop_mapgets. } } }

        { (* FALSE branch: i = 0, exit → post-loop *)
          intro Heq_zero.

          (* fp12_copy(out, result) *)
          exists [pout; a_result].
          split.
          { cbv [dexprs list_map list_map_body
                 WeakestPrecondition.expr WeakestPrecondition.expr_body
                 WeakestPrecondition.get].
            rewrite Hget_out. rewrite Hget_result.
            eexists. split; [exact eq_refl |].
            eexists. split; [exact eq_refl |].
            exact eq_refl. }
          eapply Semantics.weaken_call.
          1: { eapply HFp12copy.
               split; ecancel_assumption. }
          intros t_cp m_cp ? [Hrets_cp Hsep_cp].
          subst.
          destruct Hsep_cp as [Htr_cp Hsep_cp'].
          symmetry in Htr_cp. subst t_cp.

          exists l_vi.
          split. { cbv [map.putmany_of_list_zip]. exact eq_refl. }

          (* === 4 stack deallocs + final postcondition === *)

          (* Dealloc h3: array scalar 20 words → anybytes 160 *)
          eassert (Hh3_sep : (_ ⋆ array scalar (word.of_Z 8) a_h3 h3_limbs) m_cp).
          { pose proof Hsep_cp' as H'. ecancel_assumption. }
          destruct Hh3_sep as [m_rest_h3p [m_h3p [[Heq_h3p Hd_h3p] [Hrest_h3p Hfh3p]]]].
          exists m_rest_h3p, m_h3p.
          split. { (* array scalar → Bignum → array ptsto → anybytes *)
            assert (Hbn : Bignum.Bignum 20 a_h3 h3_limbs m_h3p).
            { unfold Bignum.Bignum. exists map.empty, m_h3p.
              split. { split.
                { apply (proj2 (Properties.map.split_empty_l m_h3p m_h3p)). reflexivity. }
                { apply Properties.map.disjoint_empty_l. } }
              split. { split; reflexivity. }
              { exact Hfh3p. } }
            pose proof (proj1 (Bignum.Bignum_to_bytes 20 a_h3 h3_limbs m_h3p) Hbn) as Hbn2.
            destruct Hbn2 as [m_e2 [m_a2 [Hspl2 [[He2 Hlen_ws2bs] Harr_ptsto]]]].
            subst m_e2. apply Properties.map.split_empty_l in Hspl2. subst m_a2.
            apply (Array.array_1_to_anybytes) in Harr_ptsto.
            change (Z.of_nat (Datatypes.length
              (ws2bs (Z.to_nat (Memory.bytes_per_word 64)) h3_limbs))) with 160
              in Harr_ptsto.
            exact Harr_ptsto. }
          split. { split; [exact Heq_h3p | exact Hd_h3p]. }

          (* Dealloc base *)
          eassert (Hbase_sep : (_ ⋆ FElem_Fp12 a_base base_vi) m_rest_h3p).
          { pose proof Hrest_h3p as H'. ecancel_assumption. }
          destruct Hbase_sep as [m_rest_base [m_base_d [[Heq_bd Hd_bd] [Hrest_base Hfbase]]]].
          exists m_rest_base, m_base_d.
          split. { exact (AbstractField.FElem_to_bytes a_base base_vi m_base_d Hfbase). }
          split. { split; [exact Heq_bd | exact Hd_bd]. }

          (* Dealloc tmp *)
          eassert (Htmp_sep : (_ ⋆ FElem_Fp12 a_tmp tmp_vi) m_rest_base).
          { pose proof Hrest_base as H'. ecancel_assumption. }
          destruct Htmp_sep as [m_rest_tmp [m_tmp_d [[Heq_td Hd_td] [Hrest_tmp Hftmp]]]].
          exists m_rest_tmp, m_tmp_d.
          split. { exact (AbstractField.FElem_to_bytes a_tmp tmp_vi m_tmp_d Hftmp). }
          split. { split; [exact Heq_td | exact Hd_td]. }

          (* Dealloc result *)
          eassert (Hres_sep : (_ ⋆ FElem_Fp12 a_result result_vi) m_rest_tmp).
          { pose proof Hrest_tmp as H'. ecancel_assumption. }
          destruct Hres_sep as [m_rest_res [m_res_d [[Heq_rd Hd_rd] [Hrest_res Hfres]]]].
          exists m_rest_res, m_res_d.
          split. { exact (AbstractField.FElem_to_bytes a_result result_vi m_res_d Hfres). }
          split. { split; [exact Heq_rd | exact Hd_rd]. }

          (* Final postcondition *)
          cbv [list_map list_map_body].
          split. { exact eq_refl. }
          split. { exact eq_refl. }
          exists result_vi.
          split. { pose proof (@DodecicFieldExtensionsSpecs.Fp12_field_representation_ok
                       _ _ _ _ bls12_pf_params bls12_Fp_rep bls12_Fp_rep_ok bls12_beta
                       bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix) as Hfp12_ok.
                   exact (@AbstractField.relax_bounds _ _ _ _ _ _ _ Hfp12_ok _ Hbr). }
          ecancel_assumption. } }
    Qed.

End BLS12_FinalExp.

