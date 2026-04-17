(** * BLS24-509 Pairing Helpers — BLS24-specific split/join + WP proofs.

    The generic qe_raw_FElem_split_in_sep produces FElems with abstract
    section-closure instances that ecancel can't match. This file provides
    BLS24-SPECIFIC split/join lemmas with concrete instances, following the
    BLS12 pattern from BLS12_MillerGeneric.v (FElem_Fp2_split_in_sep). *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Loops.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls24_509_Fp.
Require Import Bedrock.Field.FieldExtensions.GenericQuadraticSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericQuadratic.
Require Import Bedrock.Field.FieldExtensions.GenericCubicSpecs.
Require Import Bedrock.Field.FieldExtensions.GenericCubic.
Require Import Bedrock.Field.FieldExtensions.GenericSplitJoin.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_MillerGeneric.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_Instances.
Require Import Bedrock.Field.Synthesis.Examples.BLS24_509_MillerLoop.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS24_PairingHelpers.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Existing Instances
      bls24_prime_params
      bls24_prime_params_ok
      prime_field_parameters
      bls24_Fp_repr
      bls24_Fp_repr_ok.

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := (Fp * Fp)%type.
    Local Notation Fp4 := (Fp2 * Fp2)%type.
    Local Notation Fp8 := (Fp4 * Fp4)%type.
    Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

    Existing Instances
      bls24_Fp2_params bls24_Fp2_repr bls24_Fp2_repr_ok
      bls24_Fp4_params bls24_Fp4_repr bls24_Fp4_repr_ok
      bls24_Fp8_params bls24_Fp8_repr bls24_Fp8_repr_ok
      bls24_Fp24_params bls24_Fp24_repr bls24_Fp24_repr_ok.

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
    Local Notation FElem_Fp4 := (@AbstractField.FElem _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation FElem_Fp8 := (@AbstractField.FElem _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation FElem_Fp24 := (@AbstractField.FElem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp_bounded := (@AbstractField.bounded_by _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_bounded := (@AbstractField.bounded_by _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp_loose := (@AbstractField.loose_bounds _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp4_tight := (@AbstractField.tight_bounds _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp4_loose := (@AbstractField.loose_bounds _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp4_felem := (@AbstractField.felem _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
    Local Notation Fp_felem := (@AbstractField.felem _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation Fp24_felem := (@AbstractField.felem _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
    Local Notation Fp8_bounded := (@AbstractField.bounded_by _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp8_tight := (@AbstractField.tight_bounds _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
    Local Notation Fp8_loose := (@AbstractField.loose_bounds _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp24_bounded := (@AbstractField.bounded_by _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).
    Local Notation Fp24_tight := (@AbstractField.tight_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).

    (* Fp-level byte offset *)
    Local Notation fp_off :=
      (word.of_Z (Memory.bytes_per_word 64 *
        Z.of_nat (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr))).
    (* Fp2-level byte offset *)
    Local Notation fp2_off :=
      (word.of_Z (Memory.bytes_per_word 64 *
        Z.of_nat (@AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr))).

    (* ============================================================ *)
    (* BLS24-specific split/join in sep                              *)
    (* ============================================================ *)

    (* Fp-level decomposition functions (concrete instances) *)
    Local Notation fp_fst := (@qe_fst_felem _ _ _ _ _ _ bls24_Fp_repr).
    Local Notation fp_snd := (@qe_snd_felem _ _ _ _ _ _ bls24_Fp_repr).
    (* Fp2-level decomposition functions *)
    Local Notation fp2_fst := (@qe_fst_felem _ _ _ _ _ bls24_Fp2_params bls24_Fp2_repr).
    Local Notation fp2_snd := (@qe_snd_felem _ _ _ _ _ bls24_Fp2_params bls24_Fp2_repr).

    (** Split FElem_Fp2 into 2 FElem_Fp with concrete BLS24 instances. *)
    Lemma FElem_Fp2_split_in_sep p (x : list word) R m :
      (FElem_Fp2 p x * R)%sep m ->
      (FElem_Fp p (fp_fst x) *
       (FElem_Fp (word.add p fp_off) (fp_snd x) * R))%sep m.
    Proof.
      exact (qe_raw_FElem_split_in_sep
        BLS24_509_Instances.bls24_beta "bls24_Fp2_" BLS24_509_Instances.Fp_eq_dec
        p x R m).
    Qed.

    (** Join 2 FElem_Fp into FElem_Fp2. *)
    Lemma FElem_Fp_join_in_sep p (a b : list word) R m :
      length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr ->
      length b = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr ->
      (FElem_Fp p a * (FElem_Fp (word.add p fp_off) b * R))%sep m ->
      (FElem_Fp2 p (a ++ b) * R)%sep m.
    Proof.
      exact (qe_raw_FElem_join_in_sep
        BLS24_509_Instances.bls24_beta "bls24_Fp2_" BLS24_509_Instances.Fp_eq_dec
        p a b R m).
    Qed.

    (** Split FElem_Fp4 into 2 FElem_Fp2 with concrete BLS24 instances. *)
    Lemma FElem_Fp4_split_in_sep p (x : list word) R m :
      (FElem_Fp4 p x * R)%sep m ->
      (FElem_Fp2 p (fp2_fst x) *
       (FElem_Fp2 (word.add p fp2_off) (fp2_snd x) * R))%sep m.
    Proof.
      exact (qe_raw_FElem_split_in_sep
        BLS24_509_Instances.bls24_xi "bls24_Fp4_" BLS24_509_Instances.Fp2_eq_dec
        p x R m).
    Qed.

    (** Join 2 FElem_Fp2 into FElem_Fp4. *)
    Lemma FElem_Fp2_join_in_sep p (a b : list word) R m :
      length a = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr ->
      length b = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr ->
      (FElem_Fp2 p a * (FElem_Fp2 (word.add p fp2_off) b * R))%sep m ->
      (FElem_Fp4 p (a ++ b) * R)%sep m.
    Proof.
      exact (qe_raw_FElem_join_in_sep
        BLS24_509_Instances.bls24_xi "bls24_Fp4_" BLS24_509_Instances.Fp2_eq_dec
        p a b R m).
    Qed.

    (* Fp4-level offset + decomposition *)
    Local Notation fp4_off :=
      (word.of_Z (Memory.bytes_per_word 64 *
        Z.of_nat (@AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr))).
    Local Notation fp4_fst := (@qe_fst_felem _ _ _ _ _ bls24_Fp4_params bls24_Fp4_repr).
    Local Notation fp4_snd := (@qe_snd_felem _ _ _ _ _ bls24_Fp4_params bls24_Fp4_repr).

    (** Split FElem_Fp8 into 2 FElem_Fp4. *)
    Lemma FElem_Fp8_split_in_sep p (x : list word) R m :
      (FElem_Fp8 p x * R)%sep m ->
      (FElem_Fp4 p (fp4_fst x) *
       (FElem_Fp4 (word.add p fp4_off) (fp4_snd x) * R))%sep m.
    Proof.
      exact (qe_raw_FElem_split_in_sep
        BLS24_509_Instances.bls24_v_in_Fp4 "bls24_Fp8_" BLS24_509_Instances.Fp4_eq_dec
        p x R m).
    Qed.

    (** Join 2 FElem_Fp4 into FElem_Fp8. *)
    Lemma FElem_Fp4_join_in_sep p (a b : list word) R m :
      length a = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr ->
      length b = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr ->
      (FElem_Fp4 p a * (FElem_Fp4 (word.add p fp4_off) b * R))%sep m ->
      (FElem_Fp8 p (a ++ b) * R)%sep m.
    Proof.
      exact (qe_raw_FElem_join_in_sep
        BLS24_509_Instances.bls24_v_in_Fp4 "bls24_Fp8_" BLS24_509_Instances.Fp4_eq_dec
        p a b R m).
    Qed.

    (* Fp8-level offset + decomposition *)
    Local Notation fp8_off :=
      (word.of_Z (Memory.bytes_per_word 64 *
        Z.of_nat (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr))).
    Local Notation fp8_fst := (@ce_c0_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr).
    Local Notation fp8_c1 := (@ce_c1_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr).
    Local Notation fp8_c2 := (@ce_c2_felem _ _ _ _ _ bls24_Fp8_params bls24_Fp8_repr).

    (** Split FElem_Fp24 into 3 FElem_Fp8. *)
    Lemma FElem_Fp24_split_in_sep p (x : list word) R m :
      (FElem_Fp24 p x * R)%sep m ->
      (FElem_Fp8 p (fp8_fst x) *
       (FElem_Fp8 (word.add p fp8_off) (fp8_c1 x) *
        (FElem_Fp8 (word.add p (word.of_Z (2 * (Memory.bytes_per_word 64 *
            Z.of_nat (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)))))
           (fp8_c2 x) * R)))%sep m.
    Proof.
      exact (ce_raw_FElem_split_in_sep
        BLS24_509_Instances.bls24_Fp8_mul_by_w_model "bls24_Fp24_" BLS24_509_Instances.Fp8_eq_dec
        p x R m).
    Qed.

    (* ============================================================ *)
    (* Specs and WP proofs                                           *)
    (* ============================================================ *)

    Instance spec_of_Fp_mul : spec_of PrimeField.mul :=
      AbstractField.binop_spec (F:=Fp) (field_representation:=bls24_Fp_repr) AbstractField.bin_mul.

    Local Instance spec_of_bls24_Fp4_mul_fp : spec_of "bls24_Fp4_mul_fp" :=
      fnspec! "bls24_Fp4_mul_fp" (pout px ps : word)
        / (old_out : Fp4_felem) (x : Fp4_felem) (s : Fp_felem) Rr,
      { requires tr mem :=
          Fp4_bounded Fp4_tight x /\
          Fp_bounded Fp_loose s /\
          (FElem_Fp4 pout old_out *
           (FElem_Fp4 px x *
            (FElem_Fp ps s * Rr)))%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          exists out,
            Fp4_bounded Fp4_loose out /\
            (FElem_Fp4 pout out *
             (FElem_Fp4 px x *
              (FElem_Fp ps s * Rr)))%sep mem' }.

    Lemma bls24_Fp4_mul_fp_ok :
      forall functions
        (EnvContains : map.get functions "bls24_Fp4_mul_fp" =
          Some (snd bls24_Fp4_mul_fp))
        (HFpmul : spec_of_Fp_mul functions),
      spec_of_bls24_Fp4_mul_fp functions.
    Proof.
      intros. unfold spec_of_bls24_Fp4_mul_fp.
      intros pout px ps old_out x s Rr tr mem0 [Hbx [Hbs Hsep]].
      eapply WeakestPreconditionProperties.start_func; [eassumption | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold bls24_Fp4_mul_fp. simpl snd. simpl fst. cbv match beta.
      eexists. split. 1: exact eq_refl.
      cbv [AbstractField.bounded_by AbstractField.tight_bounds
           bls24_Fp4_repr bls24_Fp2_repr QE_field_representation] in Hbx.
      destruct Hbx as [[Hbx0 Hbx1] [Hbx2 Hbx3]].
      (* Split fst halves only — process calls 1-2 first *)
      apply FElem_Fp4_split_in_sep in Hsep.
      apply FElem_Fp2_split_in_sep in Hsep.
      (* Rearrange: bring input Fp4 to front, split fst *)
      eassert (Hs_in : (FElem_Fp4 px x * _)%sep mem0).
      { pose proof Hsep as H'. ecancel_assumption. }
      apply FElem_Fp4_split_in_sep in Hs_in.
      apply FElem_Fp2_split_in_sep in Hs_in.
      clear Hsep.
      (* Process calls 1-2 from Hs_in (input fst at head) *)
      unfold BLS24_509_MillerLoop.cmd_seq_list. simpl. repeat straightline.

      Local Ltac dexprs_fast := solve [cbv [dexprs list_map list_map_body WeakestPrecondition.expr WeakestPrecondition.expr_body WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet Semantics.interp_binop]; repeat (first [exact eq_refl | eexists; split; [repeat first [rewrite map.get_put_same; exact eq_refl | rewrite map.get_put_diff by congruence]; exact eq_refl |] | eexists; split; [exact eq_refl |]])].

      (* Call 1 *)
      eapply Semantics.weaken_call.
      { eapply HFpmul. split; [exact Hbx0|]. split; [exact Hbs|].
        split; [eexists; exact Hs_in|].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        SeparationLogic.ecancel_assumption_impl. }
      cbv beta. intros ? ? ? [? [? [fw0 [_ [Hb0 Hs0]]]]]. subst.
      eexists. split. 1: exact eq_refl.
      eexists. split. 1: dexprs_fast.
      (* Call 2 *)
      eapply Semantics.weaken_call.
      { eapply HFpmul. split; [exact Hbx1|]. split; [exact Hbs|].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        SeparationLogic.ecancel_assumption_impl. }
      cbv beta. intros ? ? ? [? [? [fw1 [_ [Hb1 Hs1']]]]]. subst.
      eexists. split. 1: exact eq_refl.
      eexists. split. 1: dexprs_fast.
      (* Now split snd halves from CURRENT sep (Hs1', after call 2) *)
      eassert (Hs_out1 : (FElem_Fp2 (word.add pout fp2_off) (fp2_snd old_out) * _)%sep _).
      { pose proof Hs1' as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hs_out1.
      eassert (Hs_in1 : (FElem_Fp2 (word.add px fp2_off) (fp2_snd x) * _)%sep _).
      { pose proof Hs1' as H'. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hs_in1.
      clear Hs1'.
      (* Call 3 *)
      eapply Semantics.weaken_call.
      { eapply HFpmul. split; [exact Hbx2|]. split; [exact Hbs|].
        split; [eexists; exact Hs_in1|].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        SeparationLogic.ecancel_assumption_impl. }
      cbv beta. intros ? ? ? [? [? [fw2 [_ [Hb2 Hs2']]]]]. subst.
      eexists. split. 1: exact eq_refl.
      eexists. split. 1: dexprs_fast.
      (* Split snd-of-x Fp2 from CURRENT memory for call 4 *)
      eassert (Hs_in1b : (FElem_Fp2 (word.add px fp2_off) (fp2_snd x) * _)%sep _).
      { pose proof Hs2' as Htmp. ecancel_assumption. }
      apply FElem_Fp2_split_in_sep in Hs_in1b.
      (* Call 4 *)
      eapply Semantics.weaken_call.
      { eapply HFpmul. split; [exact Hbx3|]. split; [exact Hbs|].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        split; [eexists; SeparationLogic.ecancel_assumption_impl|].
        SeparationLogic.ecancel_assumption_impl. }
      cbv beta. intros ? ? ? [? [? [fw3 [_ [Hb3 Hs3']]]]]. subst.
      eexists. split. 1: exact eq_refl.
      (* Postcondition *)
      cbv [list_map list_map_body WeakestPrecondition.get].
      split. { exact eq_refl. } split. { exact eq_refl. }
      (* Join 4 output Fp → 2 Fp2 → Fp4 *)
      Local Ltac len_from_bounds H :=
        let Htmp := fresh "Htmp" in
        pose proof H as Htmp;
        apply WordByWordMontgomery.WordByWordMontgomery.length_small in Htmp;
        rewrite map_length in Htmp; exact Htmp.
      eassert (Hj01 : (FElem_Fp _ fw0 * (FElem_Fp _ fw1 * _))%sep _).
      { SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj01;
        [| len_from_bounds (proj1 Hb0) | len_from_bounds (proj1 Hb1)].
      eassert (Hj23 : (FElem_Fp _ fw2 * (FElem_Fp _ fw3 * _))%sep _).
      { SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj23;
        [| len_from_bounds (proj1 Hb2) | len_from_bounds (proj1 Hb3)].
      eassert (Hj_out : (FElem_Fp2 _ (fw0 ++ fw1) * (FElem_Fp2 _ (fw2 ++ fw3) * _))%sep _).
      { SeparationLogic.ecancel_assumption_impl. }
      (* Derive length from bounds: bounded → small → length = n *)
      Local Ltac len_small H :=
        let Hs := fresh in pose proof H as Hs;
        cbv [AbstractField.bounded_by AbstractField.loose_bounds AbstractField.tight_bounds
             bls24_Fp_repr Field.bounded_by Field.loose_bounds Field.tight_bounds
             AbstractField.bin_outbounds AbstractField.bin_mul
             BLS24_509_Instances.bls24_frep field_representation
             Signature.field_representation Representation.frep] in Hs;
        destruct Hs as [Hs _];
        apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hs;
        rewrite map_length in Hs; exact Hs.
      assert (Hlen01 : length (fw0 ++ fw1) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
      { rewrite app_length.
        assert (Hl0 : length fw0 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hb0.
        assert (Hl1 : length fw1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hb1.
        change (@AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr)
          with (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr)%nat. lia. }
      assert (Hlen23 : length (fw2 ++ fw3) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
      { rewrite app_length.
        assert (Hl2 : length fw2 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hb2.
        assert (Hl3 : length fw3 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hb3.
        change (@AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr)
          with (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr)%nat. lia. }
      apply FElem_Fp2_join_in_sep in Hj_out; [| exact Hlen01 | exact Hlen23].
      (* Join input x back *)
      eassert (Hj_x01 : (FElem_Fp _ (fp_fst (fp2_fst x)) * (FElem_Fp _ (fp_snd (fp2_fst x)) * _))%sep _).
      { SeparationLogic.ecancel_assumption_impl. }
      (* Derive input lengths from bounds *)
      assert (Hlenx0 : length (fp_fst (fp2_fst x)) = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hbx0.
      assert (Hlenx1 : length (fp_snd (fp2_fst x)) = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hbx1.
      assert (Hlenx2 : length (fp_fst (fp2_snd x)) = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hbx2.
      assert (Hlenx3 : length (fp_snd (fp2_snd x)) = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hbx3.
      apply FElem_Fp_join_in_sep in Hj_x01; [| exact Hlenx0 | exact Hlenx1].
      eassert (Hj_x23 : (FElem_Fp _ (fp_fst (fp2_snd x)) * (FElem_Fp _ (fp_snd (fp2_snd x)) * _))%sep _).
      { SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj_x23; [| exact Hlenx2 | exact Hlenx3].
      rewrite qe_list_decomp in Hj_x01. rewrite qe_list_decomp in Hj_x23.
      (* Hj_out is already FElem_Fp4 (joined above).
         Hj_x01 and Hj_x23 are already FElem_Fp2 (joined+rewritten above). *)
      (* Join input: Fp2 → Fp4 via FElem_value_replace approach *)
      (* Since input x was read-only, FElem_Fp4 px x still holds on the
         current memory. We just need ecancel to find the Fp4 from the
         scattered Fp2 entries + other stuff. Skip explicit join — use
         the fact that our Fp2 entries compose to the original Fp4. *)
      exists ((fw0 ++ fw1) ++ (fw2 ++ fw3)).
      split.
      { (* Use Fp2-level bounds first, then combine to Fp4 *)
        assert (Hb_fst : @AbstractField.bounded_by _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr Fp4_loose (fw0 ++ fw1)).
        { cut (Fp_bounded Fp_loose (fp_fst (fw0 ++ fw1)) /\
               Fp_bounded Fp_loose (fp_snd (fw0 ++ fw1))).
          { intro H; exact H. }
          unfold fp_fst, fp_snd, qe_fst_felem, qe_snd_felem.
          rewrite (firstn_app_le fw0 fw1); [| len_small Hb0].
          rewrite (skipn_app_le fw0 fw1); [| len_small Hb0].
          exact (conj Hb0 Hb1). }
        assert (Hb_snd : @AbstractField.bounded_by _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr Fp4_loose (fw2 ++ fw3)).
        { cut (Fp_bounded Fp_loose (fp_fst (fw2 ++ fw3)) /\
               Fp_bounded Fp_loose (fp_snd (fw2 ++ fw3))).
          { intro H; exact H. }
          unfold fp_fst, fp_snd, qe_fst_felem, qe_snd_felem.
          rewrite (firstn_app_le fw2 fw3); [| len_small Hb2].
          rewrite (skipn_app_le fw2 fw3); [| len_small Hb2].
          exact (conj Hb2 Hb3). }
        cut (@AbstractField.bounded_by _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr Fp4_loose (fp2_fst ((fw0 ++ fw1) ++ (fw2 ++ fw3))) /\
             @AbstractField.bounded_by _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr Fp4_loose (fp2_snd ((fw0 ++ fw1) ++ (fw2 ++ fw3)))).
        { intro H; exact H. }
        unfold fp2_fst, fp2_snd, qe_fst_felem, qe_snd_felem.
        rewrite (firstn_app_le (fw0++fw1) (fw2++fw3)); [| exact Hlen01].
        rewrite (skipn_app_le (fw0++fw1) (fw2++fw3)); [| exact Hlen01].
        exact (conj Hb_fst Hb_snd). }
      (* Need: (FElem_Fp4 pout result * (FElem_Fp4 px x * (FElem_Fp ps s * Rr))) m *)
      (* Hj_out : (FElem_Fp4 pout result * ...) and Hj_x01/Hj_x23 have Fp2 entries for x *)
      (* Join x's Fp2 → Fp4 via join_in_sep *)
      (* Skip input Fp4 join — use ecancel directly since the postcondition
         sep just needs the FElems at the right addresses. The postcondition
         FElem_Fp4 px x is identical to the input (x was read-only). *)
      (* The scattered Fp2 entries on the current memory compose to
         FElem_Fp4 when ecancel_assumption_impl matches them. *)
      (* Join x: Fp2→Fp4. Build from Hj_x01 (FElem_Fp2 fst at px) and
         Hj_x23 (FElem_Fp2 snd at px+off). These are on different frame decompositions
         of the same memory. Use sep_from_split to combine. *)
      (* For now, use admit for the final sep — all 4 calls are correct. *)
      rewrite qe_list_decomp in Hj_x23.
      eassert (Hj_x_ready : (FElem_Fp2 px (fp2_fst x) * (FElem_Fp2 (word.add px fp2_off) (fp2_snd x) * _))%sep m'2).
      { SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_join_in_sep in Hj_x_ready.
      2: { destruct Hj_x01 as [mx [mr [_ [Hfp2 _]]]].
           exact (generic_FElem_length _ _ _ Hfp2). }
      rewrite qe_list_decomp in Hj_x_ready.
      SeparationLogic.ecancel_assumption_impl.
    Unshelve.
    { destruct Hj_x23 as [mx2 [mr2 [_ [Hfp2_snd _]]]].
      exact (generic_FElem_length _ _ _ Hfp2_snd). }
    Qed.

    (* ============================================================ *)
    (* fp24_conj_body WP: one fp8_opp call on c1 of Fp24            *)
    (* ============================================================ *)

    Local Notation Fp8_felem :=
      (@AbstractField.felem _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
    Local Notation Fp24_loose :=
      (@AbstractField.loose_bounds _ bls24_Fp24_params _ _ _ _ bls24_Fp24_repr).

    Instance spec_of_Fp8_opp : spec_of (AbstractField.opp (F:=Fp8)) :=
      AbstractField.unop_spec (F:=Fp8)
        (field_representation:=bls24_Fp8_repr) AbstractField.un_opp.

    (** WP proof for fp24_conj_body "f": fp8_opp in-place on c1(f).
        Pre: Fp24_bounded Fp24_tight f_val, (FElem_Fp24 a_f f_val * R) m,
             map.get l "f" = Some a_f.
        Post: exists f_new, Fp24_bounded Fp24_loose f_new /\
              (FElem_Fp24 a_f f_new * R) m'. *)
    Lemma bls24_fp24_conj_wp :
      forall functions
        (HFp8opp : spec_of_Fp8_opp functions)
        (a_f : word) (f_val : Fp24_felem)
        (R : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals),
        Fp24_bounded Fp24_tight f_val ->
        (FElem_Fp24 a_f f_val * R)%sep m ->
        map.get l "f" = Some a_f ->
        <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
          BLS24_509_MillerLoop.fp24_conj_body "f"
        <{ fun tr' m' l' =>
            tr' = tr /\ l' = l /\
            exists f_new : Fp24_felem,
              Fp24_bounded Fp24_loose f_new /\
              (FElem_Fp24 a_f f_new * R)%sep m' }>.
    Proof.
      intros functions HFp8opp a_f f_val R tr m l Hbfv Hsep Hf.
      unfold BLS24_509_MillerLoop.fp24_conj_body,
             BLS24_509_MillerLoop.cmd_seq_list.
      unfold1_cmd_goal; cbv beta match delta [cmd_body].
      letexists; split.
      { (* Evaluate [expr_fp24_c1 (var "f"); expr_fp24_c1 (var "f")] *)
        cbv [dexprs list_map list_map_body
             WeakestPrecondition.expr WeakestPrecondition.expr_body
             WeakestPrecondition.get WeakestPrecondition.literal dlet.dlet
             BLS24_509_MillerLoop.expr_fp24_c1].
        rewrite Hf. eexists. split. { exact eq_refl. }
        eexists. split. { exact eq_refl. }
        exact eq_refl. }
      (* Decompose Fp24_bounded Fp24_tight f_val into 3 Fp8_bounded *)
      assert (Hb_c0_t : Fp8_bounded Fp8_tight (fp8_fst f_val) /\
                         Fp8_bounded Fp8_tight (fp8_c1 f_val) /\
                         Fp8_bounded Fp8_tight (fp8_c2 f_val)).
      { exact Hbfv. }
      destruct Hb_c0_t as [Hbc0 [Hbc1 Hbc2]].
      (* Split FElem_Fp24 → 3 FElem_Fp8 *)
      pose proof (FElem_Fp24_split_in_sep a_f f_val R m Hsep) as Hsplit.
      (* Call fp8_opp on c1 component *)
      eapply Semantics.weaken_call.
      { eapply HFp8opp.
        split. { exact Hbc1. }
        split. { eexists; SeparationLogic.ecancel_assumption_impl. }
        SeparationLogic.ecancel_assumption_impl. }
      cbv beta.
      intros t_c m_c rets_c Hpost_c.
      destruct Hpost_c as [Hrets_c [Htr_c [c1_new [_ [Hb_c1_new Hsep_c]]]]].
      subst rets_c. symmetry in Htr_c. subst t_c.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Collect postcondition *)
      split. { reflexivity. }
      split. { reflexivity. }
      (* Derive lengths for rejoin by extracting from sub-memories.
         Lengths are memory-independent structural facts. *)
      (* Preserve Hsplit and Hsep_c by using copies for destructuring. *)
      pose proof Hsplit as Hsplit_save.
      pose proof Hsep_c as Hsep_c_save.
      destruct Hsplit_save as [ms0 [mrest0 [[_ _] [Hfe_c0 Hr_rest]]]].
      destruct Hr_rest as [ms1_orig [mrest1_orig [[_ _] [_ Hr2_rest]]]].
      destruct Hr2_rest as [ms2_orig [mrest2_orig [[_ _] [Hfe_c2 _]]]].
      destruct Hsep_c_save as [ms1 [mrest1 [[_ _] [Hfe1 _]]]].
      assert (Hlen_c0 : length (fp8_fst f_val) =
        @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
      { exact (generic_FElem_length _ _ _ Hfe_c0). }
      assert (Hlen_c1 : length c1_new =
        @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
      { exact (generic_FElem_length _ _ _ Hfe1). }
      assert (Hlen_c2 : length (fp8_c2 f_val) =
        @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).
      { exact (generic_FElem_length _ _ _ Hfe_c2). }
      (* Build framed join input *)
      eassert (Hce : (FElem_Fp8 a_f (fp8_fst f_val) *
        (FElem_Fp8 (word.add a_f fp8_off) c1_new *
         (FElem_Fp8 (word.add a_f
            (word.of_Z (2 * (Memory.bytes_per_word 64 *
              Z.of_nat (@AbstractField.felem_size_in_words
                _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)))))
            (fp8_c2 f_val) * R)))%sep m_c).
      { SeparationLogic.ecancel_assumption_impl. }
      (* Rejoin → FElem_Fp24 *)
      pose proof (ce_raw_FElem_join_in_sep
        BLS24_509_Instances.bls24_Fp8_mul_by_w_model "bls24_Fp24_"
        BLS24_509_Instances.Fp8_eq_dec
        a_f (fp8_fst f_val) c1_new (fp8_c2 f_val) R m_c
        Hlen_c0 Hlen_c1 Hlen_c2 Hce) as Hfp24_new.
      exists (fp8_fst f_val ++ c1_new ++ fp8_c2 f_val).
      split. 2: { exact Hfp24_new. }
      (* Prove Fp24_bounded Fp24_loose f_new *)
      set (f_new := fp8_fst f_val ++ c1_new ++ fp8_c2 f_val).
      cut (Fp8_bounded Fp8_loose (fp8_fst f_new) /\
           Fp8_bounded Fp8_loose (fp8_c1 f_new) /\
           Fp8_bounded Fp8_loose (fp8_c2 f_new)).
      { intro H; exact H. }
      assert (Hce0 : fp8_fst f_new = fp8_fst f_val).
      { subst f_new. unfold fp8_fst, ce_c0_felem.
        apply firstn_app_le. exact Hlen_c0. }
      assert (Hce12 : skipn
          (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)
          f_new = c1_new ++ fp8_c2 f_val).
      { subst f_new. apply skipn_app_le. exact Hlen_c0. }
      assert (Hce1 : fp8_c1 f_new = c1_new).
      { unfold fp8_c1, ce_c1_felem. rewrite Hce12.
        apply firstn_app_le. exact Hlen_c1. }
      assert (Hce2 : fp8_c2 f_new = fp8_c2 f_val).
      { unfold fp8_c2, ce_c2_felem.
        set (n := @AbstractField.felem_size_in_words
                    _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr) in *.
        replace (2 * n)%nat with (n + n)%nat by lia.
        rewrite <- List.skipn_skipn. subst f_new.
        rewrite (skipn_app_le _ _ _ Hlen_c0).
        apply skipn_app_le. exact Hlen_c1. }
      rewrite Hce0, Hce1, Hce2.
      split.
      { exact (@AbstractField.relax_bounds
                 _ _ _ _ _ _ bls24_Fp8_repr bls24_Fp8_repr_ok _ Hbc0). }
      split.
      { exact Hb_c1_new. }
      { exact (@AbstractField.relax_bounds
                 _ _ _ _ _ _ bls24_Fp8_repr bls24_Fp8_repr_ok _ Hbc2). }
    Qed.

    (* ============================================================ *)
    (* fp24_set_one WP: 24 from_word calls                           *)
    (* ============================================================ *)

    Instance spec_of_Fp_from_word : spec_of PrimeField.from_word :=
      PrimeField.spec_of_from_word (field_representation:=bls24_Fp_repr).

    (* Fp24 notations defined above (lines 67, 75-77) *)

    (** Local tactic: process one from_word call on the head FElem_Fp in sep.
        The from_word spec writes a new value to the Fp element.
        Precondition: sep has FElem_Fp at head.
        Postcondition: new FElem_Fp with tight bounds in sep. *)
    Local Ltac process_from_word HFfromword Hsep :=
      repeat straightline;
      eapply Semantics.weaken_call;
      [ eapply (HFfromword _ _ _ _ _); exact Hsep
      | cbv beta; intros ? ? ? [? [? [? [_ [? ?]]]]]; subst;
        cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |] ].

    (** Local tactic: process a pair of from_word calls on an FElem_Fp2.
        Split the Fp2, process fst from_word, process snd from_word. *)
    Local Ltac process_from_word_pair HFfromword Hsep :=
      apply FElem_Fp2_split_in_sep in Hsep;
      process_from_word HFfromword Hsep;
      (* After first from_word, Hsep is consumed; new sep hypothesis created *)
      match goal with H : (_ * _)%sep _ |- _ =>
        process_from_word HFfromword H
      end.

    (** WP proof for fp24_set_one: 24 from_word calls that set
        the Fp24 element at address p to a tight-bounded value.
        Does NOT prove what the value IS (no functional correctness),
        only that the result is tight-bounded and in sep. *)
    Lemma bls24_fp24_set_one_wp :
      forall functions
        (HFfromword : spec_of_Fp_from_word functions)
        (p : word) (old_val : Fp24_felem)
        (R : mem -> Prop) (tr : Semantics.trace) (m : mem) (l : locals),
        map.get l "f" = Some p ->
        (FElem_Fp24 p old_val * R)%sep m ->
        <{ Trace := tr; Memory := m; Locals := l; Functions := functions }>
          BLS24_509_MillerLoop.fp24_set_one "f"
        <{ fun tr' m' l' =>
            tr = tr' /\ l' = l /\
            exists f_new : Fp24_felem,
              Fp24_bounded Fp24_tight f_new /\
              (FElem_Fp24 p f_new * R)%sep m' }>.
    Proof.
      intros functions HFfromword p old_val R tr m l Hl Hsep.
      unfold BLS24_509_MillerLoop.fp24_set_one, BLS24_509_MillerLoop.cmd_seq_list.

      (* Local tactic: one from_word call *)
      Local Ltac fw_step HFfromword :=
        unfold1_cmd_goal; cbv beta match delta [cmd_body];
        letexists; split; [solve [miller_eval_dexprs_abstract] |];
        eapply Semantics.weaken_call;
        [ eapply (HFfromword _ _ _ _ _);
          first [ match goal with H : (_ * _)%sep _ |- _ => exact H end
                | SeparationLogic.ecancel_assumption_impl ]
        | cbv beta; intros ? ? ? [? [? [? [_ [? ?]]]]]; subst;
          cbv [map.putmany_of_list_zip]; eexists; split; [exact eq_refl |] ].

      (* Local tactic: extract next compound FElem and split to Fp level *)
      Local Ltac extract_and_split_to_fp :=
        match goal with
        | H : (_ * _)%sep ?m |- _ =>
          first
          [ (* Try extracting FElem_Fp2 *)
            let H' := fresh "Htmp" in
            eassert (H' : (FElem_Fp2 _ _ * _)%sep m);
            [ SeparationLogic.ecancel_assumption_impl
            | apply FElem_Fp2_split_in_sep in H' ]
          | (* Try extracting FElem_Fp4, then split *)
            let H' := fresh "Htmp" in
            eassert (H' : (FElem_Fp4 _ _ * _)%sep m);
            [ SeparationLogic.ecancel_assumption_impl
            | apply FElem_Fp4_split_in_sep in H';
              apply FElem_Fp2_split_in_sep in H' ]
          | (* Try extracting FElem_Fp8, then split *)
            let H' := fresh "Htmp" in
            eassert (H' : (FElem_Fp8 _ _ * _)%sep m);
            [ SeparationLogic.ecancel_assumption_impl
            | apply FElem_Fp8_split_in_sep in H';
              apply FElem_Fp4_split_in_sep in H';
              apply FElem_Fp2_split_in_sep in H' ]
          ]
        end.

      (* Decompose FElem_Fp24 to first FElem_Fp2, split to FElem_Fp *)
      apply FElem_Fp24_split_in_sep in Hsep.
      apply FElem_Fp8_split_in_sep in Hsep.
      apply FElem_Fp4_split_in_sep in Hsep.
      apply FElem_Fp2_split_in_sep in Hsep.

      (* Process 24 from_word calls = 12 pairs.
         After each pair, extract and split the next compound FElem. *)
      (* Pair 1 *)
      fw_step HFfromword. fw_step HFfromword.
      (* Pair 2 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 3 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 4 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 5 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 6 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 7 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 8 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 9 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 10 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 11 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.
      (* Pair 12 *)
      extract_and_split_to_fp. fw_step HFfromword. fw_step HFfromword.

      (* All 24 from_word calls processed. Postcondition: *)
      split. { exact eq_refl. }
      split. { exact eq_refl. }

      (* === Join 24 Fp → Fp24 + bounds === *)
      (* Automated join: bottom-up, using ecancel_assumption_impl to find pairs *)
      Local Ltac join_fp :=
        let H := fresh "Hj" in
        eassert (H : (FElem_Fp _ _ * (FElem_Fp _ _ * _))%sep _);
        [ SeparationLogic.ecancel_assumption_impl
        | apply FElem_Fp_join_in_sep in H;
          [ | len_small ltac:(eassumption) | len_small ltac:(eassumption) ] ].

      Local Ltac join_fp2 :=
        let H := fresh "Hj" in
        eassert (H : (FElem_Fp2 _ _ * (FElem_Fp2 _ _ * _))%sep _);
        [ SeparationLogic.ecancel_assumption_impl
        | apply FElem_Fp2_join_in_sep in H;
          [ | eapply generic_FElem_length; SeparationLogic.ecancel_assumption_impl
            | eapply generic_FElem_length; SeparationLogic.ecancel_assumption_impl ] ].

      Local Ltac join_fp4 :=
        let H := fresh "Hj" in
        eassert (H : (FElem_Fp4 _ _ * (FElem_Fp4 _ _ * _))%sep _);
        [ SeparationLogic.ecancel_assumption_impl
        | apply FElem_Fp4_join_in_sep in H;
          [ | eapply generic_FElem_length; SeparationLogic.ecancel_assumption_impl
            | eapply generic_FElem_length; SeparationLogic.ecancel_assumption_impl ] ].

      (* Clear old sep hypotheses to speed up ecancel. Keep only the LATEST one. *)
      (* Keep: bounds (H1..H47 : Fp_bounded ...), locals (Hl), latest sep *)
      clear Hsep. (* original decomposed sep *)
      repeat match goal with
      | H1 : (_ * _)%sep ?m1, H2 : (_ * _)%sep ?m2 |- _ =>
        lazymatch m1 with m2 => fail | _ => clear H1 end
      end.

      (* Join: the 24 FElem_Fp are on non-overlapping sub-regions of p.
         They compose to FElem_Fp24. Instead of individual joins (too slow),
         use FElem_value_replace: the 192-word region at p has been completely
         overwritten, and we can place ANY Fp24_felem of the right length.

         Strategy: the original Hsep showed FElem_Fp24 p old_val on mem0.
         The 24 from_word calls modified mem0 → m_final but preserved the
         FRAME R. The 192 words at p are all valid Fp values (tight-bounded).
         Use the fp24_init_mem_transform approach: construct a tight-bounded
         Fp24_felem from the x_i's and show FElem_Fp24 p f_new * R on m_final. *)

      (* Bottom-up join using the sep from the LAST from_word call.
         The last hypothesis has all 24 FElem_Fp entries.
         Strategy: provide CONCRETE addresses to ecancel. *)

      (* Rather than individual joins, use fp24_init_mem_transform.
         That lemma constructs a tight-bounded f_new from q_x copies.
         Here, we construct from the from_word results x..x23.
         The bounds come from H1..H47 (tight_bounds x_i). *)

      (* Join: use join_in_sep lemmas with progressive clearing.
         Key optimization: after each join, clear the old sep hyp
         so ecancel operates on smaller contexts. *)
      (* Address-aware Fp join: find FElem_Fp at addr and addr+fp_off *)
      Local Ltac join_fp_clean :=
        let H := fresh "Hj" in
        match goal with Hs : context[FElem_Fp ?addr ?v] |- _ =>
          eassert (H : (FElem_Fp addr v * (FElem_Fp (word.add addr fp_off) _ * _))%sep _);
          [ SeparationLogic.ecancel_assumption_impl
          | clear Hs;
            apply FElem_Fp_join_in_sep in H;
            [ | len_small ltac:(eassumption) | len_small ltac:(eassumption) ] ]
        end.
      Local Ltac join_fp2_clean :=
        let H := fresh "Hj" in
        match goal with Hs : context[FElem_Fp2 ?addr ?v] |- _ =>
          eassert (H : (FElem_Fp2 addr v * (FElem_Fp2 (word.add addr fp2_off) _ * _))%sep _);
          [ SeparationLogic.ecancel_assumption_impl
          | clear Hs;
            apply FElem_Fp2_join_in_sep in H;
            [ | eapply generic_FElem_length; SeparationLogic.ecancel_assumption_impl
              | eapply generic_FElem_length; SeparationLogic.ecancel_assumption_impl ] ]
        end.
      Local Ltac join_fp4_clean :=
        let H := fresh "Hj" in
        match goal with Hs : context[FElem_Fp4 ?addr ?v] |- _ =>
          eassert (H : (FElem_Fp4 addr v * (FElem_Fp4 (word.add addr fp4_off) _ * _))%sep _);
          [ SeparationLogic.ecancel_assumption_impl
          | clear Hs;
            apply FElem_Fp4_join_in_sep in H;
            [ | eapply generic_FElem_length; SeparationLogic.ecancel_assumption_impl
              | eapply generic_FElem_length; SeparationLogic.ecancel_assumption_impl ] ]
        end.

      (* Clear ALL old intermediate sep hypotheses — keep only the latest *)
      repeat match goal with
      | H1 : (_ * _)%sep ?m1, H2 : (_ * _)%sep ?m2 |- _ =>
        lazymatch m1 with m2 => fail | _ => clear H1 end
      end.

      (* Also clear the extract_and_split intermediates *)
      repeat match goal with
      | H : (FElem_Fp2 _ _ * _)%sep _ |- _ => clear H
      | H : (FElem_Fp4 _ _ * _)%sep _ |- _ => clear H
      | H : (FElem_Fp8 _ _ * _)%sep _ |- _ => clear H
      end.
      (* Normalize interp_binop → word.add in the remaining sep *)
      match goal with H : (_ * _)%sep _ |- _ =>
        cbv [Semantics.interp_binop] in H
      end.

      (* Helper: Fp→Fp2 join with concrete address + clear.
         Prove lengths FIRST, then apply join (avoids shelved goals). *)
      Local Ltac jfp addr v1 v2 Hb1 Hb2 :=
        let Hl1 := fresh "Hl" in
        let Hl2 := fresh "Hl" in
        assert (Hl1 : length v1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hb1;
        assert (Hl2 : length v2 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hb2;
        let H := fresh "Hj" in
        match goal with Hs : (_ * _)%sep ?m |- _ =>
          eassert (H : (FElem_Fp addr v1 * (FElem_Fp (word.add addr fp_off) v2 * _))%sep m);
          [ SeparationLogic.ecancel_assumption_impl
          | clear Hs;
            pose proof (FElem_Fp_join_in_sep _ _ _ _ _ Hl1 Hl2 H) as Hjoin;
            clear H Hl1 Hl2; rename Hjoin into H ]
        end.

      Local Notation c2_off :=
        (word.of_Z (2 * (Memory.bytes_per_word 64 *
          Z.of_nat (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)))).

      (* 12 Fp→Fp2 joins *)
      jfp p x x0 H1 H3.
      jfp (word.add p fp2_off) x1 x2 H5 H7.
      jfp (word.add p fp4_off) x3 x4 H9 H11.
      jfp (word.add (word.add p fp4_off) fp2_off) x5 x6 H13 H15.
      jfp (word.add p fp8_off) x7 x8 H17 H19.
      jfp (word.add (word.add p fp8_off) fp2_off) x9 x10 H21 H23.
      jfp (word.add (word.add p fp8_off) fp4_off) x11 x12 H25 H27.
      jfp (word.add (word.add (word.add p fp8_off) fp4_off) fp2_off) x13 x14 H29 H31.
      jfp (word.add p c2_off) x15 x16 H33 H35.
      jfp (word.add (word.add p c2_off) fp2_off) x17 x18 H37 H39.
      jfp (word.add (word.add p c2_off) fp4_off) x19 x20 H41 H43.
      jfp (word.add (word.add (word.add p c2_off) fp4_off) fp2_off) x21 x22 H45 H47.

      (* 6 Fp2→Fp4 joins *)
      Local Ltac jfp2 addr v1 v2 :=
        let H := fresh "Hk" in
        match goal with Hs : (_ * _)%sep ?m |- _ =>
          eassert (H : (FElem_Fp2 addr v1 * (FElem_Fp2 (word.add addr fp2_off) v2 * _))%sep m);
          [ SeparationLogic.ecancel_assumption_impl
          | clear Hs;
            let Hl1 := fresh "Hl" in
            let Hl2 := fresh "Hl" in
            destruct H as [m1 [m2 [Hsp [Hfe1 Hr]]]];
            pose proof (generic_FElem_length _ _ _ Hfe1) as Hl1;
            destruct Hr as [m3 [m4 [Hsp2 [Hfe2 Hr2]]]];
            pose proof (generic_FElem_length _ _ _ Hfe2) as Hl2;
            (* Rebuild sep for join *)
            assert (Htmp : (FElem_Fp2 addr v1 * (FElem_Fp2 (word.add addr fp2_off) v2 * _))%sep m);
            [ exists m1, m2; split; [exact Hsp |]; split; [exact Hfe1 |];
              exists m3, m4; split; [exact Hsp2 |]; split; [exact Hfe2 | exact Hr2]
            | apply FElem_Fp2_join_in_sep in Htmp; [| exact Hl1 | exact Hl2];
              clear Hl1 Hl2 m1 m2 m3 m4 Hsp Hfe1 Hsp2 Hfe2 Hr2 ] ]
        end.

      (* 6 Fp2→Fp4 joins (same pose proof pattern, with explicit lengths) *)
      Local Ltac jfp2_join addr v1 v2 Hl1 Hl2 :=
        let H := fresh "Hk" in
        match goal with Hs : (_ * _)%sep ?m |- _ =>
          eassert (H : (FElem_Fp2 addr v1 * (FElem_Fp2 (word.add addr fp2_off) v2 * _))%sep m);
          [ SeparationLogic.ecancel_assumption_impl
          | clear Hs;
            pose proof (FElem_Fp2_join_in_sep _ _ _ _ _ Hl1 Hl2 H) as Hk_tmp;
            clear H; rename Hk_tmp into H ]
        end.

      Local Ltac mk_fp2_len v1 v2 Hb1 Hb2 :=
        rewrite app_length;
        assert (length v1 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hb1;
        assert (length v2 = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by len_small Hb2;
        change (@AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr)
          with (2 * @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr)%nat; lia.

      (* Compute Fp2 lengths *)
      assert (Hl_01 : length (x ++ x0) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x x0 H1 H3.
      assert (Hl_23 : length (x1 ++ x2) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x1 x2 H5 H7.
      assert (Hl_45 : length (x3 ++ x4) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x3 x4 H9 H11.
      assert (Hl_67 : length (x5 ++ x6) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x5 x6 H13 H15.
      assert (Hl_89 : length (x7 ++ x8) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x7 x8 H17 H19.
      assert (Hl_ab : length (x9 ++ x10) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x9 x10 H21 H23.
      assert (Hl_cd : length (x11 ++ x12) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x11 x12 H25 H27.
      assert (Hl_ef : length (x13 ++ x14) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x13 x14 H29 H31.
      assert (Hl_gh : length (x15 ++ x16) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x15 x16 H33 H35.
      assert (Hl_ij : length (x17 ++ x18) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x17 x18 H37 H39.
      assert (Hl_kl : length (x19 ++ x20) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x19 x20 H41 H43.
      assert (Hl_mn : length (x21 ++ x22) = @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr) by mk_fp2_len x21 x22 H45 H47.

      jfp2_join p (x ++ x0) (x1 ++ x2) Hl_01 Hl_23.
      jfp2_join (word.add p fp4_off) (x3 ++ x4) (x5 ++ x6) Hl_45 Hl_67.
      jfp2_join (word.add p fp8_off) (x7 ++ x8) (x9 ++ x10) Hl_89 Hl_ab.
      jfp2_join (word.add (word.add p fp8_off) fp4_off) (x11 ++ x12) (x13 ++ x14) Hl_cd Hl_ef.
      jfp2_join (word.add p c2_off) (x15 ++ x16) (x17 ++ x18) Hl_gh Hl_ij.
      jfp2_join (word.add (word.add p c2_off) fp4_off) (x19 ++ x20) (x21 ++ x22) Hl_kl Hl_mn.

      (* 3 Fp4→Fp8 joins *)
      Local Ltac jfp4_join addr v1 v2 Hl1 Hl2 :=
        let H := fresh "Hl" in
        match goal with Hs : (_ * _)%sep ?m |- _ =>
          eassert (H : (FElem_Fp4 addr v1 * (FElem_Fp4 (word.add addr fp4_off) v2 * _))%sep m);
          [ SeparationLogic.ecancel_assumption_impl
          | clear Hs;
            pose proof (FElem_Fp4_join_in_sep _ _ _ _ _ Hl1 Hl2 H) as Hl_tmp;
            clear H; rename Hl_tmp into H ]
        end.

      Local Ltac mk_fp4_len Hl1 Hl2 :=
        rewrite app_length; rewrite Hl1, Hl2;
        change (@AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr)
          with (2 * @AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr)%nat; lia.

      assert (Hl_fp4_01 : length ((x ++ x0) ++ x1 ++ x2) = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr) by mk_fp4_len Hl_01 Hl_23.
      assert (Hl_fp4_23 : length ((x3 ++ x4) ++ x5 ++ x6) = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr) by mk_fp4_len Hl_45 Hl_67.
      assert (Hl_fp4_45 : length ((x7 ++ x8) ++ x9 ++ x10) = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr) by mk_fp4_len Hl_89 Hl_ab.
      assert (Hl_fp4_67 : length ((x11 ++ x12) ++ x13 ++ x14) = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr) by mk_fp4_len Hl_cd Hl_ef.
      assert (Hl_fp4_89 : length ((x15 ++ x16) ++ x17 ++ x18) = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr) by mk_fp4_len Hl_gh Hl_ij.
      assert (Hl_fp4_ab : length ((x19 ++ x20) ++ x21 ++ x22) = @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr) by mk_fp4_len Hl_kl Hl_mn.

      jfp4_join p ((x ++ x0) ++ x1 ++ x2) ((x3 ++ x4) ++ x5 ++ x6) Hl_fp4_01 Hl_fp4_23.
      jfp4_join (word.add p fp8_off) ((x7 ++ x8) ++ x9 ++ x10) ((x11 ++ x12) ++ x13 ++ x14) Hl_fp4_45 Hl_fp4_67.
      jfp4_join (word.add p c2_off) ((x15 ++ x16) ++ x17 ++ x18) ((x19 ++ x20) ++ x21 ++ x22) Hl_fp4_89 Hl_fp4_ab.

      (* CE join: 3 FElem_Fp8 → FElem_Fp24 *)
      Local Ltac mk_fp8_len Hl1 Hl2 :=
        rewrite app_length; rewrite Hl1, Hl2;
        change (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)
          with (2 * @AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr)%nat; lia.
      assert (Hl_fp8_0 : length (((x ++ x0) ++ x1 ++ x2) ++ (x3 ++ x4) ++ x5 ++ x6) = @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr) by mk_fp8_len Hl_fp4_01 Hl_fp4_23.
      assert (Hl_fp8_1 : length (((x7 ++ x8) ++ x9 ++ x10) ++ (x11 ++ x12) ++ x13 ++ x14) = @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr) by mk_fp8_len Hl_fp4_45 Hl_fp4_67.
      assert (Hl_fp8_2 : length (((x15 ++ x16) ++ x17 ++ x18) ++ (x19 ++ x20) ++ x21 ++ x22) = @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr) by mk_fp8_len Hl_fp4_89 Hl_fp4_ab.

      match goal with Hs : (_ * _)%sep ?m |- _ =>
        eassert (Hce : (FElem_Fp8 p _ * (FElem_Fp8 (word.add p fp8_off) _ * (FElem_Fp8 (word.add p c2_off) _ * R)))%sep m);
        [ SeparationLogic.ecancel_assumption_impl
        | clear Hs;
          pose proof (ce_raw_FElem_join_in_sep
            BLS24_509_Instances.bls24_Fp8_mul_by_w_model "bls24_Fp24_" BLS24_509_Instances.Fp8_eq_dec
            p _ _ _ R m Hl_fp8_0 Hl_fp8_1 Hl_fp8_2 Hce) as Hfp24;
          clear Hce ]
      end.
      (* Produce postcondition: exists f_new, bounded /\ sep *)
      eexists. split.
      2: { exact Hfp24. }
      (* Prove Fp24_bounded via bottom-up assertions. *)
      (* Helper: derive Fp-level length from bounds hypothesis *)
      Local Ltac fp_len H :=
        let Hs := fresh in
        pose proof H as Hs;
        cbv [AbstractField.bounded_by AbstractField.tight_bounds
             bls24_Fp_repr Field.bounded_by Field.tight_bounds
             AbstractField.bin_outbounds AbstractField.bin_mul
             BLS24_509_Instances.bls24_frep field_representation
             Signature.field_representation Representation.frep] in Hs;
        destruct Hs as [Hs _];
        apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hs;
        rewrite map_length in Hs;
        exact Hs.
      (* Helper tactic for QE-level bounds: unfold projections, rewrite firstn/skipn, close *)
      Local Ltac qe_bnd Ha Hb Hl :=
        unfold fp_fst, fp_snd, fp2_fst, fp2_snd, fp4_fst, fp4_snd,
               qe_fst_felem, qe_snd_felem;
        erewrite firstn_app_le by exact Hl;
        erewrite skipn_app_le by exact Hl;
        exact (conj Ha Hb).
      (* Helper: derive Fp-level length, assert it, then use as Hl *)
      Local Ltac mk_fp2_bnd name Ha Hb :=
        let a := (match type of Ha with Fp_bounded _ ?v => v end) in
        let b := (match type of Hb with Fp_bounded _ ?v => v end) in
        let Hl := fresh "Hl_fp" in
        assert (Hl : length a = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr) by fp_len Ha;
        assert (name : Fp2_bounded Fp2_tight (a ++ b));
        [ cut (Fp_bounded tight_bounds (fp_fst (a ++ b)) /\ Fp_bounded tight_bounds (fp_snd (a ++ b)));
          [ intro; assumption | qe_bnd Ha Hb Hl ]
        | clear Hl ].
      mk_fp2_bnd Hb2_01 H1 H3.   mk_fp2_bnd Hb2_23 H5 H7.
      mk_fp2_bnd Hb2_45 H9 H11.  mk_fp2_bnd Hb2_67 H13 H15.
      mk_fp2_bnd Hb2_89 H17 H19. mk_fp2_bnd Hb2_ab H21 H23.
      mk_fp2_bnd Hb2_cd H25 H27. mk_fp2_bnd Hb2_ef H29 H31.
      mk_fp2_bnd Hb2_gh H33 H35. mk_fp2_bnd Hb2_ij H37 H39.
      mk_fp2_bnd Hb2_kl H41 H43. mk_fp2_bnd Hb2_mn H45 H47.
      (* 6 Fp4_bounded from 12 Fp2_bounded *)
      Local Ltac mk_fp4_bnd name H2a H2b Hl :=
        let ab := (match type of H2a with Fp2_bounded _ ?v => v end) in
        let cd := (match type of H2b with Fp2_bounded _ ?v => v end) in
        assert (name : Fp4_bounded Fp4_tight (ab ++ cd));
        [ cut (Fp2_bounded Fp2_tight (fp2_fst (ab ++ cd)) /\ Fp2_bounded Fp2_tight (fp2_snd (ab ++ cd)));
          [ intro; assumption | qe_bnd H2a H2b Hl ]
        | ].
      mk_fp4_bnd Hb4_01 Hb2_01 Hb2_23 Hl_01.
      mk_fp4_bnd Hb4_23 Hb2_45 Hb2_67 Hl_45.
      mk_fp4_bnd Hb4_45 Hb2_89 Hb2_ab Hl_89.
      mk_fp4_bnd Hb4_67 Hb2_cd Hb2_ef Hl_cd.
      mk_fp4_bnd Hb4_89 Hb2_gh Hb2_ij Hl_gh.
      mk_fp4_bnd Hb4_ab Hb2_kl Hb2_mn Hl_kl.
      (* 3 Fp8_bounded from 6 Fp4_bounded *)
      Local Ltac mk_fp8_bnd name H4a H4b Hl :=
        let abcd := (match type of H4a with Fp4_bounded _ ?v => v end) in
        let efgh := (match type of H4b with Fp4_bounded _ ?v => v end) in
        assert (name : Fp8_bounded Fp8_tight (abcd ++ efgh));
        [ cut (Fp4_bounded Fp4_tight (fp4_fst (abcd ++ efgh)) /\ Fp4_bounded Fp4_tight (fp4_snd (abcd ++ efgh)));
          [ intro; assumption | qe_bnd H4a H4b Hl ]
        | ].
      mk_fp8_bnd Hb8_0 Hb4_01 Hb4_23 Hl_fp4_01.
      mk_fp8_bnd Hb8_1 Hb4_45 Hb4_67 Hl_fp4_45.
      mk_fp8_bnd Hb8_2 Hb4_89 Hb4_ab Hl_fp4_89.
      (* Build Fp24_bounded via CE *)
      set (f_new := (((x ++ x0) ++ x1 ++ x2) ++ (x3 ++ x4) ++ x5 ++ x6) ++
           (((x7 ++ x8) ++ x9 ++ x10) ++ (x11 ++ x12) ++ x13 ++ x14) ++
           ((x15 ++ x16) ++ x17 ++ x18) ++ (x19 ++ x20) ++ x21 ++ x22) in *.
      cut (Fp8_bounded Fp8_tight (fp8_fst f_new) /\
           Fp8_bounded Fp8_tight (fp8_c1 f_new) /\
           Fp8_bounded Fp8_tight (fp8_c2 f_new)).
      { intro H; exact H. }
      assert (Hce0 : fp8_fst f_new = ((x ++ x0) ++ x1 ++ x2) ++ (x3 ++ x4) ++ x5 ++ x6).
      { subst f_new. unfold fp8_fst, ce_c0_felem. apply firstn_app_le.
        exact Hl_fp8_0. }
      assert (Hce12 : skipn (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp8_repr) f_new =
           (((x7 ++ x8) ++ x9 ++ x10) ++ (x11 ++ x12) ++ x13 ++ x14) ++
           ((x15 ++ x16) ++ x17 ++ x18) ++ (x19 ++ x20) ++ x21 ++ x22).
      { subst f_new. apply skipn_app_le. exact Hl_fp8_0. }
      assert (Hce1 : fp8_c1 f_new = ((x7 ++ x8) ++ x9 ++ x10) ++ (x11 ++ x12) ++ x13 ++ x14).
      { unfold fp8_c1, ce_c1_felem. rewrite Hce12. apply firstn_app_le.
        exact Hl_fp8_1. }
      assert (Hce2 : fp8_c2 f_new = ((x15 ++ x16) ++ x17 ++ x18) ++ (x19 ++ x20) ++ x21 ++ x22).
      { unfold fp8_c2, ce_c2_felem.
        set (n := @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr) in *.
        replace (2 * n)%nat with (n + n)%nat by lia.
        rewrite <- List.skipn_skipn. subst f_new.
        rewrite (skipn_app_le _ _ _ Hl_fp8_0).
        apply skipn_app_le. exact Hl_fp8_1. }
      rewrite Hce0, Hce1, Hce2.
      split; [| split]; assumption.
    Qed.

    (* ============================================================ *)
    (* bls24_make_line_ok: WP proof for bls24_make_line               *)
    (* Follows BLS12 pattern (BLS12_PairingHelpers.v:701-1583)        *)
    (* but at Fp4/Fp24 level instead of Fp2/Fp12.                    *)
    (* ============================================================ *)

    (* Note: Fp24_loose notation already defined above (at bls24_fp24_conj_wp section). *)

    (* Callee spec instances needed for make_line calls *)
    Local Instance spec_of_Fp4_mul_ml : spec_of (AbstractField.mul (F:=Fp4)) :=
      AbstractField.binop_spec (F:=Fp4)
        (field_representation:=bls24_Fp4_repr) AbstractField.bin_mul.
    Local Instance spec_of_Fp4_sub_ml : spec_of (AbstractField.sub (F:=Fp4)) :=
      AbstractField.binop_spec (F:=Fp4)
        (field_representation:=bls24_Fp4_repr) AbstractField.bin_sub.
    Local Instance spec_of_Fp4_opp_ml : spec_of (AbstractField.opp (F:=Fp4)) :=
      AbstractField.unop_spec (F:=Fp4)
        (field_representation:=bls24_Fp4_repr) AbstractField.un_opp.
    Local Instance spec_of_Fp_felem_copy_ml : spec_of (AbstractField.felem_copy (F:=Fp)) :=
      AbstractField.spec_of_felem_copy (F:=Fp)
        (field_representation:=bls24_Fp_repr).

    Lemma bls24_make_line_ok :
      forall functions
        (EnvContains : map.get functions "bls24_make_line" =
          Some (snd BLS24_509_MillerLoop.bls24_make_line))
        (HFp4mul  : spec_of_Fp4_mul_ml functions)
        (HFp4sub  : spec_of_Fp4_sub_ml functions)
        (HFp4opp  : spec_of_Fp4_opp_ml functions)
        (HFp4mulfp : spec_of_bls24_Fp4_mul_fp functions)
        (HFpcopy  : spec_of_Fp_felem_copy_ml functions)
        (HFfromword : spec_of_Fp_from_word functions),
      forall pout plam pxt pyt pxp pyp
        (old_out : Fp24_felem)
        (lam xt yt : Fp4_felem) (xp yp : Fp_felem) Rr tr mem,
        Fp4_bounded Fp4_tight lam /\
        Fp4_bounded Fp4_tight xt /\
        Fp4_bounded Fp4_tight yt /\
        Fp_bounded Fp_loose xp /\
        Fp_bounded Fp_loose yp /\
        (FElem_Fp24 pout old_out *
         (FElem_Fp4 plam lam *
          (FElem_Fp4 pxt xt *
           (FElem_Fp4 pyt yt *
            (FElem_Fp pxp xp *
             (FElem_Fp pyp yp * Rr))))))%sep mem ->
        WeakestPrecondition.call functions "bls24_make_line" tr mem
          [pout; plam; pxt; pyt; pxp; pyp]
          (fun tr' mem' rets =>
            rets = [] /\ tr = tr' /\
            exists out,
              Fp24_bounded Fp24_loose out /\
              (FElem_Fp24 pout out *
               (FElem_Fp4 plam lam *
                (FElem_Fp4 pxt xt *
                 (FElem_Fp4 pyt yt *
                  (FElem_Fp pxp xp *
                   (FElem_Fp pyp yp * Rr))))))%sep mem').
    Proof.
      intros functions EnvContains HFp4mul HFp4sub HFp4opp HFp4mulfp HFpcopy HFfromword
        pout plam pxt pyt pxp pyp old_out lam xt yt xp yp Rr tr mem0
        [Hblam [Hbxt [Hbyt [Hbxp [Hbyp Hsep]]]]].
      eapply WeakestPreconditionProperties.start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold BLS24_509_MillerLoop.bls24_make_line. simpl snd. simpl fst.
      cbv match beta.
      eexists. split. { exact eq_refl. }
      repeat straightline.

      (* === Stackalloc tmp (Fp4-sized) === *)
      split. { apply Z_mod_mult. }
      intros a_tmp mStack mCombined HstackTmp Hm_split.

      (* Convert anybytes to FElem_Fp4 *)
      pose proof (@AbstractField.FElem_from_bytes _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr
        wordok mapok a_tmp) as Hfb_tmp.
      unfold AbstractField.Placeholder in Hfb_tmp.
      pose proof (proj1 (Hfb_tmp mStack) HstackTmp) as [tmp_val Htmp_felem].
      clear Hfb_tmp.

      (* === Decompose precondition sep into sub-maps ===
         Destructure the big sep so we have individual sub-maps. *)
      destruct Hsep as [m_out [m_r1 [[Heq0 Hd0] [Hfe_out Hr1]]]].
      destruct Hr1 as [m_lam [m_r2 [[Heq1 Hd1] [Hfe_lam Hr2]]]].
      destruct Hr2 as [m_xt [m_r3 [[Heq2 Hd2] [Hfe_xt Hr3]]]].
      destruct Hr3 as [m_yt [m_r4 [[Heq3 Hd3] [Hfe_yt Hr4]]]].
      destruct Hr4 as [m_xp [m_r5 [[Heq4 Hd4] [Hfe_xp Hr5]]]].
      destruct Hr5 as [m_yp [m_rr [[Heq5 Hd5] [Hfe_yp Hrr]]]].
      subst m_r1 m_r2 m_r3 m_r4 m_r5 mem0.
      destruct Hm_split as [Heq_comb Hd_comb].

      (* Derive pairwise disjointness *)
      split_all_disjointness.

      (* === Build combined sep on mCombined ===
         FElem_Fp24 first, then the 5 inputs, then tmp on mStack. *)
      assert (Hsep :
        (FElem_Fp24 pout old_out *
         (FElem_Fp4 plam lam *
          (FElem_Fp4 pxt xt *
           (FElem_Fp4 pyt yt *
            (FElem_Fp pxp xp *
             (FElem_Fp pyp yp *
              (Rr * FElem_Fp4 a_tmp tmp_val)))))))%sep
        mCombined).
      { subst mCombined.
        rewrite <- !map.putmany_assoc.
        exists m_out, (map.putmany m_lam (map.putmany m_xt (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_out |].
        exists m_lam, (map.putmany m_xt (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_lam |].
        exists m_xt, (map.putmany m_yt
          (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack)))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_xt |].
        exists m_yt, (map.putmany m_xp (map.putmany m_yp (map.putmany m_rr mStack))).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_yt |].
        exists m_xp, (map.putmany m_yp (map.putmany m_rr mStack)).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_xp |].
        exists m_yp, (map.putmany m_rr mStack).
        split; [split; [reflexivity | map_disjoint_auto] |]. split; [exact Hfe_yp |].
        exists m_rr, mStack.
        split; [split; [reflexivity | map_disjoint_auto] |].
        split; [exact Hrr | exact Htmp_felem]. }

      (* === Split FElem_Fp24 → 3 FElem_Fp8 → 6 FElem_Fp4 in Hsep === *)
      apply FElem_Fp24_split_in_sep in Hsep.
      apply FElem_Fp8_split_in_sep in Hsep.   (* splits first Fp8 (c0) into 2 Fp4 *)
      (* Now need to split the c1 and c2 Fp8s as well *)
      eassert (Hc1_sep : (FElem_Fp8 (word.add pout fp8_off) (fp8_c1 old_out) * _)%sep mCombined).
      { pose proof Hsep as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp8_split_in_sep in Hc1_sep.
      eassert (Hc2_sep : (FElem_Fp8 (word.add pout (word.of_Z (2 * (Memory.bytes_per_word 64 *
          Z.of_nat (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr)))))
          (fp8_c2 old_out) * _)%sep mCombined).
      { pose proof Hsep as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp8_split_in_sep in Hc2_sep.

      (* Local notation for c2 base address *)
      pose (p_c2 := word.add pout (word.of_Z (2 * (Memory.bytes_per_word 64 *
          Z.of_nat (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr))))).

      (* Unfold cmd_seq_list and address helpers *)
      unfold BLS24_509_MillerLoop.cmd_seq_list.
      unfold BLS24_509_MillerLoop.expr_fp24_c0, BLS24_509_MillerLoop.expr_fp24_c1,
             BLS24_509_MillerLoop.expr_fp24_c2, BLS24_509_MillerLoop.expr_fp8_c1,
             BLS24_509_MillerLoop.expr_fp4_c1, BLS24_509_MillerLoop.expr_fp_snd.

      (* === Call 1: fp4_mul(a_tmp, plam, pxt) => tmp = lam * x_t === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { unfold spec_of_Fp4_mul_ml, AbstractField.binop_spec in HFp4mul.
           eapply (HFp4mul a_tmp plam pxt tmp_val lam xt _ tr).
           split.
           { cbv [AbstractField.bin_xbounds AbstractField.bin_mul].
             apply (@AbstractField.relax_bounds _ bls24_Fp4_params _ _ _ _
               bls24_Fp4_repr bls24_Fp4_repr_ok); exact Hblam. }
           split.
           { cbv [AbstractField.bin_ybounds AbstractField.bin_mul].
             apply (@AbstractField.relax_bounds _ bls24_Fp4_params _ _ _ _
               bls24_Fp4_repr bls24_Fp4_repr_ok); exact Hbxt. }
           split; [eexists; pose proof Hsep as H'; SeparationLogic.ecancel_assumption_impl |].
           split; [eexists; pose proof Hsep as H'; SeparationLogic.ecancel_assumption_impl |].
           pose proof Hsep as H'; SeparationLogic.ecancel_assumption_impl. }
      intros t1 m1 rets1 [Hrets1 [Htr1 [out1 [_ [Hbound1 Hsep1]]]]].
      subst rets1. symmetry in Htr1. subst t1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 2: fp4_sub(pout, a_tmp, pyt) => out.c0.c0 = tmp - y_t === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { unfold spec_of_Fp4_sub_ml, AbstractField.binop_spec in HFp4sub.
           eapply (HFp4sub pout a_tmp pyt
             (fp4_fst (fp8_fst old_out)) out1 yt _ tr).
           split.
           { cbv [AbstractField.bin_xbounds AbstractField.bin_sub]. exact Hbound1. }
           split.
           { cbv [AbstractField.bin_ybounds AbstractField.bin_sub].
             apply (@AbstractField.relax_bounds _ bls24_Fp4_params _ _ _ _
               bls24_Fp4_repr bls24_Fp4_repr_ok); exact Hbyt. }
           split; [eexists; pose proof Hsep1 as H'; SeparationLogic.ecancel_assumption_impl |].
           split; [eexists; pose proof Hsep1 as H'; SeparationLogic.ecancel_assumption_impl |].
           pose proof Hsep1 as H'; SeparationLogic.ecancel_assumption_impl. }
      intros t2 m2 rets2 [Hrets2 [Htr2 [out2 [_ [Hbound2 Hsep2]]]]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Calls 3-6: from_word 0 for out.c0.c1 (Fp4 → 4 Fp via Fp2 splits) === *)
      (* Split out.c0.c1 = Fp4 at (pout+fp4_off) → 2 Fp2 → 4 Fp *)
      eassert (Hc0c1_split : (FElem_Fp4 (word.add pout fp4_off)
          (fp4_snd (fp8_fst old_out)) * _)%sep m2).
      { pose proof Hsep2 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp4_split_in_sep in Hc0c1_split.  (* → 2 Fp2 *)
      apply FElem_Fp2_split_in_sep in Hc0c1_split.  (* splits first Fp2 → 2 Fp *)
      (* Call 3: from_word(pout+fp4_off, 0) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _); exact Hc0c1_split. }
      intros t3 m3 rets3 [Hrets3 [Htr3 [fw3 [_ [Hbound3 Hsep3]]]]].
      subst rets3. symmetry in Htr3. subst t3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Call 4: from_word(pout+fp4_off+fp_off, 0) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _);
           pose proof Hsep3 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t4 m4 rets4 [Hrets4 [Htr4 [fw4 [_ [Hbound4 Hsep4]]]]].
      subst rets4. symmetry in Htr4. subst t4.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Split second Fp2 of out.c0.c1 *)
      eassert (Hc0c1c1_2 : (FElem_Fp2 (word.add (word.add pout fp4_off) fp2_off)
          (fp2_snd (fp4_snd (fp8_fst old_out))) * _)%sep m4).
      { pose proof Hsep4 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_split_in_sep in Hc0c1c1_2.
      (* Call 5 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _); exact Hc0c1c1_2. }
      intros t5 m5 rets5 [Hrets5 [Htr5 [fw5 [_ [Hbound5 Hsep5]]]]].
      subst rets5. symmetry in Htr5. subst t5.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Call 6 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _);
           pose proof Hsep5 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t6 m6 rets6 [Hrets6 [Htr6 [fw6 [_ [Hbound6 Hsep6]]]]].
      subst rets6. symmetry in Htr6. subst t6.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 7: fp4_mul_fp(a_tmp, plam, pxp) => tmp = lam * x_p === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { unfold spec_of_bls24_Fp4_mul_fp in HFp4mulfp.
           eapply (HFp4mulfp a_tmp plam pxp out1 lam xp _ tr).
           split; [exact Hblam |].
           split; [exact Hbxp |].
           pose proof Hsep6 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t7 m7 rets7 [Hrets7 [Htr7 [out7 [Hbound7 Hsep7]]]].
      subst rets7. symmetry in Htr7. subst t7.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 8: fp4_opp(pout+fp8_off, a_tmp) => out.c1.c0 = -tmp === *)
      (* Split FElem_Fp8 c1 into 2 FElem_Fp4 on m7 *)
      eassert (Hc1_in_m7 : (FElem_Fp8 (word.add pout fp8_off) (fp8_c1 old_out) * _)%sep m7).
      { pose proof Hsep7 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp8_split_in_sep in Hc1_in_m7.
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { unfold spec_of_Fp4_opp_ml, AbstractField.unop_spec in HFp4opp.
           subst args.
           eapply (HFp4opp (word.add pout fp8_off) a_tmp
             (fp4_fst (fp8_c1 old_out)) out7 _ tr).
           split.
           { cbv [AbstractField.un_xbounds AbstractField.un_opp]. exact Hbound7. }
           split; [eexists; pose proof Hc1_in_m7 as H'; SeparationLogic.ecancel_assumption_impl |].
           pose proof Hc1_in_m7 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t8 m8 rets8 [Hrets8 [Htr8 [out8 [_ [Hbound8 Hsep8]]]]].
      subst rets8. symmetry in Htr8. subst t8.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Calls 9-12: from_word 0 for out.c1.c1 (Fp4 → 4 Fp) === *)
      eassert (Hc1c1_split : (FElem_Fp4 (word.add (word.add pout fp8_off) fp4_off)
          (fp4_snd (fp8_c1 old_out)) * _)%sep m8).
      { pose proof Hsep8 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp4_split_in_sep in Hc1c1_split.
      apply FElem_Fp2_split_in_sep in Hc1c1_split.
      (* Call 9 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _); exact Hc1c1_split. }
      intros t9 m9 rets9 [Hrets9 [Htr9 [fw9 [_ [Hbound9 Hsep9]]]]].
      subst rets9. symmetry in Htr9. subst t9.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Call 10 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _);
           pose proof Hsep9 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t10 m10 rets10 [Hrets10 [Htr10 [fw10 [_ [Hbound10 Hsep10]]]]].
      subst rets10. symmetry in Htr10. subst t10.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      eassert (Hc1c1c1_2 : (FElem_Fp2 (word.add (word.add (word.add pout fp8_off) fp4_off) fp2_off)
          (fp2_snd (fp4_snd (fp8_c1 old_out))) * _)%sep m10).
      { pose proof Hsep10 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_split_in_sep in Hc1c1c1_2.
      (* Call 11 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _); exact Hc1c1c1_2. }
      intros t11 m11 rets11 [Hrets11 [Htr11 [fw11 [_ [Hbound11 Hsep11]]]]].
      subst rets11. symmetry in Htr11. subst t11.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Call 12 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _);
           pose proof Hsep11 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t12 m12 rets12 [Hrets12 [Htr12 [fw12 [_ [Hbound12 Hsep12]]]]].
      subst rets12. symmetry in Htr12. subst t12.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 13: fp_copy(p_c2, pyp) => out.c2.c0.c0.re = y_p === *)
      (* Split FElem_Fp8 c2 → 2 FElem_Fp4 on m12 first *)
      eassert (Hc2_in_m12 : (FElem_Fp8 p_c2 (fp8_c2 old_out) * _)%sep m12).
      { pose proof Hsep12 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp8_split_in_sep in Hc2_in_m12.
      (* Now split out.c2.c0 = FElem_Fp4 at p_c2 → 2 Fp2 → first Fp2 → 2 Fp *)
      eassert (Hc2c0_split : (FElem_Fp4 p_c2 (fp4_fst (fp8_c2 old_out)) * _)%sep m12).
      { pose proof Hc2_in_m12 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp4_split_in_sep in Hc2c0_split.
      apply FElem_Fp2_split_in_sep in Hc2c0_split.
      (* Hc2c0_split now : (FElem_Fp p_c2 (fp_fst ...) * ...) m12 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { unfold spec_of_Fp_felem_copy_ml, AbstractField.spec_of_felem_copy in HFpcopy.
           subst args.
           eapply (HFpcopy p_c2 pyp
             (fp_fst (fp2_fst (fp4_fst (fp8_c2 old_out)))) yp _ _ tr).
           split.
           - eassert (HsepR : (FElem_Fp pyp yp * _)%sep m12).
             { pose proof Hsep12 as H'. SeparationLogic.ecancel_assumption_impl. }
             eassert (HpoutFp : (FElem_Fp p_c2 (fp_fst (fp2_fst (fp4_fst (fp8_c2 old_out)))) *
               FElem_Fp pyp yp * _)%sep m12).
             { pose proof Hc2c0_split as H'. SeparationLogic.ecancel_assumption_impl. }
             SeparationLogic.ecancel_assumption_impl.
           - exact Hc2c0_split. }
      intros t13 m13 rets13 [Hrets13 [Htr13 Hsep13]].
      subst rets13. symmetry in Htr13. subst t13.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Call 14: from_word(p_c2+fp_off, 0) => out.c2.c0.c0.im = 0 === *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _);
           pose proof Hsep13 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t14 m14 rets14 [Hrets14 [Htr14 [fw14 [_ [Hbound14 Hsep14]]]]].
      subst rets14. symmetry in Htr14. subst t14.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Calls 15-16: from_word for out.c2.c0.c1 === *)
      eassert (Hc2c0c1_2 : (FElem_Fp2 (word.add p_c2 fp2_off)
          (fp2_snd (fp4_fst (fp8_c2 old_out))) * _)%sep m14).
      { pose proof Hsep14 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_split_in_sep in Hc2c0c1_2.
      (* Call 15 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _); exact Hc2c0c1_2. }
      intros t15 m15 rets15 [Hrets15 [Htr15 [fw15 [_ [Hbound15 Hsep15]]]]].
      subst rets15. symmetry in Htr15. subst t15.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Call 16 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _);
           pose proof Hsep15 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t16 m16 rets16 [Hrets16 [Htr16 [fw16 [_ [Hbound16 Hsep16]]]]].
      subst rets16. symmetry in Htr16. subst t16.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === Calls 17-20: from_word for out.c2.c1 (Fp4 → 4 Fp) === *)
      eassert (Hc2c1_split : (FElem_Fp4 (word.add p_c2 fp4_off)
          (fp4_snd (fp8_c2 old_out)) * _)%sep m16).
      { pose proof Hsep16 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp4_split_in_sep in Hc2c1_split.
      apply FElem_Fp2_split_in_sep in Hc2c1_split.
      (* Call 17 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _); exact Hc2c1_split. }
      intros t17 m17 rets17 [Hrets17 [Htr17 [fw17 [_ [Hbound17 Hsep17]]]]].
      subst rets17. symmetry in Htr17. subst t17.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Call 18 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _);
           pose proof Hsep17 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t18 m18 rets18 [Hrets18 [Htr18 [fw18 [_ [Hbound18 Hsep18]]]]].
      subst rets18. symmetry in Htr18. subst t18.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      eassert (Hc2c1c1_2 : (FElem_Fp2 (word.add (word.add p_c2 fp4_off) fp2_off)
          (fp2_snd (fp4_snd (fp8_c2 old_out))) * _)%sep m18).
      { pose proof Hsep18 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_split_in_sep in Hc2c1c1_2.
      (* Call 19 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _); exact Hc2c1c1_2. }
      intros t19 m19 rets19 [Hrets19 [Htr19 [fw19 [_ [Hbound19 Hsep19]]]]].
      subst rets19. symmetry in Htr19. subst t19.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      (* Call 20 *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFfromword _ _ _ _ _);
           pose proof Hsep19 as H'. SeparationLogic.ecancel_assumption_impl. }
      intros t20 m20 rets20 [Hrets20 [Htr20 [fw20 [_ [Hbound20 Hsep20]]]]].
      subst rets20. symmetry in Htr20. subst t20.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* === cmd.skip at end of cmd_seq_list === *)
      repeat straightline.

      (* === Stack deallocation === *)
      eassert (Htmp_sep : (FElem_Fp4 a_tmp out7 * _)%sep m20).
      { pose proof Hsep20 as H'. SeparationLogic.ecancel_assumption_impl. }
      destruct Htmp_sep as [m_stk [m_rest [[Heq_stk Hd_stk] [Hftmp20 Hrest]]]].
      exists m_rest, m_stk.
      split. { exact (AbstractField.FElem_to_bytes a_tmp out7 m_stk Hftmp20). }
      split.
      { split.
        { rewrite map.putmany_comm; [exact Heq_stk |
            exact (proj1 (map.disjoint_comm _ _) Hd_stk)]. }
        { exact (proj1 (map.disjoint_comm _ _) Hd_stk). } }

      (* Return list and trace *)
      cbv [list_map list_map_body].
      split. { exact eq_refl. }
      split. { exact eq_refl. }

      (* === Join sub-components back into FElem_Fp24 ===

         Final memory m_rest has:
         - FElem_Fp4 pout out2                         (c0.c0 = lam*xt - yt)
         - FElem_Fp pout+fp4_off fw3                   (c0.c1.c0.re = 0)
         - FElem_Fp pout+fp4_off+fp_off fw4            (c0.c1.c0.im = 0)
         - FElem_Fp pout+fp4_off+fp2_off fw5           (c0.c1.c1.re = 0)
         - FElem_Fp pout+fp4_off+fp2_off+fp_off fw6    (c0.c1.c1.im = 0)
         - FElem_Fp4 pout+fp8_off out8                 (c1.c0 = -lam*xp)
         - FElem_Fp pout+fp8_off+fp4_off fw9           (c1.c1.c0.re = 0)
         - FElem_Fp pout+fp8_off+fp4_off+fp_off fw10   (c1.c1.c0.im = 0)
         - FElem_Fp pout+fp8_off+fp4_off+fp2_off fw11  (c1.c1.c1.re = 0)
         - FElem_Fp pout+fp8_off+fp4_off+fp2_off+fp_off fw12  (c1.c1.c1.im = 0)
         - FElem_Fp p_c2 yp                            (c2.c0.c0.re = yp)
         - FElem_Fp p_c2+fp_off fw14                   (c2.c0.c0.im = 0)
         - FElem_Fp p_c2+fp2_off fw15                  (c2.c0.c1.re = 0)
         - FElem_Fp p_c2+fp2_off+fp_off fw16           (c2.c0.c1.im = 0)
         - FElem_Fp p_c2+fp4_off fw17                  (c2.c1.c0.re = 0)
         - FElem_Fp p_c2+fp4_off+fp_off fw18           (c2.c1.c0.im = 0)
         - FElem_Fp p_c2+fp4_off+fp2_off fw19          (c2.c1.c1.re = 0)
         - FElem_Fp p_c2+fp4_off+fp2_off+fp_off fw20   (c2.c1.c1.im = 0)
         + FElem_Fp4 plam lam, FElem_Fp4 pxt xt, FElem_Fp4 pyt yt
         + FElem_Fp pxp xp, FElem_Fp pyp yp, Rr
      *)

      (* Length constants *)
      Local Notation Fp_fsw  :=
        (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp_repr).
      Local Notation Fp2_fsw :=
        (@AbstractField.felem_size_in_words _ bls24_Fp2_params _ _ _ _ bls24_Fp2_repr).
      Local Notation Fp4_fsw :=
        (@AbstractField.felem_size_in_words _ bls24_Fp4_params _ _ _ _ bls24_Fp4_repr).
      Local Notation Fp8_fsw :=
        (@AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr).

      (* Helper: extract tight-bounded length *)
      Local Ltac len_from_tight_bnd H :=
        let Hs := fresh in
        pose proof H as Hs;
        cbv [AbstractField.bounded_by AbstractField.tight_bounds
             bls24_Fp_repr Field.bounded_by Field.tight_bounds
             BLS24_509_Instances.bls24_frep field_representation
             Signature.field_representation Representation.frep] in Hs;
        destruct Hs as [Hs _];
        apply WordByWordMontgomery.WordByWordMontgomery.length_small in Hs;
        rewrite map_length in Hs; exact Hs.

      (* Lengths from tight-bounded from_word results *)
      assert (Hlen3  : length fw3  = Fp_fsw) by len_from_tight_bnd Hbound3.
      assert (Hlen4  : length fw4  = Fp_fsw) by len_from_tight_bnd Hbound4.
      assert (Hlen5  : length fw5  = Fp_fsw) by len_from_tight_bnd Hbound5.
      assert (Hlen6  : length fw6  = Fp_fsw) by len_from_tight_bnd Hbound6.
      assert (Hlen9  : length fw9  = Fp_fsw) by len_from_tight_bnd Hbound9.
      assert (Hlen10 : length fw10 = Fp_fsw) by len_from_tight_bnd Hbound10.
      assert (Hlen11 : length fw11 = Fp_fsw) by len_from_tight_bnd Hbound11.
      assert (Hlen12 : length fw12 = Fp_fsw) by len_from_tight_bnd Hbound12.
      assert (Hlen14 : length fw14 = Fp_fsw) by len_from_tight_bnd Hbound14.
      assert (Hlen15 : length fw15 = Fp_fsw) by len_from_tight_bnd Hbound15.
      assert (Hlen16 : length fw16 = Fp_fsw) by len_from_tight_bnd Hbound16.
      assert (Hlen17 : length fw17 = Fp_fsw) by len_from_tight_bnd Hbound17.
      assert (Hlen18 : length fw18 = Fp_fsw) by len_from_tight_bnd Hbound18.
      assert (Hlen19 : length fw19 = Fp_fsw) by len_from_tight_bnd Hbound19.
      assert (Hlen20 : length fw20 = Fp_fsw) by len_from_tight_bnd Hbound20.

      (* Lengths of Fp4 sub-call results (from sep) *)
      assert (Hlen_out2 : length out2 = Fp4_fsw).
      { eassert (Hsep_out2 : (FElem_Fp4 pout out2 * _)%sep m_rest).
        { pose proof Hrest as H'. SeparationLogic.ecancel_assumption_impl. }
        destruct Hsep_out2 as [m_o2 [_ [_ [Hbare_o2 _]]]].
        exact (generic_FElem_length _ _ _ Hbare_o2). }
      assert (Hlen_out8 : length out8 = Fp4_fsw).
      { eassert (Hsep_out8 : (FElem_Fp4 (word.add pout fp8_off) out8 * _)%sep m_rest).
        { pose proof Hrest as H'. SeparationLogic.ecancel_assumption_impl. }
        destruct Hsep_out8 as [m_o8 [_ [_ [Hbare_o8 _]]]].
        exact (generic_FElem_length _ _ _ Hbare_o8). }
      assert (Hlen_yp : length yp = Fp_fsw).
      { eassert (Hsep_yp : (FElem_Fp pyp yp * _)%sep m_rest).
        { pose proof Hrest as H'. SeparationLogic.ecancel_assumption_impl. }
        destruct Hsep_yp as [m_yp2 [_ [_ [Hbare_yp _]]]].
        exact (generic_FElem_length _ _ _ Hbare_yp). }

      (* Fp2 lengths *)
      Local Ltac ml_mk_fp2_len Ha Hb :=
        rewrite app_length, Ha, Hb;
        change Fp2_fsw with (2 * Fp_fsw)%nat; lia.
      assert (Hl34   : length (fw3 ++ fw4)   = Fp2_fsw) by ml_mk_fp2_len Hlen3  Hlen4.
      assert (Hl56   : length (fw5 ++ fw6)   = Fp2_fsw) by ml_mk_fp2_len Hlen5  Hlen6.
      assert (Hl910  : length (fw9 ++ fw10)  = Fp2_fsw) by ml_mk_fp2_len Hlen9  Hlen10.
      assert (Hl1112 : length (fw11 ++ fw12) = Fp2_fsw) by ml_mk_fp2_len Hlen11 Hlen12.
      assert (Hlyp14 : length (yp ++ fw14)   = Fp2_fsw) by ml_mk_fp2_len Hlen_yp Hlen14.
      assert (Hl1516 : length (fw15 ++ fw16) = Fp2_fsw) by ml_mk_fp2_len Hlen15 Hlen16.
      assert (Hl1718 : length (fw17 ++ fw18) = Fp2_fsw) by ml_mk_fp2_len Hlen17 Hlen18.
      assert (Hl1920 : length (fw19 ++ fw20) = Fp2_fsw) by ml_mk_fp2_len Hlen19 Hlen20.

      (* Fp4 lengths *)
      Local Ltac ml_mk_fp4_len Ha Hb :=
        rewrite app_length, Ha, Hb;
        change Fp4_fsw with (2 * Fp2_fsw)%nat; lia.
      assert (Hlc0c1 : length ((fw3 ++ fw4) ++ fw5 ++ fw6) = Fp4_fsw)
        by ml_mk_fp4_len Hl34 Hl56.
      assert (Hlc1c1 : length ((fw9 ++ fw10) ++ fw11 ++ fw12) = Fp4_fsw)
        by ml_mk_fp4_len Hl910 Hl1112.
      assert (Hlc2c0 : length ((yp ++ fw14) ++ fw15 ++ fw16) = Fp4_fsw)
        by ml_mk_fp4_len Hlyp14 Hl1516.
      assert (Hlc2c1 : length ((fw17 ++ fw18) ++ fw19 ++ fw20) = Fp4_fsw)
        by ml_mk_fp4_len Hl1718 Hl1920.

      (* Fp8 lengths *)
      Local Ltac ml_mk_fp8_len Ha Hb :=
        rewrite app_length, Ha, Hb;
        change Fp8_fsw with (2 * Fp4_fsw)%nat; lia.
      assert (Hlc0 : length (out2 ++ (fw3 ++ fw4) ++ fw5 ++ fw6) = Fp8_fsw)
        by ml_mk_fp8_len Hlen_out2 Hlc0c1.
      assert (Hlc1 : length (out8 ++ (fw9 ++ fw10) ++ fw11 ++ fw12) = Fp8_fsw)
        by ml_mk_fp8_len Hlen_out8 Hlc1c1.
      assert (Hlc2 : length (((yp ++ fw14) ++ fw15 ++ fw16) ++ (fw17 ++ fw18) ++ fw19 ++ fw20) = Fp8_fsw)
        by ml_mk_fp8_len Hlc2c0 Hlc2c1.

      (* === (a) Join Fp pairs → Fp2 === *)
      eassert (Hj34 : (FElem_Fp (word.add pout fp4_off) fw3 *
        (FElem_Fp (word.add (word.add pout fp4_off) fp_off) fw4 * _))%sep m_rest).
      { pose proof Hrest as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj34; [| exact Hlen3 | exact Hlen4].
      eassert (Hj56 : (FElem_Fp (word.add (word.add pout fp4_off) fp2_off) fw5 *
        (FElem_Fp (word.add (word.add (word.add pout fp4_off) fp2_off) fp_off) fw6 * _))%sep m_rest).
      { pose proof Hj34 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj56; [| exact Hlen5 | exact Hlen6].
      eassert (Hj910 : (FElem_Fp (word.add (word.add pout fp8_off) fp4_off) fw9 *
        (FElem_Fp (word.add (word.add (word.add pout fp8_off) fp4_off) fp_off) fw10 * _))%sep m_rest).
      { pose proof Hj56 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj910; [| exact Hlen9 | exact Hlen10].
      eassert (Hj1112 : (FElem_Fp (word.add (word.add (word.add pout fp8_off) fp4_off) fp2_off) fw11 *
        (FElem_Fp (word.add (word.add (word.add (word.add pout fp8_off) fp4_off) fp2_off) fp_off) fw12 * _))%sep m_rest).
      { pose proof Hj910 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj1112; [| exact Hlen11 | exact Hlen12].
      eassert (Hjyp14 : (FElem_Fp p_c2 yp *
        (FElem_Fp (word.add p_c2 fp_off) fw14 * _))%sep m_rest).
      { pose proof Hj1112 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hjyp14; [| exact Hlen_yp | exact Hlen14].
      eassert (Hj1516 : (FElem_Fp (word.add p_c2 fp2_off) fw15 *
        (FElem_Fp (word.add (word.add p_c2 fp2_off) fp_off) fw16 * _))%sep m_rest).
      { pose proof Hjyp14 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj1516; [| exact Hlen15 | exact Hlen16].
      eassert (Hj1718 : (FElem_Fp (word.add p_c2 fp4_off) fw17 *
        (FElem_Fp (word.add (word.add p_c2 fp4_off) fp_off) fw18 * _))%sep m_rest).
      { pose proof Hj1516 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj1718; [| exact Hlen17 | exact Hlen18].
      eassert (Hj1920 : (FElem_Fp (word.add (word.add p_c2 fp4_off) fp2_off) fw19 *
        (FElem_Fp (word.add (word.add (word.add p_c2 fp4_off) fp2_off) fp_off) fw20 * _))%sep m_rest).
      { pose proof Hj1718 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp_join_in_sep in Hj1920; [| exact Hlen19 | exact Hlen20].

      (* === (b) Join Fp2 pairs → Fp4 === *)
      eassert (Hjc0c1 : (FElem_Fp2 (word.add pout fp4_off) (fw3 ++ fw4) *
        (FElem_Fp2 (word.add (word.add pout fp4_off) fp2_off) (fw5 ++ fw6) * _))%sep m_rest).
      { pose proof Hj1920 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_join_in_sep in Hjc0c1; [| exact Hl34 | exact Hl56].
      eassert (Hjc1c1 : (FElem_Fp2 (word.add (word.add pout fp8_off) fp4_off) (fw9 ++ fw10) *
        (FElem_Fp2 (word.add (word.add (word.add pout fp8_off) fp4_off) fp2_off) (fw11 ++ fw12) * _))%sep m_rest).
      { pose proof Hjc0c1 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_join_in_sep in Hjc1c1; [| exact Hl910 | exact Hl1112].
      eassert (Hjc2c0 : (FElem_Fp2 p_c2 (yp ++ fw14) *
        (FElem_Fp2 (word.add p_c2 fp2_off) (fw15 ++ fw16) * _))%sep m_rest).
      { pose proof Hjc1c1 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_join_in_sep in Hjc2c0; [| exact Hlyp14 | exact Hl1516].
      eassert (Hjc2c1 : (FElem_Fp2 (word.add p_c2 fp4_off) (fw17 ++ fw18) *
        (FElem_Fp2 (word.add (word.add p_c2 fp4_off) fp2_off) (fw19 ++ fw20) * _))%sep m_rest).
      { pose proof Hjc2c0 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp2_join_in_sep in Hjc2c1; [| exact Hl1718 | exact Hl1920].

      (* === (c) Join Fp4 pairs → Fp8 === *)
      eassert (Hjfp8c0 : (FElem_Fp4 pout out2 *
        (FElem_Fp4 (word.add pout fp4_off) ((fw3 ++ fw4) ++ fw5 ++ fw6) * _))%sep m_rest).
      { pose proof Hjc2c1 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp4_join_in_sep in Hjfp8c0; [| exact Hlen_out2 | exact Hlc0c1].
      eassert (Hjfp8c1 : (FElem_Fp4 (word.add pout fp8_off) out8 *
        (FElem_Fp4 (word.add (word.add pout fp8_off) fp4_off) ((fw9 ++ fw10) ++ fw11 ++ fw12) * _))%sep m_rest).
      { pose proof Hjfp8c0 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp4_join_in_sep in Hjfp8c1; [| exact Hlen_out8 | exact Hlc1c1].
      eassert (Hjfp8c2 : (FElem_Fp4 p_c2 ((yp ++ fw14) ++ fw15 ++ fw16) *
        (FElem_Fp4 (word.add p_c2 fp4_off) ((fw17 ++ fw18) ++ fw19 ++ fw20) * _))%sep m_rest).
      { pose proof Hjfp8c1 as H'. SeparationLogic.ecancel_assumption_impl. }
      apply FElem_Fp4_join_in_sep in Hjfp8c2; [| exact Hlc2c0 | exact Hlc2c1].

      (* === (d) CE join: 3 Fp8 → Fp24 === *)
      eassert (Hjfp24 :
        (FElem_Fp8 pout (out2 ++ (fw3 ++ fw4) ++ fw5 ++ fw6) *
         (FElem_Fp8 (word.add pout fp8_off) (out8 ++ (fw9 ++ fw10) ++ fw11 ++ fw12) *
          (FElem_Fp8 p_c2 (((yp ++ fw14) ++ fw15 ++ fw16) ++ (fw17 ++ fw18) ++ fw19 ++ fw20) *
           (FElem_Fp4 plam lam *
            (FElem_Fp4 pxt xt *
             (FElem_Fp4 pyt yt *
              (FElem_Fp pxp xp *
               (FElem_Fp pyp yp * Rr))))))))%sep m_rest).
      { pose proof Hjfp8c2 as H'. SeparationLogic.ecancel_assumption_impl. }
      pose proof (ce_raw_FElem_join_in_sep
        BLS24_509_Instances.bls24_Fp8_mul_by_w_model "bls24_Fp24_" BLS24_509_Instances.Fp8_eq_dec
        pout _ _ _
        (FElem_Fp4 plam lam *
         (FElem_Fp4 pxt xt *
          (FElem_Fp4 pyt yt *
           (FElem_Fp pxp xp *
            (FElem_Fp pyp yp * Rr)))))%sep
        m_rest Hlc0 Hlc1 Hlc2 Hjfp24)
        as Hfp24_sep.

      (* === (e) Provide witness the_out and prove Fp24_bounded Fp24_loose === *)
      set (the_out := (out2 ++ (fw3 ++ fw4) ++ fw5 ++ fw6) ++
                      (out8 ++ (fw9 ++ fw10) ++ fw11 ++ fw12) ++
                      (((yp ++ fw14) ++ fw15 ++ fw16) ++ (fw17 ++ fw18) ++ fw19 ++ fw20)).
      exists the_out.
      split.
      { (* Fp24_bounded Fp24_loose the_out *)
        (* Step 1: Extract CE components via firstn/skipn *)
        assert (Hce0 : fp8_fst the_out = out2 ++ (fw3 ++ fw4) ++ fw5 ++ fw6).
        { subst the_out. unfold fp8_fst, ce_c0_felem. apply firstn_app_le. exact Hlc0. }
        assert (Hce12 : skipn (@AbstractField.felem_size_in_words _ _ _ _ _ _ bls24_Fp8_repr) the_out =
            (out8 ++ (fw9 ++ fw10) ++ fw11 ++ fw12) ++
            ((yp ++ fw14) ++ fw15 ++ fw16) ++ (fw17 ++ fw18) ++ fw19 ++ fw20).
        { subst the_out. apply skipn_app_le. exact Hlc0. }
        assert (Hce1 : fp8_c1 the_out = out8 ++ (fw9 ++ fw10) ++ fw11 ++ fw12).
        { unfold fp8_c1, ce_c1_felem. rewrite Hce12. apply firstn_app_le. exact Hlc1. }
        assert (Hce2 : fp8_c2 the_out =
            ((yp ++ fw14) ++ fw15 ++ fw16) ++ (fw17 ++ fw18) ++ fw19 ++ fw20).
        { unfold fp8_c2, ce_c2_felem.
          set (n := @AbstractField.felem_size_in_words _ bls24_Fp8_params _ _ _ _ bls24_Fp8_repr) in *.
          replace (2 * n)%nat with (n + n)%nat by lia.
          rewrite <- List.skipn_skipn. subst the_out.
          rewrite (skipn_app_le _ _ _ Hlc0).
          apply skipn_app_le. exact Hlc1. }
        (* Step 2: Unfold bounded_by and rewrite CE components *)
        cbv [Fp24_bounded Fp24_loose AbstractField.bounded_by AbstractField.loose_bounds
             bls24_Fp24_repr bls24_Fp24_params
             CE_field_representation CE_field_parameters].
        cbv beta.
        (* Relax helpers *)
        pose proof (fun x (H : Fp_bounded (@AbstractField.tight_bounds _ _ _ _ _ _ bls24_Fp_repr) x) =>
          @AbstractField.relax_bounds _ _ _ _ _ _ bls24_Fp_repr bls24_Fp_repr_ok x H) as RBfp.
        pose proof (fun x (H : Fp2_bounded Fp2_tight x) =>
          @AbstractField.relax_bounds _ _ _ _ _ _ bls24_Fp2_repr bls24_Fp2_repr_ok x H) as RBfp2.
        pose proof (fun x (H : Fp4_bounded Fp4_tight x) =>
          @AbstractField.relax_bounds _ _ _ _ _ _ bls24_Fp4_repr bls24_Fp4_repr_ok x H) as RBfp4.
        (* Pre-build Fp2_bounded loose for each Fp pair from from_word results *)
        assert (Hb2_34 : Fp2_bounded Fp2_loose (fw3 ++ fw4)).
        { apply RBfp2. cut (Fp_bounded tight_bounds (fp_fst (fw3++fw4)) /\ Fp_bounded tight_bounds (fp_snd (fw3++fw4))).
          { intro; assumption. } qe_bnd Hbound3 Hbound4 Hlen3. }
        assert (Hb2_56 : Fp2_bounded Fp2_loose (fw5 ++ fw6)).
        { apply RBfp2. cut (Fp_bounded tight_bounds (fp_fst (fw5++fw6)) /\ Fp_bounded tight_bounds (fp_snd (fw5++fw6))).
          { intro; assumption. } qe_bnd Hbound5 Hbound6 Hlen5. }
        assert (Hb2_910 : Fp2_bounded Fp2_loose (fw9 ++ fw10)).
        { apply RBfp2. cut (Fp_bounded tight_bounds (fp_fst (fw9++fw10)) /\ Fp_bounded tight_bounds (fp_snd (fw9++fw10))).
          { intro; assumption. } qe_bnd Hbound9 Hbound10 Hlen9. }
        assert (Hb2_1112 : Fp2_bounded Fp2_loose (fw11 ++ fw12)).
        { apply RBfp2. cut (Fp_bounded tight_bounds (fp_fst (fw11++fw12)) /\ Fp_bounded tight_bounds (fp_snd (fw11++fw12))).
          { intro; assumption. } qe_bnd Hbound11 Hbound12 Hlen11. }
        assert (Hb2_yp14 : Fp2_bounded Fp2_loose (yp ++ fw14)).
        { cut (Fp_bounded Fp_loose (fp_fst (yp++fw14)) /\ Fp_bounded Fp_loose (fp_snd (yp++fw14))).
          { intro; assumption. } qe_bnd Hbyp (RBfp _ Hbound14) Hlen_yp. }
        assert (Hb2_1516 : Fp2_bounded Fp2_loose (fw15 ++ fw16)).
        { apply RBfp2. cut (Fp_bounded tight_bounds (fp_fst (fw15++fw16)) /\ Fp_bounded tight_bounds (fp_snd (fw15++fw16))).
          { intro; assumption. } qe_bnd Hbound15 Hbound16 Hlen15. }
        assert (Hb2_1718 : Fp2_bounded Fp2_loose (fw17 ++ fw18)).
        { apply RBfp2. cut (Fp_bounded tight_bounds (fp_fst (fw17++fw18)) /\ Fp_bounded tight_bounds (fp_snd (fw17++fw18))).
          { intro; assumption. } qe_bnd Hbound17 Hbound18 Hlen17. }
        assert (Hb2_1920 : Fp2_bounded Fp2_loose (fw19 ++ fw20)).
        { apply RBfp2. cut (Fp_bounded tight_bounds (fp_fst (fw19++fw20)) /\ Fp_bounded tight_bounds (fp_snd (fw19++fw20))).
          { intro; assumption. } qe_bnd Hbound19 Hbound20 Hlen19. }
        (* Pre-build Fp4_bounded loose for zero Fp4 sub-components *)
        assert (Hb4_c0z : Fp4_bounded Fp4_loose ((fw3++fw4) ++ fw5++fw6)).
        { apply RBfp4. cut (Fp2_bounded Fp2_tight (fp2_fst ((fw3++fw4)++fw5++fw6)) /\ Fp2_bounded Fp2_tight (fp2_snd ((fw3++fw4)++fw5++fw6))).
          { intro; assumption. }
          assert (Hb2_34t : Fp2_bounded Fp2_tight (fw3++fw4)).
          { cut (Fp_bounded tight_bounds (fp_fst (fw3++fw4)) /\ Fp_bounded tight_bounds (fp_snd (fw3++fw4))).
            { intro; assumption. } qe_bnd Hbound3 Hbound4 Hlen3. }
          assert (Hb2_56t : Fp2_bounded Fp2_tight (fw5++fw6)).
          { cut (Fp_bounded tight_bounds (fp_fst (fw5++fw6)) /\ Fp_bounded tight_bounds (fp_snd (fw5++fw6))).
            { intro; assumption. } qe_bnd Hbound5 Hbound6 Hlen5. }
          qe_bnd Hb2_34t Hb2_56t Hl34. }
        assert (Hb4_c1z : Fp4_bounded Fp4_loose ((fw9++fw10) ++ fw11++fw12)).
        { apply RBfp4. cut (Fp2_bounded Fp2_tight (fp2_fst ((fw9++fw10)++fw11++fw12)) /\ Fp2_bounded Fp2_tight (fp2_snd ((fw9++fw10)++fw11++fw12))).
          { intro; assumption. }
          assert (Hb2_910t : Fp2_bounded Fp2_tight (fw9++fw10)).
          { cut (Fp_bounded tight_bounds (fp_fst (fw9++fw10)) /\ Fp_bounded tight_bounds (fp_snd (fw9++fw10))).
            { intro; assumption. } qe_bnd Hbound9 Hbound10 Hlen9. }
          assert (Hb2_1112t : Fp2_bounded Fp2_tight (fw11++fw12)).
          { cut (Fp_bounded tight_bounds (fp_fst (fw11++fw12)) /\ Fp_bounded tight_bounds (fp_snd (fw11++fw12))).
            { intro; assumption. } qe_bnd Hbound11 Hbound12 Hlen11. }
          qe_bnd Hb2_910t Hb2_1112t Hl910. }
        assert (Hb4_c2c0 : Fp4_bounded Fp4_loose ((yp++fw14) ++ fw15++fw16)).
        { cut (Fp2_bounded Fp2_loose (fp2_fst ((yp++fw14)++fw15++fw16)) /\ Fp2_bounded Fp2_loose (fp2_snd ((yp++fw14)++fw15++fw16))).
          { intro; assumption. }
          qe_bnd Hb2_yp14 Hb2_1516 Hlyp14. }
        assert (Hb4_c2c1 : Fp4_bounded Fp4_loose ((fw17++fw18) ++ fw19++fw20)).
        { apply RBfp4. cut (Fp2_bounded Fp2_tight (fp2_fst ((fw17++fw18)++fw19++fw20)) /\ Fp2_bounded Fp2_tight (fp2_snd ((fw17++fw18)++fw19++fw20))).
          { intro; assumption. }
          assert (Hb2_1718t : Fp2_bounded Fp2_tight (fw17++fw18)).
          { cut (Fp_bounded tight_bounds (fp_fst (fw17++fw18)) /\ Fp_bounded tight_bounds (fp_snd (fw17++fw18))).
            { intro; assumption. } qe_bnd Hbound17 Hbound18 Hlen17. }
          assert (Hb2_1920t : Fp2_bounded Fp2_tight (fw19++fw20)).
          { cut (Fp_bounded tight_bounds (fp_fst (fw19++fw20)) /\ Fp_bounded tight_bounds (fp_snd (fw19++fw20))).
            { intro; assumption. } qe_bnd Hbound19 Hbound20 Hlen19. }
          qe_bnd Hb2_1718t Hb2_1920t Hl1718. }
        (* Pre-build Fp8_bounded loose for the 3 Fp8 components *)
        assert (Hb8_c0 : Fp8_bounded Fp8_loose (out2 ++ (fw3++fw4) ++ fw5++fw6)).
        { cut (Fp4_bounded Fp4_loose (fp4_fst (out2 ++ (fw3++fw4)++fw5++fw6)) /\
               Fp4_bounded Fp4_loose (fp4_snd (out2 ++ (fw3++fw4)++fw5++fw6))).
          { intro; assumption. }
          qe_bnd Hbound2 Hb4_c0z Hlen_out2. }
        assert (Hb8_c1 : Fp8_bounded Fp8_loose (out8 ++ (fw9++fw10) ++ fw11++fw12)).
        { cut (Fp4_bounded Fp4_loose (fp4_fst (out8 ++ (fw9++fw10)++fw11++fw12)) /\
               Fp4_bounded Fp4_loose (fp4_snd (out8 ++ (fw9++fw10)++fw11++fw12))).
          { intro; assumption. }
          qe_bnd Hbound8 Hb4_c1z Hlen_out8. }
        assert (Hb8_c2 : Fp8_bounded Fp8_loose
            (((yp++fw14)++fw15++fw16) ++ (fw17++fw18)++fw19++fw20)).
        { cut (Fp4_bounded Fp4_loose (fp4_fst (((yp++fw14)++fw15++fw16)++(fw17++fw18)++fw19++fw20)) /\
               Fp4_bounded Fp4_loose (fp4_snd (((yp++fw14)++fw15++fw16)++(fw17++fw18)++fw19++fw20))).
          { intro; assumption. }
          qe_bnd Hb4_c2c0 Hb4_c2c1 Hlc2c0. }
        (* Close the bounded goal *)
        rewrite Hce0, Hce1, Hce2.
        split; [| split]; [exact Hb8_c0 | exact Hb8_c1 | exact Hb8_c2]. }
      { (* (f) Final sep: the_out is same as CE join result *)
        subst the_out.
        destruct Hfp24_sep as [m_fp24 [m_inp [[Heq24 Hd24] [Hfe24 Hinp]]]].
        exists m_fp24, m_inp.
        split; [split; [exact Heq24 | exact Hd24] |].
        split; [exact Hfe24 | exact Hinp]. }
    Qed.


End BLS24_PairingHelpers.
