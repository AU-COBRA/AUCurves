(** * BLS12-381 final exponentiation, hard part: functional WP proof

    Functional version of [bls12_final_exp_hard_dsd_ok] (BLS12_FinalExpHardDSD.v).
    Callee specs are hypotheses, with their feval equalities:
    Fp12 mul / conjugate (binop_spec / unop_spec, as before), the Frobenius maps
    (feval out = Pairing.fp12_frobenius(_p2) of the fevals, the conjunct of
    PairingFieldOps.spec_of_Fp12_frobenius(_p2)), the loaders (feval = the constants
    of BLS12_FrobConstants.v, as proved in BLS12_LoadersFeval.v) and the cyclotomic
    exponentiations (BLS12_CycExpFunctional.v), whose Granger-Scott squaring needs the
    subgroup of order p^4 - p^2 + 1 ([CyclotomicGS.gs], closed under the steps of the
    chain: [CyclotomicGS.gs_step_*]).

      bls12_final_exp_hard_dsd_functional_ok : post (besides bounds and frame)
        CyclotomicGS.gs (feval f) ->
        feval out = Pairing.final_exp_hard_dsd p gamma1_381 gamma2_381
                      (feval g1p2) (feval g2p2) c1_381 (feval wp2) (feval f)
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


Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExpHardDSD.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.Frob381.
Require Import Theory.BLS12Pairing.CycExpModel.
Require Theory.BLS12Pairing.CyclotomicGS.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FrobConstants.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FinalExpModel381.
Require Theory.BLS12Pairing.Pairing.
Require Bedrock.Field.Synthesis.Examples.BLS12_PairingFevalInst.
Module P := Theory.BLS12Pairing.Pairing.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Record hidden (P : Prop) : Prop := hide { unhide : P }.

Section BLS12_FinalExpHardDSDFunctional.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Existing Instance BLS12_FinalExpHardDSD.bls12_pf_params.
    Existing Instance BLS12_FinalExpHardDSD.bls12_pf_params_ok.
    Existing Instance prime_field_parameters.
    Existing Instance BLS12_FinalExpHardDSD.bls12_Fp_rep.
    Existing Instance BLS12_FinalExpHardDSD.bls12_Fp_rep_ok.

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

    Existing Instance BLS12_FinalExpHardDSD.bls12_Fp2_params'.
    Existing Instance BLS12_FinalExpHardDSD.bls12_Fp2_rep'.
    Existing Instance BLS12_FinalExpHardDSD.bls12_Fp6_params'.
    Existing Instance BLS12_FinalExpHardDSD.bls12_Fp6_rep'.
    Existing Instance BLS12_FinalExpHardDSD.bls12_Fp12_params'.
    Existing Instance BLS12_FinalExpHardDSD.bls12_Fp12_rep'.

    Local Notation bls12_Fp_rep := BLS12_FinalExpHardDSD.bls12_Fp_rep.
    Local Notation bls12_pf_params := BLS12_FinalExpHardDSD.bls12_pf_params.
    Local Notation bls12_Fp2_params' := BLS12_FinalExpHardDSD.bls12_Fp2_params'.
    Local Notation bls12_Fp2_rep' := BLS12_FinalExpHardDSD.bls12_Fp2_rep'.
    Local Notation bls12_Fp12_params' := BLS12_FinalExpHardDSD.bls12_Fp12_params'.
    Local Notation bls12_Fp12_rep' := BLS12_FinalExpHardDSD.bls12_Fp12_rep'.

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
    Local Typeclasses Opaque BLS12_FinalExpHardDSD.bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    Local Instance bls12_Fp12_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp12_params' _ _ _ _ bls12_Fp12_rep' :=
      BLS12_FinalExpHardDSD.bls12_Fp12_rep_ok'.
    Local Instance bls12_Fp2_rep_ok'' :
      @AbstractField.FieldRepresentation_ok _ bls12_Fp2_params' _ _ _ _ bls12_Fp2_rep' :=
      BLS12_FinalExpHardDSD.bls12_Fp2_rep_ok'.

    (* ================================================================ *)
    (* Functional callee specs                                          *)
    (* ================================================================ *)

    Let fp12_frobenius_name : string := (fp12_prefix ++ "frobenius")%string.
    Definition spec_of_Fp12_frobenius_functional : spec_of fp12_frobenius_name :=
      fnspec! fp12_frobenius_name
        (pout px pgamma1 pgamma2 pw_frob_c1 : word)
        / (old_out x : Fp12_felem) (gamma1 gamma2 w_frob_c1 : Fp2_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight x /\
          Fp2_bounded Fp2_loose gamma1 /\
          Fp2_bounded Fp2_loose gamma2 /\
          Fp2_bounded Fp2_loose w_frob_c1 /\
          (FElem_Fp12 px x ⋆ (FElem_Fp2 pgamma1 gamma1 ⋆
            (FElem_Fp2 pgamma2 gamma2 ⋆
             (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆
              (FElem_Fp12 pout old_out ⋆ Rr))))) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_feval out = P.fp12_frobenius PrimeField.M_pos
              (Fp2_feval gamma1) (Fp2_feval gamma2) (Fp2_feval w_frob_c1) (Fp12_feval x) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 px x ⋆
              (FElem_Fp2 pgamma1 gamma1 ⋆
               (FElem_Fp2 pgamma2 gamma2 ⋆
                (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ Rr))))) mem' }.

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

    Definition spec_of_cyc_exp_x_neg_functional : spec_of "bls12_Fp12_cyc_exp_x_neg" :=
      fnspec! "bls12_Fp12_cyc_exp_x_neg" (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            (CyclotomicGS.gs (Fp12_feval base_val) ->
             Fp12_feval out = P.fp12_pow_bls_x_signed PrimeField.M_pos (Fp12_feval base_val)) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    Definition spec_of_cyc_exp_c_neg_functional : spec_of "bls12_Fp12_cyc_exp_c_neg" :=
      fnspec! "bls12_Fp12_cyc_exp_c_neg" (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            (CyclotomicGS.gs (Fp12_feval base_val) ->
             Fp12_feval out = P.fp12_pow_bls_c_signed PrimeField.M_pos (Fp12_feval base_val)) /\
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    Definition spec_of_bls12_load_gamma1_functional : spec_of "bls12_load_gamma1" :=
      fnspec! "bls12_load_gamma1" (pout : word) / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists v,
          Fp2_feval v = BLS12_381_Frob.frob_gamma1 /\
          Fp2_bounded Fp2_tight v /\ (FElem_Fp2 pout v ⋆ Rr) mem' }.
    Definition spec_of_bls12_load_gamma2_functional : spec_of "bls12_load_gamma2" :=
      fnspec! "bls12_load_gamma2" (pout : word) / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists v,
          Fp2_feval v = BLS12_381_Frob.frob_gamma2 /\
          Fp2_bounded Fp2_tight v /\ (FElem_Fp2 pout v ⋆ Rr) mem' }.
    Definition spec_of_bls12_load_w_frob_c1_functional : spec_of "bls12_load_w_frob_c1" :=
      fnspec! "bls12_load_w_frob_c1" (pout : word) / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists v,
          Fp2_feval v = BLS12_381_Frob.frob_coeff_fp12_c1 /\
          Fp2_bounded Fp2_tight v /\ (FElem_Fp2 pout v ⋆ Rr) mem' }.

    (* The functional spec of the hard part *)
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

    (* Models of Fp12 mul / conjugate in Pairing.v terms *)
    Lemma F12mul_eq' (o a b : Fp12) :
      o = @AbstractField.Fmul _ bls12_Fp12_params' a b -> o = P.fp12_mul PrimeField.M_pos a b.
    Proof. intros ->. exact (BLS12_PairingFevalInst.fp12_mul_eq_closed PrimeField.M_pos a b). Qed.

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

    Lemma bls12_final_exp_hard_dsd_functional_ok :
      forall functions
        (EnvContains : map.get functions "bls12_final_exp_hard_dsd" =
          Some (snd BLS12_Pairing.bls12_final_exp_hard_dsd))
        (HFp12mul : BLS12_FinalExpHardDSD.spec_of_Fp12_mul functions)
        (HFp12conj : BLS12_FinalExpHardDSD.spec_of_Fp12_conjugate functions)
        (HFp12frob : spec_of_Fp12_frobenius_functional functions)
        (HFp12frobp2 : spec_of_Fp12_frobenius_p2_functional functions)
        (HFexpx : spec_of_cyc_exp_x_neg_functional functions)
        (HFexpc : spec_of_cyc_exp_c_neg_functional functions)
        (HFloadg1 : spec_of_bls12_load_gamma1_functional functions)
        (HFloadg2 : spec_of_bls12_load_gamma2_functional functions)
        (HFloadw : spec_of_bls12_load_w_frob_c1_functional functions),
      spec_of_bls12_final_exp_hard_dsd_functional functions.
    Proof.
      intros. unfold spec_of_bls12_final_exp_hard_dsd_functional.
      intros pout pf pg1p2 pg2p2 pwp2 old_out f_val g1p2 g2p2 wp2 Rr tr mem0
        [Hbf [Hbg1p2 [Hbg2p2 [Hbwp2 Hsep]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold BLS12_Pairing.bls12_final_exp_hard_dsd. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }

      straightline. split. { apply Z_mod_mult. }
      intros a_t0 mS_t0 mC_t0 HaS_t0 HmS_t0.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_t0 mS_t0) HaS_t0) as [t0i Ht0i].
      straightline. split. { apply Z_mod_mult. }
      intros a_t1 mS_t1 mC_t1 HaS_t1 HmS_t1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_t1 mS_t1) HaS_t1) as [t1i Ht1i].
      straightline. split. { apply Z_mod_mult. }
      intros a_t2 mS_t2 mC_t2 HaS_t2 HmS_t2.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_t2 mS_t2) HaS_t2) as [t2i Ht2i].
      straightline. split. { apply Z_mod_mult. }
      intros a_g1 mS_g1 mC_g1 HaS_g1 HmS_g1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _
        bls12_Fp2_rep' wordok mapok a_g1 mS_g1) HaS_g1) as [g1i Hg1i].
      straightline. split. { apply Z_mod_mult. }
      intros a_g2 mS_g2 mC_g2 HaS_g2 HmS_g2.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _
        bls12_Fp2_rep' wordok mapok a_g2 mS_g2) HaS_g2) as [g2i Hg2i].
      straightline. split. { apply Z_mod_mult. }
      intros a_w mS_w mC_w HaS_w HmS_w.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _
        bls12_Fp2_rep' wordok mapok a_w mS_w) HaS_w) as [wi Hwi].

      unfold BLS12_Pairing.final_exp_hard_dsd_body, BLS12_Pairing.cmd_seq_list.

      pose proof (proj1 (map.split_comm mC_t0 mem0 mS_t0) HmS_t0) as HmS_t0'.
      assert (Hl_t0 : (FElem_Fp12 a_t0 t0i ⋆ (FElem_Fp12 pf f_val ⋆ (FElem_Fp2 pg1p2 g1p2 ⋆ (FElem_Fp2 pg2p2 g2p2 ⋆ (FElem_Fp2 pwp2 wp2 ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))))) mC_t0).
      { exists mS_t0, mem0. exact (conj HmS_t0' (conj Ht0i Hsep)). }
      pose proof (proj1 (map.split_comm mC_t1 mC_t0 mS_t1) HmS_t1) as HmS_t1'.
      assert (Hl_t1 : (FElem_Fp12 a_t1 t1i ⋆ (FElem_Fp12 a_t0 t0i ⋆ (FElem_Fp12 pf f_val ⋆ (FElem_Fp2 pg1p2 g1p2 ⋆ (FElem_Fp2 pg2p2 g2p2 ⋆ (FElem_Fp2 pwp2 wp2 ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))))) mC_t1).
      { exists mS_t1, mC_t0. exact (conj HmS_t1' (conj Ht1i Hl_t0)). }
      pose proof (proj1 (map.split_comm mC_t2 mC_t1 mS_t2) HmS_t2) as HmS_t2'.
      assert (Hl_t2 : (FElem_Fp12 a_t2 t2i ⋆ (FElem_Fp12 a_t1 t1i ⋆ (FElem_Fp12 a_t0 t0i ⋆ (FElem_Fp12 pf f_val ⋆ (FElem_Fp2 pg1p2 g1p2 ⋆ (FElem_Fp2 pg2p2 g2p2 ⋆ (FElem_Fp2 pwp2 wp2 ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))))))) mC_t2).
      { exists mS_t2, mC_t1. exact (conj HmS_t2' (conj Ht2i Hl_t1)). }
      pose proof (proj1 (map.split_comm mC_g1 mC_t2 mS_g1) HmS_g1) as HmS_g1'.
      assert (Hl_g1 : (FElem_Fp2 a_g1 g1i ⋆ (FElem_Fp12 a_t2 t2i ⋆ (FElem_Fp12 a_t1 t1i ⋆ (FElem_Fp12 a_t0 t0i ⋆ (FElem_Fp12 pf f_val ⋆ (FElem_Fp2 pg1p2 g1p2 ⋆ (FElem_Fp2 pg2p2 g2p2 ⋆ (FElem_Fp2 pwp2 wp2 ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))))))) mC_g1).
      { exists mS_g1, mC_t2. exact (conj HmS_g1' (conj Hg1i Hl_t2)). }
      pose proof (proj1 (map.split_comm mC_g2 mC_g1 mS_g2) HmS_g2) as HmS_g2'.
      assert (Hl_g2 : (FElem_Fp2 a_g2 g2i ⋆ (FElem_Fp2 a_g1 g1i ⋆ (FElem_Fp12 a_t2 t2i ⋆ (FElem_Fp12 a_t1 t1i ⋆ (FElem_Fp12 a_t0 t0i ⋆ (FElem_Fp12 pf f_val ⋆ (FElem_Fp2 pg1p2 g1p2 ⋆ (FElem_Fp2 pg2p2 g2p2 ⋆ (FElem_Fp2 pwp2 wp2 ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))))))))) mC_g2).
      { exists mS_g2, mC_g1. exact (conj HmS_g2' (conj Hg2i Hl_g1)). }
      pose proof (proj1 (map.split_comm mC_w mC_g2 mS_w) HmS_w) as HmS_w'.
      assert (Hl_w : (FElem_Fp2 a_w wi ⋆ (FElem_Fp2 a_g2 g2i ⋆ (FElem_Fp2 a_g1 g1i ⋆ (FElem_Fp12 a_t2 t2i ⋆ (FElem_Fp12 a_t1 t1i ⋆ (FElem_Fp12 a_t0 t0i ⋆ (FElem_Fp12 pf f_val ⋆ (FElem_Fp2 pg1p2 g1p2 ⋆ (FElem_Fp2 pg2p2 g2p2 ⋆ (FElem_Fp2 pwp2 wp2 ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))))))))) mC_w).
      { exists mS_w, mC_g2. exact (conj HmS_w' (conj Hwi Hl_g2)). }
      clear Hsep Hl_t0 Hl_t1 Hl_t2 Hl_g1 Hl_g2
        HmS_t0 HmS_t1 HmS_t2 HmS_g1 HmS_g2 HmS_w HmS_t0' HmS_t1' HmS_t2' HmS_g1' HmS_g2' HmS_w'
        HaS_t0 HaS_t1 HaS_t2 HaS_g1 HaS_g2 HaS_w Ht0i Ht1i Ht2i Hg1i Hg2i Hwi.

      (* Call 1: load_gamma1(gamma1) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadg1. ecancel_assumption. }
      intros ? ? ? [? [? [g1_v [Lg1 [Hb_g1 Hsep_c1]]]]]. subst.
      rewrite frob_gamma1_381 in Lg1. apply hide in Lg1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 2: load_gamma2(gamma2) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadg2. ecancel_assumption. }
      intros ? ? ? [? [? [g2_v [Lg2 [Hb_g2 Hsep_c2]]]]]. subst.
      rewrite frob_gamma2_381 in Lg2. apply hide in Lg2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 3: load_w_frob_c1(w_frob_c1) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadw. ecancel_assumption. }
      intros ? ? ? [? [? [w_v [Lw [Hb_w Hsep_c3]]]]]. subst.
      rewrite frob_coeff_fp12_c1_381 in Lw. apply hide in Lw.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 4: cyc_exp_c_neg(t1, f): t1 = f^{-c} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpc.
           split; [exact Hbf |]. ecancel_assumption. }
      intros ? ? ? [? [? [a1 [E1 [Hb_a1 Hsep_c4]]]]]. subst. apply hide in E1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 5: cyc_exp_x_neg(t2, t1): t2 = f^{c|x|} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpx.
           split; [exact Hb_a1 |]. ecancel_assumption. }
      intros ? ? ? [? [? [a2 [E2 [Hb_a2 Hsep_c5]]]]]. subst. apply hide in E2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 6: conjugate(t1, t1): t1 = f^c *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_a1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a3 [E3 [Hb_a3 Hsep_c6]]]]]. subst.
      apply F12conj_eq' in E3. apply hide in E3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 7: mul(t1, t1, t2): t1 = A *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_a3 |].
           split; [exact Hb_a2 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a4 [E4 [Hb_a4 Hsep_c7]]]]]. subst.
      apply F12mul_eq' in E4. apply hide in E4.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 8: cyc_exp_x_neg(t2, t1): t2 = A^{-|x|} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpx.
           split; [exact Hb_a4 |]. ecancel_assumption. }
      intros ? ? ? [? [? [a5 [E5 [Hb_a5 Hsep_c8]]]]]. subst. apply hide in E5.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 9: frobenius(t0, t1, gamma1, gamma2, w_frob_c1): t0 = A^p *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_a4 |].
           split; [exact Hb_g1 |]. split; [exact Hb_g2 |]. split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [a6 [E6 [Hb_a6 Hsep_c9]]]]]. subst.
      rewrite (unhide _ Lg1), (unhide _ Lg2), (unhide _ Lw) in E6. apply hide in E6.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 10: mul(t1, t0, t2): t1 = B *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_a6 |].
           split; [exact Hb_a5 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a7 [E7 [Hb_a7 Hsep_c10]]]]]. subst.
      apply F12mul_eq' in E7. apply hide in E7.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 11: cyc_exp_x_neg(t0, t1): t0 = B^{-|x|} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpx.
           split; [exact Hb_a7 |]. ecancel_assumption. }
      intros ? ? ? [? [? [a8 [E8 [Hb_a8 Hsep_c11]]]]]. subst. apply hide in E8.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 12: cyc_exp_x_neg(t2, t0): t2 = B^{|x|^2} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpx.
           split; [exact Hb_a8 |]. ecancel_assumption. }
      intros ? ? ? [? [? [a9 [E9 [Hb_a9 Hsep_c12]]]]]. subst. apply hide in E9.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 13: frobenius_p2(t0, t1, gamma1_p2, gamma2_p2, w_frob_p2_c1): t0 = B^{p^2} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frobp2.
           split; [exact Hb_a7 |].
           split; [exact Hbg1p2 |]. split; [exact Hbg2p2 |]. split; [exact Hbwp2 |].
           ecancel_assumption. }
      intros ? ? ? [? [? [a10 [E10 [Hb_a10 Hsep_c13]]]]]. subst. apply hide in E10.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 14: conjugate(t1, t1): t1 = B^{-1} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_a7 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a11 [E11 [Hb_a11 Hsep_c14]]]]]. subst.
      apply F12conj_eq' in E11. apply hide in E11.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 15: mul(t1, t1, t2) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_a11 |].
           split; [exact Hb_a9 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a12 [E12 [Hb_a12 Hsep_c15]]]]]. subst.
      apply F12mul_eq' in E12. apply hide in E12.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 16: mul(t1, t1, t0) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_a12 |].
           split; [exact Hb_a10 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a13 [E13 [Hb_a13 Hsep_c16]]]]]. subst.
      apply F12mul_eq' in E13. apply hide in E13.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 17: mul(out, f, t1): out = f^{h3} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hbf |].
           split; [exact Hb_a13 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a14 [E14 [Hb_a14 Hsep_c17]]]]]. subst.
      apply F12mul_eq' in E14. apply hide in E14.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      do 3 dealloc_with constr:(FElem_Fp2).
      do 3 dealloc_with constr:(FElem_Fp12).

      cbv [list_map list_map_body WeakestPrecondition.get].
      split. { reflexivity. }
      split. { reflexivity. }
      exists a14.
      split.
      { intros Hcyc.
        apply unhide in E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14.
        specialize (E1 Hcyc).
        pose proof (CyclotomicGS.gs_step_cs _ _ Hcyc E1) as C1.
        specialize (E2 C1).
        pose proof (CyclotomicGS.gs_step_a4 _ _ _ _ C1 E2 E3 E4) as C4.
        specialize (E5 C4).
        pose proof (CyclotomicGS.gs_step_a7 _ _ _ _ C4 E5 E6 E7) as C7.
        specialize (E8 C7).
        pose proof (CyclotomicGS.gs_step_xs _ _ C7 E8) as C8.
        specialize (E9 C8).
        exact (hard_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14). }
      split. { exact Hb_a14. }
      ecancel_assumption.
    Qed.

End BLS12_FinalExpHardDSDFunctional.
