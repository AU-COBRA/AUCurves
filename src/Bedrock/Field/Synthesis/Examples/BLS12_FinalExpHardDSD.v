(** * BLS12-381 final exponentiation, hard part: WP proof

    Proves [bls12_final_exp_hard_dsd] (BLS12_Pairing.v) safe: 6 stackallocs and
    17 calls, the output bounded and the frame, including the input and the
    three Frobenius-p^2 constants, preserved.  The hard part computes f^{h3},
    h3 = (p^4-p^2+1)/r, by the chain
      h3 = 1 + (u^2-1+p^2) (u+1) ((u+1)/3) (p-u),  u = |x|
    (FinalExpEquiv.v, h3_exact_chain).  The exponentiations by |x| and by
    (u+1)/3 are the callees bls12_Fp12_cyc_exp_x_neg / _c_neg (BLS12_CycExp.v);
    their specs, like the other callee specs, are hypotheses.
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

Section BLS12_FinalExpHardDSD.


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

    Local Typeclasses Opaque bls12_Fp12_params'.
    Local Typeclasses Opaque bls12_Fp6_params'.
    Local Typeclasses Opaque bls12_Fp2_params'.

    (* === Callee specs === *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep') AbstractField.bin_mul.

    Let fp12_conjugate_name : string := (fp12_prefix ++ "conjugate")%string.
    Instance spec_of_Fp12_conjugate : spec_of fp12_conjugate_name :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls12_Fp12_rep')
        (@DodecicFieldExtensions.un_Fp12_conjugate _ _ _ _
          bls12_pf_params bls12_Fp_rep bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix).

    (* Frobenius and Frobenius-p^2: the shape of PairingFieldOps.spec_of_Fp12_frobenius
       without its functional conjunct *)
    Let fp12_frobenius_name : string := (fp12_prefix ++ "frobenius")%string.
    Instance spec_of_Fp12_frobenius : spec_of fp12_frobenius_name :=
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
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 px x ⋆
              (FElem_Fp2 pgamma1 gamma1 ⋆
               (FElem_Fp2 pgamma2 gamma2 ⋆
                (FElem_Fp2 pw_frob_c1 w_frob_c1 ⋆ Rr))))) mem' }.

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

    (* The two cyclotomic exponentiations (proved in BLS12_CycExp.v) *)
    Instance spec_of_cyc_exp_x_neg : spec_of "bls12_Fp12_cyc_exp_x_neg" :=
      fnspec! "bls12_Fp12_cyc_exp_x_neg" (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    Instance spec_of_cyc_exp_c_neg : spec_of "bls12_Fp12_cyc_exp_c_neg" :=
      fnspec! "bls12_Fp12_cyc_exp_c_neg" (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    (* Loaders of the Frobenius-p constants *)
    Instance spec_of_bls12_load_gamma1 : spec_of "bls12_load_gamma1" :=
      fnspec! "bls12_load_gamma1" (pout : word) / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists v,
          Fp2_bounded Fp2_loose v /\ (FElem_Fp2 pout v ⋆ Rr) mem' }.
    Instance spec_of_bls12_load_gamma2 : spec_of "bls12_load_gamma2" :=
      fnspec! "bls12_load_gamma2" (pout : word) / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists v,
          Fp2_bounded Fp2_loose v /\ (FElem_Fp2 pout v ⋆ Rr) mem' }.
    Instance spec_of_bls12_load_w_frob_c1 : spec_of "bls12_load_w_frob_c1" :=
      fnspec! "bls12_load_w_frob_c1" (pout : word) / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists v,
          Fp2_bounded Fp2_loose v /\ (FElem_Fp2 pout v ⋆ Rr) mem' }.

    (* Spec of the hard part: same frame shape as Frobenius-p^2 *)
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

    Lemma bls12_final_exp_hard_dsd_ok :
      forall functions
        (EnvContains : map.get functions "bls12_final_exp_hard_dsd" =
          Some (snd BLS12_Pairing.bls12_final_exp_hard_dsd))
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12conj : spec_of_Fp12_conjugate functions)
        (HFp12frob : spec_of_Fp12_frobenius functions)
        (HFp12frobp2 : spec_of_Fp12_frobenius_p2 functions)
        (HFexpx : spec_of_cyc_exp_x_neg functions)
        (HFexpc : spec_of_cyc_exp_c_neg functions)
        (HFloadg1 : spec_of_bls12_load_gamma1 functions)
        (HFloadg2 : spec_of_bls12_load_gamma2 functions)
        (HFloadw : spec_of_bls12_load_w_frob_c1 functions),
      spec_of_bls12_final_exp_hard_dsd functions.
    Proof.
      intros. unfold spec_of_bls12_final_exp_hard_dsd.
      intros pout pf pg1p2 pg2p2 pwp2 old_out f_val g1p2 g2p2 wp2 Rr tr mem0
        [Hbf [Hbg1p2 [Hbg2p2 [Hbwp2 Hsep]]]].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold BLS12_Pairing.bls12_final_exp_hard_dsd. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }

      (* Stackalloc 1: t0 *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t0 mS_t0 mC_t0 HaS_t0 HmS_t0.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_t0 mS_t0) HaS_t0) as [t0i Ht0i].

      (* Stackalloc 2: t1 *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t1 mS_t1 mC_t1 HaS_t1 HmS_t1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_t1 mS_t1) HaS_t1) as [t1i Ht1i].

      (* Stackalloc 3: t2 *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t2 mS_t2 mC_t2 HaS_t2 HmS_t2.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp12_params' _ _ _ _
        bls12_Fp12_rep' wordok mapok a_t2 mS_t2) HaS_t2) as [t2i Ht2i].

      (* Stackalloc 4: g1 *)
      straightline. split. { apply Z_mod_mult. }
      intros a_g1 mS_g1 mC_g1 HaS_g1 HmS_g1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _
        bls12_Fp2_rep' wordok mapok a_g1 mS_g1) HaS_g1) as [g1i Hg1i].

      (* Stackalloc 5: g2 *)
      straightline. split. { apply Z_mod_mult. }
      intros a_g2 mS_g2 mC_g2 HaS_g2 HmS_g2.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls12_Fp2_params' _ _ _ _
        bls12_Fp2_rep' wordok mapok a_g2 mS_g2) HaS_g2) as [g2i Hg2i].

      (* Stackalloc 6: w *)
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
      1: { eapply HFloadg1.
           ecancel_assumption. }
      intros ? ? ? [? [? [g1_v [Hb_g1 Hsep_c1]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 2: load_gamma2(gamma2) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadg2.
           ecancel_assumption. }
      intros ? ? ? [? [? [g2_v [Hb_g2 Hsep_c2]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 3: load_w_frob_c1(w_frob_c1) *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadw.
           ecancel_assumption. }
      intros ? ? ? [? [? [w_v [Hb_w Hsep_c3]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 4: cyc_exp_c_neg(t1, f): t1 = f^{-c} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpc.
           split; [exact Hbf |]. ecancel_assumption. }
      intros ? ? ? [? [? [a1 [Hb_a1 Hsep_c4]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 5: cyc_exp_x_neg(t2, t1): t2 = f^{c|x|} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpx.
           split; [exact Hb_a1 |]. ecancel_assumption. }
      intros ? ? ? [? [? [a2 [Hb_a2 Hsep_c5]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 6: conjugate(t1, t1): t1 = f^c *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_a1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a3 [Hfe_a3 [Hb_a3 Hsep_c6]]]]]. subst.
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
      intros ? ? ? [? [? [a4 [Hfe_a4 [Hb_a4 Hsep_c7]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 8: cyc_exp_x_neg(t2, t1): t2 = A^{-|x|} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpx.
           split; [exact Hb_a4 |]. ecancel_assumption. }
      intros ? ? ? [? [? [a5 [Hb_a5 Hsep_c8]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 9: frobenius(t0, t1, gamma1, gamma2, w_frob_c1): t0 = A^p *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_a4 |].
           split; [exact Hb_g1 |]. split; [exact Hb_g2 |]. split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [a6 [Hb_a6 Hsep_c9]]]]. subst.
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
      intros ? ? ? [? [? [a7 [Hfe_a7 [Hb_a7 Hsep_c10]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 11: cyc_exp_x_neg(t0, t1): t0 = B^{-|x|} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpx.
           split; [exact Hb_a7 |]. ecancel_assumption. }
      intros ? ? ? [? [? [a8 [Hb_a8 Hsep_c11]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 12: cyc_exp_x_neg(t2, t0): t2 = B^{|x|^2} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFexpx.
           split; [exact Hb_a8 |]. ecancel_assumption. }
      intros ? ? ? [? [? [a9 [Hb_a9 Hsep_c12]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 13: frobenius_p2(t0, t1, gamma1_p2, gamma2_p2, w_frob_p2_c1): t0 = B^{p^2} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frobp2.
           split; [exact Hb_a7 |].
           split; [exact Hbg1p2 |]. split; [exact Hbg2p2 |]. split; [exact Hbwp2 |].
           ecancel_assumption. }
      intros ? ? ? [? [? [a10 [Hb_a10 Hsep_c13]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Call 14: conjugate(t1, t1): t1 = B^{-1} *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_a7 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [a11 [Hfe_a11 [Hb_a11 Hsep_c14]]]]]. subst.
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
      intros ? ? ? [? [? [a12 [Hfe_a12 [Hb_a12 Hsep_c15]]]]]. subst.
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
      intros ? ? ? [? [? [a13 [Hfe_a13 [Hb_a13 Hsep_c16]]]]]. subst.
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
      intros ? ? ? [? [? [a14 [Hfe_a14 [Hb_a14 Hsep_c17]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* Stack deallocation, innermost first: w, g2, g1 (Fp2), t2, t1, t0 (Fp12) *)
      do 3 dealloc_with constr:(FElem_Fp2).
      do 3 dealloc_with constr:(FElem_Fp12).

      (* Postcondition *)
      cbv [list_map list_map_body WeakestPrecondition.get].
      split. { reflexivity. }
      split. { reflexivity. }
      exists a14.
      split. { exact Hb_a14. }
      ecancel_assumption.
    Qed.

End BLS12_FinalExpHardDSD.
