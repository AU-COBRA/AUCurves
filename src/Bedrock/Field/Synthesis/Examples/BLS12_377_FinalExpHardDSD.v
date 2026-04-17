(** * BLS12-377 DSD Final Exponentiation Hard Part WP Proof
    Proves bls377_final_exp_hard_dsd (25 calls, 7 stackallocs) satisfies its spec.
    The hard part computes f^{(p^4 - p^2 + 1)/r} using the DSD decomposition.
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
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_PowU.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BLS12_377_FinalExpHardDSD.

    (* === BLS12-377 Instance Boilerplate === *)
    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bls377_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_377_prime.m).

    Instance bls377_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls377_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls377_mul"; PrimeField.add := "bls377_add";
      PrimeField.sub := "bls377_sub"; PrimeField.opp := "bls377_opp";
      PrimeField.square := "bls377_square"; PrimeField.scmula24 := "bls377_scmula24";
      PrimeField.inv := "bls377_inv"; PrimeField.from_bytes := "bls377_from_bytes";
      PrimeField.to_bytes := "bls377_to_bytes"; PrimeField.select_znz := "bls377_select_znz";
      PrimeField.felem_copy := "bls377_felem_copy"; PrimeField.from_word := "bls377_from_word";
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

    Let bls377_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-5).
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

    (* === Abbreviations === *)
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep').
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep').
    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bls377_Fp12_params'.
    Local Typeclasses Opaque bls377_Fp6_params'.
    Local Typeclasses Opaque bls377_Fp2_params'.

    (* === Operation specs === *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bls377_Fp12_rep') AbstractField.bin_mul.
    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls377_Fp12_rep') AbstractField.un_square.
    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bls377_Fp12_rep').

    Let fp12_conjugate_name : string := (fp12_prefix ++ "conjugate")%string.
    Instance spec_of_Fp12_conjugate : spec_of fp12_conjugate_name :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bls377_Fp12_rep')
        (@DodecicFieldExtensions.un_Fp12_conjugate _ _ _ _
          bls377_pf_params bls377_Fp_rep bls377_beta bls377_xi_re bls377_xi_im fp12_prefix fp6_prefix fp2_prefix).

    Let fp12_frobenius_name : string := (fp12_prefix ++ "frobenius")%string.

    (* Frobenius spec — same shape as PairingFieldOps.spec_of_Fp12_frobenius,
       instantiated for BLS12-377 *)
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

    (* pow_u spec — normal (pout != pbase) *)
    Instance spec_of_pow_u : spec_of "bls377_Fp12_pow_u" :=
      fnspec! "bls377_Fp12_pow_u" (pout pbase : word)
        / (old_out base_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight base_val /\
          (FElem_Fp12 pbase base_val ⋆
           (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆
             (FElem_Fp12 pbase base_val ⋆ Rr)) mem' }.

    (* pow_u spec — in-place (pout = pbase) *)
    Definition spec_of_pow_u_inplace (functions : @map.rep String.string
      (list String.string * list String.string * Syntax.cmd.cmd) _) : Prop :=
      forall pbase (base_val : Fp12_felem) Rr tr mem,
        Fp12_bounded Fp12_tight base_val ->
        (FElem_Fp12 pbase base_val ⋆ Rr) mem ->
        WeakestPrecondition.call functions "bls377_Fp12_pow_u"
          tr mem [pbase; pbase]
          (fun tr' mem' rets =>
             rets = [] /\ tr = tr' /\ exists out,
               Fp12_bounded Fp12_loose out /\
               (FElem_Fp12 pbase out ⋆ Rr) mem').

    (* Loader specs — inline definitions *)
    Instance spec_of_bls377_load_gamma1 : spec_of "bls377_load_gamma1" :=
      fnspec! "bls377_load_gamma1" (pout : word)
        / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists gamma1,
          Fp2_bounded Fp2_loose gamma1 /\
          (FElem_Fp2 pout gamma1 ⋆ Rr) mem' }.

    Instance spec_of_bls377_load_gamma2 : spec_of "bls377_load_gamma2" :=
      fnspec! "bls377_load_gamma2" (pout : word)
        / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists gamma2,
          Fp2_bounded Fp2_loose gamma2 /\
          (FElem_Fp2 pout gamma2 ⋆ Rr) mem' }.

    Instance spec_of_bls377_load_w_frob_c1 : spec_of "bls377_load_w_frob_c1" :=
      fnspec! "bls377_load_w_frob_c1" (pout : word)
        / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists w_frob_c1,
          Fp2_bounded Fp2_loose w_frob_c1 /\
          (FElem_Fp2 pout w_frob_c1 ⋆ Rr) mem' }.

    (* Spec for the DSD hard part *)
    Instance spec_of_bls377_final_exp_hard_dsd : spec_of "bls377_final_exp_hard_dsd" :=
      fnspec! "bls377_final_exp_hard_dsd" (pout pf : word)
        / (old_out f_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight f_val /\
          (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f_val ⋆ Rr)) mem' }.

    Local Instance bls377_Fp12_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bls377_Fp12_params' _ _ _ _ bls377_Fp12_rep' :=
      DodecicFieldExtensionsSpecs.Fp12_field_representation_ok bls377_beta bls377_xi_re bls377_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

    Local Instance bls377_Fp2_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bls377_Fp2_params' _ _ _ _ bls377_Fp2_rep' :=
      QuadraticFieldExtensionsSpecs.Fp2_field_representation_ok bls377_beta fp2_prefix.

    Lemma bls377_final_exp_hard_dsd_ok :
      forall functions
        (EnvContains : map.get functions "bls377_final_exp_hard_dsd" =
          Some (snd BLS12_377_Pairing.bls377_final_exp_hard_dsd))
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HFp12conj : spec_of_Fp12_conjugate functions)
        (HFp12frob : spec_of_Fp12_frobenius functions)
        (HFp12copy : spec_of_Fp12_felem_copy functions)
        (HFpowu : spec_of_pow_u functions)
        (HFpowu_ip : spec_of_pow_u_inplace functions)
        (HFloadg1 : spec_of_bls377_load_gamma1 functions)
        (HFloadg2 : spec_of_bls377_load_gamma2 functions)
        (HFloadw : spec_of_bls377_load_w_frob_c1 functions),
      spec_of_bls377_final_exp_hard_dsd functions.
    Proof.
      intros. unfold spec_of_bls377_final_exp_hard_dsd.
      intros pout pf old_out f_val Rr tr mem0 [Hbf Hsep].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold BLS12_377_Pairing.bls377_final_exp_hard_dsd. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Stackalloc 1: t0 (Fp12)                                         *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t0 mS_t0 mC_t0 HaS_t0 HmS_t0.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls377_Fp12_params' _ _ _ _
        bls377_Fp12_rep' wordok mapok a_t0 mS_t0) HaS_t0) as [t0i Ht0i].

      (* ================================================================ *)
      (* Stackalloc 2: t1 (Fp12)                                         *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t1 mS_t1 mC_t1 HaS_t1 HmS_t1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls377_Fp12_params' _ _ _ _
        bls377_Fp12_rep' wordok mapok a_t1 mS_t1) HaS_t1) as [t1i Ht1i].

      (* ================================================================ *)
      (* Stackalloc 3: t2 (Fp12)                                         *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t2 mS_t2 mC_t2 HaS_t2 HmS_t2.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls377_Fp12_params' _ _ _ _
        bls377_Fp12_rep' wordok mapok a_t2 mS_t2) HaS_t2) as [t2i Ht2i].

      (* ================================================================ *)
      (* Stackalloc 4: t3 (Fp12)                                         *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t3 mS_t3 mC_t3 HaS_t3 HmS_t3.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls377_Fp12_params' _ _ _ _
        bls377_Fp12_rep' wordok mapok a_t3 mS_t3) HaS_t3) as [t3i Ht3i].

      (* ================================================================ *)
      (* Stackalloc 5: gamma1 (Fp2)                                      *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_gamma1 mS_g1 mC_g1 HaS_g1 HmS_g1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls377_Fp2_params' _ _ _ _
        bls377_Fp2_rep' wordok mapok a_gamma1 mS_g1) HaS_g1) as [g1i Hg1i].

      (* ================================================================ *)
      (* Stackalloc 6: gamma2 (Fp2)                                      *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_gamma2 mS_g2 mC_g2 HaS_g2 HmS_g2.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls377_Fp2_params' _ _ _ _
        bls377_Fp2_rep' wordok mapok a_gamma2 mS_g2) HaS_g2) as [g2i Hg2i].

      (* ================================================================ *)
      (* Stackalloc 7: w_frob_c1 (Fp2)                                   *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_wfc1 mS_w mC_w HaS_w HmS_w.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bls377_Fp2_params' _ _ _ _
        bls377_Fp2_rep' wordok mapok a_wfc1 mS_w) HaS_w) as [wi Hwi].

      unfold BLS12_377_Pairing.final_exp_hard_dsd_body, BLS12_377_Pairing.cmd_seq_list.

      (* Build master sep from all 7 stackalloc layers + original *)
      (* Layer 1: t0 *)
      pose proof (proj1 (map.split_comm mC_t0 mem0 mS_t0) HmS_t0) as HmS_t0'.
      assert (Hsep1 :
        (FElem_Fp12 a_t0 t0i ⋆
         (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr))) mC_t0).
      { exists mS_t0, mem0. exact (conj HmS_t0' (conj Ht0i Hsep)). }

      (* Layer 2: t1 *)
      pose proof (proj1 (map.split_comm mC_t1 mC_t0 mS_t1) HmS_t1) as HmS_t1'.
      assert (Hsep2 :
        (FElem_Fp12 a_t1 t1i ⋆
         (FElem_Fp12 a_t0 t0i ⋆
          (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))) mC_t1).
      { exists mS_t1, mC_t0. exact (conj HmS_t1' (conj Ht1i Hsep1)). }

      (* Layer 3: t2 *)
      pose proof (proj1 (map.split_comm mC_t2 mC_t1 mS_t2) HmS_t2) as HmS_t2'.
      assert (Hsep3 :
        (FElem_Fp12 a_t2 t2i ⋆
         (FElem_Fp12 a_t1 t1i ⋆
          (FElem_Fp12 a_t0 t0i ⋆
           (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))) mC_t2).
      { exists mS_t2, mC_t1. exact (conj HmS_t2' (conj Ht2i Hsep2)). }

      (* Layer 4: t3 *)
      pose proof (proj1 (map.split_comm mC_t3 mC_t2 mS_t3) HmS_t3) as HmS_t3'.
      assert (Hsep4 :
        (FElem_Fp12 a_t3 t3i ⋆
         (FElem_Fp12 a_t2 t2i ⋆
          (FElem_Fp12 a_t1 t1i ⋆
           (FElem_Fp12 a_t0 t0i ⋆
            (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))))) mC_t3).
      { exists mS_t3, mC_t2. exact (conj HmS_t3' (conj Ht3i Hsep3)). }

      (* Layer 5: gamma1 *)
      pose proof (proj1 (map.split_comm mC_g1 mC_t3 mS_g1) HmS_g1) as HmS_g1'.
      assert (Hsep5 :
        (FElem_Fp2 a_gamma1 g1i ⋆
         (FElem_Fp12 a_t3 t3i ⋆
          (FElem_Fp12 a_t2 t2i ⋆
           (FElem_Fp12 a_t1 t1i ⋆
            (FElem_Fp12 a_t0 t0i ⋆
             (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))))) mC_g1).
      { exists mS_g1, mC_t3. exact (conj HmS_g1' (conj Hg1i Hsep4)). }

      (* Layer 6: gamma2 *)
      pose proof (proj1 (map.split_comm mC_g2 mC_g1 mS_g2) HmS_g2) as HmS_g2'.
      assert (Hsep6 :
        (FElem_Fp2 a_gamma2 g2i ⋆
         (FElem_Fp2 a_gamma1 g1i ⋆
          (FElem_Fp12 a_t3 t3i ⋆
           (FElem_Fp12 a_t2 t2i ⋆
            (FElem_Fp12 a_t1 t1i ⋆
             (FElem_Fp12 a_t0 t0i ⋆
              (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)))))))) mC_g2).
      { exists mS_g2, mC_g1. exact (conj HmS_g2' (conj Hg2i Hsep5)). }

      (* Layer 7: w_frob_c1 *)
      pose proof (proj1 (map.split_comm mC_w mC_g2 mS_w) HmS_w) as HmS_w'.
      assert (Hsep_all :
        (FElem_Fp2 a_wfc1 wi ⋆
         (FElem_Fp2 a_gamma2 g2i ⋆
          (FElem_Fp2 a_gamma1 g1i ⋆
           (FElem_Fp12 a_t3 t3i ⋆
            (FElem_Fp12 a_t2 t2i ⋆
             (FElem_Fp12 a_t1 t1i ⋆
              (FElem_Fp12 a_t0 t0i ⋆
               (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr))))))))) mC_w).
      { exists mS_w, mC_g2. exact (conj HmS_w' (conj Hwi Hsep6)). }

      clear Hsep Hsep1 Hsep2 Hsep3 Hsep4 Hsep5 Hsep6.

      (* ================================================================ *)
      (* Call 1: bls377_load_gamma1(gamma1)                               *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadg1. ecancel_assumption. }
      intros ? ? ? [? [? [gamma1_v [Hb_g1 Hsep_g1]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 2: bls377_load_gamma2(gamma2)                               *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadg2. ecancel_assumption. }
      intros ? ? ? [? [? [gamma2_v [Hb_g2 Hsep_g2]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 3: bls377_load_w_frob_c1(w_frob_c1)                        *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadw. ecancel_assumption. }
      intros ? ? ? [? [? [wfc1_v [Hb_w Hsep_w]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 4: pow_u(t0, f) — t0 = f^u                                 *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFpowu.
           split; [exact Hbf |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t0_v [Hb_t0 Hsep_t0]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 5: sqr(t1, t0) — t1 = t0^2                                 *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12sqr.
           split; [exact Hb_t0 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v [Hfeval_t1 [Hb_t1 Hsep_t1]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 6: pow_u(t2, t0) — t2 = pow_u(t0) = f^{u^2}               *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFpowu.
           split; [exact Hb_t0 |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t2_v [Hb_t2 Hsep_t2]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 7: sqr(t3, t2) — t3 = t2^2                                 *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12sqr.
           split; [exact Hb_t2 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t3_v [Hfeval_t3 [Hb_t3 Hsep_t3]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 8: mul(t1, t1, t2) — t1 = t1 * t2                          *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t1 |].
           split; [exact Hb_t2 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v2 [Hfeval_t1b [Hb_t1b Hsep_t1b]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 9: pow_u(t2, t2) — IN-PLACE — t2 = pow_u(t2) = f^{u^3}   *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFpowu_ip; [exact Hb_t2 | ecancel_assumption]. }
      intros ? ? ? [? [? [t2_v2 [Hb_t2b Hsep_t2b]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 10: mul(t1, t1, t2) — t1 = t1 * t2                         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t1b |].
           split; [exact Hb_t2b |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v3 [Hfeval_t1c [Hb_t1c Hsep_t1c]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 11: conjugate(t1, t1)                                       *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_t1c |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v4 [Hfeval_t1d [Hb_t1d Hsep_t1d]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 12: mul(t1, t1, f) — t1 = t1 * f                           *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t1d |].
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v5 [Hfeval_t1e [Hb_t1e Hsep_t1e]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 13: conjugate(t1, t1)                                       *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_t1e |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v6 [Hfeval_t1f [Hb_t1f Hsep_t1f]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 14: conjugate(t0, f) — t0 = conj(f)                        *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v2 [Hfeval_t0b [Hb_t0b Hsep_t0b]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 15: mul(t1, t1, t0) — t1 = t1 * conj(f)                    *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t1f |].
           split; [exact Hb_t0b |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v7 [Hfeval_t1g [Hb_t1g Hsep_t1g]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 16: pow_u(t2, t2) — IN-PLACE — t2 = pow_u(t2) = f^{u^4}  *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFpowu_ip; [exact Hb_t2b | ecancel_assumption]. }
      intros ? ? ? [? [? [t2_v3 [Hb_t2c Hsep_t2c]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 17: mul(t0, t2, t3)                                         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t2c |].
           split; [exact Hb_t3 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v3 [Hfeval_t0c [Hb_t0c Hsep_t0c]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 18: mul(t0, t0, t1)                                         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0c |].
           split; [exact Hb_t1g |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v4 [Hfeval_t0d [Hb_t0d Hsep_t0d]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 19: frobenius(t1, f, gamma1, gamma2, w_frob_c1)             *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hbf |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [frob1_v [Hb_frob1 Hsep_frob1]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 20: frobenius(t2, t1, gamma1, gamma2, w_frob_c1)            *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_frob1 |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [frob2_v [Hb_frob2 Hsep_frob2]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 21: frobenius(t3, t2, gamma1, gamma2, w_frob_c1)            *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_frob2 |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [frob3_v [Hb_frob3 Hsep_frob3]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 22: mul(t0, t0, t1)                                         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0d |].
           split; [exact Hb_frob1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v5 [Hfeval_t0e [Hb_t0e Hsep_t0e]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 23: mul(t0, t0, t2)                                         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0e |].
           split; [exact Hb_frob2 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v6 [Hfeval_t0f [Hb_t0f Hsep_t0f]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 24: mul(t0, t0, t3)                                         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0f |].
           split; [exact Hb_frob3 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v7 [Hfeval_t0g [Hb_t0g Hsep_t0g]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 25: copy(out, t0)                                           *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12copy.
           split; ecancel_assumption_with_copy. }
      intros ? ? ? [? [? Hsep_copy]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Stack deallocation: 7 stack frames (innermost first)             *)
      (* ================================================================ *)

      (* Dealloc w_frob_c1 (Fp2) *)
      match goal with Hc : (_ ⋆ _)%sep ?m |- _ =>
        assert (Hsep_w_front :
          (FElem_Fp2 a_wfc1 wfc1_v ⋆
           (FElem_Fp12 pout t0_v7 ⋆
            (FElem_Fp12 a_t0 t0_v7 ⋆
             (FElem_Fp2 a_gamma2 gamma2_v ⋆
              (FElem_Fp2 a_gamma1 gamma1_v ⋆
               (FElem_Fp12 a_t3 frob3_v ⋆
                (FElem_Fp12 a_t2 frob2_v ⋆
                 (FElem_Fp12 a_t1 frob1_v ⋆
                  (FElem_Fp12 pf f_val ⋆ Rr))))))))) m);
        [ecancel_assumption | clear Hc]
      end.
      destruct Hsep_w_front as [mStack_w [m_after_w [Hsp_w [Hfe_w Hrest_w]]]].
      assert (Hab_w : Memory.anybytes a_wfc1 (AbstractField.felem_size_in_bytes (F:=Fp2)) mStack_w).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bls377_Fp2_rep')
                      a_wfc1 wfc1_v mStack_w Hfe_w) as Hw_bytes.
        cbv [Placeholder] in Hw_bytes. exact Hw_bytes. }
      exists m_after_w, mStack_w.
      split. { exact Hab_w. }
      split. { apply map.split_comm. exact Hsp_w. }

      (* Dealloc gamma2 (Fp2) *)
      assert (Hsep_g2_front :
        (FElem_Fp2 a_gamma2 gamma2_v ⋆
         (FElem_Fp12 pout t0_v7 ⋆
          (FElem_Fp12 a_t0 t0_v7 ⋆
           (FElem_Fp2 a_gamma1 gamma1_v ⋆
            (FElem_Fp12 a_t3 frob3_v ⋆
             (FElem_Fp12 a_t2 frob2_v ⋆
              (FElem_Fp12 a_t1 frob1_v ⋆
               (FElem_Fp12 pf f_val ⋆ Rr)))))))) m_after_w).
      { ecancel_assumption. }
      clear Hrest_w.
      destruct Hsep_g2_front as [mStack_g2 [m_after_g2 [Hsp_g2 [Hfe_g2 Hrest_g2]]]].
      assert (Hab_g2 : Memory.anybytes a_gamma2 (AbstractField.felem_size_in_bytes (F:=Fp2)) mStack_g2).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bls377_Fp2_rep')
                      a_gamma2 gamma2_v mStack_g2 Hfe_g2) as Hg2_bytes.
        cbv [Placeholder] in Hg2_bytes. exact Hg2_bytes. }
      exists m_after_g2, mStack_g2.
      split. { exact Hab_g2. }
      split. { apply map.split_comm. exact Hsp_g2. }

      (* Dealloc gamma1 (Fp2) *)
      assert (Hsep_g1_front :
        (FElem_Fp2 a_gamma1 gamma1_v ⋆
         (FElem_Fp12 pout t0_v7 ⋆
          (FElem_Fp12 a_t0 t0_v7 ⋆
           (FElem_Fp12 a_t3 frob3_v ⋆
            (FElem_Fp12 a_t2 frob2_v ⋆
             (FElem_Fp12 a_t1 frob1_v ⋆
              (FElem_Fp12 pf f_val ⋆ Rr))))))) m_after_g2).
      { ecancel_assumption. }
      clear Hrest_g2.
      destruct Hsep_g1_front as [mStack_g1 [m_after_g1 [Hsp_g1 [Hfe_g1 Hrest_g1]]]].
      assert (Hab_g1 : Memory.anybytes a_gamma1 (AbstractField.felem_size_in_bytes (F:=Fp2)) mStack_g1).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bls377_Fp2_rep')
                      a_gamma1 gamma1_v mStack_g1 Hfe_g1) as Hg1_bytes.
        cbv [Placeholder] in Hg1_bytes. exact Hg1_bytes. }
      exists m_after_g1, mStack_g1.
      split. { exact Hab_g1. }
      split. { apply map.split_comm. exact Hsp_g1. }

      (* Dealloc t3 (Fp12) *)
      assert (Hsep_t3_front :
        (FElem_Fp12 a_t3 frob3_v ⋆
         (FElem_Fp12 pout t0_v7 ⋆
          (FElem_Fp12 a_t0 t0_v7 ⋆
           (FElem_Fp12 a_t2 frob2_v ⋆
            (FElem_Fp12 a_t1 frob1_v ⋆
             (FElem_Fp12 pf f_val ⋆ Rr)))))) m_after_g1).
      { ecancel_assumption. }
      clear Hrest_g1.
      destruct Hsep_t3_front as [mStack_t3 [m_after_t3 [Hsp_t3 [Hfe_t3 Hrest_t3]]]].
      assert (Hab_t3 : Memory.anybytes a_t3 (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_t3).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bls377_Fp12_rep')
                      a_t3 frob3_v mStack_t3 Hfe_t3) as Ht3_bytes.
        cbv [Placeholder] in Ht3_bytes. exact Ht3_bytes. }
      exists m_after_t3, mStack_t3.
      split. { exact Hab_t3. }
      split. { apply map.split_comm. exact Hsp_t3. }

      (* Dealloc t2 (Fp12) *)
      assert (Hsep_t2_front :
        (FElem_Fp12 a_t2 frob2_v ⋆
         (FElem_Fp12 pout t0_v7 ⋆
          (FElem_Fp12 a_t0 t0_v7 ⋆
           (FElem_Fp12 a_t1 frob1_v ⋆
            (FElem_Fp12 pf f_val ⋆ Rr))))) m_after_t3).
      { ecancel_assumption. }
      clear Hrest_t3.
      destruct Hsep_t2_front as [mStack_t2 [m_after_t2 [Hsp_t2 [Hfe_t2 Hrest_t2]]]].
      assert (Hab_t2 : Memory.anybytes a_t2 (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_t2).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bls377_Fp12_rep')
                      a_t2 frob2_v mStack_t2 Hfe_t2) as Ht2_bytes.
        cbv [Placeholder] in Ht2_bytes. exact Ht2_bytes. }
      exists m_after_t2, mStack_t2.
      split. { exact Hab_t2. }
      split. { apply map.split_comm. exact Hsp_t2. }

      (* Dealloc t1 (Fp12) *)
      assert (Hsep_t1_front :
        (FElem_Fp12 a_t1 frob1_v ⋆
         (FElem_Fp12 pout t0_v7 ⋆
          (FElem_Fp12 a_t0 t0_v7 ⋆
           (FElem_Fp12 pf f_val ⋆ Rr)))) m_after_t2).
      { ecancel_assumption. }
      clear Hrest_t2.
      destruct Hsep_t1_front as [mStack_t1 [m_after_t1 [Hsp_t1 [Hfe_t1 Hrest_t1]]]].
      assert (Hab_t1 : Memory.anybytes a_t1 (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_t1).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bls377_Fp12_rep')
                      a_t1 frob1_v mStack_t1 Hfe_t1) as Ht1_bytes.
        cbv [Placeholder] in Ht1_bytes. exact Ht1_bytes. }
      exists m_after_t1, mStack_t1.
      split. { exact Hab_t1. }
      split. { apply map.split_comm. exact Hsp_t1. }

      (* Dealloc t0 (Fp12) *)
      assert (Hsep_t0_front :
        (FElem_Fp12 a_t0 t0_v7 ⋆
         (FElem_Fp12 pout t0_v7 ⋆
          (FElem_Fp12 pf f_val ⋆ Rr))) m_after_t1).
      { ecancel_assumption. }
      clear Hrest_t1.
      destruct Hsep_t0_front as [mStack_t0 [m_final [Hsp_t0 [Hfe_t0 Hrest_final]]]].
      assert (Hab_t0 : Memory.anybytes a_t0 (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_t0).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bls377_Fp12_rep')
                      a_t0 t0_v7 mStack_t0 Hfe_t0) as Ht0_bytes.
        cbv [Placeholder] in Ht0_bytes. exact Ht0_bytes. }
      exists m_final, mStack_t0.
      split. { exact Hab_t0. }
      split. { apply map.split_comm. exact Hsp_t0. }

      (* Final postcondition *)
      cbv [list_map list_map_body WeakestPrecondition.get].
      split. { reflexivity. }
      split. { reflexivity. }
      exists t0_v7.
      split. { exact Hb_t0g. }
      exact Hrest_final.
    Qed.

End BLS12_377_FinalExpHardDSD.
