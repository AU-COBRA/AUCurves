(** * BN256 DSD Final Exponentiation Hard Part WP Proof
    Proves bn256_final_exp_hard_dsd (35 calls, 7 stackallocs) satisfies its spec.
    The hard part computes f^{(p^4 - p^2 + 1)/r} using the
    Fuentes-Castaneda Algorithm 1 decomposition for BN curves.
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
Require Import Bedrock.Field.Synthesis.Examples.BN256_PowU.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.
Require Import bedrock2.Loops.
Require Import bedrock2.SepCalls.
Require Import coqutil.Z.Lia.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Section BN256_FinalExpHardDSD.

    (* === BN256 Instance Boilerplate === *)
    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bn256_M_pos : positive := Eval vm_compute in (Z.to_pos bn256_prime.m).

    Instance bn256_pf_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bn256_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bn256_mul"; PrimeField.add := "bn256_add";
      PrimeField.sub := "bn256_sub"; PrimeField.opp := "bn256_opp";
      PrimeField.square := "bn256_square"; PrimeField.scmula24 := "bn256_scmula24";
      PrimeField.inv := "bn256_inv"; PrimeField.from_bytes := "bn256_from_bytes";
      PrimeField.to_bytes := "bn256_to_bytes"; PrimeField.select_znz := "bn256_select_znz";
      PrimeField.felem_copy := "bn256_felem_copy"; PrimeField.from_word := "bn256_from_word";
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

    Let bn256_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
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

    (* === Abbreviations === *)
    Local Notation FElem_Fp12 := (@AbstractField.FElem _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_bounded := (@AbstractField.bounded_by _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_tight := (@AbstractField.tight_bounds _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_loose := (@AbstractField.loose_bounds _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_felem := (@AbstractField.felem _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation Fp12_feval := (@AbstractField.feval _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep').
    Local Notation FElem_Fp2 := (@AbstractField.FElem _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation Fp2_bounded := (@AbstractField.bounded_by _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation Fp2_tight := (@AbstractField.tight_bounds _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation Fp2_loose := (@AbstractField.loose_bounds _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation Fp2_felem := (@AbstractField.felem _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep').
    Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

    Local Typeclasses Opaque bn256_Fp12_params'.
    Local Typeclasses Opaque bn256_Fp6_params'.
    Local Typeclasses Opaque bn256_Fp2_params'.

    (* === Operation specs === *)
    Instance spec_of_Fp12_mul : spec_of (AbstractField.mul (F:=Fp12)) :=
      AbstractField.binop_spec (F:=Fp12) (field_representation:=bn256_Fp12_rep') AbstractField.bin_mul.
    Instance spec_of_Fp12_sqr : spec_of (AbstractField.square (F:=Fp12)) :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn256_Fp12_rep') AbstractField.un_square.
    Instance spec_of_Fp12_felem_copy : spec_of (AbstractField.felem_copy (F:=Fp12)) :=
      AbstractField.spec_of_felem_copy (F:=Fp12) (field_representation:=bn256_Fp12_rep').

    Let fp12_conjugate_name : string := (fp12_prefix ++ "conjugate")%string.
    Instance spec_of_Fp12_conjugate : spec_of fp12_conjugate_name :=
      AbstractField.unop_spec (F:=Fp12) (field_representation:=bn256_Fp12_rep')
        (@DodecicFieldExtensions.un_Fp12_conjugate _ _ _ _
          bn256_pf_params bn256_Fp_rep bn256_beta bn256_xi_re bn256_xi_im fp12_prefix fp6_prefix fp2_prefix).

    Let fp12_frobenius_name : string := (fp12_prefix ++ "frobenius")%string.

    (* Frobenius spec — same shape as PairingFieldOps.spec_of_Fp12_frobenius,
       instantiated for BN256 *)
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
    Instance spec_of_pow_u : spec_of "bn256_Fp12_pow_u" :=
      fnspec! "bn256_Fp12_pow_u" (pout pbase : word)
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
        WeakestPrecondition.call functions "bn256_Fp12_pow_u"
          tr mem [pbase; pbase]
          (fun tr' mem' rets =>
             rets = [] /\ tr = tr' /\ exists out,
               Fp12_bounded Fp12_loose out /\
               (FElem_Fp12 pbase out ⋆ Rr) mem').

    (* Loader specs — inline definitions *)
    Instance spec_of_bn256_load_gamma1 : spec_of "bn256_load_gamma1" :=
      fnspec! "bn256_load_gamma1" (pout : word)
        / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists gamma1,
          Fp2_bounded Fp2_loose gamma1 /\
          (FElem_Fp2 pout gamma1 ⋆ Rr) mem' }.

    Instance spec_of_bn256_load_gamma2 : spec_of "bn256_load_gamma2" :=
      fnspec! "bn256_load_gamma2" (pout : word)
        / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists gamma2,
          Fp2_bounded Fp2_loose gamma2 /\
          (FElem_Fp2 pout gamma2 ⋆ Rr) mem' }.

    Instance spec_of_bn256_load_w_frob_c1 : spec_of "bn256_load_w_frob_c1" :=
      fnspec! "bn256_load_w_frob_c1" (pout : word)
        / (old_out : Fp2_felem) Rr,
      { requires tr mem := (FElem_Fp2 pout old_out ⋆ Rr) mem;
        ensures tr' mem' := tr = tr' /\ exists w_frob_c1,
          Fp2_bounded Fp2_loose w_frob_c1 /\
          (FElem_Fp2 pout w_frob_c1 ⋆ Rr) mem' }.

    (* Spec for the DSD hard part *)
    Instance spec_of_bn256_final_exp_hard_dsd : spec_of "bn256_final_exp_hard_dsd" :=
      fnspec! "bn256_final_exp_hard_dsd" (pout pf : word)
        / (old_out f_val : Fp12_felem) Rr,
      { requires tr mem :=
          Fp12_bounded Fp12_tight f_val /\
          (FElem_Fp12 pf f_val ⋆ (FElem_Fp12 pout old_out ⋆ Rr)) mem;
        ensures tr' mem' :=
          tr = tr' /\ exists out,
            Fp12_bounded Fp12_loose out /\
            (FElem_Fp12 pout out ⋆ (FElem_Fp12 pf f_val ⋆ Rr)) mem' }.

    Local Instance bn256_Fp12_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bn256_Fp12_params' _ _ _ _ bn256_Fp12_rep' :=
      DodecicFieldExtensionsSpecs.Fp12_field_representation_ok bn256_beta bn256_xi_re bn256_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).

    Local Instance bn256_Fp2_rep_ok' :
      @AbstractField.FieldRepresentation_ok _ bn256_Fp2_params' _ _ _ _ bn256_Fp2_rep' :=
      QuadraticFieldExtensionsSpecs.Fp2_field_representation_ok bn256_beta fp2_prefix.

    Lemma bn256_final_exp_hard_dsd_ok :
      forall functions
        (EnvContains : map.get functions "bn256_final_exp_hard_dsd" =
          Some (snd BN256_Pairing.bn256_final_exp_hard_dsd))
        (HFp12mul : spec_of_Fp12_mul functions)
        (HFp12sqr : spec_of_Fp12_sqr functions)
        (HFp12conj : spec_of_Fp12_conjugate functions)
        (HFp12frob : spec_of_Fp12_frobenius functions)
        (HFp12copy : spec_of_Fp12_felem_copy functions)
        (HFpowu : spec_of_pow_u functions)
        (HFpowu_ip : spec_of_pow_u_inplace functions)
        (HFloadg1 : spec_of_bn256_load_gamma1 functions)
        (HFloadg2 : spec_of_bn256_load_gamma2 functions)
        (HFloadw : spec_of_bn256_load_w_frob_c1 functions),
      spec_of_bn256_final_exp_hard_dsd functions.
    Proof.
      intros. unfold spec_of_bn256_final_exp_hard_dsd.
      intros pout pf old_out f_val Rr tr mem0 [Hbf Hsep].
      eapply start_func; [exact EnvContains | clear EnvContains].
      cbv [WeakestPrecondition.func].
      unfold BN256_Pairing.bn256_final_exp_hard_dsd. simpl snd. simpl fst. cbv match beta.
      eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Stackalloc 1: t0 (Fp12)                                         *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t0 mS_t0 mC_t0 HaS_t0 HmS_t0.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn256_Fp12_params' _ _ _ _
        bn256_Fp12_rep' wordok mapok a_t0 mS_t0) HaS_t0) as [t0i Ht0i].

      (* ================================================================ *)
      (* Stackalloc 2: t1 (Fp12)                                         *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t1 mS_t1 mC_t1 HaS_t1 HmS_t1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn256_Fp12_params' _ _ _ _
        bn256_Fp12_rep' wordok mapok a_t1 mS_t1) HaS_t1) as [t1i Ht1i].

      (* ================================================================ *)
      (* Stackalloc 3: t2 (Fp12)                                         *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t2 mS_t2 mC_t2 HaS_t2 HmS_t2.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn256_Fp12_params' _ _ _ _
        bn256_Fp12_rep' wordok mapok a_t2 mS_t2) HaS_t2) as [t2i Ht2i].

      (* ================================================================ *)
      (* Stackalloc 4: t3 (Fp12)                                         *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_t3 mS_t3 mC_t3 HaS_t3 HmS_t3.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn256_Fp12_params' _ _ _ _
        bn256_Fp12_rep' wordok mapok a_t3 mS_t3) HaS_t3) as [t3i Ht3i].

      (* ================================================================ *)
      (* Stackalloc 5: gamma1 (Fp2)                                      *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_gamma1 mS_g1 mC_g1 HaS_g1 HmS_g1.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn256_Fp2_params' _ _ _ _
        bn256_Fp2_rep' wordok mapok a_gamma1 mS_g1) HaS_g1) as [g1i Hg1i].

      (* ================================================================ *)
      (* Stackalloc 6: gamma2 (Fp2)                                      *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_gamma2 mS_g2 mC_g2 HaS_g2 HmS_g2.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn256_Fp2_params' _ _ _ _
        bn256_Fp2_rep' wordok mapok a_gamma2 mS_g2) HaS_g2) as [g2i Hg2i].

      (* ================================================================ *)
      (* Stackalloc 7: w_frob_c1 (Fp2)                                   *)
      (* ================================================================ *)
      straightline. split. { apply Z_mod_mult. }
      intros a_wfc1 mS_w mC_w HaS_w HmS_w.
      pose proof (proj1 (@AbstractField.FElem_from_bytes _ bn256_Fp2_params' _ _ _ _
        bn256_Fp2_rep' wordok mapok a_wfc1 mS_w) HaS_w) as [wi Hwi].

      unfold BN256_Pairing.final_exp_hard_dsd_body, BN256_Pairing.cmd_seq_list.

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
      (* Call 1: bn256_load_gamma1(gamma1)                                *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadg1. ecancel_assumption. }
      intros ? ? ? [? [? [gamma1_v [Hb_g1 Hsep_g1]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 2: bn256_load_gamma2(gamma2)                                *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFloadg2. ecancel_assumption. }
      intros ? ? ? [? [? [gamma2_v [Hb_g2 Hsep_g2]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 3: bn256_load_w_frob_c1(w_frob_c1)                         *)
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
      (* Call 5: pow_u(t1, t0) — t1 = f^{u^2}                            *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFpowu.
           split; [exact Hb_t0 |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t1_v [Hb_t1 Hsep_t1]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 6: pow_u(t2, t1) — t2 = f^{u^3}                            *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFpowu.
           split; [exact Hb_t1 |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t2_v [Hb_t2 Hsep_t2]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 7: frobenius(t3, t2) — t3 = f^{u^3*p}                      *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_t2 |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t3_v [Hb_t3 Hsep_t3]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 8: mul(t2, t2, t3) — t2 = f^{u^3 + u^3*p}                  *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t2 |].
           split; [exact Hb_t3 |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t2_v2 [Hfeval_t2b [Hb_t2b Hsep_t2b]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 9: conjugate(t2, t2) — t2 = y6                              *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_t2b |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t2_v3 [Hfeval_t2c [Hb_t2c Hsep_t2c]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 10: sqr(out, t2) — out = y6^2                               *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12sqr.
           split; [exact Hb_t2c |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [out_v [Hfeval_out [Hb_out Hsep_out]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 11: frobenius(t3, t1) — t3 = f^{u^2*p}                     *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_t1 |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t3_v2 [Hb_t3b Hsep_t3b]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 12: mul(t2, t0, t3) — t2 = f^{u + u^2*p}                   *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0 |].
           split; [exact Hb_t3b |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t2_v4 [Hfeval_t2d [Hb_t2d Hsep_t2d]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 13: conjugate(t2, t2) — t2 = y4                             *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_t2d |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t2_v5 [Hfeval_t2e [Hb_t2e Hsep_t2e]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 14: mul(out, out, t2) — out = y6^2 * y4                     *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_out |].
           split; [exact Hb_t2e |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [out_v2 [Hfeval_outb [Hb_outb Hsep_outb]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 15: conjugate(t1, t1) — t1 = y5 = f^{-u^2}                 *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_t1 |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v2 [Hfeval_t1b [Hb_t1b Hsep_t1b]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 16: mul(out, out, t1) — out = T01 = y6^2 * y4 * y5         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_outb |].
           split; [exact Hb_t1b |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [out_v3 [Hfeval_outc [Hb_outc Hsep_outc]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 17: frobenius(t2, t0) — t2 = f^{u*p}                       *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_t0 |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t2_v6 [Hb_t2f Hsep_t2f]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 18: conjugate(t2, t2) — t2 = y3                             *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hb_t2f |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t2_v7 [Hfeval_t2g [Hb_t2g Hsep_t2g]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 19: mul(t0, out, t2) — t0 = T01 * y3                       *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_outc |].
           split; [exact Hb_t2g |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v2 [Hfeval_t0b [Hb_t0b Hsep_t0b]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 20: mul(t0, t0, t1) — t0 = T11 = T01 * y3 * y5            *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0b |].
           split; [exact Hb_t1b |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v3 [Hfeval_t0c [Hb_t0c Hsep_t0c]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 21: frobenius(t1, t3) — t1 = f^{u^2*p^2} = y2             *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_t3b |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t1_v3 [Hb_t1c Hsep_t1c]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 22: mul(out, out, t1) — out = T02 = T01 * y2               *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_outc |].
           split; [exact Hb_t1c |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [out_v4 [Hfeval_outd [Hb_outd Hsep_outd]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 23: sqr(t1, t0) — t1 = T11^2                               *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12sqr.
           split; [exact Hb_t0c |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v4 [Hfeval_t1d [Hb_t1d Hsep_t1d]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 24: mul(t1, t1, out) — t1 = T12 = T11^2 * T02              *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t1d |].
           split; [exact Hb_outd |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v5 [Hfeval_t1e [Hb_t1e Hsep_t1e]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 25: sqr(t1, t1) — t1 = T13 = T12^2                         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12sqr.
           split; [exact Hb_t1e |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t1_v6 [Hfeval_t1f [Hb_t1f Hsep_t1f]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 26: frobenius(t0, f) — t0 = f^p                             *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hbf |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t0_v4 [Hb_t0d Hsep_t0d]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 27: frobenius(t2, t0) — t2 = f^{p^2}                       *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_t0d |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t2_v8 [Hb_t2h Hsep_t2h]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 28: frobenius(t3, t2) — t3 = f^{p^3}                       *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12frob.
           split; [exact Hb_t2h |].
           split; [exact Hb_g1 |].
           split; [exact Hb_g2 |].
           split; [exact Hb_w |].
           ecancel_assumption. }
      intros ? ? ? [? [? [t3_v3 [Hb_t3c Hsep_t3c]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 29: mul(t0, t0, t2) — t0 = f^{p + p^2}                     *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0d |].
           split; [exact Hb_t2h |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v5 [Hfeval_t0e [Hb_t0e Hsep_t0e]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 30: mul(t0, t0, t3) — t0 = y0 = f^{p + p^2 + p^3}         *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0e |].
           split; [exact Hb_t3c |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v6 [Hfeval_t0f [Hb_t0f Hsep_t0f]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 31: mul(t2, t1, t0) — t2 = T14 = T13 * y0                  *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t1f |].
           split; [exact Hb_t0f |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t2_v9 [Hfeval_t2i [Hb_t2i Hsep_t2i]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 32: conjugate(t0, f) — t0 = y1 = conj(f) = f^{-1}          *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12conj.
           split; [exact Hbf |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v7 [Hfeval_t0g [Hb_t0g Hsep_t0g]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 33: mul(t0, t1, t0) — t0 = T03 = T13 * y1                  *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t1f |].
           split; [exact Hb_t0g |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v8 [Hfeval_t0h [Hb_t0h Hsep_t0h]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 34: sqr(t0, t0) — t0 = T03^2                               *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12sqr.
           split; [exact Hb_t0h |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [t0_v9 [Hfeval_t0i [Hb_t0i Hsep_t0i]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Call 35: mul(out, t0, t2) — out = T03^2 * T14 = RESULT          *)
      (* ================================================================ *)
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply HFp12mul.
           split; [exact Hb_t0i |].
           split; [exact Hb_t2i |].
           split; [eexists; ecancel_assumption_with_copy |].
           split; [eexists; ecancel_assumption_with_copy |].
           ecancel_assumption_with_copy. }
      intros ? ? ? [? [? [out_v5 [Hfeval_oute [Hb_oute Hsep_oute]]]]]. subst.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }

      (* ================================================================ *)
      (* Stack deallocation: 7 stack frames (innermost first)             *)
      (* ================================================================ *)

      (* Dealloc w_frob_c1 (Fp2) *)
      match goal with Hc : (_ ⋆ _)%sep ?m |- _ =>
        assert (Hsep_w_front :
          (FElem_Fp2 a_wfc1 wfc1_v ⋆
           (FElem_Fp12 pout out_v5 ⋆
            (FElem_Fp2 a_gamma2 gamma2_v ⋆
             (FElem_Fp2 a_gamma1 gamma1_v ⋆
              (FElem_Fp12 a_t3 t3_v3 ⋆
               (FElem_Fp12 a_t2 t2_v9 ⋆
                (FElem_Fp12 a_t1 t1_v6 ⋆
                 (FElem_Fp12 a_t0 t0_v9 ⋆
                  (FElem_Fp12 pf f_val ⋆ Rr))))))))) m);
        [ecancel_assumption | clear Hc]
      end.
      destruct Hsep_w_front as [mStack_w [m_after_w [Hsp_w [Hfe_w Hrest_w]]]].
      assert (Hab_w : Memory.anybytes a_wfc1 (AbstractField.felem_size_in_bytes (F:=Fp2)) mStack_w).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn256_Fp2_rep')
                      a_wfc1 wfc1_v mStack_w Hfe_w) as Hw_bytes.
        cbv [Placeholder] in Hw_bytes. exact Hw_bytes. }
      exists m_after_w, mStack_w.
      split. { exact Hab_w. }
      split. { apply map.split_comm. exact Hsp_w. }

      (* Dealloc gamma2 (Fp2) *)
      assert (Hsep_g2_front :
        (FElem_Fp2 a_gamma2 gamma2_v ⋆
         (FElem_Fp12 pout out_v5 ⋆
          (FElem_Fp2 a_gamma1 gamma1_v ⋆
           (FElem_Fp12 a_t3 t3_v3 ⋆
            (FElem_Fp12 a_t2 t2_v9 ⋆
             (FElem_Fp12 a_t1 t1_v6 ⋆
              (FElem_Fp12 a_t0 t0_v9 ⋆
               (FElem_Fp12 pf f_val ⋆ Rr)))))))) m_after_w).
      { ecancel_assumption. }
      clear Hrest_w.
      destruct Hsep_g2_front as [mStack_g2 [m_after_g2 [Hsp_g2 [Hfe_g2 Hrest_g2]]]].
      assert (Hab_g2 : Memory.anybytes a_gamma2 (AbstractField.felem_size_in_bytes (F:=Fp2)) mStack_g2).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn256_Fp2_rep')
                      a_gamma2 gamma2_v mStack_g2 Hfe_g2) as Hg2_bytes.
        cbv [Placeholder] in Hg2_bytes. exact Hg2_bytes. }
      exists m_after_g2, mStack_g2.
      split. { exact Hab_g2. }
      split. { apply map.split_comm. exact Hsp_g2. }

      (* Dealloc gamma1 (Fp2) *)
      assert (Hsep_g1_front :
        (FElem_Fp2 a_gamma1 gamma1_v ⋆
         (FElem_Fp12 pout out_v5 ⋆
          (FElem_Fp12 a_t3 t3_v3 ⋆
           (FElem_Fp12 a_t2 t2_v9 ⋆
            (FElem_Fp12 a_t1 t1_v6 ⋆
             (FElem_Fp12 a_t0 t0_v9 ⋆
              (FElem_Fp12 pf f_val ⋆ Rr))))))) m_after_g2).
      { ecancel_assumption. }
      clear Hrest_g2.
      destruct Hsep_g1_front as [mStack_g1 [m_after_g1 [Hsp_g1 [Hfe_g1 Hrest_g1]]]].
      assert (Hab_g1 : Memory.anybytes a_gamma1 (AbstractField.felem_size_in_bytes (F:=Fp2)) mStack_g1).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn256_Fp2_rep')
                      a_gamma1 gamma1_v mStack_g1 Hfe_g1) as Hg1_bytes.
        cbv [Placeholder] in Hg1_bytes. exact Hg1_bytes. }
      exists m_after_g1, mStack_g1.
      split. { exact Hab_g1. }
      split. { apply map.split_comm. exact Hsp_g1. }

      (* Dealloc t3 (Fp12) *)
      assert (Hsep_t3_front :
        (FElem_Fp12 a_t3 t3_v3 ⋆
         (FElem_Fp12 pout out_v5 ⋆
          (FElem_Fp12 a_t2 t2_v9 ⋆
           (FElem_Fp12 a_t1 t1_v6 ⋆
            (FElem_Fp12 a_t0 t0_v9 ⋆
             (FElem_Fp12 pf f_val ⋆ Rr)))))) m_after_g1).
      { ecancel_assumption. }
      clear Hrest_g1.
      destruct Hsep_t3_front as [mStack_t3 [m_after_t3 [Hsp_t3 [Hfe_t3 Hrest_t3]]]].
      assert (Hab_t3 : Memory.anybytes a_t3 (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_t3).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn256_Fp12_rep')
                      a_t3 t3_v3 mStack_t3 Hfe_t3) as Ht3_bytes.
        cbv [Placeholder] in Ht3_bytes. exact Ht3_bytes. }
      exists m_after_t3, mStack_t3.
      split. { exact Hab_t3. }
      split. { apply map.split_comm. exact Hsp_t3. }

      (* Dealloc t2 (Fp12) *)
      assert (Hsep_t2_front :
        (FElem_Fp12 a_t2 t2_v9 ⋆
         (FElem_Fp12 pout out_v5 ⋆
          (FElem_Fp12 a_t1 t1_v6 ⋆
           (FElem_Fp12 a_t0 t0_v9 ⋆
            (FElem_Fp12 pf f_val ⋆ Rr))))) m_after_t3).
      { ecancel_assumption. }
      clear Hrest_t3.
      destruct Hsep_t2_front as [mStack_t2 [m_after_t2 [Hsp_t2 [Hfe_t2 Hrest_t2]]]].
      assert (Hab_t2 : Memory.anybytes a_t2 (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_t2).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn256_Fp12_rep')
                      a_t2 t2_v9 mStack_t2 Hfe_t2) as Ht2_bytes.
        cbv [Placeholder] in Ht2_bytes. exact Ht2_bytes. }
      exists m_after_t2, mStack_t2.
      split. { exact Hab_t2. }
      split. { apply map.split_comm. exact Hsp_t2. }

      (* Dealloc t1 (Fp12) *)
      assert (Hsep_t1_front :
        (FElem_Fp12 a_t1 t1_v6 ⋆
         (FElem_Fp12 pout out_v5 ⋆
          (FElem_Fp12 a_t0 t0_v9 ⋆
           (FElem_Fp12 pf f_val ⋆ Rr)))) m_after_t2).
      { ecancel_assumption. }
      clear Hrest_t2.
      destruct Hsep_t1_front as [mStack_t1 [m_after_t1 [Hsp_t1 [Hfe_t1 Hrest_t1]]]].
      assert (Hab_t1 : Memory.anybytes a_t1 (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_t1).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn256_Fp12_rep')
                      a_t1 t1_v6 mStack_t1 Hfe_t1) as Ht1_bytes.
        cbv [Placeholder] in Ht1_bytes. exact Ht1_bytes. }
      exists m_after_t1, mStack_t1.
      split. { exact Hab_t1. }
      split. { apply map.split_comm. exact Hsp_t1. }

      (* Dealloc t0 (Fp12) *)
      assert (Hsep_t0_front :
        (FElem_Fp12 a_t0 t0_v9 ⋆
         (FElem_Fp12 pout out_v5 ⋆
          (FElem_Fp12 pf f_val ⋆ Rr))) m_after_t1).
      { ecancel_assumption. }
      clear Hrest_t1.
      destruct Hsep_t0_front as [mStack_t0 [m_final [Hsp_t0 [Hfe_t0 Hrest_final]]]].
      assert (Hab_t0 : Memory.anybytes a_t0 (AbstractField.felem_size_in_bytes (F:=Fp12)) mStack_t0).
      { pose proof (AbstractField.FElem_to_bytes
                      (field_representation:=bn256_Fp12_rep')
                      a_t0 t0_v9 mStack_t0 Hfe_t0) as Ht0_bytes.
        cbv [Placeholder] in Ht0_bytes. exact Ht0_bytes. }
      exists m_final, mStack_t0.
      split. { exact Hab_t0. }
      split. { apply map.split_comm. exact Hsp_t0. }

      (* Final postcondition *)
      cbv [list_map list_map_body WeakestPrecondition.get].
      split. { reflexivity. }
      split. { reflexivity. }
      exists out_v5.
      split. { exact Hb_oute. }
      exact Hrest_final.
    Qed.

End BN256_FinalExpHardDSD.
