(** * BLS12-381 — bls12_Fp2_mul_xi WP correctness proof.

    Extracted from BLS12_Pairing.v as a separately-cached compilation unit.
    The proof body is 301 lines of straightline + sep manipulation; keeping
    it inline forced a 30-min rebuild on every BLS12_Pairing.v edit.
    Wrapping in a Module avoids name conflicts with the host file.
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
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensionsFiat.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Algebra.Ring.

Import BinInt String List.ListNotations.
Import Syntax.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Module BLS12_Fp2_MulXi_Proof.

Section BLS12_Pairing.

    Existing Instances
      Defaults64.default_parameters
      Defaults64.default_parameters_ok.

    Let bls12_M_pos : positive := Eval vm_compute in (Z.to_pos bls12_prime.m).

    Instance bls12_prime_params : PrimeFieldParameters := {|
      PrimeField.M_pos := bls12_M_pos;
      PrimeField.a24 := F.of_Z _ 0;
      PrimeField.mul := "bls12_mul";
      PrimeField.add := "bls12_add";
      PrimeField.sub := "bls12_sub";
      PrimeField.opp := "bls12_opp";
      PrimeField.square := "bls12_square";
      PrimeField.scmula24 := "bls12_scmula24";
      PrimeField.inv := "bls12_inv";
      PrimeField.from_bytes := "bls12_from_bytes";
      PrimeField.to_bytes := "bls12_to_bytes";
      PrimeField.select_znz := "bls12_select_znz";
      PrimeField.felem_copy := "bls12_felem_copy";
      PrimeField.from_word := "bls12_from_word";
      PrimeField.from_list := "bls12_from_list";
    |}.

    Instance bls12_prime_params_ok : PrimeFieldParameters_ok.
    Proof. constructor. exact prime_bls12_381. Qed.

    Existing Instance prime_field_parameters.

    Instance bls12_fp_rep : AbstractField.FieldRepresentation (F:=F PrimeField.M_pos) :=
      {| AbstractField.feval := @Field.feval _ _ _ _ _ bls12_frep;
         AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bls12_frep;
         AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bls12_frep;
         AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bls12_frep;
         AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounds := @Field.bounds _ _ _ _ _ bls12_frep;
         AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bls12_frep;
         AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bls12_frep;
         AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bls12_frep |}.

    Instance bls12_fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=F PrimeField.M_pos).
    Proof.
      constructor. intros X H.
      cbv [bounded_by bls12_fp_rep] in *.
      cbv [Field.bounded_by bls12_frep field_representation
           Signature.field_representation Representation.frep] in *.
      exact H.
    Defined.

    Let bls12_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
    Let bls12_xi_re : F PrimeField.M_pos := @F.one PrimeField.M_pos.
    Let bls12_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

    Lemma bls12_beta_nz : bls12_beta <> @F.zero PrimeField.M_pos.
    Proof.
      unfold bls12_beta. intro H. apply (f_equal F.to_Z) in H.
      rewrite F.to_Z_0 in H. vm_compute in H. discriminate.
    Qed.

    Lemma bls12_M_big : 2 < Z.pos PrimeField.M_pos.
    Proof. vm_compute. reflexivity. Qed.

    Lemma M_mod_4_3 : (Z.pos PrimeField.M_pos mod 4 =? 3) = true.
    Proof. vm_compute. reflexivity. Qed.

    Lemma bls12_beta_qnr : ~(exists x, @F.mul PrimeField.M_pos x x = bls12_beta).
    Proof.
      change bls12_beta with (QuadraticExtensionsFiat.Quad_non_res PrimeField.M_pos).
      exact (QuadraticExtensionsFiat.beta_is_non_res PrimeField.M_pos
               prime_bls12_381 bls12_M_big M_mod_4_3).
    Qed.

    Local Lemma Fp_ring_theory : ring_theory (@F.zero PrimeField.M_pos) (@F.one PrimeField.M_pos) (@F.add PrimeField.M_pos) (@F.mul PrimeField.M_pos) (@F.sub PrimeField.M_pos) (@F.opp PrimeField.M_pos) eq.
    Proof. exact (Algebra.Ring.ring_theory_for_stdlib_tactic (zero:=@F.zero PrimeField.M_pos) (one:=@F.one PrimeField.M_pos)). Qed.
    Add Ring Fp_ring : Fp_ring_theory.

    Let fp2_prefix := "bls12_Fp2_".
    Let fp6_prefix := "bls12_Fp6_".
    Let fp12_prefix := "bls12_Fp12_".

    Local Notation Fp := (F PrimeField.M_pos).
    Local Notation Fp2 := ((Fp * Fp)%type).
    Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
    Local Notation Fp12 := ((Fp6 * Fp6)%type).

    Instance bls12_Fp2_params : AbstractField.FieldParameters Fp2 :=
      Fp2_field_parameters bls12_beta fp2_prefix.
    Instance bls12_Fp2_rep : AbstractField.FieldRepresentation (F:=Fp2) :=
      Fp2_field_representation bls12_beta fp2_prefix.
    Instance bls12_Fp2_names : FieldNames (F:=Fp2) :=
      field_names_prefixed fp2_prefix.

    Instance bls12_Fp6_params : AbstractField.FieldParameters Fp6 :=
      Fp6_field_parameters bls12_beta bls12_xi_re bls12_xi_im (fp6_prefix:=fp6_prefix).
    Instance bls12_Fp6_rep : AbstractField.FieldRepresentation (F:=Fp6) :=
      Fp6_field_representation bls12_beta bls12_xi_re bls12_xi_im (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Instance bls12_Fp6_names : FieldNames (F:=Fp6) :=
      field_names_prefixed fp6_prefix.

    Instance bls12_Fp12_params : AbstractField.FieldParameters Fp12 :=
      Fp12_field_parameters bls12_beta bls12_xi_re bls12_xi_im (fp12_prefix:=fp12_prefix).
    Instance bls12_Fp12_rep : AbstractField.FieldRepresentation (F:=Fp12) :=
      Fp12_field_representation bls12_beta bls12_xi_re bls12_xi_im
        (fp12_prefix:=fp12_prefix) (fp6_prefix:=fp6_prefix) (fp2_prefix:=fp2_prefix).
    Instance bls12_Fp12_names : FieldNames (F:=Fp12) :=
      field_names_prefixed fp12_prefix.
    Instance bls12_Fp_names : FieldNames (F:=Fp) :=
      field_names_prefixed "bls12_".

    Local Notation fp_felem_offset :=
      (Memory.bytes_per_word 64 * Z.of_nat (AbstractField.felem_size_in_words (F:=Fp))).
    Local Definition expr_fp_snd (x : Syntax.expr.expr) :=
      expr.op bopname.add x (expr.literal fp_felem_offset).

    Let fp_add_name : string := PrimeField.add.
    Let fp_sub_name : string := PrimeField.sub.
    Let fp_copy_name : string := PrimeField.felem_copy.
    Let fp2_mul_xi_name : string := (fp2_prefix ++ "mul_xi")%string.

    Definition bls12_Fp2_mul_xi : function_t :=
      (fp2_mul_xi_name,
       (["out"; "x"], []:list String.string, bedrock_func_body:(
         stackalloc (AbstractField.felem_size_in_bytes (F:=Fp2)) as tmp;
         coq:(cmd.call [] fp_copy_name
           [expr.var "tmp"; expr.var "x"]);
         coq:(cmd.call [] fp_copy_name
           [expr_fp_snd (expr.var "tmp"); expr_fp_snd (expr.var "x")]);
         coq:(cmd.call [] fp_sub_name
           [expr.var "out"; expr.var "tmp"; expr_fp_snd (expr.var "tmp")]);
         coq:(cmd.call [] fp_add_name
           [expr_fp_snd (expr.var "out"); expr.var "tmp"; expr_fp_snd (expr.var "tmp")])
       ))).

    Lemma bls12_Fp2_mul_xi_name_eq : fst bls12_Fp2_mul_xi = fp2_mul_xi_name.
    Proof. reflexivity. Qed.

    Local Instance spec_of_fp_copy : spec_of PrimeField.felem_copy :=
      AbstractField.spec_of_felem_copy (F:=Fp).
    Local Instance spec_of_fp_sub : spec_of PrimeField.sub :=
      AbstractField.binop_spec AbstractField.bin_sub (F:=Fp).
    Local Instance spec_of_fp_add : spec_of PrimeField.add :=
      AbstractField.binop_spec AbstractField.bin_add (F:=Fp).

    Local Notation FElem_Fp := (@AbstractField.FElem _ _ _ _ _ _ bls12_fp_rep).
    Local Notation fp_felem_offset_word := (word.of_Z fp_felem_offset).

    Local Notation FElem_Fp2 := (@AbstractField.FElem _ _ _ _ _ _ bls12_Fp2_rep).

    Lemma bls12_Fp2_mul_xi_nested :
      forall functions,
        map.get functions fp2_mul_xi_name = Some (snd bls12_Fp2_mul_xi) ->
        spec_of_fp_copy functions ->
        spec_of_fp_sub functions ->
        spec_of_fp_add functions ->
        forall pout px old_out x Rr tr mem0,
        @AbstractField.bounded_by _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep
          (@AbstractField.tight_bounds _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep) x ->
        (FElem_Fp2 px x ⋆ (FElem_Fp2 pout old_out ⋆ Rr)) mem0 ->
        WeakestPrecondition.call functions fp2_mul_xi_name tr mem0 [pout; px]
          (fun tr' mem' rets => rets = [] /\ tr = tr' /\
            exists out',
              @AbstractField.feval _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep out' =
              BLS12Fp6Spec.fp2_mul_xi PrimeField.M_pos bls12_beta bls12_xi_re bls12_xi_im
                (@AbstractField.feval _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep x) /\
              @AbstractField.bounded_by _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep
                (@AbstractField.loose_bounds _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep) out' /\
              (FElem_Fp2 pout out' ⋆ (FElem_Fp2 px x ⋆ Rr)) mem').
    Proof.
      intros functions HEnv HFcopy HFsub HFadd.
      intros pout px old_out x Rr tr mem0 Hbx Hsep.
      eapply start_func; [exact HEnv | clear HEnv].
      cbv match beta delta [WeakestPrecondition.func bls12_Fp2_mul_xi expr_fp_snd].
      eexists. split. { exact eq_refl. }
      repeat straightline.
      split. { apply Z_mod_mult. }
      intros a_tmp mStack mCt HaSt HmSt.
      pose proof (@AbstractField.FElem_from_bytes _ (Fp2_field_parameters bls12_beta fp2_prefix)
        _ _ _ _ (Fp2_field_representation bls12_beta fp2_prefix)
        ltac:(exact _) ltac:(exact _) a_tmp) as Hfb.
      unfold AbstractField.Placeholder in Hfb.
      pose proof (proj1 (Hfb mStack) HaSt) as [tmp_val Htmp]. clear Hfb.
      destruct Hsep as [m_x [m_or [[Heq_mem0 Hd_x_or] [Hfx Hor]]]].
      destruct Hor as [m_o [m_rr [[Heq_or Hd_o_rr] [Hfe_out Hrr]]]]. subst m_or.
      subst mem0.
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        ltac:(exact _) ltac:(exact _) bls12_prime_params bls12_fp_rep
        bls12_beta fp2_prefix px x m_x Hfx)
        as [m_x0 [m_x1 [Hsp_x01 [Hx0 Hx1]]]].
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        ltac:(exact _) ltac:(exact _) bls12_prime_params bls12_fp_rep
        bls12_beta fp2_prefix pout old_out m_o Hfe_out)
        as [m_o0 [m_o1 [Hsp_o01 [Ho0 Ho1]]]].
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        ltac:(exact _) ltac:(exact _) bls12_prime_params bls12_fp_rep
        bls12_beta fp2_prefix a_tmp tmp_val mStack Htmp)
        as [m_t0 [m_t1 [Hsp_t01 [Ht0 Ht1]]]].
      destruct Hsp_x01 as [Heq_x01 Hd_x01]. subst m_x.
      destruct Hsp_o01 as [Heq_o01 Hd_o01]. subst m_o.
      destruct Hsp_t01 as [Heq_t01 Hd_t01]. subst mStack.
      destruct HmSt as [Heq_mCt Hd_mCt].
      subst mCt. rewrite <- !map.putmany_assoc.
      change (@AbstractField.bounded_by _ (Fp2_field_parameters bls12_beta fp2_prefix) _ _ _ _ (Fp2_field_representation bls12_beta fp2_prefix))
        with (fun b ws => @AbstractField.bounded_by _ _ _ _ _ _ bls12_fp_rep b
          (QuadraticFieldExtensionsSpecs.fst_felem ws)
          /\ @AbstractField.bounded_by _ _ _ _ _ _ bls12_fp_rep b
          (QuadraticFieldExtensionsSpecs.snd_felem ws)) in Hbx.
      cbv beta in Hbx. destruct Hbx as [Hbx0 Hbx1].
      split_all_disjointness.
      assert (Hsep_fp :
        (FElem_Fp px (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
         (FElem_Fp (word.add px fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem x) ⋆
          (FElem_Fp pout (QuadraticFieldExtensionsSpecs.fst_felem old_out) ⋆
           (FElem_Fp (word.add pout fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem old_out) ⋆
            (Rr ⋆
             (FElem_Fp a_tmp (QuadraticFieldExtensionsSpecs.fst_felem tmp_val) ⋆
              FElem_Fp (word.add a_tmp fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem tmp_val)))))))
        (map.putmany m_x0 (map.putmany m_x1 (map.putmany m_o0 (map.putmany m_o1
          (map.putmany m_rr (map.putmany m_t0 m_t1))))))).
      { build_sep. }
      eexists. split. { solve_dexprs. }
      eapply Semantics.weaken_call.
      1: { eapply (HFcopy a_tmp px
             (QuadraticFieldExtensionsSpecs.fst_felem tmp_val)
             (QuadraticFieldExtensionsSpecs.fst_felem x)
             (FElem_Fp (word.add px fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem x) ⋆
               (FElem_Fp pout (QuadraticFieldExtensionsSpecs.fst_felem old_out) ⋆
                (FElem_Fp (word.add pout fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem old_out) ⋆
                 (Rr ⋆
                  FElem_Fp (word.add a_tmp fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem tmp_val)))))
             (FElem_Fp px (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
               (FElem_Fp (word.add px fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem x) ⋆
                (FElem_Fp pout (QuadraticFieldExtensionsSpecs.fst_felem old_out) ⋆
                 (FElem_Fp (word.add pout fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem old_out) ⋆
                  (Rr ⋆
                   FElem_Fp (word.add a_tmp fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem tmp_val))))))
             tr).
           split; pose proof Hsep_fp as H'; ecancel_assumption. }
      intros t1 m1 rets1 [Hrets1 [Htr1 Hsep_c1]].
      subst rets1. symmetry in Htr1. subst t1.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFcopy (word.add a_tmp fp_felem_offset_word)
                           (word.add px fp_felem_offset_word)
             (QuadraticFieldExtensionsSpecs.snd_felem tmp_val)
             (QuadraticFieldExtensionsSpecs.snd_felem x)
             (FElem_Fp a_tmp (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
               (FElem_Fp pout (QuadraticFieldExtensionsSpecs.fst_felem old_out) ⋆
                (FElem_Fp (word.add pout fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem old_out) ⋆
                 (Rr ⋆
                  FElem_Fp px (QuadraticFieldExtensionsSpecs.fst_felem x)))))
             (FElem_Fp a_tmp (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
               (FElem_Fp px (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
                (FElem_Fp (word.add px fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem x) ⋆
                 (FElem_Fp pout (QuadraticFieldExtensionsSpecs.fst_felem old_out) ⋆
                  (FElem_Fp (word.add pout fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem old_out) ⋆
                   Rr)))))
             tr).
           split; pose proof Hsep_c1 as H'; ecancel_assumption. }
      intros t2 m2 rets2 [Hrets2 [Htr2 Hsep_c2]].
      subst rets2. symmetry in Htr2. subst t2.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFsub pout a_tmp (word.add a_tmp fp_felem_offset_word)
             (QuadraticFieldExtensionsSpecs.fst_felem old_out)
             (QuadraticFieldExtensionsSpecs.fst_felem x)
             (QuadraticFieldExtensionsSpecs.snd_felem x)
             _ tr).
           split; [exact Hbx0 |].
           split; [exact Hbx1 |].
           split.
           { eexists. pose proof Hsep_c2 as H'. ecancel_assumption. }
           split.
           { eexists. pose proof Hsep_c2 as H'. ecancel_assumption. }
           { pose proof Hsep_c2 as H'. ecancel_assumption. } }
      intros t3 m3 rets3 [Hrets3 [Htr3 [sub_out [Hfeval_sub [Hbound_sub Hsep_s]]]]].
      subst rets3. symmetry in Htr3. subst t3.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      repeat straightline.
      eapply Semantics.weaken_call.
      1: { eapply (HFadd (word.add pout fp_felem_offset_word)
                          a_tmp (word.add a_tmp fp_felem_offset_word)
             (QuadraticFieldExtensionsSpecs.snd_felem old_out)
             (QuadraticFieldExtensionsSpecs.fst_felem x)
             (QuadraticFieldExtensionsSpecs.snd_felem x)
             _ tr).
           split; [exact Hbx0 |].
           split; [exact Hbx1 |].
           split.
           { eexists. pose proof Hsep_s as H'. ecancel_assumption. }
           split.
           { eexists. pose proof Hsep_s as H'. ecancel_assumption. }
           { pose proof Hsep_s as H'. ecancel_assumption. } }
      intros t4 m4 rets4 [Hrets4 [Htr4 [add_out [Hfeval_add [Hbound_add Hsep_a]]]]].
      subst rets4. symmetry in Htr4. subst t4.
      cbv [map.putmany_of_list_zip]. eexists. split. { exact eq_refl. }
      assert (Hsep_split :
        ((FElem_Fp pout sub_out ⋆
          (FElem_Fp (word.add pout fp_felem_offset_word) add_out ⋆
           (FElem_Fp px (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
            (FElem_Fp (word.add px fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem x) ⋆ Rr)))) ⋆
         (FElem_Fp a_tmp (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
          FElem_Fp (word.add a_tmp fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem x)))
        m4).
      { pose proof Hsep_a as H'. ecancel_assumption. }
      destruct Hsep_split as [m_rest [m_stack [[Heq_m4 Hd_rs] [Hrest Hstack]]]].
      destruct Hstack as [m_st0 [m_st1 [[Heq_st Hd_st] [Hst0 Hst1]]]]. subst m_stack.
      assert (Hlen_st0 : Datatypes.length (QuadraticFieldExtensionsSpecs.fst_felem x) =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_fp_rep).
      { unfold AbstractField.FElem, Bignum.Bignum in Hst0.
        destruct Hst0 as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
      assert (Hlen_st1 : Datatypes.length (QuadraticFieldExtensionsSpecs.snd_felem x) =
        @AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_fp_rep).
      { unfold AbstractField.FElem, Bignum.Bignum in Hst1.
        destruct Hst1 as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
      assert (Hjoin_st : (FElem_Fp a_tmp (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
        FElem_Fp (word.add a_tmp fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem x))
        (map.putmany m_st0 m_st1)).
      { exists m_st0, m_st1. split; [split; [reflexivity | exact Hd_st] |].
        split; [exact Hst0 | exact Hst1]. }
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
        ltac:(exact _) ltac:(exact _) bls12_prime_params bls12_fp_rep bls12_beta fp2_prefix
        a_tmp (QuadraticFieldExtensionsSpecs.fst_felem x)
        (QuadraticFieldExtensionsSpecs.snd_felem x)
        (map.putmany m_st0 m_st1) Hlen_st0 Hlen_st1 Hjoin_st) as Hfp2_st.
      pose proof (@AbstractField.FElem_to_bytes _ _ _ _ ltac:(exact _) ltac:(exact _) _
        (Fp2_field_parameters bls12_beta fp2_prefix)
        (Fp2_field_representation bls12_beta fp2_prefix)
        a_tmp _ (map.putmany m_st0 m_st1) Hfp2_st) as Hanybytes_st.
      unfold AbstractField.Placeholder in Hanybytes_st.
      exists m_rest, (map.putmany m_st0 m_st1).
      split. { exact Hanybytes_st. }
      split. { split. { exact Heq_m4. } { exact Hd_rs. } }
      cbv [list_map get]. split. { exact eq_refl. } split. { exact eq_refl. }
      exists (sub_out ++ add_out).
      assert (Hlen_sub : Datatypes.length sub_out = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_fp_rep).
      { pose proof Hrest as Hrest'.
        destruct Hrest' as [m_A [m_B1 [[_ _] [HA _]]]].
        unfold AbstractField.FElem, Bignum.Bignum in HA.
        destruct HA as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
      assert (Hlen_add : Datatypes.length add_out = @AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_fp_rep).
      { pose proof Hrest as Hrest'.
        destruct Hrest' as [m_A [m_B1 [[_ _] [_ HB1]]]].
        destruct HB1 as [m_B [m_C1 [[_ _] [HB _]]]].
        unfold AbstractField.FElem, Bignum.Bignum in HB.
        destruct HB as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
      split.
      { assert (Hfeval_out :
          @AbstractField.feval _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep (sub_out ++ add_out) =
          (@AbstractField.feval _ _ _ _ _ _ bls12_fp_rep sub_out,
           @AbstractField.feval _ _ _ _ _ _ bls12_fp_rep add_out)).
        { unfold AbstractField.feval, bls12_Fp2_rep,
                 QuadraticFieldExtensionsSpecs.Fp2_field_representation,
                 QuadraticFieldExtensionsSpecs.fst_felem,
                 QuadraticFieldExtensionsSpecs.snd_felem.
          rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ Hlen_sub).
          rewrite (QuadraticFieldExtensions.skipn_app _ _ _ Hlen_sub).
          reflexivity. }
        assert (Hfeval_x :
          @AbstractField.feval _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep x =
          (@AbstractField.feval _ _ _ _ _ _ bls12_fp_rep (QuadraticFieldExtensionsSpecs.fst_felem x),
           @AbstractField.feval _ _ _ _ _ _ bls12_fp_rep (QuadraticFieldExtensionsSpecs.snd_felem x))).
        { unfold AbstractField.feval, bls12_Fp2_rep,
                 QuadraticFieldExtensionsSpecs.Fp2_field_representation.
          reflexivity. }
        rewrite Hfeval_out, Hfeval_x.
        cbv [AbstractField.bin_model AbstractField.bin_sub AbstractField.Fsub
             AbstractField.bin_add AbstractField.Fadd] in Hfeval_sub, Hfeval_add.
        rewrite Hfeval_sub, Hfeval_add.
        cbv [BLS12Fp6Spec.fp2_mul_xi Crypto.Spec.BLS12Pairing.Fp6.fp2_mul_xi
             bls12_xi_re bls12_xi_im fst snd].
        assert (Hbeta_opp : bls12_beta = @F.opp PrimeField.M_pos (@F.one PrimeField.M_pos)).
        { unfold bls12_beta. change (-1)%Z with (Z.opp 1%Z).
          rewrite F.of_Z_opp. reflexivity. }
        rewrite Hbeta_opp.
        apply injective_projections; cbn [fst snd];
        change bls12_M_pos with PrimeField.M_pos.
        - ring_simplify. reflexivity.
        - ring_simplify. reflexivity. }
      split.
      { unfold bounded_by, AbstractField.bounded_by, bls12_Fp2_rep, bls12_Fp2_params,
          CubicFieldExtensions.Fp2_repr_inst, Fp2_field_representation. simpl.
        unfold QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
        rewrite <- Hlen_sub.
        rewrite (QuadraticFieldExtensions.firstn_app' _ _ _ (eq_refl _)).
        rewrite (QuadraticFieldExtensions.skipn_app _ _ _ (eq_refl _)).
        split; assumption. }
      { destruct Hrest as [m_sub [m_tail [[Heq_rest Hd_sub_tail] [Hsub_fe Htail]]]].
        destruct Htail as [m_add [m_tail2 [[Heq_tail Hd_add_tail2] [Hadd_fe Htail2]]]].
        subst m_tail.
        pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_sub_tail) as [Hd_sub_add Hd_sub_tail2].
        destruct Htail2 as [m_px0 [m_tail3 [[Heq_tail2 Hd_px0_tail3] [Hpx0_fe Htail3]]]].
        subst m_tail2.
        pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_add_tail2) as [Hd_add_px0 Hd_add_tail3].
        pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_sub_tail2) as [Hd_sub_px0 Hd_sub_tail3].
        destruct Htail3 as [m_px1 [m_rr' [[Heq_tail3 Hd_px1_rr'] [Hpx1_fe Hrr']]]]. subst m_tail3.
        pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_px0_tail3) as [Hd_px0_px1 Hd_px0_rr'].
        pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_add_tail3) as [Hd_add_px1 Hd_add_rr'].
        pose proof (proj1 (map.disjoint_putmany_r _ _ _) Hd_sub_tail3) as [Hd_sub_px1 Hd_sub_rr'].
        assert (Hjoin_out : (FElem_Fp pout sub_out ⋆
          FElem_Fp (word.add pout fp_felem_offset_word) add_out) (map.putmany m_sub m_add)).
        { exists m_sub, m_add. split; [split; [reflexivity | exact Hd_sub_add] |].
          split; [exact Hsub_fe | exact Hadd_fe]. }
        pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
          ltac:(exact _) ltac:(exact _) bls12_prime_params bls12_fp_rep bls12_beta fp2_prefix
          pout sub_out add_out (map.putmany m_sub m_add) Hlen_sub Hlen_add Hjoin_out) as Hfp2_out.
        assert (Hlen_px0 : Datatypes.length (QuadraticFieldExtensionsSpecs.fst_felem x) =
          @AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_fp_rep).
        { unfold AbstractField.FElem, Bignum.Bignum in Hpx0_fe.
          destruct Hpx0_fe as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
        assert (Hlen_px1 : Datatypes.length (QuadraticFieldExtensionsSpecs.snd_felem x) =
          @AbstractField.felem_size_in_words _ _ _ _ _ _ bls12_fp_rep).
        { unfold AbstractField.FElem, Bignum.Bignum in Hpx1_fe.
          destruct Hpx1_fe as [? [? [? [[? Hlen'] ?]]]]. exact Hlen'. }
        assert (Hjoin_x : (FElem_Fp px (QuadraticFieldExtensionsSpecs.fst_felem x) ⋆
          FElem_Fp (word.add px fp_felem_offset_word) (QuadraticFieldExtensionsSpecs.snd_felem x))
          (map.putmany m_px0 m_px1)).
        { exists m_px0, m_px1. split; [split; [reflexivity | exact Hd_px0_px1] |].
          split; [exact Hpx0_fe | exact Hpx1_fe]. }
        pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join _ _ _ _
          ltac:(exact _) ltac:(exact _) bls12_prime_params bls12_fp_rep bls12_beta fp2_prefix
          px (QuadraticFieldExtensionsSpecs.fst_felem x) (QuadraticFieldExtensionsSpecs.snd_felem x)
          (map.putmany m_px0 m_px1) Hlen_px0 Hlen_px1 Hjoin_x) as Hfp2_x.
        assert (Hx_eq : x = List.app (QuadraticFieldExtensionsSpecs.fst_felem x)
                                      (QuadraticFieldExtensionsSpecs.snd_felem x)).
        { unfold QuadraticFieldExtensionsSpecs.fst_felem, QuadraticFieldExtensionsSpecs.snd_felem.
          symmetry. apply List.firstn_skipn. }
        rewrite Hx_eq.
        exists (map.putmany m_sub m_add), (map.putmany (map.putmany m_px0 m_px1) m_rr').
        split; [split |].
        { subst m_rest. rewrite <- !map.putmany_assoc. reflexivity. }
        { apply map.disjoint_putmany_r. split.
          { apply map.disjoint_putmany_l. split.
            { apply map.disjoint_putmany_r. split; [exact Hd_sub_px0 | exact Hd_sub_px1]. }
            { apply map.disjoint_putmany_r. split; [exact Hd_add_px0 | exact Hd_add_px1]. } }
          { apply map.disjoint_putmany_l. split; [exact Hd_sub_rr' | exact Hd_add_rr']. } }
        split. { exact Hfp2_out. }
        exists (map.putmany m_px0 m_px1), m_rr'.
        split; [split; [reflexivity |] |].
        { apply map.disjoint_putmany_l. split; [exact Hd_px0_rr' | exact Hd_px1_rr']. }
        split. { exact Hfp2_x. }
        exact Hrr'. }
    Qed.

    Local Notation mem := (@map.rep _ _ BasicC64Semantics.mem).

    Local Lemma array_scalar_precise : forall sz p v (m1 m2 : mem),
      array scalar sz p v m1 -> array scalar sz p v m2 -> m1 = m2.
    Proof.
      intros sz p v. revert p. induction v; intros p m1 m2 H1 H2.
      - simpl in *. destruct H1, H2. subst. reflexivity.
      - simpl in H1, H2.
        destruct H1 as [ms1 [mr1 [[? ?] [Hs1 Ha1]]]].
        destruct H2 as [ms2 [mr2 [[? ?] [Hs2 Ha2]]]]. subst.
        unfold scalar, truncated_scalar, truncated_word in Hs1, Hs2.
        simpl in Hs1, Hs2. unfold truncated_scalar in Hs1, Hs2.
        cbv [sepclause_of_map] in Hs1, Hs2. subst.
        f_equal. eapply IHv; eassumption.
    Qed.

    Local Lemma FElem_Fp_precise : forall p v (m1 m2 : mem),
      FElem_Fp p v m1 -> FElem_Fp p v m2 -> m1 = m2.
    Proof.
      intros p v m1 m2 H1 H2.
      unfold AbstractField.FElem, bls12_fp_rep in *. simpl in *.
      unfold Bignum.Bignum in *.
      destruct H1 as [me1 [ma1 [Hsp1 [Hemp1 Harr1]]]].
      destruct H2 as [me2 [ma2 [Hsp2 [Hemp2 Harr2]]]].
      cbv [emp] in *. destruct Hemp1 as [? _]. destruct Hemp2 as [? _]. subst.
      destruct Hsp1 as [? _]. destruct Hsp2 as [? _].
      rewrite map.putmany_empty_l in *. subst.
      eapply array_scalar_precise; eassumption.
    Qed.

    Local Lemma FElem_Fp2_precise : forall p v (m1 m2 : mem),
      FElem_Fp2 p v m1 -> FElem_Fp2 p v m2 -> m1 = m2.
    Proof.
      intros p v m1 m2 H1 H2.
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        ltac:(exact _) ltac:(exact _) bls12_prime_params bls12_fp_rep
        bls12_beta fp2_prefix p v m1 H1)
        as [m1a [m1b [Hsp1 [Ha1 Hb1]]]].
      pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split _ _ _ _
        ltac:(exact _) ltac:(exact _) bls12_prime_params bls12_fp_rep
        bls12_beta fp2_prefix p v m2 H2)
        as [m2a [m2b [Hsp2 [Ha2 Hb2]]]].
      destruct Hsp1 as [? Hd1]. destruct Hsp2 as [? Hd2]. subst.
      f_equal; eapply FElem_Fp_precise; eassumption.
    Qed.

    Local Instance un_Fp2_mul_xi
      : @AbstractField.UnOp _ _ _ _ (Fp*Fp)%type bls12_Fp2_params bls12_Fp2_rep
          fp2_mul_xi_name :=
      {| AbstractField.un_model := BLS12Fp6Spec.fp2_mul_xi PrimeField.M_pos bls12_beta bls12_xi_re bls12_xi_im;
         AbstractField.un_xbounds := @AbstractField.tight_bounds _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep;
         AbstractField.un_outbounds := @AbstractField.loose_bounds _ bls12_Fp2_params _ _ _ _ bls12_Fp2_rep |}.

    Lemma bls12_Fp2_mul_xi_ok :
      forall functions,
        map.get functions fp2_mul_xi_name = Some (snd bls12_Fp2_mul_xi) ->
        spec_of_fp_copy functions ->
        spec_of_fp_sub functions ->
        spec_of_fp_add functions ->
        AbstractField.unop_spec_nested un_Fp2_mul_xi functions.
    Proof.
      intros functions HEnv HFcopy HFsub HFadd.
      unfold AbstractField.unop_spec_nested.
      intros pout px old_out x Rr tr mem0 [Hbx Hsep].
      eapply Semantics.weaken_call.
      1: { eapply bls12_Fp2_mul_xi_nested; try eassumption. }
      cbv beta. intros t' m' rets Hpost.
      destruct Hpost as [Hrets [Htr [out' [Hfeval [Hbounds Hsep']]]]].
      split. { exact Hrets. }
      split. { exact Htr. }
      exists out'. split. { exact Hfeval. }
      split. { exact Hbounds. }
      exact Hsep'.
    Qed.

End BLS12_Pairing.

End BLS12_Fp2_MulXi_Proof.
