(** * BLS12-381: Fp6 / Fp12 leaf specs of the functional pairing theorem, from the tower library.

    The bodies are the ones of the extraction's list ([BLS12_Pairing.bls12_Fp6_funcs],
    [bls12_Fp12_funcs], [bls12_pairing_ops]); the correctness lemmas of the tower library
    ([CubicFieldExtensions], [DodecicFieldExtensions], [PairingFieldOps]) are instantiated at
    beta = -1, xi = 1 + u and the prefixes "bls12_Fp2_" / "bls12_Fp6_" / "bls12_Fp12_".
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalClosed.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalEnv.
Require Bedrock.Field.Synthesis.Examples.BLS12_Pairing.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp2.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module CE := Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Module FE := Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.

Import List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

Local Notation function_t := (String.string * Syntax.func)%type.
Local Notation Fp := (F (@PrimeField.M_pos MS.bls12_pf_params)).
Local Notation pp := MS.bls12_pf_params.
Local Notation frep := MS.bls12_Fp_rep.

Definition bls12_xi_re : Fp := F.one.
Definition bls12_xi_im : Fp := F.one.
Definition fp6_prefix : string := "bls12_Fp6_".
Definition fp12_prefix : string := "bls12_Fp12_".

Local Notation FElem1 := (@AbstractField.FElem _ _ _ _ _ _ frep).
Local Notation FElem2 := (@AbstractField.FElem _ MS.bls12_Fp2_params' _ _ _ _ MS.bls12_Fp2_rep').
Local Notation fst_felem := (fst_felem (prime_parameters:=pp) (field_representation:=frep)).
Local Notation snd_felem := (snd_felem (prime_parameters:=pp) (field_representation:=frep)).

Add Ring bls12_Fp_ring_tower : (@F.ring_theory (@PrimeField.M_pos pp)).

Local Ltac binop_call H pout px py out x y bx byy :=
  eapply WeakestPreconditionProperties.Proper_call;
  [ | refine (H pout px py out x y _ _ _ (conj bx (conj byy (conj _ (conj _ _)))));
      [ eexists; ecancel_assumption | eexists; ecancel_assumption | ecancel_assumption ] ].

Lemma mul_xi_algebra (u v : Fp) :
  (F.sub u v, F.add u v) =
  (F.add (F.mul u F.one) (F.mul (F.mul (F.opp F.one) v) F.one), F.add (F.mul u F.one) (F.mul v F.one)).
Proof. f_equal; ring. Qed.

(** The in-place ("flat") spec of [BLS12_Pairing.bls12_Fp2_mul_xi]: the body copies its input
    to the stack first, so the output may alias it. *)
Lemma bls12_Fp2_mul_xi_flat (functions : env) :
  map.get functions "bls12_Fp2_mul_xi" = Some (snd BLS12_Pairing.bls12_Fp2_mul_xi) ->
  MS.spec_of_Fp_felem_copy functions ->
  AbstractField.binop_spec (F:=Fp) (field_representation:=frep) AbstractField.bin_sub functions ->
  AbstractField.binop_spec (F:=Fp) (field_representation:=frep) AbstractField.bin_add functions ->
  CubicFieldExtensions.spec_of_Fp2_mul_xi (prime_parameters:=pp) (F_representation:=frep)
    bls12_beta bls12_xi_re bls12_xi_im fp2_prefix functions.
Proof.
  intros E Hcp Hsub Hadd.
  cbv [CubicFieldExtensions.spec_of_Fp2_mul_xi AbstractField.unop_spec].
  intros pout px out x Rr tr m (Hb & [Ra HX] & HO).
  eapply start_func; [exact E | clear E].
  cbv match beta delta [WeakestPrecondition.func BLS12_Pairing.bls12_Fp2_mul_xi snd].
  eexists; split; [exact eq_refl|].
  cbv [BLS12_Pairing.expr_fp_snd].
  repeat straightline.
  split; [reflexivity|].
  intros a mStack m0 Hany Hsplit.
  repeat straightline.
  clear HX HO H H0 length_stack length_stack0 stack stack0.
  rename HX0 into HX, HO0 into HO.
  destruct (proj1 (AbstractField.FElem_from_bytes (field_representation:=MS.bls12_Fp2_rep') a mStack) Hany)
    as [oldt Holdt].
  assert (Hm1 : (eq m0 * FElem2 a oldt)%sep m1) by (exists m0, mStack; auto).
  clear Hany Hsplit Holdt.
  apply (sep_impl_l _ _ _ _ (Fp2_split48 px x)) in HX.
  apply (sep_impl_l _ _ _ _ (Fp2_split48 pout out)) in HO.
  apply sep_comm in Hm1. apply (sep_impl_l _ _ _ _ (Fp2_split48 a oldt)) in Hm1.
  pose proof (sep_eq_l _ _ _ _ HX (proj1 (sep_comm _ _ _) Hm1)) as HXm.
  destruct Hb as [Hb1 Hb2].
  subst args.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hcp a px (fst_felem oldt) (fst_felem x)
                  (FElem1 (word.add px (word.of_Z 48)) (snd_felem x) * Ra
                   * FElem1 (word.add a (word.of_Z 48)) (snd_felem oldt))%sep
                  (FElem1 (word.add a (word.of_Z 48)) (snd_felem oldt) * eq m0)%sep
                  tr m1 (conj _ _)); ecancel_assumption ].
  intros tr2 m2 rets (Hrets & Htr2 & Hm2). subst rets tr2.
  eexists; split; [reflexivity|].
  clear HXm Hm1.
  assert (Hm2' : (eq m0 * (FElem1 a (fst_felem x) * FElem1 (word.add a (word.of_Z 48)) (snd_felem oldt)))%sep m2)
    by ecancel_assumption.
  pose proof (sep_eq_l _ _ _ _ HX Hm2') as HXm2. clear Hm2'.
  repeat straightline.
  subst args.
  repeat match goal with |- context [word.of_Z (Memory.bytes_per_word 64 * Z.of_nat ?n)] =>
    change (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat n)) with (word.of_Z (word:=Naive.word 64) 48) end.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | refine (Hcp (word.add a (word.of_Z 48)) (word.add px (word.of_Z 48))
                  (snd_felem oldt) (snd_felem x)
                  (FElem1 px (fst_felem x) * Ra * FElem1 a (fst_felem x))%sep
                  (FElem1 a (fst_felem x) * eq m0)%sep
                  tr m2 (conj _ _)); ecancel_assumption ].
  intros tr3 m3 rets (Hrets & Htr3 & Hm3). subst rets tr3.
  eexists; split; [reflexivity|].
  clear HXm2 Hm2 HX.
  assert (Hm3' : (eq m0 * (FElem1 a (fst_felem x) * FElem1 (word.add a (word.of_Z 48)) (snd_felem x)))%sep m3)
    by ecancel_assumption.
  pose proof (sep_eq_l _ _ _ _ HO Hm3') as H4. clear Hm3' Hm3 HO.
  repeat straightline.
  subst args.
  repeat match goal with |- context [word.of_Z (Memory.bytes_per_word 64 * Z.of_nat ?n)] =>
    change (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat n)) with (word.of_Z (word:=Naive.word 64) 48) end.
  binop_call Hsub pout a (word.add a (word.of_Z 48)) (fst_felem out) (fst_felem x) (snd_felem x) Hb1 Hb2.
  intros tr4 m4 rets (Hrets & Htr4 & r0 & Hr0 & Hbr0 & H5). subst rets tr4.
  eexists; split; [reflexivity|]. clear H4.
  repeat straightline.
  subst args.
  repeat match goal with |- context [word.of_Z (Memory.bytes_per_word 64 * Z.of_nat ?n)] =>
    change (word.of_Z (Memory.bytes_per_word 64 * Z.of_nat n)) with (word.of_Z (word:=Naive.word 64) 48) end.
  binop_call Hadd (word.add pout (word.of_Z 48)) a (word.add a (word.of_Z 48)) (snd_felem out) (fst_felem x) (snd_felem x) Hb1 Hb2.
  intros tr5 m5 rets (Hrets & Htr5 & r1 & Hr1 & Hbr1 & H6). subst rets tr5.
  eexists; split; [reflexivity|]. clear H5.
  assert (L1 : length r0 = 6%nat).
  { eapply (FElem1_length pout r0 m5
             (FElem1 (word.add pout (word.of_Z 48)) r1 * Rr * FElem1 a (fst_felem x)
              * FElem1 (word.add a (word.of_Z 48)) (snd_felem x))%sep).
    ecancel_assumption. }
  assert (H7 : ((FElem1 a (fst_felem x) * FElem1 (word.add a (word.of_Z 48)) (snd_felem x))
                * ((FElem1 pout r0 * FElem1 (word.add pout (word.of_Z 48)) r1) * Rr))%sep m5)
    by ecancel_assumption.
  clear H6.
  apply (sep_impl_l _ _ _ _ (Fp2_join48 a _ _)) in H7.
  rewrite (Fp2_list_decomp (prime_parameters:=pp) (F_representation:=frep)) in H7.
  apply (sep_impl_l _ _ _ _ (AbstractField.FElem_to_bytes a x)) in H7.
  destruct H7 as (mS & mR & Hs & HS & HR).
  exists mR, mS. split; [exact HS|]. split; [apply map.split_comm; exact Hs|].
  apply (sep_impl_l _ _ _ _ (Fp2_join48 pout _ _)) in HR.
  cbn [list_map]. split; [reflexivity|]. split; [reflexivity|].
  assert (Ef : fst_felem (r0 ++ r1)%list = r0) by (apply firstn_app'; exact L1).
  assert (Es : snd_felem (r0 ++ r1)%list = r1) by (apply skipn_app; exact L1).
  exists (r0 ++ r1)%list. split; [|split; [|exact HR]].
  - assert (Hfe : @AbstractField.feval _ _ _ _ _ _ MS.bls12_Fp2_rep' (r0 ++ r1)%list
                  = (@AbstractField.feval _ _ _ _ _ _ frep (fst_felem (r0 ++ r1)%list),
                     @AbstractField.feval _ _ _ _ _ _ frep (snd_felem (r0 ++ r1)%list)))
      by reflexivity.
    rewrite Ef, Es in Hfe.
    lazymatch goal with |- _ = ?r =>
      change (@AbstractField.feval _ _ _ _ _ _ MS.bls12_Fp2_rep' (r0 ++ r1)%list = r) end.
    rewrite Hfe, Hr0, Hr1.
    cbv beta iota delta [AbstractField.bin_model AbstractField.bin_sub AbstractField.bin_add
      AbstractField.un_model CubicFieldExtensions.un_Fp2_mul_xi
      CubicFieldExtensionsSpecs.BLS12Fp6Spec.fp2_mul_xi bls12_beta bls12_xi_re bls12_xi_im fst snd].
    change ((F.sub (@AbstractField.feval _ _ _ _ _ _ frep (fst_felem x))
                   (@AbstractField.feval _ _ _ _ _ _ frep (snd_felem x)),
             F.add (@AbstractField.feval _ _ _ _ _ _ frep (fst_felem x))
                   (@AbstractField.feval _ _ _ _ _ _ frep (snd_felem x))) =
            (F.add (F.mul (@AbstractField.feval _ _ _ _ _ _ frep (fst_felem x)) F.one)
                   (F.mul (F.mul (F.opp F.one) (@AbstractField.feval _ _ _ _ _ _ frep (snd_felem x))) F.one),
             F.add (F.mul (@AbstractField.feval _ _ _ _ _ _ frep (fst_felem x)) F.one)
                   (F.mul (@AbstractField.feval _ _ _ _ _ _ frep (snd_felem x)) F.one))).
    apply mul_xi_algebra.
  - refine (conj _ _).
    + change (@AbstractField.bounded_by _ _ _ _ _ _ frep
                (@AbstractField.loose_bounds _ _ _ _ _ _ frep) (fst_felem (r0 ++ r1)%list)).
      rewrite Ef. exact Hbr0.
    + change (@AbstractField.bounded_by _ _ _ _ _ _ frep
                (@AbstractField.loose_bounds _ _ _ _ _ _ frep) (snd_felem (r0 ++ r1)%list)).
      rewrite Es. exact Hbr1.
Qed.

Section Tower.
  Variable extra : list function_t.
  Local Notation functions := (map.of_list (bls12_pairing_funcs ++ extra) : env).

  Local Ltac env_main := rewrite get_of_list_find; apply first_binding_app; exact eq_refl.

  Lemma env_Fp6_felem_copy :
    map.get functions "bls12_Fp6_felem_copy" =
    Some (snd (Fp6_felem_copy (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp6_add :
    map.get functions "bls12_Fp6_add" =
    Some (snd (Fp6_add (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp6_opp :
    map.get functions "bls12_Fp6_opp" =
    Some (snd (Fp6_opp (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp12_felem_copy :
    map.get functions "bls12_Fp12_felem_copy" =
    Some (snd (Fp12_felem_copy (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp12_conjugate :
    map.get functions "bls12_Fp12_conjugate" =
    Some (snd (Fp12_conjugate (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp2_conjugate :
    map.get functions "bls12_Fp2_conjugate" =
    Some (snd (PairingFieldOps.Fp2_conjugate (prime_parameters:=pp) (F_representation:=frep)
                 fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp6_mul_fp2 :
    map.get functions "bls12_Fp6_mul_fp2" =
    Some (snd (Fp6_mul_fp2 (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp6_frobenius :
    map.get functions "bls12_Fp6_frobenius" =
    Some (snd (Fp6_frobenius (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp6_frobenius_p2 :
    map.get functions "bls12_Fp6_frobenius_p2" =
    Some (snd (Fp6_frobenius_p2 (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp12_frobenius :
    map.get functions "bls12_Fp12_frobenius" =
    Some (snd (Fp12_frobenius (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp12_frobenius_p2 :
    map.get functions "bls12_Fp12_frobenius_p2" =
    Some (snd (Fp12_frobenius_p2 (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp2_mul_xi :
    map.get functions "bls12_Fp2_mul_xi" = Some (snd BLS12_Pairing.bls12_Fp2_mul_xi).
  Proof. env_main. Qed.

  Lemma env_Fp6_mul :
    map.get functions "bls12_Fp6_mul" =
    Some (snd (Fp6_mul (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Lemma env_Fp6_mul_by_v :
    map.get functions "bls12_Fp6_mul_by_v" =
    Some (snd (Fp6_mul_by_v (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Hypothesis HFp2copy : MS.spec_of_Fp2_felem_copy functions.
  Hypothesis HFp2add : MS.spec_of_Fp2_add functions.

  Lemma bls12_Fp6_felem_copy_spec :
    CubicFieldExtensions.spec_of_Fp6_copy (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions.
  Proof.
    exact (Fp6_felem_copy_ok (prime_parameters:=pp) (F_representation:=frep)
             bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions
             env_Fp6_felem_copy HFp2copy HFp2copy HFp2copy).
  Qed.

  Lemma bls12_Fp6_add_leaf : CE.spec_of_Fp6_add functions.
  Proof.
    pose proof bls12_Fp6_felem_copy_spec as Hc6.
    exact (Fp6_add_ok (prime_parameters:=pp) (F_representation:=frep)
             bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions
             env_Fp6_add Hc6 Hc6 HFp2add HFp2add HFp2add).
  Qed.

  Hypothesis HFp2opp : MS.spec_of_Fp2_opp functions.

  Lemma bls12_Fp6_opp_spec :
    CubicFieldExtensions.spec_of_Fp6_opp (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions.
  Proof.
    exact (Fp6_opp_ok (prime_parameters:=pp) (F_representation:=frep)
             bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions
             env_Fp6_opp bls12_Fp6_felem_copy_spec HFp2opp HFp2opp HFp2opp).
  Qed.

  Lemma bls12_Fp12_felem_copy_leaf : MS.spec_of_Fp12_felem_copy functions.
  Proof.
    pose proof bls12_Fp6_felem_copy_spec as Hc6.
    exact (Fp12_felem_copy_ok (prime_parameters:=pp) (F_representation:=frep)
             bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix functions
             env_Fp12_felem_copy Hc6 Hc6).
  Qed.

  Lemma bls12_Fp12_conjugate_leaf : FE.spec_of_Fp12_conjugate functions.
  Proof.
    exact (Fp12_conjugate_ok (prime_parameters:=pp) (F_representation:=frep)
             (F_representation_ok:=MS.bls12_Fp_rep_ok)
             bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix functions
             env_Fp12_conjugate bls12_Fp12_felem_copy_leaf bls12_Fp6_felem_copy_spec
             bls12_Fp6_opp_spec).
  Qed.

  Hypothesis HFpcopy : MS.spec_of_Fp_felem_copy functions.
  Hypothesis HFpopp :
    AbstractField.unop_spec (F:=Fp) (field_representation:=frep) AbstractField.un_opp functions.
  Hypothesis HFp2mul : MS.spec_of_Fp2_mul functions.

  Lemma bls12_Fp2_conjugate_spec :
    PairingFieldOps.spec_of_Fp2_conjugate (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta fp2_prefix functions.
  Proof.
    exact (Fp2_conjugate_ok (prime_parameters:=pp) (F_representation:=frep)
             (F_representation_ok:=MS.bls12_Fp_rep_ok) bls12_beta fp2_prefix functions
             env_Fp2_conjugate HFpcopy HFpopp).
  Qed.

  Lemma bls12_Fp6_mul_fp2_spec :
    PairingFieldOps.spec_of_Fp6_mul_fp2 (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions.
  Proof.
    exact (Fp6_mul_fp2_ok (prime_parameters:=pp) (F_representation:=frep)
             (F_representation_ok:=MS.bls12_Fp_rep_ok)
             bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions
             env_Fp6_mul_fp2 HFp2copy HFp2mul).
  Qed.

  Lemma bls12_Fp12_frobenius_leaf : spec_of_Fp12_frobenius_381 functions.
  Proof.
    pose proof (Fp6_frobenius_ok (prime_parameters:=pp) (F_representation:=frep)
             (F_representation_ok:=MS.bls12_Fp_rep_ok)
             bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions
             env_Fp6_frobenius bls12_Fp2_conjugate_spec HFp2copy HFp2mul) as Hf6.
    exact (Fp12_frobenius_ok (prime_parameters:=pp) (F_representation:=frep)
             (F_representation_ok:=MS.bls12_Fp_rep_ok) (bounds_equiv:=bls12_Fp_bounds_equiv)
             bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix functions
             env_Fp12_frobenius env_Fp6_mul_fp2 Hf6 bls12_Fp6_mul_fp2_spec HFp2copy HFp2mul).
  Qed.

  Lemma bls12_Fp12_frobenius_p2_leaf : spec_of_Fp12_frobenius_p2_381 functions.
  Proof.
    pose proof (Fp6_frobenius_p2_ok (prime_parameters:=pp) (F_representation:=frep)
             (F_representation_ok:=MS.bls12_Fp_rep_ok)
             bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions
             env_Fp6_frobenius_p2 HFp2copy HFp2mul) as Hf6.
    exact (Fp12_frobenius_p2_ok (prime_parameters:=pp) (F_representation:=frep)
             (F_representation_ok:=MS.bls12_Fp_rep_ok) (bounds_equiv:=bls12_Fp_bounds_equiv)
             bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix functions
             env_Fp12_frobenius_p2 env_Fp6_mul_fp2 Hf6 bls12_Fp6_mul_fp2_spec HFp2copy HFp2mul).
  Qed.

  Hypothesis HFp2sub : MS.spec_of_Fp2_sub functions.
  Hypothesis HFpsub :
    AbstractField.binop_spec (F:=Fp) (field_representation:=frep) AbstractField.bin_sub functions.
  Hypothesis HFpadd :
    AbstractField.binop_spec (F:=Fp) (field_representation:=frep) AbstractField.bin_add functions.

  Lemma bls12_Fp6_mul_leaf : CE.spec_of_Fp6_mul functions.
  Proof.
    pose proof bls12_Fp6_felem_copy_spec as Hc6.
    pose proof (bls12_Fp2_mul_xi_flat functions env_Fp2_mul_xi HFpcopy HFpsub HFpadd) as Hxi.
    eapply (Fp6_mul_ok (prime_parameters:=pp) (F_representation:=frep)
              (bounds_equiv:=bls12_Fp_bounds_equiv)
              bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix
              (fun a b => eq_refl) functions env_Fp6_mul).
    all: lazymatch goal with
         | |- context [CubicFieldExtensions.spec_of_Fp6_copy] => exact Hc6
         | |- context [CubicFieldExtensions.spec_of_Fp2_mul_xi] => exact Hxi
         | |- context [CubicFieldExtensions.spec_of_Fp2_mul] => exact HFp2mul
         | |- context [QuadraticFieldExtensions.spec_of_Fp2_add] => exact HFp2add
         | |- context [QuadraticFieldExtensions.spec_of_Fp2_sub] => exact HFp2sub
         | |- context [CubicFieldExtensions.spec_of_Fp2_add] => exact HFp2add
         | |- context [CubicFieldExtensions.spec_of_Fp2_sub] => exact HFp2sub
         | |- ?g => idtac "UNMATCHED" g; fail
         end.
  Qed.

  Lemma bls12_Fp6_mul_by_v_leaf : CE.spec_of_Fp6_mul_by_v functions.
  Proof.
    pose proof bls12_Fp6_felem_copy_spec as Hc6.
    pose proof (bls12_Fp2_mul_xi_flat functions env_Fp2_mul_xi HFpcopy HFpsub HFpadd) as Hxi.
    exact (Fp6_mul_by_v_ok (prime_parameters:=pp) (F_representation:=frep)
             (F_representation_ok:=MS.bls12_Fp_rep_ok)
             bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions
             env_Fp6_mul_by_v Hc6 Hxi HFp2copy HFp2copy).
  Qed.
End Tower.
