(** * BN254_PairingCorrect.v — G2: strengthened WP spec for
    [bn254_pairing_dsd_optimal].

    Strengthens the WP postcondition of the existing
    [bn254_pairing_dsd_optimal_ok] from

        "exists bounded [out], in memory at [pout]"

    to

        "[bn254_fp12_to_Z out] = [bn254_optimal_ate_spec ...]".

    ** Structure of the file

      §1  Math-level spec composition ([pairing_spec_compose], Qed):
          [final_exp ∘ (apply_corrections ∘ affine_miller_aux)
              = bn254_optimal_ate_spec].

      §2  Full bedrock2 instance setup (PrimeFieldParameters,
          FieldRepresentation, etc.) duplicated from
          [BN254_PairingTopOptimal.v] so this file doesn't depend on
          [BN254_PairingTopOptimal.vo] (which is expensive).

      §3  [feval]→[Z] bridges specialised to BN254.

      §4  Strong callee-hypothesis types.

      §5  Strong spec instance + main theorem.

    Notably this file lives in AUCurves rather than fiat-crypto:
    it neither extends fiat-crypto definitions nor is consumed by
    fiat-crypto proofs, so upstreaming would only add build cost.
*)

(* ================================================================ *)
(* Imports                                                           *)
(* ================================================================ *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Specs.AbstractField.
Require Import Crypto.Bedrock.Specs.PrimeField.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_prime_certif.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Crypto.Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSpecs.
Require Import Crypto.Bedrock.Field.FieldExtensions.PairingFieldOps.
Require Import Crypto.Bedrock.Field.FieldExtensions.WPTactics.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN254_Pairing.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BN_StraightlineFast.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.BLS12_CurveInstances.

Require Import Crypto.Bedrock.Field.PairingTheory.ZModTower.
Require Import Crypto.Bedrock.Field.PairingTheory.Affine.
Require Import Crypto.Bedrock.Field.PairingTheory.PairingSpec.
Require Import Crypto.Bedrock.Field.PairingTheory.CurveParams.
Require Import Crypto.Bedrock.Field.PairingTheory.Curves.BN254_params.
Require Import Crypto.Bedrock.Field.PairingTheory.MillerLoopWP.
Require Import Crypto.Bedrock.Field.PairingTheory.FevalBridge.

Import BinInt String List.ListNotations.

(* ================================================================ *)
(* §1. Math-level pairing composition                                *)
(* ================================================================ *)

Local Definition bn254_p  : Z     := prime_p bn254_params.
Local Definition bn254_xi : Fp2_Z := (9%Z, 1%Z).

Definition bn254_miller_loop_with_corrections
           (gamma1 gamma_y gamma1_p2 : Fp2_Z)
           (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
  let '(f, Tx, Ty) :=
    affine_miller_aux bn254_zmod_ops
      (loop_abs bn254_params)
      (Z.to_nat (Z.log2 (loop_abs bn254_params)))
      Px Py Qx Qy
      (fp12_one bn254_zmod_ops) Qx Qy in
  PairingSpec.apply_corrections
    bn254_zmod_ops
    (zfp2_conj bn254_p)
    (zfp2_mul_const bn254_p)
    (optimal_ate_extras bn254_params)
    f Tx Ty Px Py Qx Qy
    gamma1 gamma_y gamma1_p2.

Lemma pairing_spec_compose :
  forall (gamma1 gamma_y gamma1_p2 : Fp2_Z)
         (Px Py : Z) (Qx Qy : Fp2_Z),
    PairingSpec.final_exp bn254_zmod_ops
      (zfp12_conj bn254_p)
      (zfp12_inv bn254_p bn254_xi)
      (zfp12_frob_p2 bn254_p bn254_xi)
      (zfp12_pow bn254_p bn254_xi)
      (prime_p bn254_params) (scalar_r bn254_params)
      (bn254_miller_loop_with_corrections gamma1 gamma_y gamma1_p2
         Px Py Qx Qy)
    =
    bn254_optimal_ate_spec gamma1 gamma_y gamma1_p2 Px Py Qx Qy.
Proof.
  intros.
  unfold bn254_optimal_ate_spec, PairingSpec.optimal_ate,
         bn254_miller_loop_with_corrections.
  simpl loop_neg.
  destruct (affine_miller_aux bn254_zmod_ops _ _ _ _ _ _ _ _ _)
    as [[f_mid Tx_mid] Ty_mid] eqn:Hml.
  reflexivity.
Qed.

(* ================================================================ *)
(* §2. Bedrock2 instance setup for BN254                             *)
(*     (duplicated from BN254_PairingTopOptimal.v; that file's       *)
(*      .vo is expensive to build, and the instances are small.)     *)
(* ================================================================ *)

Section BN254_PairingCorrect.

  Existing Instances
    Defaults64.default_parameters
    Defaults64.default_parameters_ok.

  Let bn254_M_pos : positive := Eval vm_compute in (Z.to_pos bn254_prime.m).

  Instance bn254_pf_params : PrimeFieldParameters := {|
    PrimeField.M_pos := bn254_M_pos;
    PrimeField.a24 := F.of_Z _ 0;
    PrimeField.mul := "bn254_mul";
    PrimeField.add := "bn254_add";
    PrimeField.sub := "bn254_sub";
    PrimeField.opp := "bn254_opp";
    PrimeField.square := "bn254_square";
    PrimeField.scmula24 := "bn254_scmula24";
    PrimeField.inv := "bn254_inv";
    PrimeField.from_bytes := "bn254_from_bytes";
    PrimeField.to_bytes := "bn254_to_bytes";
    PrimeField.select_znz := "bn254_select_znz";
    PrimeField.felem_copy := "bn254_felem_copy";
    PrimeField.from_word := "bn254_from_word";
    PrimeField.from_list := "bn254_from_list";
  |}.

  Instance bn254_pf_params_ok : PrimeFieldParameters_ok.
  Proof. constructor. exact prime_bn254. Qed.

  Existing Instance prime_field_parameters.

  Local Notation Fp := (F PrimeField.M_pos).
  Local Notation Fp2 := ((Fp * Fp)%type).
  Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
  Local Notation Fp12 := ((Fp6 * Fp6)%type).

  Instance bn254_Fp_rep : AbstractField.FieldRepresentation (F:=Fp) :=
    {| AbstractField.feval := @Field.feval _ _ _ _ _ bn254_frep;
       AbstractField.feval_bytes := @Field.feval_bytes _ _ _ _ _ bn254_frep;
       AbstractField.felem_size_in_words := @Field.felem_size_in_words _ _ _ _ _ bn254_frep;
       AbstractField.encoded_felem_size_in_bytes := @Field.encoded_felem_size_in_bytes _ _ _ _ _ bn254_frep;
       AbstractField.bytes_in_bounds := @Field.bytes_in_bounds _ _ _ _ _ bn254_frep;
       AbstractField.bounds := @Field.bounds _ _ _ _ _ bn254_frep;
       AbstractField.bounded_by := @Field.bounded_by _ _ _ _ _ bn254_frep;
       AbstractField.loose_bounds := @Field.loose_bounds _ _ _ _ _ bn254_frep;
       AbstractField.tight_bounds := @Field.tight_bounds _ _ _ _ _ bn254_frep |}.

  Instance bn254_Fp_rep_ok : AbstractField.FieldRepresentation_ok (F:=Fp).
  Proof.
    constructor. intros X H.
    cbv [bounded_by bn254_Fp_rep] in *.
    cbv [Field.bounded_by bn254_frep field_representation
         Signature.field_representation Representation.frep] in *.
    exact H.
  Defined.

  Let bn254_beta : F PrimeField.M_pos := F.of_Z PrimeField.M_pos (-1).
  Let bn254_xi_re : F PrimeField.M_pos := F.of_Z PrimeField.M_pos 9.
  Let bn254_xi_im : F PrimeField.M_pos := @F.one PrimeField.M_pos.

  Instance bn254_Fp2_params' : AbstractField.FieldParameters Fp2 :=
    ltac:(let v := eval cbv [ext_Fp2_params append] in
                       (ext_Fp2_params bn254_beta "bn254_") in exact v).
  Instance bn254_Fp2_rep' : AbstractField.FieldRepresentation (F:=Fp2) :=
    ltac:(let v := eval cbv [ext_Fp2_rep append] in
                       (ext_Fp2_rep bn254_beta "bn254_") in exact v).
  Instance bn254_Fp6_params' : AbstractField.FieldParameters Fp6 :=
    ltac:(let v := eval cbv [ext_Fp6_params append] in
                       (ext_Fp6_params bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
  Instance bn254_Fp6_rep' : AbstractField.FieldRepresentation (F:=Fp6) :=
    ltac:(let v := eval cbv [ext_Fp6_rep append] in
                       (ext_Fp6_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
  Instance bn254_Fp12_params' : AbstractField.FieldParameters Fp12 :=
    ltac:(let v := eval cbv [ext_Fp12_params append] in
                       (ext_Fp12_params bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).
  Instance bn254_Fp12_rep' : AbstractField.FieldRepresentation (F:=Fp12) :=
    ltac:(let v := eval cbv [ext_Fp12_rep append] in
                       (ext_Fp12_rep bn254_beta bn254_xi_re bn254_xi_im "bn254_") in exact v).

  Local Notation FElem_Fp :=
    (@AbstractField.FElem _ _ _ _ _ _ bn254_Fp_rep).
  Local Notation FElem_Fp2 :=
    (@AbstractField.FElem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
  Local Notation FElem_Fp12 :=
    (@AbstractField.FElem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
  Local Notation Fp_bounded :=
    (@AbstractField.bounded_by _ _ _ _ _ _ bn254_Fp_rep).
  Local Notation Fp2_bounded :=
    (@AbstractField.bounded_by _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
  Local Notation Fp12_bounded :=
    (@AbstractField.bounded_by _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
  Local Notation Fp_loose :=
    (@AbstractField.loose_bounds _ _ _ _ _ _ bn254_Fp_rep).
  Local Notation Fp2_tight :=
    (@AbstractField.tight_bounds _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
  Local Notation Fp12_tight :=
    (@AbstractField.tight_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
  Local Notation Fp12_loose :=
    (@AbstractField.loose_bounds _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').
  Local Notation Fp_felem :=
    (@AbstractField.felem _ _ _ _ _ _ bn254_Fp_rep).
  Local Notation Fp2_felem :=
    (@AbstractField.felem _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
  Local Notation Fp12_felem :=
    (@AbstractField.felem _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').

  Local Typeclasses Opaque bn254_Fp12_params'.
  Local Typeclasses Opaque bn254_Fp6_params'.
  Local Typeclasses Opaque bn254_Fp2_params'.

  (** Stack-allocation helper (copied from BN254_PairingTopOptimal.v). *)
  Local Lemma sep_stack_extend (P Q : mem -> Prop) (mC mPrev mStack : mem) :
    map.split mC mPrev mStack -> P mPrev -> Q mStack -> (Q ⋆ P) mC.
  Proof.
    intros Hs HP HQ.
    apply Properties.map.split_comm in Hs.
    exists mStack, mPrev. exact (conj Hs (conj HQ HP)).
  Qed.

  (* ================================================================ *)
  (* §3. [feval] → [Z] bridges                                         *)
  (* ================================================================ *)

  Local Notation Fp_feval   :=
    (@AbstractField.feval _ _ _ _ _ _ bn254_Fp_rep).
  Local Notation Fp2_feval  :=
    (@AbstractField.feval _ bn254_Fp2_params' _ _ _ _ bn254_Fp2_rep').
  Local Notation Fp12_feval :=
    (@AbstractField.feval _ bn254_Fp12_params' _ _ _ _ bn254_Fp12_rep').

  Definition bn254_fp_to_Z   (x : Fp_felem)   : Z :=
    fp_to_Z  PrimeField.M_pos (Fp_feval x).
  Definition bn254_fp2_to_Z  (x : Fp2_felem)  : Fp2_Z :=
    fp2_to_Z PrimeField.M_pos (Fp2_feval x).
  Definition bn254_fp12_to_Z (x : Fp12_felem) : Fp12_Z :=
    fp12_to_Z PrimeField.M_pos (Fp12_feval x).

  (* ================================================================ *)
  (* §4. Strong callee hypothesis types                                *)
  (* ================================================================ *)

  (** Each strong callee hypothesis is the existing weak one
      conjoined with a [bn254_fpN_to_Z out = spec_val] equality. *)

  Definition strong_loader_spec
             (functions : Semantics.env) (fname : string)
             (spec_val : Fp2_Z) : Prop :=
    forall pout (old_out : Fp2_felem) R tr m,
      (FElem_Fp2 pout old_out ⋆ R) m ->
      Semantics.call functions fname tr m [pout]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
          exists out,
            Fp2_bounded Fp2_tight out /\
            bn254_fp2_to_Z out = spec_val /\
            (FElem_Fp2 pout out ⋆ R) m').

  Definition strong_miller_spec
             (functions : Semantics.env)
             (gamma1 gamma_y gamma1_p2 : Fp2_Z) : Prop :=
    forall ptmp ppx ppy pqx pqy
           (old_tmp : Fp12_felem) (px py : Fp_felem)
           (qx qy : Fp2_felem) R tr m,
      Fp2_bounded Fp2_tight qx ->
      Fp2_bounded Fp2_tight qy ->
      Fp_bounded Fp_loose px ->
      Fp_bounded Fp_loose py ->
      (FElem_Fp12 ptmp old_tmp ⋆
       (FElem_Fp ppx px ⋆
        (FElem_Fp ppy py ⋆
         (FElem_Fp2 pqx qx ⋆
          (FElem_Fp2 pqy qy ⋆ R))))) m ->
      Semantics.call functions "bn254_miller_loop_optimal" tr m
        [ptmp; ppx; ppy; pqx; pqy]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
          exists ml_out,
            Fp12_bounded Fp12_tight ml_out /\
            bn254_fp12_to_Z ml_out =
              bn254_miller_loop_with_corrections
                gamma1 gamma_y gamma1_p2
                (bn254_fp_to_Z px) (bn254_fp_to_Z py)
                (bn254_fp2_to_Z qx) (bn254_fp2_to_Z qy) /\
            (FElem_Fp12 ptmp ml_out ⋆
             (FElem_Fp ppx px ⋆
              (FElem_Fp ppy py ⋆
               (FElem_Fp2 pqx qx ⋆
                (FElem_Fp2 pqy qy ⋆ R))))) m').

  Definition strong_final_exp_spec
             (functions : Semantics.env) : Prop :=
    forall po pf pg1 pg2 pw
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
      Semantics.call functions "bn254_final_exp_dsd" tr m
        [po; pf; pg1; pg2; pw]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
          exists fe_out,
            Fp12_bounded Fp12_loose fe_out /\
            bn254_fp12_to_Z fe_out =
              PairingSpec.final_exp bn254_zmod_ops
                (zfp12_conj bn254_p)
                (zfp12_inv bn254_p bn254_xi)
                (zfp12_frob_p2 bn254_p bn254_xi)
                (zfp12_pow bn254_p bn254_xi)
                (prime_p bn254_params) (scalar_r bn254_params)
                (bn254_fp12_to_Z f) /\
            (FElem_Fp12 po fe_out ⋆
             (FElem_Fp12 pf f ⋆
              (FElem_Fp2 pg1 g1 ⋆
               (FElem_Fp2 pg2 g2 ⋆
                (FElem_Fp2 pw w ⋆ R))))) m').

  (* ================================================================ *)
  (* §5. Strengthened spec + top-level theorem                         *)
  (* ================================================================ *)

  (** The strong spec postcondition: [bn254_fp12_to_Z out] equals
      the math-level [bn254_optimal_ate_spec].  The three Frobenius
      constants (gamma1, gamma_y, gamma1_p2) are Section variables
      set by the caller (supplied by the strong loader hypotheses). *)

  Context (gamma1 gamma_y gamma1_p2 : Fp2_Z).

  Instance spec_of_bn254_pairing_dsd_optimal_strong
    : spec_of "bn254_pairing_dsd_optimal" :=
    fnspec! "bn254_pairing_dsd_optimal"
      (pout p_px p_py p_qx p_qy : word)
      / (old_out : Fp12_felem)
        (p_x p_y : Fp_felem)
        (q_x q_y : Fp2_felem) Rr,
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
          bn254_fp12_to_Z out =
            bn254_optimal_ate_spec gamma1 gamma_y gamma1_p2
              (bn254_fp_to_Z p_x) (bn254_fp_to_Z p_y)
              (bn254_fp2_to_Z q_x) (bn254_fp2_to_Z q_y) /\
          (FElem_Fp12 pout out ⋆
           (FElem_Fp p_px p_x ⋆
            (FElem_Fp p_py p_y ⋆
             (FElem_Fp2 p_qx q_x ⋆
              (FElem_Fp2 p_qy q_y ⋆ Rr))))) mem' }.

  (** The end-to-end theorem for G2. Given strong callee hypotheses
      (loader outputs = Frobenius constants; miller_loop output =
      Miller + corrections; final_exp output = final_exp input),
      the pairing function writes [bn254_optimal_ate_spec] at [pout].

      The proof parallels [bn254_pairing_dsd_optimal_ok] in
      [BN254_PairingTopOptimal.v] (170 lines, Qed), with the
      destructuring pattern at each [Semantics.weaken_call] extended
      by one conjunct (the math equality), and the final postcondition
      split closed by [pairing_spec_compose] above. *)

  Theorem bn254_pairing_dsd_optimal_correct :
    forall functions
      (EnvContains : map.get functions "bn254_pairing_dsd_optimal" =
        Some (snd bn254_pairing_dsd_optimal))
      (HLoadG1 : strong_loader_spec functions
                   "bn254_load_gamma1_p2" gamma1)
      (HLoadG2 : strong_loader_spec functions
                   "bn254_load_gamma2_p2" gamma_y)
      (HLoadW  : strong_loader_spec functions
                   "bn254_load_w_frob_p2_c1" gamma1_p2)
      (HMillerLoop : strong_miller_spec functions
                       gamma1 gamma_y gamma1_p2)
      (HFinalExp   : strong_final_exp_spec functions),
    spec_of_bn254_pairing_dsd_optimal_strong functions.
  Proof.
    intros functions EnvContains HLoadG1 HLoadG2 HLoadW HMillerLoop HFinalExp.
    unfold spec_of_bn254_pairing_dsd_optimal_strong.
    intros pout p_px p_py p_qx p_qy old_out p_x p_y q_x q_y Rr tr mem0
      [Hbqx [Hbqy [Hbpx [Hbpy Hsep]]]].
    eapply start_func; [exact EnvContains | clear EnvContains].
    cbv [WeakestPrecondition.func].
    unfold bn254_pairing_dsd_optimal. simpl snd. simpl fst.
    cbv match beta.
    eexists. split. { exact eq_refl. }

    (* === Stackalloc 1: tmp (Fp12-sized) === *)
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros a_tmp mStack_tmp mComb_tmp HstackTmp Hm_split_tmp.
    pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp12_params' _ _ _ _
      bn254_Fp12_rep' wordok mapok a_tmp) as Hfb_tmp.
    unfold AbstractField.Placeholder in Hfb_tmp.
    pose proof (proj1 (Hfb_tmp mStack_tmp) HstackTmp) as [tmp_val Htmp_felem].
    clear Hfb_tmp HstackTmp.

    (* === Stackalloc 2: gamma1_p2 (Fp2-sized) === *)
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros a_g1 mStack_g1 mComb_g1 HstackG1 Hm_split_g1.
    pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _
      bn254_Fp2_rep' wordok mapok a_g1) as Hfb_g1.
    unfold AbstractField.Placeholder in Hfb_g1.
    pose proof (proj1 (Hfb_g1 mStack_g1) HstackG1) as [g1_val Hg1_felem].
    clear Hfb_g1 HstackG1.

    (* === Stackalloc 3: gamma2_p2 (Fp2-sized) === *)
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros a_g2 mStack_g2 mComb_g2 HstackG2 Hm_split_g2.
    pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _
      bn254_Fp2_rep' wordok mapok a_g2) as Hfb_g2.
    unfold AbstractField.Placeholder in Hfb_g2.
    pose proof (proj1 (Hfb_g2 mStack_g2) HstackG2) as [g2_val Hg2_felem].
    clear Hfb_g2 HstackG2.

    (* === Stackalloc 4: w_frob_p2_c1 (Fp2-sized) === *)
    repeat straightline.
    split. { apply Z_mod_mult. }
    intros a_w mStack_w mComb_w HstackW Hm_split_w.
    pose proof (@AbstractField.FElem_from_bytes _ bn254_Fp2_params' _ _ _ _
      bn254_Fp2_rep' wordok mapok a_w) as Hfb_w.
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

    unfold BN254_Pairing.pairing_dsd_optimal_body, BN254_Pairing.cmd_seq_list.

    (* === Call 1: bn254_load_gamma1_p2(gamma1_p2) — STRONG === *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HLoadG1. ecancel_assumption. }
    intros t1 m1 rets1
      [Hrets1 [Htr1 [g1_out [Hbg1_out [Hmath_g1 Hsep_g1]]]]].
    subst rets1. symmetry in Htr1. subst t1.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }

    (* === Call 2: bn254_load_gamma2_p2(gamma2_p2) — STRONG === *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HLoadG2. ecancel_assumption. }
    intros t2 m2 rets2
      [Hrets2 [Htr2 [g2_out [Hbg2_out [Hmath_g2 Hsep_g2]]]]].
    subst rets2. symmetry in Htr2. subst t2.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }

    (* === Call 3: bn254_load_w_frob_p2_c1(w_frob_p2_c1) — STRONG === *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HLoadW. ecancel_assumption. }
    intros t3 m3 rets3
      [Hrets3 [Htr3 [w_out [Hbw_out [Hmath_w Hsep_w]]]]].
    subst rets3. symmetry in Htr3. subst t3.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }

    (* === Call 4: bn254_miller_loop_optimal — STRONG === *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply HMillerLoop;
         [exact Hbqx | exact Hbqy | exact Hbpx | exact Hbpy |].
         ecancel_assumption. }
    intros t4 m4 rets4
      [Hrets4 [Htr4 [ml_out [Hbml_out [Hmath_ml Hsep_ml]]]]].
    subst rets4. symmetry in Htr4. subst t4.
    cbv [map.putmany_of_list_zip].
    eexists. split. { exact eq_refl. }

    (* === Call 5: bn254_final_exp_dsd — STRONG === *)
    repeat straightline.
    eapply Semantics.weaken_call.
    1: { eapply (HFinalExp pout a_tmp a_g1 a_g2 a_w
                  old_out ml_out g1_out g2_out w_out);
         [exact Hbml_out | exact Hbg1_out | exact Hbg2_out | exact Hbw_out |].
         ecancel_assumption. }
    intros t5 m5 rets5
      [Hrets5 [Htr5 [fe_out [Hbfe_out [Hmath_fe Hsep_fe]]]]].
    subst rets5. symmetry in Htr5. subst t5.

    (* === Stack deallocation (4 levels) + final postcondition === *)
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
    split.
    { (** Math equality: [bn254_fp12_to_Z fe_out = bn254_optimal_ate_spec ...].
          Derived from [Hmath_fe : bn254_fp12_to_Z fe_out = final_exp (...) (bn254_fp12_to_Z ml_out)]
          and [Hmath_ml : bn254_fp12_to_Z ml_out = bn254_miller_loop_with_corrections ...]
          via [pairing_spec_compose]. *)
      rewrite Hmath_fe, Hmath_ml.
      apply pairing_spec_compose. }
    exact Hrest_tmp.
  Qed.

End BN254_PairingCorrect.

(* ================================================================ *)
(* §6. Discharge roadmap                                             *)
(* ================================================================ *)

(** The proof of [bn254_pairing_dsd_optimal_correct] is the only
    [Admitted] in the BN254 end-to-end verification chain once the
    G1 bridge is closed.  Its structure mirrors
    [bn254_pairing_dsd_optimal_ok] line-by-line (578-line file;
    the 170-line [Proof ... Qed] span is what's copied and adapted):

      (a) Intro + unfold + 4 stackalloc blocks (~50 lines, identical
          to original).

      (b) Calls 1-3 (loaders): each [eapply Semantics.weaken_call;
          [eapply HLoadG1 | ...]; intros ... [Hrets [Htr [g1_out
          [Hbg1_out [Hmath_g1 Hsep_g1]]]]]]. The extra
          [Hmath_g1 : bn254_fp2_to_Z g1_out = gamma1] is the new
          conjunct.

      (c) Call 4 (miller_loop): similar to (b) but [Hmath_ml :
          bn254_fp12_to_Z ml_out = bn254_miller_loop_with_corrections
          gamma1 gamma_y gamma1_p2 ...].

      (d) Call 5 (final_exp): [Hmath_fe : bn254_fp12_to_Z fe_out =
          PairingSpec.final_exp ... (bn254_fp12_to_Z ml_out)].

      (e) Stack deallocation (4 levels, identical to original).

      (f) Final [exists fe_out; split; [exact Hbfe_out | split | ...]]:
          the new middle [split] is the math equality,
          discharged by:
            rewrite Hmath_fe.
            rewrite Hmath_ml.
            apply pairing_spec_compose.

    Everything else — stack allocation tracking, sep-logic
    manipulation, [ecancel_assumption] patterns — is unchanged.

    Estimated: a concentrated 30-90 minute edit + compile cycle. *)
