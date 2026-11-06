(** * BLS12-381: the Fp12 square and inverse leaf specs of the functional pairing theorem.

    The library lemmas [DodecicFieldExtensionsSqr.Fp12_sqr_ok] and
    [DodecicFieldExtensionsInv.Fp12_inv_ok] take the Fp6 square callee with the generic
    model [Fsquare x = Fmul x x] ([= fp6_mul x x]), while [CubicFieldExtensions.Fp6_sqr_ok]
    proves it with the Chung-Hasan model [fp6_sqr].  The bridge is proved once, on abstract
    parameters (any prime field, any [beta], [xi]): [fp6_sqr_eq_mul_abstract] is a ring identity
    over six abstract Fp2 coordinates, and [Fp6_square_of_sqr] turns the [fp6_sqr] spec into the
    [Fmul x x] spec of [DS]/[DI].  Instantiating it at the BLS12 parameters is then a plain
    application, with no unification against the instances of the BLS12 tower (a direct
    elaboration against the [DS] instance took over 6 minutes).
*)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Specs.PrimeField.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.FieldExtensions.CubicFieldExtensions.
Require Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSqr.
Require Bedrock.Field.FieldExtensions.DodecicFieldExtensionsInv.
Module DS := Bedrock.Field.FieldExtensions.DodecicFieldExtensionsSqr.
Module DI := Bedrock.Field.FieldExtensions.DodecicFieldExtensionsInv.
Module CF := Bedrock.Field.FieldExtensions.CubicFieldExtensions.

(** ** A unop spec only depends on its model pointwise *)

Section UnopModel.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {F : Type} {field_parameters : AbstractField.FieldParameters F}
          {field_representation : AbstractField.FieldRepresentation (F:=F)}.

  Lemma unop_spec_model_eq {name} (op1 op2 : AbstractField.UnOp name) fs :
    op1.(AbstractField.un_xbounds) = op2.(AbstractField.un_xbounds) ->
    op1.(AbstractField.un_outbounds) = op2.(AbstractField.un_outbounds) ->
    (forall x, op1.(AbstractField.un_model) x = op2.(AbstractField.un_model) x) ->
    AbstractField.unop_spec op1 fs -> AbstractField.unop_spec op2 fs.
  Proof.
    intros Hx Ho Hm H. cbv [AbstractField.unop_spec] in *.
    intros pout px out x Rr tr m0 Hpre. destruct Hpre as (Hb & HX & HO).
    rewrite <- Hx in Hb.
    eapply WeakestPreconditionProperties.Proper_call;
      [ | exact (H pout px out x Rr tr m0 (conj Hb (conj HX HO))) ].
    intros tr' m' rets (Hrets & Htr & o & Hv & Hbo & Hs).
    split; [exact Hrets|]. split; [exact Htr|].
    exists o. split; [rewrite Hv; apply Hm|]. split; [rewrite <- Ho; exact Hbo| exact Hs].
  Qed.
End UnopModel.

(** ** The Fp6 square model identity, on abstract parameters *)

Section Abstract.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {prime_parameters : PrimeFieldParameters}.
  Existing Instance prime_field_parameters.
  Context {F_representation : AbstractField.FieldRepresentation (F:=F M_pos)}.
  Variable beta xi_re xi_im : F M_pos.
  Variable fp6_prefix fp2_prefix : string.

  Add Ring Fp_ring_abs : (@F.ring_theory M_pos).

  Lemma fp6_sqr_eq_mul_abstract (a : (F M_pos * F M_pos) * (F M_pos * F M_pos) * (F M_pos * F M_pos)) :
    BLS12Fp6Spec.fp6_sqr M_pos beta xi_re xi_im a = BLS12Fp6Spec.fp6_mul M_pos beta xi_re xi_im a a.
  Proof.
    destruct a as [[[a00 a01] [a10 a11]] [a20 a21]].
    cbv [BLS12Fp6Spec.fp6_sqr BLS12Fp6Spec.fp6_mul BLS12Fp6Spec.fp6_build
         BLS12Fp6Spec.fp6_c0 BLS12Fp6Spec.fp6_c1 BLS12Fp6Spec.fp6_c2
         BLS12Fp6Spec.fp2_add BLS12Fp6Spec.fp2_sub BLS12Fp6Spec.fp2_mul
         BLS12Fp6Spec.fp2_mul_xi fst snd].
    f_equal; [f_equal|]; f_equal; ring.
  Qed.

  Lemma Fp6_square_of_sqr_DS fs :
    CF.spec_of_Fp6_sqr beta xi_re xi_im fp6_prefix fp2_prefix fs ->
    DS.spec_of_Fp6_square beta xi_re xi_im fp6_prefix fp2_prefix fs.
  Proof.
    cbv [CF.spec_of_Fp6_sqr DS.spec_of_Fp6_square].
    apply unop_spec_model_eq; [reflexivity | reflexivity |].
    intros x. exact (fp6_sqr_eq_mul_abstract x).
  Qed.

  Lemma Fp6_square_of_sqr_DI fs :
    CF.spec_of_Fp6_sqr beta xi_re xi_im fp6_prefix fp2_prefix fs ->
    DI.spec_of_Fp6_square beta xi_re xi_im fp6_prefix fp2_prefix fs.
  Proof.
    cbv [CF.spec_of_Fp6_sqr DI.spec_of_Fp6_square].
    apply unop_spec_model_eq; [reflexivity | reflexivity |].
    intros x. exact (fp6_sqr_eq_mul_abstract x).
  Qed.

  Lemma Fp6_inv_DI fs :
    CF.spec_of_Fp6_inv beta xi_re xi_im fp6_prefix fp2_prefix fs ->
    DI.spec_of_Fp6_inv beta xi_re xi_im fp6_prefix fp2_prefix fs.
  Proof. intros H; exact H. Qed.
End Abstract.

(** ** The BLS12 instances *)

Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.FieldExtensions.DodecicFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalEnv.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp2.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesTower.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp12.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module FE := Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.

Import List.ListNotations.
Local Open Scope string_scope.
Local Open Scope list_scope.

Existing Instances
  Bitwidth64.BW64
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

Local Notation function_t := (String.string * Syntax.func)%type.
Local Notation pp := MS.bls12_pf_params.
Local Notation frep := MS.bls12_Fp_rep.

Section Fp12SqrInv.
  Variable extra : list function_t.
  Local Notation functions := (map.of_list (bls12_pairing_funcs ++ extra) : env).

  Local Ltac env_main := rewrite get_of_list_find; apply first_binding_app; exact eq_refl.

  Lemma env_Fp12_sqr :
    map.get functions (fst (Fp12_sqr (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)) =
    Some (snd (Fp12_sqr (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.
  Lemma env_Fp12_inv :
    map.get functions (fst (Fp12_inv (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)) =
    Some (snd (Fp12_inv (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix)).
  Proof. env_main. Qed.

  Hypothesis HFp2copy : MS.spec_of_Fp2_felem_copy functions.
  Hypothesis HFp2add : MS.spec_of_Fp2_add functions.
  Hypothesis HFp2sub : MS.spec_of_Fp2_sub functions.
  Hypothesis HFp2mul : MS.spec_of_Fp2_mul functions.
  Hypothesis HFp2sqr : MS.spec_of_Fp2_sqr functions.
  Hypothesis HFp2inv : MS.spec_of_Fp2_inv functions.
  Hypothesis HFp2opp : MS.spec_of_Fp2_opp functions.
  Hypothesis HFpcopy : MS.spec_of_Fp_felem_copy functions.
  Hypothesis HFpsub :
    AbstractField.binop_spec (F:=F (@PrimeField.M_pos pp)) (field_representation:=frep)
      AbstractField.bin_sub functions.
  Hypothesis HFpadd :
    AbstractField.binop_spec (F:=F (@PrimeField.M_pos pp)) (field_representation:=frep)
      AbstractField.bin_add functions.

  Let Hc6 := bls12_Fp6_felem_copy_spec extra HFp2copy.
  Let Ha6 := bls12_Fp6_add_leaf extra HFp2copy HFp2add.
  Let Hm6 := bls12_Fp6_mul_leaf extra HFp2copy HFp2add HFpcopy HFp2mul HFp2sub HFpsub HFpadd.
  Let Hv6 := bls12_Fp6_mul_by_v_leaf extra HFp2copy HFpcopy HFpsub HFpadd.
  Let Ho6 := bls12_Fp6_opp_spec extra HFp2copy HFp2opp.
  Let Hc12 := bls12_Fp12_felem_copy_leaf extra HFp2copy.
  Let Hs6 := bls12_Fp6_sub_spec extra HFp2copy HFp2sub.
  Let Hq6 := bls12_Fp6_sqr_spec extra HFp2copy HFp2add HFp2sub HFp2mul HFp2sqr HFpcopy HFpsub HFpadd.
  Let Hi6 := bls12_Fp6_inv_spec extra HFp2copy HFp2add HFp2sub HFp2mul HFp2sqr HFp2inv HFpcopy
               HFpsub HFpadd.

  Let HsqDS := Fp6_square_of_sqr_DS (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions Hq6.
  Let HsqDI := Fp6_square_of_sqr_DI (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions Hq6.
  Let HinvDI := Fp6_inv_DI (prime_parameters:=pp) (F_representation:=frep)
                 bls12_beta bls12_xi_re bls12_xi_im fp6_prefix fp2_prefix functions Hi6.

  (** Callee specs chosen by the spec constant (no [exact] against a wrong spec). *)
  Local Ltac specs :=
    lazymatch goal with
    | |- context [DS.spec_of_Fp6_square] => exact HsqDS
    | |- context [DS.spec_of_Fp6_felem_copy] => exact Hc6
    | |- context [DS.spec_of_Fp6_add] => exact Ha6
    | |- context [DS.spec_of_Fp6_mul] => exact Hm6
    | |- context [DS.spec_of_Fp6_sub] => exact Hs6
    | |- context [DS.spec_of_Fp6_mul_by_v] => exact Hv6
    | |- context [DS.spec_of_Fp12_copy] => exact Hc12
    | |- context [DI.spec_of_Fp6_square] => exact HsqDI
    | |- context [DI.spec_of_Fp6_inv] => exact HinvDI
    | |- context [DI.spec_of_Fp6_felem_copy] => exact Hc6
    | |- context [DI.spec_of_Fp6_add] => exact Ha6
    | |- context [DI.spec_of_Fp6_mul] => exact Hm6
    | |- context [DI.spec_of_Fp6_sub] => exact Hs6
    | |- context [DI.spec_of_Fp6_opp] => exact Ho6
    | |- context [DI.spec_of_Fp6_mul_by_v] => exact Hv6
    | |- context [DI.spec_of_Fp12_copy] => exact Hc12
    | |- ?g => idtac "UNMATCHED" g; fail
    end.

  Lemma bls12_Fp12_sqr_spec :
    DS.spec_of_Fp12_sqr (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix functions.
  Proof.
    eapply (DS.Fp12_sqr_ok (prime_parameters:=pp) (F_representation:=frep)
              (bounds_equiv:=bls12_Fp_bounds_equiv)
              bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix
              functions env_Fp12_sqr).
    all: specs.
  Qed.

  Lemma bls12_Fp12_inv_spec :
    DI.spec_of_Fp12_inv (prime_parameters:=pp) (F_representation:=frep)
      bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix functions.
  Proof.
    eapply (DI.Fp12_inv_ok (prime_parameters:=pp) (F_representation:=frep)
              (F_representation_ok:=MS.bls12_Fp_rep_ok)
              (bounds_equiv:=bls12_Fp_bounds_equiv)
              bls12_beta bls12_xi_re bls12_xi_im fp12_prefix fp6_prefix fp2_prefix
              functions env_Fp12_inv).
    all: specs.
  Qed.

  Lemma bls12_Fp12_sqr_leaf_MS : MS.spec_of_Fp12_sqr functions.
  Proof. exact bls12_Fp12_sqr_spec. Qed.
  Lemma bls12_Fp12_inv_leaf_FE : FE.spec_of_Fp12_inv functions.
  Proof. exact bls12_Fp12_inv_spec. Qed.
End Fp12SqrInv.
