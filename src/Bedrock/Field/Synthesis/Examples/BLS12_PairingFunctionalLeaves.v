(** * BLS12-381: the functional pairing theorem for the extraction's list plus verified extras.

    [bls12_extra_funcs] are the functions called by the tower that the extraction's list
    ([BLS12_PairingFunctionalEnv.bls12_pairing_funcs]) does not contain, with verified bodies:
    Fp [from_word] (with the fiat [to_mont] it calls), Fp [opp] (fiat synthesis), and the Fp2
    functions [felem_copy], [add], [sub], [mul] (tower library), [square], [opp], [inv] (new
    bodies), and the Fermat inverse [bls12_inv] with its helper [bls12_inv_pow_word]
    ([BLS12_FpInvFermat]).  The list is not part of [BLS12_Pairing.bls12_all_pairing_funcs]; the generated
    C/Rust code is unchanged.

    [bls12_pairing_functional_reduced] is [spec_of_bls12_pairing_functional] for
    [map.of_list (bls12_pairing_funcs ++ bls12_extra_funcs)], assuming the three leaf specs
    discharged afterwards; [bls12_pairing_functional_unconditional] is the theorem without them.
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
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctional.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalClosed.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingFunctionalEnv.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpExtra.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp2.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesTower.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp12.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_PairingLeavesFp12SqrInv.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_FpInvFermat.
Require Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Require Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Require Bedrock.Field.Synthesis.Examples.BLS12_CycExp.
Module MS := Bedrock.Field.Synthesis.Examples.BLS12_MillerStepFunctional.
Module FE := Bedrock.Field.Synthesis.Examples.BLS12_FinalExp.
Module CE := Bedrock.Field.Synthesis.Examples.BLS12_CycExp.

Import BinInt String List.ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Existing Instances
  Defaults64.default_parameters
  Defaults64.default_parameters_ok.

Local Notation function_t := (String.string * Syntax.func)%type.

Definition bls12_extra_funcs : list function_t :=
  [ bls12_from_word; bls12_to_mont; bls12_opp;
    bls12_Fp2_felem_copy; bls12_Fp2_add; bls12_Fp2_sub; bls12_Fp2_mul;
    bls12_Fp2_square; bls12_Fp2_opp; bls12_Fp2_inv;
    bls12_inv_pow_word; bls12_inv ].

Local Notation functions := (map.of_list (bls12_pairing_funcs ++ bls12_extra_funcs) : env).

(** ** Environment facts *)

Lemma first_binding_app_None (l1 l2 : list function_t) (k : string) :
  first_binding l1 k = None -> first_binding (l1 ++ l2) k = first_binding l2 k.
Proof.
  unfold first_binding. induction l1 as [| a l1 IH]; simpl.
  - intros _. reflexivity.
  - destruct (String.eqb (fst a) k); [discriminate | exact IH].
Qed.

(** A function of the extraction's list. *)
Local Ltac env_main := rewrite get_of_list_find; apply first_binding_app; exact eq_refl.
(** A function of [bls12_extra_funcs] (absent from the extraction's list). *)
Local Ltac env_extra :=
  rewrite get_of_list_find, first_binding_app_None by exact eq_refl; exact eq_refl.

Lemma env_mul : map.get functions "bls12_mul" = Some (snd bls12_mul).
Proof. env_main. Qed.
Lemma env_add : map.get functions "bls12_add" = Some (snd bls12_add).
Proof. env_main. Qed.
Lemma env_sub : map.get functions "bls12_sub" = Some (snd bls12_sub).
Proof. env_main. Qed.
Lemma env_square : map.get functions "bls12_square" = Some (snd bls12_square).
Proof. env_main. Qed.
Lemma env_felem_copy : map.get functions "bls12_felem_copy" = Some bls12_felem_copy.
Proof. env_main. Qed.
Lemma env_Fp2_mul_xi :
  map.get functions "bls12_Fp2_mul_xi" = Some (snd BLS12_Pairing.bls12_Fp2_mul_xi).
Proof. env_main. Qed.

Lemma env_from_word : map.get functions "bls12_from_word" = Some (snd bls12_from_word).
Proof. env_extra. Qed.
Lemma env_to_mont : map.get functions "bls12_to_mont" = Some (snd bls12_to_mont).
Proof. env_extra. Qed.
Lemma env_opp : map.get functions "bls12_opp" = Some (snd bls12_opp).
Proof. env_extra. Qed.
Lemma env_Fp2_felem_copy :
  map.get functions "bls12_Fp2_felem_copy" = Some (snd bls12_Fp2_felem_copy).
Proof. env_extra. Qed.
Lemma env_Fp2_add : map.get functions "bls12_Fp2_add" = Some (snd bls12_Fp2_add).
Proof. env_extra. Qed.
Lemma env_Fp2_sub : map.get functions "bls12_Fp2_sub" = Some (snd bls12_Fp2_sub).
Proof. env_extra. Qed.
Lemma env_Fp2_mul : map.get functions "bls12_Fp2_mul" = Some (snd bls12_Fp2_mul).
Proof. env_extra. Qed.
Lemma env_Fp2_square : map.get functions "bls12_Fp2_square" = Some (snd bls12_Fp2_square).
Proof. env_extra. Qed.
Lemma env_Fp2_opp : map.get functions "bls12_Fp2_opp" = Some (snd bls12_Fp2_opp).
Proof. env_extra. Qed.
Lemma env_Fp2_inv : map.get functions "bls12_Fp2_inv" = Some (snd bls12_Fp2_inv).
Proof. env_extra. Qed.
Lemma env_inv_pow_word :
  map.get functions "bls12_inv_pow_word" = Some (snd bls12_inv_pow_word).
Proof. env_extra. Qed.
Lemma env_inv : map.get functions "bls12_inv" = Some (snd bls12_inv).
Proof. env_extra. Qed.

(** ** The discharged leaves *)

Local Ltac envs :=
  first [ exact env_mul | exact env_add | exact env_sub | exact env_square | exact env_felem_copy
        | exact env_from_word | exact env_to_mont | exact env_opp | exact env_Fp2_felem_copy
        | exact env_Fp2_add | exact env_Fp2_sub | exact env_Fp2_mul | exact env_Fp2_square
        | exact env_Fp2_opp | exact env_Fp2_inv ].

Lemma bls12_Fp2_mul_leaf : MS.spec_of_Fp2_mul functions.
Proof. eapply bls12_Fp2_mul_spec; envs. Qed.

(** ** The three leaves discharged last *)

(** The Fp inverse: the verified Fermat body of [BLS12_FpInvFermat] (the C/Rust code calls a
    hand-written divstep inversion instead). *)
Definition spec_of_bls12_Fp_inv (fs : env) : Prop :=
  AbstractField.unop_spec (F:=F (@PrimeField.M_pos MS.bls12_pf_params))
    (field_representation:=MS.bls12_Fp_rep) AbstractField.un_inv fs.

(** Fp12 square and inverse: [DodecicFieldExtensionsSqr.Fp12_sqr_ok],
    [DodecicFieldExtensionsInv.Fp12_inv_ok], with the Fp6 square model bridge of
    [BLS12_PairingLeavesFp12SqrInv]. *)
Definition bls12_pairing_remaining_leaves (fs : env) : Prop :=
  MS.spec_of_Fp12_sqr fs /\ FE.spec_of_Fp12_inv fs.

Theorem bls12_pairing_functional_reduced :
  spec_of_bls12_Fp_inv functions ->
  bls12_pairing_remaining_leaves functions ->
  spec_of_bls12_pairing_functional functions.
Proof.
  intros Hinv (H23 & H29).
  apply (bls12_pairing_functional_of_arith_leaves bls12_extra_funcs).
  pose proof bls12_Fp2_mul_leaf as Hmul2.
  refine (conj Hmul2 _).
  refine (conj _ _). { eapply bls12_Fp2_add_spec; envs. }
  refine (conj _ _). { eapply bls12_Fp2_sub_spec; envs. }
  refine (conj _ _).
  { eapply bls12_Fp2_square_spec.
    all: lazymatch goal with |- map.get _ _ = _ => envs | _ => exact Hmul2 end. }
  refine (conj _ _).
  { eapply bls12_Fp2_inv_spec.
    all: lazymatch goal with |- map.get _ _ = _ => envs | _ => exact Hinv end. }
  refine (conj _ _). { eapply bls12_Fp2_opp_spec; envs. }
  refine (conj _ _). { eapply bls12_Fp2_felem_copy_spec; envs. }
  pose proof (bls12_Fp2_felem_copy_spec functions env_felem_copy env_Fp2_felem_copy) as Hcp2.
  pose proof (bls12_Fp_felem_copy_leaf functions env_felem_copy) as Hcp1.
  pose proof (bls12_Fp_opp_leaf functions env_opp) as Hop1.
  pose proof (bls12_Fp_sub_leaf functions env_sub) as Hsub1.
  pose proof (bls12_Fp_add_leaf_MS functions env_add) as Hadd1.
  assert (Hadd2 : MS.spec_of_Fp2_add functions) by (eapply bls12_Fp2_add_spec; envs).
  assert (Hsub2 : MS.spec_of_Fp2_sub functions) by (eapply bls12_Fp2_sub_spec; envs).
  pose proof (bls12_Fp12_mul_leaf_FE bls12_extra_funcs Hcp2 Hadd2 Hsub2 Hmul2
                Hcp1 Hsub1 Hadd1) as H28.
  refine (conj H23 _).
  refine (conj (bls12_Fp12_felem_copy_leaf bls12_extra_funcs Hcp2) _).
  refine (conj (bls12_Fp_mul_leaf functions env_mul) _).
  refine (conj (bls12_Fp_felem_copy_leaf functions env_felem_copy) _).
  refine (conj (bls12_Fp_from_word_leaf_MS functions env_from_word env_to_mont) _).
  refine (conj H28 _).
  refine (conj H29 _).
  refine (conj _ _).
  { eapply bls12_Fp12_conjugate_leaf; [exact Hcp2 |].
    eapply bls12_Fp2_opp_spec; envs. }
  refine (conj (bls12_Fp2_mul_xi_flat functions env_Fp2_mul_xi Hcp1 Hsub1 Hadd1) _).
  refine (conj (bls12_Fp_from_word_leaf_CE functions env_from_word env_to_mont) _).
  refine (conj (bls12_Fp12_frobenius_leaf bls12_extra_funcs Hcp2 Hcp1 Hop1 Hmul2) _).
  exact (bls12_Fp12_frobenius_p2_leaf bls12_extra_funcs Hcp2 Hmul2).
Qed.

Lemma bls12_Fp_inv_leaf : spec_of_bls12_Fp_inv functions.
Proof.
  exact (bls12_inv_ok functions env_inv env_inv_pow_word env_square env_mul env_felem_copy
           env_from_word env_to_mont).
Qed.

Theorem bls12_pairing_functional_unconditional : spec_of_bls12_pairing_functional functions.
Proof.
  pose proof bls12_Fp_inv_leaf as Hinv.
  apply (bls12_pairing_functional_reduced Hinv).
  pose proof (bls12_Fp2_felem_copy_spec functions env_felem_copy env_Fp2_felem_copy) as Hcp2.
  pose proof bls12_Fp2_mul_leaf as Hmul2.
  assert (Hadd2 : MS.spec_of_Fp2_add functions) by (eapply bls12_Fp2_add_spec; envs).
  assert (Hsub2 : MS.spec_of_Fp2_sub functions) by (eapply bls12_Fp2_sub_spec; envs).
  assert (Hsqr2 : MS.spec_of_Fp2_sqr functions).
  { eapply bls12_Fp2_square_spec.
    all: lazymatch goal with |- map.get _ _ = _ => envs | _ => exact Hmul2 end. }
  assert (Hinv2 : MS.spec_of_Fp2_inv functions).
  { eapply bls12_Fp2_inv_spec.
    all: lazymatch goal with |- map.get _ _ = _ => envs | _ => exact Hinv end. }
  assert (Hopp2 : MS.spec_of_Fp2_opp functions) by (eapply bls12_Fp2_opp_spec; envs).
  pose proof (bls12_Fp_felem_copy_leaf functions env_felem_copy) as Hcp1.
  pose proof (bls12_Fp_sub_leaf functions env_sub) as Hsub1.
  pose proof (bls12_Fp_add_leaf_MS functions env_add) as Hadd1.
  refine (conj _ _);
  [ eapply (bls12_Fp12_sqr_leaf_MS bls12_extra_funcs)
  | eapply (bls12_Fp12_inv_leaf_FE bls12_extra_funcs) ].
  (* callee specs chosen by the spec constant (no [exact] against a wrong spec) *)
  all:
    lazymatch goal with
    | |- MS.spec_of_Fp2_felem_copy _ => exact Hcp2
    | |- MS.spec_of_Fp2_add _ => exact Hadd2
    | |- MS.spec_of_Fp2_sub _ => exact Hsub2
    | |- MS.spec_of_Fp2_mul _ => exact Hmul2
    | |- MS.spec_of_Fp2_sqr _ => exact Hsqr2
    | |- MS.spec_of_Fp2_inv _ => exact Hinv2
    | |- MS.spec_of_Fp2_opp _ => exact Hopp2
    | |- MS.spec_of_Fp_felem_copy _ => exact Hcp1
    | |- AbstractField.binop_spec AbstractField.bin_sub _ => exact Hsub1
    | |- AbstractField.binop_spec AbstractField.bin_add _ => exact Hadd1
    | |- ?g => idtac "UNMATCHED" g; fail
    end.
Qed.

Print Assumptions bls12_pairing_functional_unconditional.

(* Use downstream (SSProve/Commitments, not part of this repository).  A lemma of the form
   [bls12_pairing_computes_pair_of_leaves : forall fs, <leaf specs of fs> -> <pair spec of fs>]
   whose leaf premise is [spec_of_bls12_pairing_functional fs] yields the premise-free form
     Corollary bls12_pairing_computes_pair :
       <pair spec of (map.of_list (bls12_pairing_funcs ++ bls12_extra_funcs))>.
     Proof. exact (bls12_pairing_computes_pair_of_leaves _
                     bls12_pairing_functional_unconditional). Qed. *)
