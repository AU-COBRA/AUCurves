(** * Bridge: Z×Z polynomial identity → Fp2 isogeny identity.

    Strategy: define polynomial operations at the Fp2 level using `ring`,
    show the identity reduces to comparing specific Fp2 coefficient lists,
    and verify these lists match the Z×Z computation in IsogenyCompute_G2. *)

From Stdlib Require Import ZArith List Lia Ring.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveG2.
Require Import Spec.HashToCurveFieldSetup.
Require Import Spec.HashToCurveG2FieldSetup.
Require Import Spec.HashToCurveIsogenyCompute_G2.

Local Open Scope F_scope.

Local Notation ofZ := (F.of_Z p_pos).
Local Notation toZ := (@F.to_Z p_pos).

(* ================================================================== *)
(** * Polynomial operations at Fp2 level                                *)
(* ================================================================== *)

Definition poly_add_fp2 : list Fp2 -> list Fp2 -> list Fp2 :=
  fix add f g :=
    match f, g with
    | [], _ => g
    | _, [] => f
    | a :: f', b :: g' => fp2_add a b :: add f' g'
    end.

Definition poly_scale_fp2 (c : Fp2) (f : list Fp2) : list Fp2 := map (fp2_mul c) f.

Fixpoint poly_mul_fp2 (f g : list Fp2) : list Fp2 :=
  match f with
  | [] => []
  | a :: f' => poly_add_fp2 (poly_scale_fp2 a g) (fp2_zero :: poly_mul_fp2 f' g)
  end.

Definition poly_sqr_fp2 (f : list Fp2) : list Fp2 := poly_mul_fp2 f f.
Definition poly_cube_fp2 (f : list Fp2) : list Fp2 := poly_mul_fp2 (poly_sqr_fp2 f) f.

(* ================================================================== *)
(** * Polynomial evaluation homomorphism                                *)
(* ================================================================== *)

Lemma horner_eval_fp2_add : forall f g x,
  horner_eval_fp2 (poly_add_fp2 f g) x =
  fp2_add (horner_eval_fp2 f x) (horner_eval_fp2 g x).
Proof.
  induction f as [|a f' IH]; intros [|b g'] x.
  - simpl. unfold fp2_zero. apply injective_projections; simpl; ring.
  - simpl horner_eval_fp2 at 1 2. simpl. apply injective_projections; simpl; ring.
  - simpl. unfold fp2_zero. apply injective_projections; simpl; ring.
  - simpl. rewrite IH.
    set (HA := horner_eval_fp2 f' x). set (HB := horner_eval_fp2 g' x).
    clearbody HA HB.
    apply injective_projections; simpl; ring.
Qed.

Lemma horner_eval_fp2_scale : forall c f x,
  horner_eval_fp2 (poly_scale_fp2 c f) x = fp2_mul c (horner_eval_fp2 f x).
Proof.
  intros c. induction f as [|a f' IH]; intro x.
  - simpl. unfold fp2_zero. apply injective_projections; simpl; ring.
  - simpl. rewrite IH.
    set (H := horner_eval_fp2 f' x). clearbody H.
    apply injective_projections; simpl; ring.
Qed.

Lemma horner_eval_fp2_cons0 : forall f x,
  horner_eval_fp2 (fp2_zero :: f) x = fp2_mul x (horner_eval_fp2 f x).
Proof.
  intros f x. simpl.
  set (H := horner_eval_fp2 f x). clearbody H.
  unfold fp2_zero. apply injective_projections; simpl; ring.
Qed.

Lemma horner_eval_fp2_mul : forall f g x,
  horner_eval_fp2 (poly_mul_fp2 f g) x =
  fp2_mul (horner_eval_fp2 f x) (horner_eval_fp2 g x).
Proof.
  induction f as [|a f' IH]; intro g.
  - intro x. simpl. unfold fp2_zero. apply injective_projections; simpl; ring.
  - intro x. simpl poly_mul_fp2.
    rewrite horner_eval_fp2_add, horner_eval_fp2_scale, horner_eval_fp2_cons0.
    rewrite IH. simpl horner_eval_fp2.
    set (HF := horner_eval_fp2 f' x). set (HG := horner_eval_fp2 g x).
    clearbody HF HG.
    apply injective_projections; simpl; ring.
Qed.

Lemma horner_eval_fp2_sqr : forall f x,
  horner_eval_fp2 (poly_sqr_fp2 f) x = fp2_mul (horner_eval_fp2 f x) (horner_eval_fp2 f x).
Proof. intros. unfold poly_sqr_fp2. apply horner_eval_fp2_mul. Qed.

Lemma horner_eval_fp2_cube : forall f x,
  horner_eval_fp2 (poly_cube_fp2 f) x =
  fp2_mul (fp2_mul (horner_eval_fp2 f x) (horner_eval_fp2 f x)) (horner_eval_fp2 f x).
Proof.
  intros. unfold poly_cube_fp2. rewrite horner_eval_fp2_mul, horner_eval_fp2_sqr.
  reflexivity.
Qed.

(* ================================================================== *)
(** * Fp2 list comparison via Z×Z projection                           *)
(* ================================================================== *)

Definition fp2_to_zp2_proj (a : Fp2) : Zp2 := (toZ (fst a), toZ (snd a)).
Definition fp2_list_to_zp2_proj (cs : list Fp2) : list Zp2 := map fp2_to_zp2_proj cs.

(** Convert a Z×Z element back to Fp2 via F.of_Z. *)
Definition zp2_to_fp2_inj (a : Zp2) : Fp2 := (ofZ (fst a), ofZ (snd a)).

(** Round-trip: F.of_Z (F.to_Z x) = x. *)
Lemma fp2_round_trip : forall a : Fp2,
  zp2_to_fp2_inj (fp2_to_zp2_proj a) = a.
Proof.
  intros [ar ai]. unfold zp2_to_fp2_inj, fp2_to_zp2_proj. simpl.
  f_equal; apply F.of_Z_to_Z.
Qed.

(** Map of round-trip on a list. *)
Lemma fp2_list_round_trip : forall cs : list Fp2,
  map zp2_to_fp2_inj (fp2_list_to_zp2_proj cs) = cs.
Proof.
  induction cs as [|c cs' IH]; simpl; [reflexivity|].
  rewrite fp2_round_trip, IH. reflexivity.
Qed.

(** Two Fp2 lists are equal iff their Z×Z projections are equal. *)
Lemma fp2_list_eq_via_zp2 : forall cs1 cs2 : list Fp2,
  fp2_list_to_zp2_proj cs1 = fp2_list_to_zp2_proj cs2 -> cs1 = cs2.
Proof.
  intros cs1 cs2 H.
  rewrite <- (fp2_list_round_trip cs1), <- (fp2_list_round_trip cs2).
  rewrite H. reflexivity.
Qed.
