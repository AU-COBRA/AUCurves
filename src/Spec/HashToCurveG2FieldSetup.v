(** * Fp2 field infrastructure for G2 hash-to-curve proofs.

    Constructs an [Algebra.Hierarchy.field] instance for Fp2 = Fp × Fp
    with u² = -1, enabling [Field.fsatz] for algebraic proofs over Fp2.
    Also provides decidable equality and [fp2_eqb] reflection lemmas.

    Self-contained: avoids importing HashToCurveSWUProof to keep
    memory usage low (SWUCompute.vo is ~2GB). *)

From Stdlib Require Import ZArith Lia RelationClasses.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Algebra.Hierarchy.
Require Import Spec.HashToCurve.
Require Import Spec.HashToCurveG2.
Require Import Spec.HashToCurveFieldSetup.
Require Import Crypto.Util.Decidable.

Local Open Scope F_scope.

(** Fp field instance (local, needed by Field.fsatz and ring). *)
#[local] Instance Fp_field : @Algebra.Hierarchy.field Fp Logic.eq 0f 1f
  F.opp F.add F.sub F.mul F.inv F.div
  := @F.field_modulo p_pos p_pos_prime.
#[local] Instance Fp_eq_dec : Decidable.DecidableRel (@Logic.eq Fp) := F.eq_dec.

(* ================================================================== *)
(** * Lightweight Fp lemmas (avoid importing SWUProof)                  *)
(* ================================================================== *)

Local Lemma fp_eqb_true_iff : forall (a b : Fp),
  fp_eqb a b = true <-> a = b.
Proof. intros a b. unfold fp_eqb. rewrite Z.eqb_eq. split; apply F.eq_to_Z_iff. Qed.

Local Lemma fp_eqb_false_iff : forall (a b : Fp),
  fp_eqb a b = false <-> a <> b.
Proof.
  intros a b. unfold fp_eqb. rewrite Z.eqb_neq. split.
  - intros H Habs. apply H. apply F.eq_to_Z_iff in Habs. exact Habs.
  - intros H Habs. apply H. apply F.eq_to_Z_iff. exact Habs.
Qed.

Local Lemma mul_nz : forall (a b : Fp), a <> 0f -> b <> 0f -> a *f b <> 0f.
Proof.
  intros a b Ha Hb Hab. apply Ha.
  replace a with (a *f b *f F.inv b).
  - rewrite Hab. ring.
  - replace (a *f b *f F.inv b) with (a *f (b *f F.inv b)) by ring.
    rewrite (Fp_mul_inv_r b Hb). ring.
Qed.

Local Lemma fermat_local : forall (x : Fp),
  x <> 0f -> F.pow x (Z.to_N (Z.pos p_pos - 1)) = 1f.
Proof.
  intros x Hx.
  assert (Hinv := Fp_inv_nonzero x Hx).
  assert (Hfermat := @F.Fq_inv_fermat p_pos p_pos_prime p_pos_gt_2 x).
  rewrite Hfermat in Hinv.
  replace (F.pow x (Z.to_N (Z.pos p_pos - 2)) *f x)
    with (F.pow x (Z.to_N (Z.pos p_pos - 2)) *f F.pow x 1) in Hinv
    by (rewrite F.pow_1_r; reflexivity).
  rewrite <- F.pow_add_r in Hinv.
  replace (Z.to_N (Z.pos p_pos - 2) + 1)%N with (Z.to_N (Z.pos p_pos - 1)) in Hinv
    by (vm_compute; reflexivity).
  exact Hinv.
Qed.

(* ================================================================== *)
(** * Fp2 norm is nonzero for nonzero elements                         *)
(* ================================================================== *)

Lemma fp2_norm_nonzero : forall (a : Fp2),
  a <> fp2_zero -> fp2_norm a <> 0f.
Proof.
  intros [a0 a1] Hne. unfold fp2_norm. simpl.
  intro Hnorm.
  destruct (F.eq_dec a1 (@F.zero p_pos)) as [Ha1z | Ha1nz].
  - subst a1.
    assert (Ha0sq : a0 *f a0 = 0f)
      by (replace (a0 *f a0 +f 0f *f 0f) with (a0 *f a0) in Hnorm by ring; exact Hnorm).
    assert (Ha0z : a0 = 0f).
    { destruct (F.eq_dec a0 (@F.zero p_pos)) as [|Ha0nz]; [assumption|].
      exfalso. exact (mul_nz a0 a0 Ha0nz Ha0nz Ha0sq). }
    apply Hne. subst. reflexivity.
  - exfalso.
    assert (H1 : a0 *f a0 = F.opp (a1 *f a1))
      by (replace (a0 *f a0) with (a0 *f a0 +f a1 *f a1 +f F.opp (a1 *f a1)) by ring;
          rewrite Hnorm; ring).
    assert (Hinv : F.inv a1 *f a1 = 1f)
      by (apply Hierarchy.left_multiplicative_inverse; exact Ha1nz).
    set (r := a0 *f F.inv a1).
    assert (Hr_sq : r *f r = F.opp 1f).
    { subst r.
      replace (a0 *f F.inv a1 *f (a0 *f F.inv a1))
        with (a0 *f a0 *f (F.inv a1 *f F.inv a1)) by ring.
      rewrite H1.
      replace (F.opp (a1 *f a1) *f (F.inv a1 *f F.inv a1))
        with (F.opp ((F.inv a1 *f a1) *f (F.inv a1 *f a1))) by ring.
      rewrite Hinv. ring. }
    assert (Hr_nz : r <> 0f).
    { intro Hr0. assert (F.opp 1f = 0f) by (rewrite <- Hr_sq, Hr0; ring).
      assert (F.to_Z (F.opp 1f) = F.to_Z 0f) by (f_equal; assumption).
      revert H0. vm_compute. discriminate. }
    (* (-1)^((p-1)/2) = (r²)^((p-1)/2) = r^(p-1) = 1 *)
    (* But is_square(-1) = false means (-1)^legendre = p-1 ≠ 1 *)
    assert (Hm1_euler : F.pow (F.opp 1f) (Z.to_N legendre_exp) = 1f).
    { rewrite <- Hr_sq.
      rewrite F.pow_mul_l.
      replace (F.pow r (Z.to_N legendre_exp) *f F.pow r (Z.to_N legendre_exp))
        with (F.pow r (Z.to_N legendre_exp + Z.to_N legendre_exp))
        by (rewrite F.pow_add_r; reflexivity).
      replace (Z.to_N legendre_exp + Z.to_N legendre_exp)%N
        with (Z.to_N (Z.pos p_pos - 1))
        by (vm_compute; reflexivity).
      exact (fermat_local r Hr_nz). }
    (* But is_square(-1) = false *)
    assert (Hbad : is_square (F.opp 1f) = true).
    { unfold is_square. rewrite (proj2 (fp_eqb_true_iff _ _) Hm1_euler).
      reflexivity. }
    rewrite minus_one_nonsquare in Hbad. discriminate.
Qed.

(* ================================================================== *)
(** * Fp2 field instance (built level-by-level for memory efficiency)   *)
(* ================================================================== *)

(** Make Fp operations opaque so [simpl] only unfolds Fp2 structure. *)
Local Opaque F.add F.mul F.sub F.opp F.inv.

Local Ltac fp2_eq :=
  intros;
  repeat match goal with [a : Fp2 |- _] => destruct a end;
  apply injective_projections; simpl; ring.

#[local] Instance Fp2_add_monoid :
  @Hierarchy.monoid Fp2 (@eq Fp2) fp2_add fp2_zero.
Proof.
  constructor;
    [constructor; fp2_eq | constructor; fp2_eq | constructor; fp2_eq
    | repeat intro; subst; reflexivity | exact (@eq_equivalence Fp2)].
Qed.

#[local] Instance Fp2_add_group :
  @Hierarchy.group Fp2 (@eq Fp2) fp2_add fp2_zero fp2_neg.
Proof.
  constructor;
    [exact Fp2_add_monoid | constructor; fp2_eq | constructor; fp2_eq
    | repeat intro; subst; reflexivity].
Qed.

#[local] Instance Fp2_add_comm_group :
  @Hierarchy.commutative_group Fp2 (@eq Fp2) fp2_add fp2_zero fp2_neg.
Proof. constructor; [exact Fp2_add_group | constructor; fp2_eq]. Qed.

#[local] Instance Fp2_mul_monoid :
  @Hierarchy.monoid Fp2 (@eq Fp2) fp2_mul fp2_one.
Proof.
  constructor;
    [constructor; fp2_eq | constructor; fp2_eq | constructor; fp2_eq
    | repeat intro; subst; reflexivity | exact (@eq_equivalence Fp2)].
Qed.

#[local] Instance Fp2_ring :
  @Hierarchy.ring Fp2 (@eq Fp2) fp2_zero fp2_one fp2_neg
    fp2_add fp2_sub fp2_mul.
Proof.
  constructor;
    [exact Fp2_add_comm_group | exact Fp2_mul_monoid
    | constructor; fp2_eq | constructor; fp2_eq
    | fp2_eq
    | repeat intro; subst; reflexivity
    | repeat intro; subst; reflexivity].
Qed.

#[local] Instance Fp2_comm_ring :
  @Hierarchy.commutative_ring Fp2 (@eq Fp2) fp2_zero fp2_one fp2_neg
    fp2_add fp2_sub fp2_mul.
Proof. constructor; [exact Fp2_ring | constructor; fp2_eq]. Qed.

#[export] Instance Fp2_field : @Hierarchy.field Fp2 (@eq Fp2)
  fp2_zero fp2_one fp2_neg fp2_add fp2_sub fp2_mul fp2_inv fp2_div.
Proof.
  split.
  - exact Fp2_comm_ring.
  - split. intros [a0 a1] Hne.
    assert (Hnz : fp2_norm (a0, a1) <> 0f)
      by (apply fp2_norm_nonzero; exact Hne).
    unfold fp2_norm in Hnz. simpl in Hnz.
    apply injective_projections; simpl; field; exact Hnz.
  - split. intro H.
    assert (H0 : @F.zero p_pos = @F.one p_pos)
      by (exact (f_equal (@fst Fp Fp) H)).
    apply (f_equal F.to_Z) in H0. revert H0. vm_compute. discriminate.
  - intros [a0 a1] [b0 b1]. reflexivity.
  - repeat intro; subst; reflexivity.
  - repeat intro; subst; reflexivity.
Qed.

(* ================================================================== *)
(** * Decidable equality for Fp2                                        *)
(* ================================================================== *)

#[export] Instance Fp2_eq_dec : Decidable.DecidableRel (@Logic.eq Fp2).
Proof.
  intros [a0 a1] [b0 b1].
  destruct (F.eq_dec a0 b0) as [H0|H0], (F.eq_dec a1 b1) as [H1|H1].
  - left. f_equal; assumption.
  - right. intro H. apply H1. change (snd (a0, a1) = snd (b0, b1)). f_equal. exact H.
  - right. intro H. apply H0. change (fst (a0, a1) = fst (b0, b1)). f_equal. exact H.
  - right. intro H. apply H0. change (fst (a0, a1) = fst (b0, b1)). f_equal. exact H.
Defined.

(* ================================================================== *)
(** * fp2_eqb reflection lemmas                                         *)
(* ================================================================== *)

Lemma fp2_eqb_true_iff : forall (a b : Fp2),
  fp2_eqb a b = true <-> a = b.
Proof.
  intros [a0 a1] [b0 b1]. unfold fp2_eqb. simpl.
  rewrite Bool.andb_true_iff, !fp_eqb_true_iff.
  split.
  - intros [H0 H1]. f_equal; assumption.
  - intros H. split; [change (fst (a0,a1) = fst (b0,b1)) | change (snd (a0,a1) = snd (b0,b1))]; f_equal; exact H.
Qed.

Lemma fp2_eqb_false_iff : forall (a b : Fp2),
  fp2_eqb a b = false <-> a <> b.
Proof.
  intros a b. rewrite <- Bool.not_true_iff_false, fp2_eqb_true_iff.
  reflexivity.
Qed.

(* Restore transparency for ring/field tactics and char_ge. *)
Local Transparent F.add F.mul F.sub F.opp F.inv.

(** Characteristic ≥ 3 for Fp2 (p is 381-bit prime, so char > 3). *)
#[export] Instance Fp2_char_ge_3 :
  @Ring.char_ge Fp2 (@eq Fp2) fp2_zero fp2_one fp2_neg fp2_add fp2_sub fp2_mul 3.
Proof.
  unfold Ring.char_ge, Hierarchy.char_ge.
  intros p Hp Heq.
  assert (Hfst : fst (Ring.of_Z (BinInt.Z.pos p)) = @F.zero p_pos)
    by (rewrite Heq; reflexivity).
  destruct p; [destruct p|destruct p|];
    try (exfalso; revert Hp; vm_compute; discriminate).
  (* p = 2: fst(of_Z 2) = F.one + F.one ≠ 0 *)
  all: simpl @Ring.of_Z in Hfst; unfold fp2_add, fp2_one in Hfst;
       simpl fst in Hfst;
       apply (f_equal F.to_Z) in Hfst;
       rewrite ?F.to_Z_add in Hfst;
       revert Hfst; native_compute; discriminate.
Qed.

Require Crypto.Algebra.Ring.

Add Ring Fp2_ring : (@Ring.ring_theory_for_stdlib_tactic
  Fp2 (@eq Fp2) fp2_zero fp2_one fp2_neg fp2_add fp2_sub fp2_mul
  (Hierarchy.field_commutative_ring(field:=Fp2_field))).

Add Field Fp2_field_tac :
  (@Field.field_theory_for_stdlib_tactic
    Fp2 (@eq Fp2) fp2_zero fp2_one fp2_neg fp2_add fp2_mul fp2_sub fp2_inv fp2_div
    Fp2_field).
