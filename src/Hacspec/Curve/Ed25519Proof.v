Require Import Hacspec.Util.Lib.
Require Import Hacspec.Util.MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

Require Import Hacspec.Curve.Ed25519.

From Coqprime Require Import GZnZ.
Require Import Field.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Curves.Edwards.XYZT.Basic.
Require Import Crypto.Algebra.Hierarchy.

Notation ed_field := (nat_mod 57896044618658097711785492504343953926634992332820282019728792003956564819949).

Lemma ed_field_theory: @field_theory ed25519_field_element_t nat_mod_zero nat_mod_one nat_mod_add nat_mod_mul nat_mod_sub nat_mod_neg nat_mod_div nat_mod_inv Logic.eq.
Proof. apply FZpZ. apply prime_p. Qed.

Lemma ed_field_theory': @field_theory ed_field nat_mod_zero nat_mod_one nat_mod_add nat_mod_mul nat_mod_sub nat_mod_neg nat_mod_div nat_mod_inv Logic.eq.
Proof. apply FZpZ. apply prime_p. Qed.

Add Field ed_field: ed_field_theory.
Add Field ed_field': ed_field_theory'.

Lemma test: forall x: ed25519_field_element_t, x -% x = nat_mod_zero.
Proof. intros. field. Qed.

Global Instance fc_field: @field ed25519_field_element_t (@Logic.eq ed_field) nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div.
Proof.
    repeat split; try apply (Fdiv_def ed_field_theory); try (intros; field); try apply (_ (ed_field_theory)); auto.
     symmetry; apply (F_1_neq_0 (ed_field_theory)).
Qed.


Lemma pos_le_three: forall pos: positive, (pos < 3)%positive -> pos = 1%positive \/ pos = 2%positive.
Proof. intros [] H; auto; inversion H.
- unfold Pos.compare, Pos.compare_cont in H1. destruct p; inversion H1.
- assert (p = 1%positive). unfold Pos.compare, Pos.compare_cont in H1. destruct p; inversion H1. auto. 
  rewrite H0. auto.
Qed.

Lemma ed_char_ge:  @Ring.char_ge ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul (BinNat.N.succ_pos BinNat.N.two).
Proof. 
  unfold char_ge, Hierarchy.char_ge. intros pos. cbn. intros H. apply pos_le_three in H. destruct H;
  rewrite H; simpl; intro c; discriminate c.
Qed.


Lemma ed_dec: DecidableRel (@Logic.eq ed25519_field_element_t).
Proof. unfold Decidable. intros x y. destruct (x =.? y) eqn:E.
  - left. apply eqb_leibniz. apply E. 
  - right. intro. rewrite H in E. unfold "=.?", nat_mod_eqdec in E. rewrite Z.eqb_refl in E. discriminate.
Qed.

Notation a := (nat_mod_neg nat_mod_one : ed25519_field_element_t).
Notation d := (mkznz _ _ (modz _ 37095705934669439343138083508754565189542113879843219016388785533085940283555) : ed25519_field_element_t).

Notation twice_d := (d +% d).

Lemma nonzero_a : a <> nat_mod_zero.
Proof. intro. inversion H. 
Qed.

Require Import Lia.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

Lemma square_a : exists sqrt_a : ed25519_field_element_t, sqrt_a *% sqrt_a = a.
Proof.
  exists (mkznz _ _ (modz _ 19681161376707505956807079304988542015446066515923890162744021073123829784752)).
  unfold "*%", mul, nat_mod_neg, GZnZ.opp, nat_mod_one, one, val. apply zirr.
  pull_Zmod. reflexivity.
Qed.

Lemma nonsquare_d : forall x : ed25519_field_element_t, x *% x <> d.
Proof. intros x H.  Admitted. 

Notation fc_point := (@point ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_add nat_mod_mul a d).
Notation fc_add := (@m1add ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fc_field ed_char_ge ed_dec
a d nonzero_a square_a nonsquare_d eq_refl twice_d eq_refl).

Notation fc_eq := (@eq ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_add nat_mod_mul a d).

Lemma same_d: nat_mod_from_byte_seq_le (constant_d_v) = d.
Proof. 
Admitted.

Lemma two_equiv: (nat_mod_two: ed25519_field_element_t) = nat_mod_one +% nat_mod_one.
Proof. reflexivity. Qed.

Definition ed_eq (p q : ed_point_t): Prop := 
  let '(x1, y1, z1, _) := p in
  let '(x2, y2, z2, _) := q in
  z2 *% x1 = z1 *% x2 /\ z2 *% y1 = z1 *% y2.

Lemma add_equiv: forall p q: fc_point, (point_add (coordinates p) (coordinates q)) = (coordinates (fc_add p q)).
Proof. intros [[[[]]]] [[[[]]]]. unfold m1add, coordinates, proj1_sig, point_add, ed_eq. rewrite same_d, two_equiv.
  repeat (apply pair_equal_spec; split); field_simplify; reflexivity.
Qed.

Notation "x ^%2" := (x *% x) (at level 20).

Definition onCurve (p: ed_point_t) : Prop :=
  let '(x, y, z, t) := p in
  a *% x^%2 *% z^%2 +% y^%2 *% z^%2 = (z^%2)^%2 +% d *% x^%2 *% y^%2
  /\ x *% y = z *% t
  /\ z <> nat_mod_zero.

Program Definition to_fc_point (p: ed_point_t) (onc : onCurve p): fc_point :=
  p.
  
Lemma to_and_from: forall (p : ed_point_t) (oncp :onCurve p),
  p = coordinates (to_fc_point p oncp).
Proof.
  intros. reflexivity.
Qed.

Lemma on_curve_fc: forall (p : fc_point), onCurve (coordinates p).
Proof.
  intros [[[[]]]]. apply y.
Qed.

Lemma add_preserves_curve: forall p q (oncp: onCurve p) (oncq: onCurve q), 
  onCurve (point_add p q).
Proof.
  intros. rewrite (to_and_from p oncp). rewrite (to_and_from q oncq). rewrite add_equiv.
  apply on_curve_fc.
Qed.

Lemma add_equiv': forall (p q : ed_point_t) (oncp : onCurve p) (oncq : onCurve q),
  eq (fc_add (to_fc_point p oncp) (to_fc_point q oncq)) (to_fc_point (point_add p q) (add_preserves_curve _ _ oncp oncq)).
Proof.
  intros [[[]]] [[[]]] oncp oncq. unfold m1add, to_fc_point, point_add, eq, coordinates, proj1_sig. rewrite same_d, two_equiv.
  split; field_simplify; reflexivity.
Qed.

Require Import Crypto.Spec.CompleteEdwardsCurve.

Notation spec_point := (@E.point ed25519_field_element_t Logic.eq nat_mod_one nat_mod_add nat_mod_mul a d).
Notation spec_add := (@E.add ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fc_field ed_char_ge ed_dec
a d nonzero_a square_a nonsquare_d).

Notation fc_from_spec := (@from_twisted ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fc_field ed_dec
  a d nonzero_a).
Notation fc_to_spec := (@to_twisted ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fc_field ed_dec
  a d nonzero_a).


Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Monoid.

Lemma fc_eq_equiv: forall (p q: fc_point), ed_eq (coordinates p) (coordinates q) <-> fc_eq p q.
Proof.
  intros [[[[]]]] [[[[]]]].
  unfold eq, coordinates, proj1_sig, ed_eq. reflexivity.
Qed.

Local Instance iso_group : Group.isomorphic_commutative_groups 
:= (@isomorphic_commutative_group_m1 ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fc_field ed_char_ge ed_dec
a d nonzero_a square_a nonsquare_d eq_refl twice_d eq_refl).

Local Instance fc_eq_class : RelationClasses.Equivalence eq := (@Equivalence_eq ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fc_field ed_dec
a d nonzero_a).

Lemma add_spec_equiv: forall (p q : spec_point), ed_eq (point_add (coordinates (fc_from_spec p)) (coordinates (fc_from_spec q))) (coordinates (fc_from_spec (spec_add p q))).
Proof.
   intros. rewrite add_equiv, fc_eq_equiv. symmetry. apply homomorphism.
Qed.

Lemma spec_refl: forall (x: spec_point), E.eq x x.
Proof.
  intros [[]]. split; reflexivity.
Qed.

Lemma spec_symm: forall (x y : spec_point), E.eq x y -> E.eq y x.
Proof.
  intros [[]] [[]]. cbn. intros [-> ->]. auto.
Qed.

Lemma spec_trans: forall (x y z : spec_point), E.eq x y -> E.eq y z -> E.eq x z.
Proof.
  intros [[]] [[]] [[]]. cbn. intros [-> ->] [-> ->]. auto.
Qed. 

Add Relation spec_point E.eq
  reflexivity proved by spec_refl
  symmetry proved by spec_symm
  transitivity proved by spec_trans
  as spec_eq_rel.  

Lemma add_spec_equiv': forall (p q : ed_point_t) (oncp : onCurve p) (oncq : onCurve q),
  E.eq (spec_add (fc_to_spec (to_fc_point p oncp)) (fc_to_spec (to_fc_point q oncq))) (fc_to_spec (to_fc_point (point_add p q) (add_preserves_curve _ _ oncp oncq))).
Proof.
  intros. rewrite <- add_equiv'. rewrite homomorphism. reflexivity.
Qed.
  