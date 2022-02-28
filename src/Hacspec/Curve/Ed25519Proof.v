(* Proving equivalence between the Hacspec implementation of the Ed25519 curve operations
   and the fiat crypto specification. Addition is finished, but there is missing parts of 
   multiplication. *)

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
Notation fc_id := (@Basic.zero ed25519_field_element_t Logic.eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fc_field ed_dec
a d nonzero_a).

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

Notation "x ?=? y" := (ed_eq x y) (at level 90).
Notation "x ?+? y" := (point_add x y) (at level 60).
Notation "x #=# y" := (fc_eq x y) (at level 90).
Notation "x #+# y" := (fc_add x y) (at level 60).

Lemma ed_refl: forall x, x ?=? x.
Proof. intros [[[]]]. split; reflexivity.
Qed.

Lemma ed_symm: forall x y, x ?=? y -> y ?=? x.
Proof.
  intros [[[]]] [[[]]]. cbn. intros [-> ->]. auto.
Qed.

Lemma ed_field_refl: forall x: ed25519_field_element_t, x =.? x = true.
Proof. intros. unfold "=.?", nat_mod_eqdec. apply Z.eqb_refl. Qed.

(* Missing the case for zero, should be possible using fiat-crypto IntegralDomain *)
Lemma ed_trans: forall x y z, x ?=? y -> y ?=? z -> x ?=? z.
Proof.
  intros [[[]]] [[[]]] [[[]]]. cbn. intros [] []. split.
  - destruct (e5 =.? (nat_mod_zero : ed25519_field_element_t)) eqn:E.
    + rewrite eqb_leibniz in E. subst. admit.
    + apply (f_equal (fun x => e9 *% (nat_mod_inv e5) *% x)) in H. field_simplify in H. rewrite H.
   pose proof ed_field_theory as [[]]. rewrite (Rmul_comm e9). rewrite <- Rmul_assoc. rewrite H1. field. 
   intro. all: subst; rewrite ed_field_refl in E; discriminate.
  - destruct (e5 =.? (nat_mod_zero : ed25519_field_element_t)) eqn:E.
   + rewrite eqb_leibniz in E. subst. admit.
   + apply (f_equal (fun x => e9 *% (nat_mod_inv e5) *% x)) in H0. field_simplify in H0. rewrite H0.
  pose proof ed_field_theory as [[]]. rewrite (Rmul_comm e9). rewrite <- Rmul_assoc. rewrite H2. field. 
  intro. all: subst; rewrite ed_field_refl in E; discriminate.
Admitted. 

Add Relation ed_point_t ed_eq
  reflexivity proved by ed_refl
  symmetry proved by ed_symm
  transitivity proved by ed_trans
  as ed_eq_rel.
  
Lemma ed_add_comm: forall x y, onCurve x -> onCurve y -> x ?+? y ?=? y ?+? x.
  intros. rewrite (to_and_from _ H). rewrite (to_and_from _ H0). do 2 rewrite -> add_equiv.
  rewrite fc_eq_equiv. apply commutative.
Qed.

Lemma ed_add_assoc: forall x y z, onCurve x -> onCurve y -> onCurve z -> x ?+? (y ?+? z) ?=? (x ?+? y) ?+? z.
Proof. intros. rewrite (to_and_from _ H). rewrite (to_and_from _ H0). rewrite (to_and_from _ H1).
repeat rewrite add_equiv. rewrite fc_eq_equiv. apply associative.
Qed. 

Require Import Lia.

Require Import MachineIntegers.

Lemma max_unsigned32 : @max_unsigned WORDSIZE32 = 4294967295.
Proof. reflexivity. Qed.

Lemma modulus32 : @modulus WORDSIZE32 = 4294967296.
Proof. reflexivity. Qed.

Lemma foldi_helper: forall A n i f (acc : A), 0 <= i <= 256 -> foldi_ (S n) (repr i) f acc = foldi_ (n) (repr (i +1)) f (f (repr i) acc).
Proof. intros. assert (@add WORDSIZE32 (repr i) one = repr (i + 1)). {
    unfold add. rewrite unsigned_one. rewrite unsigned_repr. reflexivity.
    rewrite max_unsigned32. lia.
  } 
  cbn. rewrite H0. reflexivity.
Qed.

Notation scalarmod := (2^252 + 27742317777372353535851937790883648493).

Definition scalar_from_z (z : Z) : scalar_t := (mkznz _ _ (modz _ z)).
Definition scalar_from_pos (p : positive) : scalar_t := scalar_from_z (Zpos p).



Definition helperf (s: scalar_t) := (fun i_69 '(p_67, q_68) =>
let '(q_68) :=
  if nat_mod_bit (s) (i_69):bool then (let q_68 :=
      point_add (q_68) (p_67) in 
    (q_68)) else ((q_68)) in 
let p_67 :=
  point_add (p_67) (p_67) in 
(p_67, q_68)).

Notation point_double p := (point_add p p).

Fixpoint helpermul1 (n: nat) (z: Z) (acc: ed_point_t * ed_point_t) := 
  let (acc1, acc2) := acc in match n with
  | O => acc
  | S n' => match z with
    | 0 => helpermul1 n' 0 (point_double acc1, acc2)
    | Zneg _ => acc
    | Zpos b => match b with
      | xH => helpermul1 n' 0 (point_double acc1, point_add acc2 acc1)
      | xO b => helpermul1 n' (Zpos b) (point_double acc1, acc2)
      | xI b => helpermul1 n' (Zpos b) (point_double acc1, point_add acc2 acc1)
      end
  end
end.

(* Should be in Hacspec.Lib *)
Lemma foldi_one_more: forall (A: Type) (lo hi: Z) f (acc: A), foldi (repr lo) (repr (Z.succ hi)) f acc = f (repr hi) (foldi (repr lo) (repr hi) f acc).
Admitted.

Lemma helpermul1_help: forall n z acc1 acc2, 0 <= z -> helpermul1 (S n) z (acc1, acc2) = 
  let (acc1', acc2') := helpermul1 n z (acc1, acc2) in
  (point_double acc1', if Z.testbit z n then point_add acc2' acc1' else acc2').
Proof. induction n.
  - intros. cbn. destruct z; cbn.
    + reflexivity.
    + destruct p; reflexivity.
    + lia.
  - intros. destruct z. 
    + rewrite nat_N_Z, Nat2Z.inj_succ. cbn. assert (0 = 2 * 0) as -> by reflexivity. rewrite Z.testbit_even_succ.
    rewrite nat_N_Z in IHn. rewrite <- IHn. reflexivity. lia. lia.
    + destruct p.
      * rewrite nat_N_Z, Nat2Z.inj_succ. cbn. assert (Z.pos p~1 = 2 * (Z.pos p) + 1) as -> by reflexivity. rewrite Z.testbit_odd_succ.
      rewrite nat_N_Z in IHn. rewrite <- IHn. reflexivity. lia. lia.
      * rewrite nat_N_Z, Nat2Z.inj_succ. cbn. assert (Z.pos p~0 = 2 * (Z.pos p)) as -> by reflexivity. rewrite Z.testbit_even_succ.
      rewrite nat_N_Z in IHn. rewrite <- IHn. reflexivity. lia. lia.
      * rewrite nat_N_Z, Nat2Z.inj_succ. cbn. assert (1 = 2 * 0 + 1) as -> by reflexivity. rewrite Z.testbit_odd_succ.
        rewrite nat_N_Z in IHn. rewrite <- IHn. reflexivity. lia. lia.
    + lia.
Qed.

Lemma foldi_is_ok: forall (i: uint_size) (z: Z) acc, 0 <= z < scalarmod -> 
  foldi (repr 0) i (helperf (scalar_from_z z)) acc = helpermul1 (Z.to_nat (unsigned i)) z acc.
Proof. intro i. induction_uint_size i.
  - cbn. destruct acc. reflexivity.
  - unfold foldi. repeat rewrite unsigned_repr;try rewrite max_unsigned32; try lia. cbn. assert (Pos.to_nat 1 = 1%nat) as -> by reflexivity. cbn.
  destruct z. 
    + unfold helperf. cbn. destruct acc. reflexivity.
    + unfold helperf. cbn. rewrite Zmod_small; try lia. destruct p; cbn; destruct acc; reflexivity.
    + lia.
  - rewrite modulus32 in H. rewrite unsigned_repr in H0; try rewrite max_unsigned32; try lia. cbn in H0.
    rewrite foldi_one_more. rewrite H0; try lia.
    repeat rewrite unsigned_repr;try rewrite max_unsigned32; try lia. rewrite Z2Nat.inj_succ; try lia. destruct acc. rewrite helpermul1_help.
    unfold helperf, nat_mod_bit. 
    assert ((from_uint_size (repr (Z.pos b))) = Z.pos b). {
    unfold from_uint_size, Z_uint_sizable. apply unsigned_repr. rewrite max_unsigned32. lia. }
    rewrite H2. rewrite Z_nat_N, Z2N.id. 
    cbn. rewrite Zmod_small. reflexivity. lia. lia. lia.
Qed.

Fixpoint helpermul2 (pos: positive) (acc1 acc2 : fc_point) := match pos with
| xH => fc_add acc2 acc1
| xO b => helpermul2 b (fc_add acc1 acc1) acc2
| xI b => helpermul2 b (fc_add acc1 acc1) (fc_add acc2 acc1)
end.

(* Need equivalence between helpermul1 and helpermul2, Something like this *)
Lemma one_two_equiv: forall pos n acc1 acc2, Pos.size_nat pos <= n -> snd (helpermul1 n (Zpos pos) (coordinates acc1, coordinates acc2)) = coordinates (helpermul2 pos acc1 acc2).
Admitted.

Require Export Setoid.


Add Morphism helpermul2 : helpermul2_m.
Proof. induction y; intros.
  - simpl. rewrite IHy. reflexivity. rewrite H. reflexivity. rewrite H, H0. reflexivity.
  - simpl. rewrite IHy. reflexivity. rewrite H. reflexivity. apply H0.
  - simpl.  rewrite H, H0. reflexivity.
Qed.
  


Lemma helpermul2_helper2: forall pos acc1 acc2 acc3, helpermul2 pos acc1 (acc2 #+# acc3) #=# acc3 #+# (helpermul2 pos acc1 acc2).
Proof. induction pos; intros.  
- simpl. rewrite <- associative. rewrite (commutative acc3). rewrite associative. apply IHpos.
- simpl. apply IHpos.
-  simpl. rewrite associative. rewrite (commutative acc2). reflexivity.
Qed.

Notation fc_double x := (fc_add x x).
Lemma double_add: forall x y, fc_double (x #+# y) #=# fc_double x #+# fc_double y.
Proof. intros. rewrite associative. rewrite (commutative _ x). rewrite associative. symmetry. apply associative.
Qed.

Lemma helpermul2_helper: forall pos acc1, helpermul2 pos (fc_double acc1) fc_id #=# fc_double (helpermul2 pos acc1 fc_id).
Proof. induction pos; intros.
  - simpl. rewrite helpermul2_helper2. rewrite IHpos. rewrite helpermul2_helper2. symmetry. apply double_add.
  - simpl. apply IHpos.
  - simpl. do 2 rewrite left_identity. reflexivity.
Qed.

Fixpoint helpermul3 (pos : positive) (p : fc_point) : fc_point := match pos with
| xH => p
| xO pos' => fc_double (helpermul3 pos' p)
| xI pos' => (fc_double (helpermul3 pos' p)) #+# p
end.

Lemma two_three_equiv : forall pos p, helpermul2 pos p fc_id #=# helpermul3 pos p.
Proof. induction pos; intros.
- simpl. rewrite helpermul2_helper2. rewrite helpermul2_helper. rewrite IHpos. apply commutative.
- simpl. rewrite helpermul2_helper. rewrite IHpos. reflexivity.
- simpl. apply left_identity.
Qed.

(* Need equivalence between helpermul3 and fiat crypto mul *)

