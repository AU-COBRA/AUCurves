(* ########### PROOF SECTION ########### 
This file contains proofs that the hacspec specification of the bls12-381 curve group operations (addition and 
scalar multiplication) is equivalent to the fiat-crypto specifiaction of curve addition and scalar multiplication.
This is done for both of the curves E(Fp): y²=x³+4 and E'(Fp²): y²=x²+4(u+1), with Fp² defined as Fp(u)/(u²+1).
*)

Require Import Hacspec.Util.Lib. 
Require Import Hacspec.Util.MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec.Curve.Bls.

Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Algebra.Field Crypto.Algebra.Hierarchy.
Require Import Crypto.Util.Decidable Crypto.Util.Tactics.DestructHead Crypto.Util.Tactics.BreakMatch.
Require Import blsprime.
Require Import Ring.
Require Export Ring_theory.
Require Import Setoid.
Require Import Field.

Require Import Init.Logic.

Local Notation fp' := (nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab).

(* Equality between fp elements *)
Lemma fp_eq_ok: forall x y : fp, (x = y) <-> @eq fp' x y.
Proof. reflexivity.
Qed.

Local Notation prime := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787.

Local Notation nat_mod_two := (nat_mod_one +% nat_mod_one).

Lemma two_equiv : @Lib.nat_mod_two prime = nat_mod_two.
Proof. reflexivity. Qed.

Local Notation nat_mod_three := (nat_mod_two +% nat_mod_one).

Lemma three_equiv : nat_mod_from_literal 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab (repr 3) = nat_mod_three.
Proof. unfold nat_mod_from_literal, nat_mod_from_secret_literal. 
 apply GZnZ.zirr. reflexivity. 
Qed.
Local Notation nat_mod_four := (nat_mod_three +% nat_mod_one).

Local Notation neg_one := (nat_mod_neg nat_mod_one).

(* Checking if a point is actually on the curve - since FC points are only defined as points on the curve, and our points are everyting from (fp, fp), this is needed *)
Definition g1_on_curve (p:g1) := let '(x, y, inf) := p in if inf then True else y*%y=x*%x*%x +% nat_mod_four.

(* Checking equivalence between two points in G1. First check is if they're pointAtInfinity, and if not, then check coordinates *)
Definition g1_eq (x y: g1) := 
  let '(x1, x2, xinf) := x in
  let '(y1, y2, yinf) := y in
  if xinf then yinf = true else
    yinf = false /\ x1 = y1 /\ x2 = y2.

Local Infix "?+?" := g1add (at level 61).
Local Infix "?=?" := g1_eq (at level 70).
 
Lemma g1_eq_refl: forall x, x ?=? x.
Proof. intros [[]]. destruct b; easy.
Qed.

Lemma g1_eq_symm: forall x y, x ?=? y -> y ?=? x.
Proof.
    intros [[] []] [[] []]; unfold "?=?"; easy.
Qed. 

Lemma g1_eq_tran: forall x y z, x ?=? y -> y ?=? z -> x ?=? z.
Proof.
    intros [[] []] [[] []] [[] []]; unfold "?=?"; try easy.
    intros [_ [-> ->]] [_ [-> ->]]. easy.
Qed.

Add Relation (g1) (g1_eq) 
    reflexivity proved by g1_eq_refl
    symmetry proved by g1_eq_symm
    transitivity proved by g1_eq_tran 
    as g1_eq_rel.


Lemma fp_same_if_eq: forall x y: fp', x =.? y = true <-> x = y.
Proof. intros x y. split.
  - apply eqb_leibniz. 
  - intros ->. apply Z.eqb_refl.
Qed.

Lemma fp_eq_true: forall x: fp, x =.? x = true.
Proof. intros x. apply Z.eqb_refl. 
Qed.

(* Every element is equal itself *)
Lemma g1_eqb_true: forall p: g1, p =.? p = true.
Proof. intros [[]]. unfold "=.?", Dec_eq_prod. apply Bool.andb_true_iff; split. 
  - apply Bool.andb_true_iff; split; apply fp_same_if_eq; reflexivity. 
  - apply Bool.eqb_reflx.
Qed.

Lemma fp_field_theory: @field_theory fp' nat_mod_zero nat_mod_one nat_mod_add nat_mod_mul nat_mod_sub nat_mod_neg nat_mod_div nat_mod_inv (@eq fp').
Proof. apply (GZnZ.FZpZ prime blsprime).  Qed.

Add Field fp_field: fp_field_theory.

Lemma fp_field_theory2: @field_theory fp nat_mod_zero nat_mod_one nat_mod_add nat_mod_mul nat_mod_sub nat_mod_neg nat_mod_div nat_mod_inv (@eq fp).
Proof. apply (GZnZ.FZpZ prime blsprime).  Qed.

Add Field fp_field2 : fp_field_theory2.


(* Fiat-crypto field from standard library field *)
Instance fp_fc_field : @field fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div.
Proof.
  repeat split; try apply fp_field_theory; try apply (Fdiv_def fp_field_theory); try (intros ; field); try apply (_ (fp_field_theory)); auto.
  - symmetry; apply (F_1_neq_0 (fp_field_theory)).
Qed.

Lemma g1_dec: DecidableRel (@eq fp').
Proof. unfold Decidable. intros x y. pose proof (fp_same_if_eq x y). destruct (x =.? y) eqn:E.
  - left. apply H. reflexivity. 
  - right. apply not_iff_compat in H. apply H. congruence.
Qed.

Lemma pos_le_three: forall pos: positive, (pos < 3)%positive -> pos = 1%positive \/ pos = 2%positive.
Proof. intros [] H; auto; inversion H.
- unfold Pos.compare, Pos.compare_cont in H1. destruct p; inversion H1.
- assert (p = 1%positive). unfold Pos.compare, Pos.compare_cont in H1. destruct p; inversion H1. auto. 
  rewrite H0. auto.
Qed.

Lemma fp_char_ge:  @Ring.char_ge fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul (BinNat.N.succ_pos BinNat.N.two).
Proof. 
  unfold char_ge. unfold Hierarchy.char_ge. intros pos. cbn. intros H. apply pos_le_three in H. destruct H;
  rewrite H; simpl; intro c; discriminate c.
Qed.

(* Representation af a Fiat-crypto G1 point *)
Local Notation g1_fc_point := (@W.point fp' eq nat_mod_add nat_mod_mul nat_mod_zero nat_mod_four). 
(* Fiat-Crypto Equivalence, Addition and Zero element *)
Local Notation g1_fc_eq := (@W.eq fp' eq nat_mod_add nat_mod_mul nat_mod_zero nat_mod_four).       
Notation g1_fc_add := (@W.add fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fp_fc_field g1_dec fp_char_ge nat_mod_zero nat_mod_four).
Local Notation g1_fc_zero := (@W.zero fp' eq nat_mod_add nat_mod_mul nat_mod_zero nat_mod_four).

(* ?x? is x performed by hacspec. #x# is x performed by Fiat-Crypto *)
Local Infix "#+#" := g1_fc_add (at level 61).
Local Infix "#=#" := g1_fc_eq (at level 70).

(* Checking the Fiat-Crypto functions actually work*)
Example add_zero_is_zero_in_fc: (g1_fc_zero #+# g1_fc_zero) #=# g1_fc_zero.
Proof. reflexivity.
Qed.

(* Translating Fiat-Crypto Point Representations to our G1 points (x, y, isPointAtInfinity) *)
Definition g1_from_fc (p: g1_fc_point): g1 := 
  match W.coordinates p with
  | inr tt => (nat_mod_zero, nat_mod_zero, true)
  | inl (pair x y) => (x, y, false)
  end.


(* Translating our points to Fiat-Crypto Points *)
Program Definition g1_to_fc (p: g1) (on_curve: g1_on_curve p): g1_fc_point :=
    match p return fp*fp+unit with
    | (_, _, true) => inr tt
    | (x, y, false) => inl (x, y)
    end.
    Opaque "=.?".
    Next Obligation.
    Crypto.Util.Tactics.BreakMatch.break_match; auto. unfold g1_on_curve in on_curve. rewrite on_curve. field. 
    Qed.


Lemma algebra_helper_1: forall x y z:fp', x -% y = z <-> x = y +% z.
Proof. intros x y z. split; intros H; [rewrite <- H | rewrite H]; field.
Qed.

Lemma sub_eq_zero_means_same: forall x y: fp', x -% y = nat_mod_zero <-> x = y.
Proof. split; intros H. 
  - apply algebra_helper_1 in H. rewrite H. field.
  - rewrite H. field. 
Qed.

(* Integral domain to help with som algebraic properties *)
Local Notation fp_integral_domain := (@Field.integral_domain fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_mul nat_mod_sub nat_mod_inv nat_mod_div fp_fc_field g1_dec).

Local Notation nonzero_iff := (@IntegralDomain.IntegralDomain.nonzero_product_iff_nonzero_factors fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul fp_integral_domain).

Lemma negation_eq_implies_zero: forall x: fp', x = (nat_mod_neg x) -> x = nat_mod_zero.
Proof. intros x H. generalize fp_field_theory. intros [[]].
rewrite <- (Radd_0_l (nat_mod_neg x)) in H. rewrite Radd_comm in H.
rewrite <- algebra_helper_1 in H.
assert (nat_mod_two *% x = nat_mod_zero). { rewrite <- H. field. }
apply (f_equal (fun x => x *% (nat_mod_inv nat_mod_two))) in H0.
field_simplify in H0; easy.
Qed.

Lemma square_law: forall x y: fp', (x *% x) -% (y *% y) = (x +% y) *% (x -% y).
Proof. intros x y. field. 
Qed.

Lemma zero_iff : forall x y : fp', x *% y = nat_mod_zero <-> x = nat_mod_zero \/ y = nat_mod_zero.
Proof. intros. split. 
  - apply Decidable.contrapositive. apply Logic.Decidable.dec_or.
    + destruct (g1_dec x nat_mod_zero) as [e|e]; [left|right]; apply e.
    + destruct (g1_dec y nat_mod_zero) as [e|e]; [left|right]; apply e.
    + intros H. setoid_rewrite Decidable.not_or_iff in H. apply nonzero_iff. apply H.
  - intros [-> | ->]; field.
Qed.

Lemma symmetrical_x_axis: forall x1 y1 x2 y2 : fp', g1_on_curve (x1, y1, false) -> g1_on_curve (x2, y2, false) -> x1 = x2 -> y1 = y2 \/ y1 = nat_mod_neg y2.
Proof. intros x1 y1 x2 y2 H1 H2 H3. 
  unfold g1_on_curve in H1. unfold g1_on_curve in H2. rewrite <- H3 in H2. rewrite <- H2 in H1. apply sub_eq_zero_means_same in H1. rewrite square_law in H1.
  apply zero_iff in H1.
  destruct H1.
  - right. apply sub_eq_zero_means_same. rewrite <- H. field.
  - left. apply sub_eq_zero_means_same, H.
Qed.

Lemma exp2ismul: forall (x:fp), nat_mod_exp x (2) = x *% x.
Proof. intros. unfold nat_mod_exp. assert ((Z.to_nat (from_uint_size 2)) = 2%nat) as -> by reflexivity. field.
Qed.

(* The equivalence proof. If two points are on the curve, adding them together using hacspec is the same as converting to fiat-crypto, adding them and converting back *)
Theorem g1_addition_equal: forall (p q: g1) on_curve_p on_curve_q, (p ?+? q) ?=? (g1_from_fc ((g1_to_fc p on_curve_p) #+# (g1_to_fc q on_curve_q))). 
Proof. intros [[]] [[]] H H0. unfold g1add, g1_from_fc, g1_to_fc, g1_fc_add, g1_eq. cbn. 
  (generalize fp_field_theory). intros [[]].
  destruct b eqn:E, b0 eqn:E1; auto. 
  unfold dec. destruct (g1_dec f f1) as [e|e]. 
  2:{ destruct ((f, f0, false) =.? (f1, f2, false)) eqn:N; [ apply eqb_leibniz in N; inversion N; contradiction |]. 
    destruct (f =.? f1)eqn:N1; [apply eqb_leibniz in N1; contradiction|]. cbn. rewrite exp2ismul. 
    split; split; auto; field. }
  destruct (g1_dec f2 (nat_mod_neg f0)) as [e0 |e0]; subst; cbn; destruct (f0 =.? nat_mod_zero) eqn:k.
  - apply eqb_leibniz in k as ->. field_simplify (@nat_mod_neg prime nat_mod_zero).
    rewrite g1_eqb_true. cbn. auto.
  - destruct ((f1, f0, false) =.? (f1, nat_mod_neg f0, false)) eqn: eqb; 
    [apply eqb_leibniz in eqb; inversion eqb; apply negation_eq_implies_zero in H2; subst; rewrite fp_eq_true in k; discriminate|]. 
    field_simplify (nat_mod_zero -% nat_mod_neg f0). repeat rewrite fp_eq_true. cbn. reflexivity.
  - apply eqb_leibniz in k. subst. pose proof (symmetrical_x_axis _ _ _ _ H0 H eq_refl).
    destruct H1; [ field_simplify (@nat_mod_neg prime nat_mod_zero) in e0; contradiction | contradiction].
  - pose proof (symmetrical_x_axis _ _ _ _ H0 H eq_refl). destruct H1; [| contradiction].
    subst. rewrite g1_eqb_true. cbn. repeat rewrite exp2ismul. rewrite three_equiv, two_equiv.
    split; split; auto; rewrite fp_eq_ok; field; split; intro c; try (rewrite c in k; rewrite fp_eq_true in k); discriminate.
Qed.

(* Equivalence of point multiplication*)

Local Notation g1_fc_mul := (@W.mul fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fp_fc_field g1_dec fp_char_ge nat_mod_zero nat_mod_four).

Local Notation scalarmod := 0x8000000000000000000000000000000000000000000000000000000000000000.

Local Notation inf := (nat_mod_zero, nat_mod_zero, true).

Require Import Lia.

Lemma max_unsigned32 : @max_unsigned WORDSIZE32 = 4294967295.
Proof. reflexivity. Qed.

Lemma modulus32 : @modulus WORDSIZE32 = 4294967296.
Proof. reflexivity. Qed.

(* Lemma for doing a single step in a for-loop *)
Lemma foldi_helper: forall A n i f (acc : A), 0 <= i <= 256 -> foldi_ (S n) (repr i) f acc = foldi_ (n) (repr (i +1)) f (f (repr i) acc).
Proof. intros. assert (@add WORDSIZE32 (repr i) one = repr (i + 1)). {
    unfold add. rewrite unsigned_one. rewrite unsigned_repr. reflexivity.
    rewrite max_unsigned32. lia.
  } 
  cbn. rewrite H0. reflexivity.
Qed.

Lemma g1_double_inf: forall x y, (g1double (x, y, true)) = inf. 
Proof. 
  intros. unfold g1double. destruct ((y =.? nat_mod_zero)); reflexivity. 
Qed.

Lemma g1_add_inf_l: forall p x y, (x, y, true) ?+? p = p.
Proof. intros. cbn. destruct p, p. reflexivity. 
Qed.

Lemma g1_add_inf_r: forall p x y, p ?+? (x, y, true) ?=? p.
Proof. intros [[] []]. reflexivity. reflexivity. 
Qed.

(* Defining some intermediete multiplication function to make proving easier *)

Fixpoint helperg1mul (pos : positive) (p : g1) : g1 := match pos with
| xH => p
| xO pos' => g1double (helperg1mul pos' p)
| xI pos' => g1double (helperg1mul pos' p) ?+? p
end.

Fixpoint helperg1mul' (l : list bool) (p acc : g1) : g1 := match l with
| nil => acc
| false :: l' => helperg1mul' l' p (g1double acc)
| true :: l' => helperg1mul' l' p (g1double acc ?+? p)
end.

Fixpoint from_pos_to_listbool (p : positive) := match p with
| xH => [true]
| xO p' => (from_pos_to_listbool p') ++ [false]
| xI p' => (from_pos_to_listbool p') ++ [true]
end.

Fixpoint from_listbool_to_pos (l : list bool) acc := match l with
| nil => acc
| false :: l' => from_listbool_to_pos l' (xO acc)
| true :: l' => from_listbool_to_pos l' (xI acc)
end.

Fixpoint from_listbool_to_Z (l : list bool) := match l with
| nil => Z0
| false :: l' => from_listbool_to_Z l'
| true :: l' => Zpos (from_listbool_to_pos l' xH)
end.

Definition from_Z_to_listbool z := match z with
| Z0 => nil
| Zneg _ => nil
| Zpos p => from_pos_to_listbool p
end.

Fixpoint nth_bit (n:nat) l := match l with
| b :: l' => if (n =? length l')%nat then b else nth_bit n l'
| nil => false
end.

(* Some helper lemma *)

Lemma nth_helper : forall l n a, n = length l -> nth_bit n (a :: l) = a.
Proof. intros. destruct l.
  - rewrite H. reflexivity.
  - cbn in H. cbn. rewrite H. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma mul2p1: forall p, Zpos p~1 = ((2 * Zpos p)%Z + 1)%Z.
Proof. intros. reflexivity. Qed.

Lemma mul2p: forall p, Zpos p~0 = (2 * Zpos p)%Z.
Proof. intros. reflexivity. Qed.

Lemma nth_bit2p: forall l n b, nth_bit n l = nth_bit (S n) (l ++ [b]).
Proof. intro l. induction l. reflexivity. intros. cbn.  rewrite List.last_length. destruct (n =? length l)%nat eqn:E. reflexivity.
  apply IHl.
Qed.

Lemma nth_bit_0: forall l b, nth_bit 0 (l ++ [b]) = b.
Proof. intro l. induction l; intros.
  - reflexivity.
  - cbn.  rewrite List.last_length. apply IHl.
Qed. 

Lemma testbiteq : forall (n: nat) z, 0 <= z -> Z.testbit z (Z.of_nat n) = nth_bit n (from_Z_to_listbool z).
Proof. intros n. induction n.
- intros. cbn. destruct z. reflexivity.
  + destruct p.
    * cbn. rewrite nth_bit_0. reflexivity.
    * cbn. rewrite nth_bit_0. reflexivity.
    * reflexivity.
  + lia.
- intros. destruct z. reflexivity.
  + destruct p.
    * rewrite mul2p1. rewrite Nat2Z.inj_succ. rewrite Z.testbit_odd_succ. rewrite IHn. cbn. apply nth_bit2p. lia. lia.
    * rewrite mul2p. rewrite Nat2Z.inj_succ. rewrite Z.testbit_even_succ. rewrite IHn. cbn. apply nth_bit2p. lia. lia.
    * reflexivity.
  + lia.
Qed.

Fixpoint norm_listbool l := match l with 
| nil => nil
| false :: l' => norm_listbool l'
| l => l
end.

Lemma pos_bckandfth: forall l a, from_pos_to_listbool (from_listbool_to_pos l a) = from_pos_to_listbool a ++ l.
Proof. intro l. induction l; intros.
  - destruct a; symmetry; apply List.app_nil_r.
  - cbn. destruct a; rewrite IHl; cbn; rewrite <- List.app_assoc; reflexivity.
Qed.

Lemma bckandfth: forall l, from_Z_to_listbool (from_listbool_to_Z l) = norm_listbool l.
Proof. intros. induction l.
  - reflexivity.
  - cbn. destruct a.
    + cbn. apply pos_bckandfth.
    + apply IHl.
Qed.

Lemma listboolhelper6 : forall l acc, from_listbool_to_pos (l ++ [true]) acc = ((from_listbool_to_pos l acc)~1)%positive.
Proof. intros l. induction l; intros. 
  - reflexivity.
  - cbn. destruct a; rewrite IHl; reflexivity.
Qed.

Lemma listboolhelper7 : forall l, from_listbool_to_Z (l ++ [true]) = (2 * (from_listbool_to_Z l) + 1)%Z.
Proof. intros l. induction l.
  - reflexivity.
  - cbn. destruct a.
    + cbn. rewrite listboolhelper6. reflexivity.
    + rewrite IHl. reflexivity.
Qed.

Lemma listboolhelper8 : forall l acc, from_listbool_to_pos (l ++ [false]) acc = ((from_listbool_to_pos l acc)~0)%positive.
Proof. intros l. induction l; intros. 
  - reflexivity.
  - cbn. destruct a; rewrite IHl; reflexivity.
Qed.

Lemma listboolhelper9 : forall l, from_listbool_to_Z (l ++ [false]) = (2 * (from_listbool_to_Z l))%Z.
Proof. intros l. induction l.
  - reflexivity.
  - cbn. destruct a.
    + cbn. rewrite listboolhelper8. reflexivity.
    + rewrite IHl. reflexivity.
Qed.

Lemma fthandbck: forall z, 0 <= z -> (from_listbool_to_Z (from_Z_to_listbool z)) = z.
Proof. intros. destruct z.
  - reflexivity.
  - cbn. induction p.
    + cbn. rewrite listboolhelper7. rewrite IHp. reflexivity. lia. 
    + cbn. rewrite listboolhelper9. rewrite IHp. reflexivity. lia.
    + reflexivity.
  - lia. 
Qed.

Lemma nthbit_help: forall l (n:nat), (length l <= n)%nat -> nth_bit n l = false.
Proof. intros l. induction l; intros.
  - reflexivity.
  - destruct n. cbn in H. lia. cbn. destruct (length l) eqn:E. destruct l. reflexivity. inversion E. 
    cbn in H. rewrite E in H. destruct (n =? n0)%nat eqn:E1. apply Nat.eqb_eq in E1. lia. apply IHl. lia.
Qed.

Lemma testbiteq2 : forall (n:nat) l, Z.testbit (from_listbool_to_Z l) (Z.of_nat n) =  nth_bit n l.
Proof. intros. rewrite testbiteq. rewrite bckandfth. induction l.
  + reflexivity.
  + cbn. destruct a. reflexivity. rewrite IHl. destruct (n =? length l)%nat eqn:E. apply Nat.eqb_eq in E. apply nthbit_help. lia.
    reflexivity.
  + induction l. reflexivity. cbn. destruct a. lia. lia.
Qed.

Definition helperf (s: scalar) (p : g1) := (fun i_161 t_160 =>
let t_160 :=
  g1double (t_160) in 
let '(t_160) :=
  if nat_mod_bit (s) ((usize 255) - (i_161)):bool then (
    let t_160 :=
      g1add (t_160) (p) in 
    (t_160)
  ) else ( (t_160)
  ) in 
  (t_160)).

Require Import ZArithRing.

Lemma arith_helper1 : forall (n: nat), n <= 255 -> 256 - Z.pos (Pos.of_succ_nat n) = 255 - Z.of_nat n.
Proof. intros. rewrite Zpos_P_of_succ_nat. ring.
Qed.

Lemma arith_helper2 : forall n, 0 <= n <= 255 -> (@Z_mod_modulus WORDSIZE32 (n)) = n.
Proof. intros. rewrite Z_mod_modulus_eq. rewrite Zmod_small. reflexivity. rewrite modulus32. cbn. lia.
Qed.

Lemma around: forall n, 0 <= n -> Z.of_N (N.of_nat (Z.to_nat n)) = n.
Proof. intros. rewrite Z_nat_N. apply Z2N.id, H.
Qed.

Lemma arith_helper3 : forall n, n <= 255 -> (Z.to_nat 255 - Z.to_nat (255 - n)) = n.
Proof. intros. rewrite around. rewrite around. ring. lia. lia.
Qed.

Lemma arith_helper4 : forall n, (256 - S (n) + 1)%Z = 256 - n.
Proof. intros. do 2 rewrite nat_N_Z. assert (Z.of_nat (S n) = Z.succ (Z.of_nat n)) as -> by apply Zpos_P_of_succ_nat.  ring.
Qed.

Lemma nth_small : forall (n: nat) l a, n < length l -> nth_bit n (a :: l) = nth_bit n l.
Proof. intros n. induction n.
  - intros. destruct l. cbn in H. lia. reflexivity.
  - intros. cbn. destruct (length l =? S n)%nat eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + destruct (length l) eqn:E2. reflexivity. destruct (n =? n0)%nat eqn:E3. apply Nat.eqb_eq in E3. lia.
      reflexivity. 
Qed.

Lemma listbool_size_help2 : forall l acc1 acc2, (acc1 <= acc2)%positive -> Zpos (from_listbool_to_pos l acc1) <= Zpos (from_listbool_to_pos l acc2).
Proof. intro l. induction l.
  -  intros. cbn. lia.
  - intros. cbn. destruct a; apply IHl; lia.
Qed.

Lemma listbool_size_help : forall l a, from_listbool_to_Z l <= from_listbool_to_Z (a :: l).
Proof. intros. induction l.
  - cbn. destruct a; lia.
  - destruct a, a0.
    + cbn. apply listbool_size_help2. lia.
    + cbn. cbn in IHl. pose proof listbool_size_help2 l 1 2. lia .
    + cbn. lia.
    + cbn. lia.
Qed. 

Lemma listbool_gt_0 : forall l, 0 <= from_listbool_to_Z l.
Proof. induction l.
  - cbn. lia.
  - destruct a.
    + cbn. lia.
    + cbn. apply IHl.
Qed.

Lemma listbool_size_helper : forall p, length (from_pos_to_listbool p) = Pos.size_nat p.
Proof. intros p. induction p.
  - cbn. rewrite List.last_length. rewrite IHp. reflexivity.
  - cbn. rewrite List.last_length. rewrite IHp. reflexivity.
  - reflexivity.
Qed.

Lemma listbool_size : forall z, 0 <= z < scalarmod -> (length (from_Z_to_listbool z) <= 256)%nat.
Proof. intros. destruct z.
  - cbn. lia.
  - cbn. rewrite listbool_size_helper. apply Zpow_facts.Zpower2_Psize.  lia.
  - lia.
Qed.

Lemma foldi_helper2 : forall (n: nat) l p acc a, 0 <= from_listbool_to_Z (a :: l) < scalarmod -> 0 <= n <= 256 -> (n <= length l)%nat -> foldi_ n (repr (256 - n)) (helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z (a :: l)))) p) acc
= foldi_ n (repr (256 - n)) (helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p) acc.
Proof with try lia. intros n. induction n.
  - intros. reflexivity.
  - intros. rewrite foldi_helper... rewrite foldi_helper...  rewrite arith_helper4. rewrite IHn... unfold helperf, nat_mod_bit. Opaque from_listbool_to_Z. Opaque Z.sub.  cbn.
  repeat rewrite Zmod_small... rewrite arith_helper1... rewrite (arith_helper2 (_ - Z.of_nat _))...  rewrite arith_helper3... rewrite arith_helper2...  
  rewrite testbiteq2. rewrite testbiteq2. rewrite nth_small... reflexivity. 
  pose proof (listbool_size_help l a). pose proof (listbool_gt_0 l). lia.
Qed.

Lemma helperg1muleq: forall l (n: nat) p acc,  (0 <= n <= 256)%nat -> (n = length l)%nat -> 0 <= from_listbool_to_Z (l) < scalarmod -> 
  foldi_ n (repr (256 - n)) (helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p) acc = helperg1mul' l p acc.
Proof with try lia.
  intros l. induction l.
  - intros. cbn in H0. rewrite H0. reflexivity.
  - intros. 
  subst. cbn in H. assert (length (a :: l) = S (length l)) as -> by reflexivity. rewrite foldi_helper... 
    rewrite arith_helper4. rewrite foldi_helper2... unfold helperf, nat_mod_bit. Opaque Z.sub. Opaque from_listbool_to_Z. cbn. 
    rewrite (Zmod_small (from_listbool_to_Z (a :: l))) ... rewrite arith_helper1... rewrite (arith_helper2 (_ - Z.of_nat _))... rewrite arith_helper3...  rewrite arith_helper2...  
    rewrite testbiteq2. rewrite nth_helper... unfold helperf, nat_mod_bit in IHl. cbn in IHl.
    rewrite IHl... destruct a; reflexivity. 
    pose proof (listbool_size_help l a). pose proof (listbool_gt_0 l). lia.
Qed.

Lemma foldi_helper3 : forall (n m: nat) l p, 0 <= from_listbool_to_Z l < scalarmod -> length l <= n <= 256 -> m = length l -> foldi_ n (repr (256 - n)) (helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p) inf
          = foldi_ m (repr (256 - m)) (helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p) inf.
Proof with try lia.
  intros. unfold helperf, nat_mod_bit. cbn. rewrite Zmod_small...  induction n.
  - destruct m. reflexivity. lia.
  - destruct (m =? S n)%nat eqn:E. apply Nat.eqb_eq in E. rewrite E. reflexivity.
    apply Nat.eqb_neq in E.   
    rewrite foldi_helper... rewrite arith_helper4. rewrite g1_double_inf, g1_add_inf_l. cbn.  
    rewrite arith_helper1... rewrite (arith_helper2 (255 - Z.of_nat _))...  rewrite arith_helper3...  rewrite arith_helper2... 
    rewrite testbiteq2. rewrite nthbit_help...
    apply IHn...
Qed.
    
(* Equivalence between g1mul and an intermediate mul function *)
Lemma helperg1muleq2 : forall l p, length l <= 256 -> 0 <= from_listbool_to_Z l < scalarmod -> g1mul (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p = helperg1mul' l p inf.
Proof with try lia. 
  intros. unfold g1mul, foldi. pose proof helperg1muleq. unfold helperf in H1.
  assert (unsigned (usize 256) - unsigned (usize 0) = 256) as -> by reflexivity.
  assert (Pos.to_nat 256 = 256%nat) as -> by reflexivity. rewrite <- (Z.sub_diag 256).
  pose proof foldi_helper3. unfold helperf in H2.
  rewrite H2 with (m := length l)...
  rewrite H1... reflexivity.
Qed.

(* Point multiplication defined over Z *)
Definition Zhelperg1mul (z: Z) p := match z with
| Z0 => (nat_mod_zero, nat_mod_zero, true)
| Zpos pos => helperg1mul pos p
| Zneg _ => (nat_mod_zero, nat_mod_zero, true)
end.

Opaque g1double. Opaque g1add.

Lemma mul_add_lsb1 : forall l p acc, helperg1mul' (l ++ [true]) p acc = g1double(helperg1mul' l p acc) ?+? p.
Proof. intros l. induction l.
  - intros. reflexivity.
  - intros. cbn. destruct a; apply IHl.
Qed. 

Lemma mul_add_lsb0 : forall l p acc, helperg1mul' (l ++ [false]) p acc = g1double(helperg1mul' l p acc).
Proof. intros l. induction l.
  - intros. reflexivity.
  - intros. cbn. destruct a; apply IHl.
Qed. 

Lemma helperg1muleq3 : forall z p, 0 <= z <= scalarmod -> helperg1mul' (from_Z_to_listbool z) p inf = Zhelperg1mul z p.
Proof.
  intros. destruct z.
  - reflexivity.
  - cbn. induction p0.
    + cbn. rewrite mul_add_lsb1. rewrite IHp0. reflexivity. lia.
    + cbn. rewrite mul_add_lsb0. rewrite IHp0. reflexivity. lia.
    + cbn. rewrite g1_double_inf, g1_add_inf_l. reflexivity.
  - lia.
Qed.


(* Proving some facts about g1add and g1double*)

Transparent g1double. Transparent g1add.

Lemma g1add_comm : forall p1 p2, g1_on_curve p1 -> g1_on_curve p2 -> p1 ?+? p2 ?=? p2 ?+? p1.
Proof. intros [[] []] [[] []] onc1 onc2.
  - reflexivity.
  - cbn. auto.
  - cbn. auto.
  - cbn. destruct ((f, f0, false) =.? (f1, f2, false)) eqn:E.
    + destruct (f0 =.? nat_mod_zero) eqn:E2.
      * apply eqb_leibniz in E, E2. inversion E. subst. rewrite g1_eqb_true. rewrite fp_eq_true. reflexivity.
      * apply eqb_leibniz in E. inversion E. subst. rewrite g1_eqb_true. rewrite E2. reflexivity.
    + destruct ((f1, f2, false) =.? (f, f0, false)) eqn:E3. apply eqb_leibniz in E3. rewrite E3 in E. rewrite g1_eqb_true in E. discriminate.
      destruct (f =.? f1) eqn:E1.  
      * destruct (f0 =.? nat_mod_zero -% f2) eqn:E2.
        -- apply eqb_leibniz in E1, E2. subst. field_simplify (nat_mod_zero -% (nat_mod_zero -% f2)). repeat rewrite fp_eq_true.
        reflexivity.
        -- apply eqb_leibniz in E1. subst.
        pose proof (symmetrical_x_axis _ _ _ _ onc1 onc2 eq_refl).
        destruct H.
          ++ subst. rewrite g1_eqb_true in E. discriminate.
          ++ subst. field_simplify (nat_mod_zero -% f2) in E2. rewrite fp_eq_true in E2. discriminate.
      * destruct (f1 =.? f) eqn:E4. apply eqb_leibniz in E4. rewrite E4, fp_eq_true in E1. discriminate.
        cbn. repeat rewrite exp2ismul.  split; auto; split; rewrite fp_eq_ok; field; split; intro c; rewrite sub_eq_zero_means_same in c; subst; rewrite fp_eq_true in E1; discriminate.
Qed.      
        
Lemma g1double_is_add: forall p, g1double p ?=? p ?+? p.
Proof. Opaque g1double. intros [[] []]. 
  - cbn. rewrite g1_double_inf. reflexivity.
  - cbn. rewrite g1_eqb_true. reflexivity.
  Transparent g1double.
Qed.

Add Morphism g1double : g1double_m.
Proof. intros [[][]] [[][]] H.
  - do 2 rewrite g1_double_inf. reflexivity.
  - discriminate.
  - destruct H. discriminate.
  - destruct H, H0. subst. reflexivity.
Qed.

Add Morphism g1add : g1add_m.
Proof. intros [[][]] [[][]] H [[][]] [[][]] H0; try easy; try (destruct H; discriminate).
  - destruct H0; discriminate.
  - destruct H, H0, H1, H2. subst. reflexivity.
Qed.


Lemma forth_and_back : forall p onc, g1_from_fc (g1_to_fc p onc) ?=? p.
Proof. intros [[][]] onc; reflexivity.
Qed.

Lemma g1_fc_eq_eq: forall x y, g1_from_fc x ?=? g1_from_fc y <-> x #=# y.
Proof.
    intros [[[] | []]] [[[] | []]]; unfold "?=?", "#=#"; cbn; easy.
Qed.

Lemma fc_aff_eq_refl: forall x, x #=# x.
Proof. intros [[[]| []]]; cbn; auto.
Qed.

Lemma fc_aff_eq_symm: forall x y, x #=# y -> y #=# x.
Proof. intros [[[] | []]] [[[] | []]]; unfold "#=#"; cbn; intros []; auto.
Qed.

Lemma fc_aff_eq_trans: forall x y z, x #=# y -> y #=# z -> x #=# z.
Proof.  intros [[[] | []]] [[[] | []]] [[[] | []]]; unfold "#=#"; cbn; intros [] []; subst; auto.
Qed. 

Add Relation g1_fc_point g1_fc_eq
    reflexivity proved by fc_aff_eq_refl
    symmetry proved by fc_aff_eq_symm
    transitivity proved by fc_aff_eq_trans
    as fc_aff_rel.

Add Morphism g1_fc_add : g1_fc_add_m.
Proof.
  intros p1 q1 H p2 q2 H0. unfold "#=#" in H, H0. destruct p1 as [[[]| []]], q1 as [[[]| []]]; cbn in H; destruct H; subst; cbn;
  destruct p2 as [[[]| []]], q2 as [[[]| []]]; cbn in H0; destruct H0; subst; cbn; auto. 
  rewrite (Eqdep_dec.UIP_dec g1_dec y y0). rewrite (Eqdep_dec.UIP_dec g1_dec y1 y2). reflexivity.
Qed.

Add Morphism g1_on_curve : g1_on_curve_m.
Proof.
  intros [[][]] [[][]] H; try easy; destruct H. discriminate. destruct H0. subst. reflexivity.
Qed.
  

Lemma back_and_forth : forall p onc, g1_to_fc (g1_from_fc p) onc #=# p.
Proof. intros [[[]|[]]] onc; unfold g1_to_fc; cbn; auto. Qed.


Lemma preserves_on_curve : forall p, g1_on_curve (g1_from_fc p).
Proof. intros [[[] | []]]; cbn; auto.  rewrite y. field.
Qed.

Lemma additioneqhelper: forall p q, g1_from_fc p ?+? g1_from_fc q ?=? g1_from_fc (p #+# q).
Proof. intros. rewrite (g1_addition_equal _ _ (preserves_on_curve _) (preserves_on_curve _)).
  rewrite g1_fc_eq_eq.
  rewrite (back_and_forth p). rewrite (back_and_forth q).
  reflexivity.
  Qed.

Lemma add_preserves_curve : forall p1 p2, g1_on_curve p1 -> g1_on_curve p2 -> g1_on_curve (p1 ?+? p2).
Proof. intros. rewrite <- (forth_and_back p1 H). rewrite <- (forth_and_back p2 H0). rewrite additioneqhelper. apply preserves_on_curve.
Qed.

Lemma helperg1mul_preserves_curve: forall pos p, g1_on_curve p -> g1_on_curve (helperg1mul pos p).
Proof. intros. induction pos.
  - cbn. apply add_preserves_curve; auto. rewrite g1double_is_add. apply add_preserves_curve; auto.
  - cbn. rewrite g1double_is_add. apply add_preserves_curve; auto.
  - cbn. auto.
Qed.

 
Require Import Crypto.Curves.Weierstrass.AffineProofs.
Require Import Theory.Fields.FieldsUtil.
Local Notation char_ge_12 := (Char_geq_p prime 12%positive eq_refl).

Lemma discriminant_nonzero : id
((((nat_mod_four *% @nat_mod_zero prime) *% nat_mod_zero) *% nat_mod_zero) +%
 ((((((((nat_mod_four *% nat_mod_four) +% nat_mod_four) +%
       nat_mod_four) +% nat_mod_one) +% nat_mod_one) +% nat_mod_one) *%
   nat_mod_four) *% nat_mod_four) <> nat_mod_zero).
Proof. unfold id. intro c. field_simplify in c. inversion c. Qed.

(* Proof that fiat-crypto points form a commutative group *)
Local Notation commutative_group := (@W.commutative_group fp eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div nat_mod_zero nat_mod_four fp_fc_field g1_dec fp_char_ge char_ge_12 discriminant_nonzero).

Lemma fc_assoc : forall p1 p2 p3, (p1 #+# p2) #+# p3 #=# p1 #+# (p2 #+# p3).
Proof. intros. pose proof commutative_group. destruct H, commutative_group_group, group_monoid, monoid_is_associative. symmetry. apply associative.
Qed.


Lemma g1add_assoc: forall p1 p2 p3, g1_on_curve p1 -> g1_on_curve p2 -> g1_on_curve p3 -> p1 ?+? p2 ?+? p3 ?=? p1 ?+? (p2 ?+? p3).
Proof. intros. rewrite <- (forth_and_back p1 H). rewrite <- (forth_and_back p2 H0). rewrite <- (forth_and_back p3 H1). repeat rewrite additioneqhelper. rewrite g1_fc_eq_eq.
apply fc_assoc.
Qed.

Local Hint Resolve preserves_on_curve add_preserves_curve helperg1mul_preserves_curve : on_curves.

Add Morphism g1_on_curve : on_curve_m.
Proof. intros [[][]] [[][]] H; try easy.
  - destruct H. easy.
  - destruct H, H0. subst. reflexivity.
Qed.

Lemma mul_succ_is_add : forall pos p, g1_on_curve p -> helperg1mul (Pos.succ pos) p ?=? helperg1mul (pos) p ?+? p.
Proof with auto with on_curves.
 intros. induction pos.
  - cbn. rewrite IHpos. repeat rewrite g1double_is_add. rewrite g1add_assoc... rewrite (g1add_comm p _)... repeat rewrite g1add_assoc... reflexivity.
  - cbn. reflexivity.
  - cbn. apply g1double_is_add.
Qed.

(* Equivalence from helper mul function to fiat-crypto mul *)
Lemma helperg1muleq4 : forall (n :nat) p, 0 <= Z.of_nat n < scalarmod -> Zhelperg1mul (Z.of_nat n) (g1_from_fc p) ?=? g1_from_fc (g1_fc_mul n p).
Proof with auto with on_curves. intros. induction n.
  - reflexivity.
  - cbn. destruct n.
    + cbn. destruct p as [[[]|[]]]; unfold g1_from_fc, "#+#"; cbn; auto.
    + cbn in IHn. rewrite <- Pos.succ_of_nat; auto. rewrite mul_succ_is_add... rewrite <- Pos.of_nat_succ. rewrite IHn. cbn.
      rewrite g1add_comm... rewrite additioneqhelper. reflexivity.
      lia.
Qed.

(* Equivalence from g1mul to fiat-crypto mul *)
Theorem g1_mul_equal : forall n p, 0 <= Z.of_nat n < scalarmod -> g1mul (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (Z.of_nat n))) (g1_from_fc p) ?=? g1_from_fc (g1_fc_mul n p).
Proof with try lia. intros. pose proof helperg1muleq2. unfold g1mul, nat_mod_bit. unfold g1mul, nat_mod_bit in H0. cbn. cbn in H0. 
rewrite <- (fthandbck (Z.of_nat n))... rewrite H0. rewrite helperg1muleq3... apply helperg1muleq4...
  apply listbool_size in H. lia. rewrite fthandbck...
Qed.

(*** G2 proof section ***)

Definition fp2one :fp2 := (nat_mod_one, nat_mod_zero).

Lemma fp2_ring_theory: ring_theory fp2zero fp2one fp2add fp2mul fp2sub fp2neg eq.
Proof. split; intros; unfold fp2add, fp2zero, fp2one, fp2mul, fp2sub, fp2sub, fp2neg, fp2fromfp; try destruct x; try destruct y; try destruct z; apply pair_equal_spec; split; rewrite fp_eq_ok; try field.
Qed.

Add Ring fp2_ring: fp2_ring_theory.

Definition fp2div x y := fp2mul x (fp2inv y).

Lemma helper0: forall a : fp', a *% a = nat_mod_zero -> a = nat_mod_zero.
Proof. intros. apply zero_iff in H. destruct H; apply H.
Qed. 

Lemma fp_eqb_neq: forall a b: fp', a =.? b = false -> a <> b.
Proof. intros. intro c. rewrite c in H. rewrite fp_eq_true in H. discriminate.
Qed.

Require Import Theory.Fields.QuadraticFieldExtensions.

Lemma neg_one_is_non_res:
  ~(exists x : fp', (x *% x) = neg_one).
Proof. intros contra. apply (beta_is_non_res prime blsprime eq_refl eq_refl). destruct contra as [x H]. exists x.
  unfold "*%" in H. rewrite H. reflexivity. 
Qed.

Lemma helper1: forall a b : fp', ((a *% a) +% (b *% b)) = nat_mod_zero -> a = nat_mod_zero /\ b = nat_mod_zero.
Proof. intros. destruct (b =.? nat_mod_zero) eqn:E.
  - apply eqb_leibniz in E. split. rewrite E in H. field_simplify in H. 
  apply helper0 in H. apply H.  apply E.
  - apply fp_eqb_neq in E. assert ((a *% a) /% (b *% b) = (nat_mod_neg nat_mod_one)). 
  { symmetry in H. generalize fp_field_theory. intros [[]]. rewrite Radd_comm in H. 
    rewrite <- algebra_helper_1 in H. rewrite <- H. field. apply E. }
    exfalso. apply neg_one_is_non_res. exists (a /% b). rewrite <- H0. field. apply E.
Qed.

Lemma fp2_field_theory: field_theory fp2zero fp2one fp2add fp2mul fp2sub fp2neg fp2div fp2inv eq.
Proof. split.
- apply fp2_ring_theory.
- unfold "<>". intros H. discriminate.
- reflexivity.
- intros []. unfold fp2zero, fp2mul, fp2inv, fp2one, fp2fromfp. intros H. apply pair_equal_spec. split; rewrite fp_eq_ok; field;
  intros H1; apply H; apply helper1 in H1; destruct H1 as [-> ->]; auto.
Qed.

Add Field fp2_field: fp2_field_theory.

Infix "-%2" := (fp2sub) (at level 33).
Infix "+%2" := fp2add (at level 33).
Infix "*%2" := fp2mul (at level 30).

Local Notation fp2two := (fp2one +%2 fp2one).

Lemma fp2two_equiv : fp2fromfp Lib.nat_mod_two = fp2two.
Proof. reflexivity. Qed.

Local Notation fp2three := (fp2two +%2 fp2one).

Lemma fp2three_equiv : fp2fromfp (nat_mod_from_literal 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab (repr 3))
                        = fp2three.
Proof. rewrite three_equiv. reflexivity.
Qed.

Lemma fp2_same_if_eq: forall x y:fp2, x =.? y = true <-> x = y.
Proof. Transparent "=.?". 
  intros x y. split.
  - apply eqb_leibniz.
  - intros H. rewrite H. destruct y. unfold "=.?", Dec_eq_prod. apply Bool.andb_true_iff; split; apply fp_same_if_eq; reflexivity. 
Qed.

Definition g2_eq (x y: g2) := 
  let '(x1, x2, xinf) := x in
  let '(y1, y2, yinf) := y in
  if xinf then yinf = true else
    yinf = false /\ x1 = y1 /\ x2 = y2.

Local Infix "?=2?" := g2_eq (at level 70).

Lemma g2_eq_refl: forall x, x ?=2? x.
Proof. intros [[]]. destruct b; easy.
Qed.

Lemma g2_eq_symm: forall x y, x ?=2? y -> y ?=2? x.
Proof.
    intros [[] []] [[] []]; unfold "?=2?"; easy.
Qed. 

Lemma g2_eq_tran: forall x y z, x ?=2? y -> y ?=2? z -> x ?=2? z.
Proof.
    intros [[] []] [[] []] [[] []]; unfold "?=2?"; try easy.
    intros [_ [-> ->]] [_ [-> ->]]. easy.
Qed.

Add Relation (g2) (g2_eq) 
    reflexivity proved by g2_eq_refl
    symmetry proved by g2_eq_symm
    transitivity proved by g2_eq_tran 
    as g2_eq_rel.    

(* Fiat-crypto field from standard library field *)
Instance fp2_fc_field : @field fp2 eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2inv fp2div.
Proof.
  repeat split; try apply (Fdiv_def fp_field_theory); try (intros ; field); try apply (_ (fp_field_theory)); auto.
  - symmetry; apply (F_1_neq_0 (fp2_field_theory)).
Qed.

Lemma g2_dec: DecidableRel (@eq fp2).
Proof. unfold Decidable. intros x y. pose proof (fp2_same_if_eq x y). destruct (x =.? y).
  - left. apply H. reflexivity. 
  - right. apply not_iff_compat in H. apply H. congruence.
Qed.

Lemma fp2_char_ge:  @Ring.char_ge fp2 eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul (BinNat.N.succ_pos BinNat.N.two).
Proof. 
  unfold char_ge. unfold Hierarchy.char_ge. intros pos. simpl. intros H. apply pos_le_three in H. destruct H;
  rewrite H; easy.
Qed.

Notation g2_b := (nat_mod_four, nat_mod_four).

(* Representation af a Fiat-crypto G1 point *)
Local Notation g2_fc_point := (@W.point fp2 eq fp2add fp2mul fp2zero g2_b). 
(* Fiat-Crypto Equivalence, Addition and Zero element *)
Local Notation g2_fc_eq := (@W.eq fp2 eq fp2add fp2mul fp2zero g2_b).       
Local Notation g2_fc_add := (@W.add fp2 eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2inv fp2div fp2_fc_field g2_dec fp2_char_ge fp2zero g2_b).
Local Notation g2_fc_zero := (@W.zero fp2 eq fp2add fp2mul fp2zero g2_b).

(* ?x? is x performed by hacspec. #x# is x performed by Fiat-Crypto *)
Local Infix "?+2?" := g2add (at level 61).
Local Infix "#+2#" := g2_fc_add (at level 61).
Local Infix "#=2#" := g2_fc_eq (at level 70).

(* Checking the Fiat-Crypto functions actually work*)
Example g2_add_zero_is_zero_in_fc: (g2_fc_zero #+2# g2_fc_zero) #=2# g2_fc_zero.
Proof. reflexivity.
Qed.

(* Translating Fiat-Crypto Point Representations to our G1 points (x, y, isPointAtInfinity) *)
Definition g2_from_fc (p: g2_fc_point): g2 := 
  match W.coordinates p with
  | inr tt => (fp2zero, fp2zero, true)
  | inl (pair x y) => (x, y, false)
  end.

(* Checking if a point is actually on the curve - since FC points are only defined as points on the curve, and our points are everyting from (fp, fp), this is needed *)
Definition g2_on_curve (p:g2) := let '(x, y, binf) := p in if binf then True else y *%2 y = x *%2 x *%2 x +%2 g2_b.

(* Translating our points to Fiat-Crypto Points *)
Program Definition g2_to_fc (p: g2) (on_curve : g2_on_curve p): g2_fc_point :=
    match p return fp2*fp2+unit with
    | (_, _, true) => inr tt
    | (x, y, false) => inl (x, y)
    end.
    Opaque fp2mul.
    Opaque "=.?". 
    Next Obligation.
    Crypto.Util.Tactics.BreakMatch.break_match;
    auto. rewrite on_curve. field. 
    Qed.

Lemma fp2_algebra_helper_1: forall x y z, x -%2 y = z <-> x = y +%2 z.
Proof. intros x y z. split.
  - intros H. rewrite <- H. field. 
  - intros H. rewrite H. field.
Qed.

Lemma fp2_sub_eq_zero_means_same: forall x y, x -%2 y = fp2zero <-> x = y.
Proof. split. 
  - intros H. apply fp2_algebra_helper_1 in H. rewrite H. field.
  - intros H. rewrite H. field. 
Qed.

(* Integral domain to help with som algebraic properties *)
Local Notation fp2_integral_domain := (@Field.integral_domain fp2 eq fp2zero fp2one fp2neg fp2add fp2mul fp2sub fp2inv fp2div fp2_fc_field g2_dec).

Local Notation fp2_nonzero_iff := (@IntegralDomain.IntegralDomain.nonzero_product_iff_nonzero_factors fp2 eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2_integral_domain).

Lemma fp2_negation_eq_implies_zero: forall x: fp2, x = (fp2neg x) -> x = fp2zero.
Proof. intros x H. generalize fp2_field_theory. intros [[]].
rewrite <- (Radd_0_l (fp2neg x)) in H. rewrite Radd_comm in H.
rewrite <- fp2_algebra_helper_1 in H.
assert (fp2two *%2 x = fp2zero). { rewrite <- H. field. }
apply (f_equal (fun x => x *%2 (fp2inv fp2two))) in H0.
field_simplify in H0; easy.
Qed.

Lemma fp2_square_law: forall x y, x *%2 x -%2 y *%2 y = (x +%2 y) *%2 (x -%2 y).
Proof. intros x y. field. 
Qed.

Lemma fp2_zero_iff : forall x y : fp2, x *%2 y = fp2zero <-> x = fp2zero \/ y = fp2zero.
Proof. intros. split.
  - apply Decidable.contrapositive. apply Logic.Decidable.dec_or.
    + destruct (g2_dec x fp2zero) as [e|e]; [left|right]; apply e.
    + destruct (g2_dec y fp2zero) as [e|e]; [left|right]; apply e.
    + intros H. setoid_rewrite Decidable.not_or_iff in H. apply fp2_nonzero_iff. apply H.
  - intros [-> | ->]; field.
Qed. 


Lemma fp2_symmetrical_x_axis: forall x1 y1 x2 y2, g2_on_curve (x1, y1, false) -> g2_on_curve (x2, y2, false) -> x1 = x2 -> y1 = y2 \/ y1 = fp2neg y2.
Proof. intros x1 y1 x2 y2 H1 H2 H3. 
  unfold g2_on_curve in H1, H2. rewrite <- H3 in H2. rewrite <- H2 in H1. apply fp2_sub_eq_zero_means_same in H1. rewrite fp2_square_law in H1.
  apply fp2_zero_iff in H1.
  destruct H1.
  - right. apply fp2_sub_eq_zero_means_same. rewrite <- H. field.
  - left. apply fp2_sub_eq_zero_means_same, H.
Qed.

Lemma fp2_eq_true: forall x:fp2, x =.? x = true.
Proof. intros x. apply fp2_same_if_eq. reflexivity.
Qed. 

Lemma g2_eqb_true: forall x:g2, x =.? x = true.
Proof. Transparent "=.?".
  intros [[]]. unfold "=.?", Dec_eq_prod.  
  apply Bool.andb_true_iff; split. 
  - unfold "=.?". apply Bool.andb_true_iff; split; apply fp2_same_if_eq; reflexivity. 
  - unfold "=.?", bool_eqdec. apply Bool.eqb_reflx.
Qed.


(* The equivalence proof. If two points are on the curve, adding them together using hacspec is the same as converting to fiat-crypto, adding them and converting back *)
Theorem g2_addition_equal: forall (p q: g2) on_curve_p on_curve_q, (p ?+2? q) ?=2? (g2_from_fc ((g2_to_fc p on_curve_p) #+2# (g2_to_fc q on_curve_q))). 
Proof. Opaque "=.?". Opaque fp2zero. Opaque fp2add. intros [[f f0]] [[f1 f2]] H H0. unfold g2add, g2_from_fc, g2_to_fc, g2_fc_add, g2_eq. cbn. 
  (generalize fp_field_theory). intros [[]].
  destruct b eqn:E, b0 eqn:E1; auto. 
  unfold dec. destruct (g2_dec f f1) as [e|e]. 
  2:{ destruct ((f, f0, false) =.? (f1, f2, false)) eqn:N; [ apply eqb_leibniz in N; inversion N; contradiction |]. 
    destruct (f =.? f1)eqn:N1; [apply eqb_leibniz in N1; contradiction|]. cbn.  
    split; split; auto; field. }
  destruct (g2_dec f2 (fp2neg f0)) as [e0 |e0]; subst; cbn; destruct (f0 =.? fp2zero) eqn:k.
  - apply eqb_leibniz in k as ->. assert (fp2neg fp2zero = fp2zero) as -> by field.
    rewrite g2_eqb_true. reflexivity.
  - destruct ((f1, f0, false) =.? (f1, fp2neg f0, false)) eqn: eqb;
    [apply eqb_leibniz in eqb; inversion eqb; apply fp2_negation_eq_implies_zero in H2; subst; rewrite fp2_eq_true in k; discriminate|]. 
    field_simplify (fp2neg (fp2neg f0)). repeat rewrite fp2_eq_true. cbn. reflexivity.
  - apply eqb_leibniz in k. subst. pose proof (fp2_symmetrical_x_axis _ _ _ _ H0 H eq_refl).
    destruct H1; [ field_simplify (@nat_mod_neg prime nat_mod_zero) in e0; contradiction | contradiction].
  - pose proof (fp2_symmetrical_x_axis _ _ _ _ H0 H eq_refl). destruct H1; [| contradiction].
    subst. rewrite g2_eqb_true. cbn. rewrite fp2three_equiv, fp2two_equiv.
    split; split; auto;  field; split; intro c; try (rewrite c in k; rewrite fp2_eq_true in k); discriminate.
Qed.

(* Equivalence of point multiplication*)

Local Notation g2_fc_mul := (@W.mul fp2 eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2inv fp2div fp2_fc_field g2_dec fp2_char_ge fp2zero g2_b).

Local Notation inf2 := (fp2zero, fp2zero, true).

Lemma g2_double_inf: forall x y, (g2double (x, y, true)) = inf2. 
Proof. 
  intros. unfold g2double. destruct ((y =.? fp2zero)); reflexivity. 
Qed.

Lemma g2_add_inf_l: forall p x y, (x, y, true) ?+2? p = p.
Proof. intros. cbn. destruct p, p. reflexivity. 
Qed.

Lemma g2_add_inf_r: forall p x y, p ?+2? (x, y, true) ?=2? p.
Proof. intros [[] []]; reflexivity. 
Qed.

(* Defining some intermediete multiplication function to make proving easier *)

Fixpoint helperg2mul (pos : positive) (p : g2) : g2 := match pos with
| xH => p
| xO pos' => g2double (helperg2mul pos' p)
| xI pos' => g2double (helperg2mul pos' p) ?+2? p
end.

Fixpoint helperg2mul' (l : list bool) (p acc : g2) : g2 := match l with
| nil => acc
| false :: l' => helperg2mul' l' p (g2double acc)
| true :: l' => helperg2mul' l' p (g2double acc ?+2? p)
end.

(* Some helper lemma *)

Definition g2_helperf (s: scalar) (p : g2) := (fun i_161 t_160 =>
let t_160 :=
  g2double (t_160) in 
let '(t_160) :=
  if nat_mod_bit (s) ((usize 255) - (i_161)):bool then (
    let t_160 :=
      g2add (t_160) (p) in 
    (t_160)
  ) else ( (t_160)
  ) in 
  (t_160)).

Lemma g2_foldi_helper2 : forall (n: nat) l p acc a, 0 <= from_listbool_to_Z (a :: l) < scalarmod -> 0 <= n <= 256 -> (n <= length l)%nat -> foldi_ n (repr (256 - n)) (g2_helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z (a :: l)))) p) acc
= foldi_ n (repr (256 - n)) (g2_helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p) acc.
Proof with try lia. intros n. induction n.
  - intros. reflexivity.
  - intros. rewrite foldi_helper... rewrite foldi_helper...  rewrite arith_helper4. rewrite IHn... unfold g2_helperf, nat_mod_bit. Opaque from_listbool_to_Z. Opaque Z.sub.  cbn.
  repeat rewrite Zmod_small... rewrite arith_helper1... rewrite (arith_helper2 (_ - Z.of_nat _))...  rewrite arith_helper3... rewrite arith_helper2...  
  rewrite testbiteq2. rewrite testbiteq2. rewrite nth_small... reflexivity. 
  pose proof (listbool_size_help l a). pose proof (listbool_gt_0 l). lia.
Qed.

Lemma helperg2muleq: forall l (n: nat) p acc,  (0 <= n <= 256)%nat -> (n = length l)%nat -> 0 <= from_listbool_to_Z (l) < scalarmod -> 
  foldi_ n (repr (256 - n)) (g2_helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p) acc = helperg2mul' l p acc.
Proof with try lia.
  intros l. induction l.
  - intros. cbn in H0. rewrite H0. reflexivity.
  - intros. 
  subst. cbn in H. assert (length (a :: l) = S (length l)) as -> by reflexivity. rewrite foldi_helper... 
    rewrite arith_helper4. rewrite g2_foldi_helper2... unfold g2_helperf, nat_mod_bit. Opaque Z.sub. Opaque from_listbool_to_Z. cbn. 
    rewrite (Zmod_small (from_listbool_to_Z (a :: l))) ... rewrite arith_helper1... rewrite (arith_helper2 (_ - Z.of_nat _))... rewrite arith_helper3...  rewrite arith_helper2...  
    rewrite testbiteq2. rewrite nth_helper... unfold g2_helperf, nat_mod_bit in IHl. cbn in IHl.
    rewrite IHl... destruct a; reflexivity. 
    pose proof (listbool_size_help l a). pose proof (listbool_gt_0 l). lia.
Qed.

Lemma g2_foldi_helper3 : forall (n m: nat) l p, 0 <= from_listbool_to_Z l < scalarmod -> length l <= n <= 256 -> m = length l -> foldi_ n (repr (256 - n)) (g2_helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p) inf2
          = foldi_ m (repr (256 - m)) (g2_helperf (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p) inf2.
Proof with try lia.
  intros. unfold g2_helperf, nat_mod_bit. cbn. rewrite Zmod_small...  induction n.
  - destruct m. reflexivity. lia.
  - destruct (m =? S n)%nat eqn:E. apply Nat.eqb_eq in E. rewrite E. reflexivity.
    apply Nat.eqb_neq in E.   
    rewrite foldi_helper... rewrite arith_helper4. rewrite g2_double_inf, g2_add_inf_l. cbn.  
    rewrite arith_helper1... rewrite (arith_helper2 (255 - Z.of_nat _))...  rewrite arith_helper3...  rewrite arith_helper2... 
    rewrite testbiteq2. rewrite nthbit_help...
    apply IHn...
Qed.
    
(* Equivalence between g1mul and an intermediate mul function *)
Lemma helperg2muleq2 : forall l p, length l <= 256 -> 0 <= from_listbool_to_Z l < scalarmod -> g2mul (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (from_listbool_to_Z l))) p = helperg2mul' l p inf2.
Proof with try lia. 
  intros. unfold g2mul, foldi. pose proof helperg2muleq. unfold g2_helperf in H1.
  assert (unsigned (usize 256) - unsigned (usize 0) = 256) as -> by reflexivity.
  assert (Pos.to_nat 256 = 256%nat) as -> by reflexivity. rewrite <- (Z.sub_diag 256).
  pose proof g2_foldi_helper3. unfold g2_helperf in H2.
  rewrite H2 with (m := length l)...
  rewrite H1... reflexivity.
Qed.

(* Point multiplication defined over Z *)
Definition Zhelperg2mul (z: Z) p := match z with
| Z0 => inf2
| Zpos pos => helperg2mul pos p
| Zneg _ => inf2
end.

Opaque g2double. Opaque g2add.

Lemma g2_mul_add_lsb1 : forall l p acc, helperg2mul' (l ++ [true]) p acc = g2double(helperg2mul' l p acc) ?+2? p.
Proof. intros l. induction l.
  - intros. reflexivity.
  - intros. cbn. destruct a; apply IHl.
Qed. 

Lemma g2_mul_add_lsb0 : forall l p acc, helperg2mul' (l ++ [false]) p acc = g2double(helperg2mul' l p acc).
Proof. intros l. induction l.
  - intros. reflexivity.
  - intros. cbn. destruct a; apply IHl.
Qed. 

Lemma helperg2muleq3 : forall z p, 0 <= z <= scalarmod -> helperg2mul' (from_Z_to_listbool z) p inf2 = Zhelperg2mul z p.
Proof.
  intros. destruct z.
  - reflexivity.
  - cbn. induction p0.
    + cbn. rewrite g2_mul_add_lsb1. rewrite IHp0. reflexivity. lia.
    + cbn. rewrite g2_mul_add_lsb0. rewrite IHp0. reflexivity. lia.
    + cbn. rewrite g2_double_inf, g2_add_inf_l. reflexivity.
  - lia.
Qed.

(* Proving some facts about g2double and g2add *)
Lemma g2double_is_add: forall p, g2double p ?=2? p ?+2? p.
Proof. Opaque g2double. Transparent g2add. intros [[] []]. 
  - cbn. rewrite g2_double_inf. reflexivity.
  - cbn. rewrite g2_eqb_true. reflexivity.
  Transparent g1double.
Qed.

Add Morphism g2double : g2double_m.
Proof. intros [[][]] [[][]] H.
  - do 2 rewrite g2_double_inf. reflexivity.
  - discriminate.
  - destruct H. discriminate.
  - destruct H, H0. subst. reflexivity.
Qed.

Add Morphism g2add : g2add_m.
Proof. intros [[][]] [[][]] H [[][]] [[][]] H0; try easy; try (destruct H; discriminate).
  - destruct H0; discriminate.
  - destruct H, H0, H1, H2. subst. reflexivity.
Qed.


Lemma g2_forth_and_back : forall p onc, g2_from_fc (g2_to_fc p onc) ?=2? p.
Proof. intros [[][]] onc; reflexivity.
Qed.

Lemma g2_fc_eq_eq: forall x y, g2_from_fc x ?=2? g2_from_fc y <-> x #=2# y.
Proof.
    intros [[[] | []]] [[[] | []]]; unfold "?=2?", "#=2#"; cbn; easy.
Qed.

Lemma g2_fc_aff_eq_refl: forall x, x #=2# x.
Proof. intros [[[]| []]]; cbn; auto.
Qed.

Lemma g2_fc_aff_eq_symm: forall x y, x #=2# y -> y #=2# x.
Proof. intros [[[] | []]] [[[] | []]]; unfold "#=2#"; cbn; intros []; auto.
Qed.

Lemma g2_fc_aff_eq_trans: forall x y z, x #=2# y -> y #=2# z -> x #=2# z.
Proof.  intros [[[] | []]] [[[] | []]] [[[] | []]]; unfold "#=2#"; cbn; intros [] []; subst; auto.
Qed. 

Add Relation g2_fc_point g2_fc_eq
    reflexivity proved by g2_fc_aff_eq_refl
    symmetry proved by g2_fc_aff_eq_symm
    transitivity proved by g2_fc_aff_eq_trans
    as g2_fc_aff_rel.

Add Morphism g2_fc_add : g2_fc_add_m.
Proof.
  intros p1 q1 H p2 q2 H0. unfold "#=2#" in H, H0. destruct p1 as [[[]| []]], q1 as [[[]| []]]; cbn in H; destruct H; subst; cbn;
  destruct p2 as [[[]| []]], q2 as [[[]| []]]; cbn in H0; destruct H0; subst; cbn; auto. 
  rewrite (Eqdep_dec.UIP_dec g2_dec y y0). rewrite (Eqdep_dec.UIP_dec g2_dec y1 y2). reflexivity.
Qed.

Add Morphism g2_on_curve : g2_on_curve_m.
Proof.
  intros [[][]] [[][]] H; try easy; destruct H. discriminate. destruct H0. subst. reflexivity.
Qed.
  

Lemma g2_back_and_forth : forall p onc, g2_to_fc (g2_from_fc p) onc #=2# p.
Proof. intros [[[]|[]]] onc; unfold g1_to_fc; cbn; auto. Qed.


Lemma g2_preserves_on_curve : forall p, g2_on_curve (g2_from_fc p).
Proof. intros [[[] | []]]; cbn; auto.  rewrite y. field.
Qed.

Lemma g2_additioneqhelper: forall p q, g2_from_fc p ?+2? g2_from_fc q ?=2? g2_from_fc (p #+2# q).
Proof. intros. rewrite (g2_addition_equal _ _ (g2_preserves_on_curve _) (g2_preserves_on_curve _)).
  rewrite g2_fc_eq_eq.
  rewrite (g2_back_and_forth p). rewrite (g2_back_and_forth q).
  reflexivity.
  Qed.

Lemma g2_add_preserves_curve : forall p1 p2, g2_on_curve p1 -> g2_on_curve p2 -> g2_on_curve (p1 ?+2? p2).
Proof. intros. rewrite <- (g2_forth_and_back p1 H). rewrite <- (g2_forth_and_back p2 H0). rewrite g2_additioneqhelper. apply g2_preserves_on_curve.
Qed.

Lemma helperg2mul_preserves_curve: forall pos p, g2_on_curve p -> g2_on_curve (helperg2mul pos p).
Proof. intros. induction pos.
  - cbn. apply g2_add_preserves_curve; auto. rewrite g2double_is_add. apply g2_add_preserves_curve; auto.
  - cbn. rewrite g2double_is_add. apply g2_add_preserves_curve; auto.
  - cbn. auto.
Qed.

Local Notation fp2four := (fp2three +%2 fp2one). 

Lemma g2_discriminant_nonzero : id
((((fp2four *%2 fp2zero) *%2 fp2zero) *%2 fp2zero) +%2
 ((((((((fp2four *%2 fp2four) +%2 fp2four) +%2
 fp2four) +%2 fp2one) +%2 fp2one) +%2 fp2one) *%2
 g2_b) *%2 g2_b) <> fp2zero).
Proof. unfold id. intro c. field_simplify in c. inversion c. Qed.

Local Notation fp2_char_ge_12' := (Char_Fp2_geq_p prime blsprime 12 eq_refl).

Lemma fp2_char_ge_12:  @Ring.char_ge fp2 eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul (12).
Proof. unfold Ring.char_ge, char_ge. intros.
  do 4 (destruct p; try easy).
Qed.

(* Proof that fiat-crypto points form a commutative group *)
Local Notation g2_commutative_group := (@W.commutative_group fp2 eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2inv fp2div fp2zero g2_b fp2_fc_field g2_dec fp2_char_ge fp2_char_ge_12 g2_discriminant_nonzero).

Lemma g2_fc_assoc : forall p1 p2 p3, (p1 #+2# p2) #+2# p3 #=2# p1 #+2# (p2 #+2# p3).
Proof. intros. pose proof g2_commutative_group. destruct H, commutative_group_group, group_monoid, monoid_is_associative. symmetry. apply associative.
Qed.

Lemma g2_fc_comm : forall p1 p2, (p1 #+2# p2) #=2# (p2 #+2# p1).
Proof. intros. pose proof g2_commutative_group. destruct H, commutative_group_is_commutative. apply commutative.
Qed.

Lemma g2add_comm : forall p1 p2, g2_on_curve p1 -> g2_on_curve p2 -> p1 ?+2? p2 ?=2? p2 ?+2? p1.
Proof. intros. rewrite <- (g2_forth_and_back p1 H). rewrite <- (g2_forth_and_back p2 H0).
  repeat rewrite g2_additioneqhelper. rewrite g2_fc_eq_eq. apply g2_fc_comm.
Qed.

Lemma g2add_assoc: forall p1 p2 p3, g2_on_curve p1 -> g2_on_curve p2 -> g2_on_curve p3 -> p1 ?+2? p2 ?+2? p3 ?=2? p1 ?+2? (p2 ?+2? p3).
Proof. intros. rewrite <- (g2_forth_and_back p1 H). rewrite <- (g2_forth_and_back p2 H0). rewrite <- (g2_forth_and_back p3 H1).
  repeat rewrite g2_additioneqhelper. rewrite g2_fc_eq_eq. apply g2_fc_assoc.
Qed.

Local Hint Resolve g2_preserves_on_curve g2_add_preserves_curve helperg2mul_preserves_curve : g2_on_curves.

Lemma g2_mul_succ_is_add : forall pos p, g2_on_curve p -> helperg2mul (Pos.succ pos) p ?=2? helperg2mul (pos) p ?+2? p.
Proof with auto with g2_on_curves.
 intros. induction pos.
  - cbn. rewrite IHpos. repeat rewrite g2double_is_add. rewrite g2add_assoc... rewrite (g2add_comm p _)... repeat rewrite g2add_assoc... reflexivity.
  - cbn. reflexivity.
  - cbn. apply g2double_is_add.
Qed.

(* Equivalence from helper mul function to fiat-crypto mul *)
Lemma helperg2muleq4 : forall (n :nat) p, 0 <= Z.of_nat n < scalarmod -> Zhelperg2mul (Z.of_nat n) (g2_from_fc p) ?=2? g2_from_fc (g2_fc_mul n p).
Proof with auto with g2_on_curves. intros. induction n.
  - reflexivity.
  - cbn. destruct n.
    + cbn. destruct p as [[[]|[]]]; cbn; auto.
    + cbn in IHn. rewrite <- Pos.succ_of_nat; auto. rewrite g2_mul_succ_is_add... rewrite <- Pos.of_nat_succ. rewrite IHn. cbn.
      rewrite g2add_comm... rewrite g2_additioneqhelper. reflexivity.
      lia.
Qed.

(* Equivalence from g2mul to fiat-crypto mul *)
Theorem g2_mul_equal : forall n p, 0 <= Z.of_nat n < scalarmod -> g2mul (GZnZ.mkznz _ _ (GZnZ.modz scalarmod (Z.of_nat n))) (g2_from_fc p) ?=2? g2_from_fc (g2_fc_mul n p).
Proof with try lia. intros. pose proof helperg2muleq2. unfold g2mul, nat_mod_bit. unfold g2mul, nat_mod_bit in H0. cbn. cbn in H0. 
rewrite <- (fthandbck (Z.of_nat n))... rewrite H0. rewrite helperg2muleq3... apply helperg2muleq4...
  apply listbool_size in H. lia. rewrite fthandbck...
Qed.