(* ########### PROOF SECTION ########### *)

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
Local Notation g1_fc_add := (@W.add fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul nat_mod_inv nat_mod_div fp_fc_field g1_dec fp_char_ge nat_mod_zero nat_mod_four).
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
Lemma g1_addition_equal: forall (p q: g1) on_curve_p on_curve_q, (p ?+? q) ?=? (g1_from_fc ((g1_to_fc p on_curve_p) #+# (g1_to_fc q on_curve_q))). 
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

Local Notation fp2three := (fp2one +%2 fp2two).

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

Local Notation g2_b := (nat_mod_four, nat_mod_four).

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
Definition g2_on_curve (p:g2) := let '(x, y, inf) := p in if inf then True else y *%2 y = x *%2 x *%2 x +%2 g2_b.

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
Lemma g2_addition_equal: forall (p q: g2) on_curve_p on_curve_q, (p ?+2? q) ?=2? (g2_from_fc ((g2_to_fc p on_curve_p) #+2# (g2_to_fc q on_curve_q))). 
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