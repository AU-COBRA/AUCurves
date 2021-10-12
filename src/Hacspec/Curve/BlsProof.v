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

Require Import Init.Logic.

Local Notation fp' := (nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab).

(* Equality between fp elements *)
(*Local Notation fp_eq := (@eq (nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab)).*)
Lemma fp_eq_ok: forall x y : fp, (x = y) <-> @eq fp' x y.
Proof. reflexivity.
Qed.

Local Notation prime := 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
(*
Local Notation fp_zero := (@nat_mod_zero 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab).

Local Notation fp_one := (@nat_mod_one 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab).
*)
Local Notation nat_mod_two := (nat_mod_one +% nat_mod_one).
Lemma two_equiv' : nat_mod_from_literal 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab (repr 2) = nat_mod_two.
Proof. unfold nat_mod_from_literal, nat_mod_from_secret_literal. 
 apply GZnZ.zirr. reflexivity. 
Qed.

Lemma two_equiv : @Lib.nat_mod_two prime = nat_mod_two.
Proof. reflexivity. Qed.

Local Notation nat_mod_three := (nat_mod_two +% nat_mod_one).

Lemma three_equiv : nat_mod_from_literal 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab (repr 3) = nat_mod_three.
Proof. unfold nat_mod_from_literal, nat_mod_from_secret_literal. 
 apply GZnZ.zirr. reflexivity. 
Qed.
Local Notation nat_mod_four := (nat_mod_three +% nat_mod_one).
(*
Local Notation fp_add  := nat_mod_add.
*)

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

Require Import Setoid.
 
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

(* If the boolean equality is the same, then the elements are the same *)
Lemma same_if_g1_eq: forall x y:g1, (x =.? y) = true -> x ?=? y.
Proof. intros [[]] [[]] H. apply eqb_leibniz in H. destruct b; now inversion H.
Qed.

(* Every element is equal itself *)
Lemma g1_eqb_true: forall p: g1, p =.? p = true.
Proof. intros [[]]. unfold "=.?", Dec_eq_prod. apply Bool.andb_true_iff; split. 
  - apply Bool.andb_true_iff; split; apply fp_same_if_eq; reflexivity. 
  - apply Bool.eqb_reflx.
Qed.

Require Import Coq.setoid_ring.Field.
Check @field_theory.
Lemma fp_field_theory: @field_theory fp' nat_mod_zero nat_mod_one nat_mod_add nat_mod_mul nat_mod_sub nat_mod_neg nat_mod_div nat_mod_inv (@eq fp').
Proof. apply (GZnZ.FZpZ prime blsprime).  Qed.

Add Field fp_field: fp_field_theory.
Lemma test : forall x: fp', x +% nat_mod_zero = x.
Proof. intros. field.
Qed.
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
    Crypto.Util.Tactics.BreakMatch.break_match. 
    - trivial. 
    - unfold g1_on_curve in on_curve. rewrite on_curve. field. 
    Qed.


Lemma algebra_helper_1: forall x y z:fp', x -% y = z <-> x = y +% z.
Proof. intros x y z. split; intros H; [rewrite <- H | rewrite H]; field.
Qed.

Lemma algebra_helper_2: forall x y z : fp', x = y -> x *% z = y *% z.
Proof.
  intros x y z ->. auto.
Qed.

Lemma sub_eq_zero_means_same: forall x y: fp', x -% y = nat_mod_zero <-> x = y.
Proof. split; intros H. 
  - apply algebra_helper_1 in H. rewrite H. field.
  - rewrite H. field. 
Qed.

(* Integral domain to help with som algebraic properties *)
Definition fp_integral_domain := @Field.integral_domain fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_mul nat_mod_sub nat_mod_inv nat_mod_div fp_fc_field g1_dec.

Definition nonzero_iff := @IntegralDomain.IntegralDomain.nonzero_product_iff_nonzero_factors fp' eq nat_mod_zero nat_mod_one nat_mod_neg nat_mod_add nat_mod_sub nat_mod_mul fp_integral_domain.

Lemma double_negation: forall p: Prop, p -> ~~p.
Proof. intros P H H1. contradiction. Qed. 

Lemma fp_neg_invo: forall x:fp, nat_mod_neg (nat_mod_neg x) = x. 
Proof. intros x. field. Qed. 

Lemma negation_eq_implies_zero: forall x: fp', x = (nat_mod_neg x) -> x = nat_mod_zero.
Proof. intros x H. generalize fp_field_theory. intros [[]].
  rewrite <- (Radd_0_l (nat_mod_neg x)) in H. rewrite Radd_comm in H.
  rewrite <- algebra_helper_1 in H.
  rewrite Rsub_def in H.
  assert (x +% x = nat_mod_two *% x). { field. }
  rewrite fp_neg_invo in H. rewrite H0 in H.
  apply (algebra_helper_2 _ _ (nat_mod_inv nat_mod_two)) in H.
  field_simplify in H; easy.
Qed.

Lemma square_law: forall x y: fp', (x *% x) -% (y *% y) = (x +% y) *% (x -% y).
Proof. intros x y. field. 
Qed.

Lemma symmetrical_x_axis: forall x1 y1 x2 y2 : fp', g1_on_curve (x1, y1, false) -> g1_on_curve (x2, y2, false) -> x1 = x2 -> y1 = y2 \/ y1 = nat_mod_neg y2.
Proof. intros x1 y1 x2 y2 H1 H2 H3. pose proof (nonzero_iff (y1 +% y2) (y1 -% y2)) as H4.
  unfold g1_on_curve in H1. unfold g1_on_curve in H2. rewrite <- H3 in H2. rewrite <- H2 in H1. apply sub_eq_zero_means_same in H1. rewrite square_law in H1.
  rewrite H1 in H4. apply not_iff_compat in H4. 
   setoid_rewrite <- @Decidable.not_or_iff in H4. destruct H4. 
  (generalize fp_field_theory). intros [[]]. assert (~@nat_mod_zero prime <> nat_mod_zero) by congruence.
  apply H in H4. setoid_rewrite not_not in H4.
  - destruct H4; [right | left]; apply sub_eq_zero_means_same; auto; rewrite Rsub_def; rewrite fp_neg_invo; auto.
  - apply @dec_or; apply g1_dec.
Qed.

Lemma exphelper: (Z.to_nat (from_uint_size 2)) = 2%nat.
Proof. reflexivity. Qed.

(* Admitted because weird compilation (wordsize is weird) *)
Lemma exp2ismul: forall (x:fp), nat_mod_exp x (2) = x *% x.
Proof. intros. unfold nat_mod_exp. rewrite exphelper. field.
Qed.

(* The equivalence proof. If two points are on the curve, adding them together using hacspec is the same as converting to fiat-crypto, adding them and converting back *)
Lemma g1_addition_equal: forall (p q: g1) on_curve_p on_curve_q, (p ?+? q) ?=? (g1_from_fc ((g1_to_fc p on_curve_p) #+# (g1_to_fc q on_curve_q))). 
Proof. intros [[]] [[]] H H0. unfold g1add, g1_from_fc, g1_to_fc, g1_fc_add, g1_eq. cbn. 
  (generalize fp_field_theory). intros [[]].
  destruct b eqn:E, b0 eqn:E1; auto. 
  unfold dec. destruct (g1_dec f f1) as [e|e]. 
  2:{ assert ((f, f0, false) =.? (f1, f2, false) = false). 
  { destruct ((f, f0, false) =.? (f1, f2, false)) eqn:N; auto. apply eqb_leibniz in N. inversion N. contradiction. }
    rewrite H1.
    destruct (f =.? f1)eqn:N; [apply eqb_leibniz in N; contradiction|]. cbn. rewrite exp2ismul. 
    split; split; auto; field. }
    
   destruct (g1_dec f2 (nat_mod_neg f0)) as [e0 |e0]. subst; cbn.
   - pose proof (symmetrical_x_axis _ _ _ _ H H0 eq_refl). 
   ((f, f0, false) =.? (f1, f2, false)) eqn:n;  inversion n. cbn. 1:{} 
  



    destruct ((f, f0, false) =.? (f1, f2, false)) eqn:E2. 
      * simpl. destruct (f0 =.? nat_mod_zero) eqn:E3. 
        --  simpl. apply same_if_g1_eq in E2. unfold g1_eq in E2. destruct E2 as [_ []]. rewrite H1. unfold dec. destruct (g1_dec f1 f1) eqn:E6. 
          ++ destruct (g1_dec f2 (nat_mod_neg f0)).
            ** simpl. reflexivity.
            ** exfalso. rewrite <- H2 in n. apply fp_same_if_eq in E3. rewrite E3 in n. destruct n. reflexivity.
          ++ exfalso. destruct n. reflexivity.
        -- simpl. apply same_if_g1_eq in E2. simpl in E2. destruct E2 as [_ []]. unfold dec. destruct (g1_dec f f1).
          ++ destruct (g1_dec f2 (nat_mod_neg f0)).
            ** exfalso. rewrite <- H2 in e0. apply negation_eq_implies_zero in e0. rewrite e0 in E3. rewrite fp_eq_true in E3. discriminate E3.
            ** repeat rewrite exp2ismul. split. reflexivity. split.
              ---  rewrite H1. rewrite two_equiv. rewrite three_equiv. rewrite fp_eq_ok. field. split.
                +++ intros c. rewrite c in E3. rewrite fp_eq_true in E3. discriminate E3.
                +++ intros c. discriminate c.
              --- rewrite two_equiv. rewrite three_equiv. rewrite H1. rewrite fp_eq_ok. field. split. 
                +++ intros c. rewrite c in E3. rewrite fp_eq_true in E3. discriminate E3.
                +++ intros c. discriminate c.
          ++ rewrite H1 in n. destruct n. reflexivity.
      * destruct (f =.? f1) eqn:E3.
        -- destruct (f0 =.? (nat_mod_zero -% f2)) eqn:E4.
          ++ simpl. destruct (g1_dec f f1).
            ** destruct (g1_dec f2 (nat_mod_neg f0)).
              --- reflexivity.
              --- exfalso. apply fp_same_if_eq in E4. rewrite E4 in n. destruct n. rewrite Rsub_def. rewrite Radd_0_l. rewrite fp_neg_invo. reflexivity.
            ** exfalso. destruct n. apply (fp_same_if_eq _ _). apply E3.
          ++ exfalso. generalize (symmetrical_x_axis f f0 f1 f2 H H0). apply fp_same_if_eq in E3. intros c. apply c in E3 as H7. destruct H7.
            ** rewrite E3 in E2. rewrite H1 in E2. rewrite g1_eqb_true in E2. discriminate.
            ** rewrite H1 in E4. rewrite Rsub_def in E4. rewrite Radd_0_l in E4. rewrite fp_eq_true in E4. discriminate E4.
        -- simpl. destruct (g1_dec f f1).
          ++ exfalso. rewrite e in E3. rewrite fp_eq_true in E3. discriminate E3.
          ++ rewrite exp2ismul. split. reflexivity. split;
             rewrite fp_eq_ok; field; intros H1; rewrite sub_eq_zero_means_same in H1; rewrite H1 in E3; rewrite fp_eq_true in E3; discriminate E3.
Qed.

Print Assumptions g1_addition_equal.

(*Lemma nat_mod_eqb_spec : forall {p} (a b : nat_mod p), Z.eqb (nat_mod_val p a) (nat_mod_val p b) = true -> a = b.
Proof. intros p [] [] H. apply GZnZ.zirr. apply Z.eqb_eq in H. cbn in H. apply H.
Qed.
  *)

(* fp2 ring/field stuff*)



Definition fp2one := (fp_one, fp_zero).

Definition fp2eq (x y:fp2) := x = y.

Lemma fp2eq_ok: forall x y, x = y <-> fp2eq x y.
Proof. intros x y. reflexivity.
Qed.

Lemma fp2_ring_theory: ring_theory fp2zero fp2one fp2add fp2mul fp2sub fp2neg fp2eq.
Proof. split; intros; unfold fp2eq, fp2add, fp2zero, fp2one, fp2mul, fp2sub, fp2sub, fp2neg, fp2fromfp; try destruct x; try destruct y; try destruct z; apply pair_equal_spec; split; rewrite fp_eq_ok; fold fp_zero; try field.
Qed.

Add Ring fp2_ring: fp2_ring_theory.

Definition fp2div x y := fp2mul x (fp2inv y).

(* Works for our prime I guess, cf. https://github.com/zkcrypto/bls12_381/blob/main/src/fp2.rs#L305 *)
Lemma helper1: forall a b, fp_eq ((a *% a) +% (b *% b)) fp_zero -> a = fp_zero /\ b = fp_zero.
Proof.  Admitted.

Check @eq.

Lemma fp2_field_theory: field_theory fp2zero fp2one fp2add fp2mul fp2sub fp2neg fp2div fp2inv fp2eq.
Proof. split.
- apply fp2_ring_theory.
- unfold "<>". intros H. discriminate.
- reflexivity.
- intros p. unfold fp2eq, fp2zero, fp2mul, fp2inv, fp2one, fp2fromfp. destruct p. intros H. apply pair_equal_spec. split; fold fp_zero; field;
  intros H1; destruct H; apply helper1 in H1; destruct H1; rewrite H0; rewrite H; apply pair_equal_spec; split; reflexivity.
Qed.

Add Field fp2_field: fp2_field_theory.

Infix "-" := fp2sub.
Infix "+" := fp2add.
Infix "*" := fp2mul.

Definition fp2two := fp2one + fp2one.

Lemma fp2two_equiv : fp2fromfp nat_mod_two = fp2two.
Proof. reflexivity. Qed.

Definition fp2three := fp2one + fp2two.

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

(* Fiat-crypto field from standard library field *)
Instance fp2_fc_field : @field fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2inv fp2div.
Proof.
  repeat split; try apply (Fdiv_def fp_field_theory); try (intros ; field); try apply (_ (fp_field_theory)); auto.
  - symmetry; apply (F_1_neq_0 (fp2_field_theory)).
Qed.

Lemma g2_dec: DecidableRel fp2eq.
Proof. unfold Decidable. unfold fp2eq. intros x y. generalize (fp2_same_if_eq x y). intros H. destruct (x =.? y).
  - left. apply H. reflexivity. 
  - right. apply not_iff_compat in H. apply H. congruence.
Qed.

Lemma fp2_char_ge:  @Ring.char_ge fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul (BinNat.N.succ_pos BinNat.N.two).
Proof. 
  unfold char_ge. unfold Hierarchy.char_ge. intros pos. simpl. intros H. apply pos_le_three in H. destruct H;
  rewrite H; simpl; intro c; discriminate c.
Qed.

Definition g2_b: fp2 := (fp_four, fp_four).

(* Representation af a Fiat-crypto G1 point *)
Definition g2_fc_point := @W.point fp2 fp2eq fp2add fp2mul fp2zero g2_b. 
(* Fiat-Crypto Equivalence, Addition and Zero element *)
Definition g2_fc_eq := @W.eq fp2 fp2eq fp2add fp2mul fp2zero g2_b.       
Definition g2_fc_add (p1 p2 :g2_fc_point ) :g2_fc_point := @W.add fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2inv fp2div fp2_fc_field g2_dec fp2_char_ge fp2zero g2_b p1 p2.
Definition g2_fc_zero := @W.zero fp2 fp2eq fp2add fp2mul fp2zero g2_b.

(* ?x? is x performed by hacspec. #x# is x performed by Fiat-Crypto *)
Local Infix "?+2?" := g2add (at level 61).
Local Infix "?=2?" := g2_eq (at level 70).
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


(* Translating our points to Fiat-Crypto Points *)
Program Definition g2_to_fc (p: g2): g2_fc_point :=
    match p return fp2*fp2+unit with
    | (_, _, true) => inr tt
    | (x, y, false) => if (y*y) =.? (x*x*x + g2_b) 
      then inl (x, y) 
      else inr tt
    end.
    Opaque fp2mul.
    Opaque "=.?". 
    Next Obligation.
    Crypto.Util.Tactics.BreakMatch.break_match. 
    - trivial. 
    - apply fp2_same_if_eq in Heqb. rewrite Heqb. field. 
    - trivial.
    Qed.

Lemma fp2_eq_ok: forall x y, x = y <-> fp2eq x y.
Proof.
  reflexivity.
Qed.

Lemma fp2_algebra_helper_1: forall x y z, x - y = z <-> x = y + z.
Proof. intros x y z. split.
  - intros H. rewrite <- H. rewrite fp2_eq_ok. field. 
  - intros H. rewrite H. rewrite fp2_eq_ok. field.
Qed.

Lemma fp2_sub_eq_zero_means_same: forall x y, x - y = fp2zero <-> x = y.
Proof. split. 
  - intros H. apply fp2_algebra_helper_1 in H. rewrite H. rewrite fp2_eq_ok. field.
  - intros H. rewrite H. rewrite fp2_eq_ok. field. 
Qed.

(* Integral domain to help with som algebraic properties *)
Definition fp2_integral_domain := @Field.integral_domain fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2mul fp2sub fp2inv fp2div fp2_fc_field g2_dec.

Definition fp2_nonzero_iff := @IntegralDomain.IntegralDomain.nonzero_product_iff_nonzero_factors fp2 fp2eq fp2zero fp2one fp2neg fp2add fp2sub fp2mul fp2_integral_domain.

Lemma fp2_neg_invo: forall x, fp2neg (fp2neg x) = x. 
Proof. intros x.  rewrite fp2_eq_ok. field. 
Qed. 

Lemma fp2_negation_eq_implies_zero: forall x, fp2eq x (fp2neg x) -> x = fp2zero.
Proof. intros x H. unfold fp2eq in H. generalize fp2_field_theory. intros [[]].
  rewrite <- (Radd_0_l (fp2neg x)) in H. rewrite Radd_comm in H.
  rewrite <- fp2_algebra_helper_1 in H.
  rewrite Rsub_def in H.
  rewrite <- fp2_neg_invo.
  assert (x + x = fp2two * x). {  rewrite fp2_eq_ok. unfold fp2two. field. }
  rewrite fp2_neg_invo in H. rewrite H0 in H. generalize (fp2_nonzero_iff fp2two x). intros H1. apply not_iff_compat in H1. destruct H1.
  apply double_negation in H. apply H1 in H. apply Classical_Prop.not_and_or in H. destruct H.
  - destruct H. intros c. discriminate c.
  - apply Classical_Prop.NNPP in H. rewrite H. rewrite fp2_neg_invo. reflexivity.
Qed.

Lemma fp2_square_law: forall x y, x * x - y * y = (x + y) * (x - y).
Proof. intros x y. rewrite fp2_eq_ok. field. 
Qed.

(* Checking if a point is actually on the curve - since FC points are only defined as points on the curve, and our points are everyting from (fp, fp), this is needed *)
Definition g2_on_curve (p:g2) := let '(x, y, inf) := p in if inf then True else y*y=x*x*x + g2_b.

Lemma fp2_symmetrical_x_axis: forall x1 y1 x2 y2, g2_on_curve (x1, y1, false) -> g2_on_curve (x2, y2, false) -> x1 = x2 -> y1 = y2 \/ y1 = fp2neg y2.
Proof. intros x1 y1 x2 y2 H1 H2 H3. generalize (fp2_nonzero_iff (y1 + y2) (y1 - y2)). intro H4.
  unfold g2_on_curve in H1. unfold g2_on_curve in H2. rewrite <- H3 in H2. rewrite <- H2 in H1. apply fp2_sub_eq_zero_means_same in H1. rewrite fp2_square_law in H1.
  apply not_iff_compat in H4. rewrite H1 in H4. unfold fp2eq in H4. destruct H4. 
  (generalize fp2_field_theory). intros [[]]. apply Classical_Prop.not_and_or in H. 
  - destruct H.
    + right. apply fp2_sub_eq_zero_means_same. rewrite Rsub_def. rewrite fp2_neg_invo. apply Classical_Prop.NNPP. apply H.
    + left. apply fp2_sub_eq_zero_means_same. apply Classical_Prop.NNPP. apply H.
  - congruence.
Qed.


Lemma fp2_eq_true: forall x:fp2, x =.? x = true.
Proof. intros x. apply fp2_same_if_eq. reflexivity.
Qed. 

Lemma same_if_g2_eq: forall x y, x =.? y = true -> g2_eq x y.
Proof. intros x y. unfold g2_eq. destruct x. destruct y. destruct p. destruct p0. intros H. apply eqb_leibniz in H.
destruct b.
- inversion H. reflexivity.
- inversion H. split; split; reflexivity.
Qed.

Lemma fp2from_two: fp2fromfp fp_two = fp2two.
Proof. reflexivity. 
Qed.

Lemma fp2from_three: fp2fromfp fp_three = fp2three.
Proof. reflexivity. 
Qed.

Lemma g2_eqb_true: forall x:g2, x =.? x = true.
Proof. Transparent "=.?".
  intros p. destruct p. destruct p. unfold "=.?", Dec_eq_prod.  
  apply Bool.andb_true_iff; split. 
  - unfold "=.?". apply Bool.andb_true_iff; split; apply fp2_same_if_eq; reflexivity. 
  - unfold "=.?", bool_eqdec. apply Bool.eqb_reflx.
Qed.


(* The equivalence proof. If two points are on the curve, adding them together using hacspec is the same as converting to fiat-crypto, adding them and converting back *)
Lemma g2_addition_equal: forall p q: g2, g2_on_curve p -> g2_on_curve q -> (p ?+2? q) ?=2? (g2_from_fc ((g2_to_fc p) #+2# (g2_to_fc q))). 
Proof. Opaque "=.?". Opaque fp2add. intros p q H H0. unfold g2add. destruct p. destruct p. destruct q. destruct p1.
  unfold g2_from_fc, g2_to_fc, g2_fc_add. unfold g2_eq. simpl. repeat rewrite fp2from_two. repeat rewrite fp2from_three.
  (generalize fp2_field_theory). intros [[]].
  destruct b eqn:E.
  - destruct b0 eqn:E1.
    + reflexivity.
    + unfold g2_on_curve in H0. rewrite <- H0. rewrite fp2_eq_true. split; split; reflexivity. 
  - destruct b0 eqn:E1.
    + unfold g2_on_curve in H. rewrite <- H. rewrite fp2_eq_true. split; split; reflexivity.
    + unfold g2_on_curve in H. unfold g2_on_curve in H0. rewrite H0. rewrite H. repeat rewrite fp2_eq_true.       
    destruct ((p, p0, false) =.? (p1, p2, false)) eqn:E2. 
      * simpl. destruct (p0 =.? fp2zero) eqn:E3. 
        --  simpl. apply same_if_g2_eq in E2. unfold g2_eq in E2. destruct E2 as [_ []]. rewrite H1. unfold fp2eq. unfold dec. destruct (g2_dec p1 p1) eqn:E6. 
          ++ destruct (g2_dec p2 (fp2neg p0)).
            ** reflexivity.
            ** exfalso. rewrite <- H2 in n. apply fp2_same_if_eq in E3. rewrite E3 in n. destruct n. reflexivity.
          ++ exfalso. destruct n. reflexivity.
        -- simpl. apply same_if_g2_eq in E2. simpl in E2. destruct E2 as [_ []]. destruct (dec (fp2eq p p1)).
          ++ destruct (dec (fp2eq p2 (fp2neg p0))).
            ** exfalso. rewrite <- H2 in f0. apply fp2_negation_eq_implies_zero in f0. rewrite f0 in E3. rewrite fp2_eq_true in E3. discriminate E3.
            ** split. reflexivity. split.
              --- rewrite fp2_eq_ok. rewrite H1. rewrite fp2two_equiv. rewrite fp2three_equiv. unfold fp2three. unfold fp2two. field. split.
                +++ unfold fp2eq. intros c. rewrite c in E3. rewrite fp2_eq_true in E3. discriminate E3.
                +++ unfold fp2eq. intros c. discriminate c.
              --- rewrite fp2two_equiv. rewrite fp2three_equiv. unfold fp2three. unfold fp2three. unfold fp2two. rewrite fp2_eq_ok. rewrite H1. field. split. 
                +++ unfold fp2eq. intros c. rewrite c in E3. rewrite fp2_eq_true in E3. discriminate E3.
                +++ unfold fp2eq. intros c. discriminate c.
          ++ rewrite H1 in n. destruct n. reflexivity.
      * destruct (p =.? p1) eqn:E3.
        -- destruct (p0 =.? (fp2neg p2)) eqn:E4.
          ++ simpl. destruct (dec (fp2eq p p1)).
            ** destruct (dec (fp2eq p2 (fp2neg p0))).
              --- reflexivity.
              --- exfalso. apply fp2_same_if_eq in E4. rewrite E4 in n. destruct n. field.
            ** exfalso. destruct n. unfold fp2eq. apply (fp2_same_if_eq _ _). apply E3.
          ++ exfalso. generalize (fp2_symmetrical_x_axis p p0 p1 p2 H H0). apply fp2_same_if_eq in E3. intros c. apply c in E3 as H7. destruct H7.
            ** rewrite E3 in E2. rewrite H1 in E2. rewrite g2_eqb_true in E2. discriminate.
            ** rewrite H1 in E4. rewrite fp2_eq_true in E4. discriminate E4.
        -- simpl. destruct (dec (fp2eq p p1)).
          ++ exfalso. unfold fp2eq in f. rewrite f in E3. rewrite fp2_eq_true in E3. discriminate E3.
          ++ split. reflexivity. split;
            rewrite fp2_eq_ok; field; unfold fp2eq; intros H1; rewrite fp2_sub_eq_zero_means_same in H1; rewrite H1 in E3; rewrite fp2_eq_true in E3; discriminate E3.
Qed.