Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Bedrock.Field.bls12prime.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import MontgomeryRingTheory.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Theory.Fields.FieldsUtil.
Require Import Hacspec.Curve.blsprime.
From Coqprime Require Import GZnZ.

Local Open Scope Z_scope.

(*Parameters to be changed: specify prime and import reification from cache.*)
Require Import Bedrock.Examples.felem_copy_64.
Local Definition felem_suffix := felem_copy_64.aff.
Local Notation m := bls12prime.m.
Local Notation a := (0 mod m).
Local Notation b := (4 mod m).

(*Initializing parameters; do not touch*)
Local Notation bw := width.
Local Notation m' := (@WordByWordMontgomery.m' m bw).
Notation n := (WordByWordMontgomery.n m (@width semantics)).
Local Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
Local Notation valid := (@WordByWordMontgomery.valid bw n m).
Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
Local Notation thisword := (@word semantics).
Local Definition valid_words w := valid (List.map (@Interface.word.unsigned width thisword) w).
Local Definition map_words := List.map (@Interface.word.unsigned width thisword).
Local Notation r := (WordByWordMontgomery.r bw).
Local Notation r' := (WordByWordMontgomery.r' m bw).
Local Definition num_bytes := Eval compute in (Z.of_nat (((Z.to_nat bw * n) / 8)%nat)).
Local Notation three_b := (3 * b mod m).
Local Notation uw := (uweight bw).
Notation three_b_list := (MontgomeryCurveSpecs.three_b_list bw n three_b).
Definition three_b_mont := Eval vm_compute in (MontgomeryCurveSpecs.three_b_mont_list m bw n m' three_b).

(*Lemmas of correctness of parameters to be used for montgomery arithmetic.*)
Lemma a_small : a = a mod m.
Proof. auto. Qed.

Lemma three_b_small : three_b = three_b mod m.
Proof. auto. Qed.

Definition BLS12_add_Gallina_spec :=
    BLS12_add_Gallina_spec m bw n m' a three_b.

Local Infix "*'" := (my_mul m) (at level 40).
Local Infix "+'" := (my_add m) (at level 50).
Local Infix "-'" := (my_sub m) (at level 50).

Local Infix "*m" := (mul m) (at level 40).
Local Infix "+m" := (add m) (at level 50).
Local Infix "-m" := (sub m) (at level 50).

Definition fp_a := mkznz _ _ (modz m a).
Definition fp_b := mkznz _ _ (modz m b).
Definition fc_field := ZpZfc m blsprime.

Lemma three_small : 3 < m.
Proof. reflexivity. Qed.

Definition char_ge_3 := (Char_geq_p m 3%positive three_small).

Lemma fp_dec: DecidableRel (@eq (znz m)).
Proof. unfold Decidable. intros [x Hx] [y Hy]. generalize (Z.eqb_eq x y). intros H. destruct (x =? y) eqn:E.
  - left. apply (zirr m x y Hx Hy). apply H. reflexivity. 
  - right. intros c. inversion c. apply H in H1. discriminate H1.
Qed.

Definition fp_3_b := mkznz _ _ (modz m three_b).

Lemma fp_3_b_correct : fp_3_b = fp_b +m fp_b +m fp_b. 
Proof. reflexivity. Qed.

Lemma discriminant_nonzero: id(((mkznz m _ (modz m 4)) *m fp_a *m fp_a *m fp_a +m (mkznz m _ (modz m 27)) *m fp_b *m fp_b) <> (zero m)).
Proof. unfold fp_a, fp_b, zero, add. cbn. congruence. Qed.

Lemma twenty1_small : 21 < m.
Proof. reflexivity. Qed.

Definition char_ge_21 := (Char_geq_p m 21%positive twenty1_small).


Local Notation fc_proj_point := (@Projective.point (znz m) (@eq (znz m)) (zero m) (add m) (mul m) fp_a fp_b).
Local Notation fc_proj_add := (@Projective.add (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field char_ge_3 fp_dec fp_3_b fp_3_b_correct discriminant_nonzero char_ge_21).


Local Notation evfrom x := (eval (from_mont x)).

Definition On_Curve (X1 Y1 Z1 : znz m) := (Y1 *m Y1 *m Z1) = (X1 *m (X1 *m X1) +m fp_a *m X1 *m (Z1 *m Z1) +m fp_b *m (Z1 *m (Z1 *m Z1))) /\ (Z1 = zero m -> Y1 <> zero m).


Program Definition to_fc_point (X1 Y1 Z1 : znz m) (on_curve : On_Curve X1 Y1 Z1) : fc_proj_point := 
     (X1, Y1, Z1).

Definition to_fc_point_from_mont X1 Y1 Z1 := to_fc_point (mkznz _ _ (modz m (evfrom X1))) (mkznz _ _ (modz m (evfrom Y1))) (mkznz _ _ (modz m (evfrom Z1))) .

Definition pair_val (p: znz m * znz m * znz m ) : Z*Z*Z := let '(x, y, z) := p in (val m x, val m y, val m z).

Lemma add_eq: forall x y : znz m, val _ (x +m y) = (val _ x) +' (val _ y).
Proof. intros. reflexivity. Qed.

Lemma mul_eq: forall x y : znz m, val _ (x *m y) = (val _ x) *' (val _ y).
Proof. intros. reflexivity. Qed.

Lemma sub_eq: forall x y : znz m, val _ (x -m y) = (val _ x) -' (val _ y).
Proof. intros. reflexivity. Qed.

Lemma val_eq: forall x H, val m (mkznz m x H) = x.
Proof. intros. reflexivity. Qed.
Search ((?x * ?y) mod ?m = (?x mod ?m * ?y mod ?m) mod ?m).

Lemma add_elim_mod: forall x y, x mod m +' y mod m = x +' y.
Proof. intros. unfold my_add. symmetry. apply Zplus_mod. Qed.

Lemma mul_elim_mod: forall x y, (x mod m) *' (y mod m) = x *' y.
Proof. intros. unfold my_mul. symmetry. apply Z.mul_mod. unfold m. congruence. Qed.

Lemma sub_elim_mod: forall x y, x mod m -' y mod m = x -' y.
Proof. intros. unfold my_sub. symmetry. apply Zminus_mod. Qed.

Ltac helper := repeat (try rewrite add_eq; try rewrite mul_eq; try rewrite sub_eq; try rewrite val_eq; try rewrite add_elim_mod; try rewrite mul_elim_mod; try rewrite sub_elim_mod).

Lemma galina_fiat_crypto_equiv : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz on_curve1 on_curve2 not_except, 
    (BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <-> 
    (evfrom outx, evfrom outy, evfrom outz) = pair_val (proj1_sig (fc_proj_add (to_fc_point_from_mont X1 Y1 Z1 on_curve1) (to_fc_point_from_mont X2 Y2 Z2 on_curve2) not_except))).
Proof. split.
    - unfold BLS12_add_Gallina_spec. unfold MontgomeryCurveSpecs.BLS12_add_Gallina_spec. intros H. apply pair_equal_spec in H. destruct H as [H H3]. apply pair_equal_spec in H. destruct H as [H1 H2].
    apply pair_equal_spec. split.
        + apply pair_equal_spec. split.
            * unfold fp_a, fp_3_b. helper. rewrite <- a_small. rewrite <- three_b_small. rewrite H1. reflexivity.
            * unfold fp_a, fp_3_b. helper. rewrite <- a_small. rewrite <- three_b_small. rewrite H2. reflexivity.
        + unfold fp_a, fp_3_b. helper. rewrite <- a_small. rewrite <- three_b_small. rewrite H3. reflexivity.
    - intros H. apply pair_equal_spec in H. destruct H as [H H3]. apply pair_equal_spec in H. destruct H as [H1 H2].
    apply pair_equal_spec. split.
        + apply pair_equal_spec. split.
         * rewrite H1. unfold fp_a, fp_3_b. helper. rewrite <- a_small. rewrite <- three_b_small. reflexivity.
         * rewrite H2. unfold fp_a, fp_3_b. helper. rewrite <- a_small. rewrite <- three_b_small. reflexivity.
        + rewrite H3. unfold fp_a, fp_3_b. helper. rewrite <- a_small. rewrite <- three_b_small. reflexivity.
Qed.

