

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
Require Import Hacspec.Curve.Bls.
Require Import Hacspec.Curve.BlsProof.
Require Import Field.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.


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

Lemma r'_correct : (2 ^ bw * r') mod m = 1.
Proof. auto with zarith. Qed.

Lemma m'_correct : (m * m') mod 2 ^ bw = -1 mod 2 ^ bw.
Proof. auto with zarith. Qed.

Lemma bw_big : 0 < bw.
Proof. cbv; auto. Qed.

Lemma m_big : 1 < m.
Proof. cbv; auto. Qed.

Lemma n_nz : n <> 0%nat.
Proof. cbv; discriminate. Qed.

Lemma m_small : m < (2 ^ bw) ^ Z.of_nat n.
Proof. cbv; auto. Qed.

Lemma m_big' : 1 < m.
Proof. cbv; auto. Qed.

Lemma n_small : Z.of_nat n < 2 ^ bw.
Proof. cbv. auto. Qed.

(** G1 Equivalence section **)

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

Definition char_ge_3 := (Char_geq_p m (N.succ_pos N.two) three_small).

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

(* Notation for fiat-crypto specifications/lemmas *)
Local Notation fc_proj_point := (@Projective.point (znz m) (@eq (znz m)) (zero m) (add m) (mul m) fp_a fp_b).
Local Notation fc_proj_add := (@Projective.add (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field char_ge_3 fp_dec fp_3_b fp_3_b_correct discriminant_nonzero char_ge_21).
Local Notation fc_proj_eq := (@Projective.eq (znz m) (@eq (znz m)) (zero m) (add m) (mul m) fp_a fp_b fp_dec).

Local Notation evfrom x := (eval (from_mont x)).
Local Notation encodemod := (WordByWordMontgomery.encodemod bw n m m').

Local Notation eval_encodemod := (WordByWordMontgomery.eval_encodemod bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
Local Notation encodemod_correct := (WordByWordMontgomery.encodemod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
Local Notation valid_mod := (valid_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

Local Notation to_affine := (@Projective.to_affine (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field fp_dec).
Local Notation to_affine_add := (@Projective.to_affine_add (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field char_ge_3 fp_dec fp_3_b fp_3_b_correct discriminant_nonzero char_ge_21).
Local Notation not_exceptional := (@Projective.not_exceptional (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field char_ge_3 fp_dec).
Local Infix "?=?" := g1_eq (at level 70).
Local Notation of_affine := (@Projective.of_affine (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field fp_dec ).
Local Notation fc_eq_iff_Weq := (@Projective.eq_iff_Weq (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field fp_dec).

Local Notation fc_aff_point := (@WeierstrassCurve.W.point (znz m) (@eq (znz m)) (add m) (mul m) fp_a fp_b).
Local Notation fc_aff_eq := (@WeierstrassCurve.W.eq (znz m) (@eq (znz m)) (add m) (mul m) fp_a fp_b).
Local Notation fc_aff_add := (@WeierstrassCurve.W.add (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fc_field fp_dec char_ge_3 fp_a fp_b).


Definition On_Curve (X1 Y1 Z1 : znz m) := (Y1 *m Y1 *m Z1) = (X1 *m (X1 *m X1) +m fp_a *m X1 *m (Z1 *m Z1) +m fp_b *m (Z1 *m (Z1 *m Z1))) /\ (Z1 = zero m -> Y1 <> zero m).


Program Definition to_fc_point (X1 Y1 Z1 : znz m) (on_curve : On_Curve X1 Y1 Z1) : fc_proj_point := 
     (X1, Y1, Z1).

Definition to_fc_point_from_mont X1 Y1 Z1 on_curve := to_fc_point (mkznz _ _ (modz m (evfrom X1))) (mkznz _ _ (modz m (evfrom Y1))) (mkznz _ _ (modz m (evfrom Z1))) on_curve .

Definition pair_val (p: znz m * znz m * znz m ) : Z*Z*Z := let '(x, y, z) := p in (val m x, val m y, val m z).

Lemma add_eq: forall x y : znz m, val _ (x +m y) = (val _ x) +' (val _ y).
Proof. intros. reflexivity. Qed.

Lemma mul_eq: forall x y : znz m, val _ (x *m y) = (val _ x) *' (val _ y).
Proof. intros. reflexivity. Qed.

Lemma sub_eq: forall x y : znz m, val _ (x -m y) = (val _ x) -' (val _ y).
Proof. intros. reflexivity. Qed.

Lemma val_eq: forall x H, val m (mkznz m x H) = x.
Proof. intros. reflexivity. Qed.

Lemma add_elim_mod: forall x y, x mod m +' y mod m = x +' y.
Proof. intros. unfold my_add. pull_Zmod. reflexivity. Qed.

Lemma mul_elim_mod: forall x y, (x mod m) *' (y mod m) = x *' y.
Proof. intros. unfold my_mul. pull_Zmod. reflexivity. Qed.

Lemma sub_elim_mod: forall x y, x mod m -' y mod m = x -' y.
Proof. intros. unfold my_sub. pull_Zmod. reflexivity. Qed.

Ltac znz_to_z_arith := unfold fp_a, fp_3_b; repeat (try rewrite add_eq; try rewrite mul_eq; try rewrite sub_eq; try rewrite val_eq; try rewrite add_elim_mod; try rewrite mul_elim_mod; try rewrite sub_elim_mod); rewrite <- a_small, <- three_b_small.
Ltac rememberp X1 X2 Y1 Y2 Z1 Z2 := remember (evfrom X1) as x1; remember (evfrom X2) as x2; remember (evfrom Y1) as y1; remember (evfrom Y2) as y2; remember (evfrom Z1) as z1; remember (evfrom Z2) as z2.

(* Equivalence between gallina and fiat with eq relation *)
Lemma gallina_fiat_crypto_equiv : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz on_curve1 on_curve2 except, 
    (BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <-> 
    (evfrom outx, evfrom outy, evfrom outz) = pair_val (proj1_sig (fc_proj_add (to_fc_point_from_mont X1 Y1 Z1 on_curve1) (to_fc_point_from_mont X2 Y2 Z2 on_curve2) except))).
Proof. assert (forall A (x y z: A), y = z -> (x = y <-> x = z)). {  intros. rewrite H. reflexivity. } 
    intros. apply H. unfold pair_val, fc_proj_add, proj1_sig, to_fc_point_from_mont, to_fc_point.
    rememberp X1 X2 Y1 Y2 Z1 Z2. znz_to_z_arith. reflexivity.
Qed.


Lemma fc_proj_eq_sig: forall x y, proj1_sig x = proj1_sig y -> fc_proj_eq x y.
Proof. intros [[[]]] [[[]]] H. cbn. inversion H. destruct (dec (z4 = zero m))eqn:E1; [apply e |].
    split ; reflexivity.
Qed. 

(* Equivalence between from gallina to fiat with point equality relation *)
Lemma gallina_fiat_crypto_equiv' : forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz on_curve1 on_curve2 on_curve_out except, 
    (BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz -> 
    fc_proj_eq (to_fc_point_from_mont outx outy outz on_curve_out)  (fc_proj_add (to_fc_point_from_mont X1 Y1 Z1 on_curve1) (to_fc_point_from_mont X2 Y2 Z2 on_curve2) except)).
Proof. intros. rewrite (gallina_fiat_crypto_equiv _ _ _ _ _ _ _ _ _ on_curve1 on_curve2 except) in H. 
    apply fc_proj_eq_sig. unfold to_fc_point_from_mont, to_fc_point, fc_proj_add, proj1_sig.
    apply pair_equal_spec in H.     rememberp X1 X2 Y1 Y2 Z1 Z2. 
    destruct H as [H ->]. apply pair_equal_spec in H. destruct H as [-> ->].
    apply pair_equal_spec. split; [apply pair_equal_spec; split |]; apply zirr; znz_to_z_arith; unfold "-'", "+'"; rewrite Zmod_mod; reflexivity.
Qed.

Definition gallina_spec_from_fc_point (p1 p2 pout : fc_proj_point) := 
    let '(x1, y1, z1) := pair_val (proj1_sig p1) in
    let '(x2, y2, z2) := pair_val (proj1_sig p2) in
    let '(outx, outy, outz) := pair_val (proj1_sig pout) in
    let x1 := encodemod x1 in
    let x2 := encodemod x2 in
    let y1 := encodemod y1 in
    let y2 := encodemod y2 in
    let z1 := encodemod z1 in
    let z2 := encodemod z2 in
    let outx := encodemod outx in
    let outy := encodemod outy in
    let outz := encodemod outz in
    BLS12_add_Gallina_spec x1 y1 z1 x2 y2 z2 outx outy outz.


Lemma eval_encodemod_val : forall v, evfrom (encodemod (val m v)) = (val m v).
Proof. intros v. assert (0 <= val m v < m). { destruct v. cbn. rewrite inZnZ. apply Z_mod_lt. reflexivity. }
 generalize encodemod_correct. intros []. apply H0 in H as H2. apply H1 in H as H3. rewrite <- (valid_mod H3). rewrite H2.  destruct v. cbn. symmetry. apply inZnZ. 
Qed. 

Lemma eval_three_b_list : eval three_b_list = three_b.
Proof. reflexivity. Qed.

Lemma eval_a_list : eval (a_list bw n a) = a.
Proof. reflexivity. Qed.

(* Equivalence between from fiat to gallina with point equality relation *)
Lemma gallina_fiat_crypto_equiv'' : forall p1 p2 pout except,
    fc_proj_eq pout (fc_proj_add p1 p2 except) ->
    exists pout', fc_proj_eq pout pout' /\ gallina_spec_from_fc_point p1 p2 pout'.
Proof. intros. exists (fc_proj_add p1 p2 except).
    split; [apply H|]. unfold gallina_spec_from_fc_point, BLS12_add_Gallina_spec, MontgomeryCurveSpecs.BLS12_add_Gallina_spec.
    destruct p1 as [[[]]]. destruct p2 as [[[]]]. unfold fc_proj_add, proj1_sig, pair_val. 
    repeat rewrite eval_encodemod_val. znz_to_z_arith. rewrite eval_three_b_list. rewrite eval_a_list. reflexivity.
Qed.


Definition to_hacspec_point (X1 Y1 Z1 : list Z) on_curve : g1 := g1_from_fc (to_affine (to_fc_point_from_mont X1 Y1 Z1 on_curve)).

Add Field hs_fp_field: fp_field_theory.

Lemma preserves_on_curve : forall p, g1_on_curve (g1_from_fc p).
Proof. intros [[[] | []]]; cbn; auto.  rewrite y. field.
Qed.

Lemma g1_fc_eq: forall x y :fc_aff_point, g1_from_fc x ?=? g1_from_fc y <-> fc_aff_eq x y.
Proof.
    intros [[[] | []]] [[[] | []]]; unfold "?=?", fc_aff_eq; cbn; split; intros H; inversion H; auto; discriminate.
Qed.

Lemma same_field_opp : forall x, Lib.nat_mod_neg x = opp m x.
Proof. intros. reflexivity. Qed.

Lemma dec_same: forall X x y (a b: X), (if (g1_dec x y) then a else b) = if (fp_dec x y) then a else b. 
Proof. intros. destruct (g1_dec x y); destruct (fp_dec x y); try reflexivity; try contradiction.
Qed. 


Lemma same_fc_add: forall x y, fc_aff_eq (g1_fc_add x y) (fc_aff_add x y).
Proof. intros [[[] | []]] [[[] | []]]; unfold g1_fc_add; unfold fc_aff_add; unfold fc_aff_eq; cbn; auto.
 unfold dec. do 2 rewrite dec_same. rewrite same_field_opp. destruct (fp_dec f f1); destruct (fp_dec f2 (opp m f0));
    try trivial; split; reflexivity.
Qed.

Lemma fc_aff_eq_refl: forall x, fc_aff_eq x x.
Proof. intros [[[]| []]]; cbn; auto.
Qed.

Lemma fc_aff_eq_symm: forall x y, fc_aff_eq x y -> fc_aff_eq y x.
Proof. intros [[[] | []]] [[[] | []]]; unfold fc_aff_eq; cbn; intros []; auto.
Qed.

Lemma fc_aff_eq_trans: forall x y z, fc_aff_eq x y -> fc_aff_eq y z -> fc_aff_eq x z.
Proof.  intros [[[] | []]] [[[] | []]] [[[] | []]]; unfold fc_aff_eq; cbn; intros [] []; subst; auto.
Qed. 

Add Relation fc_aff_point fc_aff_eq
    reflexivity proved by fc_aff_eq_refl
    symmetry proved by fc_aff_eq_symm
    transitivity proved by fc_aff_eq_trans
    as fc_aff_rel.

Lemma fc_aff_eq_sig: forall x y, proj1_sig x = proj1_sig y -> fc_aff_eq x y.
Proof. intros [[[] | []]] [[[] | []]]; cbn; intros H; inversion H; auto.
Qed.

Lemma fc_aff_add_compat: forall x y, fc_aff_eq (fc_aff_add x y) (fc_aff_add (g1_to_fc (g1_from_fc x) (preserves_on_curve _)) (g1_to_fc (g1_from_fc y) (preserves_on_curve _))).
Proof. intros [[[] | []]] [[[] | []]]; apply fc_aff_eq_sig; cbn; reflexivity.
Qed.

(* Gallina to hacspec equivalence *)
Lemma gallina_hacspec_equiv : forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz on_curve1 on_curve2 on_curve_out (except: not_exceptional (to_fc_point_from_mont _ _ _ on_curve1) (to_fc_point_from_mont _ _ _ on_curve2)), 
    (BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz ->
    (to_hacspec_point outx outy outz on_curve_out ?=? g1add (to_hacspec_point X1 Y1 Z1 on_curve1) (to_hacspec_point X2 Y2 Z2 on_curve2))).
Proof. intros. apply (gallina_fiat_crypto_equiv' _ _ _ _ _ _ _ _ _ on_curve1 on_curve2 on_curve_out except) in H.
    unfold to_hacspec_point. rewrite (g1_addition_equal _ _ (preserves_on_curve (to_affine (to_fc_point_from_mont X1 Y1 Z1 on_curve1))) (preserves_on_curve (to_affine (to_fc_point_from_mont X2 Y2 Z2 on_curve2)))).
    apply g1_fc_eq. rewrite same_fc_add. rewrite <- fc_aff_add_compat. rewrite <- (to_affine_add _ _ except). 
    apply fc_eq_iff_Weq. apply H.
Qed.

Definition gallina_spec_from_hacspec p1 p2 pout on_curve1 on_curve2 on_curve_out := 
        gallina_spec_from_fc_point 
        (of_affine (g1_to_fc p1 on_curve1)) 
        (of_affine (g1_to_fc p2 on_curve2)) 
        (of_affine (g1_to_fc pout on_curve_out)).

(* Hacspec to gallina equivalence *)
Lemma gallina_hacspec_equiv' : forall p1 p2 pout (except : not_exceptional p1 p2), 
    g1_from_fc (to_affine pout) ?=? g1add (g1_from_fc (to_affine p1)) (g1_from_fc (to_affine p2)) ->
    exists pout', fc_proj_eq pout pout' /\ gallina_spec_from_fc_point p1 p2 pout'.
Proof.
    intros. assert (fc_proj_eq pout (fc_proj_add p1 p2 except)).
    { apply fc_eq_iff_Weq. rewrite (to_affine_add). apply g1_fc_eq. rewrite H. 
    rewrite (g1_addition_equal _ _ (preserves_on_curve _) (preserves_on_curve _)). apply g1_fc_eq. rewrite same_fc_add. rewrite <- fc_aff_add_compat. reflexivity. }
    apply gallina_fiat_crypto_equiv'' in H0. apply H0. 
Qed.

(** G2 Equivalence section **)
Require Import Crypto.Arithmetic.Partition.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Crypto.Algebra.Hierarchy.

(* Some notation and definitions*)
Local Notation br := (4 mod m).
Local Notation bi := (4 mod m).

Local Notation three_br := (3 * br mod m).
Local Notation three_bi := (3 * bi mod m).

Definition BLS12_G2_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
    @BLS12_G2_add_Gallina_spec m bw n m' 0 0 three_br three_bi X1 Y1 Z1 X2 Y2 Z2 outx outy outz.

Local Infix "*p2'" := (my_mulFp2 m) (at level 40).
Local Infix "+p2'" := (my_addFp2 m) (at level 50).
Local Infix "-p2'" := (my_subFp2 m) (at level 50).

Local Infix "*m2" := (mulp2 m) (at level 40).
Local Infix "+m2" := (addp2 m) (at level 50).
Local Infix "-m2" := (subp2 m) (at level 50).


Local Notation Fp2 := (znz m * znz m)%type.
Local Notation fp2_a := (zerop2 m).
Local Notation fp2_b := (fp_b, fp_b).

Lemma m_odd: 2 < m.
Proof. reflexivity. Qed.

Lemma m_mod3: m mod 4 =? 3 = true.
Proof. reflexivity. Qed.

Local Notation FFp2 := ((@FFp2 m) blsprime m_odd m_mod3).

Definition fp2_fc_field := (Fp2fc m blsprime m_odd m_mod3).
Definition fp2_char_ge_3 := Char_Fp2_geq_p m blsprime 3 three_small.
Definition fp2_char_ge_21 := Char_Fp2_geq_p m blsprime 21 twenty1_small.

Lemma fc_fp2_dec : DecidableRel (@eq (Fp2)).
Proof. unfold Decidable. apply eq_dec_Fp2. Qed.

Local Notation fp2_3_b := (fp2_b +m2 fp2_b +m2 fp2_b).

Lemma mul_zero_r: forall x, x *m (zero m) = zero m.
Proof. intros []. unfold "*m". cbn. rewrite Z.mul_0_r. reflexivity. 
Qed.

Lemma fp2_discriminant_nonzero: id(((mkznz m _ (modz m 4), zero m) *m2 fp2_a *m2 fp2_a *m2 fp2_a +m2 (mkznz m _ (modz m 27), zero m) *m2 fp2_b *m2 fp2_b) <> (zerop2 m)).
Proof.  unfold id, fp_a, fp_b, zerop2, addp2, mulp2, fst, snd.  
    intros c. apply pair_equal_spec in c. destruct c.  repeat rewrite mul_zero_r in H0. discriminate H0.
Qed.

Local Notation fc_proj_p2_point := (@Projective.point Fp2 eq (zerop2 m) (addp2 m) (mulp2 m) fp2_a fp2_b).
Local Notation fc_proj_p2_add :=  (@Projective.add Fp2 eq (zerop2 m) (onep2 m) (oppp2 m) (addp2 m) (subp2 m) (mulp2 m) (invp2 m) (divp2 m) fp2_a fp2_b fp2_fc_field fp2_char_ge_3 fc_fp2_dec fp2_3_b (eq_refl) fp2_discriminant_nonzero fp2_char_ge_21).
Local Notation fc_proj_p2_eq := (@Projective.eq Fp2 eq (zerop2 m) (addp2 m) (mulp2 m) fp2_a fp2_b fc_fp2_dec).


Definition On_Curve_p2 (X1 Y1 Z1 : Fp2) := (Y1 *m2 Y1 *m2 Z1) = (X1 *m2 (X1 *m2 X1) +m2 fp2_a *m2 X1 *m2 (Z1 *m2 Z1) +m2 fp2_b *m2 (Z1 *m2 (Z1 *m2 Z1))) /\ (Z1 = zerop2 m -> Y1 <> zerop2 m).

Program Definition to_fc_p2_point (X1 Y1 Z1 : Fp2) (on_curve : On_Curve_p2 X1 Y1 Z1) : fc_proj_p2_point := 
     (X1, Y1, Z1).

Local Notation evfrom_pair := (evfrom_pair m bw n m').

Definition Fp2_from_Z_Z (x: Z*Z) : Fp2 := (mkznz _ _ (modz m (fst x)), mkznz _ _ (modz m (snd x))).

Definition to_fc_p2_point_from_mont X1 Y1 Z1 on_curve := to_fc_p2_point (Fp2_from_Z_Z (evfrom_pair X1)) (Fp2_from_Z_Z (evfrom_pair Y1)) (Fp2_from_Z_Z (evfrom_pair Z1)) on_curve.

Definition valp2 x := (val m (fst x), val m (snd x)).

Definition pair_p2_val (x: Fp2*Fp2*Fp2) := let '(x, y, z) := x in (valp2 x, valp2 y, valp2 z).

Definition pair_mod x := (fst x mod m, snd x mod m).

(* Some helper lemmas*)
Lemma Quad_neg_one: (Quad_non_res m = opp m (one m)).
Proof. reflexivity. Qed.

Lemma addp2_eq: forall x y : Fp2, valp2 (x +m2 y) = (valp2 x) +p2' (valp2 y).
Proof. intros. reflexivity. Qed.

Add Field fc_field : (FZpZ m blsprime).

Lemma mulp2_eq: forall x y : Fp2, valp2 (x *m2 y) = (valp2 x) *p2' (valp2 y).
Proof. intros [] []. unfold "*m2", "*p2'". rewrite Quad_neg_one. cbn. 
    assert (z *m z1 +m (opp m (one m) *m z0) *m z2 = z *m z1 -m z0 *m z2). { field. }
    rewrite H. unfold valp2. cbn. pull_Zmod. reflexivity.
Qed.

Lemma subp2_eq: forall x y : Fp2, valp2 (x -m2 y) = (valp2 x) -p2' (valp2 y).
Proof. reflexivity. Qed.

Lemma valp2_eq: forall x, valp2 (Fp2_from_Z_Z x) = pair_mod x.
Proof. reflexivity. Qed.

Lemma addp2_elim_mod: forall x y, pair_mod x +p2' pair_mod y = x +p2' y.
Proof. intros [] []. unfold "+p2'". cbn. pull_Zmod. reflexivity.
Qed.

Lemma mulp2_elim_mod: forall x y, pair_mod x *p2' pair_mod y = x *p2' y.
Proof. intros [] []. unfold "*p2'". cbn. push_Zmod. reflexivity. 
Qed.

Lemma subp2_elim_mod: forall x y, pair_mod x -p2' pair_mod y = x -p2' y.
Proof. intros [] []. unfold "-p2'". cbn. pull_Zmod. reflexivity.
Qed. 

Lemma three_bp2_eq: (eval (three_br_list bw n three_bi), eval (three_bi_list bw n three_bi)) = valp2 fp2_3_b.
Proof. reflexivity. Qed.

Lemma ap2_eq: (eval (ar_list bw n 0), eval (ai_list bw n 0)) = valp2 fp2_a.
Proof. reflexivity. Qed.

Ltac znz2_to_z2_arith := rewrite three_bp2_eq; rewrite ap2_eq; repeat (try rewrite addp2_eq; try rewrite mulp2_eq; try rewrite subp2_eq; try rewrite valp2_eq; try rewrite addp2_elim_mod; try rewrite mulp2_elim_mod; try rewrite subp2_elim_mod).
Ltac rememberp2 X1 X2 Y1 Y2 Z1 Z2 := remember (evfrom_pair X1) as x1; remember (evfrom_pair X2) as x2; remember (evfrom_pair Y1) as y1; remember (evfrom_pair Y2) as y2; remember (evfrom_pair Z1) as z1; remember (evfrom_pair Z2) as z2.  

(* Equivalence between gallina and fiat with eq relation *)
Lemma gallina_fiat_crypto_p2_equiv : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz on_curve1 on_curve2 except, 
    (BLS12_G2_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <-> 
    (evfrom_pair outx, evfrom_pair outy, evfrom_pair outz) = pair_p2_val (proj1_sig (fc_proj_p2_add (to_fc_p2_point_from_mont X1 Y1 Z1 on_curve1) (to_fc_p2_point_from_mont X2 Y2 Z2 on_curve2) except))).
Proof. assert (forall A (x y z: A), y = z -> (x = y <-> x = z)). {  intros. rewrite H. reflexivity. }
    intros. unfold BLS12_G2_add_Gallina_spec, MontgomeryCurveSpecs.BLS12_G2_add_Gallina_spec, to_fc_p2_point_from_mont.
    apply H. unfold pair_p2_val, fc_proj_p2_add, proj1_sig, to_fc_p2_point. 
    rememberp2 X1 X2 Y1 Y2 Z1 Z2. znz2_to_z2_arith. reflexivity.
Qed.

Lemma fc_proj_p2_eq_sig: forall x y, proj1_sig x = proj1_sig y -> fc_proj_p2_eq x y.
Proof. intros [[[]]] [[[]]] H. cbn. inversion H. destruct (dec (p4 = zerop2 m))eqn:E1; [apply e |].
    split ; reflexivity.
Qed. 

Lemma p2_backandforth: forall p, Fp2_from_Z_Z (valp2 p) = p.
Proof. intros [[][]]. apply pair_equal_spec. split; apply zirr; cbn; symmetry; [apply inZnZ | apply inZnZ0].
Qed.

(* Equivalence between from gallina to fiat with point equality relation *)
Lemma gallina_fiat_crypto_p2_equiv': forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz on_curve1 on_curve2 on_curveout except, 
(BLS12_G2_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz -> 
fc_proj_p2_eq (to_fc_p2_point_from_mont outx outy outz on_curveout) (fc_proj_p2_add (to_fc_p2_point_from_mont X1 Y1 Z1 on_curve1) (to_fc_p2_point_from_mont X2 Y2 Z2 on_curve2) except)).
Proof. intros. apply fc_proj_p2_eq_sig. rewrite (gallina_fiat_crypto_p2_equiv _ _ _ _ _ _ _ _ _ on_curve1 on_curve2 except) in H.
 unfold to_fc_p2_point_from_mont, to_fc_p2_point, proj1_sig.
 apply pair_equal_spec in H; destruct H as [H ->]; apply pair_equal_spec in H; destruct H as [-> ->].
 do 3 rewrite p2_backandforth. reflexivity. 
Qed.

Definition pair_valp2 x := let '(x, y, z) := x in (valp2 x, valp2 y, valp2 z).

Definition encodemodp2 x := (encodemod (fst x), encodemod (snd x)).

Lemma eval_encodemod_valp2 : forall v, evfrom_pair (encodemodp2 (valp2 v)) = (valp2 v).
Proof. intros []. apply pair_equal_spec. unfold encodemodp2, valp2, fst, snd. split; apply eval_encodemod_val.  
Qed. 

Definition gallina_G2_spec_from_fc_point (p1 p2 pout : fc_proj_p2_point) := 
    let '(x1, y1, z1) := pair_valp2 (proj1_sig p1) in
    let '(x2, y2, z2) := pair_valp2 (proj1_sig p2) in
    let '(outx, outy, outz) := pair_valp2 (proj1_sig pout) in
    let x1 := encodemodp2 x1 in
    let x2 := encodemodp2 x2 in
    let y1 := encodemodp2 y1 in
    let y2 := encodemodp2 y2 in
    let z1 := encodemodp2 z1 in
    let z2 := encodemodp2 z2 in
    let outx := encodemodp2 outx in
    let outy := encodemodp2 outy in
    let outz := encodemodp2 outz in
    BLS12_G2_add_Gallina_spec x1 y1 z1 x2 y2 z2 outx outy outz.

(* Equivalence between from fiat to gallina with point equality relation *)
Lemma gallina_fiat_crypto_p2_equiv'' : forall p1 p2 pout except,
    fc_proj_p2_eq pout (fc_proj_p2_add p1 p2 except) ->
    exists pout', fc_proj_p2_eq pout pout' /\ gallina_G2_spec_from_fc_point p1 p2 pout'.
Proof. intros. exists (fc_proj_p2_add p1 p2 except).
    split; [apply H|]. unfold gallina_G2_spec_from_fc_point, BLS12_G2_add_Gallina_spec, MontgomeryCurveSpecs.BLS12_G2_add_Gallina_spec.
    destruct p1 as [[[]]]. destruct p2 as [[[]]]. unfold fc_proj_p2_add, proj1_sig, pair_valp2. 
    repeat rewrite eval_encodemod_valp2. znz2_to_z2_arith. reflexivity.
Qed.
