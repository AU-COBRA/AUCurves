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
From Coqprime Require Import GZnZ.
Require Import Field.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import ZArith.Znumtheory.
Require Import Lia.

About prime.
Section G1Equiv.
    Open Scope Z_scope.
    Local Coercion Z.of_nat : nat >-> Z.
    (*Some notation*)
    Context (m : Z)
            (bw : Z)
            (n : nat)
            (r' : Z)
            (m' : Z)
            (a : Z)
            (b : Z)
            (a_small : a = a mod m)            
            (m_prime : prime m).

    Local Notation three_b := (b + b + b).
    Local Notation r := (MontgomeryRingTheory.r bw).

    Context (three_b_small : three_b = three_b mod m)
            (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bw_big : 0 < bw)
            (n_nz : n <> 0%nat)
            (m_small : m < r ^ (n%nat))
            (m_big : 1 < m)
            (twenty1_small : 21 < m).

    Local Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
    Local Notation valid := (@WordByWordMontgomery.valid bw n m).
    Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
    Local Notation three_b_list := (MontgomeryCurveSpecs.three_b_list bw n three_b).

    Definition BLS12_add_Gallina_spec :=
        BLS12_add_Gallina_spec m bw n m' a three_b.

    Local Infix "*'" := (my_mul m) (at level 40).
    Local Infix "+'" := (my_add m) (at level 50).
    Local Infix "-'" := (my_sub m) (at level 50).

    Local Infix "*m" := (mul m) (at level 40).
    Local Infix "+m" := (add m) (at level 50).
    Local Infix "-m" := (sub m) (at level 50).

    Local Notation fp_a := (mkznz _ _ (modz m a)).
    Local Notation fp_b := (mkznz _ _ (modz m b)).
    Local Notation fc_field := (ZpZfc m m_prime).

    Lemma three_small : 3 < m.
    Proof. lia. Qed.

    Local Notation char_ge_3 := (Char_geq_p m (N.succ_pos N.two) three_small).

    Lemma fp_dec: DecidableRel (@eq (znz m)).
    Proof. unfold Decidable. intros [x Hx] [y Hy]. generalize (Z.eqb_eq x y). intros H. destruct (x =? y) eqn:E.
    - left. apply (zirr m x y Hx Hy). apply H. reflexivity. 
    - right. intros c. inversion c. apply H in H1. discriminate H1.
    Qed.

    Local Notation fp_3_b := (mkznz _ _ (modz m three_b)).

    Lemma fp_3_b_correct : fp_3_b = fp_b +m fp_b +m fp_b. 
    Proof.  apply zirr. cbn. pull_Zmod. reflexivity. Qed.

    Local Notation four := (one m +m one m +m one m +m one m).
    Local Notation twenty7 := (four *m four +m four +m four +m one m +m one m +m one m).
    Hypothesis discriminant_nonzero: id((four *m fp_a *m fp_a *m fp_a +m twenty7 *m fp_b *m fp_b) <> (zero m)).


    Definition char_ge_21 := (Char_geq_p m 21%positive twenty1_small).

    (* Notation for fiat-crypto specifications/lemmas *)
    Local Notation fc_proj_point := (@Projective.point (znz m) (@eq (znz m)) (zero m) (add m) (mul m) fp_a fp_b).
    Local Notation fc_proj_add := (@Projective.add (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field char_ge_3 fp_dec fp_3_b fp_3_b_correct discriminant_nonzero char_ge_21).
    Local Notation fc_proj_eq := (@Projective.eq (znz m) (@eq (znz m)) (zero m) (add m) (mul m) fp_a fp_b fp_dec).
    Local Notation not_exceptional := (@Projective.not_exceptional (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field char_ge_3 fp_dec).

    Local Notation evfrom x := (eval (from_mont x)).
    Local Notation encodemod := (WordByWordMontgomery.encodemod bw n m m').

    Local Notation eval_encodemod := (WordByWordMontgomery.eval_encodemod bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Notation encodemod_correct := (WordByWordMontgomery.encodemod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Notation valid_mod := (valid_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

    (*
    Local Notation to_affine := (@Projective.to_affine (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field fp_dec).
    Local Notation to_affine_add := (@Projective.to_affine_add (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field char_ge_3 fp_dec fp_3_b fp_3_b_correct discriminant_nonzero char_ge_21).
    
    Local Notation of_affine := (@Projective.of_affine (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field fp_dec ).
    Local Notation fc_eq_iff_Weq := (@Projective.eq_iff_Weq (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fp_a fp_b fc_field fp_dec).

    Local Notation fc_aff_point := (@WeierstrassCurve.W.point (znz m) (@eq (znz m)) (add m) (mul m) fp_a fp_b).
    Local Notation fc_aff_eq := (@WeierstrassCurve.W.eq (znz m) (@eq (znz m)) (add m) (mul m) fp_a fp_b).
    Local Notation fc_aff_add := (@WeierstrassCurve.W.add (znz m) (@eq (znz m)) (zero m) (one m) (opp m) (add m) (sub m) (mul m) (inv m) (div m) fc_field fp_dec char_ge_3 fp_a fp_b).
    *)

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

    Ltac znz_to_z_arith := repeat (try rewrite add_eq; try rewrite mul_eq; try rewrite sub_eq; try rewrite val_eq; try rewrite add_elim_mod; try rewrite mul_elim_mod; try rewrite sub_elim_mod); rewrite <- a_small, <- three_b_small.
    Ltac rememberp X1 X2 Y1 Y2 Z1 Z2 := remember (evfrom X1) as x1; remember (evfrom X2) as x2; remember (evfrom Y1) as y1; remember (evfrom Y2) as y2; remember (evfrom Z1) as z1; remember (evfrom Z2) as z2.

    Lemma eval_three_b_list : eval three_b_list = three_b.
    Proof. Admitted.

    Lemma eval_a_list : eval (a_list bw n a) = a.
    Proof. Admitted.

    (* Equivalence between gallina and fiat with eq relation *)
    Lemma gallina_fiat_crypto_equiv : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz on_curve1 on_curve2 except, 
        (BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <-> 
        (evfrom outx, evfrom outy, evfrom outz) = pair_val (proj1_sig (fc_proj_add (to_fc_point_from_mont X1 Y1 Z1 on_curve1) (to_fc_point_from_mont X2 Y2 Z2 on_curve2) except))).
    Proof. assert (forall A (x y z: A), y = z -> (x = y <-> x = z)). {  intros. rewrite H. reflexivity. } 
        intros. apply H. unfold pair_val, fc_proj_add, proj1_sig, to_fc_point_from_mont, to_fc_point.
        rememberp X1 X2 Y1 Y2 Z1 Z2. znz_to_z_arith. rewrite eval_three_b_list, eval_a_list. reflexivity.
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
    Proof. intros v. assert (0 <= val m v < m). { destruct v. cbn. rewrite inZnZ. apply Z_mod_lt. lia. }
    generalize encodemod_correct. intros []. apply H0 in H as H2. apply H1 in H as H3. rewrite <- (valid_mod H3). rewrite H2.  destruct v. cbn. symmetry. apply inZnZ. 
    Qed. 

    (* Equivalence between from fiat to gallina with point equality relation *)
    Lemma gallina_fiat_crypto_equiv'' : forall p1 p2 pout except,
        fc_proj_eq pout (fc_proj_add p1 p2 except) ->
        exists pout', fc_proj_eq pout pout' /\ gallina_spec_from_fc_point p1 p2 pout'.
    Proof. intros. exists (fc_proj_add p1 p2 except).
        split; [apply H|]. unfold gallina_spec_from_fc_point, BLS12_add_Gallina_spec, MontgomeryCurveSpecs.BLS12_add_Gallina_spec.
        destruct p1 as [[[]]]. destruct p2 as [[[]]]. unfold fc_proj_add, proj1_sig, pair_val. 
        repeat rewrite eval_encodemod_val. znz_to_z_arith. rewrite eval_three_b_list, eval_a_list. reflexivity.
    Qed.
