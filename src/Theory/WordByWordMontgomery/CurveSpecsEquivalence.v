Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Semantics.
Require Import Crypto.Bedrock.Field.Common.Types.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import MontgomeryRingTheory.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Algebra.Field.
Require Import Theory.Fields.FieldsUtil.
From Coqprime Require Import GZnZ.
Require Import Field.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import ZArith.Znumtheory.
Require Import Lia.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Crypto.Algebra.Hierarchy.

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
            (three_b : Z)
            (a_small : a = a mod m) 
            (b_small : b = b mod m)
            (three_b_small : three_b = three_b mod m)
            (three_b_correct : three_b = b + b + b).

    Local Notation r := (MontgomeryRingTheory.r bw).

    Context (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bw_big : 0 < bw)
            (n_nz : n <> 0%nat)
            (m_small : m < r ^ (n%nat))
            (m_big : 1 < m)
            (twenty1_small : 21 < m)           
            (m_prime : prime m).

    Local Notation eval := (@WordByWordMontgomery.WordByWordMontgomery.eval bw n).
    Local Notation valid := (@WordByWordMontgomery.valid bw n m).
    Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
    Local Notation three_b_list := (MontgomeryCurveSpecs.three_b_list bw n three_b).

    Local Notation BLS12_add_Gallina_spec :=
        (BLS12_add_Gallina_spec m bw n m' a three_b).

    Local Infix "*'" := (my_mul m) (at level 40).
    Local Infix "+'" := (my_add m) (at level 50).
    Local Infix "-'" := (my_sub m) (at level 50).

    Local Infix "*m" := (mul m) (at level 40).
    Local Infix "+m" := (add m) (at level 50).
    Local Infix "-m" := (sub m) (at level 50).

    Local Notation fp_a := (mkznz m a a_small).
    Local Notation fp_b := (mkznz m b b_small).
    Local Notation fc_field := (ZpZfc m m_prime).

    Lemma three_small : 3 < m.
    Proof. lia. Qed.

    Local Notation char_ge_3 := (Char_geq_p m (N.succ_pos N.two) three_small).

    Lemma fp_dec: DecidableRel (@eq (znz m)).
    Proof. unfold Decidable. intros [x Hx] [y Hy]. generalize (Z.eqb_eq x y). intros H. destruct (x =? y) eqn:E.
    - left. apply (zirr m x y Hx Hy). apply H. reflexivity. 
    - right. intros c. inversion c. apply H in H1. discriminate H1.
    Qed.

    Local Notation fp_3_b := (mkznz m three_b three_b_small).

    Lemma fp_3_b_correct : fp_3_b = fp_b +m fp_b +m fp_b. 
    Proof.  apply zirr. cbn. pull_Zmod. rewrite <- three_b_correct. auto. Qed.

    Local Notation four := (one m +m one m +m one m +m one m).
    Local Notation twenty7 := (four *m four +m four +m four +m one m +m one m +m one m).
    Context     (discriminant_nonzero: id((four *m fp_a *m fp_a *m fp_a +m twenty7 *m fp_b *m fp_b) <> (zero m))).


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


    Definition On_Curve (X1 Y1 Z1 : znz m) := (Y1 *m Y1 *m Z1) = (X1 *m (X1 *m X1) +m fp_a *m X1 *m (Z1 *m Z1) +m fp_b *m (Z1 *m (Z1 *m Z1))) /\ (Z1 = zero m -> Y1 <> zero m).


    Program Definition to_fc_point (X1 Y1 Z1 : znz m) (on_curve : On_Curve X1 Y1 Z1) : fc_proj_point := 
        (X1, Y1, Z1).

    Definition to_fc_point_from_mont X1 Y1 Z1 on_curve := to_fc_point (mkznz _ _ (modz m (evfrom X1))) (mkznz _ _ (modz m (evfrom Y1))) (mkznz _ _ (modz m (evfrom Z1))) on_curve .

    Definition pair_val (p: znz m * znz m * znz m ) : Z*Z*Z := let '(x, y, z) := p in (val m x, val m y, val m z).

    Lemma add_eq: forall x y : znz m, val _ (x +m y) = (val _ x) +' (val _ y).
    Proof. auto. Qed.

    Lemma mul_eq: forall x y : znz m, val _ (x *m y) = (val _ x) *' (val _ y).
    Proof. auto. Qed.

    Lemma sub_eq: forall x y : znz m, val _ (x -m y) = (val _ x) -' (val _ y).
    Proof. auto. Qed.

    Lemma val_eq: forall x H, val m (mkznz m x H) = x.
    Proof. auto. Qed.

    Lemma add_elim_mod: forall x y, x mod m +' y mod m = x +' y.
    Proof. intros. unfold my_add. pull_Zmod. auto. Qed.

    Lemma mul_elim_mod: forall x y, (x mod m) *' (y mod m) = x *' y.
    Proof. intros. unfold my_mul. pull_Zmod. auto. Qed.

    Lemma sub_elim_mod: forall x y, x mod m -' y mod m = x -' y.
    Proof. intros. unfold my_sub. pull_Zmod. auto. Qed.

    Lemma m_small' : m < uw bw n.
    Proof.
            cbv [uw uweight ModOps.weight].
            rewrite Z.div_1_r, Z.opp_involutive.
            pose proof m_small as H. unfold r in H. rewrite Z.pow_mul_r; [auto| pose proof bw_big; lia| pose proof n_nz; lia].
    Qed.

    Lemma eval_list : forall x, x = x mod m -> eval (Partition.partition (uw bw) n x) = x.
    Proof. intros. unfold eval.  rewrite eval_partition; [| apply uwprops, bw_big].
        rewrite Zmod_small; auto.
        assert (x < m) by ( rewrite H; apply Z_mod_lt; lia ).
        pose proof m_small'.
        split; [| lia]. rewrite H. apply Z_mod_lt; pose proof m_big; lia.
    Qed.

    Hint Rewrite add_eq mul_eq sub_eq val_eq add_elim_mod mul_elim_mod sub_elim_mod : znz_to_z_arith.
    Ltac rememberp X1 X2 Y1 Y2 Z1 Z2 := remember (evfrom X1) as x1; remember (evfrom X2) as x2; remember (evfrom Y1) as y1; remember (evfrom Y2) as y2; remember (evfrom Z1) as z1; remember (evfrom Z2) as z2.

    (* Equivalence between gallina and fiat with eq relation *)
    Lemma gallina_fiat_crypto_equiv : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz on_curve1 on_curve2 except, 
        (BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <-> 
        (evfrom outx, evfrom outy, evfrom outz) = pair_val (proj1_sig (fc_proj_add (to_fc_point_from_mont X1 Y1 Z1 on_curve1) (to_fc_point_from_mont X2 Y2 Z2 on_curve2) except))).
    Proof. assert (forall A (x y z: A), y = z -> (x = y <-> x = z)) by ( intros; rewrite H; reflexivity ). 
        intros. apply H. unfold pair_val, fc_proj_add, proj1_sig, to_fc_point_from_mont, to_fc_point.
        rememberp X1 X2 Y1 Y2 Z1 Z2. autorewrite with znz_to_z_arith.
        unfold three_b_list, a_list. rewrite (eval_list _ three_b_small), (eval_list _ a_small) . reflexivity.
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
        apply pair_equal_spec in H. rememberp X1 X2 Y1 Y2 Z1 Z2. 
        destruct H as [H ->]. apply pair_equal_spec in H. destruct H as [-> ->].
        apply pair_equal_spec. split; [apply pair_equal_spec; split |]; apply zirr; autorewrite with znz_to_z_arith; unfold "-'", "+'"; rewrite Zmod_mod; reflexivity.
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
        split; [apply H|]. unfold gallina_spec_from_fc_point, BLS12_add_Gallina_spec.
        destruct p1 as [[[]]]. destruct p2 as [[[]]]. unfold fc_proj_add, proj1_sig, pair_val. 
        repeat rewrite eval_encodemod_val. autorewrite with znz_to_z_arith. 
        unfold three_b_list, a_list. rewrite (eval_list _ three_b_small), (eval_list _ a_small) . reflexivity.
    Qed.
End G1Equiv.

Section G2Equiv.
    Open Scope Z_scope.
    Local Coercion Z.of_nat : nat >-> Z.

    Context (m : Z)
            (bw : Z)
            (n : nat)
            (r' : Z)
            (m' : Z)
            (ar ai : Z)
            (br bi : Z)
            (three_br three_bi : Z)
            (ar_small : ar = ar mod m)
            (ai_small : ai = ai mod m)
            (br_small : br = br mod m)
            (bi_small : bi = bi mod m)
            (three_br_small : three_br = three_br mod m)
            (three_bi_small : three_bi = three_bi mod m)
            (three_br_correct : three_br = br + br + br)
            (three_bi_correct : three_bi = bi + bi + bi).

    Local Notation r := (MontgomeryRingTheory.r bw).

    Context (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bw_big : 0 < bw)
            (n_nz : n <> 0%nat)
            (m_small : m < r ^ (n%nat))
            (m_big : 1 < m)
            (m_mod : m mod 4 = 3)
            (m_prime : prime m)
            (m_odd : 2 < m)
            (twenty1_small : 21 < m).

    Lemma m_mod3 : m mod 4 =? 3 = true.
    Proof. rewrite m_mod. auto. Qed.

    Local Notation eval := (@WordByWordMontgomery.eval bw n).
    Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
    Local Notation evfrom x := (eval (from_mont x)).
    Local Notation valid := (@WordByWordMontgomery.valid bw n m).
    Local Notation uw := (MontgomeryRingTheory.uw bw).

    Local Notation mont_enc := (mont_enc m bw n).
    
    Local Notation BLS12_G2_add_Gallina_spec :=
        (BLS12_G2_add_Gallina_spec m bw n m' ar ai three_br three_bi).

    Local Infix "*p2'" := (my_mulFp2 m) (at level 40).
    Local Infix "+p2'" := (my_addFp2 m) (at level 50).
    Local Infix "-p2'" := (my_subFp2 m) (at level 50).

    Local Infix "*m2" := (mulp2 m) (at level 40).
    Local Infix "+m2" := (addp2 m) (at level 50).
    Local Infix "-m2" := (subp2 m) (at level 50).


    Local Notation Fp2 := (znz m * znz m)%type.
    
    Local Notation fp2_a := (mkznz m ar ar_small, mkznz m ai ai_small).
    Local Notation fp2_b := (mkznz m br br_small, mkznz m bi bi_small).
    Local Notation fp2_3_b := (mkznz m three_br three_br_small, mkznz m three_bi three_bi_small).

    Local Notation FFp2 := ((@FFp2 m) m_prime m_odd m_mod3).

    Definition fp2_fc_field := (Fp2fc m m_prime m_odd m_mod3).
    Definition fp2_char_ge_3 := Char_Fp2_geq_p m m_prime 3 (three_small m n n_nz twenty1_small).
    Definition fp2_char_ge_21 := Char_Fp2_geq_p m m_prime 21 twenty1_small.

    Lemma fc_fp2_dec : DecidableRel (@eq (Fp2)).
    Proof. unfold Decidable. apply eq_dec_Fp2. Qed.

    Local Notation fourp2 := (onep2 m +m2 onep2 m +m2 onep2 m +m2 onep2 m).
    Local Notation twenty7p2 := (fourp2 *m2 fourp2 +m2 fourp2 +m2 fourp2 +m2 onep2 m +m2 onep2 m +m2 onep2 m).

    Context     (fp2_discriminant_nonzero: id((fourp2 *m2 fp2_a *m2 fp2_a *m2 fp2_a +m2 twenty7p2 *m2 fp2_b *m2 fp2_b) <> (zerop2 m))).

    Lemma fp2_3_b_correct : fp2_3_b = (fp2_b +m2 fp2_b) +m2 fp2_b.
    Proof. apply pair_equal_spec; split; apply zirr; cbn; pull_Zmod; [rewrite <- three_br_correct | rewrite <- three_bi_correct]; auto.
    Qed.


    Local Notation fc_proj_p2_point := (@Projective.point Fp2 eq (zerop2 m) (addp2 m) (mulp2 m) fp2_a fp2_b).
    Local Notation fc_proj_p2_add :=  (@Projective.add Fp2 eq (zerop2 m) (onep2 m) (oppp2 m) (addp2 m) (subp2 m) (mulp2 m) (invp2 m) (divp2 m) fp2_a fp2_b fp2_fc_field fp2_char_ge_3 fc_fp2_dec fp2_3_b fp2_3_b_correct fp2_discriminant_nonzero fp2_char_ge_21).
    Local Notation fc_proj_p2_eq := (@Projective.eq Fp2 eq (zerop2 m) (addp2 m) (mulp2 m) fp2_a fp2_b fc_fp2_dec).

    Local Notation encodemod := (WordByWordMontgomery.encodemod bw n m m').

    Local Notation eval_encodemod := (WordByWordMontgomery.eval_encodemod bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Notation encodemod_correct := (WordByWordMontgomery.encodemod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Notation valid_mod := (valid_mod m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).


    Definition On_Curve_p2 (X1 Y1 Z1 : Fp2) := (Y1 *m2 Y1 *m2 Z1) = (X1 *m2 (X1 *m2 X1) +m2 fp2_a *m2 X1 *m2 (Z1 *m2 Z1) +m2 fp2_b *m2 (Z1 *m2 (Z1 *m2 Z1))) /\ (Z1 = zerop2 m -> Y1 <> zerop2 m).

    Program Definition to_fc_p2_point (X1 Y1 Z1 : Fp2) (on_curve : On_Curve_p2 X1 Y1 Z1) : fc_proj_p2_point := 
        (X1, Y1, Z1).

    Local Notation evfrom_pair := (evfrom_pair m bw n m').

    Definition Fp2_from_Z_Z (x: Z*Z) : Fp2 := (mkznz _ _ (modz m (fst x)), mkznz _ _ (modz m (snd x))).

    Definition to_fc_p2_point_from_mont X1 Y1 Z1 on_curve := to_fc_p2_point (Fp2_from_Z_Z (evfrom_pair X1)) (Fp2_from_Z_Z (evfrom_pair Y1)) (Fp2_from_Z_Z (evfrom_pair Z1)) on_curve.

    Local Notation Fp2_to_Z2 := (Fp2_to_Z2 m).
    
    Definition pair_p2_val (x: Fp2*Fp2*Fp2) := let '(x, y, z) := x in (Fp2_to_Z2 x, Fp2_to_Z2 y, Fp2_to_Z2 z).

    Definition pair_mod x := (fst x mod m, snd x mod m).

    (* Some helper lemmas *)
    Local Notation Fp2_add_equiv := (Fp2_add_equiv m).

    Local Notation Fp2_mul_equiv := (Fp2_mul_equiv m n n_nz m_mod).

    Local Notation Fp2_sub_equiv := (Fp2_sub_equiv m).

    Lemma Fp2_to_Z2_eq: forall x, Fp2_to_Z2 (Fp2_from_Z_Z x) = pair_mod x.
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

    Local Notation eval_list := (eval_list m _ _ bw_big n_nz m_small m_big).

    Lemma three_bp2_eq: (eval (three_br_list bw n three_br), eval (three_bi_list bw n three_bi)) = Fp2_to_Z2 fp2_3_b.
    Proof. unfold three_br_list, three_bi_list. repeat rewrite eval_list; auto. 
    Qed.

    Lemma ap2_eq: (eval (ar_list bw n ar), eval (ai_list bw n ai)) = Fp2_to_Z2 fp2_a.
    Proof. unfold ar_list, ai_list. repeat rewrite eval_list; auto. 
    Qed.

    Hint Rewrite three_bp2_eq ap2_eq Fp2_add_equiv Fp2_mul_equiv Fp2_sub_equiv Fp2_to_Z2_eq addp2_elim_mod mulp2_elim_mod subp2_elim_mod : znz2_to_z2_arith.
    Ltac rememberp2 X1 X2 Y1 Y2 Z1 Z2 := remember (evfrom_pair X1) as x1; remember (evfrom_pair X2) as x2; remember (evfrom_pair Y1) as y1; remember (evfrom_pair Y2) as y2; remember (evfrom_pair Z1) as z1; remember (evfrom_pair Z2) as z2.  

    (* Equivalence between gallina and fiat with eq relation *)
    Lemma gallina_fiat_crypto_p2_equiv : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz on_curve1 on_curve2 except, 
        (BLS12_G2_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <-> 
        (evfrom_pair outx, evfrom_pair outy, evfrom_pair outz) = pair_p2_val (proj1_sig (fc_proj_p2_add (to_fc_p2_point_from_mont X1 Y1 Z1 on_curve1) (to_fc_p2_point_from_mont X2 Y2 Z2 on_curve2) except))).
    Proof. assert (forall A (x y z: A), y = z -> (x = y <-> x = z)) by ( intros; rewrite H; reflexivity ). 
        intros. unfold BLS12_G2_add_Gallina_spec, to_fc_p2_point_from_mont.
        apply H. unfold pair_p2_val, fc_proj_p2_add, proj1_sig, to_fc_p2_point. 
        rememberp2 X1 X2 Y1 Y2 Z1 Z2. autorewrite with znz2_to_z2_arith. reflexivity.
    Qed.

    Lemma fc_proj_p2_eq_sig: forall x y, proj1_sig x = proj1_sig y -> fc_proj_p2_eq x y.
    Proof. intros [[[]]] [[[]]] H. cbn. inversion H. destruct (dec (p4 = zerop2 m))eqn:E1; [apply e |].
        split ; reflexivity.
    Qed. 

    Lemma p2_backandforth: forall p, Fp2_from_Z_Z (Fp2_to_Z2 p) = p.
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

    Definition pair_Fp2_to_Z2 x := let '(x, y, z) := x in (Fp2_to_Z2 x, Fp2_to_Z2 y, Fp2_to_Z2 z).

    Definition encodemodp2 x := (encodemod (fst x), encodemod (snd x)).

    Local Notation eval_encodemod_val := (eval_encodemod_val m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
    
    Lemma eval_encodemod_Fp2_to_Z2 : forall v, evfrom_pair (encodemodp2 (Fp2_to_Z2 v)) = (Fp2_to_Z2 v).
    Proof. intros []. apply pair_equal_spec. unfold encodemodp2, Fp2_to_Z2, fst, snd. split; apply eval_encodemod_val.  
    Qed. 

    Definition gallina_G2_spec_from_fc_point (p1 p2 pout : fc_proj_p2_point) := 
        let '(x1, y1, z1) := pair_Fp2_to_Z2 (proj1_sig p1) in
        let '(x2, y2, z2) := pair_Fp2_to_Z2 (proj1_sig p2) in
        let '(outx, outy, outz) := pair_Fp2_to_Z2 (proj1_sig pout) in
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
        split; [apply H|]. unfold gallina_G2_spec_from_fc_point, BLS12_G2_add_Gallina_spec.
        destruct p1 as [[[]]]. destruct p2 as [[[]]]. unfold fc_proj_p2_add, proj1_sig, pair_Fp2_to_Z2. 
        repeat rewrite eval_encodemod_Fp2_to_Z2. autorewrite with znz2_to_z2_arith. reflexivity.
    Qed.

End G2Equiv.
