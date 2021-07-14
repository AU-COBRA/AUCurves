Require Import MontgomeryRingTheory.
Require Import Coq.ZArith.ZArith.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Coq.micromega.Lia.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Theory.WordByWordMontgomery.wbw_morphisms.

Section G1Specs.
    Open Scope Z_scope.
    Local Coercion Z.of_nat : nat >-> Z.
    (*Some notation*)
    Context (m : Z)
            (bw : Z)
            (n : nat)
            (r' : Z)
            (m' : Z)
            (a : Z)
            (three_b : Z)
            (a_small : a = a mod m)
            (three_b_small : three_b = three_b mod m).

    Local Notation r := (MontgomeryRingTheory.r bw).

    Context (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bw_big : 0 < bw)
            (n_nz : n <> 0%nat)
            (m_small : m < r ^ (n%nat))
            (m_big : 1 < m).

    Local Notation eval := (@WordByWordMontgomery.eval bw n).
    Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
    Local Notation evfrom x := (eval (from_mont x)).
    Local Notation valid := (@WordByWordMontgomery.valid bw n m).
    Local Notation uw := (MontgomeryRingTheory.uw bw).

    Local Definition from_mont_correct := (WordByWordMontgomery.from_montgomerymod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition to_mont_correct := (WordByWordMontgomery.to_montgomerymod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition add_mod_correct := (WordByWordMontgomery.addmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition sub_mod_correct := (WordByWordMontgomery.submod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition opp_mod_correct := (WordByWordMontgomery.oppmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Definition mul_mod_correct := (WordByWordMontgomery.mulmod_correct bw n m r' m' r'_correct m'_correct bw_big m_big n_nz m_small).
    Local Notation mont_enc := (mont_enc m bw n).

    Definition a_list := Partition.partition uw n a.
    Definition three_b_list := Partition.partition uw n three_b.
    Definition three_b_mont_list := @WordByWordMontgomery.to_montgomerymod bw n m m' three_b_list.
    Definition a_mont_list := @WordByWordMontgomery.to_montgomerymod bw n m m' a_list.

    Lemma three_b_list_valid : valid three_b_list.
    Proof. apply valid_partition_small; try assumption. Qed.

    Lemma three_b_mont_valid : valid three_b_mont_list.
    Proof. apply to_mont_correct, three_b_list_valid. Qed.

    Lemma a_list_valid : valid a_list.
    Proof. apply valid_partition_small; auto. Qed.

    Lemma a_mont_valid : valid a_mont_list.
    Proof. apply to_mont_correct, a_list_valid. Qed.

    Program Definition a_mont : mont_enc := enc_mont m bw n a_mont_list _.
    Next Obligation. apply valid_valid'_equiv; auto. apply a_mont_valid. Defined.

    Program Definition three_b_mont : mont_enc := enc_mont _ _ _ three_b_mont_list _.
    Next Obligation. apply valid_valid'_equiv, three_b_mont_valid; auto. Defined.

    Lemma ev_three_b : eval three_b_list = evfrom (val _ _ _ three_b_mont).
    Proof.
        destruct (to_mont_correct); simpl.
        rewrite <- valid_mod with (r' := r'); auto; [| apply three_b_mont_valid].
        unfold three_b_mont_list. rewrite H; [| apply three_b_list_valid].
        pose proof three_b_list_valid. apply valid_valid'_equiv in H1; auto. destruct H1. rewrite H2.
        auto with zarith.
    Qed.

    Lemma ev_a : eval a_list = evfrom (val _ _ _ a_mont).
    Proof.
        destruct (to_mont_correct); simpl.
        rewrite <- valid_mod with (r' := r'); auto; [| apply a_mont_valid].
        unfold a_mont_list. rewrite H; [| apply a_list_valid].
        pose proof a_list_valid. apply valid_valid'_equiv in H1; auto. destruct H1. rewrite H2.
        auto with zarith.
    Qed.


    Definition my_mul (x y : Z) : Z :=
        (x * y) mod m.

    Definition my_add (x y : Z) : Z :=
        (x + y) mod m.
        
    Definition my_sub (x y : Z) : Z :=
        (x - y) mod m.

    Local Infix "*'" := my_mul (at level 70).
    Local Infix "+'" := my_add (at level 80).
    Local Infix "-'" := my_sub (at level 80).

    Local Infix "*mont" := (mont_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 70).
    Local Infix "+mont" := (mont_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 80).
    Local Infix "-mont" := (mont_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 80).

    Definition BLS12_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
        let X1 := evfrom X1 in
        let Y1 := evfrom Y1 in
        let Z1 := evfrom Z1 in
        let X2 := evfrom X2 in
        let Y2 := evfrom Y2 in
        let Z2 := evfrom Z2 in
        let t0 := X1*'X2 in
        let t1 := Y1*'Y2 in
        let t2 := Z1*'Z2 in
        let t3 := X1+'Y1 in
        let t4 := X2+'Y2 in
        let t3 := t3*'t4 in
        let t4 := t0+'t1 in
        let t3 := t3-'t4 in
        let t4 := X1+'Z1 in
        let t5 := X2+'Z2 in
        let t4 := t4*'t5 in
        let t5 := t0+'t2 in
        let t4 := t4-'t5 in
        let t5 := Y1+'Z1 in
        let X3 := Y2+'Z2 in
        let t5 := t5*'X3 in
        let X3 := t1+'t2 in
        let t5 := t5-'X3 in
        let Z3 := eval a_list*'t4 in
        let X3 := eval three_b_list *'t2 in
        let Z3 := X3+'Z3 in
        let X3 := t1-'Z3 in
        let Z3 := t1+'Z3 in
        let Y3 := X3*'Z3 in
        let t1 := t0+'t0 in
        let t1 := t1+'t0 in
        let t2 := eval a_list*'t2 in
        let t4 := eval three_b_list *'t4 in
        let t1 := t1+'t2 in
        let t2 := t0-'t2 in
        let t2 := eval a_list*'t2 in
        let t4 := t4+'t2 in
        let t0 := t1*'t4 in
        let Y3 := Y3+'t0 in
        let t0 := t5*'t4 in
        let X3 := t3*'X3 in
        let X3 := X3-'t0 in
        let t0 := t3*'t1 in
        let Z3 := t5*'Z3 in
        let Z3 := Z3+'t0 in
        ( eval (from_mont (outx)), eval (from_mont ( outy)), eval (from_mont(outz))) = (X3, Y3, Z3).


    Definition BLS12_add_mont_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
        let t0 := X1 *mont X2 in
        let t1 := Y1 *mont Y2 in
        let t2 := Z1 *mont Z2 in
        let t3 := X1 +mont Y1 in
        let t4 := X2 +mont Y2 in
        let t3 := t3 *mont t4 in
        let t4 := t0+mont t1 in
        let t3 := t3-mont t4 in
        let t4 := X1+mont Z1 in
        let t5 := X2+mont Z2 in
        let t4 := t4*mont t5 in
        let t5 := t0+mont t2 in
        let t4 := t4-mont t5 in
        let t5 := Y1+mont Z1 in
        let X3 := Y2+mont Z2 in
        let t5 := t5*mont X3 in
        let X3 := t1+mont t2 in
        let t5 := t5-mont X3 in
        let Z3 := a_mont *mont t4 in
        let X3 := three_b_mont *mont t2 in
        let Z3 := X3+mont Z3 in
        let X3 := t1-mont Z3 in
        let Z3 := t1+mont Z3 in
        let Y3 := X3*mont Z3 in
        let t1 := t0+mont t0 in
        let t1 := t1+mont t0 in
        let t2 := a_mont *mont t2 in
        let t4 := three_b_mont *mont t4 in
        let t1 := t1+mont t2 in
        let t2 := t0-mont t2 in
        let t2 := a_mont *mont t2 in
        let t4 := t4+mont t2 in
        let t0 := t1*mont t4 in
        let Y3 := Y3+mont t0 in
        let t0 := t5*mont t4 in
        let X3 := t3*mont X3 in
        let X3 := X3-mont t0 in
        let t0 := t3*mont t1 in
        let Z3 := t5*mont Z3 in
        let Z3 := Z3+mont t0 in
        ( outx, outy, outz) = (X3, Y3, Z3).


        Ltac push_mont := repeat progress first
        [ rewrite evfrom_val_add
        | rewrite evfrom_val_sub 
        | rewrite evfrom_val_mul].

        Ltac push_mont_in H := repeat progress first
        [ rewrite evfrom_val_add in H
        | rewrite evfrom_val_sub in H
        | rewrite evfrom_val_mul in H].

    Lemma BLS12_add_specs_equiv : forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz,
        BLS12_add_mont_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <->
            BLS12_add_Gallina_spec (val _ _ _ X1) (val _ _ _ Y1) (val _ _ _ Z1) (val _ _ _ X2) (val _ _ _ Y2) (val _ _ _ Z2) (val _ _ _ outx) (val _ _ _ outy) (val _ _ _ outz).
        Proof.
            split; intros.
                - unfold BLS12_add_Gallina_spec.
                unfold BLS12_add_mont_spec in H.
                apply pair_equal_spec in H; destruct H.
                apply pair_equal_spec in H; destruct H.
                apply (f_equal (fun y => evfrom (val _ _ _ y))) in H, H0, H1.
                destruct outx as [outx Hx], outy as [outy Hy], outz as [outz Hz].
                rewrite !mont_enc_val in H, H0, H1.
                rewrite !mont_enc_val.
                rewrite <- (valid'_mod _ _ _ _ _ r'_correct m'_correct bw_big n_nz m_small m_big Hx) in H.
                rewrite <- (valid'_mod _ _ _ _ _ r'_correct m'_correct bw_big n_nz m_small m_big Hx).
                rewrite <- (valid'_mod _ _ _ _ _ r'_correct m'_correct bw_big n_nz m_small m_big Hy) in H1.
                rewrite <- (valid'_mod _ _ _ _ _ r'_correct m'_correct bw_big n_nz m_small m_big Hy).
                rewrite <- (valid'_mod _ _ _ _ _ r'_correct m'_correct bw_big n_nz m_small m_big Hz) in H0.
                rewrite <- (valid'_mod _ _ _ _ _ r'_correct m'_correct bw_big n_nz m_small m_big Hz).
                push_mont_in H.
                push_mont_in H0; push_mont_in H1.
                rewrite H, H0, H1.
                apply pair_equal_spec; split.
                apply pair_equal_spec; split.
                all: unfold my_mul, my_add, my_sub; pull_Zmod; rewrite ev_three_b; rewrite ev_a; reflexivity.
                - unfold BLS12_add_mont_spec.
                destruct outx as [x Hx], outy as [y Hy], outz as [z Hz].
                rewrite !mont_enc_val in H.
                unfold BLS12_add_Gallina_spec, my_mul, my_add, my_sub in H.
                apply pair_equal_spec in H; destruct H as [H H1].
                apply pair_equal_spec in H; destruct H as [H H0].
                apply pair_equal_spec; split.
                apply pair_equal_spec; split.
                    + apply eval_from_mont_mod_inj with (r' := r') (m' := m'); auto; rewrite mont_enc_val, H. push_mont. pull_Zmod. rewrite ev_three_b. rewrite ev_a. reflexivity.
                    + apply eval_from_mont_mod_inj with (r' := r') (m' := m'); auto; rewrite mont_enc_val, H0. push_mont. pull_Zmod. rewrite ev_three_b. rewrite ev_a. reflexivity.
                    + apply eval_from_mont_mod_inj with (r' := r') (m' := m'); auto; rewrite mont_enc_val, H1. push_mont. pull_Zmod. rewrite ev_three_b. rewrite ev_a. reflexivity.
    Qed.

    Lemma BLS12_add_specs_equiv' : forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz
        (HX1 : valid' _ _ _ X1) (HX2 : valid' _ _ _ X2) (HY1 : valid' _ _ _ Y1) (HY2 : valid' _ _ _ Y2) (HZ1 : valid' _ _ _ Z1) (HZ2 : valid' _ _ _ Z2)
        (Houtx : valid' _ _ _ outx) (Houty : valid' _ _ _ outy) (Houtz : valid' _ _ _ outz),
        BLS12_add_mont_spec (enc_mont _ _ _ X1 HX1) (enc_mont _ _ _ Y1 HY1) (enc_mont _ _ _ Z1 HZ1) (enc_mont _ _ _ X2 HX2) (enc_mont _ _ _ Y2 HY2)
            (enc_mont _ _ _ Z2 HZ2) (enc_mont _ _ _ outx Houtx) (enc_mont _ _ _ outy Houty) (enc_mont _ _ _ outz Houtz) <->
            BLS12_add_Gallina_spec (X1) (Y1) (Z1) (X2) (Y2) (Z2) (outx) (outy) (outz).
    Proof.
        split; intros.
            - apply BLS12_add_specs_equiv in H. rewrite !mont_enc_val in H. auto.
            - apply BLS12_add_specs_equiv. rewrite !mont_enc_val. auto.
    Qed.

End G1Specs.

Section G2Specs.
    Local Open Scope Z_scope.
    Local Coercion Z.of_nat : nat >-> Z.

    Context (m : Z)
            (bw : Z)
            (n : nat)
            (r' : Z)
            (m' : Z)
            (ar ai : Z)
            (three_br three_bi : Z)
            (ar_small : ar = ar mod m)
            (ai_small : ai = ai mod m)
            (three_bi_small : three_bi = three_bi mod m)
            (three_br_small : three_br = three_br mod m).

    Local Notation r := (MontgomeryRingTheory.r bw).

    Context (r'_correct : (r * r') mod m = 1)
            (m'_correct : (m * m') mod r = (-1) mod r)
            (bw_big : 0 < bw)
            (n_nz : n <> 0%nat)
            (m_small : m < r ^ (n%nat))
            (m_big : 1 < m)
            (m_mod : m mod 4 = 3).

    Local Notation eval := (@WordByWordMontgomery.eval bw n).
    Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
    Local Notation evfrom x := (eval (from_mont x)).
    Local Notation valid := (@WordByWordMontgomery.valid bw n m).
    Local Notation uw := (MontgomeryRingTheory.uw bw).

    Local Notation mont_enc := (mont_enc m bw n).

    Definition ar_list := Partition.partition uw n ar.
    Definition ai_list := Partition.partition uw n ai.
    Definition three_br_list := Partition.partition uw n three_br.
    Definition three_br_mont_list := @WordByWordMontgomery.to_montgomerymod bw n m m' three_br_list.
    Definition three_bi_list := Partition.partition uw n three_bi.
    Definition three_bi_mont_list := @WordByWordMontgomery.to_montgomerymod bw n m m' three_bi_list.
    Definition ar_mont_list := @WordByWordMontgomery.to_montgomerymod bw n m m' ar_list.
    Definition ai_mont_list := @WordByWordMontgomery.to_montgomerymod bw n m m' ai_list.

    Definition evfrom_pair x := (evfrom (fst x), evfrom (snd x)).

    Definition three_br_list_valid : valid three_br_list :=
        (three_b_list_valid m bw n three_br three_br_small bw_big n_nz  m_small m_big).
    Definition three_bi_list_valid : valid three_bi_list :=
        (three_b_list_valid m bw n three_bi three_bi_small bw_big n_nz  m_small m_big).

    Definition three_br_mont_valid : valid three_br_mont_list :=
        (three_b_mont_valid m bw n r' m' three_br three_br_small r'_correct m'_correct bw_big n_nz  m_small m_big).
    Definition three_bi_mont_valid : valid three_bi_mont_list :=
        (three_b_mont_valid m bw n r' m' three_bi three_bi_small r'_correct m'_correct bw_big n_nz  m_small m_big).

    Definition ar_list_valid : valid ar_list :=
        (a_list_valid m bw n ar ar_small bw_big n_nz  m_small m_big).
    Definition ai_list_valid : valid ai_list :=
        (a_list_valid m bw n ai ai_small bw_big n_nz  m_small m_big).

    Definition ar_mont_valid : valid ar_mont_list :=
        (a_mont_valid m bw n r' m' ar ar_small r'_correct m'_correct bw_big n_nz  m_small m_big).
    Definition ai_mont_valid : valid ai_mont_list :=
        (a_mont_valid m bw n r' m' ai ai_small r'_correct m'_correct bw_big n_nz  m_small m_big).

    Program Definition ai_mont : mont_enc := enc_mont m bw n ai_mont_list _.
    Next Obligation. apply valid_valid'_equiv; auto. apply ai_mont_valid. Defined.

    Program Definition ar_mont : mont_enc := enc_mont m bw n ar_mont_list _.
    Next Obligation. apply valid_valid'_equiv; auto. apply ar_mont_valid. Defined.

    Program Definition three_bi_mont : mont_enc := enc_mont _ _ _ three_bi_mont_list _.
    Next Obligation. apply valid_valid'_equiv, three_bi_mont_valid; auto. Defined.

    Program Definition three_br_mont : mont_enc := enc_mont _ _ _ three_br_mont_list _.
    Next Obligation. apply valid_valid'_equiv, three_br_mont_valid; auto. Defined.

    Definition ap2 := (ar_mont, ai_mont).
    Definition three_bp2 := (three_br_mont, three_bi_mont).

    Definition val_pair x := (val m bw n (fst x), val m bw n (snd x)).

    Local Lemma fst_val_comm x : fst (val_pair x) = val m bw n (fst x).
    Proof. reflexivity. Qed.

    Local Lemma snd_val_comm x : snd (val_pair x) = val m bw n (snd x).
    Proof. reflexivity. Qed.

    Lemma evfrom_ap2 : ( evfrom_pair (val_pair ap2) = (eval ar_list, eval ai_list)).
    Proof.
        unfold evfrom_pair; rewrite fst_val_comm, snd_val_comm;
        unfold ap2; simpl; unfold ar_mont_list, ai_mont_list.
        rewrite !(from_to_mont_inv m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big);
        [auto| apply ai_list_valid| apply ar_list_valid].
    Qed.

    Lemma evfrom_three_bp2 : ( evfrom_pair (val_pair three_bp2) = (eval three_br_list, eval three_bi_list)).
    Proof.
        unfold evfrom_pair; rewrite fst_val_comm, snd_val_comm;
        unfold three_bp2; simpl; unfold three_br_mont_list, three_bi_mont_list.
        rewrite !(from_to_mont_inv m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big);
        [auto| apply three_bi_list_valid| apply three_br_list_valid].
    Qed.

    Definition my_mulFp2 (x y : (Z * Z)) : (Z * Z) :=
        (
        (fst x * fst y - snd x * snd y) mod m,
        (fst x * snd y + snd x * fst y) mod m
        ).

    Definition my_addFp2 (x y : (Z * Z)) : (Z * Z) :=
    (
        (fst x + fst y) mod m,
        (snd x + snd y) mod m
    ).

    Definition my_subFp2 (x y : (Z * Z)) : (Z * Z) :=
        (
        (fst x - fst y) mod m,
        (snd x - snd y) mod m
        ).

    Definition Fp2_to_Z2 x := (GZnZ.val m (fst x), GZnZ.val m (snd x)).

    Lemma Fp2_add_equiv : forall x y, Fp2_to_Z2 (addp2 m x y) = my_addFp2 (Fp2_to_Z2 x) (Fp2_to_Z2 y).
    Proof. reflexivity. Qed.

    Lemma Fp2_mul_equiv : forall x y, Fp2_to_Z2 (mulp2 m x y) = my_mulFp2 (Fp2_to_Z2 x) (Fp2_to_Z2 y).
    Proof.
        intros; apply pair_equal_spec; simpl; cbv [Quad_non_res]; rewrite m_mod; simpl.
        split; (pull_Zmod; auto with zarith).
    Qed.

    Lemma Fp2_sub_equiv : forall x y, Fp2_to_Z2 (subp2 m x y) = my_subFp2 (Fp2_to_Z2 x) (Fp2_to_Z2 y).
    Proof. reflexivity. Qed.

    Local Infix "*p2'" := my_mulFp2 (at level 70).
    Local Infix "+p2'" := my_addFp2 (at level 80).
    Local Infix "-p2'" := my_subFp2 (at level 80).

    Definition BLS12_G2_add_Gallina_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
        let X1 := evfrom_pair X1 in
        let Y1 := evfrom_pair Y1 in
        let Z1 := evfrom_pair Z1 in
        let X2 := evfrom_pair X2 in
        let Y2 := evfrom_pair Y2 in
        let Z2 := evfrom_pair Z2 in
        let t0 := X1*p2'X2 in
        let t1 := Y1*p2'Y2 in
        let t2 := Z1*p2'Z2 in
        let t3 := X1+p2'Y1 in
        let t4 := X2+p2'Y2 in
        let t3 := t3*p2't4 in
        let t4 := t0+p2't1 in
        let t3 := t3-p2't4 in
        let t4 := X1+p2'Z1 in
        let t5 := X2+p2'Z2 in
        let t4 := t4*p2't5 in
        let t5 := t0+p2't2 in
        let t4 := t4-p2't5 in
        let t5 := Y1+p2'Z1 in
        let X3 := Y2+p2'Z2 in
        let t5 := t5*p2'X3 in
        let X3 := t1+p2't2 in
        let t5 := t5-p2'X3 in
        let Z3 := (eval ar_list, eval ai_list)*p2't4 in
        let X3 := (eval three_br_list, eval three_bi_list) *p2't2 in
        let Z3 := X3+p2'Z3 in
        let X3 := t1-p2'Z3 in
        let Z3 := t1+p2'Z3 in
        let Y3 := X3*p2'Z3 in
        let t1 := t0+p2't0 in
        let t1 := t1+p2't0 in
        let t2 := (eval ar_list, eval ai_list)*p2't2 in
        let t4 := (eval three_br_list, eval three_bi_list) *p2't4 in
        let t1 := t1+p2't2 in
        let t2 := t0-p2't2 in
        let t2 := (eval ar_list, eval ai_list)*p2't2 in
        let t4 := t4+p2't2 in
        let t0 := t1*p2't4 in
        let Y3 := Y3+p2't0 in
        let t0 := t5*p2't4 in
        let X3 := t3*p2'X3 in
        let X3 := X3-p2't0 in
        let t0 := t3*p2't1 in
        let Z3 := t5*p2'Z3 in
        let Z3 := Z3+p2't0 in
        (evfrom_pair outx, evfrom_pair outy, evfrom_pair outz) = (X3, Y3, Z3).

    Local Infix "*montp2" := (montFp2_mul m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 70).
    Local Infix "+montp2" := (montFp2_add m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 80).
    Local Infix "-montp2" := (montFp2_sub m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big) (at level 80).

    Local Notation psip2 := (psiFp2 m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
    Local Notation psi := (psi m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).

    Lemma evfrom_val_pair_mul x y : (evfrom_pair (val_pair (x *montp2 y))) = ((evfrom_pair (val_pair x)) *p2' (evfrom_pair (val_pair y))).
    Proof.
        apply pair_equal_spec; split;
        unfold evfrom_pair; rewrite !Prod.fst_pair, !Prod.snd_pair, !fst_val_comm, !snd_val_comm;
        apply (evfrom_val_mulFp2 m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big x y).
    Qed.

    Lemma evfrom_val_pair_add x y : (evfrom_pair (val_pair (x +montp2 y))) = ((evfrom_pair (val_pair x)) +p2' (evfrom_pair (val_pair y))).
    Proof.
        apply pair_equal_spec; split;
        unfold evfrom_pair; [rewrite !Prod.fst_pair, fst_val_comm| rewrite !Prod.snd_pair, snd_val_comm];
        apply (evfrom_val_addFp2 m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big x y).
    Qed.

    Lemma evfrom_val_pair_sub x y : (evfrom_pair (val_pair (x -montp2 y))) = ((evfrom_pair (val_pair x)) -p2' (evfrom_pair (val_pair y))).
    Proof.
        apply pair_equal_spec; split;
        unfold evfrom_pair; [rewrite !Prod.fst_pair, fst_val_comm| rewrite !Prod.snd_pair, snd_val_comm];
        apply (evfrom_val_subFp2 m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big x y).
    Qed.

    Definition BLS12_G2_add_mont_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz :=
        let t0 := X1 *montp2 X2 in
        let t1 := Y1 *montp2 Y2 in
        let t2 := Z1 *montp2 Z2 in
        let t3 := X1 +montp2 Y1 in
        let t4 := X2 +montp2 Y2 in
        let t3 := t3 *montp2 t4 in
        let t4 := t0+montp2 t1 in
        let t3 := t3-montp2 t4 in
        let t4 := X1+montp2 Z1 in
        let t5 := X2+montp2 Z2 in
        let t4 := t4*montp2 t5 in
        let t5 := t0+montp2 t2 in
        let t4 := t4-montp2 t5 in
        let t5 := Y1+montp2 Z1 in
        let X3 := Y2+montp2 Z2 in
        let t5 := t5*montp2 X3 in
        let X3 := t1+montp2 t2 in
        let t5 := t5-montp2 X3 in
        let Z3 := ap2 *montp2 t4 in
        let X3 := three_bp2 *montp2 t2 in
        let Z3 := X3+montp2 Z3 in
        let X3 := t1-montp2 Z3 in
        let Z3 := t1+montp2 Z3 in
        let Y3 := X3*montp2 Z3 in
        let t1 := t0+montp2 t0 in
        let t1 := t1+montp2 t0 in
        let t2 := ap2 *montp2 t2 in
        let t4 := three_bp2 *montp2 t4 in
        let t1 := t1+montp2 t2 in
        let t2 := t0-montp2 t2 in
        let t2 := ap2 *montp2 t2 in
        let t4 := t4+montp2 t2 in
        let t0 := t1*montp2 t4 in
        let Y3 := Y3+montp2 t0 in
        let t0 := t5*montp2 t4 in
        let X3 := t3*montp2 X3 in
        let X3 := X3-montp2 t0 in
        let t0 := t3*montp2 t1 in
        let Z3 := t5*montp2 Z3 in
        let Z3 := Z3+montp2 t0 in
        ( outx, outy, outz) = (X3, Y3, Z3).

    Local Lemma evfrom_val_pair : forall x y Hx Hy, evfrom_pair (val_pair ({|val := x; Hvalid := Hx|}, {|val := y; Hvalid := Hy|}))
        = evfrom_pair (x, y).
    Proof. auto. Qed.

    Ltac mont_to_Z_in H0 := repeat (first [progress rewrite evfrom_val_pair_add in H0| progress rewrite evfrom_val_pair_sub in H0| rewrite evfrom_val_pair_mul in H0]).
    Ltac mont_to_Z := repeat (first [progress rewrite evfrom_val_pair_add| progress rewrite evfrom_val_pair_sub| rewrite evfrom_val_pair_mul]).
    
    Lemma evfrom_val_pair_inj : forall x y, evfrom_pair (val_pair x) = evfrom_pair (val_pair y) -> x = y.
    Proof.
        intros [xr xi] [yr yi] H. unfold evfrom_pair in H. unfold val_pair in H. apply pair_equal_spec in H. simpl in H. destruct H.
        pose proof (eval_from_mont_inj m bw n r' m' r'_correct m'_correct bw_big n_nz m_small m_big).
        apply H1 in H, H0. apply pair_equal_spec; auto.
    Qed.

    Lemma BLS12_G2_add_specs_equiv : forall X1 Y1 Z1 X2 Y2 Z2 outx outy outz,
    BLS12_G2_add_mont_spec X1 Y1 Z1 X2 Y2 Z2 outx outy outz <->
        BLS12_G2_add_Gallina_spec (val_pair X1) (val_pair Y1) (val_pair Z1) (val_pair X2) (val_pair Y2) (val_pair Z2) (val_pair outx) (val_pair outy) (val_pair outz).
    Proof.
        split; intros.
            - unfold BLS12_G2_add_Gallina_spec.
                unfold BLS12_G2_add_mont_spec in H.
                apply pair_equal_spec in H; destruct H.
                apply pair_equal_spec in H; destruct H.
                apply (f_equal (fun y => evfrom_pair (val_pair y))) in H, H0, H1.
                destruct outx as [[outxr Houtxr] [outxi Houtxi]].
                destruct outy as [[outyr Houtyr] [outyi Houtyi]].
                destruct outz as [[outzr Houtzr] [outzi Houtzi]].
                rewrite !evfrom_val_pair.
                rewrite evfrom_val_pair in H, H0, H1.
                rewrite evfrom_val_pair_add in H0.
                mont_to_Z_in H.
                mont_to_Z_in H0.
                mont_to_Z_in H1.
                rewrite H, H0, H1.
                rewrite evfrom_three_bp2.
                rewrite evfrom_ap2.            
                reflexivity.
            - unfold BLS12_G2_add_mont_spec. unfold BLS12_G2_add_Gallina_spec in H.
                destruct outx as [[xr Hxr] [xi Hxi]], outy as [[yr Hyr] [yi Hyi]], outz as [[zr Hzr] [zi Hzi]].
                apply pair_equal_spec in H. destruct H as [H H0].
                apply pair_equal_spec in H. destruct H as [H H1].
                rewrite <- evfrom_ap2 in H, H0, H1.
                rewrite <- evfrom_three_bp2 in H, H0, H1.
                apply pair_equal_spec; split; [apply pair_equal_spec; split| ]; apply evfrom_val_pair_inj; mont_to_Z; auto.
    Qed.

    Local Notation enc_mont_pair := (enc_mont_pair m bw n).
    Definition valid'_pair x := valid' m bw n (fst x) /\ valid' m bw n (snd x).

    Local Lemma val_pair_enc_pair : forall x Hx, val_pair (enc_mont_pair x Hx) = x.
    Proof. intros [xr xi] [Hxr Hxi]; auto. Qed.

    Lemma BLS12_G2_add_Specs_equiv' : forall X1 X2 Y1 Y2 Z1 Z2 outx outy outz
        (HX1 : valid'_pair X1) (HX2 : valid'_pair X2) (HY1 : valid'_pair Y1) (HY2 : valid'_pair Y2) (HZ1 : valid'_pair Z1) (HZ2 : valid'_pair Z2)
        (Houtx : valid'_pair outx) (Houty : valid'_pair outy) (Houtz : valid'_pair outz),
        BLS12_G2_add_mont_spec (enc_mont_pair X1 HX1) (enc_mont_pair Y1 HY1) (enc_mont_pair Z1 HZ1) (enc_mont_pair X2 HX2) (enc_mont_pair Y2 HY2)
            (enc_mont_pair Z2 HZ2) (enc_mont_pair outx Houtx) (enc_mont_pair outy Houty) (enc_mont_pair outz Houtz) <->
            BLS12_G2_add_Gallina_spec (X1) (Y1) (Z1) (X2) (Y2) (Z2) (outx) (outy) (outz).
    Proof.
        split; intros.
        - apply BLS12_G2_add_specs_equiv in H; rewrite !val_pair_enc_pair in H; auto.
        - apply BLS12_G2_add_specs_equiv; rewrite !val_pair_enc_pair; auto.
    Qed.
End G2Specs.