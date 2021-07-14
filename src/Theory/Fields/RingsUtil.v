Require Import ZArith Znumtheory.
Require Import Coq.setoid_ring.Field.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Pmod.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Znat.
Require Import Lia.

(*Relates the specification of a ring in the standard library to that of fiatCrypto. *)
Section Ring.
    Context {R Rzero Rone Radd Rmul Rsub Ropp}
            {std_ring: @ring_theory R Rzero Rone Radd Rmul Rsub Ropp (@eq R)}.

    Add Ring R : std_ring.

    Instance std_to_fiatCrypto_ring : @ring R (@eq R) Rzero Rone Ropp Radd Rsub Rmul.
    Proof. repeat split; try (intros; ring); try apply (_ (std_ring)). Qed.


End Ring.

(*Relates to specification of a field in the standard library to that of fiatCrypto. *)
Section Field.
    Context {F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv}
            {std_field: @field_theory F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv (@eq F)}.

    Add Field F : std_field.

    Instance std_to_fiatCrypto_field : @field F (@eq F) Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv.
    Proof.
        repeat split; try apply (Fdiv_def std_field); try (intros ; field); try apply (_ (std_field)); auto.
        - symmetry; apply (F_1_neq_0 (std_field)).
    Qed.
End Field.


(* Few elementary results on the characteristics of prime order fields and their binary extensions. *)
Section Characteristic.

    Context {n : Z}.
    Notation "x + y" := (add n x y).
    Notation "x 'zmod' n" := (mkznz n (x mod n) (modz n x)) (at level 90).
    Notation char_znz_n_ge := (@char_ge (znz n)%type (@eq (znz n)) (zero n) (one n) (opp n) (add n) (sub n) (mul n)).
    Notation ZnZ_of_Z := (@of_Z (znz n) (zero n) (one n) (opp n) (add n)). 
    Notation ZnZ_of_nat := (@of_nat (znz n) (zero n) (one n) (add n)).

    Section RZnZ.

        Context {n_pos: 0 < n}.

        Add Ring Zn : (RZnZ n n_pos).
        Notation ZnZ := (RZnZ n n_pos).

        Instance ZnZfc : @ring (znz n) (@eq (znz n)) (zero n) (one n) (opp n) (add n) (sub n) (mul n).
        Proof. apply @std_to_fiatCrypto_ring, ZnZ. Qed.

        Lemma of_nat_ZnZ : forall m, ZnZ_of_nat m = ((Z.of_nat m) zmod n).
        Proof.
            intros. induction m as [|m' IHm'].
                - reflexivity.
                - assert (((Z.of_nat (S m')) zmod n) = add n (Z.of_nat m' zmod n) (one n)) as H0 by
                (apply zirr; simpl; rewrite <- Zplus_mod; lia).
                rewrite H0; simpl; apply zirr; rewrite IHm'; reflexivity.
        Qed.


        Lemma of_Z_ZnZ : forall m, ZnZ_of_Z m = (m zmod n).
        Proof.
            intros m. destruct m.
                - reflexivity.
                - simpl; rewrite of_nat_ZnZ, positive_nat_Z; reflexivity.
                - simpl. rewrite of_nat_ZnZ, positive_nat_Z. unfold opp. apply zirr. simpl.
                assert (Z.neg p = -1 * p) by lia. rewrite H. rewrite Zmult_mod.
                assert (- (p mod n) = -1 * (p mod n)) by lia. rewrite H0. rewrite Zmult_mod.
                rewrite Zmod_mod. reflexivity.
        Qed.

        
        Lemma Char_geq_n :forall (m : positive), m < n ->
        char_znz_n_ge m.
        Proof.
            unfold char_ge, Hierarchy.char_ge.
            intros m H p Hp; simpl.
            remember (Pos.to_nat p) as pnat eqn:Hp'. induction (pnat) as [| p' IHp'].
            - apply (f_equal (fun y => Z.of_nat y)) in Hp';
            rewrite positive_nat_Z in Hp'; discriminate.
            - assert (Z.of_nat (S p') < n) as H0 by lia; rewrite of_nat_ZnZ; intros contra.
            assert (Z.of_nat (S p') mod n = Z.of_nat (S p')) as H2 by (apply Zmod_small; lia).
            inversion contra as [H3]; rewrite Zmod_0_l in H3; simpl in H0; lia.
        Qed.
    End RZnZ.

    Section Field.

        Notation p := n.
        Hypothesis p_prime : prime p.

        Instance ZpZfc : @field (znz p) (@eq (znz p)) (zero p) (one p) (opp p) (add p) (sub p) (mul p) (inv p) (div p).
        Proof. apply @std_to_fiatCrypto_field, FZpZ; apply p_prime. Qed.

        Section FZpZ.

            Lemma Char_geq_p : forall (m : positive), m < p -> char_znz_n_ge m.
            Proof. apply Char_geq_n. Qed.

        End FZpZ.

        Section Fp2.
        
            Hypothesis p_odd: 2 < p.
            Hypothesis p_mod: (p mod 4 =? 3) = true.
            Add Field Fp2 : (FFp2 p p_prime p_odd p_mod).
            Add Field Fp : (FZpZ p p_prime).

            Notation char_Fp2_p_ge := (@char_ge (znz p * znz p)%type (@eq (znz p * znz p)) (zerop2 p) (onep2 p) (oppp2 p) (addp2 p) (subp2 p) (mulp2 p)).
            
            Instance Fp2fc : @field (znz p * znz p) (@eq (znz p * znz p)) (zerop2 p)
                (onep2 p) (oppp2 p) (addp2 p) (subp2 p) (mulp2 p) (invp2 p) (divp2 p).
            Proof. apply @std_to_fiatCrypto_field, (FFp2 p p_prime p_odd p_mod). Qed.

            Notation Fp2_of_nat := (@of_nat (znz p * znz p) (zerop2 p) (onep2 p) (addp2 p)).

            Lemma of_nat_Fp2 : forall m, (Fp2_of_nat m) = (ZnZ_of_nat m, zero p).
            Proof. intros; induction m as [| m IHm]; try reflexivity;
                simpl; rewrite IHm; rewrite of_nat_ZnZ; apply Fp2irr; simpl; field.
            Qed.  

            Theorem Char_Fp2_geq_p : forall (m : positive), m < p -> char_Fp2_p_ge m.
            Proof. 
                intros m Hm p Hp contra; unfold of_Z in contra; rewrite of_nat_Fp2 in contra;
                inversion contra; pose proof Char_geq_n (p + 1) as H1; assert (p + 1 < Field.p) as H2 by lia;
                apply H1 in H2; assert (ZnZ_of_Z p <> zero Field.p) by (apply H2; lia); contradiction. 
            Qed.

        End Fp2.

    End Field.

End Characteristic.
