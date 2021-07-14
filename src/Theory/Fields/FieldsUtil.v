Require Import ZArith Znumtheory.
Require Import Coq.setoid_ring.Field.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Pmod.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Theory.Fields.QuadraticFieldExtensions.
Require Import Znat.
Require Import Lia.
Require Import Theory.Fields.RingsUtil.
Require Import Theory.Util.UList.
Require Import Theory.Util.UListUtil.
Require Import Lists.List.
From Coqprime Require Import List.UList.
From Coqprime Require Import PrimalityTest.IGroup.
From Coqprime Require Import PrimalityTest.EGroup.
From Coqprime Require Import PrimalityTest.FGroup.

(*Relates to specification of a field in the standard library to that of fiatCrypto. *)
Section Fiat.
    Context {F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv}
            {std_field: @field_theory F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv (@eq F)}.

    Add Field F : std_field.

    Instance std_to_fiatCrypto_field : @field F (@eq F) Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv.
    Proof.
        repeat split; try apply (Fdiv_def std_field); try (intros ; field); try apply (_ (std_field)); auto.
        - symmetry; apply (F_1_neq_0 (std_field)).
    Qed.
End Fiat.

(* Characteristic of Prime order fields and their binary extensions. *)
Section Characteristic.

    Variable p : Z.
    Hypothesis p_prime : prime p.
    Notation char_znz_n_ge := (@char_ge (znz p)%type (@eq (znz p)) (zero p) (one p) (opp p) (add p) (sub p) (mul p)).
    Notation ZnZ_of_nat := (@of_nat (znz p) (zero p) (one p) (add p)).
    Notation ZnZ_of_Z := (@of_Z (znz p) (zero p) (one p) (opp p) (add p)).
    Notation inv := GZnZ.inv.

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
            intros m Hm p0 Hp contra;
            unfold of_Z in contra; rewrite of_nat_Fp2 in contra;
            inversion contra; pose proof (@Char_geq_n p (p0 + 1)) as H1; assert (p0 + 1 < p) as H2 by lia;
            apply H1 in H2; assert (ZnZ_of_Z p0 <> zero p) by (apply H2; lia); contradiction. 
        Qed.
    End Fp2.
End Characteristic.

(*Constructs the group of units*)
Section UnitGroup.

    Context {F : Set}
            {Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv}
            {std_field: @field_theory F Fzero Fone Fadd Fmul Fsub Fopp Fdiv Finv (@eq F)}
            {Flist : list F}.

    Hypothesis Flist_unique : ulist Flist.
    Hypothesis Flist_F : forall x, In x Flist.
    Hypothesis Decidable_Feq : forall x y : F, {x = y} + {x <> y}.

    Notation "x * y" := (Fmul x y).
    Notation "x + y" := (Fadd x y).

    Add Field Field : std_field.

    Lemma one_in_Flist : In Fone Flist.
    Proof. auto. Qed.

    Lemma mul_in_Flist : forall x y, In x Flist -> In y Flist -> In (x * y) Flist.
    Proof. auto. Qed.

    Lemma mul_assoc : forall x y z, In x Flist -> In y Flist -> In z Flist -> x * (y * z) = (x * y) * z.
    Proof. intros; field. Qed.

    Lemma mul_1_r : forall x, In x Flist -> Fone * x = x.
    Proof. intros; field. Qed.

    Lemma mul_1_l : forall x, In x Flist -> x * Fone = x.
    Proof. intros; field. Qed.

    Definition Fstar := IGroup F Fmul Flist Fone Decidable_Feq Flist_unique one_in_Flist
    mul_in_Flist mul_assoc mul_1_r mul_1_l.

    Ltac FGroupTac := try (apply mul_assoc || apply mul_1_r || apply mul_1_l ||
                    apply Flist_F || apply mul_in_Flist || apply Flist_unique).

    Lemma Fstar_list_elems : forall x, In x (s Fstar) <-> x <> Fzero.
    Proof.
        split.
        - intros Hx contra; simpl in Hx; unfold isupport in Hx;
        assert (~(In x (isupport_aux F Fmul Flist Fone Decidable_Feq Flist))) as Hzero; try auto.
            + apply isupport_aux_not_in; intros a Ha; right; intros contra2; rewrite contra in contra2;
            simpl in contra2; apply std_field; rewrite <- contra2; field.
        - intros H; simpl; apply isupport_is_in; try FGroupTac; unfold is_inv;
        apply inv_aux_inv with (A := F) (a := Finv x); (FGroupTac; field; auto).
    Qed.

    Lemma Fstar_perm : Permutation.permutation (s Fstar) (remove Decidable_Feq Fzero Flist).
    Proof.
        remember (remove Decidable_Feq Fzero Flist) as lrem eqn:Hlrem.
        apply ulist_incl2_permutation.
            - apply (unique_s Fstar).
            - rewrite Hlrem. apply ulist_rem. FGroupTac.
            - unfold incl. intros a Ha. apply Fstar_list_elems in Ha. rewrite Hlrem.
            apply in_in_remove; auto; FGroupTac.
            - unfold incl; intros a Ha; destruct (Decidable_Feq a Fzero).
            + rewrite Hlrem in Ha; rewrite e in Ha; apply remove_In in Ha; contradiction.
            + apply Fstar_list_elems; auto.
    Qed.

    Lemma Fstar_list_len : length (s Fstar) = Nat.pred (length Flist).
    Proof.
        assert (H : length (s Fstar) = length (remove Decidable_Feq Fzero Flist)) by apply Permutation.permutation_length, Fstar_perm; rewrite H;
        assert (H1 : S (length (remove Decidable_Feq Fzero Flist)) = (length Flist)) by (symmetry; apply ulist_rem_len; FGroupTac);
        apply (f_equal (fun y => Nat.pred y)) in H1; auto.
    Qed.

End UnitGroup.

