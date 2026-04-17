Require Import ZArith Znumtheory.
Require Import Coq.setoid_ring.Field.
From Coqprime Require Import GZnZ.
From Coqprime Require Import Pmod.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Bedrock.Field.FieldExtensions.Theory.QuadraticExtensions.
Require Import Znat.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Lia.
Require Import Crypto.Algebra.Ring.

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
    Context {n : positive}.
    Notation "x + y" := (add n x y).
    Notation "x 'zmod' n" := (F.of_Z n x) (at level 90).
    Notation char_znz_n_ge := (@char_ge (F n)%type (@eq (F n)) (F.zero n) (F.one n) (F.opp n) (F.add n) (F.sub n) (F.mul n)).
    Notation ZnZ_of_Z := (F.of_Z n).
    Notation ZnZ_of_nat := (F.of_nat n).

    Section RZnZ.
        Context {n_pos : 0 < n}.

        Lemma ring_theory : Ring_theory.ring_theory (@F.zero n) F.one F.add F.mul F.sub F.opp eq.
        Proof.
            eapply ring_theory_for_stdlib_tactic.
        Qed.
    
        Add Ring Rn : ring_theory.

        Instance ZnZfc : @ring (F n) (@eq (F n)) (F.zero) (F.one) (F.opp ) (F.add) (F.sub) (F.mul).
        Proof. apply @std_to_fiatCrypto_ring, ring_theory. Qed.

        Lemma of_nat_ZnZ : forall m, ZnZ_of_nat m = ((Z.of_nat m) zmod n).
        Proof.
            intros. induction m as [|m' IHm'].
                - reflexivity.
                - assert ((((Z.of_nat (S m'))) zmod n) = F.add ((Z.of_nat m') zmod n) (F.one)) as H0.
                    {
                        assert (F.of_Z n 1 = 1%F) by auto;
                        rewrite <- H; rewrite <- F.of_Z_add; apply f_equal; lia.
                    }
                rewrite H0; simpl. rewrite <- IHm'. auto.
        Qed.

        Lemma of_Z_ZnZ : forall m, ZnZ_of_Z m = (m zmod n).
        Proof.
            auto.
        Qed.
            
        (*revisit if needed*)
        (* Lemma Char_geq_n :forall (m : positive), m < n ->
        (@char_ge (F n)%type (@eq (F n)) (@F.zero n) (@F.one n) (F.opp ) (F.add ) (F.sub ) (F.mul )) m.
        Proof.
            unfold char_ge, Hierarchy.char_ge.
            intros m H p Hp; simpl.
            remember (Pos.to_nat p) as pnat eqn:Hp'. induction (pnat) as [| p' IHp'].
            - apply (f_equal (fun y => Z.of_nat y)) in Hp';
            rewrite positive_nat_Z in Hp'; discriminate.
            - assert (Z.of_nat (S p') < n) as H0 by lia. intros contra.
              simpl in contra.
              eapply (f_equal (fun y => F.to_Z y)) in contra.
              simpl in contra.
              rewrite (Zmod_small 1 _) in contra; try lia.
              rewrite (Zmod_small 0 _) in contra; try lia.
              Search (_ mod _ = 0).
              epose proof (Div.Z.div_positive_gt_0 _ _ _ _ contra ).

              rewrite Zmod_small in contra.
              2: {
                  eassert ( forall n', F.to_Z (of_nat n') = _).
                  2: {
                      split.
                      1: {
                        Set Printing All.
                      }
                  }
                  {
                      intros. Search of_nat. assert (exists p, n' = Pos.to_nat p).
                        {
                            induction n'; eexists.
                                
                        }
                  }
                  split; try lia. 
              }
              rewrite Zmod_small; [| split; try lia]. split; try lia.

              }

              erewrite F.of_Z_add in contra.
              Search (of_nat).
              pose proof of_nat_ZnZ. cbv [ZnZ_of_nat ZnZ_of_Z] in H1.
            rewrite of_nat_ZnZ in contra. intros contra.
            assert (Z.of_nat (S p') mod n = Z.of_nat (S p')) as H2 by (apply Zmod_small; lia).
            inversion contra as [H3]; rewrite Zmod_0_l in H3; simpl in H0; lia.
        Qed. *)
    End RZnZ.

    Section Field.

        Notation p := n.
        Hypothesis p_prime : prime p.

        Instance ZpZfc : @field (znz p) (@eq (znz p)) (zero p) (one p) (opp p) (add p) (sub p) (mul p) (inv p) (div p).
        Proof. apply @std_to_fiatCrypto_field, FZpZ; apply p_prime. Qed.

        Section FZpZ.

            (* Lemma Char_geq_p : forall (m : positive), m < p -> char_znz_n_ge m.
            Proof. apply Char_geq_n. Qed. *)

        End FZpZ.

        Section Fp2.
        
            Hypothesis p_odd: 2 < p.
            Variable beta : F p.
            Hypothesis beta_nz : beta <> @F.zero p.
            Hypothesis beta_qnr : ~(exists x, @F.mul p x x = beta).
            Add Field Fp2 : (FFp2 p p_prime p_odd beta beta_nz beta_qnr).
            Add Field Fp : (FZpZ p p_prime).

            Notation char_Fp2_p_ge := (@char_ge (znz p * znz p)%type (@eq (znz p * znz p)) (zerop2 p) (onep2 p) (oppp2 p) (addp2 p) (subp2 p) (mulp2 p)).
            
            (* Instance Fp2fc : @field (znz p * znz p) (@eq (znz p * znz p)) (zerop2 p)
                (onep2 p) (oppp2 p) (addp2 p) (subp2 p) (mulp2 p) (invp2 p) (divp2 p).
            Proof. apply @std_to_fiatCrypto_field, (FFp2 p p_prime p_odd beta beta_nz beta_qnr). Qed.

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
            Qed. *)

        End Fp2.

    End Field.

End Characteristic.