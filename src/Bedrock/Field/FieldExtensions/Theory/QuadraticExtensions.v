(*move elsewhere?*)
From Coq Require Import ZArith Znumtheory.
From Coq Require Import Eqdep_dec.
From Coq Require Import List.
From Coq Require Import Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
From Coq Require Import Field.
(* From Coqprime Require Import Euler.
From Coqprime Require Import UList. *)
Require Import Coqprime.elliptic.GZnZ.
From Coqprime Require Import Zp.
From Coqprime Require Import Pmod.
(*From QuickChick Require Import QuickChick.
Import QcNotation.*)
Require Import Zpow_facts.
Require Import Znat.

Section Fp2.

  Variable p: positive.
  Hypothesis p_prime: prime p.
  Hypothesis p_odd: 2 < p.

  (* β is an explicit quadratic non-residue in Fp.
     For BLS12-381: β = F.of_Z p (-1) (since p ≡ 3 mod 4).
     For BLS12-377: β = F.of_Z p (-5) (since p ≡ 1 mod 8). *)
  Variable Quad_non_res : F p.
  Hypothesis Quad_nres_not_zero : Quad_non_res <> @F.zero p.
  Hypothesis beta_is_non_res : ~(exists x, @F.mul p x x = Quad_non_res).

  Lemma p_gt_0: 0 < p.
  Proof. lia. Qed.

  Notation "x +p y" := (@F.add p x y) (at level 100).
  Notation "x *p y" := (@F.mul p x y) (at level 90).
  Notation "x -p y" := (@F.sub p x y) (at level 100).
  Notation "x /p y" := (@F.div p x y) (at level 90).
  Notation "n 'zmod' p" := (F.of_Z p n) (at level 90).

  Notation "'β'" := Quad_non_res.

  Notation Fp2 := ((F p) * (F p))%type.

  Theorem Firr : forall x y, @F.to_Z p x = F.to_Z y -> x = y.
  Proof.
    intros. apply (f_equal (fun y => @F.of_Z p y)) in H.
    do 2 rewrite F.of_Z_to_Z in H. auto.
  Qed.

  Theorem Fp2irr : forall (x1 x2 y1 y2 : F p),
    x1 = y1 -> x2 = y2 -> (x1, x2) = (y1, y2).
  Proof. intros x1 x2 y1 y2 H1 H2; subst x1 x2; reflexivity. Qed. 

  (* Defining Ring Structure of Fp2 *)

  Definition zerop2 : Fp2 := (@F.zero p, @F.zero p).

  Definition onep2 : Fp2 := (@F.one p, @F.zero p).

  Definition addp2 (x1 x2 : Fp2) : Fp2 :=
    ( fst x1 +p fst x2, snd x1 +p snd x2).

  Definition subp2 (x1 x2 : Fp2) : Fp2 :=
    (fst x1 -p fst x2, snd x1 -p snd x2).

  Definition mulp2 (x1 x2 : Fp2) :  Fp2 :=
    (fst x1 *p fst x2 +p β *p snd x1 *p snd x2,
      fst x1 *p snd x2 +p snd x1 *p fst x2).

  Definition oppp2 (x : Fp2) : Fp2 := (@F.opp p (fst x), @F.opp p (snd x)).

  Definition of_Zp2 (x : Z) := (@F.zero p, @F.of_Z p x).

  Add Field F : field_theory_for_stdlib_tactic.

  Definition RFp2: ring_theory zerop2
    onep2 addp2 mulp2 subp2 oppp2 (@eq Fp2).
  Proof.
    split; intros; case x; intros; refine (Fp2irr _ _ _ _ _ _); simpl; field.
  Qed.

  Definition Zerop2_iff: forall x,
    x = zerop2 <-> ( fst x = F.zero /\ snd x = F.zero ).
  Proof.
    intros [x1 x2]; split.
    - intros H; inversion H; split; reflexivity.
    - intros H; simpl in H; destruct H as [H1 H2]; rewrite H1, H2; reflexivity.
  Qed.

  Definition Zerop_iff: forall x,
    x = (@F.zero p) <-> x = F.of_Z p 0.
    intros; split; auto.
  Qed.

  Lemma Zerop_iff': forall x,
  F.to_Z x = 0 <-> x = F.of_Z p 0.
  intros; split; intros; subst; auto. eapply (f_equal (fun y => F.of_Z p y)) in H.
  rewrite <- H. rewrite F.of_Z_to_Z. auto.
  Qed.

  Definition ZpZ_integral_domain: forall x y,
    x <> F.zero -> y <> F.zero -> (x *p y) <> F.zero.
  Proof.
    intros x y Hx Hy contra. 
    assert ((F.one *p F.one) = F.zero) as H by (
      assert ((x *p y *p F.inv x *p F.inv y) = F.zero) as H0 by
      (rewrite contra; field; split; assumption);
      rewrite <- H0; field; split; assumption).
      apply field_theory_for_stdlib_tactic; rewrite <- H; field.
  Qed.

  (* Definining additional field structure *)

  Definition invp2 (x : Fp2) : Fp2 :=
  if (F.to_Z (fst x) =? 0) then  (F.zero, F.inv (snd x *p β))
    else
      ( F.one /p fst x +p ( (snd x *p snd x *p β /p (fst x *p fst x)) *p F.inv (fst x -p ( snd x *p snd x *p β /p fst x)) ), 
        F.opp ((snd x /p fst x) /p ( fst x -p snd x *p snd x *p β /p fst x ))).

  Definition divp2 (x1 x2 : Fp2) : Fp2 := mulp2 x1 (invp2 x2).

  Definition FFp2: field_theory zerop2 onep2 addp2 mulp2
    subp2 oppp2 divp2 invp2 (@eq (F p * F p)).
    split.
    - apply RFp2.
    - intros H. apply (f_equal fst) in H. simpl in H.
      apply (f_equal F.to_Z) in H. rewrite (@F.to_Z_1 _ p_odd), F.to_Z_0 in H. lia.
    - reflexivity.
    - intros [x1 x2] H. unfold invp2, mulp2, onep2. repeat rewrite Prod.fst_pair. repeat rewrite Prod.snd_pair. destruct (F.to_Z x1 =? 0) eqn:eq1.
      (*Case : x1 is zero*)
      + rewrite Prod.fst_pair. rewrite Prod.snd_pair. apply Z.eqb_eq in eq1; refine (Fp2irr _ _ _ _ _ _).
        * field. split; [apply Quad_nres_not_zero| ].
          unfold not. intros. eapply (f_equal (fun y => F.of_Z p y)) in eq1.
          rewrite F.of_Z_to_Z in eq1. apply H. subst. auto.
        * eapply (f_equal (fun y => F.of_Z p y)) in eq1.
          rewrite F.of_Z_to_Z in eq1. subst.
          assert (Hmul0r : forall x, (0 *p x) = 0%F) by (intros; field).
          rewrite Hmul0r.
          assert (Hmul0l : forall x, (x *p 0) = 0%F) by (intros; field).
          rewrite Hmul0l. field.
      (* Case : x1 is not zero *)
      + apply Z.eqb_neq in eq1; refine (Fp2irr _ _ _ _ _ _); rewrite Prod.fst_pair, Prod.snd_pair.
        * destruct (F.to_Z x2 =? 0) eqn:eq2.
            (* case x2 is zero *)
            {
              apply Z.eqb_eq in eq2. apply Zerop_iff' in eq2. rewrite eq2.
              assert ((0 zmod p) = 0%F) as Hzero by auto. rewrite Hzero. field.
              intros contra. apply eq1. rewrite contra. auto.
            }
            (* case x2 is not zero *)
            {
              field. split.
              - intros contra. apply eq1. rewrite contra. auto.
              - intros contra. exfalso. apply beta_is_non_res.
                exists (x1 /p x2). field_simplify.
                + apply (f_equal (fun z => F.add z ((x2 *p x2) *p β))) in contra.
                  replace (x1 *p x1 -p (x2 *p x2) *p β +p (x2 *p x2) *p β) with (x1 *p x1) in contra by field.
                  replace (F.zero +p (x2 *p x2) *p β) with ((x2 *p x2) *p β) in contra by field.
                  rewrite contra. field.
                  intros Hc. apply Z.eqb_neq in eq2. apply eq2. rewrite Hc. auto.
                + intros Hc. apply Z.eqb_neq in eq2. apply eq2. rewrite Hc. auto.
            }
        * field. split.
          { intros contra. apply eq1. rewrite contra. auto. }
          { intros contra. exfalso.
            destruct (F.to_Z x2 =? 0) eqn:Hx2.
            - (* x2 = 0: x1² = 0, contradicts x1 ≠ 0 via integral domain *)
              apply Z.eqb_eq in Hx2.
              assert (Hx2z: x2 = @F.zero p).
              { eapply (f_equal (fun y => F.of_Z p y)) in Hx2.
                rewrite F.of_Z_to_Z in Hx2. exact Hx2. }
              assert (Hneq1: x1 <> @F.zero p).
              { intros Hc. apply eq1. rewrite Hc. auto. }
              assert (Hsq: (x1 *p x1) = @F.zero p).
              { rewrite <- contra. rewrite Hx2z. field. }
              exact (ZpZ_integral_domain x1 x1 Hneq1 Hneq1 Hsq).
            - (* x2 ≠ 0: (x1/x2)² = β contradicts non-residue *)
              apply beta_is_non_res. exists (x1 /p x2). field_simplify.
              + apply (f_equal (fun z => F.add z ((x2 *p x2) *p β))) in contra.
                replace (x1 *p x1 -p (x2 *p x2) *p β +p (x2 *p x2) *p β) with (x1 *p x1) in contra by field.
                replace (F.zero +p (x2 *p x2) *p β) with ((x2 *p x2) *p β) in contra by field.
                rewrite contra. field.
                intros Hc. apply Z.eqb_neq in Hx2. apply Hx2. rewrite Hc. auto.
              + intros Hc. apply Z.eqb_neq in Hx2. apply Hx2. rewrite Hc. auto.
          }
  Defined.

  Add Field Fp2 : FFp2.
  Require Import Crypto.Util.ZUtil.Tactics.PullPush.Modulo.

  (*Few auxilliary lemmas that are used in proving correctness of Bedrock2 implementations*)
  Lemma F_mul_assoc : forall x y z, ((x *p y) *p z) = (x *p (y *p z)).
  Proof.
    intros; field.  
  Qed.


  (* mul_neg_1 and invp2_plus_norm were removed from the generic theory.
     They assumed β = -1 (p ≡ 3 mod 4). For BLS12-381 compatibility,
     these are now proved in CubicFieldExtensions.v as bridge lemmas.
     For general β, use mulp2/invp2 directly. *)

  (* Generic norm formula: norm(a0, a1) = a0² - β·a1² *)
  Definition normp2 (x : Fp2) : F p :=
    fst x *p fst x -p β *p snd x *p snd x.

  (* The generic inverse formula: inv(a0, a1) = (a0/N, -a1/N) where N = a0² - β·a1².
     This is the standard formula for arbitrary β. *)
  Lemma invp2_generic_norm : forall a0 a1,
    invp2 (a0, a1) = (a0 *p F.inv (normp2 (a0, a1)),
                       F.opp a1 *p F.inv (normp2 (a0, a1))).
  Proof.
    (* Helper tactic for norm ≠ 0 side condition *)
    assert (norm_nz : forall a0 a1 : F p, a0 <> F.zero ->
      (a0 *p a0 -p (β *p a1) *p a1) <> F.zero).
    { intros a0' a1' Hane' Hnorm'.
      destruct (F.to_Z a1' =? 0) eqn:Ha1'.
      - apply Z.eqb_eq in Ha1'.
        assert (Ha1z : a1' = F.zero)
          by (eapply (f_equal (fun y => F.of_Z p y)) in Ha1'; rewrite F.of_Z_to_Z in Ha1'; exact Ha1').
        subst a1'. assert (Hsq : (a0' *p a0') = F.zero) by (rewrite <- Hnorm'; ring).
        exact (ZpZ_integral_domain a0' a0' Hane' Hane' Hsq).
      - apply Z.eqb_neq in Ha1'.
        assert (Ha1ne : a1' <> F.zero)
          by (intro Heq; subst a1'; apply Ha1'; rewrite F.to_Z_0; reflexivity).
        apply beta_is_non_res. exists (a0' /p a1'). field_simplify; [| exact Ha1ne].
        apply (f_equal (fun z => F.add z ((β *p a1') *p a1'))) in Hnorm'.
        replace (a0' *p a0' -p (β *p a1') *p a1' +p (β *p a1') *p a1') with (a0' *p a0') in Hnorm' by field.
        replace (F.zero +p (β *p a1') *p a1') with ((β *p a1') *p a1') in Hnorm' by field.
        rewrite Hnorm'. field. exact Ha1ne. }
    intros a0 a1.
    destruct (F.to_Z a0 =? 0) eqn:Ha.
    - (* a0 = 0 *)
      apply Z.eqb_eq in Ha.
      assert (Ha0 : a0 = F.zero) by (apply F.eq_to_Z_iff; rewrite F.to_Z_0; exact Ha).
      subst a0.
      replace (invp2 (F.zero, a1)) with (@F.zero p, @F.inv p (a1 *p β))
        by (unfold invp2; simpl fst; rewrite Z.eqb_refl; reflexivity).
      unfold normp2. cbv [fst snd].
      destruct (F.eq_dec a1 F.zero) as [Ha1z | Ha1nz].
      + subst a1.
        replace (0 *p β) with (@F.zero p) by ring.
        replace (0 *p 0 -p (β *p 0) *p 0) with (@F.zero p) by ring.
        rewrite !(F.inv_0 p). reflexivity.
      + apply Fp2irr.
        * field.
          intro H.
          pose proof (ZpZ_integral_domain β a1 Quad_nres_not_zero Ha1nz) as Hba.
          pose proof (ZpZ_integral_domain (β *p a1) a1 Hba Ha1nz) as Hba2.
          apply Hba2. replace ((β *p a1) *p a1) with (F.opp (F.opp ((β *p a1) *p a1))) by ring.
          rewrite H. ring.
        * field. split; [| split; assumption].
          intro H.
          pose proof (ZpZ_integral_domain β a1 Quad_nres_not_zero Ha1nz) as Hba.
          pose proof (ZpZ_integral_domain (β *p a1) a1 Hba Ha1nz) as Hba2.
          apply Hba2. replace ((β *p a1) *p a1) with (F.opp (F.opp ((β *p a1) *p a1))) by ring.
          rewrite H. ring.
    - (* a0 ≠ 0 *)
      apply Z.eqb_neq in Ha.
      assert (Hane : a0 <> F.zero) by (intro Heq; subst a0; apply Ha; rewrite F.to_Z_0; reflexivity).
      unfold invp2. simpl fst.
      replace (F.to_Z a0 =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha).
      simpl snd at 1.
      unfold normp2. cbv [fst snd].
      apply Fp2irr.
      + field. split; [exact (norm_nz a0 a1 Hane) | exact Hane].
      + field. split; [exact (norm_nz a0 a1 Hane) | exact Hane].
  Qed.

  (* Former invp2_plus_norm for β = -1 is a special case where normp2 = a0² + a1². *)

  Lemma mul_equiv : forall a b c d, ((((c +p d) *p (a +p b)) -p (a *p c)) -p (b *p d)) = ((a *p d) +p (b *p c)).
  Proof.
    intros; field.
  Qed.


  (*Verify that Fp2 is a finite field of order p*p by producing a ulist of its elements of length p * p *)

  (* Definition all_Fp2 := List.list_prod (all_znz p p_gt_0) (all_znz p p_gt_0).

  Lemma in_all_Fp2 : forall x, List.In x all_Fp2.
  Proof. intros x; case x; intros; apply List.in_prod; apply in_all_znz. Qed.

  Lemma Fp2_list_unique : ulist all_Fp2.
  Proof. apply ulist_list_prod; apply uniq_all_znz. Qed.

  Lemma all_Fp2_length : (length all_Fp2) = Z.abs_nat(p * p).
  Proof.
    unfold all_Fp2; rewrite List.prod_length, all_znz_length, Zabs2Nat.inj_mul; auto.
  Qed. *)

  (*Fp2 has decidable equality*)

  Lemma eq_dec_Fp2 : forall x y : (Fp2), {x = y} + {x <> y}.
  intros x y. case x as [x1 x2]. case y as [y1 y2].
  destruct ((F.to_Z x1) =? (F.to_Z y1)) eqn:H1.
    - destruct ((F.to_Z x2 =? F.to_Z y2)) eqn: H2.
      + left. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2.
        eapply (f_equal (fun y => F.of_Z p y)) in H1, H2. repeat rewrite F.of_Z_to_Z in H1, H2; auto. auto.
        apply Prod.path_pair; auto.
      + right; apply Z.eqb_neq in H2; intros contra; apply pair_equal_spec in contra; destruct contra as [_ H0]; apply H2; inversion H0; auto.
    - right; apply Z.eqb_neq in H1; intros contra; apply pair_equal_spec in contra; destruct contra as [H _]; apply H1; rewrite H; auto.
  Qed.

End Fp2.
