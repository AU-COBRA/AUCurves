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
  Hypothesis p_mod3: p mod 4 =? 3 = true.

  Lemma p_mod3_eq: p mod 4 = 3.
  Proof. apply Z.eqb_eq, p_mod3. Qed.

  Lemma p_gt_0: 0 < p.
  Proof. lia. Qed.

  Notation "x +p y" := (@F.add p x y) (at level 100).
  Notation "x *p y" := (@F.mul p x y) (at level 90).
  Notation "x -p y" := (@F.sub p x y) (at level 100).
  Notation "x /p y" := (@F.div p x y) (at level 90).
  Notation "n 'zmod' p" := (F.of_Z p n) (at level 90).

  Definition Quad_non_res: F p :=
  if (p mod 4 =? 3) then -1 zmod p
    else ( if (p mod 8 =? 3) then 2 zmod p
      else -2 zmod p ).

  Notation "'β'" := Quad_non_res.

  Ltac discriminate_incongruence H:= repeat
        (try (rewrite Zmod_small, Zmod_small in H; auto with zarith);
        rewrite <- Z_mod_plus_full with (b :=1) in H).

  Lemma Quad_nres_not_zero:
  β <> @F.zero p.
  Proof.
    unfold Quad_non_res, not; intros H. destruct (p mod 4 =? 3).
    - inversion H as [H1]; discriminate_incongruence H1.
    - destruct (p mod 8 =? 3) eqn:case2; inversion H as [H1]; discriminate_incongruence H1.
  Qed.


  Lemma minus_one_odd_power: forall x,
    0 <= x -> (-1)^(2*x + 1) = -1.
  Proof.
    intros x H. rewrite (Z.pow_opp_odd 1 _), Z.pow_1_l; auto with zarith.
    exists x; reflexivity. Qed.

  Lemma beta_is_non_res: (*review proof*)
  ~(exists x, (x *p x) = β).
  Proof.
    intros contra.
    eapply F.sqrt_3mod4_correct in contra.
    pose proof Zmod_small.
    cbv [Quad_non_res] in contra. rewrite p_mod3 in contra.
    eapply (f_equal (fun y => @F.to_Z p y)) in contra.
    rewrite <- F.mod_to_Z in contra.
    rewrite F.to_Z_mul in contra. rewrite Z.mul_mod in contra.
    pose proof (F.mod_to_Z (-1 zmod p)).
    cbv [F.sqrt_3mod4] in contra.
    pose proof PullPush.Z.mod_pow_full.
    rewrite F.to_Z_pow in contra.
    rewrite <- Z.mul_mod in contra.
    rewrite <- Z.mul_mod in contra.
    rewrite Z.mod_mod in contra.
    rewrite <- Z.pow_twice_r in contra.
    rewrite F.to_Z_of_Z in contra.
    rewrite <- PullPush.Z.mod_pow_full in contra.
    rewrite Z.pow_mul_r in contra. assert ( (-1)^ 2 = 1) by auto.
    rewrite H2 in contra. rewrite Z.pow_1_l in contra.
    all: try lia.
    eapply (f_equal (fun y => ((y - (-1 mod p))) mod p)) in contra.
    rewrite Z.sub_diag in contra. rewrite Zmod_0_l in contra.
    rewrite <- Zminus_mod in contra. simpl in contra.
    apply Zmod_divide in contra; try lia.
    destruct contra.
    destruct x.
      - lia.
      - lia.
      - lia. Unshelve. eapply Z.eqb_eq. auto.
  Qed.

  Notation Fp2 := ((F p) * (F p))%type.

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
    - intros H; injection H; intros H'; discriminate_incongruence H'.
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
            - apply Z.eqb_eq in Hx2.
              assert (Hx2z: x2 = @F.zero p).
              { eapply (f_equal (fun y => F.of_Z p y)) in Hx2.
                rewrite F.of_Z_to_Z in Hx2. exact Hx2. }
              assert (Hneq1: x1 <> @F.zero p).
              { intros Hc. apply eq1. rewrite Hc. auto. }
              assert (Hsq: (x1 *p x1) = @F.zero p).
              { rewrite <- contra. rewrite Hx2z. field. }
              exact (ZpZ_integral_domain x1 x1 Hneq1 Hneq1 Hsq).
            - apply beta_is_non_res. exists (x1 /p x2). field_simplify.
              + apply (f_equal (fun z => F.add z ((x2 *p x2) *p β))) in contra.
                replace (x1 *p x1 -p (x2 *p x2) *p β +p (x2 *p x2) *p β) with (x1 *p x1) in contra by field.
                replace (F.zero +p (x2 *p x2) *p β) with ((x2 *p x2) *p β) in contra by field.
                rewrite contra. field.
                intros Hc. apply Z.eqb_neq in Hx2. apply Hx2. rewrite Hc. auto.
              + intros Hc. apply Z.eqb_neq in Hx2. apply Hx2. rewrite Hc. auto.
          }
  Defined.

  Add Field Fp2 : FFp2.


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
