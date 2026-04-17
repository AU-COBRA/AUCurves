(* Generic quadratic extension Fp2 = Fp[u]/(u² - β) for arbitrary QNR β.
   The existing QuadraticExtensions.v hardcodes β computation from p mod 4/8,
   which fails for primes with p ≡ 1 (mod 8) (like BLS12-377).

   This file parameterizes over β directly, requiring only that β is a QNR. *)

From Coq Require Import ZArith Znumtheory.
From Coq Require Import List Lia.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
From Coq Require Import Field.
Require Import Coqprime.elliptic.GZnZ.

Section Fp2Generic.

  Variable p : positive.
  Hypothesis p_prime : prime p.
  Hypothesis p_odd : 2 < p.

  (* β is an explicit quadratic non-residue *)
  Variable beta : F p.
  Hypothesis beta_nonzero : beta <> @F.zero p.
  Hypothesis beta_is_QNR : ~(exists x : F p, @F.mul p x x = beta).

  Notation "x +p y" := (@F.add p x y) (at level 100).
  Notation "x *p y" := (@F.mul p x y) (at level 90).
  Notation "x -p y" := (@F.sub p x y) (at level 100).
  Notation "x /p y" := (@F.div p x y) (at level 90).

  Notation Fp2 := ((F p) * (F p))%type.

  Definition zerop2 : Fp2 := (@F.zero p, @F.zero p).
  Definition onep2 : Fp2 := (@F.one p, @F.zero p).

  Definition addp2 (x1 x2 : Fp2) : Fp2 :=
    (fst x1 +p fst x2, snd x1 +p snd x2).

  Definition subp2 (x1 x2 : Fp2) : Fp2 :=
    (fst x1 -p fst x2, snd x1 -p snd x2).

  (* (a + bu)(c + du) = (ac + β·bd) + (ad + bc)u *)
  Definition mulp2 (x1 x2 : Fp2) : Fp2 :=
    (fst x1 *p fst x2 +p beta *p snd x1 *p snd x2,
     fst x1 *p snd x2 +p snd x1 *p fst x2).

  Definition oppp2 (x : Fp2) : Fp2 := (@F.opp p (fst x), @F.opp p (snd x)).

  Theorem Fp2irr : forall (x1 x2 y1 y2 : F p),
    x1 = y1 -> x2 = y2 -> (x1, x2) = (y1, y2).
  Proof. intros; subst; reflexivity. Qed.

  Add Field FG : (Algebra.Field.field_theory_for_stdlib_tactic (T:=F p)).

  Definition RFp2 : ring_theory zerop2 onep2 addp2 mulp2 subp2 oppp2 (@eq Fp2).
  Proof.
    split; intros; destruct x; try destruct y; try destruct z;
    apply Fp2irr; simpl; field.
  Qed.

  (* Inversion: (a + bu)^(-1) = (a - bu) / (a² - β·b²) *)
  (* The denominator a² - β·b² ≠ 0 because β is a QNR *)
  Definition invp2 (x : Fp2) : Fp2 :=
    if (F.to_Z (fst x) =? 0) then (F.zero, F.inv (snd x *p beta))
    else
      let norm := fst x *p fst x -p beta *p snd x *p snd x in
      (fst x /p norm, F.opp (snd x /p norm)).

  Definition divp2 (x1 x2 : Fp2) : Fp2 := mulp2 x1 (invp2 x2).

  (* Helper: product of nonzero elements is nonzero in Fp (integral domain) *)
  Local Lemma F_mul_nonzero (a b : F p) : a <> F.zero -> b <> F.zero -> (a *p b) <> F.zero.
  Proof.
    intros Ha Hb Hab. apply Ha.
    assert (H : a = @F.div p (a *p b) b) by (field; exact Hb).
    rewrite H, Hab. field; exact Hb.
  Qed.

  (* Helper: square root doesn't exist for QNR *)
  Local Lemma norm_nonzero (a b : F p) :
    (a <> F.zero \/ b <> F.zero) ->
    (a *p a -p beta *p b *p b) <> F.zero.
  Proof.
    intros Hne Hnorm.
    apply beta_is_QNR.
    (* From a² - β·b² = 0 deduce a² = β·b² *)
    assert (Heq : (a *p a) = (beta *p b *p b)).
    { assert (H := Hnorm).
      apply (f_equal (fun x => x +p (beta *p b *p b))) in H.
      replace (a *p a -p beta *p b *p b +p (beta *p b *p b)) with (a *p a) in H by field.
      replace (F.zero +p (beta *p b *p b)) with (beta *p b *p b) in H by field.
      exact H. }
    destruct (F.eq_dec b F.zero) as [Hb0 | Hbne].
    - (* b = 0: then a² = 0, so a = 0 *)
      subst b. exfalso.
      assert (Ha2 : (a *p a) = F.zero) by (rewrite Heq; field).
      (* a² = 0 in Fp implies a = 0: use integral domain property *)
      assert (Ha : a = F.zero).
      { destruct (F.eq_dec a F.zero) as [|Ha]; [assumption|].
        exfalso. apply (F_mul_nonzero a a Ha Ha). exact Ha2. }
      destruct Hne; contradiction.
    - (* b ≠ 0: then (a/b)² = β *)
      exists (@F.div p a b).
      replace (@F.div p a b *p @F.div p a b) with (@F.div p (a *p a) (b *p b)) by (field; exact Hbne).
      rewrite Heq. field. exact Hbne.
  Qed.

  Lemma FFp2 : field_theory zerop2 onep2 addp2 mulp2
    subp2 oppp2 divp2 invp2 (@eq (F p * F p)).
  Proof.
    constructor.
    - exact RFp2.
    - intros H.
      assert (H0 : fst onep2 = fst zerop2) by (rewrite H; reflexivity).
      simpl in H0. apply F.eq_to_Z_iff in H0.
      rewrite (@F.to_Z_1 p p_odd), (@F.to_Z_0 p) in H0. lia.
    - intros. reflexivity.
    - intros [a b] Hne.
      unfold mulp2, onep2.
      destruct (F.to_Z a =? 0) eqn:Ha.
      + apply Z.eqb_eq in Ha.
        assert (Ha0 : a = F.zero) by (apply F.eq_to_Z_iff; rewrite (@F.to_Z_0 p); exact Ha).
        subst a.
        assert (Hbne : b <> F.zero) by (intro Hb; apply Hne; subst b; reflexivity).
        replace (invp2 (F.zero, b)) with (@F.zero p, @F.inv p (b *p beta))
          by (unfold invp2; simpl fst; rewrite Z.eqb_refl; reflexivity).
        cbv [fst snd]. apply Fp2irr.
        * field. split; assumption.
        * field. split; assumption.
      + apply Z.eqb_neq in Ha.
        assert (Hane : a <> F.zero) by (intro Heq; subst a; rewrite (@F.to_Z_0 p) in Ha; exact (Ha eq_refl)).
        set (norm := a *p a -p beta *p b *p b).
        assert (Hnorm : norm <> F.zero) by (apply norm_nonzero; left; exact Hane).
        replace (invp2 (a, b)) with (a /p norm, @F.opp p (b /p norm))
          by (unfold invp2; simpl fst;
              replace (F.to_Z a =? 0) with false by (symmetry; apply Z.eqb_neq; exact Ha);
              reflexivity).
        cbv [fst snd]. apply Fp2irr.
        * unfold norm. field. apply norm_nonzero. left. exact Hane.
        * unfold norm. field. apply norm_nonzero. left. exact Hane.
  Qed.

End Fp2Generic.
