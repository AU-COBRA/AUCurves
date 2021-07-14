From Coqprime Require Import UList.
Require Import List.
Require Import Crypto.Util.Decidable.

Section UList.
  Variable T : Set.
  Hypothesis dec_eq : forall x y : T, {x = y} + {x <> y}.

  (*Proof copied from standard library, may be omitted in coq version 12. *)
  Lemma in_in_remove : forall l x y, x <> y -> In x l -> In x (remove dec_eq y l).
  Proof.
    induction l as [|z l]; simpl; intros x y Hneq Hin.
    - apply Hin.
    - destruct (dec_eq y z); subst.
      + destruct Hin.
        * exfalso; now apply Hneq.
        * now apply IHl.
      + simpl; destruct Hin; [now left|right].
        now apply IHl.
  Qed.

  (*Proof copied from standard library, may be omitted in coq version 12. *)
  Lemma in_remove : forall l x y, In x (remove dec_eq y l) -> In x l /\ x <> y.
  Proof.
    induction l as [|z l]; intros x y Hin.
    - inversion Hin.
    - simpl in Hin.
      destruct (dec_eq y z) as [Heq|Hneq]; subst; split.
      + right; now apply IHl with z.
      + intros Heq; revert Hin; subst; apply remove_In.
      + inversion Hin; subst; [left; reflexivity|right].
        now apply IHl with y.
      + destruct Hin as [Hin|Hin]; subst.
        * now intros Heq; apply Hneq.
        * intros Heq; revert Hin; subst; apply remove_In.
  Qed.

  (*Proof copied from standard library, may be omitted in coq version 12. *)
  Lemma notin_remove: forall l x, ~ In x l -> remove dec_eq x l = l.
  Proof.
    intros l x; induction l as [|y l]; simpl; intros Hnin.
    - reflexivity.
    - destruct (dec_eq x y); subst; intuition.
      f_equal; assumption.
  Qed.


  Lemma remove_cons : forall x l, remove dec_eq x (x :: l) = remove dec_eq x l.
  Proof.
    intros x l; simpl; destruct (dec_eq x x); [ reflexivity | now exfalso ].
  Qed.

  Lemma incl_rem : forall l m x, incl m l -> incl (remove dec_eq x m) l.
  Proof. intros l m x H; intros a Ha; apply H; apply in_remove in Ha; destruct Ha; auto. Qed.

  Lemma incl_rem_l_l : forall l x, incl (remove dec_eq x l) l.
  Proof. intros l x; apply incl_rem, incl_refl. Qed.

  Import ListNotations.

  Lemma ulist_rem : forall l x, ulist l -> ulist (remove dec_eq x l).
  Proof.
    intros l x H; remember (length l) as len; generalize dependent l; induction len as [| len' IHlen'].
      - intros l H1 H2; assert (l = []) as Hnil by (destruct l; auto; discriminate);
        rewrite Hnil; apply ulist_nil.
      - intros l H1 H2; destruct l as [| x' l']; try auto; simpl in H2; inversion H2 as [H3]; simpl;
        destruct (dec_eq x x') as [Hxval | Hxval] eqn:dec.
          + simpl; apply IHlen'; try inversion H1; auto.
          + apply ulist_cons.
            * inversion H1; pose proof incl_rem_l_l l' x; auto.
            * apply IHlen'; try inversion H1; auto.
  Qed.  

  Lemma ulist_rem_len : forall l x, ulist l -> In x l -> length l = S( length (remove dec_eq x l)).
  Proof.
    intros l x H1 H2; induction l as [|x' l' IHl']; try contradiction.
      - simpl; destruct (dec_eq x x') as [e|e].
        + inversion H1; assert (remove dec_eq x l' = l') as H' by (apply notin_remove; rewrite e; auto);
          rewrite H'; auto.
        + inversion H2 as [H|H]; try (symmetry in H; contradiction).
          inversion H1; apply (f_equal (fun y => S y)); apply IHl'; auto.
  Qed.
End UList.