(** * SepReflectiveAC — Reflective seps emp absorption.

    Helpers for finishing bedrock2 WP proofs that get stuck on ecancel
    timeouts due to extra `emp True` clauses (typically from `cbn [array]`
    reducing nil-tailed arrays).

    Use after `flatten_seps_in_goal` / `flatten_seps_in H` so both sides
    are in `seps [...] m` form.  Then `drop_all_emp_True_in H` and
    `drop_all_emp_True_in_goal` strip emp True clauses reflectively
    (Ltac walk over the concrete Gallina list — no setoid rewrite on the
    big sep tree).
*)

From Stdlib Require Import List ZArith.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Import ListNotations.

Section SepReflectiveAC.
  Context {key value : Type}
          {key_eqb : key -> key -> bool}
          {key_eqb_spec : forall k1 k2, BoolSpec (k1 = k2) (k1 <> k2) (key_eqb k1 k2)}
          {map : map.map key value} {map_ok : map.ok map}.

  Local Notation iff1 := Lift1Prop.iff1.
  Local Notation pred := (map -> Prop).

  (** seps L is iff1-equal to its tail when head = emp True. *)
  Lemma seps_emp_True_cons : forall (l : list pred),
    iff1 (seps (emp True :: l)) (seps l).
  Proof.
    intros [|p l]; cbn [seps].
    - reflexivity.
    - rewrite sep_emp_True_l. reflexivity.
  Qed.

  (** Cons-preserves-iff1 lemma. *)
  Lemma seps_cons_iff1 : forall p (l1 l2 : list pred),
    iff1 (seps l1) (seps l2) ->
    iff1 (seps (p :: l1)) (seps (p :: l2)).
  Proof.
    intros p l1 l2 Hiff.
    destruct l1 as [|x l1]; destruct l2 as [|y l2]; cbn [seps] in *.
    - reflexivity.
    - cbn [seps] in Hiff. rewrite <- Hiff. rewrite sep_emp_True_r. reflexivity.
    - cbn [seps] in Hiff. rewrite Hiff. rewrite sep_emp_True_r. reflexivity.
    - apply iff1_sep_cancel. exact Hiff.
  Qed.

  (** General: emp True at any position can be dropped. *)
  Lemma seps_emp_True_split : forall (l1 l2 : list pred),
    iff1 (seps (l1 ++ emp True :: l2)) (seps (l1 ++ l2)).
  Proof.
    induction l1 as [|p l1 IH]; intros l2; cbn [List.app seps].
    - destruct l2 as [|x l2]; cbn [seps].
      + reflexivity.
      + rewrite sep_emp_True_l. reflexivity.
    - destruct l1 as [|q l1]; cbn [List.app seps] in *.
      + destruct l2 as [|x l2]; cbn [seps].
        * rewrite sep_emp_True_r. reflexivity.
        * apply iff1_sep_cancel. rewrite sep_emp_True_l. reflexivity.
      + apply iff1_sep_cancel. apply IH.
  Qed.

  (** Trailing emp True can be dropped from a seps list. *)
  Lemma seps_emp_True_snoc : forall (l : list pred),
    iff1 (seps (l ++ [emp True])) (seps l).
  Proof.
    induction l as [|p l IH].
    - cbn [List.app seps]. reflexivity.
    - cbn [List.app seps].
      destruct (l ++ [emp True]) as [|x xs] eqn:E.
      + destruct l; cbn in E; discriminate.
      + destruct l as [|y l]; cbn [seps] in *.
        * cbn in E. injection E as ? ?. subst x xs.
          rewrite sep_emp_True_r. reflexivity.
        * apply iff1_sep_cancel. exact IH.
  Qed.

End SepReflectiveAC.

(** Recursively strip leading `emp True` clauses from a `seps` hypothesis. *)
Ltac strip_leading_emp_True_in H :=
  lazymatch type of H with
  | seps (emp True :: ?l) ?m =>
      apply (proj1 (seps_emp_True_cons l m)) in H;
      strip_leading_emp_True_in H
  | _ => idtac
  end.

(** Repeatedly strip leading emp True until none remain at head. *)
Ltac drop_leading_emps_in H :=
  repeat strip_leading_emp_True_in H.

(** Same for goal. *)
Ltac strip_leading_emp_True_in_goal :=
  lazymatch goal with
  | |- seps (emp True :: ?l) ?m =>
      apply (proj2 (seps_emp_True_cons l m));
      strip_leading_emp_True_in_goal
  | _ => idtac
  end.

Ltac drop_leading_emps_in_goal :=
  repeat strip_leading_emp_True_in_goal.
