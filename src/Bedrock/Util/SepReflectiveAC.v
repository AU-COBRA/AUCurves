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

From Stdlib Require Import List ZArith Lia.
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

  (** The element at position [n] can be moved to the head of the seps list. *)
  Lemma seps_pick_iff1 : forall (l : list pred) (n : nat),
    (n < length l)%nat ->
    iff1 (seps l)
         (seps (List.nth n l (emp True)
                :: List.firstn n l ++ List.skipn (S n) l)).
  Proof.
    induction l as [|p l IH]; intros n Hn.
    - cbn [length] in Hn. exfalso; inversion Hn.
    - destruct n as [|n].
      + cbn [List.nth List.firstn List.skipn List.app].
        reflexivity.
      + cbn [length] in Hn. apply Nat.succ_lt_mono in Hn.
        cbn [List.nth List.firstn List.skipn List.app].
        specialize (IH n Hn).
        (* IH : iff1 (seps l) (seps (nth n l _ :: firstn n l ++ skipn (S n) l)) *)
        rewrite seps_cons_iff1 with (l2 := List.nth n l (emp True)
                                           :: List.firstn n l ++ List.skipn (S n) l)
          by exact IH.
        (* Goal: iff1 (seps (p :: nth n l _ :: firstn n l ++ skipn (S n) l))
                      (seps (nth n l _ :: p :: firstn n l ++ skipn (S n) l)) *)
        rewrite !seps_cons.
        rewrite <- !sep_assoc.
        rewrite (sep_comm p (List.nth n l (emp True))).
        reflexivity.
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

(** [flatten_seps_in_strict H] — alternative to coqutil's [flatten_seps_in]
    that works on FElem-bearing hypotheses.

    The upstream [flatten_seps_in] uses [iff1_syntactic_reflexivity] which
    requires [constr_eq] on the reified vs original sep tree.  When the
    hypothesis contains [FElem addr X] (a typeclass-method projection), the
    [cbv [seps Tree.to_sep Tree.interp]] step doesn't produce a syntactically-
    equal form.  This implementation uses [change] (cbv-equivalence) instead
    of syntactic equality, then applies [Tree.flatten_iff1_to_sep] directly
    via its [proj2]. *)
Ltac flatten_seps_in_strict H :=
  lazymatch type of H with
  | ?nested ?m =>
      let tree := SeparationLogic.reify nested in
      change (SeparationLogic.Tree.to_sep tree m) in H;
      apply (proj2 (SeparationLogic.Tree.flatten_iff1_to_sep tree m)) in H;
      cbv [SeparationLogic.Tree.flatten SeparationLogic.app] in H
  end.

(** [find_index_of_atom atom l] — Ltac that returns the index of [atom] in [l]
    (a Coq nat), or fails if not found. *)
Ltac find_index_of_atom atom l :=
  let rec go l n :=
    lazymatch l with
    | nil => fail "find_index_of_atom: atom not found"
    | cons ?head ?tail =>
        tryif constr_eq head atom then n
        else go tail uconstr:(S n)
    end
  in let n := go l O in constr:(n).

(** [reflective_ecancel H] — close a goal of shape [(target ⋆ ?Rr)%sep m] by
    finding [target] as an atom in [H : <some ⋆-tree>%sep m].

    Pipeline:
      1. flatten_seps_in_strict H  →  H : seps Hin m
      2. flatten_seps_in_goal       →  goal: seps [target; ?Rr_atoms] m
      3. find index i of target in Hin (Ltac, compile-time)
      4. apply [seps_pick_iff1 i] to permute Hin so target is at position 0
      5. cbn down the firstn/skipn/app to a concrete list
      6. exact H — ?Rr unifies with [seps (Hin without target)]

    Reflective: all proof-term contributions are Qed-sealed lemma applications
    (Tree.flatten_iff1_to_sep, seps_pick_iff1) plus a vm_compute on the index
    bound proof. *)
Ltac reflective_ecancel H :=
  flatten_seps_in_strict H;
  SeparationLogic.flatten_seps_in_goal;
  lazymatch type of H with
  | seps ?Hin ?m =>
      lazymatch goal with
      | |- seps (?target :: _) _ =>
          let i := find_index_of_atom target Hin in
          apply (proj1 (seps_pick_iff1 Hin i ltac:(cbv [List.length]; lia))
                       m) in H;
          cbn [List.nth List.firstn List.skipn List.app] in H;
          exact H
      end
  end.
