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
Require Import coqutil.Sorting.OrderToPermutation.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.TransferSepsOrder.
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
      cbv [SeparationLogic.Tree.flatten SeparationLogic.Tree.interp
           SeparationLogic.app List.app] in H
  end.

(** [find_index_of_atom atom l] — Ltac that returns the index of [atom] in [l]
    (a Coq nat), or fails if not found. *)
Ltac find_index_of_atom atom l :=
  lazymatch l with
  | nil => fail "find_index_of_atom: atom not found"
  | cons ?head ?tail =>
      match constr:(Set) with
      | _ => let _ := match constr:(Set) with
                      | _ => constr_eq head atom
                      end in
             constr:(O)
      | _ => let n := find_index_of_atom atom tail in constr:(S n)
      end
  end.

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
  lazymatch goal with
  | |- (?target ⋆ _)%sep ?m =>
      lazymatch type of H with
      | seps ?Hin _ =>
          let i := find_index_of_atom target Hin in
          (* Permute Hin so target is at position 0 *)
          apply (proj1 (seps_pick_iff1 Hin i ltac:(cbv [List.length]; lia)
                       m)) in H;
          cbn [List.nth List.firstn List.skipn List.app] in H;
          (* Convert Hin back from [seps (target :: rest)] to
             [(target ⋆ seps rest)] form so the goal's [?Rr] evar
             can unify with [seps rest]. *)
          lazymatch type of H with
          | seps (?t :: ?rest) ?m' =>
              apply (proj1 (SeparationLogic.seps_cons t rest m')) in H
          end;
          exact H
      end
  end.

(** [reflective_seps_perm] — close a goal of shape [seps L1 m] given a
    hypothesis [H : seps L2 m] where [L2] is a permutation of [L1].

    Used when both sides have been flattened to seps lists with the same
    atoms in different order.  Builds an explicit permutation order from
    [L2] to [L1] via [find_index_of_atom] in a tail-recursive Ltac, then
    applies [reorder_is_iff1] (Qed-sealed in coqutil). *)
Ltac build_order_from_to from to acc :=
  lazymatch to with
  | nil => acc
  | cons ?head ?tail =>
      let i := find_index_of_atom head from in
      let acc' := uconstr:(cons i acc) in
      build_order_from_to from tail acc'
  end.

(** [reflective_seps_iff1] — closes a goal of shape
    [iff1 (seps L1) (seps L2)] when L1 and L2 are permutations of each
    other.  Computes the order via Ltac, applies [reorder_is_iff1]
    (Qed-sealed), vm_computes the permutation, and uses [reflexivity].

    The Qed-sealed [reorder_is_iff1] absorbs the cancel work; the per-call
    proof-term contribution is a single application of that lemma plus
    a vm_compute-checked permutation list. *)
Ltac reflective_seps_iff1 :=
  lazymatch goal with
  | |- iff1 (seps ?L1) (seps ?L2) =>
      let order_rev := build_order_from_to L1 L2 uconstr:(@nil nat) in
      let order := constr:(List.rev order_rev) in
      (* Use existing reorder_is_iff1 from coqutil *)
      etransitivity;
      [ apply (TransferSepsOrder.reorder_is_iff1 order L1
                                                ltac:(reflexivity)) |];
      cbv [OrderToPermutation.reorder
           OrderToPermutation.apply_permutation
           OrderToPermutation.apply_permutation_with_default
           OrderToPermutation.my_list_map OrderToPermutation.my_list_nth];
      let r := eval vm_compute in (OrderToPermutation.order_to_permutation order) in
        change (OrderToPermutation.order_to_permutation order) with r;
      cbn [List.nth List.map seps];
      reflexivity
  end.

(** [reflective_reshape H target_form] — close a goal of shape
    [target_form m] (a specific ⋆-tree) given [H : nested m] where
    nested is some ⋆-tree of the same atoms.

    Workflow:
      1. flatten_seps_in_strict H  →  H : seps L_H m
      2. flatten_seps_in_goal      →  goal: seps L_G m
      3. reflective_seps_iff1 to bridge L_H to L_G permutation
      4. exact H

    Useful for replacing the [(use_sep_assumption; cancel; reflexivity)]
    pattern when both H and goal have a fixed shape with the same atoms.
    Unlike [reflective_ecancel], the goal here has NO evar — it's a
    concrete sep tree to be matched. *)
Ltac reflective_reshape H :=
  flatten_seps_in_strict H;
  SeparationLogic.flatten_seps_in_goal;
  lazymatch goal with
  | |- seps ?L_G ?m =>
      lazymatch type of H with
      | seps ?L_H _ =>
          (* Convert goal: seps L_G m  ->  seps L_H m via iff1. *)
          let order_rev := build_order_from_to L_G L_H uconstr:(@nil nat) in
          let order := constr:(List.rev order_rev) in
          apply (proj1 (TransferSepsOrder.reorder_is_iff1 order L_G
                                                          ltac:(reflexivity)
                                                          m));
          cbv [OrderToPermutation.reorder
               OrderToPermutation.apply_permutation
               OrderToPermutation.apply_permutation_with_default
               OrderToPermutation.my_list_map OrderToPermutation.my_list_nth];
          let r := eval vm_compute in (OrderToPermutation.order_to_permutation order) in
            change (OrderToPermutation.order_to_permutation order) with r;
          cbn [List.nth List.map seps List.app];
          exact H
      end
  end.
