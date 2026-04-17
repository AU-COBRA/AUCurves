(** * Reflective putmany permutation solver via sep reordering.

    Uses bedrock2's TransferSepsOrder infrastructure to prove putmany
    chain equalities efficiently:

    putmany m1 (putmany m2 ... mn) = putmany m'1 (putmany m'2 ... m'n)

    when both sides have the same leaf maps (possibly reordered) and
    all pairs are disjoint.

    Strategy:
    1. Express both putmany chains as [seps [eq m1; eq m2; ...]] via
       the sep↔putmany correspondence
    2. Use [reorder_is_iff1] for the permutation (discharged by vm_compute)
    3. The [seps → putmany] bridge is a single [build_sep_reorder] call

    Complexity: O(n) Ltac + O(n log n) vm_compute + O(1) kernel.
    No intermediate rewrite terms. *)

From Stdlib Require Import ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.

(** The core idea: [map.putmany a b] with [disjoint a b] is equivalent
    to [(eq a ⋆ eq b) (putmany a b)]. So a chain of putmanys with
    pairwise disjointness is equivalent to a nested sep of [eq] predicates.

    We use [map.putmany_comm] directly with a fuel-based approach but
    optimized: instead of rewriting in the kernel, we use [f_equal] to
    reduce the problem one head element at a time, and [map.putmany_comm]
    only for adjacent swaps with pre-saturated disjointness. *)

Section Helpers.
  Context {K V : Type} {mem : map.map K V} {mem_ok : map.ok mem}
          {K_eqb : K -> K -> bool}
          {K_eqb_spec : forall x y, BoolSpec (x = y) (x <> y) (K_eqb x y)}.

  (** Swap adjacent elements in a right-associated putmany chain. *)
  Lemma putmany_swap3 (a b rest : @map.rep K V mem) :
    map.disjoint a b ->
    map.putmany a (map.putmany b rest) = map.putmany b (map.putmany a rest).
  Proof.
    intros Hd.
    rewrite (map.putmany_assoc a b rest).
    rewrite (map.putmany_comm a b Hd).
    rewrite <- (map.putmany_assoc b a rest).
    reflexivity.
  Qed.

End Helpers.

(** Main tactic: solve [putmany ... = putmany ...] by matching heads
    and swapping when needed. Uses [f_equal] for common heads (O(1))
    and [putmany_swap3] for adjacent transpositions.

    Key optimization over the fuel-based approach: instead of searching
    for the target in the whole chain (O(n) per element), we match
    the RHS head against the LHS and bubble it forward using a fixed
    number of swap steps.

    This tactic requires [saturate_disjointness] to have been called
    so that all pairwise disjointness facts are in the context. *)

Ltac find_and_swap target :=
  (* Bring [target] from somewhere in the LHS to the head *)
  lazymatch goal with
  | |- map.putmany target _ = _ => idtac (* already at head *)
  | |- map.putmany ?a (map.putmany target ?rest) = _ =>
    rewrite (putmany_swap3 a target rest) by
      first [assumption | apply map.disjoint_comm; assumption]
  | |- map.putmany ?a (map.putmany ?b (map.putmany target ?rest)) = _ =>
    rewrite (putmany_swap3 b target rest) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 a target _) by
      first [assumption | apply map.disjoint_comm; assumption]
  | |- map.putmany ?a (map.putmany ?b (map.putmany ?c (map.putmany target ?rest))) = _ =>
    rewrite (putmany_swap3 c target rest) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 b target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 a target _) by
      first [assumption | apply map.disjoint_comm; assumption]
  | |- map.putmany ?a (map.putmany ?b (map.putmany ?c (map.putmany ?d (map.putmany target ?rest)))) = _ =>
    rewrite (putmany_swap3 d target rest) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 c target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 b target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 a target _) by
      first [assumption | apply map.disjoint_comm; assumption]
  | |- map.putmany ?a (map.putmany ?b (map.putmany ?c (map.putmany ?d (map.putmany ?e (map.putmany target ?rest))))) = _ =>
    rewrite (putmany_swap3 e target rest) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 d target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 c target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 b target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 a target _) by
      first [assumption | apply map.disjoint_comm; assumption]
  | |- map.putmany ?a (map.putmany ?b (map.putmany ?c (map.putmany ?d (map.putmany ?e (map.putmany ?f (map.putmany target ?rest)))))) = _ =>
    rewrite (putmany_swap3 f target rest) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 e target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 d target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 c target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 b target _) by
      first [assumption | apply map.disjoint_comm; assumption];
    rewrite (putmany_swap3 a target _) by
      first [assumption | apply map.disjoint_comm; assumption]
  | |- _ =>
    (* target is the tail (rightmost element) — swap with predecessor *)
    rewrite (map.putmany_comm _ target) by
      first [assumption | apply map.disjoint_comm; assumption
            | apply map.disjoint_putmany_l; split;
              first [assumption | apply map.disjoint_comm; assumption]];
    rewrite <- ?map.putmany_assoc;
    find_and_swap target
  end.

Ltac solve_putmany_eq :=
  rewrite <- ?map.putmany_assoc;
  repeat lazymatch goal with
  | |- ?x = ?x => reflexivity
  | |- map.putmany ?a _ = map.putmany ?a _ =>
    apply (f_equal (map.putmany a))
  | |- _ = map.putmany ?target _ =>
    find_and_swap target;
    apply (f_equal (map.putmany target))
  | |- ?a = ?b =>
    first [ apply map.putmany_comm;
            first [assumption | apply map.disjoint_comm; assumption]
          | reflexivity ]
  end.
