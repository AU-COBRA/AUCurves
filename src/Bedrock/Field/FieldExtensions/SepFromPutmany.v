(** * Sep logic automation for putmany chains.

    Tactics to automatically construct sep conjunction facts from
    right-associated putmany chains with known per-region predicates
    and pairwise disjointness. *)

From Stdlib Require Import ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.SeparationLogic.

(** *** Disjointness saturation *)

Ltac split_disjoint_hyp H :=
  lazymatch type of H with
  | map.disjoint (map.putmany _ _) _ =>
    let H1 := fresh "Hd" in let H2 := fresh "Hd" in
    destruct (proj1 (map.disjoint_putmany_l _ _ _) H) as [H1 H2];
    clear H; split_disjoint_hyp H1; split_disjoint_hyp H2
  | map.disjoint _ (map.putmany _ _) =>
    let H1 := fresh "Hd" in let H2 := fresh "Hd" in
    destruct (proj1 (map.disjoint_putmany_r _ _ _) H) as [H1 H2];
    clear H; split_disjoint_hyp H1; split_disjoint_hyp H2
  | map.disjoint _ _ => idtac
  end.

Ltac split_all_disjointness :=
  repeat match goal with
  | H : map.disjoint (map.putmany _ _) _ |- _ => split_disjoint_hyp H
  | H : map.disjoint _ (map.putmany _ _) |- _ => split_disjoint_hyp H
  end.

(** *** Disjointness solver *)

Ltac map_disjoint_auto :=
  lazymatch goal with
  | |- map.disjoint (map.putmany _ _) _ =>
      apply map.disjoint_putmany_l; split; map_disjoint_auto
  | |- map.disjoint _ (map.putmany _ _) =>
      apply map.disjoint_putmany_r; split; map_disjoint_auto
  | |- map.disjoint ?a ?b =>
      first [ assumption
            | (apply map.disjoint_comm; assumption) ]
  end.

(** *** Putmany chain reordering *)

Ltac map_swap a b :=
  rewrite (map.putmany_assoc a b);
  let D := fresh "Hd_swap" in
  assert (D : map.disjoint a b) by map_disjoint_auto;
  rewrite (map.putmany_comm a b D);
  clear D;
  rewrite <- (map.putmany_assoc b a).

(** Bring m to the front of a putmany chain in the goal's argument. *)
Ltac bring_to_front_in m term :=
  lazymatch term with
  | map.putmany m _ => idtac
  | map.putmany ?a (map.putmany m ?rest) =>
      map_swap a m
  | map.putmany ?a m =>
      (* m is the tail of a 2-element chain: swap directly *)
      let D := fresh "Hd_tail" in
      assert (D : map.disjoint a m) by map_disjoint_auto;
      rewrite (map.putmany_comm a m D);
      clear D
  | map.putmany ?a ?inner =>
      bring_to_front_in m inner;
      map_swap a m
  end.

Ltac bring_to_front m :=
  lazymatch goal with
  | |- _ (map.putmany m _) => idtac
  | |- _ ?whole => bring_to_front_in m whole
  end.

(** *** Build sep from putmany chain *)

(** Find which map region a predicate holds on.
    Uses unification: given goal predicate P, finds H such that H's type
    unifies with (P ?m) for some m. Falls back to matching any 3-arg
    predicate sharing the same address and value arguments. *)
Ltac find_map_for_pred P :=
  multimatch goal with
  | H : P ?m |- _ => constr:(m)
  | H : ?Q |- _ =>
    lazymatch P with
    | ?F ?addr ?val =>
        lazymatch Q with
        | ?G addr val ?m => constr:(m)  (* exact addr+val match *)
        | ?G addr ?val2 ?m => constr:(m)  (* match addr only, ignore val (for evars) *)
        end
    end
  end.

(** Flatten left-nested putmany to right-associated form (recursive).
    putmany (putmany a b) c → putmany a (putmany b c)
    Also flattens inner nestings: putmany a (putmany (putmany b c) d) *)
Ltac flatten_putmany :=
  repeat match goal with
  | |- context [map.putmany (map.putmany ?a ?b) ?c] =>
      rewrite <- (map.putmany_assoc a b c)
  end.

Ltac flatten_sep := idtac.

(** Core tactic: build a sep conjunction proof from a putmany chain.

    Handles:
    - Left-associated sep: (P * Q) * R → P * (Q * R) then recurse
    - Right-associated sep on putmany: match head, bring_to_front if needed
    - Base case: single predicate on single map → eassumption
    - Frame case: evar predicate on putmany chain → continue decomposing
      by casting the evar to a sep and recursing *)
Ltac build_sep_reorder :=
  flatten_putmany;
  lazymatch goal with
  | |- (sep (sep ?P ?Q) ?R) ?m =>
      (* Left-associated: reassociate then retry *)
      apply (fun (H : (P ⋆ (Q ⋆ R))%sep m) => proj2 (sep_assoc P Q R m) H);
      build_sep_reorder
  | |- (sep ?P ?Q) (map.putmany ?m_head ?m_rest) =>
      first
      [ (exists m_head, m_rest;
         split; [split; [reflexivity | map_disjoint_auto] |];
         split; [first [eassumption | assumption] | build_sep_reorder])
      | (let target := find_map_for_pred P in
         bring_to_front target;
         build_sep_reorder)
      ]
  | |- ?P ?m =>
      first
      [ (* Prefer non-disjoint hypotheses (handles both known and evar P) *)
        match goal with
        | |- _ ?mh =>
            match goal with
            | H : _ mh |- _ =>
                lazymatch type of H with
                | map.disjoint _ _ => fail
                | _ => exact H
                end
            end
        end
      | eassumption
      | assumption
      | (* Frame construction: P is an evar, m is a putmany chain.
           Cast the goal to (sep ?A ?B) m and continue decomposing.
           The match on (H : _ m_head) ensures the hypothesis actually
           holds on the specific map region, not on some unrelated map. *)
        lazymatch m with
        | map.putmany ?m_head ?m_rest =>
            refine (_ : (sep _ _) m);
            exists m_head, m_rest;
            split; [split; [reflexivity | map_disjoint_auto] |];
            split;
            [ match goal with
              | |- _ ?mh =>
                  match goal with
                  | H : _ mh |- _ =>
                      lazymatch type of H with
                      | map.disjoint _ _ => fail
                      | _ => exact H
                      end
                  end
              end
            | build_sep_reorder ]
        end
      ]
  end.
