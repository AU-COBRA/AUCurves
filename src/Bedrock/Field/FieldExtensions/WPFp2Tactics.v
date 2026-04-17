(** * WP proof automation for Fp2-level operations.

    Provides high-level tactics that chain the bedrock2 WP proof steps
    for functions operating on Fp2 = (Fp × Fp) field elements.

    Key tactics:
    - wp_fp2_setup: start_func + cbv + straightline + stackalloc
    - wp_fp2_split: decompose Fp2 FElem into Fp halves
    - wp_fp2_call: handle one Fp-level call (dexprs + weaken_call + postcond)
    - wp_fp2_join: reassemble Fp halves into Fp2 FElem
    - wp_fp2_postcondition: final feval/bounded_by/sep assembly
*)

Require Import Rupicola.Lib.Api.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensionsSpecs.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.

(* ================================================================ *)
(* Memory map manipulation tactics                                   *)
(* ================================================================ *)

(** Decompose all map.disjoint hypotheses involving map.putmany. *)
Ltac saturate_map_disjointness :=
  repeat match goal with
  | H : map.disjoint ?a (map.putmany ?b ?c) |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_r a b c) H) as [H1 H2]; clear H
  | H : map.disjoint (map.putmany ?a ?b) ?c |- _ =>
      let H1 := fresh "Hd" in let H2 := fresh "Hd" in
      destruct (proj1 (map.disjoint_putmany_l a b c) H) as [H1 H2]; clear H
  end.

(** Solve map.disjoint goals by searching hypotheses and decomposing putmany. *)
Ltac solve_map_disjoint :=
  saturate_map_disjointness;
  try assumption;
  try (apply map.disjoint_comm; assumption);
  try (apply map.disjoint_putmany_r; split; solve_map_disjoint);
  try (apply map.disjoint_putmany_l; split; solve_map_disjoint).

(** Swap adjacent putmany terms: putmany a (putmany b rest) → putmany b (putmany a rest) *)
Ltac map_swap a b :=
  rewrite (map.putmany_comm a b) by solve_map_disjoint;
  rewrite <- map.putmany_assoc.

(** Solve putmany equalities by reordering via commutativity. *)
Ltac solve_putmany_eq :=
  repeat first
    [ reflexivity
    | progress (rewrite <- map.putmany_assoc)
    | progress (rewrite map.putmany_assoc)
    | match goal with
      | |- map.putmany ?a _ = map.putmany ?a _ => f_equal
      | |- map.putmany ?a (map.putmany ?b _) = map.putmany ?b _ =>
          map_swap a b
      end
    ].

(* ================================================================ *)
(* Fp2 FElem decomposition                                          *)
(* ================================================================ *)

(** Split an Fp2 FElem hypothesis into two Fp FElem halves.
    Usage: wp_fp2_split H as m1 m2 Hfe1 Hfe2
    where H : FElem_Fp2 ptr felem mem *)
Ltac wp_fp2_split_in H m1 m2 Hfe1 Hfe2 :=
  let Hsp := fresh "Hsp" in
  let Heq := fresh "Heq" in
  let Hd := fresh "Hd" in
  match type of H with
  | @AbstractField.FElem _ ?fp _ _ _ _ ?repr ?ptr ?felem ?mem =>
    pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_split
                  _ _ _ _ ltac:(exact _) ltac:(exact _) _ _ _ _ ptr felem mem H)
      as [m1 [m2 [Hsp [Hfe1 Hfe2]]]];
    destruct Hsp as [Heq Hd];
    try subst mem
  end.

(* ================================================================ *)
(* FElem postcondition helpers                                       *)
(* ================================================================ *)

(** Join two Fp FElem halves into one Fp2 FElem. *)
Ltac wp_fp2_join_with Hlen1 Hlen2 Hjoin :=
  match type of Hjoin with
  | (_ ⋆ _) ?m =>
    pose proof (@QuadraticFieldExtensions.Fp2_raw_FElem_join
                  _ _ _ _ ltac:(exact _) ltac:(exact _) _ _ _ _
                  _ _ _ m Hlen1 Hlen2 Hjoin)
  end.
