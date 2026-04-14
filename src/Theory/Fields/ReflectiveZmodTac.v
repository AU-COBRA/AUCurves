(******************************************************************************)
(*                                                                            *)
(*     ReflectiveZmodTac: Ltac reification + tactics for reflective Zmod     *)
(*                                                                            *)
(*  Provides:                                                                 *)
(*    rpull_Zmod   — reflective pull_Zmod, O(n) via vm_compute              *)
(*                                                                            *)
(*  Replaces the O(n²) rewrite-loop pull_Zmod with:                          *)
(*    1. Ltac reification of LHS/RHS into ZMExpr trees                       *)
(*    2. vm_compute of strip_mod + zm_eqb (boolean, O(n))                    *)
(*    3. Kernel sees only (erefl true) — instant Qed                         *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import ZArith List.
From Theory.Fields Require Import ReflectiveZmod.
Import ListNotations.

Local Open Scope Z_scope.

(** * Varmap: association list mapping Z terms to nat indices.

    We represent the variable environment as a Rocq [list Z].
    During reification, Ltac builds this list and looks up indices.

    Key technique: CPS (continuation-passing style) to thread the
    growing environment through Ltac, since Ltac can't return
    multiple values from a single tactic call. *)

(** Find [e] in [env] starting at index [n]. Returns index or fails. *)
Ltac find_idx e env n :=
  match env with
  | cons ?x ?rest =>
    match x with
    | e => n
    | _ => find_idx e rest (S n)
    end
  | _ => fail 100 "variable not found in env"
  end.

(** Reify [e] as a ZMExpr, given modulus [m] and pre-built [env].
    All atoms must already be in [env]. *)
Ltac reify m env e :=
  lazymatch e with
  | ?a + ?b =>
    let ra := reify m env a in
    let rb := reify m env b in
    constr:(ZMAdd ra rb)
  | ?a * ?b =>
    let ra := reify m env a in
    let rb := reify m env b in
    constr:(ZMMul ra rb)
  | ?a - ?b =>
    let ra := reify m env a in
    let rb := reify m env b in
    constr:(ZMSub ra rb)
  | Z.opp ?a =>
    let ra := reify m env a in
    constr:(ZMOpp ra)
  | ?a mod m =>
    let ra := reify m env a in
    constr:(ZMMod ra)
  | _ =>
    let idx := find_idx e env 0%nat in
    constr:(ZMVar idx)
  end.

(** Collect all atomic subterms (leaves) from a Z expression.
    An atom is anything not matching +, *, -, opp, mod m.
    Returns a deduplicated [list Z]. *)
Ltac mem e l :=
  match l with
  | nil => false
  | cons e _ => true
  | cons _ ?rest => mem e rest
  end.

Ltac collect m e acc :=
  lazymatch e with
  | ?a + ?b =>
    let acc := collect m a acc in
    collect m b acc
  | ?a * ?b =>
    let acc := collect m a acc in
    collect m b acc
  | ?a - ?b =>
    let acc := collect m a acc in
    collect m b acc
  | Z.opp ?a => collect m a acc
  | ?a mod m => collect m a acc
  | _ =>
    let found := mem e acc in
    match found with
    | true => acc
    | false => constr:(cons e acc)
    end
  end.

(** * Main tactic: rpull_Zmod *)

(** Proves goals of the form [LHS mod m = RHS mod m] by:
    1. Collecting variables from LHS and RHS
    2. Reifying both sides as ZMExpr
    3. Applying reflective_pull_Zmod
    4. vm_compute checks strip_mod(LHS) =? strip_mod(RHS)

    O(n) total — the Ltac reification is O(n), vm_compute is O(n). *)
Ltac rpull_Zmod :=
  lazymatch goal with
  | |- ?lhs mod ?m = ?rhs mod ?m =>
    let env := collect m lhs (@nil Z) in
    let env := collect m rhs env in
    let rl := reify m env lhs in
    let rr := reify m env rhs in
    change (zm_eval env m rl mod m = zm_eval env m rr mod m);
    apply (reflective_pull_Zmod env m rl rr);
    vm_compute;
    reflexivity
  end.

(** Variant: goal is [LHS mod m = RHS] where RHS has no outer mod.
    Wraps RHS in ZMMod for the check. *)
Ltac rpull_Zmod_l :=
  lazymatch goal with
  | |- ?lhs mod ?m = ?rhs =>
    let env := collect m lhs (@nil Z) in
    let env := collect m rhs env in
    let rl := reify m env lhs in
    let rr := reify m env rhs in
    change (zm_eval env m rl mod m = zm_eval env m rr);
    apply (reflective_pull_Zmod_l env m rl rr);
    vm_compute;
    reflexivity
  end.

(** Combined: try both forms *)
Ltac rpull_Zmod_auto :=
  first [ rpull_Zmod | rpull_Zmod_l ].

(** * rpush_Zmod: push mods inward reflectively.

    Proves goals of the form [LHS mod m = RHS mod m] when both sides become
    syntactically equal after wrapping every sub-operation with mod (add_mod).
    Analogous to rpull_Zmod but for the push direction. *)
Ltac rpush_Zmod :=
  lazymatch goal with
  | |- ?lhs mod ?m = ?rhs mod ?m =>
    let env := collect m lhs (@nil Z) in
    let env := collect m rhs env in
    let rl := reify m env lhs in
    let rr := reify m env rhs in
    change (zm_eval env m rl mod m = zm_eval env m rr mod m);
    apply (reflective_push_Zmod env m rl rr);
    vm_compute;
    reflexivity
  end.

(** Debug: just reify and print, don't apply theorem *)
Ltac rpull_Zmod_debug :=
  lazymatch goal with
  | |- ?lhs mod ?m = ?rhs mod ?m =>
    let env := collect m lhs (@nil Z) in
    let env := collect m rhs env in
    let rl := reify m env lhs in
    let rr := reify m env rhs in
    let sl := eval compute in (strip_mod rl) in
    let sr := eval compute in (strip_mod rr) in
    idtac "ENV:" env;
    idtac "LHS reified:" rl;
    idtac "RHS reified:" rr;
    idtac "LHS stripped:" sl;
    idtac "RHS stripped:" sr;
    let eq := eval compute in (zm_eqb sl sr) in
    idtac "Equal:" eq
  | |- ?g => idtac "Goal shape:" g
  end.
