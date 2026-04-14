(******************************************************************************)
(*                                                                            *)
(*     ReflectiveZmod: Reflective pull_Zmod / push_Zmod                       *)
(*                                                                            *)
(*  Replaces O(n²) rewrite-based pull_Zmod with O(n) vm_compute.             *)
(*                                                                            *)
(*  Architecture:                                                             *)
(*    1. Reify: Z expression with mod → ZMExpr syntax tree                   *)
(*    2. Normalize: strip_mod removes inner mods (pull), add_mod adds them   *)
(*       (push). Both are pure Gallina → vm_compute runs in O(n).            *)
(*    3. Soundness: eval (strip_mod e) mod m = eval e mod m                  *)
(*    4. Apply: change goal to vm_compute'd normal form, close by soundness  *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import ZArith Lia List Bool.
Import Z ListNotations.

Local Open Scope Z_scope.

(** * Syntax: Z expressions with mod *)
Inductive ZMExpr : Type :=
  | ZMVar : nat -> ZMExpr            (* variable reference *)
  | ZMConst : Z -> ZMExpr            (* literal constant *)
  | ZMAdd : ZMExpr -> ZMExpr -> ZMExpr
  | ZMMul : ZMExpr -> ZMExpr -> ZMExpr
  | ZMSub : ZMExpr -> ZMExpr -> ZMExpr
  | ZMOpp : ZMExpr -> ZMExpr
  | ZMMod : ZMExpr -> ZMExpr.        (* mod m — the modulus is implicit/fixed *)

(** * Evaluation: interpret ZMExpr as Z given an environment and modulus *)
Fixpoint zm_eval (env : list Z) (m : Z) (e : ZMExpr) : Z :=
  match e with
  | ZMVar n => nth n env 0
  | ZMConst c => c
  | ZMAdd a b => zm_eval env m a + zm_eval env m b
  | ZMMul a b => zm_eval env m a * zm_eval env m b
  | ZMSub a b => zm_eval env m a - zm_eval env m b
  | ZMOpp a => - zm_eval env m a
  | ZMMod a => (zm_eval env m a) mod m
  end.

(** * strip_mod: remove all ZMMod nodes (pull direction).
    After strip_mod, the expression has no inner mods.
    The outer mod m is applied by the user. *)
Fixpoint strip_mod (e : ZMExpr) : ZMExpr :=
  match e with
  | ZMVar n => ZMVar n
  | ZMConst c => ZMConst c
  | ZMAdd a b => ZMAdd (strip_mod a) (strip_mod b)
  | ZMMul a b => ZMMul (strip_mod a) (strip_mod b)
  | ZMSub a b => ZMSub (strip_mod a) (strip_mod b)
  | ZMOpp a => ZMOpp (strip_mod a)
  | ZMMod a => strip_mod a   (* key: just drop the mod *)
  end.

(** * add_mod: wrap every operation with mod (push direction).
    Result: every sub-expression is reduced mod m. *)
Fixpoint add_mod (e : ZMExpr) : ZMExpr :=
  match e with
  | ZMVar n => ZMVar n       (* variables are already reduced *)
  | ZMConst c => ZMConst c
  | ZMAdd a b => ZMMod (ZMAdd (add_mod a) (add_mod b))
  | ZMMul a b => ZMMod (ZMMul (add_mod a) (add_mod b))
  | ZMSub a b => ZMMod (ZMSub (add_mod a) (add_mod b))
  | ZMOpp a => ZMMod (ZMOpp (add_mod a))
  | ZMMod a => ZMMod (add_mod a)
  end.

(** * Soundness: strip_mod preserves value mod m *)

(** Key lemma: for any sub-expression, stripping inner mods
    doesn't change the value mod m. *)
Lemma strip_mod_sound : forall env m e,
  (zm_eval env m (strip_mod e)) mod m = (zm_eval env m e) mod m.
Proof.
  intros env m e. induction e; simpl; try reflexivity.
  - (* ZMAdd: (strip a + strip b) mod m = (a + b) mod m *)
    rewrite Zplus_mod. rewrite IHe1, IHe2. rewrite <- Zplus_mod. reflexivity.
  - (* ZMMul *)
    rewrite Zmult_mod. rewrite IHe1, IHe2. rewrite <- Zmult_mod. reflexivity.
  - (* ZMSub *)
    rewrite Zminus_mod. rewrite IHe1, IHe2. rewrite <- Zminus_mod. reflexivity.
  - (* ZMOpp: (-strip a) mod m = (-a) mod m *)
    (* Use: (-x) mod m = (m - x mod m) mod m = (-(x mod m)) mod m
       So (-strip a) mod m = (-(strip a mod m)) mod m
                            = (-(a mod m)) mod m    [by IHe]
                            = (-a) mod m *)
    replace (- zm_eval env m (strip_mod e))%Z
      with (0 - zm_eval env m (strip_mod e))%Z by lia.
    replace (- zm_eval env m e)%Z
      with (0 - zm_eval env m e)%Z by lia.
    rewrite Zminus_mod. rewrite IHe. rewrite <- Zminus_mod. reflexivity.
  - (* ZMMod: strip_mod(ZMMod e) = strip_mod e,
       so goal is: strip_mod e mod m = (e mod m) mod m *)
    rewrite Zmod_mod. exact IHe.
Qed.

(** Soundness for add_mod (push direction) *)
Lemma add_mod_sound : forall env m e,
  (zm_eval env m (add_mod e)) mod m = (zm_eval env m e) mod m.
Proof.
  intros env m e. induction e; simpl; try reflexivity.
  - (* ZMAdd *)
    rewrite Zmod_mod.
    rewrite Zplus_mod. rewrite IHe1, IHe2. rewrite <- Zplus_mod. reflexivity.
  - (* ZMMul *)
    rewrite Zmod_mod.
    rewrite Zmult_mod. rewrite IHe1, IHe2. rewrite <- Zmult_mod. reflexivity.
  - (* ZMSub *)
    rewrite Zmod_mod.
    rewrite Zminus_mod. rewrite IHe1, IHe2. rewrite <- Zminus_mod. reflexivity.
  - (* ZMOpp *)
    rewrite Zmod_mod.
    replace (- zm_eval env m (add_mod e))%Z
      with (0 - zm_eval env m (add_mod e))%Z by lia.
    replace (- zm_eval env m e)%Z
      with (0 - zm_eval env m e)%Z by lia.
    rewrite Zminus_mod. rewrite IHe. rewrite <- Zminus_mod. reflexivity.
  - (* ZMMod: add_mod(ZMMod e) = ZMMod(add_mod e),
       goal: (add_mod e mod m) mod m = (e mod m) mod m *)
    rewrite !Zmod_mod. exact IHe.
Qed.

(** * Boolean equality check on ZMExpr *)
Fixpoint zm_eqb (a b : ZMExpr) : bool :=
  match a, b with
  | ZMVar n1, ZMVar n2 => Nat.eqb n1 n2
  | ZMConst c1, ZMConst c2 => Z.eqb c1 c2
  | ZMAdd a1 b1, ZMAdd a2 b2 => zm_eqb a1 a2 && zm_eqb b1 b2
  | ZMMul a1 b1, ZMMul a2 b2 => zm_eqb a1 a2 && zm_eqb b1 b2
  | ZMSub a1 b1, ZMSub a2 b2 => zm_eqb a1 a2 && zm_eqb b1 b2
  | ZMOpp a1, ZMOpp a2 => zm_eqb a1 a2
  | ZMMod a1, ZMMod a2 => zm_eqb a1 a2
  | _, _ => false
  end.

Lemma zm_eqb_eq : forall a b, zm_eqb a b = true -> a = b.
Proof.
  induction a; destruct b; simpl; intros H; try discriminate;
    try reflexivity.
  - apply Nat.eqb_eq in H. congruence.
  - apply Z.eqb_eq in H. congruence.
  - apply andb_true_iff in H. destruct H. f_equal; auto.
  - apply andb_true_iff in H. destruct H. f_equal; auto.
  - apply andb_true_iff in H. destruct H. f_equal; auto.
  - f_equal; auto.
  - f_equal; auto.
Qed.

(** * Main theorem: if strip_mod(LHS) = strip_mod(RHS) syntactically,
    then LHS mod m = RHS mod m *)
Theorem reflective_pull_Zmod : forall env m lhs rhs,
  zm_eqb (strip_mod lhs) (strip_mod rhs) = true ->
  zm_eval env m lhs mod m = zm_eval env m rhs mod m.
Proof.
  intros env m lhs rhs H.
  apply zm_eqb_eq in H.
  rewrite <- (strip_mod_sound env m lhs).
  rewrite <- (strip_mod_sound env m rhs).
  rewrite H. reflexivity.
Qed.

(** Variant for proving [X mod m = Y] when Y has no outer mod *)
Theorem reflective_pull_Zmod_l : forall env m lhs rhs,
  zm_eqb (strip_mod lhs) (strip_mod rhs) = true ->
  zm_eval env m lhs mod m = (zm_eval env m rhs) mod m.
Proof. exact reflective_pull_Zmod. Qed.

(** * Main theorem (push direction): if add_mod(strip_mod(LHS)) = add_mod(strip_mod(RHS))
    syntactically, then LHS mod m = RHS mod m.

    This is the push_Zmod analogue of reflective_pull_Zmod. We first strip any
    existing inner mods (so both sides are normalized to a mod-free core) and
    then push mods inward to every sub-operation. This makes the check succeed
    regardless of which side has explicit inner mods. *)
Theorem reflective_push_Zmod : forall env m lhs rhs,
  zm_eqb (add_mod (strip_mod lhs)) (add_mod (strip_mod rhs)) = true ->
  zm_eval env m lhs mod m = zm_eval env m rhs mod m.
Proof.
  intros env m lhs rhs H.
  apply zm_eqb_eq in H.
  rewrite <- (strip_mod_sound env m lhs).
  rewrite <- (strip_mod_sound env m rhs).
  rewrite <- (add_mod_sound env m (strip_mod lhs)).
  rewrite <- (add_mod_sound env m (strip_mod rhs)).
  rewrite H. reflexivity.
Qed.

(** Corollary: if RHS is already of the form [_ mod m], strip the outer mod *)
Corollary reflective_pull_Zmod_rmod : forall env m lhs inner_rhs,
  zm_eqb (strip_mod lhs) (strip_mod inner_rhs) = true ->
  zm_eval env m lhs mod m = zm_eval env m inner_rhs mod m.
Proof. exact reflective_pull_Zmod. Qed.

(** * Tactic support *)

(** For use in Ltac: check that strip_mod of two reified expressions
    are equal, then close the goal via reflective_pull_Zmod.

    Usage pattern:
      1. Reify LHS and RHS as ZMExpr (by Ltac matching)
      2. [change (LHS mod m = RHS mod m) with
           (zm_eval env m lhs_expr mod m = zm_eval env m rhs_expr mod m)]
      3. [apply reflective_pull_Zmod; vm_compute; reflexivity]
*)

(** Helper: strip_mod + structural equality is decidable *)
Definition pull_Zmod_check (lhs rhs : ZMExpr) : bool :=
  zm_eqb (strip_mod lhs) (strip_mod rhs).

Lemma pull_Zmod_check_sound : forall env m lhs rhs,
  pull_Zmod_check lhs rhs = true ->
  zm_eval env m lhs mod m = zm_eval env m rhs mod m.
Proof. exact reflective_pull_Zmod. Qed.

(** For reflexivity-style goals: [X mod m = X mod m] *)
(** These are trivially true but pull_Zmod is called on them anyway.
    The reflective version handles them in O(1). *)

(* No section — all definitions are top-level for maximum reusability. *)
