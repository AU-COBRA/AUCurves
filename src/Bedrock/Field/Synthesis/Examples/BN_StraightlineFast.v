(** * Performance-optimized straightline for BN proofs.

    The standard [bedrock2.ProgramLogic.straightline_cleanup] uses
    [progress (cbn [Semantics.interp_binop] in * )] which re-normalizes
    every hypothesis on each call. With ~30+ separation logic hypotheses,
    this is the dominant cost in long WP proofs.

    [Semantics.interp_binop] only appears in the GOAL during straightline
    (it's introduced by unfolding cmd bodies). It does NOT appear in
    hypotheses. So we can safely change [in *] to just operate on the goal.

    This file overrides [straightline_cleanup] with the optimized version.
    Import it AFTER bedrock2.ProgramLogic to enable the optimization. *)

Require Import bedrock2.ProgramLogic.
Require Import bedrock2.Semantics.
Require Import bedrock2.Syntax.
Require Import coqutil.Map.Interface.

(* Override straightline_cleanup with the goal-only cbn.

   Key change from the original: [progress (cbn [Semantics.interp_binop])]
   instead of [progress (cbn [Semantics.interp_binop] in * )].

   Why this is safe: [Semantics.interp_binop] is a constant introduced by
   bedrock2 cmd evaluation. It appears in the GOAL when [cmd_body] is
   unfolded. It does NOT appear in the user's hypotheses (FElem, sep,
   bounds, etc.). The [in *] caused every [straightline_cleanup] call to
   re-normalize all 20-30 sep hypotheses, which dominates large WP proofs.

   Why the original used [in *]: defensive programming, in case some user
   has [interp_binop] in a hypothesis. For our codebase, it doesn't. *)
Ltac straightline_cleanup ::=
  match goal with
  | x : Word.Interface.word.rep _ |- _ => clear x
  | x : Init.Byte.byte |- _ => clear x
  | x : Semantics.trace |- _ => clear x
  | x : Syntax.cmd |- _ => clear x
  | x : Syntax.expr |- _ => clear x
  | x : coqutil.Map.Interface.map.rep |- _ => clear x
  | x : BinNums.Z |- _ => clear x
  | x : unit |- _ => clear x
  | x : bool |- _ => clear x
  | x : list _ |- _ => clear x
  | x : nat |- _ => clear x
  | x := _ : Word.Interface.word.rep _ |- _ => clear x
  | x := _ : Init.Byte.byte |- _ => clear x
  | x := _ : Semantics.trace |- _ => clear x
  | x := _ : Syntax.cmd |- _ => clear x
  | x := _ : Syntax.expr |- _ => clear x
  | x := _ : coqutil.Map.Interface.map.rep |- _ => clear x
  | x := _ : BinNums.Z |- _ => clear x
  | x := _ : unit |- _ => clear x
  | x := _ : bool |- _ => clear x
  | x := _ : list _ |- _ => clear x
  | x := _ : nat |- _ => clear x
  | |- forall _, _ => intros
  | |- let _ := _ in _ => intros
  | |- dlet.dlet ?v (fun x => ?P) => change (let x := v in P); intros
  | _ => progress (cbn [Semantics.interp_binop])
  | H: exists _, _ |- _ => destruct H
  | H: _ /\ _ |- _ => destruct H
  | x := ?y |- ?G => is_var y; subst x
  | H: ?x = ?y |- _ => constr_eq x y; clear H
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [x] in x in idtac); subst x
  | H: ?x = ?y |- _ => is_var x; is_var y; assert_fails (idtac; let __ := eval cbv [y] in y in idtac); subst y
  | H: ?x = ?v |- _ =>
    is_var x;
    assert_fails (idtac; let __ := eval cbv delta [x] in x in idtac);
    lazymatch v with context[x] => fail | _ => idtac end;
    let x' := fresh x in
    rename x into x';
    simple refine (let x := v in _);
    change (x' = x) in H;
    symmetry in H;
    destruct H
  end.
