(** This is required in Coq 8.5 to use the [omega] tactic; in Coq 8.4, it's automatically available.  But ZArith_base puts infix ~ at level 7, and we don't want that, so we don't [Import] it. *)
Require Coq.omega.Omega.
Ltac omega := Coq.omega.Omega.omega.

(** The number of arguments given in [match] statements has changed from 8.4 to 8.5. *)
Global Set Asymmetric Patterns.

(** See bug 3545 *)
Global Set Universal Lemma Under Conjunction.

(** In 8.4, [admit] created a new axiom; in 8.5, it just shelves the goal. *)
Axiom proof_admitted : False.
Ltac admit := clear; abstract case proof_admitted.

(** In 8.5, [refine] leaves over dependent subgoals. *)
Tactic Notation "refine" uconstr(term) := refine term; shelve_unifiable.

(** In 8.4, [constructor (tac)] allowed backtracking across the use of [constructor]; it has been subsumed by [constructor; tac]. *)
Ltac constructor_84 := constructor.
Ltac constructor_84_n n := constructor n.
Ltac constructor_84_tac tac := once (constructor; tac).

Tactic Notation "constructor" := constructor_84.
Tactic Notation "constructor" int_or_var(n) := constructor_84_n n.
Tactic Notation "constructor" "(" tactic(tac) ")" := constructor_84_tac tac.

(** Many things now import [PeanoNat] rather than [NPeano], so we require it so that the old absolute names in [NPeano.Nat] are available. *)
Require Coq.Numbers.Natural.Peano.NPeano.
