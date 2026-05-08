(** * CmdAST — deep-AST mirror of [bedrock2.Syntax.cmd] for reflective WP.

    Phase 1 deliverable per [BEDROCK2_REFLECTIVE_PLAN.md].  Defines a
    1-to-1 deep mirror of [bedrock2.Syntax.cmd]'s 10 constructors and
    a [denote] function back to [cmd].

    No soundness theorem yet (phase 2).  No reify Ltac yet (phase 5).
    The point of this file is to lock in the AST shape and verify the
    universe / typeclass / opam-build interactions before we spend
    weeks on soundness.

    Why a separate Inductive when [cmd] is already an Inductive?  Two
    reasons:

      1. Allows [Strategy] / [Set Universe Polymorphism] / etc. tweaks
         that we may not want to apply to upstream [cmd].

      2. Future phases (3, 4) may extend the AST with semantic-level
         hints that don't have a [cmd] counterpart — e.g., a
         loop-invariant constructor that paniciffies the reify Ltac when
         a [Lemma] for the invariant isn't in scope.  Better to
         have a separate type so those extensions are obvious.

    For now [cmdAST] and [cmd] are isomorphic up to [denote].

    DESIGN NOTE.  Since this is phase 1 only, the deeper design
    choices (single AST vs per-shape; vm_compute strategy; reify path)
    are deferred to phase 2's soundness work.  Choices made here that
    are tentative:

      - [expr] is shared with [bedrock2.Syntax.expr] — we don't reify
        expressions because their evaluation is already tractable
        (they're not the bottleneck).  If phase 2 measures expr
        elaboration as a hot spot, revisit.
      - [access_size] is shared.  Same reasoning.
      - String identifiers (variable names, function names) are
        shared.  No reification needed; they're already first-class
        Coq values. *)

From Stdlib Require Import String List ZArith.
Require Import bedrock2.Syntax.

(** ** Mirror of [bedrock2.Syntax.cmd].

    Constructors are renamed [AST_*] to avoid shadowing.  Order and
    arity match [Syntax.cmd] exactly. *)
Inductive cmdAST : Set :=
| AST_skip
| AST_set        (lhs : String.string) (rhs : expr)
| AST_unset      (lhs : String.string)
| AST_store      (sz : access_size) (address : expr) (value : expr)
| AST_stackalloc (lhs : String.string) (nbytes : Z) (body : cmdAST)
| AST_cond       (condition : expr) (nonzero_branch zero_branch : cmdAST)
| AST_seq        (s1 s2 : cmdAST)
| AST_while      (test : expr) (body : cmdAST)
| AST_call       (binds : list String.string) (function : String.string) (args : list expr)
| AST_interact   (binds : list String.string) (action : String.string) (args : list expr).

(** ** Denotation [cmdAST → cmd].

    Trivial structural recursion: each [AST_*] maps to [cmd.*].  A
    fixpoint, not a notation, so [vm_compute] can step through it. *)
Fixpoint denote (a : cmdAST) : cmd :=
  match a with
  | AST_skip => cmd.skip
  | AST_set x e => cmd.set x e
  | AST_unset x => cmd.unset x
  | AST_store sz addr v => cmd.store sz addr v
  | AST_stackalloc x n body => cmd.stackalloc x n (denote body)
  | AST_cond c t f => cmd.cond c (denote t) (denote f)
  | AST_seq s1 s2 => cmd.seq (denote s1) (denote s2)
  | AST_while t body => cmd.while t (denote body)
  | AST_call binds f args => cmd.call binds f args
  | AST_interact binds a args => cmd.interact binds a args
  end.

(** ** Smoke test: [denote] of a simple AST gives back the expected
    [cmd]. *)
Module SmokeTest.

  Local Open Scope string_scope.
  Local Open Scope Z_scope.

  Definition example_AST : cmdAST :=
    AST_seq
      (AST_set "x" (expr.literal 42))
      (AST_skip).

  (** [denote example_AST] should reduce to [cmd.seq (cmd.set "x" 42) cmd.skip]
      via [cbv [denote]] / [vm_compute]. *)
  Goal denote example_AST = cmd.seq (cmd.set "x" (expr.literal 42)) cmd.skip.
  Proof. cbv [denote example_AST]. reflexivity. Qed.

  (** Same goal via [vm_compute] — confirms the fixpoint reduces under
      the bytecode VM (no opacity / typeclass interference). *)
  Goal denote example_AST = cmd.seq (cmd.set "x" (expr.literal 42)) cmd.skip.
  Proof. vm_compute. reflexivity. Qed.

End SmokeTest.

(** ** Phase 1 result line.

    Build status: pending (this file is the deliverable).
    Soundness theorem: NOT proven (phase 2).
    Reify Ltac: NOT defined (phase 5).
    R10 wired: NO (phases 6+).

    Validation criterion (from plan): "File builds Qed-clean."
    The two [Goal]s in [SmokeTest] additionally verify that [denote]
    reduces under both [cbv] and [vm_compute] — early signal that
    phase 2's soundness theorem won't immediately hit a typeclass /
    opacity wall. *)
