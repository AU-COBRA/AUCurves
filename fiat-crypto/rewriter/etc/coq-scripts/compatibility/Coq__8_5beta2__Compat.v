(** See https://coq.inria.fr/bugs/show_bug.cgi?id=4319 for updates *)

(** [set (x := y)] is about 50x slower than it needs to be in Coq 8.4,
    but is about 4x faster than the alternatives in 8.5.  See
    https://coq.inria.fr/bugs/show_bug.cgi?id=3280 (comment 13) for
    more details. *)
Ltac fast_set' x y := set (x := y).
Ltac fast_set'_in x y H := set (x := y) in H.
Tactic Notation "fast_set" "(" ident(x) ":=" constr(y) ")" := fast_set' x y.
Tactic Notation "fast_set" "(" ident(x) ":=" constr(y) ")" "in" hyp(H) := fast_set'_in x y H.

(** https://coq.inria.fr/bugs/show_bug.cgi?id=4461 *)
Require Coq.Classes.RelationClasses.
Global Arguments Coq.Classes.RelationClasses.Antisymmetric A eqA {_} _.
Global Arguments Coq.Classes.RelationClasses.symmetry {A} {R} {_} [x] [y] _.
Global Arguments Coq.Classes.RelationClasses.asymmetry {A} {R} {_} [x] [y] _ _.
Global Arguments Coq.Classes.RelationClasses.transitivity {A} {R} {_} [x] [y] [z] _ _.

Require Coq.Program.Tactics.
Ltac rapply term := Coq.Program.Tactics.rapply term; shelve_unifiable.

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

(** Add Coq 8.4+8.5 notations, so that we don't accidentally make use of Coq 8.4-only notations *)
Require Coq.Lists.List.
Require Coq.Vectors.Vector.
Module Export LocalListNotations.
Notation " [ ] " := nil (format "[ ]") : list_scope.
Notation " [ x ; .. ; y ] " := (cons x .. (cons y nil) ..) : list_scope.
Notation " [ x ; y ; .. ; z ] " := (cons x (cons y .. (cons z nil) ..)) : list_scope.
End LocalListNotations.
Module Export LocalVectorNotations.
Notation " [ ] " := (Vector.nil _) (format "[ ]") : vector_scope.
Notation " [ x ; .. ; y ] " := (Vector.cons _ x _ .. (Vector.cons _ y _ (Vector.nil _)) ..) : vector_scope.
Notation " [ x ; y ; .. ; z ] " := (Vector.cons _ x _ (Vector.cons _ y _ .. (Vector.cons _ z _ (Vector.nil _)) ..)) : vector_scope.
End LocalVectorNotations.

Require Coq.Arith.Even.

Require Coq.FSets.FMapFacts.

Require Coq.ZArith.Int.
Module Export Coq.

Module Export Numbers.
Module Export Natural.
Module Export Peano.
Module NPeano.
Export Coq.Numbers.Natural.Peano.NPeano.
Import Coq.Arith.Even.
Notation leb := Nat.leb (compat "8.4").
Notation ltb := Nat.ltb (compat "8.4").
Notation leb_le := Nat.leb_le (compat "8.4").
Notation ltb_lt := Nat.ltb_lt (compat "8.4").
Notation pow := Nat.pow (compat "8.4").
Notation pow_0_r := Nat.pow_0_r (compat "8.4").
Notation pow_succ_r := Nat.pow_succ_r (compat "8.4").
Notation square := Nat.square (compat "8.4").
Notation square_spec := Nat.square_spec (compat "8.4").
Notation Even := Nat.Even (compat "8.4").
Notation Odd := Nat.Odd (compat "8.4").
Notation even := Nat.even (compat "8.4").
Notation odd := Nat.odd (compat "8.4").
Notation even_spec := Nat.even_spec (compat "8.4").
Notation odd_spec := Nat.odd_spec (compat "8.4").

Lemma Even_equiv n : Even n <-> Even.even n.
Proof. symmetry. apply Even.even_equiv. Qed.
Lemma Odd_equiv n : Odd n <-> Even.odd n.
Proof. symmetry. apply Even.odd_equiv. Qed.

Notation divmod := Nat.divmod (compat "8.4").
Notation div := Nat.div (compat "8.4").
Notation modulo := Nat.modulo (compat "8.4").
Notation divmod_spec := Nat.divmod_spec (compat "8.4").
Notation div_mod := Nat.div_mod (compat "8.4").
Notation mod_bound_pos := Nat.mod_bound_pos (compat "8.4").
Notation sqrt_iter := Nat.sqrt_iter (compat "8.4").
Notation sqrt := Nat.sqrt (compat "8.4").
Notation sqrt_iter_spec := Nat.sqrt_iter_spec (compat "8.4").
Notation sqrt_spec := Nat.sqrt_spec (compat "8.4").
Notation log2_iter := Nat.log2_iter (compat "8.4").
Notation log2 := Nat.log2 (compat "8.4").
Notation log2_iter_spec := Nat.log2_iter_spec (compat "8.4").
Notation log2_spec := Nat.log2_spec (compat "8.4").
Notation log2_nonpos := Nat.log2_nonpos (compat "8.4").
Notation gcd := Nat.gcd (compat "8.4").
Notation divide := Nat.divide (compat "8.4").
Notation gcd_divide := Nat.gcd_divide (compat "8.4").
Notation gcd_divide_l := Nat.gcd_divide_l (compat "8.4").
Notation gcd_divide_r := Nat.gcd_divide_r (compat "8.4").
Notation gcd_greatest := Nat.gcd_greatest (compat "8.4").
Notation testbit := Nat.testbit (compat "8.4").
Notation shiftl := Nat.shiftl (compat "8.4").
Notation shiftr := Nat.shiftr (compat "8.4").
Notation bitwise := Nat.bitwise (compat "8.4").
Notation land := Nat.land (compat "8.4").
Notation lor := Nat.lor (compat "8.4").
Notation ldiff := Nat.ldiff (compat "8.4").
Notation lxor := Nat.lxor (compat "8.4").
Notation double_twice := Nat.double_twice (compat "8.4").
Notation testbit_0_l := Nat.testbit_0_l (compat "8.4").
Notation testbit_odd_0 := Nat.testbit_odd_0 (compat "8.4").
Notation testbit_even_0 := Nat.testbit_even_0 (compat "8.4").
Notation testbit_odd_succ := Nat.testbit_odd_succ (compat "8.4").
Notation testbit_even_succ := Nat.testbit_even_succ (compat "8.4").
Notation shiftr_spec := Nat.shiftr_spec (compat "8.4").
Notation shiftl_spec_high := Nat.shiftl_spec_high (compat "8.4").
Notation shiftl_spec_low := Nat.shiftl_spec_low (compat "8.4").
Notation div2_bitwise := Nat.div2_bitwise (compat "8.4").
Notation odd_bitwise := Nat.odd_bitwise (compat "8.4").
Notation div2_decr := Nat.div2_decr (compat "8.4").
Notation testbit_bitwise_1 := Nat.testbit_bitwise_1 (compat "8.4").
Notation testbit_bitwise_2 := Nat.testbit_bitwise_2 (compat "8.4").
Notation land_spec := Nat.land_spec (compat "8.4").
Notation ldiff_spec := Nat.ldiff_spec (compat "8.4").
Notation lor_spec := Nat.lor_spec (compat "8.4").
Notation lxor_spec := Nat.lxor_spec (compat "8.4").

Infix "<=?" := Nat.leb (at level 70) : nat_scope.
Infix "<?" := Nat.ltb (at level 70) : nat_scope.
Infix "^" := Nat.pow : nat_scope.
Infix "/" := Nat.div : nat_scope.
Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.
Notation "( x | y )" := (Nat.divide x y) (at level 0) : nat_scope.
End NPeano.
End Peano.
End Natural.
End Numbers.

Module Export FSets.
Module FMapFacts.
Import Coq.FSets.FMapFacts.
Module WFacts_fun (E:DecidableType)(Import M:WSfun E).
  Notation option_map := option_map (compat "8.4").
  Module Coq_FSets_FMapFacts_WFacts_fun := Coq.FSets.FMapFacts.WFacts_fun E M.
  Include Coq_FSets_FMapFacts_WFacts_fun.
End WFacts_fun.
Module WFacts (M:WS) := WFacts_fun M.E M.
Module Facts := WFacts.
End FMapFacts.
End FSets.

Module Export ZArith.
  Module Int.
    Module Z_as_Int.
      Include Coq.ZArith.Int.Z_as_Int.
      Notation plus := Coq.ZArith.Int.Z_as_Int.add (only parsing).
      Notation minus := Coq.ZArith.Int.Z_as_Int.sub (only parsing).
      Notation mult := Coq.ZArith.Int.Z_as_Int.mul (only parsing).
    End Z_as_Int.
  End Int.
End ZArith.
End Coq.
