(** See https://coq.inria.fr/bugs/show_bug.cgi?id=4319 for updates *)

(** Compatibility file for making Coq act similar to Coq v8.8 *)
Local Set Warnings "-deprecated".

Require Export Coq.Compat.Coq811.

Unset Private Polymorphic Universes.

(** Unsafe flag, can hide inconsistencies. *)
Global Unset Template Check.

(** In Coq 8.9, prim token notations follow [Import] rather than
    [Require].  So we make all of the relevant notations accessible in
    compatibility mode. *)
Require Coq.Strings.Ascii Coq.Strings.String.
Export String.StringSyntax Ascii.AsciiSyntax.
Require Coq.ZArith.BinIntDef Coq.PArith.BinPosDef Coq.NArith.BinNatDef.
Require Coq.Reals.Rdefinitions.
Require Coq.Numbers.Cyclic.Int63.Int63.
Require Coq.Numbers.Cyclic.Int31.Int31.
Declare ML Module "r_syntax_plugin".
Declare ML Module "int63_syntax_plugin".
Numeral Notation BinNums.Z BinIntDef.Z.of_int BinIntDef.Z.to_int : Z_scope.
Numeral Notation BinNums.positive BinPosDef.Pos.of_int BinPosDef.Pos.to_int : positive_scope.
Numeral Notation BinNums.N BinNatDef.N.of_int BinNatDef.N.to_int : N_scope.
Numeral Notation Int31.int31 Int31.phi_inv_nonneg Int31.phi : int31_scope.

(** [set (x := y)] is about 50x slower than it needs to be in Coq 8.4,
    but is about 4x faster than the alternatives in 8.5.  See
    https://coq.inria.fr/bugs/show_bug.cgi?id=3280 (comment 13) for
    more details. *)
Ltac fast_set' x y := set (x := y).
Ltac fast_set'_in x y H := set (x := y) in H.
Tactic Notation "fast_set" "(" ident(x) ":=" constr(y) ")" := fast_set' x y.
Tactic Notation "fast_set" "(" ident(x) ":=" constr(y) ")" "in" hyp(H) := fast_set'_in x y H.

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
Require Export Coq.funind.FunInd.
