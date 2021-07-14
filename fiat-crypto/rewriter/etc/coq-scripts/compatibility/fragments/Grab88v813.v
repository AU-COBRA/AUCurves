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
Declare ML Module "int63_syntax_plugin".
Numeral Notation BinNums.Z BinIntDef.Z.of_int BinIntDef.Z.to_int : Z_scope.
Numeral Notation BinNums.positive BinPosDef.Pos.of_int BinPosDef.Pos.to_int : positive_scope.
Numeral Notation BinNums.N BinNatDef.N.of_int BinNatDef.N.to_int : N_scope.
Numeral Notation Int31.int31 Int31.phi_inv_nonneg Int31.phi : int31_scope.
