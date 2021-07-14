(** Compatibility file for making Coq act similar to Coq v8.8 *)
Local Set Warnings "-deprecated".

Require Export Coq.Compat.Coq89.

(** In Coq 8.9, prim token notations follow [Import] rather than
    [Require].  So we make all of the relevant notations accessible in
    compatibility mode. *)
Require Coq.Strings.Ascii Coq.Strings.String.
Export String.StringSyntax Ascii.AsciiSyntax.
Require Coq.ZArith.BinIntDef Coq.PArith.BinPosDef Coq.NArith.BinNatDef.
Require Coq.Reals.Rdefinitions.
Declare ML Module "r_syntax_plugin".
Numeral Notation BinNums.Z BinIntDef.Z.of_int BinIntDef.Z.to_int : Z_scope.
Numeral Notation BinNums.positive BinPosDef.Pos.of_int BinPosDef.Pos.to_int : positive_scope.
Numeral Notation BinNums.N BinNatDef.N.of_int BinNatDef.N.to_int : N_scope.
