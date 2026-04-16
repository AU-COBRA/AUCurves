(** * Point negation for Jacobian coordinates: -(X:Y:Z) = (X:-Y:Z).

    Simply negates the Y coordinate using field opp.
    The bedrock2 function body is a single opp call. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section PointNegate.
  Context {field_parameters : FieldParameters}.

  (** The bedrock2 function body: calls opp(Yout, Yin) *)
  Definition point_negate_func : function_t :=
    ("point_negate", (["Yout"; "Yin"], []:list String.string,
      cmd.call [] opp [expr.var "Yout"; expr.var "Yin"])).

End PointNegate.

Section Spec.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Local Notation F := (F M_pos).

  (** Spec: negate Y to output pointer, preserving input *)
  Definition spec_of_point_negate (functions : map.rep) : Prop :=
    forall pYout pYin (Y Yold : F) R tr m,
      (FElem (Some tight_bounds) pYin Y
       * FElem (Some tight_bounds) pYout Yold * R)%sep m ->
      Semantics.call functions "point_negate" tr m [pYout; pYin]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
           (FElem (Some tight_bounds) pYin Y
            * FElem (Some tight_bounds) pYout (F.opp Y) * R)%sep m').

End Spec.

(** ** Algebraic property: negation flips the curve_add *)

Section Algebra.
  Context {F : Type} {Fzero Fone : F} {Fopp : F -> F}.
  Context {curve_add : F * F * F -> F * F * F -> F * F * F}.

  (** For projective Jacobian: curve_add P (negate Q) = curve_sub P Q *)
  (** The key property for wNAF: negative digits use negated table points *)
  Definition curve_negate (P : F * F * F) : F * F * F :=
    let '(X, Y, Z) := P in (X, Fopp Y, Z).

End Algebra.
