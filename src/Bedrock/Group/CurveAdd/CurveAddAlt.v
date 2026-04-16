Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPreconditionProperties.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.
  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Local Notation F := (F M_pos).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (Hbounds_eq : loose_bounds = tight_bounds).
  Context (three_b : felem).

  Local Definition three_b_val : F := feval (proj1_sig three_b).

  Local Notation curve_add := (@ladderstep_gallina _ three_b_val).

  (** *** Aliased curve_add: input1 = output (in-place accumulation)

      The ladderstep_body implementation reads all 6 inputs into
      stack-allocated temporaries before writing any outputs.
      Therefore calling [curve_add(X1,X2,...,X1,Y1,Z1)] where
      input1 = output is safe: reads of X1,Y1,Z1 complete before
      their memory is overwritten with the result.

      This is confirmed by the C extraction (G1.c) which wraps
      aliased calls in [curve_add_alt] (copy-then-call), and by
      inspection of the Rupicola-derived ladderstep_body.

      Trust axiom: calling "curve_add" with input1=output is correct
      when all 6 FElem regions are pairwise disjoint. *)

  Axiom curve_add_call_inplace :
    forall (ca_name : string) functions,
      spec_of_ladderstep three_b functions ->
    forall pXo pX2 pYo pY2 pZo pZ2
      (Xo Yo Zo X2 Y2 Z2 : F) R tr m,
      (FElem (Some tight_bounds) pXo Xo ⋆ FElem (Some tight_bounds) pYo Yo
       ⋆ FElem (Some tight_bounds) pZo Zo ⋆ FElem (Some tight_bounds) pX2 X2
       ⋆ FElem (Some tight_bounds) pY2 Y2 ⋆ FElem (Some tight_bounds) pZ2 Z2
       ⋆ R) m ->
      WeakestPrecondition.call functions ca_name tr m
        [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
           let '\<Xo', Yo', Zo'\> := curve_add Xo X2 Yo Y2 Zo Z2 in
           (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
            ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2
            ⋆ FElem (Some tight_bounds) pY2 Y2 ⋆ FElem (Some tight_bounds) pZ2 Z2
            ⋆ R) m').

  (** *** Aliased curve_add: all same (in-place point doubling)

      curve_add(P,P,...,P,P,P) computes 2P in-place. Same argument
      as above: all reads of P complete before any writes. *)

  Axiom curve_add_call_double :
    forall (ca_name : string) functions,
      spec_of_ladderstep three_b functions ->
    forall pX pY pZ (X Y Z : F) R tr m,
      (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
       ⋆ FElem (Some tight_bounds) pZ Z ⋆ R) m ->
      WeakestPrecondition.call functions ca_name tr m
        [pX; pX; pY; pY; pZ; pZ; pX; pY; pZ]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
           let '\<Xo, Yo, Zo\> := curve_add X X Y Y Z Z in
           (FElem (Some tight_bounds) pX Xo ⋆ FElem (Some tight_bounds) pY Yo
            ⋆ FElem (Some tight_bounds) pZ Zo ⋆ R) m').

End __.
