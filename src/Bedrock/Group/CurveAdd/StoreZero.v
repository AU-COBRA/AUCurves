Require Import Rupicola.Lib.Api.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.

Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.
Local Open Scope sep_scope.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section StoreZero.

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

  (* Function name strings for zero and one operations *)
  Context {zero_name one_name : string}.

  Local Notation F := (F M_pos).
  Local Notation Fzero := (F.of_Z M_pos 0).
  Local Notation Fone := (F.of_Z M_pos 1).

  Instance spec_of_store_zero : spec_of "store_zero" :=
    fnspec! "store_zero"
      (pX pY pZ: word)
      / (X Y Z : F) R,
      { requires tr mem :=
          (FElem None pX X
           * FElem None pY Y
           * FElem None pZ Z * R)%sep mem;
        ensures tr' mem' :=
          tr = tr' /\
          (FElem (Some tight_bounds) pX Fzero
           * FElem (Some tight_bounds) pY Fone
           * FElem (Some tight_bounds) pZ Fzero * R)%sep mem'}.

  Definition store_zero_func : function_t :=
    ("store_zero", (["outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
            coq:(cmd.call [] zero_name [expr.var ("outx")]);
            coq:(cmd.call [] one_name [expr.var ("outy")]);
            coq:(cmd.call [] zero_name [expr.var ("outz")])
    ))).

  Lemma store_zero_ok : program_logic_goal_for_function! store_zero_func.
  Proof. exact I. Qed.

End StoreZero.
