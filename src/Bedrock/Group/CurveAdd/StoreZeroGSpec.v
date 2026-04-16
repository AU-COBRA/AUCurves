Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.ScalarsUtil.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Arithmetic.WordByWordMontgomeryUtil.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.

Section __.

      Context {width : Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
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
            {field_representation_ok : FieldRepresentation_ok}
            {group_cmov : string}
            {store_zero : string}.

    Local Notation F := (F M_pos).
    Local Notation Fzero := (F.of_Z M_pos 0).
    Local Notation Fone := (F.of_Z M_pos 1).

      Instance spec_of_store_zero : spec_of "store_zero_G" :=
      fnspec! "store_zero_G"
            (pX pY pZ: word)
            / (X Y Z : F) R,
      { requires tr mem :=
            (FElem (Some tight_bounds) pX X
            * FElem (Some tight_bounds) pY Y
            * FElem (Some tight_bounds) pZ Z * R)%sep mem;
            ensures tr' mem' :=
                  (FElem (Some tight_bounds) pX Fzero
            * FElem (Some tight_bounds) pY Fone
            * FElem (Some tight_bounds) pZ Fzero * R)%sep mem'}.

End __.
