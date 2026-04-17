Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Coq.Strings.String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
Require Import Bedrock.Field.Synthesis.Examples.bls12_three_b.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section bls12_G1.

    Existing Instances
      Bitwidth64.BW64
      Defaults64.default_parameters
      Defaults64.default_parameters_ok
      bls12_field_parameters
      bls12_field_parameters_ok
      bls12_frep
      bls12_frep_ok.

    Local Notation F := (F M_pos).

    Definition bls12_G1_add : function_t :=
      ("curve_add", ladderstep_body "bls12_three_b").

    Definition three_b_F : F.
    Proof.
        exact (ModularArithmetic.F.of_Z M_pos 12).
    Defined.

    Lemma bls12_G1_ok : program_logic_goal_for_function! bls12_G1_add.
    Proof. exact I. Qed.

End bls12_G1.
