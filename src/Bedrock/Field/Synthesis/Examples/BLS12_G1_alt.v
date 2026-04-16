Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Group.CurveAdd.CurveAddAlt.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Coq.Strings.String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_G1.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_three_b.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.
Local Definition program_logic_goal_for (_ : function_t) (P : Prop) := P.
Local Notation "program_logic_goal_for_function! proc" :=
  (program_logic_goal_for proc True) (at level 10, only parsing).

Section bls12_G1_alt.

    Existing Instances
      Bitwidth64.BW64
      Defaults64.default_parameters
      Defaults64.default_parameters_ok
      bls12_field_parameters
      bls12_field_parameters_ok
      bls12_frep
      bls12_frep_ok.

    Local Notation F := (F M_pos).

    Definition G1_add_alt_func : function_t :=
      ("G1_add_alt", (["x1"; "x2"; "y1"; "y2"; "z1"; "z2"; "outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
        stackalloc felem_size_in_bytes as allocx1;
        stackalloc felem_size_in_bytes as allocx2;
        stackalloc felem_size_in_bytes as allocy1;
        stackalloc felem_size_in_bytes as allocy2;
        stackalloc felem_size_in_bytes as allocz1;
        stackalloc felem_size_in_bytes as allocz2;
        coq:(cmd.call [] (felem_copy) [expr.var ("allocx1"); expr.var ("x1")]);
        coq:(cmd.call [] (felem_copy) [expr.var ("allocx2"); expr.var ("x2")]);
        coq:(cmd.call [] (felem_copy) [expr.var ("allocy1"); expr.var ("y1")]);
        coq:(cmd.call [] (felem_copy) [expr.var ("allocy2"); expr.var ("y2")]);
        coq:(cmd.call [] (felem_copy) [expr.var ("allocz1"); expr.var ("z1")]);
        coq:(cmd.call [] (felem_copy) [expr.var ("allocz2"); expr.var ("z2")]);
        coq:(cmd.call [] ("curve_add") [expr.var ("allocx1"); expr.var ("allocx2"); expr.var ("allocy1"); expr.var("allocy2"); expr.var ("allocz1"); expr.var ("allocz2"); expr.var ("outx"); expr.var ("outy"); expr.var ("outz")])
      ))).

    Lemma bls12_G1_alt_ok : program_logic_goal_for_function! G1_add_alt_func.
    Proof. exact I. Qed.

End bls12_G1_alt.
