Require Import Rupicola.Lib.Api.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Import Bedrock.Field.Synthesis.Examples.ArrayUtil.
Require Import Bedrock.Field.Synthesis.Examples.ScalarsUtil.
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
Require Import Crypto.Util.ZUtil.ModInv.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.

(* Compatibility shim: opam bedrock2 >=0.0.9 removed the name from func *)
Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section __.

    Existing Instances Defaults64.default_parameters
    Defaults64.default_parameters_ok.

    Existing Instance bls12_field_parameters.
    Existing Instance bls12_field_parameters_ok.
    Existing Instance bls12_frep.

    Local Notation F := (F M_pos).

    (*curve-defining parameter b*)
    Definition three_b := 1.
    Definition uw := (uweight 64).
    Definition n := felem_size_in_words.
    Definition three_b_list := Partition.partition uw n three_b.
    Definition word := BasicC64Semantics.word.

    (* Local m' definition to avoid dependency on Field.m' *)
    Definition m'_val := Z.modinv (- M) (2^64).

    Definition three_b_mont := Eval vm_compute in (@WordByWordMontgomery.to_montgomerymod 64 n M m'_val three_b_list).
    Definition three_b_words := List.map (@word.of_Z 64 word) three_b_mont.

    Definition store_zero_F_func : function_t := ("store_zero_F", (["out"], (nil : list string), bedrock_func_body:(
        coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) 0);
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) 0);
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) 0);
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) 0);
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) 0)
        ))).

    Definition store_one_F_func : function_t := ("store_one_F", (["out"], (nil : list string), bedrock_func_body:(
        coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_b_mont 0));
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_b_mont 0));
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_b_mont 0));
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_b_mont 0));
        coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_b_mont 0))
        ))).

    Definition store_zero_func : function_t :=
    ("store_zero_G", (["outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
            coq:(cmd.call [] "store_zero_F" [expr.var ("outx")]);
            coq:(cmd.call [] "store_one_F" [expr.var ("outy")]);
            coq:(cmd.call [] "store_zero_F" [expr.var ("outz")])
    ))).

End __.
