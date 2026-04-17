Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_from_list_F.
Require Import Bedrock.Group.CurveAdd.StorePointAtInfinity.

     (* Require Import bedrock2.Syntax. *)
     (* Require Import compiler.MMIO. *)

     Require Import compiler.Pipeline.
     From bedrock2 Require Import ToCString Bytedump.

     Require Import bedrock2.Syntax.
     Require Import compiler.MMIO.
     Definition funcs : list func :=
       [ bls12_select_znz].

     Compute compile (compile_ext_call (funname_env:=SortedListString.map)) (map.of_list funcs).
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Open Scope sep_scope.

          Definition from_list_func : Syntax.func := ("store_zero_F", (["out"], (nil : list string), bedrock_func_body:(
                coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_b_mont 0));
                coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_b_mont 0))
              ))).

     Definition from_list_func : Syntax.func :=
       ("store_zero_F",
         (["out"],
           (nil : list string),
           bedrock_func_body:
           (coq:(cmd.store access_size.word (expr.var "out") (expr.literal (nth 0 three_b_mont 0)));
            coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (8))) (nth 1 three_b_mont 0));
            coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (16))) (nth 2 three_b_mont 0));
            coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (24))) (nth 3 three_b_mont 0));
            coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (32))) (nth 4 three_b_mont 0));
            coq:(cmd.store access_size.word (expr.op bopname.add (expr.var "out") (expr.literal (40))) (nth 5 three_b_mont 0))
       ))).

        Definition store_zero_func : bedrock2.Syntax.func :=
        ("store_zero", (["outx"; "outy"; "outz"], []:list String.string, bedrock_func_body:(
                coq:(cmd.call [] "store_zero_F" [expr.var ("outx")]);
                coq:(cmd.call [] "store_one_F" [expr.var ("outy")]);
                coq:(cmd.call [] "store_zero_F" [expr.var ("outz")])
        ))).

        From bedrock2 Require Import ToCString Bytedump.
        Definition c_mod := (c_module (store_zero_func:: nil)).
     (* Definition mul_fun := Eval vm_compute in (bls12_mul). *)
     (* Definition mul_fun := Eval vm_compute in (bls12_mul). *)
     Definition c_test :=
       Eval vm_compute in
         c_module (bls12_add
                     :: bls12_sub
                     :: bls12_mul
                     :: bls12_from_list
                     :: bls12_G1_add
                     :: nil).
     Eval cbv in c_test.

     (* Local Open Scope bytedump_scope. *)
     (* Import Syntax BinInt String List.ListNotations. *)
     (* Local Open Scope string_scope. *)
     (* Local Open Scope Z_scope. *)
     (* Local Open Scope list_scope. *)
