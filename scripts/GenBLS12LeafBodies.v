From Stdlib Require Import String List ZArith.
Require Import bedrock2.Syntax.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Definition body (f : string * (list string * list string * cmd)) := let '(_, (_, _, b)) := f in b.
Definition add_body := Eval vm_compute in body bls12_add.
Definition sub_body := Eval vm_compute in body bls12_sub.
Definition mul_body := Eval vm_compute in body bls12_mul.
Definition square_body := Eval vm_compute in body bls12_square.
Set Printing Width 100000.
Set Printing Depth 100000000.
Unset Printing Notations.
Redirect "add_body" Print add_body.
Redirect "sub_body" Print sub_body.
Redirect "mul_body" Print mul_body.
Redirect "square_body" Print square_body.
