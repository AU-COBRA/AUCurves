(** Quick test of ToSafeRustBody on Fp2 functions. *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Require Import Bedrock.ToSafeRustBody.
Require Import Bedrock.Field.Synthesis.Examples.bn254_Fp2.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition test_fp2_add : string :=
  Eval vm_compute in
    safe_rust_func 4 [TFp2; TFp2; TFp2] Fp2_add.

Definition test_fp2_mul : string :=
  Eval vm_compute in
    safe_rust_func 4 [TFp2; TFp2; TFp2] Fp2_mul.

Definition test_fp2_sqr : string :=
  Eval vm_compute in
    safe_rust_func 4 [TFp2; TFp2] Fp2_sqr.

Redirect "test_safe_body.out" Eval vm_compute in
  (safe_type_decls 4 ++ test_fp2_add ++ test_fp2_mul ++ test_fp2_sqr).
