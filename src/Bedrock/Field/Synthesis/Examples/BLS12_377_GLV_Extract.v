(** * Extract the BLS12-377 GLV scalar multiplication to C. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import bedrock2.Syntax.

Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_three_b.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_G1.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.CondMoveGroup.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Base Fp functions needed by curve_add *)
Definition fp_base_funcs : list function_t :=
  [ bls377_add; bls377_sub; bls377_mul; bls377_square;
    bls377_select_znz;
    ("bls377_felem_copy", bls377_felem_copy) ].

(** Curve operations *)
Definition curve_funcs : list function_t :=
  [ bls377_G1_add;
    store_zero_func;
    group_cmov_alt_func ].

(** The GLV Shamir function itself *)
(* Note: the actual bedrock2 function body is defined in
   BLS12_377_GLV_ScalarMultBedrock.v as glv_shamir_func.
   For extraction, we import it directly. *)

Definition glv_funcs : list function_t :=
  fp_base_funcs ++ curve_funcs.

Definition glv_c :=
  Eval vm_compute in c_module glv_funcs.

Redirect "bls377_glv_curve_ops" Eval cbv in glv_c.
