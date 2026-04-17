(** * Extract the complete BLS12-377 pairing pipeline to C. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import bedrock2.Syntax.

Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_377_Pairing.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Base Fp functions *)
Definition fp_base_funcs : list function_t :=
  [ bls377_add; bls377_sub; bls377_mul; bls377_square;
    bls377_select_znz;
    ("bls377_felem_copy", bls377_felem_copy) ].

(** Combined: Fp base + pairing pipeline *)
Definition all_funcs : list function_t :=
  fp_base_funcs ++ BLS12_377_Pairing.bls377_all_pairing_funcs.

Definition all_c :=
  Eval vm_compute in c_module all_funcs.

Redirect "bls377_pairing_all" Eval cbv in all_c.
