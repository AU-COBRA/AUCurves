(** * Extract the complete BN446 pairing pipeline to C. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import bedrock2.Syntax.

Require Import Bedrock.Field.Synthesis.Examples.bn446_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn446_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BN446_Pairing.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Base Fp functions *)
Definition fp_base_funcs : list function_t :=
  [ bn446_add; bn446_sub; bn446_mul; bn446_square;
    bn446_select_znz;
    ("bn446_felem_copy", bn446_felem_copy) ].

(** Combined: Fp base + pairing pipeline *)
Definition all_funcs : list function_t :=
  fp_base_funcs ++ BN446_Pairing.bn446_all_pairing_funcs.

Definition all_c :=
  Eval vm_compute in c_module all_funcs.

Redirect "bn446_pairing_all" Eval cbv in all_c.
