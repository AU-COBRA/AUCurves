(** * Extract the complete BN254 pairing pipeline to C. *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
Require Import bedrock2.ToCString.
Require Import bedrock2.Syntax.

Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Bedrock.Field.FieldExtensions.QuadraticFieldExtensions.
Require Import Bedrock.Field.Synthesis.Examples.BN254_Pairing.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Local Open Scope list_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

(** Base Fp functions *)
Definition fp_base_funcs : list function_t :=
  [ bn254_add; bn254_sub; bn254_mul; bn254_square;
    bn254_select_znz;
    ("bn254_felem_copy", bn254_felem_copy) ].

(** Combined: Fp base + pairing pipeline. Fp2/Fp6/Fp12 base ops are
    already inside [bn254_all_pairing_funcs] (via the Fp6/Fp12
    factories), matching the BN256/BN446 pattern. *)
Definition all_funcs : list function_t :=
  fp_base_funcs ++ BN254_Pairing.bn254_all_pairing_funcs.

Definition all_c :=
  Eval vm_compute in c_module all_funcs.

Redirect "bn254_pairing_all" Eval cbv in all_c.
