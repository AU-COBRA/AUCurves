(** * BN254 Jasmin extraction — base Fp only (4 u64 limbs).
 *    Tests whether 4-limb mul/square fits in jasminc's 16 registers.
 *
 *    **STATUS (2026-04-14): DEPRECATED — text-based extraction.**
 *    Uses [pp_module] / [to_jasmin_sized] (the unverified text path).
 *    The verified BN254 extraction lives in [ExtractBN254FullJasminAST.v]
 *    and routes via [JasminBridgeReal.to_jasmin_cmd] (AST → AST).
 *    See [feedback_tojasmin_ast_path.md]. *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
From Stdlib Require Import ZArith String Ascii.
Require Import bedrock2.Syntax.

Require Import Bedrock.Field.Synthesis.Examples.bn254_prime.
Require Import Bedrock.Field.Synthesis.Examples.bn254_felem_copy.
Require Import Bedrock.Jasmin.Core.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bn254_fp_funcs : list function_t :=
  [ bn254_add; bn254_sub; bn254_mul; bn254_square;
    bn254_select_znz;
    ("bn254_felem_copy", bn254_felem_copy) ].

Definition bn254_all_funcs : list function_t :=
  Eval vm_compute in bn254_fp_funcs.

Definition bn254_field_size : Z := 4.

Definition bn254_all_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bn254_field_size f))
             bn254_all_funcs.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "bn254_jasmin_extracted"
  bn254_all_jasmin bn254_field_size pp_func pp_module.
