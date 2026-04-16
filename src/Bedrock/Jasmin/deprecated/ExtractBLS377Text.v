(** * OCaml extraction of the BLS12-377 Fp function list for Jasmin.
 *    Mirrors ExtractBLS12Jasmin.v for the 377 curve.
 *
 *    **STATUS (2026-04-14): DEPRECATED — text-based extraction.**
 *    Uses [pp_module] (unverified pretty-printer).  Migrate to the
 *    AST path (model: [ExtractBLS12JasminAST.v]) which calls
 *    [JasminBridgeReal.to_jasmin_cmd] for verified end-to-end output.
 *    See [feedback_tojasmin_ast_path.md].
 *)

From Stdlib Require Export Extraction ExtrOcamlBasic ExtrOcamlString.
From Stdlib Require Import ZArith String Ascii.
Require Import bedrock2.Syntax.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Crypto.Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.
Require Import Bedrock.Jasmin.Core.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bls377_fp_base_funcs : list function_t :=
  [ bls377_add; bls377_sub; bls377_mul; bls377_square;
    bls377_select_znz;
    ("bls377_felem_copy", bls377_felem_copy) ].

Definition bls377_all_funcs : list function_t :=
  Eval vm_compute in bls377_fp_base_funcs.

Definition bls377_field_size : Z := 6.

Definition bls377_all_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bls377_field_size f))
             bls377_all_funcs.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "bls377_jasmin_extracted"
  bls377_all_jasmin bls377_field_size pp_func pp_module.
