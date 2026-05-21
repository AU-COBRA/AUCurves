(** * BLS12-377 bedrock2 data extraction for Jasmin compilation.
 *
 * Mirrors [BLS12_381.v].  Extracts [bls377_all_jasmin : jasmin_func list]
 * — bedrock2 functions already translated via [tr_func_sized +
 * polish_func].  Output: [bls377_jasmin_extracted.ml] (lifted to
 * top-level Ocaml file in _build/default).
 *
 * Does NOT import [JasminBridge.BridgeReal] — that would pull in
 * mathcomp and trigger a universe inconsistency with
 * [Bedrock.Field.Synthesis.Examples.bls12_377_prime] (coqutil-based).
 *
 * Driver: [bls377_main.ml] (mirrors [bls12_main.ml]).
 *)

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_377_felem_copy.

Import bedrock2.Syntax.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bls377_fp_funcs : list function_t :=
  [ bls377_add; bls377_sub; bls377_mul; bls377_square;
    bls377_select_znz;
    ("bls377_felem_copy", bls377_felem_copy) ].

Definition bls377_field_size : Z := 6.

(** Pre-translate to [jasmin_func] in Rocq with [vm_compute] so
    typeclass-projected size constants reduce to literals. *)
Definition bls377_all_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bls377_field_size f))
             bls377_fp_funcs.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "bls377_jasmin_extracted"
  bls377_all_jasmin bls377_field_size
  pp_func pp_module.
