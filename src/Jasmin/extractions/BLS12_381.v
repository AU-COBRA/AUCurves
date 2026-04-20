(** * BLS12-381 bedrock2 data extraction for Jasmin compilation.
 *
 * Extracts [bls12_all_jasmin : jasmin_func list] — bedrock2 functions
 * already translated via [tr_func_sized + polish_func].  Output:
 * [bls12_jasmin_extracted.ml].
 *
 * Does NOT import [JasminBridge.BridgeReal] — that would pull in
 * mathcomp and trigger a universe inconsistency with
 * [Bedrock.Field.Synthesis.Examples.bls12_prime] (coqutil-based).
 *
 * The [to_jasmin_cmd] translator is extracted separately (see
 * [src/Jasmin/extractions/Bridge.v]) and combined with this data via
 * the ~30-line OCaml shim [ocaml/ast_bridge_main.ml].
 *)

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDouble.
Require Import Bedrock.Group.CurveAdd.PointNegate.
Require Import Bedrock.Group.CurveAdd.CurveAddInplaceWrapper.

Import bedrock2.Syntax.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bls12_fp_funcs : list function_t :=
  [ bls12_add; bls12_sub; bls12_mul; bls12_square;
    bls12_select_znz;
    ("bls12_felem_copy", bls12_felem_copy) ].

Definition bls12_field_size : Z := 6.

(** Pre-translate to [jasmin_func] in Rocq with [vm_compute] so
    typeclass-projected size constants reduce to literals. *)
Definition bls12_all_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bls12_field_size f))
             bls12_fp_funcs.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "bls12_jasmin_extracted"
  bls12_all_jasmin bls12_field_size
  pp_func pp_module.
