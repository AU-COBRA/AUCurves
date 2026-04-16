(** * OCaml extraction of the ToJasmin translator + FlattenStackalloc.
 *
 *    **STATUS (2026-04-14): DEPRECATED — text-based extraction surface.**
 *    Exposes [pp_func]/[pp_module]/[to_jasmin]/[to_jasmin_sized] (the
 *    unverified text path).  For verified extraction, drivers should
 *    instead extract [JasminBridgeReal.to_jasmin_cmd] (AST → AST);
 *    see [ExtractBLS12JasminAST.v] / [ExtractBN254FullJasminAST.v]
 *    for the pattern.  Kept for differential testing / AST debugging.
 *    See [feedback_tojasmin_ast_path.md]. *)

From Coq Require Export Extraction.
From Coq Require Export ExtrOcamlBasic.
From Coq Require Export ExtrOcamlString.
From Coq Require Export ExtrOcamlZInt.
From Stdlib Require Import ZArith String Ascii.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Jasmin.FlattenStackalloc.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

(* Use ExtrOcamlZInt for native Z/positive/nat *)
(* Use ExtrOcamlString for native string/ascii *)
(* These are the standard Rocq extraction remappings *)

Extraction "to_jasmin_extracted"
  tr_func tr_func_sized pp_func pp_module to_jasmin to_jasmin_sized
  flatten_stackallocs flatten_func flatten_selected.
