(** * Jasmin bridge extraction — the [to_jasmin_cmd] translator.
 *
 * Extracts [JasminBridge.BridgeReal.to_jasmin_cmd] (and its helpers)
 * into OCaml.  Output: [bridge_extracted.ml].
 *
 * Separate from curve-specific extractions (BLS12_381.v, X25519_64.v)
 * because combining [JasminBridge.BridgeReal] with any fiat-crypto
 * curve synthesis triggers the coqutil/mathcomp universe inconsistency.
 *
 * The OCaml shim [ocaml/ast_bridge_main.ml] combines this extraction
 * with a curve extraction using [Obj.magic] at the structurally
 * identical [jasmin_cmd] type boundary.
 *)

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
From Stdlib Require Import Uint63.
Import ListNotations.

Require Import JasminBridge.BridgeReal.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "bridge_extracted"
  to_jasmin_cmd
  to_pexpr
  string_to_ident
  mk_var_from_string
  mk_lval_from_string.
