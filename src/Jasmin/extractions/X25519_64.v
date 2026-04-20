(** * OCaml extraction of X25519-64 as a list of polished [jasmin_func].
 *
 *    Same pattern as [ExtractBLS12Jasmin.v] but for our X25519-64
 *    Montgomery ladder:
 *    - [funcs] is the bedrock2 function list from [MontgomeryLadder64.v]
 *    - [polish_func (tr_func_sized 5 _)] lifts to polished [jasmin_func]
 *    - [Extraction] emits [x25519_64_jasmin_extracted.ml] with
 *      [x25519_64_all_jasmin : jasmin_func list] (structurally identical
 *      to BLS12's [bls12_all_jasmin], consumed by [compile_direct.ml]
 *      or the AST-to-AST driver).
 *
 *    Deliberately does NOT import [JasminBridgeReal] — that would pull
 *    in Jasmin's mathcomp stack and trigger the universe inconsistency
 *    with coqutil (see [project_unipoly_rebuild.md]).  The verified
 *    translation [to_jasmin_cmd] is extracted separately (from
 *    [JasminBridgeReal.v]) and bridged to this extraction by the
 *    ~30-line [Obj.magic] shim in [ast2ast_driver.ml]. *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
From Stdlib Require Import ZArith String Ascii.
Require Import bedrock2.Syntax.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.End2End.X25519_64.MontgomeryLadder64.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** X25519 uses 5 u64 limbs (unsaturated Solinas, 2^255 - 19). *)
Definition x25519_64_field_size : Z := 5.

(** Step 1: bedrock2 [funcs] → polished [jasmin_func] list.
    [vm_compute] reduces every typeclass-projected size to a literal
    Z so [stackalloc] args become concrete limb counts — same reason
    as [bls12_all_jasmin] in [ExtractBLS12Jasmin.v]. *)
Definition x25519_64_all_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized x25519_64_field_size f))
             funcs.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "x25519_64_jasmin_extracted"
  x25519_64_all_jasmin x25519_64_field_size
  pp_func pp_module.
