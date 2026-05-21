(** * BW6-761 bedrock2 data extraction for Jasmin compilation.
 *
 * Mirrors [BLS12_377.v].  Extracts [bw6_761_all_jasmin : jasmin_func list]
 * for the 12-limb BW6-761 outer-curve Fp leaves.
 *
 * Does NOT import [JasminBridge.BridgeReal] — that would pull in
 * mathcomp and trigger a universe inconsistency with
 * [Bedrock.Field.Synthesis.Examples.bw6_761_prime] (coqutil-based).
 *
 * Driver: [bw6_761_main.ml] (mirrors [bls377_main.ml]).
 *
 * NB: 12-limb Montgomery mul/square will likely hit the same
 * register-pressure blocker in jasminc that fails 6-limb bls377_mul.
 * add/sub/select_znz should still emit clean .s.
 *)

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.

Import bedrock2.Syntax.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Definition bw6_761_fp_funcs : list function_t :=
  [ bw6_761_add; bw6_761_sub; bw6_761_mul; bw6_761_square;
    bw6_761_select_znz ].

Definition bw6_761_field_size : Z := 12.

(** Pre-translate to [jasmin_func] in Rocq with [vm_compute] so
    typeclass-projected size constants reduce to literals. *)
Definition bw6_761_all_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized bw6_761_field_size f))
             bw6_761_fp_funcs.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "bw6_761_jasmin_extracted"
  bw6_761_all_jasmin bw6_761_field_size
  pp_func pp_module.
