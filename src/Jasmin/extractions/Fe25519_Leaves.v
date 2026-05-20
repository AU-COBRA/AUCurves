(** * Fe25519_Leaves: extract the 5 fe25519 leaf [_prog]s directly to
 *    OCaml for end-to-end Jasmin compilation.
 *
 *  Direct AST-target path (no .jazz text rendering required).
 *  Mirror of [BLS12_381.v] / [X25519_64.v] but for the rust_cmd_ed
 *  pipeline: each leaf's [wrap_prog] composition lands a Jasmin
 *  [_prog] that can be fed straight into Jasmin's OCaml compilation
 *  entry point (Ocaml_compile.compile_funcs after Obj.magic at the
 *  structurally-identical type boundary, same trick as the existing
 *  ast_bridge_driver.ml).
 *)

From HB Require Import structures.
From Jasmin Require Import expr x86_instr_decl x86_extra arch_extra.
From mathcomp Require Import ssreflect ssrfun ssrnat seq.
From Stdlib Require Import ZArith String List.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
Import ListNotations.

Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdEdToRealJasmin.
Require Import Bedrock.Jasmin.Core.
Require Import JasminBridge.RealJasminInstance.
Require Import JasminBridge.BridgeReal.
Require Import JasminBridge.WrapFundef.

Require Import Bedrock.End2End.Ed25519.Fe25519MulBody.
Require Import Bedrock.End2End.Ed25519.Fe25519AddSubBody.
Require Import Bedrock.End2End.Ed25519.Fe25519SquareBody.
Require Import Bedrock.End2End.Ed25519.Fe25519Scmula24Body.

#[local] Existing Instance atoI | 0.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Standard 40-byte slots for fe25519 leaves                     *)
(* ================================================================ *)

Definition out_slot : located_ed := {| loc_var := "out"; loc_type := TBytes 40 |}.
Definition x_slot   : located_ed := {| loc_var := "x";   loc_type := TBytes 40 |}.
Definition y_slot   : located_ed := {| loc_var := "y";   loc_type := TBytes 40 |}.

Definition p_off_concrete : nat -> Z := fun _ => 0%Z.

(* ================================================================ *)
(* §2. Per-leaf programs                                             *)
(*                                                                  *)
(* Each [_prog] is built by composing the rust_cmd_ed body through  *)
(* [rust_cmd_ed_to_real_jasmin] and wrapping in a function via      *)
(* [WrapFundef.wrap_prog].                                          *)
(* ================================================================ *)

Definition fe25519_mul_prog :=
  Eval vm_compute in
    wrap_prog "fe25519_mul" out_slot [x_slot; y_slot]
      (rust_cmd_ed_to_real_jasmin (fe25519_mul_body out_slot [x_slot; y_slot])).

Definition fe25519_add_prog :=
  Eval vm_compute in
    wrap_prog "fe25519_add" out_slot [x_slot; y_slot]
      (rust_cmd_ed_to_real_jasmin (fe25519_add_body out_slot [x_slot; y_slot])).

Definition fe25519_sub_prog :=
  Eval vm_compute in
    wrap_prog "fe25519_sub" out_slot [x_slot; y_slot]
      (rust_cmd_ed_to_real_jasmin (fe25519_sub_body p_off_concrete out_slot [x_slot; y_slot])).

Definition fe25519_square_prog :=
  Eval vm_compute in
    wrap_prog "fe25519_square" out_slot [x_slot]
      (rust_cmd_ed_to_real_jasmin (fe25519_square_body out_slot [x_slot])).

Definition fe25519_scmula24_prog :=
  Eval vm_compute in
    wrap_prog "fe25519_scmula24" out_slot [x_slot]
      (rust_cmd_ed_to_real_jasmin (fe25519_scmula24_body out_slot [x_slot])).

(* ================================================================ *)
(* §3. Aggregated list for the OCaml driver                          *)
(* ================================================================ *)

(** All 5 leaves as a single list of (funname, fundef) pairs,
    matching the shape Jasmin's compile entry expects.  Type
    annotation elided to dodge the [seq]-vs-[ssrnat] resolution
    collision; Rocq infers it from the components. *)
Definition fe25519_all_jasmin :=
  (p_funcs fe25519_mul_prog ++
   p_funcs fe25519_add_prog ++
   p_funcs fe25519_sub_prog ++
   p_funcs fe25519_square_prog ++
   p_funcs fe25519_scmula24_prog)%list.

(* ================================================================ *)
(* §4. OCaml extraction                                              *)
(* ================================================================ *)

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "fe25519_leaves_jasmin_extracted"
  fe25519_mul_prog
  fe25519_add_prog
  fe25519_sub_prog
  fe25519_square_prog
  fe25519_scmula24_prog
  fe25519_all_jasmin.
