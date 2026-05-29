(** * Fe25519_Leaves: extract the 5 fe25519 leaf programs as
 *    [jasmin_func list] for the existing Ocaml_compile pipeline.
 *
 *  Refactored to use the bedrock2-Syntax IR path that
 *  Ocaml_compile.compile_funcs consumes (matches BLS12-381 /
 *  X25519_64 / Ed25519_Sign_Inlined pattern).
 *
 *  Pipeline per leaf:
 *      function_body_ed     (Fe25519*Body.v)
 *        ↓ instantiate with concrete TBytes 40 locals
 *      rust_cmd_ed
 *        ↓ to_bedrock_cmd                     (RustCmdToC.v, structural)
 *      bedrock2.Syntax.cmd
 *        ↓ build (name, (params, rets, cmd))
 *      function_t
 *        ↓ tr_func_sized 5 + polish_func      (Jasmin/Core.v)
 *      jasmin_func   ← consumed by Ocaml_compile.compile_funcs
 *
 *  The 5-limb size (radix-2^51 fe25519) is the same as X25519_64.v.
 *)

From Stdlib Require Import ZArith String List.
From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlString.
Require Import bedrock2.Syntax.

Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdToC.
Require Import Bedrock.Jasmin.Core.

Require Import Bedrock.End2End.Ed25519.Fe25519MulBody.
Require Import Bedrock.End2End.Ed25519.Fe25519AddSubBody.
Require Import Bedrock.End2End.Ed25519.Fe25519SquareBody.
Require Import Bedrock.End2End.Ed25519.Fe25519Scmula24Body.

Import BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Standard 40-byte slots for fe25519 leaves                     *)
(* ================================================================ *)

Definition out_slot : located_ed := {| loc_var := "out"; loc_type := TBytes 40 |}.
Definition x_slot   : located_ed := {| loc_var := "x";   loc_type := TBytes 40 |}.
Definition y_slot   : located_ed := {| loc_var := "y";   loc_type := TBytes 40 |}.

Definition p_off_concrete : nat -> Z := fun _ => 0%Z.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd))%type.

(* ================================================================ *)
(* §2. Per-leaf [function_t] via to_bedrock_cmd                       *)
(* ================================================================ *)

Definition fe25519_mul_func : function_t :=
  ("fe25519_mul",
   (["out"; "x"; "y"], []%list,
    to_bedrock_cmd (fe25519_mul_body out_slot [x_slot; y_slot]))).

Definition fe25519_add_func : function_t :=
  ("fe25519_add",
   (["out"; "x"; "y"], []%list,
    to_bedrock_cmd (fe25519_add_body out_slot [x_slot; y_slot]))).

Definition fe25519_sub_func : function_t :=
  ("fe25519_sub",
   (["out"; "x"; "y"], []%list,
    to_bedrock_cmd (fe25519_sub_body p_off_concrete out_slot [x_slot; y_slot]))).

Definition fe25519_square_func : function_t :=
  ("fe25519_square",
   (["out"; "x"], []%list,
    to_bedrock_cmd (fe25519_square_body out_slot [x_slot]))).

Definition fe25519_scmula24_func : function_t :=
  ("fe25519_scmula24",
   (["out"; "x"], []%list,
    to_bedrock_cmd (fe25519_scmula24_body out_slot [x_slot]))).

(** All 5 leaves; the OCaml driver iterates this list. *)
Definition fe25519_funcs : list function_t :=
  [ fe25519_mul_func; fe25519_add_func; fe25519_sub_func;
    fe25519_square_func; fe25519_scmula24_func ]%list.

(* ================================================================ *)
(* §3. Polished jasmin_func list (matches BLS12 / X25519_64 shape)   *)
(* ================================================================ *)

(** Fe25519 uses 5 u64 limbs (unsaturated radix-2^51, prime 2^255−19).
    [vm_compute] reduces typeclass-projected sizes to literal Z so
    stackalloc args become concrete limb counts. *)
Definition fe25519_field_size : Z := 5.

Definition fe25519_all_jasmin : list jasmin_func :=
  Eval vm_compute in
    List.map (fun f => polish_func (tr_func_sized fe25519_field_size f))
             fe25519_funcs.

(* ================================================================ *)
(* §4. OCaml extraction                                              *)
(* ================================================================ *)

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "fe25519_leaves_jasmin_extracted"
  fe25519_all_jasmin fe25519_field_size
  pp_func pp_module
  pp_func_nospill pp_module_nospill.
