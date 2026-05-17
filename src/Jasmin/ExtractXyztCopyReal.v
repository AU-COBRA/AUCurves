(** * ExtractXyztCopyReal: extract xyzt_copy through the
 *    `rust_cmd_ed_to_real_jasmin` composition to a *real* Jasmin
 *    [expr.cmd] AST.
 *
 *  Companion to [Bedrock.ExtractXyztCopyRealJasmin] but using the
 *  [RealJasmin] instance from [RealJasminInstance.v], so the output
 *  type is the real [Jasmin.expr.cmd] (i.e. [seq (instr ...)]).
 *)

From HB Require Import structures.
From Jasmin Require Import expr x86_instr_decl x86_extra arch_extra.
From mathcomp Require Import ssreflect ssrfun ssrnat seq.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.

Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.RustCmdEdToRealJasmin.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.End2End.Ed25519.XyztCopyBody.
Require Import JasminBridge.RealJasminInstance.

Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Concrete instantiation                                        *)
(* ================================================================ *)

Definition xyzt_copy_concrete : SafeRustEd25519Sim.rust_cmd_ed :=
  xyzt_copy_body
    {| loc_var := "dest"; loc_type := TBytes 200 |}
    [{| loc_var := "src"; loc_type := TBytes 200 |}].

(* ================================================================ *)
(* §2. Composition target — *real* Jasmin [expr.cmd]                 *)
(* ================================================================ *)

Definition xyzt_copy_real :
  list (@instr x86_extended_op asm_opI) :=
  rust_cmd_ed_to_real_jasmin xyzt_copy_concrete.

(* ================================================================ *)
(* §3. AST dump (sidecar file, vm-computed)                          *)
(* ================================================================ *)

Definition xyzt_copy_real_normalised :
  list (@instr x86_extended_op asm_opI) :=
  Eval vm_compute in xyzt_copy_real.

Redirect "xyzt_copy_real_jasmin_ast"
  Print xyzt_copy_real_normalised.
