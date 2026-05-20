(** * ExtractFe25519Scmula24Real: drive [fe25519_scmula24] through
 *    [rust_cmd_ed_to_real_jasmin] to a real Jasmin [expr.cmd] AST.
 *
 *  Companion to [ExtractFe25519MulReal.v].  Scalar multiplication by
 *  the Curve25519 constant a24 = 121665 (used in the Montgomery
 *  ladder).  Phase A is 5 limbwise [SLit * SLimb] products + reduce.
 *  Aliasing dest=a is disallowed (see Fe25519Scmula24Body header).
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
Require Import Bedrock.End2End.Ed25519.Fe25519Scmula24Body.
Require Import JasminBridge.RealJasminInstance.

Import ListNotations.
Local Open Scope string_scope.

Definition fe25519_scmula24_concrete : SafeRustEd25519Sim.rust_cmd_ed :=
  fe25519_scmula24_body
    {| loc_var := "out"; loc_type := TBytes 40 |}
    [ {| loc_var := "x"; loc_type := TBytes 40 |} ].

Definition fe25519_scmula24_real :
  list (@instr x86_extended_op asm_opI) :=
  rust_cmd_ed_to_real_jasmin fe25519_scmula24_concrete.

Definition fe25519_scmula24_real_normalised :
  list (@instr x86_extended_op asm_opI) :=
  Eval vm_compute in fe25519_scmula24_real.

Redirect "fe25519_scmula24_real_jasmin_ast"
  Print fe25519_scmula24_real_normalised.
