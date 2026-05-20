(** * ExtractFe25519MulReal: drive [fe25519_mul] through
 *    [rust_cmd_ed_to_real_jasmin] to a real Jasmin [expr.cmd] AST.
 *
 *  Companion to [ExtractXyztCopyReal.v].  Whereas xyzt_copy is a
 *  200-byte memcpy leaf with ~0 perf impact, [fe25519_mul] is the
 *  hottest field op in the X25519/Ed25519 stack — driving it through
 *  the proven Rocq → Jasmin bridge swaps a libjade `.jazz` source
 *  for one emitted by [BridgeReal] + [Qed], reducing the TCB on
 *  every fe25519_mul callsite (~250 per Ed25519 sign).
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
Require Import Bedrock.End2End.Ed25519.Fe25519MulBody.
Require Import JasminBridge.RealJasminInstance.

Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Concrete instantiation                                        *)
(*                                                                  *)
(* fe25519_mul takes three 40-byte (5x u64) limb slots: out, x, y.   *)
(* TBytes 40 mirrors the byte-ABI choice the rest of the framework  *)
(* uses for fe25519 in xyzt slots; if the limb-ABI [TArr U64 5] is  *)
(* preferred, swap accordingly.                                     *)
(* ================================================================ *)

Definition fe25519_mul_concrete : SafeRustEd25519Sim.rust_cmd_ed :=
  fe25519_mul_body
    {| loc_var := "out"; loc_type := TBytes 40 |}
    [ {| loc_var := "x"; loc_type := TBytes 40 |};
      {| loc_var := "y"; loc_type := TBytes 40 |} ].

(* ================================================================ *)
(* §2. Composition target — *real* Jasmin [expr.cmd]                 *)
(* ================================================================ *)

Definition fe25519_mul_real :
  list (@instr x86_extended_op asm_opI) :=
  rust_cmd_ed_to_real_jasmin fe25519_mul_concrete.

(* ================================================================ *)
(* §3. AST dump (sidecar file, vm-computed)                          *)
(* ================================================================ *)

Definition fe25519_mul_real_normalised :
  list (@instr x86_extended_op asm_opI) :=
  Eval vm_compute in fe25519_mul_real.

Redirect "fe25519_mul_real_jasmin_ast"
  Print fe25519_mul_real_normalised.
