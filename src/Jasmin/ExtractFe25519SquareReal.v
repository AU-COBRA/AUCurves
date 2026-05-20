(** * ExtractFe25519SquareReal: drive [fe25519_square] through
 *    [rust_cmd_ed_to_real_jasmin] to a real Jasmin [expr.cmd] AST.
 *
 *  Companion to [ExtractFe25519MulReal.v].  5-limb radix-2^51 square
 *  with the same algebra as fiat-crypto's [fiat_25519_carry_square].
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
Require Import Bedrock.End2End.Ed25519.Fe25519SquareBody.
Require Import JasminBridge.RealJasminInstance.

Import ListNotations.
Local Open Scope string_scope.

Definition fe25519_square_concrete : SafeRustEd25519Sim.rust_cmd_ed :=
  fe25519_square_body
    {| loc_var := "out"; loc_type := TBytes 40 |}
    [ {| loc_var := "x"; loc_type := TBytes 40 |} ].

Definition fe25519_square_real :
  list (@instr x86_extended_op asm_opI) :=
  rust_cmd_ed_to_real_jasmin fe25519_square_concrete.

Definition fe25519_square_real_normalised :
  list (@instr x86_extended_op asm_opI) :=
  Eval vm_compute in fe25519_square_real.

Redirect "fe25519_square_real_jasmin_ast"
  Print fe25519_square_real_normalised.
