(** * ExtractFe25519SubReal: drive [fe25519_sub] through
 *    [rust_cmd_ed_to_real_jasmin] to a real Jasmin [expr.cmd] AST.
 *
 *  Companion to [ExtractFe25519AddReal.v].  5-limb radix-2^51 sub chain
 *  with the [p_off] offset trick from fiat-crypto's
 *  [fiat_25519_sub] (subtract from a multiple of p to keep limbs
 *  non-negative).  Uses the concrete [p_off = fun _ => 0]
 *  instantiation from [Fe25519FiatInstantiation.v].
 *)

From HB Require Import structures.
From Jasmin Require Import expr x86_instr_decl x86_extra arch_extra.
From mathcomp Require Import ssreflect ssrfun ssrnat seq.
From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.

Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.RustCmdEdToRealJasmin.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.End2End.Ed25519.Fe25519AddSubBody.
Require Import JasminBridge.RealJasminInstance.

Import ListNotations.
Local Open Scope string_scope.

(** Zero-offset p_off, matching [Fe25519FiatInstantiation.p_off_concrete]. *)
Local Definition p_off_concrete : nat -> Z := fun _ => 0%Z.

Definition fe25519_sub_concrete : SafeRustEd25519Sim.rust_cmd_ed :=
  fe25519_sub_body p_off_concrete
    {| loc_var := "out"; loc_type := TBytes 40 |}
    [ {| loc_var := "x"; loc_type := TBytes 40 |};
      {| loc_var := "y"; loc_type := TBytes 40 |} ].

Definition fe25519_sub_real :
  list (@instr x86_extended_op asm_opI) :=
  rust_cmd_ed_to_real_jasmin fe25519_sub_concrete.

Definition fe25519_sub_real_normalised :
  list (@instr x86_extended_op asm_opI) :=
  Eval vm_compute in fe25519_sub_real.

Redirect "fe25519_sub_real_jasmin_ast"
  Print fe25519_sub_real_normalised.
