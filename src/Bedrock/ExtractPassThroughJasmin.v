(** * ExtractPassThroughJasmin: PoC extraction of the four pass-through
 *                              ed25519 curve bodies to jasmin_cmd.
 *
 *  Step (a) of the Option C ladder in
 *  [docs/jasmin-extraction-progress.md]: clone the
 *  [ExtractXyztCopyJasmin.v] pattern across the four other trivial
 *  pass-through bodies (each a single [REdCall] to its corresponding
 *  fe25519 leaf):
 *
 *    - [xyzt_add_body]            → JCcall "fe25519_xyzt_add"        [out; P; Q]
 *    - [xyzt_double_body]         → JCcall "fe25519_xyzt_double"     [out; P]
 *    - [scalarmult_body]          → JCcall "fe25519_scalarmult"      [out; scalar; P]
 *    - [scalarmult_base_body]     → JCcall "fe25519_scalarmult_base" [out; scalar]
 *
 *  Each AST-shape claim is discharged by [vm_compute; reflexivity].
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdEdToJasmin.
Require Import Bedrock.Jasmin.Core.
Require Import Bedrock.End2End.Ed25519.XyztAddBody.
Require Import Bedrock.End2End.Ed25519.XyztDoubleBody.
Require Import Bedrock.End2End.Ed25519.ScalarmultBody.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseBody.
Import ListNotations.
Local Open Scope string_scope.

(* ================================================================ *)
(* §1. Concrete instantiations                                       *)
(* ================================================================ *)

Definition xyzt_add_jasmin_cmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin
    (xyzt_add_body
       {| loc_var := "out"; loc_type := TBytes 200 |}
       [{| loc_var := "P"; loc_type := TBytes 200 |};
        {| loc_var := "Q"; loc_type := TBytes 200 |}]).

Definition xyzt_double_jasmin_cmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin
    (xyzt_double_body
       {| loc_var := "out"; loc_type := TBytes 200 |}
       [{| loc_var := "P"; loc_type := TBytes 200 |}]).

Definition scalarmult_jasmin_cmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin
    (scalarmult_body
       {| loc_var := "out"; loc_type := TBytes 200 |}
       [{| loc_var := "scalar"; loc_type := TBytes 32 |};
        {| loc_var := "P";      loc_type := TBytes 200 |}]).

Definition scalarmult_base_jasmin_cmd : jasmin_cmd :=
  rust_cmd_ed_to_jasmin
    (scalarmult_base_body
       {| loc_var := "out"; loc_type := TBytes 200 |}
       [{| loc_var := "scalar"; loc_type := TBytes 32 |}]).

(* ================================================================ *)
(* §2. Closed-form AST-shape claims                                  *)
(* ================================================================ *)

Example xyzt_add_jasmin_cmd_value :
  xyzt_add_jasmin_cmd
    = JCcall "fe25519_xyzt_add"
        [JEvar "out"; JEvar "P"; JEvar "Q"].
Proof. vm_compute; reflexivity. Qed.

Example xyzt_double_jasmin_cmd_value :
  xyzt_double_jasmin_cmd
    = JCcall "fe25519_xyzt_double"
        [JEvar "out"; JEvar "P"].
Proof. vm_compute; reflexivity. Qed.

Example scalarmult_jasmin_cmd_value :
  scalarmult_jasmin_cmd
    = JCcall "fe25519_scalarmult"
        [JEvar "out"; JEvar "scalar"; JEvar "P"].
Proof. vm_compute; reflexivity. Qed.

Example scalarmult_base_jasmin_cmd_value :
  scalarmult_base_jasmin_cmd
    = JCcall "fe25519_scalarmult_base"
        [JEvar "out"; JEvar "scalar"].
Proof. vm_compute; reflexivity. Qed.

(* ================================================================ *)
(* §3. Pretty-printed dumps (deprecated pp_cmd, for inspection only) *)
(* ================================================================ *)

Definition all_passthrough_jazz : string :=
  pp_cmd "  " xyzt_add_jasmin_cmd ++ LF ++
  pp_cmd "  " xyzt_double_jasmin_cmd ++ LF ++
  pp_cmd "  " scalarmult_jasmin_cmd ++ LF ++
  pp_cmd "  " scalarmult_base_jasmin_cmd.

Definition all_passthrough_jazz_normalised : string :=
  Eval vm_compute in all_passthrough_jazz.

Redirect "passthrough_jasmin" Print all_passthrough_jazz_normalised.
