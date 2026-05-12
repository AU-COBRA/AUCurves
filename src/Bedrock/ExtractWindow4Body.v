(** * ExtractWindow4Body — emit Rust string for the window-4
 *    variable-base scalarmult body from
 *    [Bedrock.End2End.Ed25519.Window4ScalarmultBody].
 *
 *  Sibling to [ExtractCurveBodies.v] but emits a separate file
 *  ([window4_body_rs.out]) so the base decomposed bodies stay in
 *  their current extraction artefact.
 *
 *  The output is post-processed by the curve25519-jasmin-rs build
 *  to strip the [= "..." : string] wrapper and dropped into
 *  src/ed25519_rustcmd/decomposed_bodies_window4.rs.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdToRust.
Require Import Bedrock.End2End.Ed25519.Window4ScalarmultBody.
Require Import Bedrock.End2End.Ed25519.Straus2MSMBody.
Import ListNotations.
Local Open Scope string_scope.

Definition window4_body_extract_sigs : list body_extract_sig :=
  [ {| bes_name      := "window4_scalarmult";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 32; TBytes 200];
       bes_body      := window4_scalarmult_body |} ;
    {| bes_name      := "straus_2msm";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 32; TBytes 32; TBytes 200; TBytes 200];
       bes_body      := straus_2msm_body |} ].

Definition window4_body_rs_string : string :=
  rs_table_extract window4_body_extract_sigs.

Redirect "window4_body_rs" Eval vm_compute in window4_body_rs_string.
