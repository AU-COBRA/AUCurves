(** * ExtractCurveBodies — emit Rust strings for the decomposed curve
 *    leaves from [curve_function_table].
 *
 *  Five entries are extracted as Rust functions via [rs_body_extract]:
 *    1. xyzt_add_decomposed        (out: [u8;200], P1, P2: [u8;200])
 *    2. xyzt_double_decomposed     (out: [u8;200], P:  [u8;200])
 *    3. scalarmult_decomposed      (out: [u8;200], scalar:[u8;32], P:[u8;200])
 *    4. scalarmult_base_decomposed (out: [u8;200], scalar:[u8;32])
 *    5. xyzt_copy                  (out: [u8;200], src: [u8;200])
 *
 *  Companion to ExtractEd25519CmdRs.v.  The output file [curve_bodies_rs.out]
 *  is post-processed by the curve25519-jasmin-rs build to strip the
 *  surrounding [= "..." : string] wrapper and dropped into
 *  src/ed25519_rustcmd/decomposed_bodies.rs.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdToRust.
Require Import Bedrock.End2End.Ed25519.XyztAddBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.XyztDoubleBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.ScalarmultBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.ScalarmultBaseBodyDecomposed.
Require Import Bedrock.End2End.Ed25519.XyztCopyBody.
Import ListNotations.
Local Open Scope string_scope.

Definition curve_bodies_extract_sigs : list body_extract_sig :=
  [ {| bes_name      := "xyzt_add_decomposed";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 200; TBytes 200];
       bes_body      := xyzt_add_body_decomposed |} ;
    {| bes_name      := "xyzt_double_decomposed";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 200];
       bes_body      := xyzt_double_body_decomposed |} ;
    {| bes_name      := "scalarmult_decomposed";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 32; TBytes 200];
       bes_body      := scalarmult_body_decomposed |} ;
    {| bes_name      := "scalarmult_base_decomposed";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 32];
       bes_body      := scalarmult_base_body_decomposed |} ;
    {| bes_name      := "xyzt_copy";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 200];
       bes_body      := xyzt_copy_body |} ].

Definition curve_bodies_rs_string : string :=
  rs_table_extract curve_bodies_extract_sigs.

Redirect "curve_bodies_rs" Eval vm_compute in curve_bodies_rs_string.
