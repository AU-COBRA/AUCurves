(** * ExtractEvalDemo — side-by-side eval of the three emit paths.
 *
 * Emits the same demo program through:
 *   1. [RustCmdToC.demo_direct]      — direct C from rust_cmd_ed
 *   2. [RustCmdToC.demo_via_bedrock] — bedrock2 ToCString from rust_cmd_ed
 *   3. [RustCmdToRust]               — direct Rust from rust_cmd_ed
 *
 * Strip leading [= "..."] and trailing [": string"] for clean output.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.RustCmdToC.
Require Import Bedrock.RustCmdToRust.
Import ListNotations.
Local Open Scope string_scope.

Redirect "demo_direct_c"     Eval vm_compute in demo_direct.
Redirect "demo_via_bedrock_c" Eval vm_compute in demo_via_bedrock.

(** Tiny demo via Rust path — same demo_rs as in RustCmdToC. *)
Definition demo_rs_func_sig : RustCmdToRust.rs_func_sig :=
  {| rfs_name := "demo_fn"; rfs_params := [("msg", TBytes 32)] |}.

Definition demo_rust : string :=
  rs_func_emit demo_rs_func_sig demo_rs.

Redirect "demo_direct_rs" Eval vm_compute in demo_rust.
