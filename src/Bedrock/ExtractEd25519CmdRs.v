(** * ExtractEd25519CmdRs: emit safe Rust strings for ed25519_sign /
 *    ed25519_verify (built from rust_cmd_ed via [rs_func_emit]).
 *
 * Emits two .out artifacts:
 *
 *   ed25519_sign_rs.out
 *   ed25519_verify_rs.out
 *
 * Strip the leading [= "..."] and trailing [": string"] to obtain
 * .rs files.
 *)

From Stdlib Require Import Strings.String.
Require Import Bedrock.RustCmdToRust.

Redirect "ed25519_sign_rs"   Eval vm_compute in ed25519_sign_rs_string.
Redirect "ed25519_verify_rs" Eval vm_compute in ed25519_verify_rs_string.
