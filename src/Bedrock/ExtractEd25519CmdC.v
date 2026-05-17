(** * ExtractEd25519CmdC: emit C strings for ed25519_sign and
 *    ed25519_verify (built from rust_cmd_ed via [c_emit] + [c_func_emit]).
 *
 * Run this file to produce two .v.out artifacts containing the C
 * source.  Strip the leading [= "..."] and trailing [": string"] to
 * obtain valid .c files:
 *
 *   _build/default/src/Bedrock/ed25519_sign.v.out
 *   _build/default/src/Bedrock/ed25519_verify.v.out
 *)

From Stdlib Require Import Strings.String.
Require Import Bedrock.RustCmdToC.

Redirect "ed25519_sign"   Eval vm_compute in ed25519_sign_c.
Redirect "ed25519_verify" Eval vm_compute in ed25519_verify_c.
