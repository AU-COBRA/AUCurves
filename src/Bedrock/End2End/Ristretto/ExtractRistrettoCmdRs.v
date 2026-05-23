(** * ExtractRistrettoCmdRs — emit safe Rust strings for the
 *    ristretto255 decode + encode bodies (built from [rust_cmd_ed]
 *    via [rs_func_emit]).
 *
 * Mirrors [src/Bedrock/ExtractEd25519CmdRs.v] for the ristretto255
 * decode/encode pair.  Emits two .out artifacts:
 *
 *   ristretto_decode_rs.out
 *   ristretto_encode_rs.out
 *
 * Strip the leading [= "..."] and trailing [: string] to obtain the
 * Rust source files; place them at:
 *
 *   curve25519-jasmin-rs/src/ristretto_rustcmd/decode.rs
 *   curve25519-jasmin-rs/src/ristretto_rustcmd/encode.rs
 *
 * The destination directory and the public surface of the Rust
 * module are already in place — see
 * [curve25519-jasmin-rs/src/ristretto_rustcmd/mod.rs] for the
 * stubs that will be replaced by the emitted files, and the
 * [curve25519-jasmin-rs/tests/ristretto_rfc9496_kat.rs] for the
 * 24-vector RFC 9496 §A.2 + §A.1 KAT suite that validates them.
 *
 * Status (2026-05-22):
 *   - The extractor calls [rs_func_emit] on
 *     [ristretto_decode_rs] from
 *     [Bedrock.End2End.Ristretto.Ristretto_RustCmd].
 *   - Currently that AST is a STUB ([REdSkip]) pending the
 *     Gallina-driven [compile_step] extension (file
 *     [RustCmdRupicolaGallina.v]).  The emitted .out files
 *     therefore contain a trivial 1-line Rust function.
 *   - When the real AST lands via the [Derive] block in
 *     [Ristretto_RustCmd.v], this file's [vm_compute] produces a
 *     non-trivial decoder body — no code change here.
 *
 * Build: included in the [Bedrock] dune theory by [(:standard)].
 * The [.out] artifacts are produced under [_build/default/src/Bedrock/]
 * during compilation via [Redirect].
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.RustCmdToRust.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.End2End.Ristretto.Ristretto_RustCmd.
Import ListNotations.
Local Open Scope string_scope.

(** ** [ristretto_decode_rs_sig] — Rust signature record.
 *
 *  The parameter names MUST match the variable names used inside
 *  [ristretto_decode_rs]'s [REdCall] arguments — otherwise the
 *  emitted Rust references unbound identifiers.  The current
 *  expected names (per [spec_of_ed_ristretto_decode] in
 *  [Ristretto_RustCmd.v]) are "bs_var" (input bytes) and "out_var"
 *  (200-byte xyzt output).
 *
 *  The Rust signature emitted is:
 *
 *    fn ristretto_decode(bs_var: *const u8, out_var: *mut u8) { ... }
 *
 *  with the caller-supplied buffer pointers threaded through the
 *  [REdCall] arguments.  Slot lengths are encoded in [TBytes].
 *)
Definition ristretto_decode_rs_sig : rs_func_sig :=
  {| rfs_name := "ristretto_decode";
     rfs_params := [("bs_var",  TBytes 32);
                    ("out_var", TBytes 200)] |}.

(** ** [ristretto_decode_rs_string] — fully-rendered Rust source.

    [rs_prelude] adds the `#![allow(...)]` header + the FFI
    `unsafe extern "C" { ... }` block for declared callees.  The
    callees that ristretto_decode invokes are auto-collected by
    [rs_func_emit] by walking the AST. *)
Definition ristretto_decode_rs_string : string :=
  rs_prelude ++ rs_func_emit ristretto_decode_rs_sig ristretto_decode_rs.

(** ** Emit the .out artifact via Redirect.

    [vm_compute] reduces the [rs_func_emit] call down to a closed
    [string] value, which [Redirect] writes to a file in the dune
    output dir.  The strip script in the curve25519-jasmin-rs repo
    notes converts [= "..." : string] back into a .rs file. *)
Redirect "ristretto_decode_rs"
  Eval vm_compute in ristretto_decode_rs_string.

(* ================================================================ *)
(* Future: ristretto_encode extractor                                *)
(* ================================================================ *)

(** When [ristretto_encode_rs : rust_cmd_ed] is added to
    [Ristretto_RustCmd.v] (alongside the existing _decode_rs), the
    encoder extraction follows the same pattern:

[[
Definition ristretto_encode_rs_sig : rs_func_sig :=
  {| rfs_name := "ristretto_encode";
     rfs_params := [("xyzt_var", TBytes 200);
                    ("out_var",  TBytes 32)] |}.

Definition ristretto_encode_rs_string : string :=
  rs_prelude ++ rs_func_emit ristretto_encode_rs_sig ristretto_encode_rs.

Redirect "ristretto_encode_rs"
  Eval vm_compute in ristretto_encode_rs_string.
]]
*)
