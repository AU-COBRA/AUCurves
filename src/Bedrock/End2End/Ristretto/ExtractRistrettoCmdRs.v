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
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import Lists.List.
Require Import Bedrock.RustCmdToRust.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.End2End.Ristretto.Ristretto_RustCmd.
Require Import Bedrock.End2End.Ristretto.Ristretto_Encode_RustCmd.
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

(** Newline literal for hand-built string concatenation. *)
Definition NL : string := String (Ascii.Ascii false true false true false false false false) "".

(** Ristretto-specific FFI prelude.  Replaces [rs_prelude] (which
    declares Ed25519/sha512 symbols irrelevant to ristretto, and
    omits the ristretto-specific symbols we DO call).  Mirrors the
    actual Rust ABI of [curve25519-jasmin-rs/src/ristretto_rustcmd/
    leaves.rs] plus the shared field-op leaves from the existing
    Ed25519 path. *)
Definition rs_prelude_ristretto : string :=
  "// Generated from rust_cmd_ed.  Avoid editing directly." ++ NL ++
  "// Verification: rust_cmd_ed -> safe_cmd_correct_ed (Qed) ->" ++ NL ++
  "//   to_bedrock_cmd_semantic_correct (Qed) -> bedrock2 fnspec." ++ NL ++ NL ++
  "#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code)]" ++ NL ++ NL ++
  "unsafe extern ""C"" {" ++ NL ++
  "    // Field arithmetic (shared with Ed25519 path)." ++ NL ++
  "    fn fe25519_mul(out: *mut u8, a: *const u8, b: *const u8);" ++ NL ++
  "    fn fe25519_add(out: *mut u8, a: *const u8, b: *const u8);" ++ NL ++
  "    fn fe25519_sub(out: *mut u8, a: *const u8, b: *const u8);" ++ NL ++
  "    fn fe25519_sq (out: *mut u8, a: *const u8);" ++ NL ++
  "    // Ristretto-specific leaves." ++ NL ++
  "    fn ristretto_parse_canonical_felem(s_out: *mut u8, status_out: *mut u8, bs_in: *const u8);" ++ NL ++
  "    fn ristretto_pack_canonical_felem(out: *mut u8, s_in: *const u8);" ++ NL ++
  "    fn ristretto_canonical_negate(out: *mut u8, s_in: *const u8);" ++ NL ++
  "    fn ristretto_sqrt_ratio_m1(ws_out: *mut u8, r_out: *mut u8, u_in: *const u8, v_in: *const u8);" ++ NL ++
  "    // Data-movement leaf (memmove-class)." ++ NL ++
  "    fn pack_xyzt5(out: *mut u8, x: *const u8, y: *const u8, z: *const u8, ta: *const u8, tb: *const u8);" ++ NL ++
  "}" ++ NL ++ NL.

(** ** [ristretto_decode_rs_string] — fully-rendered Rust source.

    [rs_prelude] adds the `#![allow(...)]` header + the FFI
    `unsafe extern "C" { ... }` block for declared callees.  The
    callees that ristretto_decode invokes are auto-collected by
    [rs_func_emit] by walking the AST. *)
Definition ristretto_decode_rs_string : string :=
  rs_prelude_ristretto ++ rs_func_emit ristretto_decode_rs_sig ristretto_decode_rs.

(** ** Emit the .out artifact via Redirect.

    [vm_compute] reduces the [rs_func_emit] call down to a closed
    [string] value, which [Redirect] writes to a file in the dune
    output dir.  The strip script in the curve25519-jasmin-rs repo
    notes converts [= "..." : string] back into a .rs file. *)
Redirect "ristretto_decode_rs"
  Eval vm_compute in ristretto_decode_rs_string.

(* ================================================================ *)
(* ristretto_encode extractor                                        *)
(* ================================================================ *)

(** ** [ristretto_encode_rs_sig] — Rust signature record.
 *
 *  Parameter names MUST match the slot names used inside
 *  [ristretto_encode_rs]'s [REdCall] arguments
 *  (see [spec_of_ed_ristretto_encode] in [Ristretto_Encode_RustCmd.v]):
 *  "xyzt_var" (200-byte input) and "out_var" (32-byte output).
 *
 *  Emitted Rust signature:
 *    fn ristretto_encode(xyzt_var: *const u8, out_var: *mut u8) { ... }
 *)
Definition ristretto_encode_rs_sig : rs_func_sig :=
  {| rfs_name := "ristretto_encode";
     rfs_params := [("xyzt_var", TBytes 200);
                    ("out_var",  TBytes 32)] |}.

(** Encode-specific FFI prelude.  Adds the two encode-only leaves
    ([unpack_xyzt5], [fe25519_inv]) on top of the shared field ops and
    the ristretto pack/sqrt leaves declared for the decoder. *)
Definition rs_prelude_ristretto_encode : string :=
  "// Generated from rust_cmd_ed.  Avoid editing directly." ++ NL ++
  "// Verification: rust_cmd_ed -> functional simulation against" ++ NL ++
  "//   ristretto_encode_gallina_nlet (Ristretto_Encode_*.v)." ++ NL ++ NL ++
  "#![allow(non_snake_case, unused_assignments, unused_mut, unused_variables, unused_parens, dead_code)]" ++ NL ++ NL ++
  "unsafe extern ""C"" {" ++ NL ++
  "    // Field arithmetic (shared with Ed25519 / decode path)." ++ NL ++
  "    fn fe25519_mul(out: *mut u8, a: *const u8, b: *const u8);" ++ NL ++
  "    fn fe25519_add(out: *mut u8, a: *const u8, b: *const u8);" ++ NL ++
  "    fn fe25519_sub(out: *mut u8, a: *const u8, b: *const u8);" ++ NL ++
  "    fn fe25519_sq (out: *mut u8, a: *const u8);" ++ NL ++
  "    // Modular inverse z^(p-2) mod p (shared; provided by main leaves.rs)." ++ NL ++
  "    fn fe25519_inv(out: *mut u8, a: *const u8);" ++ NL ++
  "    // Ristretto leaves (shared with decode path)." ++ NL ++
  "    fn ristretto_pack_canonical_felem(out: *mut u8, s_in: *const u8);" ++ NL ++
  "    fn ristretto_sqrt_ratio_m1(ws_out: *mut u8, r_out: *mut u8, u_in: *const u8, v_in: *const u8);" ++ NL ++
  "    // Encode-specific input split (inverse of pack_xyzt5)." ++ NL ++
  "    fn unpack_xyzt5(x_out: *mut u8, y_out: *mut u8, z_out: *mut u8, ta_out: *mut u8, tb_out: *mut u8, xyzt_in: *const u8);" ++ NL ++
  "}" ++ NL ++ NL.

Definition ristretto_encode_rs_string : string :=
  rs_prelude_ristretto_encode ++ rs_func_emit ristretto_encode_rs_sig ristretto_encode_rs.

Redirect "ristretto_encode_rs"
  Eval vm_compute in ristretto_encode_rs_string.
