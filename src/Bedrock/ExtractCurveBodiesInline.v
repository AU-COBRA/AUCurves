(** * ExtractCurveBodiesInline — emit Rust strings for the decomposed
 *    curve leaves from [curve_function_table] using the [#[inline(always)]]
 *    Rust-callable calling convention (Path (2) of the gap inventory).
 *
 *  Mirrors [ExtractCurveBodies.v] but uses [rs_table_extract_inline]
 *  (signatures take [&mut [u8; N]] references, no raw-pointer cast
 *  prelude, [#[inline(always)]]) so LLVM can inline cross-body call
 *  sites (e.g. scalarmult_decomposed → xyzt_double_decomposed) and
 *  do full alias analysis on the typed slots.
 *
 *  The output file [curve_bodies_inline_rs.out] is post-processed by
 *  curve25519-jasmin-rs into src/ed25519_rustcmd/decomposed_bodies_inline.rs.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdToRust.
Require Import Bedrock.ExtractCurveBodies.
Import ListNotations.
Local Open Scope string_scope.

(** Reuse the same [body_extract_sig] list as [ExtractCurveBodies]. *)
Definition curve_bodies_inline_rs_string : string :=
  rs_table_extract_inline curve_bodies_extract_sigs.

Redirect "curve_bodies_inline_rs" Eval vm_compute in curve_bodies_inline_rs_string.
