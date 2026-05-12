(** * ExtractWnafCombBodies — emit Rust strings for the wNAF + comb
 *    Ed25519 scalar-mult bodies.
 *
 *  Two entries are extracted as Rust functions:
 *    1. wnaf_scalarmult           (out: [u8;200], digits:[u8;64], P:[u8;200])
 *    2. comb_scalarmult_base      (out: [u8;200], scalar:[u8;32])
 *
 *  Both extern-C and inline variants are emitted side-by-side
 *  (matching the [ExtractCurveBodies.v] / [ExtractCurveBodiesInline.v]
 *  pair).  The output file is post-processed by curve25519-jasmin-rs
 *  into [src/ed25519_rustcmd/decomposed_bodies_wnaf_comb.rs].
 *
 *  Leaf surface (declared in the consumer's `unsafe extern "C"` block):
 *    - [xyzt_add_decomposed]       (verified, from ExtractCurveBodies.v)
 *    - [xyzt_double_decomposed]    (verified, from ExtractCurveBodies.v)
 *    - [xyzt_copy]                 (verified, from ExtractCurveBodies.v)
 *    - [comb_table_lookup]         (new; provided by the Rust wrapper,
 *                                   backed by a runtime-initialised
 *                                   table of dalek base-point multiples)
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import Lists.List.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.RustCmdToRust.
Require Import Bedrock.End2End.Ed25519.WnafScalarmultBody.
Require Import Bedrock.End2End.Ed25519.CombScalarmultBody.
Import ListNotations.
Local Open Scope string_scope.

Definition wnaf_comb_extract_sigs : list body_extract_sig :=
  [ {| bes_name      := "wnaf_scalarmult";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 64; TBytes 200];
       bes_body      := wnaf_scalarmult_body |} ;
    {| bes_name      := "comb_scalarmult_base";
       bes_dest_type := TBytes 200;
       bes_arg_types := [TBytes 32];
       bes_body      := comb_scalarmult_base_body |} ].

(** extern-C variant (raw-pointer FFI; cross-body REdCallFn dispatch
    goes through [unsafe { fname(out.as_mut_ptr(), ...) }]). *)
Definition wnaf_comb_bodies_rs_string : string :=
  rs_table_extract wnaf_comb_extract_sigs.

(** Inline variant (#[inline(always)] pub fn with typed-reference
    parameters); used under the [inline_leaves]/[wnaf_comb_leaves]
    cargo feature for LLVM alias analysis / cross-body inlining. *)
Definition wnaf_comb_bodies_inline_rs_string : string :=
  rs_table_extract_inline wnaf_comb_extract_sigs.

Redirect "curve_bodies_wnaf_comb_rs" Eval vm_compute in wnaf_comb_bodies_rs_string.
Redirect "curve_bodies_wnaf_comb_inline_rs" Eval vm_compute in wnaf_comb_bodies_inline_rs_string.
