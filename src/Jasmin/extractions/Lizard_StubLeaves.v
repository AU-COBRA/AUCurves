(** * Stub leaves for Lizard inject/extract FFI symbols
 *
 *  Purpose (mirror of [Ed25519_Sign_StubLeaves.v]): provide [jasmin_func]
 *  entries for every FFI symbol referenced by [lizard_inject_rs] and
 *  [lizard_extract_rs] so jasminc's MakeReferenceArguments pass
 *  (pass 16/30) finds every callee.
 *
 *  ## FFI leaves
 *
 *  | Direction | Leaf                          | Trust                       |
 *  |-----------|-------------------------------|-----------------------------|
 *  | inject    | lizard_pack                   | EXTERN — SHA-256 padding   |
 *  | inject    | elligator2_to_edwards         | EXTERN — Curve25519 math   |
 *  | inject    | ristretto_encode              | EXTERN — Edwards → Ristretto |
 *  | extract   | ristretto_decode_or_fail      | EXTERN — Ristretto → Edwards |
 *  | extract   | edwards_to_elligator2         | EXTERN — Curve25519 math   |
 *  | extract   | lizard_unpack                 | trivial — bytes 8..24 copy |
 *
 *  All 6 leaves are EMPTY-BODY ([JCskip]) stubs.  The 5 marked EXTERN
 *  delegate to the surrounding Rust code at the FFI boundary (same
 *  pattern as Ed25519 sign's 5 EXTERN leaves).  [lizard_unpack] is
 *  trivial in principle (16-byte slice copy at offset 8) but kept as
 *  a skip stub here for symmetry; a future revision can replace it
 *  with a [mk_memmove_*]-style body once driver dispatch is wired
 *  for the inject/extract drivers.
 *
 *  ## Why empty bodies are fine
 *
 *  The OCaml driver ([ocaml_compile.ml]) detects [JCskip]-body funcs
 *  as stubs and marks the matching callsites [inline] + the function
 *  CC [FInfo.Internal].  jasminc's Inlining pass replaces the calls
 *  with [JCskip] (no-op), and at link time the surrounding Rust
 *  resolves each symbol against the verified Rust backend in
 *  [verified-dalek-lizard] (or libsodium for elligator2_to_edwards
 *  via the eventual libjade ristretto255 binding).
 *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
From Stdlib Require Import ZArith String List.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Empty-body stub builder.  Same shape as
    [Ed25519_Sign_StubLeaves.mk_stub_empty]. *)
Definition mk_stub_empty (name : string) (params : list string) : jasmin_func :=
  {| jf_name := name;
     jf_params := List.map (fun p => (p, JTptr 8)) params;
     jf_locals := nil;
     jf_body := JCskip;
  |}.

(** ================================================================ *)
(** §1. FFI leaves for [lizard_inject_rs].                            *)
(** ================================================================ *)

(** lizard_pack(buf32_dst, pt_src): hash-padded buffer build.
    Trust gap: EXTERN — SHA-256-based padding.  At link time resolves
    to [verified_dalek_lizard::build_buffer] (matches Rocq spec
    [lizard_build_buffer]: buf = h[0..8] || msg || h[24..32]). *)
Definition stub_lizard_pack : jasmin_func :=
  mk_stub_empty "lizard_pack" ["lp_dst"; "lp_src"].

(** elligator2_to_edwards(xyzt_dst, buf32_src): apply Elligator2 to
    a 32-byte field element, returning a Curve25519 point converted
    to Edwards form.  Trust gap: EXTERN — Curve25519 elligator math
    requires sqrt_ratio (fiat-crypto verified) plus Montgomery →
    Edwards conversion. *)
Definition stub_elligator2_to_edwards : jasmin_func :=
  mk_stub_empty "elligator2_to_edwards" ["ee_dst"; "ee_src"].

(** ristretto_encode(out_dst, xyzt_src): serialise Edwards point to
    32-byte Ristretto encoding.  Trust gap: EXTERN — depends on fp25519
    arithmetic + canonical form decision. *)
Definition stub_ristretto_encode : jasmin_func :=
  mk_stub_empty "ristretto_encode" ["re_dst"; "re_src"].

(** ================================================================ *)
(** §2. FFI leaves for [lizard_extract_rs].                           *)
(** ================================================================ *)

(** ristretto_decode_or_fail(xyzt_dst, rist_src): deserialise 32-byte
    Ristretto bytes to Edwards point, or identity-with-sentinel on
    invalid input.  Trust gap: EXTERN. *)
Definition stub_ristretto_decode_or_fail : jasmin_func :=
  mk_stub_empty "ristretto_decode_or_fail" ["rd_dst"; "rd_src"].

(** edwards_to_elligator2(buf32_dst, xyzt_src): inverse Elligator2.
    Trust gap: EXTERN. *)
Definition stub_edwards_to_elligator2 : jasmin_func :=
  mk_stub_empty "edwards_to_elligator2" ["ed_dst"; "ed_src"].

(** lizard_unpack(pt_dst, buf32_src): extract middle 16 bytes (offsets
    8..24).  Trust gap: trivial in principle (matches
    [lizard_extract_msg]); kept as empty stub for symmetry. *)
Definition stub_lizard_unpack : jasmin_func :=
  mk_stub_empty "lizard_unpack" ["lu_dst"; "lu_src"].

(** ================================================================ *)
(** §3. Aggregate stub lists.                                         *)
(** ================================================================ *)

(** Stubs needed when emitting [lizard_inject] alone. *)
Definition lizard_inject_stubs : list jasmin_func :=
  [stub_lizard_pack;
   stub_elligator2_to_edwards;
   stub_ristretto_encode].

(** Stubs needed when emitting [lizard_extract] alone. *)
Definition lizard_extract_stubs : list jasmin_func :=
  [stub_ristretto_decode_or_fail;
   stub_edwards_to_elligator2;
   stub_lizard_unpack].

(** Aggregate: all 6 stubs for combined inject+extract emission. *)
Definition lizard_all_stubs : list jasmin_func :=
  lizard_inject_stubs ++ lizard_extract_stubs.

Definition lizard_stubs_field_size : Z := 5.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "lizard_stubs_jasmin_extracted"
  lizard_inject_stubs lizard_extract_stubs lizard_all_stubs
  lizard_stubs_field_size
  pp_func pp_module.
