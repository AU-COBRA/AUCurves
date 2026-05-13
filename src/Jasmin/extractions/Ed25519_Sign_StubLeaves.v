(** * Minimal stub leaves for Ed25519 sign FFI symbols
 *
 *  Purpose (Tier 4 / roadmap §9 path (b)): provide opaque-body
 *  [jasmin_func] entries for every FFI symbol referenced by
 *  [ed25519_sign_rs] so jasminc's MakeReferenceArguments pass
 *  (pass 16/30) finds every callee in the program.  This DOES
 *  NOT close [RustcExec_correct]; it pushes the chain past the
 *  empirical pass-15 gate that A6 established (commit c88a2f9).
 *
 *  The stubs have:
 *    * exact arity matching the [REdCall name dst args] sites in
 *      [Sign_Verify_RustCmd.v] (dst becomes the first jasmin arg);
 *    * empty body ([JCskip]);
 *    * 0 return values (matches the bedrock2 [Ccall ([], ...)]
 *      shape the OCaml driver translates [JCcall] into).
 *
 *  Because every call site passes only pointer args (TBytes / TU64),
 *  every stub takes [JTptr 8] params; the field-size constant is
 *  decorative for stubs (no body to allocate).
 *
 *  Note on [sha512_64]: in [ed25519_sign_rs] it is called with
 *  TWO arities — 2 args (initial seed hash) and 3 args (nonce /
 *  challenge hashes with a length argument).  Jasmin functions
 *  are fixed-arity, so the single stub here matches the higher
 *  arity (3); the 2-arg call site will fail typechecking inside
 *  jasminc IF this stub were ever inlined.  For the empirical
 *  gate we only need MakeReferenceArguments to find the symbol.
 *
 *  This file is intentionally STANDALONE — it does not [Require]
 *  [Ed25519_Sign_Inlined] or any [SafeRustEd25519*] module so it
 *  builds independent of in-flight Phase 0b work on those files.
 *  The driver ([ed25519_sign_stubbed_main.ml]) is responsible for
 *  prepending these stubs to the sign body at the OCaml level via
 *  [Obj.magic] (the structural type [jasmin_func] is identical
 *  across extractions).
 *)

From Stdlib Require Export Extraction.
From Stdlib Require Export ExtrOcamlBasic.
From Stdlib Require Export ExtrOcamlString.
From Stdlib Require Import ZArith String List.
Import ListNotations.

Require Import Bedrock.Jasmin.Core.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Per-stub helper: unique param names so jasminc's argument-naming
    pass treats each stub independently.

    Body: identity read-write chain through every parameter — for an
    N-arg function with params [dest; src1; ...; src_{N-1}]:
      *dest := *src1 (if N >= 2) or *dest := *dest (if N = 1);
      *dest := *src_i for i = 2..N-1 (each additional src read)

    Rationale (closure of A25's pass-28 RegAllocation failure): the
    previous [JCskip] body left the dest-param register's write status
    opaque to jasminc's register allocator, which tried to unify dest
    slots across consecutive stub calls whose actual destinations
    differed (e.g., [R_bytes] and [A_bytes] both consumed by
    [ed25519_compress]).  An identity load-store chain through every
    parameter makes both reads (every src) and writes (dest) visible
    to the allocator, breaking the spurious unification.

    The values written are semantically irrelevant — these stubs are
    placeholder declarations only; they are never inlined or executed.
    The bytes written through dest happen to equal the bytes at src1[0]
    or dest[0], but downstream Rust replaces these calls with the
    real FFI implementations.

    The auxiliary [JCstore dest 0 (JEload src_i 0)] entries for srcs
    beyond src1 may overwrite the freshly-stored byte; this is fine
    because they execute sequentially and the last write wins. *)
Fixpoint mk_stub_body_aux (dest : string) (srcs : list string) : jasmin_cmd :=
  match srcs with
  | nil => JCskip
  | s :: rest =>
      JCseq (JCstore (JEvar dest) 0 (JEload (JEvar s) 0))
            (mk_stub_body_aux dest rest)
  end.

Definition mk_stub_body (params : list string) : jasmin_cmd :=
  match params with
  | nil => JCskip
  | dest :: nil =>
      (* 1-arg stub: identity read-write through dest itself.
         Reads *dest, writes back to *dest at offset 0 — true no-op. *)
      JCstore (JEvar dest) 0 (JEload (JEvar dest) 0)
  | dest :: srcs =>
      mk_stub_body_aux dest srcs
  end.

(** Default stub body: identity load-store chain through every param.
    See [mk_stub_body] above for the rationale.  Kept here so callers
    can switch back to it by edit. *)
Definition mk_stub_idload (name : string) (params : list string) : jasmin_func :=
  {| jf_name := name;
     jf_params := List.map (fun p => (p, JTptr 8)) params;
     jf_locals := nil;
     jf_body := mk_stub_body params;
  |}.

(** Empty-body variant used by drivers that mark callsites [inline] and
    let jasminc's Inlining pass replace the call with [JCskip] (no-op).
    Mirrors A25's original [JCskip]-body shape. *)
Definition mk_stub_empty (name : string) (params : list string) : jasmin_func :=
  {| jf_name := name;
     jf_params := List.map (fun p => (p, JTptr 8)) params;
     jf_locals := nil;
     jf_body := JCskip;
  |}.

(** Active stub builder.  We use [JCskip] bodies + driver-side
    [inline]-annotated callsites + [FInfo.Internal] cc.  This minimizes
    register pressure post-inlining (no synthetic [__store_tmp_*] vars,
    no formal-param load-stores surviving renaming). *)
Definition mk_stub (name : string) (params : list string) : jasmin_func :=
  mk_stub_empty name params.

(** ================================================================ *)
(** §1. The 14 FFI leaves referenced by [ed25519_sign_rs].             *)
(** ================================================================ *)

(** sha512_64: declared with arity 2 to match the FIRST call site
    in [ed25519_sign_rs] (line 84 of Sign_Verify_RustCmd.v).  The
    remaining 2 call sites pass 3 args (msg-length variant); jasminc
    will reject those at MakeReferenceArguments — see the matching
    [sha512_64_len] entry below for the 3-arg variant.  TODO: when
    [ed25519_sign_rs] is regenerated, normalize all calls to the same
    arity (e.g., a separate [sha512_64_with_len] FFI symbol). *)
Definition stub_sha512_64 : jasmin_func :=
  mk_stub "sha512_64" ["s_dst"; "s_src"].

(** clamp_64(a): JCcall passes (dst) — 1 arg. *)
Definition stub_clamp_64 : jasmin_func :=
  mk_stub "clamp_64" ["c_dst"].

(** ed25519_scalarmult_base(P_xyzt, scalar): 2 args. *)
Definition stub_ed25519_scalarmult_base : jasmin_func :=
  mk_stub "ed25519_scalarmult_base" ["sb_dst"; "sb_scalar"].

(** ed25519_compress(bytes, point): 2 args. *)
Definition stub_ed25519_compress : jasmin_func :=
  mk_stub "ed25519_compress" ["cp_dst"; "cp_src"].

(** scalar_reduce(out_32, in_64): 2 args. *)
Definition stub_scalar_reduce : jasmin_func :=
  mk_stub "scalar_reduce" ["sr_dst"; "sr_src"].

(** scalar_muladd(sig_out, r, k, a): 4 args. *)
Definition stub_scalar_muladd : jasmin_func :=
  mk_stub "scalar_muladd" ["sm_dst"; "sm_r"; "sm_k"; "sm_a"].

(** memmove_a_from_h(a_slot, h_full): 2 args. *)
Definition stub_memmove_a_from_h : jasmin_func :=
  mk_stub "memmove_a_from_h" ["ma_dst"; "ma_src"].

(** memmove_prefix_from_h(prefix, h_full): 2 args. *)
Definition stub_memmove_prefix_from_h : jasmin_func :=
  mk_stub "memmove_prefix_from_h" ["mp_dst"; "mp_src"].

(** memmove_nonce_prefix(nonce_buf, prefix): 2 args. *)
Definition stub_memmove_nonce_prefix : jasmin_func :=
  mk_stub "memmove_nonce_prefix" ["mnp_dst"; "mnp_src"].

(** memmove_nonce_msg(nonce_buf, msg): 2 args. *)
Definition stub_memmove_nonce_msg : jasmin_func :=
  mk_stub "memmove_nonce_msg" ["mnm_dst"; "mnm_src"].

(** memmove_chal_R(chal_buf, R_bytes): 2 args. *)
Definition stub_memmove_chal_R : jasmin_func :=
  mk_stub "memmove_chal_R" ["mcr_dst"; "mcr_src"].

(** memmove_chal_A(chal_buf, A_bytes): 2 args. *)
Definition stub_memmove_chal_A : jasmin_func :=
  mk_stub "memmove_chal_A" ["mca_dst"; "mca_src"].

(** memmove_chal_M(chal_buf, msg): 2 args. *)
Definition stub_memmove_chal_M : jasmin_func :=
  mk_stub "memmove_chal_M" ["mcm_dst"; "mcm_src"].

(** memmove_sig_R(sig_out, R_bytes): 2 args. *)
Definition stub_memmove_sig_R : jasmin_func :=
  mk_stub "memmove_sig_R" ["msr_dst"; "msr_src"].

(** ================================================================ *)
(** §2. Aggregate stub list.                                          *)
(** ================================================================ *)

Definition ed25519_sign_stubs : list jasmin_func :=
  [stub_sha512_64;
   stub_clamp_64;
   stub_ed25519_scalarmult_base;
   stub_ed25519_compress;
   stub_scalar_reduce;
   stub_scalar_muladd;
   stub_memmove_a_from_h;
   stub_memmove_prefix_from_h;
   stub_memmove_nonce_prefix;
   stub_memmove_nonce_msg;
   stub_memmove_chal_R;
   stub_memmove_chal_A;
   stub_memmove_chal_M;
   stub_memmove_sig_R].

(** Field size constant — decorative.  The stubs have no body so
    the unsaturated-solinas size is unused. *)
Definition ed25519_sign_stubs_field_size : Z := 5.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "ed25519_sign_stubs_jasmin_extracted"
  ed25519_sign_stubs ed25519_sign_stubs_field_size
  pp_func pp_module.
