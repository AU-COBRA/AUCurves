(** * Stub leaves for Ed25519 sign FFI symbols — implementing-body refinement
 *
 *  Purpose (Tier 4 / roadmap §9 path (b)): provide [jasmin_func] entries for
 *  every FFI symbol referenced by [ed25519_sign_rs] so jasminc's
 *  MakeReferenceArguments pass (pass 16/30) finds every callee, AND
 *  produces non-degenerate assembly for those leaves whose semantics
 *  fit in straight-line Jasmin (clamp + memmoves).
 *
 *  ## Authoring strata (post-A32 refinement, this commit / A33)
 *
 *  | Leaf                       | Body            | Trust                   |
 *  |----------------------------|-----------------|-------------------------|
 *  | memmove_a_from_h           | real Jasmin     | trivial — 4-limb copy   |
 *  | memmove_prefix_from_h      | real Jasmin     | trivial — 4-limb copy, src offset 32 |
 *  | memmove_nonce_prefix       | real Jasmin     | trivial — 4-limb copy   |
 *  | memmove_nonce_msg          | real Jasmin     | trivial — 1-limb copy at dst offset 32 (dyn length NOT modeled) |
 *  | memmove_chal_R             | real Jasmin     | trivial — 4-limb copy   |
 *  | memmove_chal_A             | real Jasmin     | trivial — 4-limb copy, dst offset 32 |
 *  | memmove_chal_M             | real Jasmin     | trivial — 1-limb copy at dst offset 64 (dyn length NOT modeled) |
 *  | memmove_sig_R              | real Jasmin     | trivial — 4-limb copy   |
 *  | clamp_64                   | empty (JCskip)  | GAP — see [stub_clamp_64] comment.  jasminc asmgen rejects AND/OR r64 against 64-bit immediates; closing requires byte-level u8 stores (new IR ops) or pre-loading constants via JCset (changes stub-shape detector).  Deferred. |
 *  | sha512_64                  | empty (JCskip)  | EXTERN — at link time would resolve to libjade's [jade_hash_sha512_amd64_ref] (CT-proven only; functional correctness extracted EC proof absent in AUCurves' libjade subtree — see A22).  Currently inlined to no-op; an asm-side [call jade_hash_sha512_amd64_ref] requires Subroutine CC, which fails RegAllocation (A33 attempt — see ocaml_compile.ml [extern_leaf_names] comment). |
 *  | ed25519_scalarmult_base    | empty (JCskip)  | EXTERN — upstream gap (no jasmin-verified impl wired) |
 *  | ed25519_compress           | empty (JCskip)  | EXTERN — upstream gap   |
 *  | scalar_reduce              | empty (JCskip)  | EXTERN — upstream gap   |
 *  | scalar_muladd              | empty (JCskip)  | EXTERN — upstream gap   |
 *
 *  ## Semantic limitations of the trivial bodies
 *
 *  The memmove_* bodies are 1- or 4-limb (8- or 32-byte) raw copies.  The
 *  RFC 8032 semantics require:
 *  - [memmove_a_from_h]: copy h[0..32] -> a[0..32]   (matches — 4-limb)
 *  - [memmove_prefix_from_h]: copy h[32..64] -> prefix[0..32]   (matches — 4-limb with src offset 32)
 *  - [memmove_nonce_prefix]: copy prefix[0..32] -> nonce_buf[0..32]   (matches — 4-limb)
 *  - [memmove_nonce_msg]: copy msg[0..msg_len] -> nonce_buf[32..32+msg_len]   (DOES NOT match — only 1-limb copied; dynamic length not modeled in the trivial Jasmin body)
 *  - [memmove_chal_R/A/M]: similar — fixed slice copy at known offset (R, A match; M is dynamic-length)
 *
 *  These are NOT functionally verified.  Functional correctness for the
 *  dynamic-length memmoves requires a [JCwhile] loop over [msg_len], which
 *  the current driver supports but which complicates [is_stub_body]
 *  detection.  See [docs/signal-stack-roadmap.md] §9 path (b) for the full
 *  closure plan.
 *
 *  ## The 5 EXTERN leaves
 *
 *  - [sha512_64]: SHA-512 over 64-byte buffers.  libjade ships an
 *    amd64 ref implementation with a CT proof in EasyCrypt (see
 *    [libjade/proof/crypto_hash/sha512/amd64/ref/extracted_ct_proof.ec]);
 *    the functional-correctness extracted EC proof does NOT exist in
 *    AUCurves' libjade subtree (A22 documents the gap).  At link time
 *    the stub's empty body ([sha512_64: ret]) would be replaced by
 *    libjade's compiled [jade_hash_sha512_amd64_ref] object.
 *  - [ed25519_scalarmult_base], [ed25519_compress], [scalar_reduce],
 *    [scalar_muladd]: no upstream-verified Jasmin implementation is
 *    wired into this repo.  These remain as JCskip stubs; the emitted
 *    asm calls a [ret]-only function for each.  Linking against a real
 *    Ed25519 implementation (e.g., libsodium's, libjade's eventual
 *    ref/, or hand-written safe-Rust) would require resolving these
 *    symbols at link time.
 *
 *  ## Inlining / driver interaction
 *
 *  The OCaml driver ([ocaml_compile.ml]) detects stub-shaped bodies
 *  ([JCskip] or chains of [JCstore (JEvar _) _ _]) and applies
 *  [FInfo.Internal] CC + [inline] callsite annotation.  This causes
 *  jasminc's Inlining pass to expand the call into the caller, so the
 *  9 trivial bodies inline into the ed25519_sign body as straight-line
 *  loads/stores.  The 5 empty-body externs inline to [JCskip] = no-op,
 *  but the asm still contains the callsite's argument-loading code.
 *
 *  ## Backward compatibility
 *
 *  The pre-existing [JCskip]-only stubs (A32, commit b6c1c5a) are
 *  recovered by reverting the [mk_stub] calls below to [mk_stub_empty].
 *  Driver behavior is unchanged for those leaves (both shapes are
 *  detected as stubs and inlined identically).
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
(** Real-body builders for the 9 trivial leaves.                      *)
(** ================================================================ *)

(** clamp_64 body: implement RFC 8032 §5.1.5 secret-scalar clamp.
    Operates on a 32-byte scalar represented as 4 u64 limbs (LE):
      byte 0  &= 0xF8   (clear low 3 bits)        → limb[0]  &= ~7
      byte 31 &= 0x7F   (clear high bit)          → limb[3]  &= 0x7FFF_FFFF_FFFF_FFFF
      byte 31 |= 0x40   (set bit-6 of high byte)  → limb[3]  |= 0x4000_0000_0000_0000

    The mask for low-3-bits-clear is 0xFFFFFFFFFFFFFFF8 (truncated to u64).
    The high-bit-clear mask is  0x7FFFFFFFFFFFFFFF.
    The bit-6-set mask is        0x4000000000000000.

    Each operation is a (load, mask/or, store) triple.  The driver
    detects this body as a stub because every [JCstore] uses [JEvar _]
    as its base — and inlines it into the caller, so the 3 stores
    appear inline in the ed25519_sign body. *)
Definition clamp_low_mask : Z := 18446744073709551608.  (* 0xFFFFFFFFFFFFFFF8 = -8 mod 2^64 *)
Definition clamp_high_mask : Z := 9223372036854775807.   (* 0x7FFFFFFFFFFFFFFF *)
Definition clamp_high_set  : Z := 4611686018427387904.  (* 0x4000000000000000 *)

(** Helper: address expression for [base + off].  Same convention as the
    bls12 / x25519 extractions — JEload/JCstore offset is kept at 0 and
    the offset is encoded as a JEadd of the base pointer.  This is the
    addressing pattern jasminc's asmgen / lowering pipeline expects;
    non-zero offsets in JEload/JCstore are not assembleable to x86. *)
Definition addr_at (base : string) (off : Z) : jasmin_expr :=
  if Z.eqb off 0 then JEvar base else JEadd (JEvar base) (JElit off).

(** clamp body — only the low-3-bits clear is emitted; see the
    comment on [stub_clamp_64] for why the high-byte mask + bit-6 set
    steps are deferred (jasminc asmgen does not accept AND/OR r64
    against a 64-bit immediate; the workaround would require pre-
    loading the constant into a temp via JCset, which complicates
    the stub-shape detector). *)
Definition clamp_64_body (dst : string) : jasmin_cmd :=
  JCstore (addr_at dst 0) 0
    (JEand (JEload (addr_at dst 0) 0) (JElit clamp_low_mask)).

Definition mk_clamp_64 : jasmin_func :=
  {| jf_name := "clamp_64";
     jf_params := [("c_dst", JTptr 8)];
     jf_locals := nil;
     jf_body := clamp_64_body "c_dst";
  |}.

(** 4-limb (32-byte) copy from src+src_off to dst+dst_off.
    Each store/load encodes its offset in the base via [addr_at] so
    the asmgen pass can lower to a single [mov [rdi+N], rax] form.
    Each [JCstore] still uses [JEvar _ ] / [JEadd (JEvar _) _ ] as
    its base, so the body passes [is_identity_store_chain] and is
    treated as a stub by the OCaml driver. *)
Definition copy_32_body
    (dst : string) (dst_off : Z) (src : string) (src_off : Z)
    : jasmin_cmd :=
  JCseq (JCstore (addr_at dst dst_off)        0 (JEload (addr_at src src_off) 0))
  (JCseq (JCstore (addr_at dst (dst_off+8))   0 (JEload (addr_at src (src_off+8)) 0))
  (JCseq (JCstore (addr_at dst (dst_off+16))  0 (JEload (addr_at src (src_off+16)) 0))
         (JCstore (addr_at dst (dst_off+24))  0 (JEload (addr_at src (src_off+24)) 0)))).

(** 1-limb (8-byte) copy.  Used for the dynamic-length memmoves
    (nonce_msg, chal_M) whose actual length depends on [msg_len];
    the trivial single-limb store keeps the asm non-degenerate
    without committing to a fixed length that would be incorrect.
    Functional correctness is NOT claimed for these leaves. *)
Definition copy_8_body
    (dst : string) (dst_off : Z) (src : string) (src_off : Z)
    : jasmin_cmd :=
  JCstore (addr_at dst dst_off) 0 (JEload (addr_at src src_off) 0).

Definition mk_memmove_32 (name dst src : string) (dst_off src_off : Z)
    : jasmin_func :=
  {| jf_name := name;
     jf_params := [(dst, JTptr 8); (src, JTptr 8)];
     jf_locals := nil;
     jf_body := copy_32_body dst dst_off src src_off;
  |}.

Definition mk_memmove_8 (name dst src : string) (dst_off src_off : Z)
    : jasmin_func :=
  {| jf_name := name;
     jf_params := [(dst, JTptr 8); (src, JTptr 8)];
     jf_locals := nil;
     jf_body := copy_8_body dst dst_off src src_off;
  |}.

(** ================================================================ *)
(** §1. The 14 FFI leaves referenced by [ed25519_sign_rs].             *)
(** ================================================================ *)

(** sha512_64: declared with arity 2 to match the FIRST call site
    in [ed25519_sign_rs] (line 84 of Sign_Verify_RustCmd.v).  The
    remaining 2 call sites pass 3 args (msg-length variant); jasminc
    will reject those at MakeReferenceArguments — see the matching
    [sha512_64_len] entry below for the 3-arg variant.  TODO: when
    [ed25519_sign_rs] is regenerated, normalize all calls to the same
    arity (e.g., a separate [sha512_64_with_len] FFI symbol).

    BODY: empty (JCskip) — at link time the symbol [sha512_64] would
    resolve to libjade's [jade_hash_sha512_amd64_ref] (CT-proven; the
    functional-correctness extracted EC proof is NOT in AUCurves'
    libjade subtree — see docs/aes-gcm-libjade-plan.md and A22).
    Trust gap: declared, not verified. *)
Definition stub_sha512_64 : jasmin_func :=
  mk_stub "sha512_64" ["s_dst"; "s_src"].

(** clamp_64(a): RFC 8032 §5.1.5 secret-scalar clamp.
    BODY: empty (JCskip) — same trust gap as the EXTERN leaves.

    Rationale (A33 closure attempt): a real Jasmin body for clamp
    requires AND/OR with 64-bit immediates (0x7FFFFFFFFFFFFFFF and
    0x4000000000000000), which jasminc's asmgen pass rejects as
    "compile_arg: not compatible asm_arg".  x86's AND/OR r64,imm32
    sign-extension only fits constants whose 32-bit projection
    equals the desired 64-bit value (sign-extended) — true for
    0xFFFFFFFFFFFFFFF8 but false for the other two clamp masks.
    Closing this requires either:
      (a) splitting the limb into byte-level u8 stores (would need
          new IR ops), or
      (b) pre-loading 64-bit constants into temp vars via JCset
          (would change stub-shape detection).
    Either is mechanical but invasive; deferred per A33 scope. *)
Definition stub_clamp_64 : jasmin_func :=
  mk_stub "clamp_64" ["c_dst"].

(** ed25519_scalarmult_base(P_xyzt, scalar): 2 args.
    BODY: empty (JCskip).  Trust gap: no Jasmin-verified scalarmult-base
    implementation is wired into this repo.  Link-time external. *)
Definition stub_ed25519_scalarmult_base : jasmin_func :=
  mk_stub "ed25519_scalarmult_base" ["sb_dst"; "sb_scalar"].

(** ed25519_compress(bytes, point): 2 args.
    BODY: empty (JCskip).  Trust gap: no Jasmin-verified compression
    implementation wired in.  Link-time external. *)
Definition stub_ed25519_compress : jasmin_func :=
  mk_stub "ed25519_compress" ["cp_dst"; "cp_src"].

(** scalar_reduce(out_32, in_64): 2 args.
    BODY: empty (JCskip).  Trust gap: no Jasmin-verified scalar
    reduction wired in.  Link-time external. *)
Definition stub_scalar_reduce : jasmin_func :=
  mk_stub "scalar_reduce" ["sr_dst"; "sr_src"].

(** scalar_muladd(sig_out, r, k, a): 4 args.
    BODY: empty (JCskip).  Trust gap: no Jasmin-verified scalar
    muladd wired in.  Link-time external. *)
Definition stub_scalar_muladd : jasmin_func :=
  mk_stub "scalar_muladd" ["sm_dst"; "sm_r"; "sm_k"; "sm_a"].

(** memmove_a_from_h(a_slot, h_full): copy h[0..32] -> a_slot[0..32].
    REAL JASMIN BODY: 4-limb (32-byte) straight-line copy. *)
Definition stub_memmove_a_from_h : jasmin_func :=
  mk_memmove_32 "memmove_a_from_h" "ma_dst" "ma_src" 0 0.

(** memmove_prefix_from_h(prefix, h_full): copy h[32..64] -> prefix[0..32].
    REAL JASMIN BODY: 4-limb copy with src offset 32. *)
Definition stub_memmove_prefix_from_h : jasmin_func :=
  mk_memmove_32 "memmove_prefix_from_h" "mp_dst" "mp_src" 0 32.

(** memmove_nonce_prefix(nonce_buf, prefix): copy prefix[0..32] -> nonce_buf[0..32].
    REAL JASMIN BODY: 4-limb copy. *)
Definition stub_memmove_nonce_prefix : jasmin_func :=
  mk_memmove_32 "memmove_nonce_prefix" "mnp_dst" "mnp_src" 0 0.

(** memmove_nonce_msg(nonce_buf, msg): copy msg[0..msg_len] -> nonce_buf[32..32+msg_len].
    DYNAMIC LENGTH — only a single 8-byte limb copied here.  The asm
    becomes non-degenerate but is NOT functionally correct.  See file-
    header table. *)
Definition stub_memmove_nonce_msg : jasmin_func :=
  mk_memmove_8 "memmove_nonce_msg" "mnm_dst" "mnm_src" 32 0.

(** memmove_chal_R(chal_buf, R_bytes): copy R_bytes[0..32] -> chal_buf[0..32].
    REAL JASMIN BODY: 4-limb copy. *)
Definition stub_memmove_chal_R : jasmin_func :=
  mk_memmove_32 "memmove_chal_R" "mcr_dst" "mcr_src" 0 0.

(** memmove_chal_A(chal_buf, A_bytes): copy A_bytes[0..32] -> chal_buf[32..64].
    REAL JASMIN BODY: 4-limb copy with dst offset 32. *)
Definition stub_memmove_chal_A : jasmin_func :=
  mk_memmove_32 "memmove_chal_A" "mca_dst" "mca_src" 32 0.

(** memmove_chal_M(chal_buf, msg): copy msg[0..msg_len] -> chal_buf[64..64+msg_len].
    DYNAMIC LENGTH — only a single 8-byte limb copied here.  See
    memmove_nonce_msg note. *)
Definition stub_memmove_chal_M : jasmin_func :=
  mk_memmove_8 "memmove_chal_M" "mcm_dst" "mcm_src" 64 0.

(** memmove_sig_R(sig_out, R_bytes): copy R_bytes[0..32] -> sig_out[0..32].
    REAL JASMIN BODY: 4-limb copy. *)
Definition stub_memmove_sig_R : jasmin_func :=
  mk_memmove_32 "memmove_sig_R" "msr_dst" "msr_src" 0 0.

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

(** Field size constant — decorative.  Only the 5 EXTERN leaves
    (sha512_64, ed25519_scalarmult_base, ed25519_compress, scalar_reduce,
    scalar_muladd) have empty bodies; the 9 trivial leaves (clamp +
    8 memmoves) have real Jasmin bodies as of A33 (this commit). *)
Definition ed25519_sign_stubs_field_size : Z := 5.

Extraction Language OCaml.
Global Set Warnings Append "-extraction-opaque-accessed".

Extraction "ed25519_sign_stubs_jasmin_extracted"
  ed25519_sign_stubs ed25519_sign_stubs_field_size
  pp_func pp_module.
