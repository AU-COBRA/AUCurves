(** * Ed25519 sign — bedrock2 implementation.
 *
 * RFC 8032 Ed25519 sign:
 *   1. h = SHA-512(seed)                            (64 B)
 *   2. a = clamp(h[0..32])                          (scalar)
 *   3. prefix = h[32..64]
 *   4. A = a · B                                    (public key, 32 B compressed)
 *   5. r = SHA-512(prefix || M) mod L               (per-msg nonce scalar)
 *   6. R = r · B                                    (32 B compressed)
 *   7. k = SHA-512(R || A || M) mod L               (challenge scalar)
 *   8. s = (r + k · a) mod L
 *   9. signature = R || s
 *
 * STATUS (2026-05-08): bedrock2 [func!] body landed.  The Hoare-spec
 * theorem [ed25519_sign_correct] remains an [Axiom] until the body is
 * proved correct (Phase 1.3 of [docs/option-b-plan.md]).
 *
 * External primitives referenced from the body (resolved at link time
 * via the bedrock2 program env):
 *   - "sha512_64"            : verified Jasmin/asm SHA-512.
 *                              Sig: (out, input, in_len), out is 64 B.
 *   - "clamp_64"             : Field25519_64.X25519/Ed25519 scalar clamp.
 *                              Defined in [Bedrock/End2End/X25519_64/clamp_64.v].
 *                              Sig: (sk : ptr 32) — in-place.
 *   - "ed25519_scalarmult_base" : [Bedrock/End2End/Ed25519/Scalarmult_Impl_64.v].
 *                              Sig: (out_xyzt, scalar) — out is 200 B (5 felems).
 *   - "ed25519_compress"     : compress an extended-Edwards point (200 B)
 *                              to a 32-byte little-endian sign+y form.
 *                              IMPL TODO.
 *   - "scalar_reduce"        : Barrett reduction h_64 -> h mod L.
 *                              Mirrors [Bedrock/End2End/XEdDSA/Sign.v::scalar_reduce]
 *                              (same modulus L); DRAFT marked there.  XEdDSA
 *                              currently in the dune exclusion list — this
 *                              draft assumes the function is exposed in a
 *                              shared file (Tier-1 #4 follow-up).
 *   - "scalar_muladd"        : (out := r + k·a mod L).  Same modulus, same
 *                              source as [scalar_reduce].
 *   - "memmove"              : [bedrock2Examples.memmove].
 *)

From Stdlib Require Import String List ZArith.
From Stdlib.Init Require Import Byte.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Map.OfListWord.
(* Pulls in fe25519_scalar_funcs + the 6 spec_of_*_correct Parameters. *)
Require Import Bedrock.End2End.Ed25519.Scalar25519_64.
(* Pulls in ed25519_scalarmult_{,base} + correctness Parameters/Axioms. *)
Require Import Bedrock.End2End.Ed25519.Scalarmult.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Import Syntax.Coercions NotationsCustomEntry ListNotations.

Module Ed25519Sign.

  (** ** [ed25519_sign(sig_out, seed, msg, msg_len)]

      Computes a 64-byte Ed25519 signature into [sig_out].

      Stack budget (byte buffers; 7 felems × 40 + scalars + hashes):
        h_full      64
        a            32   (scalar)
        prefix      32
        A_xyzt     200   (extended-Edwards scratch from scalarmult_base)
        A_bytes    32   (compressed pubkey)
        nonce_buf  4128  (max 32 + 4096-msg)  — see scratch size note
        r_full      64
        r            32
        R_xyzt     200
        R_bytes    32
        chal_buf   4160  (32 + 32 + 4096-msg)
        k_full      64
        k            32

      Total < 9KB; fits comfortably in a 16KB stack frame.

      We cap [msg_len] at 4096 bytes for the on-stack scratch — Signal's
      Ed25519 callsites all sign \le 4 KB messages.  Larger messages would
      require a streaming SHA-512 (TODO; out of scope here). *)
  Definition ed25519_sign : Syntax.func :=
    func! (sig_out, seed, msg, msg_len) {
      (* 1. h = SHA-512(seed)                                            *)
      stackalloc 64 as h_full;
      sha512_64(h_full, seed, $32);

      (* 2. a = clamp(h[0..32])                                          *)
      stackalloc 32 as a;
      memmove(a, h_full, $32);
      clamp_64(a);

      (* 3. prefix = h[32..64]                                           *)
      stackalloc 32 as prefix;
      memmove(prefix, h_full + $32, $32);

      (* 4. A = a · B  (200-byte XYZT scratch, then compress to 32 B)    *)
      stackalloc 200 as A_xyzt;
      ed25519_scalarmult_base(A_xyzt, a);
      stackalloc 32 as A_bytes;
      ed25519_compress(A_bytes, A_xyzt);

      (* 5. r = SHA-512(prefix || M) mod L                               *)
      stackalloc 4128 as nonce_buf;     (* 32 + msg_len, msg_len <= 4096 *)
      memmove(nonce_buf, prefix, $32);
      memmove(nonce_buf + $32, msg, msg_len);
      stackalloc 64 as r_full;
      sha512_64(r_full, nonce_buf, $32 + msg_len);
      stackalloc 32 as r;
      scalar_reduce(r, r_full);

      (* 6. R = r · B  (200-byte XYZT scratch, then compress to 32 B)    *)
      stackalloc 200 as R_xyzt;
      ed25519_scalarmult_base(R_xyzt, r);
      stackalloc 32 as R_bytes;
      ed25519_compress(R_bytes, R_xyzt);

      (* 7. k = SHA-512(R || A || M) mod L                               *)
      stackalloc 4160 as chal_buf;       (* 32 + 32 + msg_len            *)
      memmove(chal_buf, R_bytes, $32);
      memmove(chal_buf + $32, A_bytes, $32);
      memmove(chal_buf + $64, msg, msg_len);
      stackalloc 64 as k_full;
      sha512_64(k_full, chal_buf, $64 + msg_len);
      stackalloc 32 as k;
      scalar_reduce(k, k_full);

      (* 8. s = (r + k · a) mod L                                        *)
      (* scalar_muladd writes the 32-byte scalar directly into sig_out+32 *)
      scalar_muladd(sig_out + $32, r, k, a);

      (* 9. signature = R || s   (R into the first 32 bytes)             *)
      memmove(sig_out, R_bytes, $32)
    }.

  (** SHA-512 model — pending verified Jasmin-asm citation.  This is the
      Gallina-level abstraction the spec composes against; the runtime is
      libjade's SHA-512 asm linked in via [sha512_64]. *)
  Parameter sha512 : list Byte.byte -> list Byte.byte.
  Parameter sha512_output_64 : forall input, length (sha512 input) = 64%nat.

  (** Abstract Gallina spec for RFC 8032 Ed25519 signing.  Composes
      [Ed25519Scalar.field_l] arithmetic + [Ed25519XYZT.m1add_correct]
      curve law + [Ed25519Compress.compress_25519] + [sha512] axiom.
      Discharged in Phase 1.3 of option-b-plan. *)
  Parameter rfc8032_ed25519_sign : list Byte.byte -> list Byte.byte -> list Byte.byte.
  Parameter rfc8032_ed25519_sign_length :
    forall seed msg, Datatypes.length (rfc8032_ed25519_sign seed msg) = 64%nat.

  (** Real Hoare-spec — proof pending.  Becomes a [Theorem] once:
      (i)   the [ed25519_compress] / [sha512_64] / [scalar_reduce] /
            [scalar_muladd] specs are wired,
      (ii)  Scalarmult_Impl_64.ed25519_scalarmult_base_correct closes
            (currently Admitted, see that file's STATUS block),
      (iii) the [_correct] proof here is structured like
            [Bedrock/End2End/XEdDSA/Sign.v::xeddsa_sign_correct]. *)
  Axiom ed25519_sign_correct :
    forall (functions : Interface.map.rep (map:=Semantics.env))
           (t : Semantics.trace) (m : Interface.map.rep)
           (sig_out_ptr seed_ptr msg_ptr : word)
           (sig_out_init : list Byte.byte)
           (seed : list Byte.byte) (msg : list Byte.byte)
           (R : Interface.map.rep -> Prop),
      Datatypes.length sig_out_init = 64%nat ->
      Datatypes.length seed = 32%nat ->
      ((sig_out_init$@sig_out_ptr) ⋆
       (seed$@seed_ptr) ⋆ (msg$@msg_ptr) ⋆ R)%sep m ->
      Interface.map.get functions "ed25519_sign"%string = Some ed25519_sign ->
      WeakestPrecondition.call functions "ed25519_sign"%string t m
        (sig_out_ptr :: seed_ptr :: msg_ptr ::
         word.of_Z (Z.of_nat (Datatypes.length msg)) :: nil)
        (fun t' m' rets =>
           t' = t /\ rets = nil /\
           ((rfc8032_ed25519_sign seed msg)$@sig_out_ptr ⋆
            (seed$@seed_ptr) ⋆ (msg$@msg_ptr) ⋆ R)%sep m').

End Ed25519Sign.
