(** * Ed25519 verify — bedrock2 implementation.
 *
 * RFC 8032 Ed25519 verify:
 *   1. Parse R || s = signature (64 B). R is 32 B (compressed point);
 *      s is 32 B (little-endian scalar).
 *   2. Reject if s ≥ L (scalar out of range).
 *   3. A' = decompress(public_key)                  (32 B → point)
 *   4. R' = decompress(R)                            (32 B → point)
 *   5. k = SHA-512(R || A || M) mod L               (challenge scalar)
 *   6. Accept iff s·B == R' + k·A'
 *      (equivalently: compress(s·B - k·A') == R, or: compress(s·B) ==
 *       compress(R' + k·A')).
 *
 * STATUS (2026-05-08): bedrock2 [func!] body landed.  The Hoare-spec
 * theorem [ed25519_verify_correct] remains an [Axiom] — see Sign.v's
 * tracking comment.
 *
 * External primitives referenced from the body (resolved at link time):
 *   - "sha512_64", "scalar_reduce"     : same as Sign.v.
 *   - "ed25519_decompress"             : 32 B → 200 B XYZT, returns 0/1.
 *                                       IMPL TODO.
 *   - "ed25519_compress"               : same as Sign.v.
 *   - "ed25519_scalarmult_base"        : same as Sign.v.
 *   - "ed25519_scalarmult"             : variable-base scalarmult,
 *                                       (out_xyzt, scalar, base_xyzt).
 *                                       Defined in [Scalarmult.v].
 *   - "ed25519_xyzt_add"               : extended-Edwards point add,
 *                                       (out_xyzt, P_xyzt, Q_xyzt).
 *                                       Already proven Qed in
 *                                       [Bedrock/End2End/Ed25519/EdwardsXYZT64.v]
 *                                       under another name; alias here.
 *   - "scalar_lt_L"                    : tests s < L.  Returns 1 iff in range.
 *                                       IMPL TODO; range check on the
 *                                       little-endian 32-byte scalar.
 *   - "bytes_equal_32"                 : constant-time byte compare,
 *                                       returns 1 iff identical.  IMPL TODO.
 *   - "memmove"                        : as Sign.v.
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
Require Import Bedrock.End2End.Ed25519.Scalar25519_64.
Require Import Bedrock.End2End.Ed25519.Scalarmult.

Local Open Scope string_scope.
Local Open Scope Z_scope.
Import Syntax.Coercions NotationsCustomEntry ListNotations.

Module Ed25519Verify.

  (** ** [ed25519_verify(result, pk, sig, msg, msg_len)]

      Writes 1 to [result] iff the signature validates, 0 otherwise.

      Strategy: rebuild sB and (R' + kA') in extended Edwards form,
      compress both, and constant-time compare the 32-byte encodings.
      The compress-then-compare is cheaper and easier to spec than
      raw-coordinate equality (which requires Z normalisation).

      Stack budget similar to Sign.v (~9 KB).  Same 4 KB cap on msg_len. *)
  Definition ed25519_verify : Syntax.func :=
    func! (result, pk, sig, msg, msg_len) {
      (* 1. Parse R || s = signature[0..32] || signature[32..64] *)
      stackalloc 32 as R_bytes;
      stackalloc 32 as s_bytes;
      memmove(R_bytes, sig, $32);
      memmove(s_bytes, sig + $32, $32);

      (* 2. Range check: reject if s >= L.  scalar_lt_L returns 1 iff valid. *)
      unpack! s_ok = scalar_lt_L(s_bytes);
      if s_ok == $0 {
        store1(result, $0)
      } else {
        (* 3. A' = decompress(pk).  Returns 0 on failure (non-square or
              kernel point), 1 on success. *)
        stackalloc 200 as A_xyzt;
        unpack! a_ok = ed25519_decompress(A_xyzt, pk);
        if a_ok == $0 {
          store1(result, $0)
        } else {
          (* 4. R' = decompress(R_bytes). *)
          stackalloc 200 as R_xyzt;
          unpack! r_ok = ed25519_decompress(R_xyzt, R_bytes);
          if r_ok == $0 {
            store1(result, $0)
          } else {
            (* 5. k = SHA-512(R || A || M) mod L *)
            stackalloc 4160 as chal_buf;       (* 32 + 32 + msg_len *)
            memmove(chal_buf, R_bytes, $32);
            memmove(chal_buf + $32, pk, $32);
            memmove(chal_buf + $64, msg, msg_len);
            stackalloc 64 as k_full;
            sha512_64(k_full, chal_buf, $64 + msg_len);
            stackalloc 32 as k;
            scalar_reduce(k, k_full);

            (* 6. lhs = s · B, rhs = R' + k · A'                            *)
            stackalloc 200 as lhs_xyzt;
            ed25519_scalarmult_base(lhs_xyzt, s_bytes);
            stackalloc 200 as kA_xyzt;
            ed25519_scalarmult(kA_xyzt, k, A_xyzt);
            stackalloc 200 as rhs_xyzt;
            ed25519_xyzt_add(rhs_xyzt, R_xyzt, kA_xyzt);

            (* 7. Compress and compare                                       *)
            stackalloc 32 as lhs_bytes;
            ed25519_compress(lhs_bytes, lhs_xyzt);
            stackalloc 32 as rhs_bytes;
            ed25519_compress(rhs_bytes, rhs_xyzt);
            unpack! eq_ok = bytes_equal_32(lhs_bytes, rhs_bytes);
            store1(result, eq_ok)
          }
        }
      }
    }.

  (** Abstract Gallina spec.  Returns [true] iff the signature validates
      against (pk, msg) per RFC 8032 §5.1.7.  Pending. *)
  Parameter rfc8032_ed25519_verify : list Byte.byte -> list Byte.byte -> list Byte.byte -> bool.

  (** Real Hoare-spec — proof pending alongside Sign.v's. *)
  Axiom ed25519_verify_correct :
    forall (functions : Interface.map.rep (map:=Semantics.env))
           (t : Semantics.trace) (m : Interface.map.rep)
           (result_ptr pk_ptr sig_ptr msg_ptr : word)
           (result_init : Byte.byte)
           (pk : list Byte.byte) (sig : list Byte.byte)
           (msg : list Byte.byte)
           (R : Interface.map.rep -> Prop),
      Datatypes.length pk = 32%nat ->
      Datatypes.length sig = 64%nat ->
      ((cons result_init nil)$@result_ptr ⋆ pk$@pk_ptr ⋆ sig$@sig_ptr ⋆ msg$@msg_ptr ⋆ R)%sep m ->
      Interface.map.get functions "ed25519_verify"%string = Some ed25519_verify ->
      WeakestPrecondition.call functions "ed25519_verify"%string t m
        (result_ptr :: pk_ptr :: sig_ptr :: msg_ptr ::
         word.of_Z (Z.of_nat (Datatypes.length msg)) :: nil)
        (fun t' m' rets =>
           t' = t /\ rets = nil /\
           ((cons (if rfc8032_ed25519_verify pk sig msg then Byte.x01 else Byte.x00) nil)$@result_ptr ⋆
            pk$@pk_ptr ⋆ sig$@sig_ptr ⋆ msg$@msg_ptr ⋆ R)%sep m').

End Ed25519Verify.
