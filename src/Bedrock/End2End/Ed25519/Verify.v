(** * Ed25519 verify — bedrock2 implementation (skeleton).
 *
 * Tier-1 #6 of the Ed25519-in-AUCurves track. Mirror of
 * [Bedrock/End2End/XEdDSA/Verify.v] for RFC 8032 Ed25519.
 *
 * RFC 8032 Algorithm:
 *   1. Parse R || s = signature (64 B). R is 32 B (compressed point);
 *      s is 32 B (little-endian scalar).
 *   2. Reject if s ≥ L (scalar out of range).
 *   3. A' = decompress(public_key)                  (32 B → point)
 *   4. R' = decompress(R)                            (32 B → point)
 *   5. k = SHA-512(R || A || M) mod L               (challenge scalar)
 *   6. Accept iff s·B == R' + k·A'
 *      (equivalently: s·B - k·A' == R')
 *
 * STATUS (2026-04-26): file structure with REAL Hoare-spec shape;
 * bedrock2 [Func] body and [_correct] proof both pending.
 *
 * Implementation prerequisites (same as Sign.v):
 *   - Bedrock2 Edwards scalarmult: declared as Parameter in
 *     [Scalarmult.v]; discharge target [Scalarmult_Impl.v.todo].
 *   - SHA-512 axiom: declared in [Sign.v::Ed25519Sign.sha512].
 *   - fe25519_scalar_funcs: declared in [Scalar25519_64.v].
 *   - Edwards point compression: closed in [EdwardsCompressDecompress.v].
 *
 * Implementation plan (~150 LoC bedrock2 + ~80-200 LoC WP proof):
 *   1. Parse signature into R_bytes (32) + s_bytes (32).
 *   2. Range check: s as little-endian Z must be < L. Reject if not.
 *   3. Compute A' = decompress_25519(public_key). Reject if None.
 *   4. Compute R' = decompress_25519(R_bytes). Reject if None.
 *   5. Compute hash_input = R_bytes ++ public_key ++ msg.
 *   6. Compute k_full = sha512(hash_input).
 *   7. k = scalar_reduce(k_full).
 *   8. Compute lhs = s · B via ed25519_scalarmult_base.
 *   9. Compute kA = k · A' via ed25519_scalarmult.
 *  10. Compute rhs = R' + kA (point addition via add_precomputed or readd).
 *  11. Compress lhs and rhs; compare equal.
 *  12. Write 1 to result if equal, else 0.
 *)

From Stdlib Require Import String List ZArith.
Require Import Crypto.Spec.Curve25519.
Require Import bedrock2.Syntax.
Require Import bedrock2.WeakestPrecondition.
Require Import bedrock2.Semantics.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Scalars.
Require Import coqutil.Word.Interface.
Require Import bedrock2.BasicC64Semantics.
Require Import coqutil.Map.OfListWord.
Require Import Bedrock.End2End.Ed25519.Scalar25519_64.
Require Import Bedrock.End2End.Ed25519.Scalarmult.

Module Ed25519Verify.

  (** Bedrock2 [Func] implementing RFC 8032 Ed25519 verify.
      Inputs: [result : ptr 1 (uint8)], [public_key : ptr 32],
      [signature : ptr 64], [msg : ptr], [msg_len : usize].
      Output: [result] = 1 if signature is valid, 0 otherwise. *)
  Parameter ed25519_verify : Syntax.func.

  (** Spec — Phase 1.4 deliverable.
      Currently `True` placeholder. Real shape (when proved):

        Theorem ed25519_verify_correct :
          forall (functions : Semantics.env)
                 (t : Semantics.trace) (m : Semantics.mem)
                 (result_ptr pk_ptr sig_ptr msg_ptr : word)
                 (result_init : Byte.byte)
                 (pk : list Byte.byte) (sig : list Byte.byte)
                 (msg : list Byte.byte)
                 (R : Semantics.mem -> Prop),
            length pk = 32%nat ->
            length sig = 64%nat ->
            (ptsto result_ptr result_init *
             pk$@pk_ptr * sig$@sig_ptr * msg$@msg_ptr *
             R)%sep m ->
            map.get functions "ed25519_verify" = Some ed25519_verify ->
            WeakestPrecondition.call functions "ed25519_verify" t m
              [result_ptr; pk_ptr; sig_ptr; msg_ptr;
               word.of_Z (Z.of_nat (length msg))]
              (fun t' m' rets =>
                 t' = t /\ rets = nil /\
                 exists result_byte,
                   result_byte = (if rfc8032_ed25519_verify pk sig msg
                                  then Byte.x01 else Byte.x00) /\
                   (ptsto result_ptr result_byte *
                    pk$@pk_ptr * sig$@sig_ptr * msg$@msg_ptr *
                    R)%sep m').

      Where [rfc8032_ed25519_verify] is the abstract spec.
      Proof structure:
        straightline.
        handle_call (Ed25519Compress.decompress_25519 ok).
        handle_call (Ed25519Compress.decompress_25519 ok).
        handle_call (sha512 axiom).
        handle_call (fe25519_scalar_from_bytes_correct).
        handle_call (Ed25519Scalarmult.ed25519_scalarmult_base_correct).
        handle_call (Ed25519Scalarmult.ed25519_scalarmult_correct).
        handle_call (add_precomputed_ok).
        handle_call (Ed25519Compress.compress_25519 unfolded).
        ecancel_assumption. *)
  (** Abstract Gallina spec for RFC 8032 Ed25519 verification.
      Returns [true] iff the signature validates. Pending. *)
  Parameter rfc8032_ed25519_verify : list Byte.byte -> list Byte.byte -> list Byte.byte -> bool.

  (** Real Hoare-spec shape — body pending. *)
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
