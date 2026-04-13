(** * XEdDSA signature generation — bedrock2 implementation

    Signal's XEdDSA: Schnorr signature using X25519 private key.
    Uses SHAKE-256 (verified Keccak) instead of SHA-512.

    Algorithm:
      1. K = clamp(privkey)
      2. A = K · G (basepoint multiplication)
      3. r = SHAKE256(random || K || msg, 64) mod l  (synthetic nonce)
      4. R = r · G (basepoint multiplication)
      5. e = SHAKE256(R || A || msg, 64) mod l  (challenge)
      6. s = (r + e · K) mod l  (response)
      7. Output: (R_bytes, s_bytes) — 64 bytes

    ## Verification chain
    Spec: AUCurves/fiat-crypto/src/Spec/XEdDSA.v
    Security: Commitments/XEdDSA_Security.v (SSProve Schnorr)
    Fiat-Shamir: Commitments/XEdDSA_FiatShamir.v (verified via Keccak)
    Implementation: this file (bedrock2 WP)
    Compilation: ToJasmin → jasminc → x86-64 *)

From Coq Require Import String List ZArith.
From Coq.Init Require Import Byte.
Require Import Crypto.Spec.Curve25519.
Require Import Crypto.Bedrock.Specs.Field.
Require Import bedrock2.Array.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2Examples.memmove.
Require Import coqutil.Word.Bitwidth32.
Require Import Crypto.Bedrock.End2End.X25519.Field25519.
Require Import Crypto.Bedrock.End2End.X25519.clamp.
Local Open Scope string_scope.
Import ListNotations Syntax.Coercions NotationsCustomEntry.

Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.

(** * XEdDSA sign function (bedrock2)

    Inputs:
      sig_out: 64-byte output buffer (R || s)
      privkey: 32-byte X25519 private key
      msg: message bytes
      msg_len: length of message
      random: 64 bytes of randomness for synthetic nonce *)

Definition xeddsa_sign := func! (sig_out, privkey, msg, msg_len, random) {
  (* 1. Clamp private key *)
  stackalloc 32 as K;
  memmove(K, privkey, $32);
  clamp(K);

  (* 2. Compute public key A = K · basepoint *)
  stackalloc 40 as A_fe;
  stackalloc 40 as base;
  fe25519_from_word(base, $9);
  montladder(A_fe, K, base);
  stackalloc 32 as A_bytes;
  fe25519_to_bytes(A_bytes, A_fe);

  (* 3. Nonce: r = SHAKE256(random || K || msg, 64) mod l *)
  (* For bedrock2: concatenate inputs, call hash, reduce mod l *)
  (* TODO: SHAKE256 bedrock2 function call *)
  (* For now: r is computed abstractly *)
  stackalloc 40 as R_fe;
  stackalloc 32 as R_bytes;
  (* R = r · G *)
  montladder(R_fe, K (* placeholder for r *), base);
  fe25519_to_bytes(R_bytes, R_fe);

  (* 4-5. Challenge + response computed abstractly *)
  (* Output signature *)
  memmove(sig_out, R_bytes, $32);
  memmove(sig_out + $32, K (* placeholder for s *), $32)
}.

(** * Specification *)

Import LittleEndianList.
Local Coercion F.to_Z : F >-> Z.
Require Import bedrock2.WeakestPrecondition bedrock2.Semantics bedrock2.ProgramLogic.
Require Import bedrock2.Syntax bedrock2.Map.SeparationLogic.
Import ProgramLogic.Coercions.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation "xs $@ a" := (Array.array ptsto (word.of_Z 1) a xs) (at level 10, format "xs $@ a").

Local Existing Instance field_parameters.

(** XEdDSA signature = (R_bytes, s_bytes), 64 bytes total.
    Spec links to XEdDSA.v's functional definition. *)

Local Existing Instance field_parameters.

(** Specification: XEdDSA signature generation.
    Links to the functional spec in Spec/XEdDSA.v. *)

Definition xeddsa_sign_spec (privkey msg random : list Byte.byte) :
  list Byte.byte (* 64-byte signature (R || s) *) :=
  (* The functional spec computes:
       K = clamp(privkey)
       A = K · G
       r = SHAKE256(random || K || msg, 64) mod l
       R = r · G
       e = SHAKE256(R_bytes || A_bytes || msg, 64) mod l
       s = (r + e · K) mod l
       output = R_bytes || s_bytes *)
  (* For now, this is abstract — the concrete computation uses
     bedrock2 field ops + SHAKE-256 (verified Keccak). *)
  List.repeat Byte.x00 64. (* placeholder *)

(** The WP proof requires a bedrock2 implementation of SHAKE-256.
    The Keccak permutation is verified in Rocq (Keccak.v), but the
    bedrock2 C-level implementation (absorb/squeeze loop) is not yet
    written. Once available, the proof follows straightline + sep-logic.

    For the scalar arithmetic (mod l reduction), we need:
    - Barrett reduction or similar for 512-bit → 253-bit reduction
    - This can reuse fiat-crypto's scalar field synthesis

    The WP proof structure mirrors x25519_ok exactly:
    repeat straightline → straightline_call per function → ecancel. *)

(* TODO: Lemma xeddsa_sign_ok : program_logic_goal_for_function! xeddsa_sign.
   Blocked on: bedrock2 SHAKE-256 implementation. *)
