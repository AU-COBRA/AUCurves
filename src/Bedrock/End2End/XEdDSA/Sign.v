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

(* TODO: full spec_of linking to Spec/XEdDSA.v
   The spec requires:
   - Scalar arithmetic mod l (for r, e, s)
   - SHAKE-256 hash function (for nonce and challenge)
   - Basepoint multiplication (for R = r·G, A = K·G)
   All components are available; assembly is needed. *)
