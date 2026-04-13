(** * XEdDSA signature verification — bedrock2 implementation

    Verify Signal's XEdDSA signature:
      Given: public key A (32 bytes), signature (R, s) (64 bytes), message
      Check: s · G == R + SHAKE256(R || A || msg, 64) · A

    Uses SHAKE-256 (verified Keccak) for the hash challenge.

    ## Key operations
    1. Decompress R from signature bytes
    2. Hash: e = SHAKE256(R || A || msg, 64) mod l
    3. Double scalar multiplication: s·G - e·A
    4. Compare result with R

    ## Verification chain
    Spec: AUCurves/fiat-crypto/src/Spec/XEdDSA.v
    Security: Commitments/XEdDSA_Security.v (SSProve soundness)
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
Local Open Scope string_scope.
Import ListNotations Syntax.Coercions NotationsCustomEntry.

Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.

(** * XEdDSA verify function (bedrock2)

    Inputs:
      result: pointer to 1-byte output (0 = invalid, 1 = valid)
      pubkey: 32-byte X25519 public key
      sig: 64-byte signature (R || s)
      msg: message bytes
      msg_len: length of message *)

Definition xeddsa_verify := func! (result, pubkey, sig, msg, msg_len) {
  (* 1. Parse signature: R = sig[0..32], s = sig[32..64] *)
  stackalloc 40 as R_fe;
  fe25519_from_bytes(R_fe, sig);

  stackalloc 40 as A_fe;
  fe25519_from_bytes(A_fe, pubkey);

  (* 2. e = SHAKE256(R || A || msg, 64) mod l *)
  (* TODO: SHAKE256 bedrock2 call + scalar reduction *)

  (* 3. Compute s·G *)
  stackalloc 40 as base;
  fe25519_from_word(base, $9);
  stackalloc 40 as sG;
  montladder(sG, sig + $32 (* s bytes *), base);

  (* 4. Compute e·A *)
  stackalloc 40 as eA;
  montladder(eA, sig (* placeholder for e *), A_fe);

  (* 5. Check s·G == R + e·A *)
  (* TODO: point addition and comparison *)
  (* For Montgomery x-coordinate only, this requires
     computing x(R + e·A) and comparing with x(s·G).
     Full verification needs Edwards coordinates. *)

  store1(result, $1 (* placeholder *))
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

(* TODO: full spec_of linking to Spec/XEdDSA.v verify equation.
   Requires: scalar arithmetic mod l, SHAKE-256, point addition.
   The Montgomery ladder gives x-coordinates only; full verification
   needs Edwards coordinates (from EdwardsXYZT.v, already proved). *)
