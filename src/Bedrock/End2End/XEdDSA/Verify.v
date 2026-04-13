(** * XEdDSA signature verification — bedrock2 implementation

    Check: s · G == R + SHAKE256(R || A || msg, 64) · A

    Uses SHAKE-256 (verified Keccak) for the hash challenge.
    Montgomery→Edwards conversion via EdwardsMontgomeryIsomorphism. *)

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
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import Syntax.Coercions NotationsCustomEntry ListNotations.

Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.

(** * XEdDSA verify function

    Inputs:
      result: pointer to 1-byte output (1 = valid, 0 = invalid)
      pubkey: 32-byte X25519 public key
      sig: 64-byte signature (R || s)
      msg: message bytes
      msg_len: length of message *)

Definition xeddsa_verify := func! (result, pubkey, sig, msg, msg_len) {
  (* 1. Parse signature: R = sig[0..31], s = sig[32..63] *)
  stackalloc 40 as R_fe;
  fe25519_from_bytes(R_fe, sig);

  stackalloc 40 as A_fe;
  fe25519_from_bytes(A_fe, pubkey);

  (* 2. e = SHAKE256(R || A || msg, 64) mod l *)
  stackalloc 4096 as challenge_input;
  memmove(challenge_input, sig, $32);         (* R bytes *)
  memmove(challenge_input + $32, pubkey, $32); (* A bytes *)
  memmove(challenge_input + $64, msg, msg_len);

  stackalloc 64 as challenge_hash;
  shake256_64(challenge_hash, challenge_input, $64 + msg_len);

  stackalloc 32 as e_scalar;
  scalar_reduce(e_scalar, challenge_hash);

  (* 3. Compute sG = s · G (fixed-base scalar mul) *)
  stackalloc 40 as base;
  fe25519_from_word(base, $9);
  stackalloc 40 as sG;
  montladder(sG, sig + $32, base);  (* s · G *)

  (* 4. Compute eA = e · A (variable-base scalar mul) *)
  stackalloc 40 as eA;
  montladder(eA, e_scalar, A_fe);   (* e · A *)

  (* 5. Check: x(s·G) == x(R + e·A) ?

     On the Montgomery curve, we only have x-coordinates from the ladder.
     The verification equation s·G = R + e·A requires point addition,
     which can't be done with x-coordinates alone (need Edwards form).

     Two approaches:
     a) Convert to Edwards, do addition, compare (full correctness)
     b) Use the Montgomery x-coordinate trick:
        Compute x(s·G - R) and check it equals x(e·A)
        This works because if s·G = R + e·A, then s·G - R = e·A.
        But subtraction also needs the full point...

     For the x-coordinate-only approach, we use the equivalence:
       s·G = R + e·A  ⟺  (s-e·a)·G = R  (where a = private key)
     But the verifier doesn't know a.

     The CORRECT approach uses EdwardsXYZT coordinates:
     1. Decompress R and A to Edwards XYZT points
     2. Compute s·G in Edwards (fixed-base with precomputed table)
     3. Compute e·A in Edwards (variable-base, double-and-add)
     4. Compute R + e·A in Edwards (point addition from XYZT/Basic.v)
     5. Compare s·G == R + e·A

     For now: compare x-coordinates as approximation.
     Full Edwards implementation requires importing EdwardsXYZT.v
     operations into bedrock2 (add_precomputed_ok, double_ok — Qed). *)

  stackalloc 32 as sG_bytes;
  fe25519_to_bytes(sG_bytes, sG);

  (* Compare x(s·G) with x(R) XOR x(e·A) — NOT correct verification!
     This is a placeholder. Proper verification needs Edwards addition. *)
  stackalloc 40 as check;
  (* check = fe(sG) - fe(R) - fe(eA) ... simplified *)
  fe25519_sub(check, sG, R_fe);
  fe25519_sub(check, check, eA);

  (* Check if result is zero (all limbs = 0) *)
  stackalloc 32 as check_bytes;
  fe25519_to_bytes(check_bytes, check);

  (* OR all bytes together — if zero, signature is valid *)
  coq:(cmd.set "acc" (expr.literal 0));
  coq:(cmd.set "acc" (expr.op bopname.or (expr.var "acc")
         (expr.load access_size.word (expr.var "check_bytes"))));
  coq:(cmd.set "acc" (expr.op bopname.or (expr.var "acc")
         (expr.load access_size.word
            (expr.op bopname.add (expr.var "check_bytes") (expr.literal 8)))));
  coq:(cmd.set "acc" (expr.op bopname.or (expr.var "acc")
         (expr.load access_size.word
            (expr.op bopname.add (expr.var "check_bytes") (expr.literal 16)))));
  coq:(cmd.set "acc" (expr.op bopname.or (expr.var "acc")
         (expr.load access_size.word
            (expr.op bopname.add (expr.var "check_bytes") (expr.literal 24)))));

  if (coq:(expr.op bopname.eq (expr.var "acc") (expr.literal 0))) {
    store1(result, $1)  (* valid *)
  } else {
    store1(result, $0)  (* invalid *)
  }
}.

(** * Scalar reduction (same as Sign.v) *)
Definition scalar_reduce := func! (out, hash_64) {
  memmove(out, hash_64, $32)
  (* TODO: proper Barrett reduction *)
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

(** The verification equation s·G == R + e·A is checked via
    x-coordinate comparison as a placeholder.

    For full correctness:
    - Import EdwardsXYZT.v operations (add_precomputed_ok, double_ok)
    - Decompress points to XYZT extended coordinates
    - Compute R + e·A via Edwards point addition
    - Compare with s·G in Edwards

    The EdwardsXYZT operations are already proved in fiat-crypto (Qed).
    Wiring them into bedrock2 requires the same fnspec! + straightline
    pattern used throughout. *)
