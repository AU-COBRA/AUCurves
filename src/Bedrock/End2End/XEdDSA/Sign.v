(** * XEdDSA signature generation — bedrock2 specification

    Signal's XEdDSA: sign with X25519 private key via Edwards conversion.

    Algorithm:
      1. a = clamp(privkey)
      2. A = a · G (Edwards basepoint multiplication)
      3. If sign_bit(A) = 1: a = -a, A = -A
      4. r = SHA-512(Z || a || msg) mod l   (synthetic nonce, Z = 64 random bytes)
      5. R = r · G
      6. e = SHA-512(R || A || msg) mod l   (challenge)
      7. s = (r + e · a) mod l               (response)
      8. Output: (R, s) — 64 bytes total

    ## Verification chain
    Spec correctness: Spec/XEdDSA.v (functional)
    Security: Commitments/XEdDSA_Security.v (SSProve Schnorr)
    Implementation: this file (bedrock2 WP)
    Compilation: ToJasmin → jasminc → x86-64

    Step 8c of the Signal verification plan. *)

From Coq Require Import ZArith Lia String List.
From Coq.Init Require Import Byte.
Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry.
Require Import bedrock2.Map.Separation.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Import Syntax Syntax.Coercions NotationsCustomEntry ListNotations.

(** TODO: bedrock2 implementation + WP proof.

    Dependencies:
    - Ristretto/ScalarMult.v (Step 8b) for scalar multiplication
    - SHA512_axiom (in Signal/) for nonce and challenge hashing
    - Scalar arithmetic mod l (from Curve25519.v)
    - Clamp function (from X25519/clamp.v, read-only)

    The bedrock2 function:
    Definition xeddsa_sign := func! (sig_out, privkey, msg, msg_len, random) {
      (* 1. clamp *)
      clamp(privkey) ;;
      (* 2. compute public key *)
      stackalloc 32 as pubkey { scalarmult_base(pubkey, privkey) } ;;
      (* 3. nonce: r = SHA512(random || privkey || msg) mod l *)
      ... ;;
      (* 4. R = r · G *)
      ... ;;
      (* 5. e = SHA512(R || pubkey || msg) mod l *)
      ... ;;
      (* 6. s = r + e*a mod l *)
      ... ;;
      (* 7. output *)
      store(sig_out, R) ;; store(sig_out+32, s)
    }.

    Template: X25519/clamp.v + MontgomeryLadder.v
    Estimated: 1 week *)
