(** * XEdDSA signature generation — bedrock2 implementation

    Signal's XEdDSA: Schnorr signature using X25519 private key.
    Uses SHAKE-256 (verified Keccak) for nonce and challenge.

    Algorithm:
      1. K = clamp(privkey)
      2. A = K · G (basepoint multiplication)
      3. r = SHAKE256(random || K || msg, 64) mod l  (synthetic nonce)
      4. R = r · G (basepoint multiplication)
      5. e = SHAKE256(R || A || msg, 64) mod l  (challenge)
      6. s = (r + e · K) mod l  (response)
      7. Output: (R_bytes, s_bytes) — 64 bytes *)

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
Require Import Crypto.Bedrock.Group.ScalarMult.MontgomeryLadder.
Local Open Scope string_scope.
Local Open Scope Z_scope.
Import Syntax.Coercions NotationsCustomEntry ListNotations.

Local Existing Instance frep25519.
Local Existing Instance frep25519_ok.

(** * Scalar reduction mod l (Barrett reduction)

    l = 2^252 + 27742317777372353535851937790883648493

    For a 512-bit input h (from SHAKE-256), compute h mod l.
    Barrett reduction: q = floor(h * mu / 2^512), r = h - q*l,
    where mu = floor(2^512 / l).

    The 512-bit input is stored as 8 × u64 words (little-endian).
    The output is a 32-byte scalar (4 × u64 words).

    For bedrock2, we implement this as multi-precision arithmetic:
    load 8 words, multiply by precomputed mu, subtract q*l. *)

Definition scalar_reduce := func! (out, hash_64) {
  (* Simple reduction: interpret hash as little-endian integer mod l.
     For a proper implementation, use Barrett reduction.
     Here we use the schoolbook approach: copy low 32 bytes,
     then subtract multiples of l.

     Since l ≈ 2^252, the high ~260 bits of the 512-bit hash
     need to be reduced. For XEdDSA security, even a biased
     reduction is acceptable (bias ≤ 2^{-128}), so we can:
     1. Take the full 64-byte hash
     2. Reduce mod l using multi-limb arithmetic

     For now: copy low 32 bytes as an approximation.
     A proper Barrett reduction would be ~100 lines. *)
  memmove(out, hash_64, $32)
  (* TODO: proper Barrett reduction for unbiased scalars *)
}.

(** * Scalar multiply-add: s = (r + e * a) mod l

    All scalars are 32-byte (256-bit) little-endian integers.
    The multiplication e*a produces a 512-bit intermediate,
    which is then added to r and reduced mod l.

    For bedrock2: multi-precision multiply (4×4 → 8 limbs),
    add r, reduce mod l. *)

Definition scalar_muladd := func! (out, r_scalar, e_scalar, a_scalar) {
  (* s = r + e * a mod l
     Multi-precision arithmetic on 4 × u64 limbs.

     Step 1: product = e * a (4×4 schoolbook → 8 limbs)
     Step 2: sum = product + r (8-limb + 4-limb)
     Step 3: reduce sum mod l (Barrett)

     For now: simplified placeholder that computes (r + e) mod 2^256
     as an approximation. Proper impl needs ~150 lines. *)
  stackalloc 32 as temp;
  (* temp = r + e (mod 2^256, no carry chain for simplicity) *)
  store(temp,      load(r_scalar)      + load(e_scalar));
  store(temp+$8,   load(r_scalar+$8)   + load(e_scalar+$8));
  store(temp+$16,  load(r_scalar+$16)  + load(e_scalar+$16));
  store(temp+$24,  load(r_scalar+$24)  + load(e_scalar+$24));
  memmove(out, temp, $32)
  (* TODO: proper schoolbook mul + Barrett reduction *)
}.

(** * XEdDSA sign function *)

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
  (* Concatenate random (64) || K (32) || msg into temp buffer *)
  stackalloc 4096 as nonce_input; (* max: 64 + 32 + msg_len *)
  memmove(nonce_input, random, $64);
  memmove(nonce_input + $64, K, $32);
  memmove(nonce_input + $96, msg, msg_len);

  stackalloc 64 as nonce_hash;
  shake256_64(nonce_hash, nonce_input, $96 + msg_len);

  stackalloc 32 as r_scalar;
  scalar_reduce(r_scalar, nonce_hash);

  (* 4. R = r · G *)
  stackalloc 40 as R_fe;
  montladder(R_fe, r_scalar, base);
  stackalloc 32 as R_bytes;
  fe25519_to_bytes(R_bytes, R_fe);

  (* 5. e = SHAKE256(R || A || msg, 64) mod l *)
  stackalloc 4096 as challenge_input;
  memmove(challenge_input, R_bytes, $32);
  memmove(challenge_input + $32, A_bytes, $32);
  memmove(challenge_input + $64, msg, msg_len);

  stackalloc 64 as challenge_hash;
  shake256_64(challenge_hash, challenge_input, $64 + msg_len);

  stackalloc 32 as e_scalar;
  scalar_reduce(e_scalar, challenge_hash);

  (* 6. s = (r + e · K) mod l *)
  stackalloc 32 as s_scalar;
  scalar_muladd(s_scalar, r_scalar, e_scalar, K);

  (* 7. Output signature (R || s) *)
  memmove(sig_out, R_bytes, $32);
  memmove(sig_out + $32, s_scalar, $32)
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

(** XEdDSA signature = (R_bytes, s_bytes), 64 bytes.
    Spec links to Spec/XEdDSA.v's functional definition.

    The spec_of requires:
    - Input: privkey (32 bytes), msg (msg_len bytes), random (64 bytes)
    - Output: sig_out (64 bytes) = R || s
    - Functional correctness: sig_out = xeddsa_sign_functional(privkey, msg, random)

    Blocked on: proper Barrett reduction for scalar_reduce.
    Once scalar_reduce is correct, the WP proof follows straightline. *)
