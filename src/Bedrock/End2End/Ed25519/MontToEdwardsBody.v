(** * MontToEdwardsBody — rust_cmd_ed AST for the
 *     Montgomery-u → Edwards-y compressed-encoding map.
 *
 *  Birational map: given the affine Montgomery x-coordinate
 *  [u : F p] (p = 2^255 − 19), output the 32-byte compressed
 *  Edwards encoding of [(?, y)] where
 *
 *     y = (u − 1) · inv(u + 1)   mod p.
 *
 *  The high bit (bit 255) of the 32-byte output is the sign-bit of
 *  the corresponding Edwards x-coordinate.  At this layer the
 *  caller passes the sign bit in as an extra input scalar
 *  [sign_bit] (0 or 1); the actual x-sign computation is the
 *  XEdDSA-sign caller's responsibility.
 *
 *  Rejection: [u + 1 = 0] (i.e., [u = −1 ≡ p − 1]) makes the map
 *  undefined; the caller must guarantee [u + 1 ≠ 0].  The body
 *  does NOT check this; the correctness statement assumes it.
 *
 *  Leaves (declared external — [REdCall]; their semantics is
 *  supplied by the caller's [callee_post] oracle):
 *    - fe25519_one  : (out)               → out := 1 ∈ F p
 *    - fe25519_add  : (out, a, b)         → out := a + b
 *    - fe25519_sub  : (out, a, b)         → out := a − b
 *    - fe25519_mul  : (out, a, b)         → out := a · b
 *    - fe25519_invert : (out, a)          → out := a^(p-2)
 *      (instantiated by the verified [Fe25519InvertBody.v] chain
 *       via [REdCall], with [fe25519_invert_correct] discharged at
 *       the call site)
 *    - fe25519_to_bytes : (out, a)        → out := 32-byte LE pack
 *    - bytes_set_sign_bit : (out, sign_bit)
 *
 *  Phase 2.B of "extend the IR": Part B of the three-chain prompt.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Helpers                                                       *)
(* ================================================================ *)

Definition LFp (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TFp25519 |}.

Definition LBytes32 (v : String.string) : located_ed :=
  {| loc_var := v; loc_type := TBytes 32 |}.

Fixpoint seqN (l : list rust_cmd_ed) : rust_cmd_ed :=
  match l with
  | [] => REdSkip
  | [c] => c
  | c :: cs => REdSeq c (seqN cs)
  end.

(* ================================================================ *)
(* §2. Body                                                          *)
(* ================================================================ *)

(** [mont_to_edwards_body] body.
    Inputs:  [u_loc      : TFp25519]   the Montgomery u-coordinate
             [sign_bit_loc : TBytes 32] one-byte sign packed in a
                                        32-byte slot whose [byte 0]
                                        holds the sign bit (0/1).
    Output:  [dest        : TBytes 32]   compressed Edwards encoding.

    Internal slots:
             [one_v, u_plus_1, u_minus_1, inv_v, y_v : TFp25519]
             [y_bytes : TBytes 32]
*)
Definition mont_to_edwards_body : function_body_ed :=
  fun dest args =>
    match args with
    | [u_loc; sign_bit_loc] =>
        REdLetZero "one_v"     TFp25519 (
        REdLetZero "u_plus_1"  TFp25519 (
        REdLetZero "u_minus_1" TFp25519 (
        REdLetZero "inv_v"     TFp25519 (
        REdLetZero "y_v"       TFp25519 (
        REdLetZero "y_bytes"   (TBytes 32) (
        seqN
          [ (* one_v := 1 *)
            REdCall "fe25519_one" (LFp "one_v") []
          (* u_plus_1 := u + 1 *)
          ; REdCall "fe25519_add"
                    (LFp "u_plus_1") [u_loc; LFp "one_v"]
          (* u_minus_1 := u - 1 *)
          ; REdCall "fe25519_sub"
                    (LFp "u_minus_1") [u_loc; LFp "one_v"]
          (* inv_v := (u + 1)^(p-2) *)
          ; REdCall "fe25519_invert" (LFp "inv_v") [LFp "u_plus_1"]
          (* y_v := (u - 1) · inv_v *)
          ; REdCall "fe25519_mul"
                    (LFp "y_v") [LFp "u_minus_1"; LFp "inv_v"]
          (* y_bytes := pack(y_v) — 32 LE bytes *)
          ; REdCall "fe25519_to_bytes"
                    (LBytes32 "y_bytes") [LFp "y_v"]
          (* dest := set_sign_bit(y_bytes, sign_bit_loc[0]) *)
          ; REdCall "bytes_set_sign_bit"
                    dest [LBytes32 "y_bytes"; sign_bit_loc]
          ]
        ))))))
    | _ => REdSkip
    end.
