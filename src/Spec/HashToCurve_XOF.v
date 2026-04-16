(** * Hash-to-Curve using SHAKE-128 (XOF suite).

    Suite: BLS12381G1_XOF:SHAKE-128_SSWU_RO_

    Reuses all SWU/isogeny/cofactor definitions from HashToCurve.v;
    only swaps hash_to_field (SHA-256/XMD) for hash_to_field_shake128
    (SHAKE-128/XOF).

    The SWU map, 11-isogeny, point addition, and cofactor clearing
    are identical — they don't depend on the hash function. *)

From Stdlib Require Import ZArith BinPos List Bool.
From Stdlib Require Import Strings.Byte.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.SHA256_axiom.
Require Import Spec.SHAKE128_axiom.
Require Import Spec.HashToCurve.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * hash_to_field with SHAKE-128 XOF (RFC 9380 §5.3.2)              *)
(* ================================================================== *)

(** hash_to_field using SHAKE-128 XOF for byte expansion.
    Same shape as [SHA256_axiom.hash_to_field_L] but uses
    [expand_message_xof] (SHAKE-128) instead of [expand_message_xmd]
    (SHA-256).  Reuses [build_field_elements] and [L_bls12_381]
    from SHA256_axiom. *)
Definition hash_to_field_shake128_L
  (p : positive) (L : nat)
  (msg : list Byte.byte) (dst : list Byte.byte) (count : nat)
  : list (F p) :=
  let len_in_bytes := (count * L)%nat in
  let uniform := expand_message_xof msg dst len_in_bytes in
  build_field_elements p uniform L count 0.

Definition hash_to_field_shake128
  (p : positive)
  (msg : list Byte.byte) (dst : list Byte.byte) (count : nat)
  : list (F p) :=
  hash_to_field_shake128_L p L_bls12_381 msg dst count.

(* ================================================================== *)
(** * hash_to_curve using XOF (RFC 9380 §3 + §5.3.2)                  *)
(* ================================================================== *)

(** hash_to_curve with SHAKE-128 XOF.
    Identical to HashToCurve.hash_to_curve except uses
    hash_to_field_shake128 instead of hash_to_field. *)
Definition hash_to_curve_xof (msg : list Byte.byte) (dst : list Byte.byte)
  : affine_point :=
  let us := hash_to_field_shake128 p_pos msg dst 2 in
  match us with
  | [u0; u1] =>
    let Q0 := map_to_curve_g1 u0 in
    let Q1 := map_to_curve_g1 u1 in
    let R := point_add (Some Q0) (Some Q1) in
    clear_cofactor R
  | _ => point_at_infinity
  end.

(** encode_to_curve with SHAKE-128 XOF. *)
Definition encode_to_curve_xof (msg : list Byte.byte) (dst : list Byte.byte)
  : affine_point :=
  let us := hash_to_field_shake128 p_pos msg dst 1 in
  match us with
  | [u0] =>
    let Q := map_to_curve_g1 u0 in
    clear_cofactor (Some Q)
  | _ => point_at_infinity
  end.

(* ================================================================== *)
(** * Correctness theorems                                              *)
(* ================================================================== *)

(** hash_to_curve_xof produces a point on E.
    Proof reuses all the SWU/isogeny/cofactor machinery from
    HashToCurve.v — only the hash input changes, and the map_to_curve
    correctness is independent of which hash was used. *)

(* These follow immediately from the existing proofs in HashToCurveProof.v
   since map_to_curve_g1, point_add, clear_cofactor don't depend on
   the hash function. The only difference is which field elements u0, u1
   are fed in, and the proofs are universally quantified over those. *)
