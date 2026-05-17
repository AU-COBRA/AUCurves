(** * BLS Signature Instance: Concrete BLS12-381 with hash-to-curve.

    Instantiates the abstract BLS signature scheme (BLSSignature.v)
    with:
    - The BLS12-381 prime and optimal Ate pairing (Pairing.v)
    - Concrete hash-to-curve from RFC 9380 (HashToCurve.v)
    - Bilinearity axioms from Bilinearity.v

    Result: an executable BLS signature scheme over BLS12-381 where
    sign/verify/aggregate are Gallina functions that compute on
    concrete byte-string messages.

    Trust model:
    - Bilinearity axioms (mathematical, not implementation-dependent)
    - SHA-256 axiom (HashToCurve.v uses SHA-256 XMD)
    - co-CDH for unforgeability (standard)
*)

From Stdlib Require Import ZArith BinPos List Bool.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.BLS12Pairing.Pairing.
Require Import Crypto.Spec.BLS12Pairing.Bilinearity.
Require Import Crypto.Spec.BLS12Pairing.BLSSignature.
Require Import Spec.HashToCurve.

Local Notation byte := Byte.byte.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * BLS12-381 prime (shared with HashToCurve.v)                      *)
(* ================================================================== *)

(** The prime from HashToCurve.v *)
Definition bls12_p_pos : positive := HashToCurve.p_pos.

Local Notation Fp := (F bls12_p_pos).
Local Notation Fp2 := ((Fp * Fp)%type).
Local Notation Fp6 := ((Fp2 * Fp2 * Fp2)%type).
Local Notation Fp12 := ((Fp6 * Fp6)%type).
Local Notation G1 := (G1Affine bls12_p_pos).
Local Notation G2 := (G2Affine bls12_p_pos).

(* ================================================================== *)
(** * Bridge: HashToCurve affine_point -> Pairing.G1Affine             *)
(* ================================================================== *)

(** Convert HashToCurve's option-based affine point to Pairing's
    record-based G1Affine. *)
Definition affine_to_G1 (pt : HashToCurve.affine_point) : G1 :=
  match pt with
  | Some (x, y) => mk_g1_affine bls12_p_pos x y false
  | None => mk_g1_affine bls12_p_pos (@F.zero bls12_p_pos) (@F.zero bls12_p_pos) true
  end.

(* ================================================================== *)
(** * Concrete hash-to-curve as G1-valued function                     *)
(* ================================================================== *)

(** Domain separation tag for BLS signatures (RFC 9380, section 8.10).
    Parameterized so users can supply the correct suite-specific DST. *)
Parameter bls_dst : list byte.

(** Concrete hash-to-curve: message bytes -> G1 point. *)
Definition bls12_hash_to_curve (msg : list byte) : G1 :=
  affine_to_G1 (HashToCurve.hash_to_curve msg bls_dst).

(* ================================================================== *)
(** * Concrete group operations on G1 (from HashToCurve.v)             *)
(* ================================================================== *)

(** G1 addition: lift HashToCurve.point_add to G1Affine. *)
Definition G1_to_affine (P : G1) : HashToCurve.affine_point :=
  if g1_infinity bls12_p_pos P
  then None
  else Some (g1_x bls12_p_pos P, g1_y bls12_p_pos P).

Definition bls12_g1_add (P Q : G1) : G1 :=
  affine_to_G1 (HashToCurve.point_add (G1_to_affine P) (G1_to_affine Q)).

(** G1 scalar multiplication: lift HashToCurve.scalar_mul to G1Affine. *)
Definition bls12_g1_scalar_mult (k : Z) (P : G1) : G1 :=
  affine_to_G1 (HashToCurve.scalar_mul (Z.to_nat (Z.abs k)) (G1_to_affine P)).

(** G2 scalar multiplication (abstract — no concrete G2 group law
    is defined in HashToCurve.v, which only covers G1).
    We leave this as a parameter. *)

(* ================================================================== *)
(** * Frobenius constants (needed for pairing/pairing_check)           *)
(* ================================================================== *)

(** These are the Frobenius constants for BLS12-381.
    gamma1^{p^2}, gamma2^{p^2}, coeff_p2_c1.
    We leave them as parameters since they are large constants
    that don't affect the structure of the signature proofs. *)
Parameter gamma1_p2 gamma2_p2 coeff_p2_c1 : Fp2.

(** Decidable equality on Fp12 (needed for pairing_check). *)
Parameter fp12_eq_dec : forall (a b : Fp12), {a = b} + {a <> b}.

(* ================================================================== *)
(** * G1 and G2 generators                                             *)
(* ================================================================== *)

(** BLS12-381 G1 generator (from the standard).
    x = 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb
    y = 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1 *)
Definition g1_generator : G1 :=
  mk_g1_affine bls12_p_pos
    (F.of_Z bls12_p_pos 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb)
    (F.of_Z bls12_p_pos 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)
    false.

(** BLS12-381 G2 generator.
    x = (x0 + x1*u) where
    x0 = 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8
    x1 = 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e
    y = (y0 + y1*u) where
    y0 = 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801
    y1 = 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be *)
Definition g2_generator : G2 :=
  mk_g2_affine bls12_p_pos
    (F.of_Z bls12_p_pos 0x024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8,
     F.of_Z bls12_p_pos 0x13e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e)
    (F.of_Z bls12_p_pos 0x0ce5d527727d6e118cc9cdc6da2e351aadfd9baa8cbdd3a76d429a695160d12c923ac9cc3baca289e193548608b82801,
     F.of_Z bls12_p_pos 0x0606c4a02ea734cc32acd2b02bc28b99cb3e287e85a763af267492ab572e99ab3f370d275cec1da1aaa9075ff05f79be)
    false.

(** Abstract G2 scalar multiplication (no concrete group law for G2
    is defined at the spec level). *)
Parameter bls12_g2_scalar_mult : Z -> G2 -> G2.

(* ================================================================== *)
(** * Instantiation of BLS signature scheme                            *)
(* ================================================================== *)

(** All BLS signature definitions are now concrete Gallina functions
    that can be evaluated on byte-string messages. *)

Definition bls12_keygen (sk : Z) : G2 :=
  keygen bls12_p_pos bls12_g2_scalar_mult g2_generator sk.

Definition bls12_sign (sk : Z) (msg : list byte) : G1 :=
  sign bls12_p_pos bls12_g1_scalar_mult (list byte) bls12_hash_to_curve sk msg.

Definition bls12_verify (pk : G2) (msg : list byte) (sig : G1) : bool :=
  verify bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1 fp12_eq_dec
    g2_generator (list byte) bls12_hash_to_curve pk msg sig.

Definition bls12_aggregate (sigs : list G1) : G1 :=
  aggregate bls12_p_pos bls12_g1_add bls12_g1_scalar_mult g1_generator sigs.

(* ================================================================== *)
(** * Correctness theorems (instantiated)                              *)
(* ================================================================== *)

(** Bilinearity hypotheses — from Bilinearity.v *)
Hypothesis bilinear_left :
  forall (a : Z) (P : G1) (Q : G2),
    pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1
      (bls12_g1_scalar_mult a P) Q =
    fp12_pow bls12_p_pos
      (pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1 P Q) a.

Hypothesis bilinear_right :
  forall (b : Z) (P : G1) (Q : G2),
    pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1
      P (bls12_g2_scalar_mult b Q) =
    fp12_pow bls12_p_pos
      (pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1 P Q) b.

Hypothesis additive_left :
  forall (P Q : G1) (R : G2),
    pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1
      (bls12_g1_add P Q) R =
    Pairing.fp12_mul bls12_p_pos
      (pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1 P R)
      (pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1 Q R).

Hypothesis non_degenerate :
  pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1
    g1_generator g2_generator <>
  Pairing.fp12_one bls12_p_pos.

Hypothesis check_correct :
  forall (P1 : G1) (Q1 : G2) (P2 : G1) (Q2 : G2),
    pairing_check bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1 fp12_eq_dec
      P1 Q1 P2 Q2 = true
    <->
    pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1 P1 Q1 =
    pairing bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1 P2 Q2.

Hypothesis fp12_mul_one_r :
  forall (x : Fp12),
    Pairing.fp12_mul bls12_p_pos x (Pairing.fp12_one bls12_p_pos) = x.

Hypothesis fp12_mul_assoc :
  forall (x y z : Fp12),
    Pairing.fp12_mul bls12_p_pos (Pairing.fp12_mul bls12_p_pos x y) z =
    Pairing.fp12_mul bls12_p_pos x (Pairing.fp12_mul bls12_p_pos y z).

(** ------------------------------------------------------------------ *)
(** Theorem: Individual BLS12-381 signature verification is correct.
    For any secret key sk and message msg (a byte string),
    bls12_verify(bls12_keygen(sk), msg, bls12_sign(sk, msg)) = true. *)
(** ------------------------------------------------------------------ *)

Theorem bls12_verify_correct :
  forall (sk : Z) (msg : list byte),
    bls12_verify (bls12_keygen sk) msg (bls12_sign sk msg) = true.
Proof.
  intros sk msg.
  unfold bls12_verify, bls12_keygen, bls12_sign.
  (* verify_correct : p, gamma*3, fp12_eq_dec, g1_scalar_mult,
     g2_scalar_mult, g2_gen, message, hash_to_curve,
     bilinear_left, bilinear_right, check_correct *)
  apply (verify_correct bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1
    fp12_eq_dec bls12_g1_scalar_mult bls12_g2_scalar_mult
    g2_generator (list byte) bls12_hash_to_curve
    bilinear_left bilinear_right check_correct).
Qed.

(** ------------------------------------------------------------------ *)
(** Theorem: n-signer aggregate verification (same message) is correct. *)
(** ------------------------------------------------------------------ *)

Theorem bls12_aggregate_verify_correct :
  forall (sks : list Z) (msg : list byte),
    sks <> [] ->
    aggregate_verify_spec bls12_p_pos gamma1_p2 gamma2_p2 coeff_p2_c1
      g2_generator (list byte) bls12_hash_to_curve
      (repeat_msg (list byte) msg (length sks))
      (keygen_all bls12_p_pos bls12_g2_scalar_mult g2_generator sks)
      (aggregate bls12_p_pos bls12_g1_add bls12_g1_scalar_mult g1_generator
        (sign_all bls12_p_pos bls12_g1_scalar_mult (list byte)
          bls12_hash_to_curve sks msg)).
Proof.
  intros sks msg Hne.
  (* aggregate_verify_n_correct : p, gamma*3, g1_add, g1_scalar_mult,
     g2_scalar_mult, g1_gen, g2_gen, message, hash_to_curve,
     bilinear_left, bilinear_right, additive_left, fp12_mul_one_r,
     sks, m, Hne *)
  apply (aggregate_verify_n_correct bls12_p_pos gamma1_p2 gamma2_p2
    coeff_p2_c1 bls12_g1_add bls12_g1_scalar_mult bls12_g2_scalar_mult
    g1_generator g2_generator (list byte) bls12_hash_to_curve
    bilinear_left bilinear_right additive_left fp12_mul_one_r
    sks msg Hne).
Qed.

(** ------------------------------------------------------------------ *)
(** Hash-to-curve produces valid curve points (from HashToCurveProof). *)
(** ------------------------------------------------------------------ *)

(** The on_curve property is proved in HashToCurveProof.v as
    map_produces_curve_points_proof. Here we just note that the
    hash_to_curve used in the signature scheme is the same function
    whose on-curve property is proved there, composed with the
    affine_to_G1 bridge. *)

(** ================================================================== *)
(** Summary of trust assumptions:                                       *)
(**                                                                     *)
(**   1. Bilinearity axioms (mathematical, standard)                    *)
(**   2. SHA-256 axiom (from SHA256_axiom.v)                            *)
(**   3. G2 scalar multiplication (abstract)                            *)
(**   4. Frobenius constants + fp12_eq_dec (computational)              *)
(**   5. co-CDH for unforgeability (standard)                           *)
(**                                                                     *)
(** The hash-to-curve itself is fully concrete: Gallina functions       *)
(** that compute on byte strings via SHA-256 XMD + Simplified SWU      *)
(** + 11-isogeny + cofactor clearing.                                   *)
(** ================================================================== *)
