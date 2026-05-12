(** * RistrettoConsts — Field constants for Ristretto255 encode/decode.
 *
 * These are the four base-field constants specified in §3.1 of
 * draft-irtf-cfrg-ristretto255-decaf448-03.
 *
 * All constants live in F_p where p = 2^255 - 19 (Ed25519 base field).
 *
 *  - [ristretto_SQRT_M1]          = sqrt(-1) mod p
 *                                 = 2^((p-1)/4) mod p
 *  - [ristretto_d]                = the Ed25519 d constant
 *                                 = -121665 / 121666 mod p
 *  - [ristretto_INVSQRT_A_MINUS_D] = 1 / sqrt(a - d) mod p, where a = -1
 *  - [ristretto_SQRT_AD_MINUS_ONE] = sqrt(a*d - 1) mod p (a = -1)
 *
 * NOTE.  Decompress's [ed25519_sqrtm1] in DecompressVerified.v carries
 * an INCORRECT value (placeholder); we therefore do NOT reuse it.  The
 * value below was independently verified by [vm_compute] sanity checks
 * (see lemmas).
 *)

From Stdlib Require Import ZArith.ZArith.
Require Import Bedrock.End2End.Ed25519.CompressVerified.
Require Import Bedrock.End2End.Ed25519.XyztAddVerified.
Local Open Scope Z_scope.

(** sqrt(-1) mod p — i.e. 2^((p-1)/4) mod p. *)
Definition ristretto_SQRT_M1 : Z :=
  19681161376707505956807079304988542015446066515923890162744021073123829784752.

(** Edwards [d] constant — reuses [ed25519_d]. *)
Definition ristretto_d : Z := ed25519_d.

(** [1 / sqrt(a - d)] mod p with a = -1, so [a - d = -1 - d].
    Decimal value from IETF draft §3.1. *)
Definition ristretto_INVSQRT_A_MINUS_D : Z :=
  54469307008909316920995813868745141605393597292927456921205312896311721017578.

(** [sqrt(a*d - 1)] mod p with a = -1.  Decimal value from IETF draft §3.1. *)
Definition ristretto_SQRT_AD_MINUS_ONE : Z :=
  25063068953384623474111414158702152701244531502492656460079210482610430750235.

(** ** Sanity check: SQRT_M1^2 ≡ -1 (mod p). *)
Lemma ristretto_SQRT_M1_sq :
  (ristretto_SQRT_M1 * ristretto_SQRT_M1) mod ed25519_p = ed25519_p - 1.
Proof. vm_compute. reflexivity. Qed.

(** ** Sanity check: INVSQRT_A_MINUS_D^2 * (a - d) ≡ 1 (mod p), a = -1. *)
Lemma ristretto_INVSQRT_A_MINUS_D_sq :
  (ristretto_INVSQRT_A_MINUS_D
   * ristretto_INVSQRT_A_MINUS_D
   * ((ed25519_p - 1 - ed25519_d) mod ed25519_p)) mod ed25519_p = 1.
Proof. vm_compute. reflexivity. Qed.

(** ** Sanity check: SQRT_AD_MINUS_ONE^2 ≡ -d - 1 ≡ a*d - 1 (mod p). *)
Lemma ristretto_SQRT_AD_MINUS_ONE_sq :
  (ristretto_SQRT_AD_MINUS_ONE * ristretto_SQRT_AD_MINUS_ONE) mod ed25519_p
  = (ed25519_p - ed25519_d - 1) mod ed25519_p.
Proof. vm_compute. reflexivity. Qed.
