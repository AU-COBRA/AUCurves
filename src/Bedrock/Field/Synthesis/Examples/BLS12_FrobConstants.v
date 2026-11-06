(** * BLS12-381 Frobenius constants: loader values = powers of xi.

    For each constant loader of [BLS12_Pairing.v]
    (bls12_load_gamma1_p2, bls12_load_gamma2_p2, bls12_load_w_frob_p2_c1,
     bls12_load_gamma1, bls12_load_gamma2, bls12_load_w_frob_c1)
    this file defines the Fp2 value whose Montgomery limbs the loader stores
    ([*_loaded]) and proves that it equals the Gallina constant, a power of
    xi = 1 + u computed by [fp2_pow] (the definitions of
    SSProve/Commitments [theories/Concrete/BLS12_Defs.v], repeated here
    verbatim since AUCurves cannot import Commitments):

      frob_gamma1_p2        = xi^((p^2-1)/3)
      frob_gamma2_p2        = xi^(2((p^2-1)/3))
      frob_coeff_fp12_p2_c1 = xi^((p^2-1)/6)
      frob_gamma1           = xi^((p-1)/3)
      frob_gamma2           = xi^(2((p-1)/3))
      frob_coeff_fp12_c1    = xi^((p-1)/6)

    Montgomery form: the stored limbs l0..l5 (little endian, 64-bit) denote
    (sum l_i 2^(64 i)) * R^-1 mod p with R = 2^384.

    This file imports only Stdlib and Crypto (no mathcomp), so the large Z
    literals stay binary.  Each equation is a lemma of its own, proved by
    vm_compute. *)

From Stdlib Require Import ZArith.ZArith Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.FinalExpEquiv.

Local Open Scope Z_scope.

Module BLS12_381_Frob.

  (** The base-field prime, as in Commitments' [BLS12_381.p]. *)
  Definition p : positive := Z.to_pos bls_p.

  Local Notation Fp := (F p).
  Local Notation Fp2 := ((Fp * Fp)%type).

  (** ** Gallina constants (verbatim from Commitments BLS12_Defs.v) *)

  Fixpoint fp2_pow_pos (a : Fp2) (n : positive) : Fp2 :=
    match n with
    | xH => a
    | xO n' => fp2_sqr p (fp2_pow_pos a n')
    | xI n' => fp2_mul p a (fp2_sqr p (fp2_pow_pos a n'))
    end.

  Definition fp2_pow (a : Fp2) (e : Z) : Fp2 :=
    match e with
    | Zpos n => fp2_pow_pos a n
    | _ => fp2_one p
    end.

  Definition xi : Fp2 := (F.one, F.one).

  Definition frob_gamma1_p2 : Fp2 := fp2_pow xi ((bls_p ^ 2 - 1) / 3).
  Definition frob_gamma2_p2 : Fp2 := fp2_pow xi (2 * ((bls_p ^ 2 - 1) / 3)).
  Definition frob_coeff_fp12_p2_c1 : Fp2 := fp2_pow xi ((bls_p ^ 2 - 1) / 6).

  (** The p (not p^2) versions, used by the DSD hard part. *)
  Definition frob_gamma1 : Fp2 := fp2_pow xi ((bls_p - 1) / 3).
  Definition frob_gamma2 : Fp2 := fp2_pow xi (2 * ((bls_p - 1) / 3)).
  Definition frob_coeff_fp12_c1 : Fp2 := fp2_pow xi ((bls_p - 1) / 6).

  (** ** Montgomery decoding *)

  (** R^-1 mod p, R = 2^384. *)
  Definition R_inv : Z :=
    0x14fec701e8fb0ce9ed5e64273c4f538b1797ab1458a88de9343ea97914956dc87fe11274d898fafbf4d38259380b4820.

  Lemma R_inv_correct : (2 ^ 384 * R_inv) mod bls_p = 1.
  Proof. vm_compute. reflexivity. Qed.

  (** Little-endian evaluation of 64-bit limbs. *)
  Fixpoint limbs_eval (l : list Z) : Z :=
    match l with
    | [] => 0
    | x :: l' => x + 2 ^ 64 * limbs_eval l'
    end.

  Definition mont_to_F (l : list Z) : Fp := F.of_Z p (limbs_eval l * R_inv).

  (** ** The limbs stored by the loaders of BLS12_Pairing.v *)

  Definition limbs_zero : list Z := [0; 0; 0; 0; 0; 0].

  Definition limbs_gamma1_p2 : list Z :=
    [0x30f1361b798a64e8; 0xf3b8ddab7ece5a2a; 0x16a8ca3ac61577f7;
     0xc26a2ff874fd029b; 0x3636b76660701c6e; 0x051ba4ab241b6160].
  Definition limbs_gamma2_p2 : list Z :=
    [0xcd03c9e48671f071; 0x5dab22461fcda5d2; 0x587042afd3851b95;
     0x8eb60ebe01bacb9e; 0x03f97d6e83d050d2; 0x18f0206554638741].
  Definition limbs_w_frob_p2_c1 : list Z :=
    [0xecfb361b798dba3a; 0xc100ddb891865a2c; 0x0ec08ff1232bda8e;
     0xd5c13cc6f1ca4721; 0x47222a47bf7b5c04; 0x0110f184e51c5f59].
  (** gamma1 = (0, im): its imaginary limbs are those of gamma2_p2. *)
  Definition limbs_gamma1_im : list Z :=
    [0xcd03c9e48671f071; 0x5dab22461fcda5d2; 0x587042afd3851b95;
     0x8eb60ebe01bacb9e; 0x03f97d6e83d050d2; 0x18f0206554638741].
  Definition limbs_gamma2 : list Z :=
    [0x890dc9e4867545c3; 0x2af322533285a5d5; 0x50880866309b7e2c;
     0xa20d1b8c7e881024; 0x14e4f04fe2db9068; 0x14e56d3f1564853a].
  Definition limbs_w_frob_c1_re : list Z :=
    [0x07089552b319d465; 0xc6695f92b50a8313; 0x97e83cccd117228f;
     0xa35baecab2dc29ee; 0x1ce393ea5daace4d; 0x08f2220fb0fb66eb].
  Definition limbs_w_frob_c1_im : list Z :=
    [0xb2f66aad4ce5d646; 0x5842a06bfc497cec; 0xcf4895d42599d394;
     0xc11b9cba40a8e8d0; 0x2e3813cbe5a0de89; 0x110eefda88847faf].

  Definition gamma1_p2_loaded : Fp2 :=
    (mont_to_F limbs_gamma1_p2, mont_to_F limbs_zero).
  Definition gamma2_p2_loaded : Fp2 :=
    (mont_to_F limbs_gamma2_p2, mont_to_F limbs_zero).
  Definition w_frob_p2_c1_loaded : Fp2 :=
    (mont_to_F limbs_w_frob_p2_c1, mont_to_F limbs_zero).
  Definition gamma1_loaded : Fp2 :=
    (mont_to_F limbs_zero, mont_to_F limbs_gamma1_im).
  Definition gamma2_loaded : Fp2 :=
    (mont_to_F limbs_gamma2, mont_to_F limbs_zero).
  Definition w_frob_c1_loaded : Fp2 :=
    (mont_to_F limbs_w_frob_c1_re, mont_to_F limbs_w_frob_c1_im).

  (** ** Equalities, by computation *)

  Lemma fp2_eq_by_to_Z (x y : Fp2) :
    F.to_Z (fst x) = F.to_Z (fst y) ->
    F.to_Z (snd x) = F.to_Z (snd y) -> x = y.
  Proof.
    destruct x as [x0 x1], y as [y0 y1]; cbn [fst snd]; intros H0 H1.
    apply F.eq_to_Z_iff in H0, H1. subst. reflexivity.
  Qed.

  Local Ltac fp2_vm :=
    apply fp2_eq_by_to_Z; vm_compute; reflexivity.

  Lemma gamma1_p2_loaded_eq : gamma1_p2_loaded = frob_gamma1_p2.
  Proof. fp2_vm. Qed.

  Lemma gamma2_p2_loaded_eq : gamma2_p2_loaded = frob_gamma2_p2.
  Proof. fp2_vm. Qed.

  Lemma w_frob_p2_c1_loaded_eq : w_frob_p2_c1_loaded = frob_coeff_fp12_p2_c1.
  Proof. fp2_vm. Qed.

  Lemma gamma1_loaded_eq : gamma1_loaded = frob_gamma1.
  Proof. fp2_vm. Qed.

  Lemma gamma2_loaded_eq : gamma2_loaded = frob_gamma2.
  Proof. fp2_vm. Qed.

  Lemma w_frob_c1_loaded_eq : w_frob_c1_loaded = frob_coeff_fp12_c1.
  Proof. fp2_vm. Qed.

  (** Sanity: the exponents are exact quotients. *)
  Lemma frob_exponents_exact :
    (bls_p ^ 2 - 1) mod 6 = 0 /\ (bls_p - 1) mod 6 = 0.
  Proof. vm_compute. split; reflexivity. Qed.

End BLS12_381_Frob.
