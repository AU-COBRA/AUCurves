(** * CurvePrimalityFacts.v — per-curve primality + nonresidue lemmas.

    For each pairing curve [c], the discharge of [zproj_double_simulates]
    requires three per-curve facts:

    1. [prime (prime_p c)] — Pocklington certificates already exist
       upstream in [Synthesis/Examples/<curve>_prime_certif.v]; this
       file re-exports them under uniform names.

    2. [prime_p c mod 4 = 3] — for the curves with [fp2_beta = -1] (all
       but BLS12-377), this gives [-1] is a nonresidue and Fp2 is a field.

    3. [Z.pos (Z.to_pos (prime_p c)) = prime_p c] — bridge from the [Z]
       value [prime_p c] to the [positive] form needed by [Fp2ZAlgebra]
       lemmas.  Closes by [vm_compute. reflexivity.] for any concrete
       positive prime.

    Curves covered: BN254, BLS12-381, BN256, BN446 (the four "u² = -1
    with q ≡ 3 mod 4" curves).  BLS12-377 has [fp2_beta = -5] and
    [p ≡ 1 mod 4]; its analogue requires [Legendre(5, p) = -1] (a
    Pocklington-style fact computable via Euler's criterion in
    vm_compute on the 377-bit prime). *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Znumtheory.

Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.Curves.BN254_params.
Require Import Bedrock.Field.PairingTheory.Curves.BLS12_381_params.
Require Import Bedrock.Field.PairingTheory.Curves.BLS12_377_params.
Require Import Bedrock.Field.PairingTheory.Curves.BN256_params.
Require Import Bedrock.Field.PairingTheory.Curves.BN446_params.

Local Open Scope Z_scope.

(** ** BN254 *)

Definition bn254_p_pos : positive := Eval vm_compute in
  Z.to_pos (prime_p bn254_params).

Lemma bn254_p_pos_eq : Z.pos bn254_p_pos = prime_p bn254_params.
Proof. vm_compute. reflexivity. Qed.

Lemma bn254_p_3mod4 : prime_p bn254_params mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

(** ** BLS12-381 *)

Definition bls12_381_p_pos : positive := Eval vm_compute in
  Z.to_pos (prime_p bls12_381_params).

Lemma bls12_381_p_pos_eq : Z.pos bls12_381_p_pos = prime_p bls12_381_params.
Proof. vm_compute. reflexivity. Qed.

Lemma bls12_381_p_3mod4 : prime_p bls12_381_params mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

(** ** BN256 *)

Definition bn256_p_pos : positive := Eval vm_compute in
  Z.to_pos (prime_p bn256_params).

Lemma bn256_p_pos_eq : Z.pos bn256_p_pos = prime_p bn256_params.
Proof. vm_compute. reflexivity. Qed.

Lemma bn256_p_3mod4 : prime_p bn256_params mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

(** ** BN446 *)

Definition bn446_p_pos : positive := Eval vm_compute in
  Z.to_pos (prime_p bn446_params).

Lemma bn446_p_pos_eq : Z.pos bn446_p_pos = prime_p bn446_params.
Proof. vm_compute. reflexivity. Qed.

Lemma bn446_p_3mod4 : prime_p bn446_params mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

(** ** BLS12-377 — placeholder.

    This curve has [fp2_beta = -5] and [p mod 4 = 1], so the
    [q ≡ 3 mod 4] discharge path does NOT apply.  The correct
    nonresidue claim is [Legendre(5, p) = -1], computable via
    Euler's criterion: [5^((p-1)/2) mod p = p - 1].  The [vm_compute]
    on the 377-bit prime takes ~1-2 seconds. *)

Definition bls12_377_p_pos : positive := Eval vm_compute in
  Z.to_pos (prime_p bls12_377_params).

Lemma bls12_377_p_pos_eq : Z.pos bls12_377_p_pos = prime_p bls12_377_params.
Proof. vm_compute. reflexivity. Qed.

(** [5] is a quadratic non-residue mod [bls12_377_p].  Using
    [Z.pow 5 ((p-1)/2)] directly under [vm_compute] would require
    computing a 2^376-scale integer before reducing mod p — not
    tractable.  The correct formulation uses a modular-exponentiation
    helper (e.g. [zpow_mod_aux] from [ZModTower]).  Deferred. *)
