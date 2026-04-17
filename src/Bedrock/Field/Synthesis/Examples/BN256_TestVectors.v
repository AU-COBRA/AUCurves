(** * BN256 test vectors — computational verification. *)

Require Import Coq.ZArith.ZArith.
Require Import Bedrock.Field.Synthesis.Examples.bn256_prime_certif.

Local Open Scope Z_scope.

(* === Prime and order === *)

Lemma bn256_prime_value :
  bn256_modulus = 65000549695646603732796438742359905742825358107623003571877145026864184071783.
Proof. vm_compute. reflexivity. Qed.

Lemma bn256_order_value :
  bn256_r = 65000549695646603732796438742359905742570406053903786389881062969044166799969.
Proof. vm_compute. reflexivity. Qed.

Lemma bn256_p_mod_4 : (bn256_modulus mod 4 = 3)%Z.
Proof. vm_compute. reflexivity. Qed.

(* === Seed and formula === *)

Lemma bn256_u_value : bn256_u = 6518589491078791937.
Proof. vm_compute. reflexivity. Qed.

Lemma bn256_p_from_u : bn256_modulus = bn256_p_of_u bn256_u.
Proof. vm_compute. reflexivity. Qed.

(* === Ate loop count === *)

Lemma bn256_ate_loop : (6 * bn256_u + 2 = 39111536946472751624)%Z.
Proof. vm_compute. reflexivity. Qed.

(* |6u+2| is 66 bits, requires 2-word storage *)
Lemma bn256_ate_loop_bits : (39111536946472751624 < 2^66)%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma bn256_ate_loop_2word : (39111536946472751624 >= 2^64)%Z.
Proof. vm_compute. discriminate. Qed.

(* === G1 generator on curve === *)
(* G1 = (1, 2) for BN256 (b = 3) *)

Lemma bn256_G1_on_curve :
  (2^2 mod bn256_modulus = (1^3 + 3) mod bn256_modulus)%Z.
Proof. vm_compute. reflexivity. Qed.

(* === Montgomery R === *)

Definition bn256_R : Z := Eval vm_compute in (2^256 mod bn256_modulus)%Z.

(* Montgomery inverse: p' = -p^(-1) mod 2^64 *)
Definition bn256_mont_inv : Z := 0x2387f9007f17daa9.

Lemma bn256_mont_inv_correct :
  ((bn256_modulus * bn256_mont_inv) mod 2^64 = (2^64 - 1))%Z.
Proof. vm_compute. reflexivity. Qed.
