Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Definition bls12_377_modulus : Z :=
  Eval vm_compute in
    (let u := (0x8508c00000000001)%Z in
     (((u - 1)^2 * (u^4 - u^2 + 1)) / 3 + u)%Z).

Definition bls12_377_prime_pos : positive :=
  Eval vm_compute in
    (Z.to_pos (let u := (0x8508c00000000001)%Z in
     (((u - 1)^2 * (u^4 - u^2 + 1)) / 3 + u)%Z)).

Lemma bls12_377_modulus_pos : bls12_377_modulus = Z.pos bls12_377_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Lemma prime_bls12_377 : prime bls12_377_modulus.
Proof.
  rewrite bls12_377_modulus_pos.
  apply (Pocklington_refl
    (Pock_certif bls12_377_prime_pos 15
      ((6633514200929891813, 1)::(409, 1)::(13, 1)::(7, 1)::(3, 1)::(2,46)::nil)
      54351534966584318807290098871096834827)
    ((Pock_certif 6633514200929891813 2 ((47521, 1)::(19, 1)::(2,2)::nil) 6048394) ::
     (Proof_certif 47521 prime47521) ::
     (Proof_certif 409 prime409) ::
     (Proof_certif 19 prime19) ::
     (Proof_certif 13 prime13) ::
     (Proof_certif 7 prime7) ::
     (Proof_certif 3 prime3) ::
     (Proof_certif 2 prime2) ::
      nil)).
  native_cast_no_check (refl_equal true).
Qed.
