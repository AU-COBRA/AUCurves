Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

(* BN254 (alt_bn128 / Ethereum): y^2 = x^3 + 3
   Seed u = 0x44E992B44A6909F1 (positive)
   Prime p = 36*u^4 + 36*u^3 + 24*u^2 + 6*u + 1
   p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
   254 bits, 4 x 64-bit words *)

Definition bn254_u : Z := 0x44E992B44A6909F1%Z.

Definition bn254_p_of_u (u : Z) : Z :=
  (36 * u^4 + 36 * u^3 + 24 * u^2 + 6 * u + 1)%Z.

Definition bn254_modulus : Z :=
  Eval vm_compute in (bn254_p_of_u bn254_u).

Definition bn254_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (bn254_p_of_u bn254_u)).

Lemma bn254_modulus_pos : bn254_modulus = Z.pos bn254_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Definition bn254_r : Z :=
  Eval vm_compute in (36 * bn254_u^4 + 36 * bn254_u^3 + 18 * bn254_u^2 + 6 * bn254_u + 1)%Z.

(* p-1 = 2 * 13427688667394608761327070753331941386769 * 815041345313164696077088872238778739 *)
Lemma prime_bn254 : prime bn254_modulus.
Proof.
  rewrite bn254_modulus_pos.
  apply (Pocklington_refl
    (Pock_certif bn254_prime_pos 3
      ((13427688667394608761327070753331941386769,1)::(2,1)::nil)
      815041345313164696077088872238778739)
    ((Pock_certif 13427688667394608761327070753331941386769 17 ((2480874801745591,1)::(173171039,1)::(4562087,1)::(1853641,1)::(11,1)::(7,1)::(3,1)::(2,4)::nil) 1) ::
     (Pock_certif 2480874801745591 6 ((35385462869,1)::(41,1)::(19,1)::(5,1)::(3,2)::(2,1)::nil) 1) ::
     (Pock_certif 35385462869 2 ((1263766531,1)::(7,1)::(2,2)::nil) 1) ::
     (Pock_certif 1263766531 10 ((3557,1)::(911,1)::(13,1)::(5,1)::(3,1)::(2,1)::nil) 1) ::
     (Proof_certif 3557 prime3557) ::
     (Proof_certif 911 prime911) ::
     (Pock_certif 173171039 13 ((13327,1)::(89,1)::(73,1)::(2,1)::nil) 1) ::
     (Proof_certif 13327 prime13327) ::
     (Pock_certif 4562087 5 ((1231,1)::(109,1)::(17,1)::(2,1)::nil) 1) ::
     (Proof_certif 1231 prime1231) ::
     (Pock_certif 1853641 17 ((271,1)::(19,1)::(5,1)::(3,2)::(2,3)::nil) 1) ::
     (Proof_certif 271 prime271) ::
     (Proof_certif 109 prime109) ::
     (Proof_certif 89 prime89) ::
     (Proof_certif 73 prime73) ::
     (Proof_certif 41 prime41) ::
     (Proof_certif 19 prime19) ::
     (Proof_certif 17 prime17) ::
     (Proof_certif 13 prime13) ::
     (Proof_certif 11 prime11) ::
     (Proof_certif 7 prime7) ::
     (Proof_certif 5 prime5) ::
     (Proof_certif 3 prime_3) ::
     (Proof_certif 2 prime_2) ::
      nil)).
  vm_compute. reflexivity.
Qed.
