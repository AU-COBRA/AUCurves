Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Definition secp256k1_modulus : Z :=
  Eval vm_compute in (2^256 - 2^32 - 977)%Z.

Definition secp256k1_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (2^256 - 2^32 - 977))%Z.

Lemma secp256k1_modulus_pos : secp256k1_modulus = Z.pos secp256k1_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Lemma prime_secp256k1 : prime secp256k1_modulus.
Proof.
  rewrite secp256k1_modulus_pos.
  apply (Pocklington_refl
    (Pock_certif secp256k1_prime_pos 3
      ((205115282021455665897114700593932402728804164701536103180137503955397371, 1)::(13441, 1)::(7, 1)::(3, 1)::(2, 1)::nil)
      1)
    [
    Proof_certif 53 prime_53;
    Proof_certif 29 prime_29;
    Proof_certif 7 prime_7;
    Proof_certif 5 prime_5;
    Proof_certif 2 prime_2;
    Pock_certif 107590001 3 ((53, 1)::(29, 1)::(7, 1)::(5, 4)::(2, 4)::nil) 1;
    Proof_certif 19 prime_19;
    Proof_certif 11 prime_11;
    Proof_certif 2 prime_2;
    Pock_certif 419 2 ((19, 1)::(11, 1)::(2, 1)::nil) 1;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 20113 10 ((419, 1)::(3, 1)::(2, 4)::nil) 1;
    Proof_certif 5 prime_5;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 1206781 10 ((20113, 1)::(5, 1)::(3, 1)::(2, 2)::nil) 1;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 7240687 3 ((1206781, 1)::(3, 1)::(2, 1)::nil) 1;
    Proof_certif 17 prime_17;
    Proof_certif 7 prime_7;
    Proof_certif 2 prime_2;
    Pock_certif 239 7 ((17, 1)::(7, 1)::(2, 1)::nil) 1;
    Proof_certif 5 prime_5;
    Proof_certif 2 prime_2;
    Pock_certif 101 2 ((5, 2)::(2, 2)::nil) 1;
    Proof_certif 2 prime_2;
    Pock_certif 96557 2 ((239, 1)::(101, 1)::(2, 2)::nil) 1;
    Proof_certif 17 prime_17;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 103 5 ((17, 1)::(3, 1)::(2, 1)::nil) 1;
    Proof_certif 5 prime_5;
    Proof_certif 2 prime_2;
    Pock_certif 41201 3 ((103, 1)::(5, 2)::(2, 4)::nil) 1;
    Proof_certif 67 prime_67;
    Proof_certif 11 prime_11;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 4423 3 ((67, 1)::(11, 1)::(3, 1)::(2, 1)::nil) 1;
    Proof_certif 83 prime_83;
    Proof_certif 2 prime_2;
    Pock_certif 2657 3 ((83, 1)::(2, 5)::nil) 1;
    Proof_certif 5 prime_5;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 271 6 ((5, 1)::(3, 3)::(2, 1)::nil) 1;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 1627 3 ((271, 1)::(3, 1)::(2, 1)::nil) 1;
    Proof_certif 11 prime_11;
    Proof_certif 7 prime_7;
    Proof_certif 2 prime_2;
    Pock_certif 255515944373312847190720520512484175977 3 ((107590001, 1)::(7240687, 1)::(96557, 1)::(41201, 1)::(4423, 1)::(2657, 1)::(1627, 1)::(11, 1)::(7, 2)::(2, 3)::nil) 1;
    Proof_certif 7 prime_7;
    Proof_certif 2 prime_2;
    Pock_certif 1373 2 ((7, 3)::(2, 2)::nil) 1;
    Proof_certif 97 prime_97;
    Proof_certif 5 prime_5;
    Proof_certif 2 prime_2;
    Pock_certif 971 6 ((97, 1)::(5, 1)::(2, 1)::nil) 1;
    Proof_certif 5 prime_5;
    Proof_certif 2 prime_2;
    Pock_certif 13331831 13 ((1373, 1)::(971, 1)::(5, 1)::(2, 1)::nil) 1;
    Proof_certif 17 prime_17;
    Proof_certif 13 prime_13;
    Proof_certif 2 prime_2;
    Pock_certif 443 2 ((17, 1)::(13, 1)::(2, 1)::nil) 1;
    Proof_certif 7 prime_7;
    Proof_certif 2 prime_2;
    Pock_certif 24809 6 ((443, 1)::(7, 1)::(2, 3)::nil) 1;
    Proof_certif 13 prime_13;
    Proof_certif 5 prime_5;
    Proof_certif 2 prime_2;
    Pock_certif 131 2 ((13, 1)::(5, 1)::(2, 1)::nil) 1;
    Proof_certif 5 prime_5;
    Proof_certif 2 prime_2;
    Pock_certif 2621 2 ((131, 1)::(5, 1)::(2, 2)::nil) 1;
    Proof_certif 5 prime_5;
    Proof_certif 2 prime_2;
    Pock_certif 173378833005251801 6 ((13331831, 1)::(24809, 1)::(2621, 1)::(5, 2)::(2, 3)::nil) 1;
    Proof_certif 17 prime_17;
    Proof_certif 13 prime_13;
    Proof_certif 2 prime_2;
    Pock_certif 443 2 ((17, 1)::(13, 1)::(2, 1)::nil) 1;
    Proof_certif 2 prime_2;
    Pock_certif 887 5 ((443, 1)::(2, 1)::nil) 1;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 5323 5 ((887, 1)::(3, 1)::(2, 1)::nil) 1;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 22149492674086928081353 5 ((173378833005251801, 1)::(5323, 1)::(3, 1)::(2, 3)::nil) 1;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 132896956044521568488119 6 ((22149492674086928081353, 1)::(3, 1)::(2, 1)::nil) 1;
    Proof_certif 13 prime_13;
    Proof_certif 11 prime_11;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 7723 3 ((13, 1)::(11, 1)::(3, 3)::(2, 1)::nil) 1;
    Proof_certif 31 prime_31;
    Proof_certif 29 prime_29;
    Proof_certif 5 prime_5;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 205115282021455665897114700593932402728804164701536103180137503955397371 10 ((255515944373312847190720520512484175977, 1)::(132896956044521568488119, 1)::(7723, 1)::(31, 1)::(29, 2)::(5, 1)::(3, 1)::(2, 1)::nil) 1;
    Proof_certif 7 prime_7;
    Proof_certif 5 prime_5;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2;
    Pock_certif 13441 11 ((7, 1)::(5, 1)::(3, 1)::(2, 7)::nil) 1;
    Proof_certif 7 prime_7;
    Proof_certif 3 prime_3;
    Proof_certif 2 prime_2
    ] _).
  native_cast_no_check (refl_equal true).
Qed.
