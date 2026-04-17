Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

(* BN256: y^2 = x^3 + 3
   Seed u = 0x5A76AE9AEC588301 (positive)
   Prime p = 36*u^4 + 36*u^3 + 24*u^2 + 6*u + 1
   p = 65000549695646603732796438742359905742825358107623003571877145026864184071783
   256 bits, 4 x 64-bit words *)

Definition bn256_u : Z := 0x5A76AE9AEC588301%Z.

Definition bn256_p_of_u (u : Z) : Z :=
  (36 * u^4 + 36 * u^3 + 24 * u^2 + 6 * u + 1)%Z.

Definition bn256_modulus : Z :=
  Eval vm_compute in (bn256_p_of_u bn256_u).

Definition bn256_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (bn256_p_of_u bn256_u)).

Lemma bn256_modulus_pos : bn256_modulus = Z.pos bn256_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Definition bn256_r : Z :=
  Eval vm_compute in (36 * bn256_u^4 + 36 * bn256_u^3 + 18 * bn256_u^2 + 6 * bn256_u + 1)%Z.

Lemma prime_bn256 : prime bn256_modulus.
Proof.
  rewrite bn256_modulus_pos.
  apply (Pocklington_refl
    (Pock_certif bn256_prime_pos 3
      ((1374947842730272154058024133,1)::(5332323573263718838033,1)::(2,1)::nil)
      4432863053093560919940756519)
    ((Pock_certif 5332323573263718838033 7 ((1145258499412310747,1)::(97,1)::(3,1)::(2,4)::nil) 1) ::
     (Pock_certif 1145258499412310747 2 ((572629249706155373,1)::(2,1)::nil) 1) ::
     (Pock_certif 572629249706155373 2 ((13954314497177,1)::(10259,1)::(2,2)::nil) 1) ::
     (Pock_certif 13954314497177 3 ((5745221,1)::(4159,1)::(73,1)::(2,3)::nil) 1) ::
     (Pock_certif 5745221 3 ((1163,1)::(19,1)::(13,1)::(5,1)::(2,2)::nil) 1) ::
     (Pock_certif 1163 5 ((83,1)::(7,1)::(2,1)::nil) 1) ::
     (Pock_certif 10259 2 ((223,1)::(23,1)::(2,1)::nil) 1) ::
     (Pock_certif 223 3 ((37,1)::(3,1)::(2,1)::nil) 1) ::
     (Pock_certif 1374947842730272154058024133 2 ((81767558454161,1)::(4159,1)::(3593,1)::(1187,1)::(79,1)::(3,1)::(2,2)::nil) 1) ::
     (Pock_certif 81767558454161 3 ((6743249,1)::(151573,1)::(5,1)::(2,4)::nil) 1) ::
     (Pock_certif 6743249 3 ((421453,1)::(2,4)::nil) 1) ::
     (Pock_certif 421453 6 ((509,1)::(23,1)::(3,2)::(2,2)::nil) 1) ::
     (Pock_certif 509 2 ((127,1)::(2,2)::nil) 1) ::
     (Pock_certif 151573 5 ((743,1)::(17,1)::(3,1)::(2,2)::nil) 1) ::
     (Pock_certif 743 5 ((53,1)::(7,1)::(2,1)::nil) 1) ::
     (Proof_certif 4159 prime4159) ::
     (Proof_certif 3593 prime3593) ::
     (Proof_certif 1187 prime1187) ::
     (Proof_certif 127 prime127) ::
     (Proof_certif 97 prime97) ::
     (Proof_certif 83 prime83) ::
     (Proof_certif 79 prime79) ::
     (Proof_certif 73 prime73) ::
     (Proof_certif 53 prime53) ::
     (Proof_certif 37 prime37) ::
     (Proof_certif 23 prime23) ::
     (Proof_certif 19 prime19) ::
     (Proof_certif 17 prime17) ::
     (Proof_certif 13 prime13) ::
     (Proof_certif 7 prime7) ::
     (Proof_certif 5 prime5) ::
     (Proof_certif 3 prime_3) ::
     (Proof_certif 2 prime_2) ::
      nil)).
  vm_compute. reflexivity.
Qed.
