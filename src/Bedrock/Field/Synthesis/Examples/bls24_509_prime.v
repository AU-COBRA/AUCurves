(** * BLS24-509 prime certificate.
    p(z) = (z-1)^2*(z^8-z^4+1)/3 + z, z = -0x800000ffff801.
    509 bits, p = 3 (mod 4). *)

From Coq Require Import ZArith Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope Z_scope.

Definition bls24_z : Z := -(0x800000ffff801).

Definition bls24_509_modulus : Z :=
  Eval vm_compute in
    (let z := bls24_z in ((z - 1)^2 * (z^8 - z^4 + 1)) / 3 + z).

Definition bls24_509_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos bls24_509_modulus).

Lemma bls24_509_modulus_pos : bls24_509_modulus = Z.pos bls24_509_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Definition bls24_509_order : Z :=
  Eval vm_compute in (let z := bls24_z in z^8 - z^4 + 1).

(** Primality via Pocklington certificate.
    p-1 = 2*3^2*5*383*1877*2447*5179*29614111*358514917*25524268123
          *10901370462156571*Q
    where Q is a 318-bit prime. *)

Lemma prime_bls24_509 : prime bls24_509_modulus.
Proof.
  rewrite bls24_509_modulus_pos.
  Local Open Scope positive_scope.
  apply (Pocklington_refl
    (Pock_certif bls24_509_prime_pos 2
      ((461265834788782365077134487816311900415269956104828398779410508380647363051094574221821530494789, 1)
       ::(10901370462156571, 1)::(25524268123, 1)::(358514917, 1)::(29614111, 1)
       ::(5179, 1)::(2447, 1)::(1877, 1)::(383, 1)::(5, 1)::(3, 2)::(2, 1)::nil)
      1)
    (* Full recursive sub-certificates *)
    (* --- Q (318-bit prime) --- *)
    ((Pock_certif 461265834788782365077134487816311900415269956104828398779410508380647363051094574221821530494789 3 ((690746431124054551143223778753258733804449211752259484084207324721, 1)::(1007987605922494441, 1)::(190588933, 1)::(79, 1)::(11, 1)::(2, 2)::nil) 1) ::
     (* --- f2 (219-bit prime) --- *)
     (Pock_certif 690746431124054551143223778753258733804449211752259484084207324721 6 ((144312522091284197826511063073845063, 1)::(47077049273, 1)::(777671431, 1)::(402823, 1)::(4057, 1)::(5, 1)::(2, 4)::nil) 1) ::
     (Pock_certif 144312522091284197826511063073845063 3 ((786607156202833272429773266801, 1)::(30577, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 786607156202833272429773266801 7 ((6286671437, 1)::(1400081, 1)::(448067, 1)::(2341, 1)::(71, 1)::(5, 2)::(3, 1)::(2, 4)::nil) 1) ::
     (Pock_certif 6286671437 2 ((82719361, 1)::(19, 1)::(2, 2)::nil) 1) ::
     (Pock_certif 82719361 11 ((4787, 1)::(5, 1)::(3, 3)::(2, 7)::nil) 1) ::
     (Proof_certif 4787 prime4787) :: (Proof_certif 5 prime5) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Proof_certif 19 prime19) :: (Proof_certif 2 prime2) ::
     (Pock_certif 1400081 3 ((43, 1)::(37, 1)::(11, 1)::(5, 1)::(2, 4)::nil) 1) ::
     (Proof_certif 43 prime43) :: (Proof_certif 37 prime37) :: (Proof_certif 11 prime11) :: (Proof_certif 5 prime5) :: (Proof_certif 2 prime2) ::
     (Pock_certif 448067 2 ((224033, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 224033 3 ((7001, 1)::(2, 5)::nil) 1) ::
     (Proof_certif 7001 prime7001) :: (Proof_certif 2 prime2) :: (Proof_certif 2 prime2) ::
     (Proof_certif 2341 prime2341) :: (Proof_certif 71 prime71) :: (Proof_certif 5 prime5) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Proof_certif 30577 prime30577) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Pock_certif 47077049273 3 ((11399, 1)::(661, 1)::(71, 1)::(11, 1)::(2, 3)::nil) 1) ::
     (Proof_certif 11399 prime11399) :: (Proof_certif 661 prime661) :: (Proof_certif 71 prime71) :: (Proof_certif 11 prime11) :: (Proof_certif 2 prime2) ::
     (Pock_certif 777671431 3 ((69497, 1)::(373, 1)::(5, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 69497 3 ((73, 1)::(17, 1)::(7, 1)::(2, 3)::nil) 1) ::
     (Proof_certif 73 prime73) :: (Proof_certif 17 prime17) :: (Proof_certif 7 prime7) :: (Proof_certif 2 prime2) ::
     (Proof_certif 373 prime373) :: (Proof_certif 5 prime5) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Pock_certif 402823 3 ((139, 1)::(23, 1)::(7, 1)::(3, 2)::(2, 1)::nil) 1) ::
     (Proof_certif 139 prime139) :: (Proof_certif 23 prime23) :: (Proof_certif 7 prime7) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Proof_certif 4057 prime4057) :: (Proof_certif 5 prime5) :: (Proof_certif 2 prime2) ::
     (* --- f1 (60-bit prime) --- *)
     (Pock_certif 1007987605922494441 7 ((238681, 1)::(1063, 1)::(263, 1)::(197, 1)::(71, 1)::(5, 1)::(3, 3)::(2, 3)::nil) 1) ::
     (Pock_certif 238681 29 ((17, 1)::(13, 1)::(5, 1)::(3, 3)::(2, 3)::nil) 1) ::
     (Proof_certif 17 prime17) :: (Proof_certif 13 prime13) :: (Proof_certif 5 prime5) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Proof_certif 1063 prime1063) :: (Proof_certif 263 prime263) :: (Proof_certif 197 prime197) :: (Proof_certif 71 prime71) :: (Proof_certif 5 prime5) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (* --- 190588933 --- *)
     (Pock_certif 190588933 2 ((5294137, 1)::(3, 2)::(2, 2)::nil) 1) ::
     (Pock_certif 5294137 5 ((220589, 1)::(3, 1)::(2, 3)::nil) 1) ::
     (Pock_certif 220589 2 ((55147, 1)::(2, 2)::nil) 1) ::
     (Pock_certif 55147 5 ((101, 1)::(13, 1)::(7, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Proof_certif 101 prime101) :: (Proof_certif 13 prime13) :: (Proof_certif 7 prime7) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Proof_certif 2 prime2) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (Proof_certif 79 prime79) :: (Proof_certif 11 prime11) :: (Proof_certif 2 prime2) ::
     (* --- 10901370462156571 --- *)
     (Pock_certif 10901370462156571 3 ((1333701641, 1)::(47, 1)::(31, 1)::(17, 1)::(11, 1)::(5, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 1333701641 3 ((9551, 1)::(3491, 1)::(5, 1)::(2, 3)::nil) 1) ::
     (Proof_certif 9551 prime9551) :: (Proof_certif 3491 prime3491) :: (Proof_certif 5 prime5) :: (Proof_certif 2 prime2) ::
     (Proof_certif 47 prime47) :: (Proof_certif 31 prime31) :: (Proof_certif 17 prime17) :: (Proof_certif 11 prime11) :: (Proof_certif 5 prime5) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (* --- 25524268123 --- *)
     (Pock_certif 25524268123 2 ((4254044687, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 4254044687 5 ((6311639, 1)::(337, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 6311639 11 ((3155819, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 3155819 2 ((1577909, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 1577909 2 ((937, 1)::(421, 1)::(2, 2)::nil) 1) ::
     (Proof_certif 937 prime937) :: (Proof_certif 421 prime421) :: (Proof_certif 2 prime2) :: (Proof_certif 2 prime2) ::
     (Proof_certif 337 prime337) :: (Proof_certif 2 prime2) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (* --- 358514917 --- *)
     (Pock_certif 358514917 5 ((3643, 1)::(139, 1)::(59, 1)::(3, 1)::(2, 2)::nil) 1) ::
     (Proof_certif 3643 prime3643) :: (Proof_certif 139 prime139) :: (Proof_certif 59 prime59) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (* --- 29614111 --- *)
     (Pock_certif 29614111 3 ((257, 1)::(167, 1)::(23, 1)::(5, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Proof_certif 257 prime257) :: (Proof_certif 167 prime167) :: (Proof_certif 23 prime23) :: (Proof_certif 5 prime5) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
     (* --- Small primes --- *)
     (Proof_certif 5179 prime5179) :: (Proof_certif 2447 prime2447) :: (Proof_certif 1877 prime1877) :: (Proof_certif 383 prime383) ::
     (Proof_certif 5 prime5) :: (Proof_certif 3 prime3) :: (Proof_certif 2 prime2) ::
      nil)).
  native_cast_no_check (refl_equal true).
Qed.

Local Close Scope positive_scope.

Lemma bls24_509_p_mod_4 : bls24_509_modulus mod 4 = 3.
Proof. vm_compute. reflexivity. Qed.

Lemma bls24_509_p_gt_2 : 2 < Z.pos bls24_509_prime_pos.
Proof. vm_compute. reflexivity. Qed.
