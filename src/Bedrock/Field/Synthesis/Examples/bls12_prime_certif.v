Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Lists.List. Import ListNotations.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Local Open Scope positive_scope.

Definition bls12_381_modulus : Z :=
  Eval vm_compute in
    (let u := (-0xd201000000010000)%Z in
     (((u - 1)^2 * (u^4 - u^2 + 1)) / 3 + u)%Z).

Definition bls12_381_prime_pos : positive :=
  Eval vm_compute in
    (Z.to_pos (let u := (-0xd201000000010000)%Z in
     (((u - 1)^2 * (u^4 - u^2 + 1)) / 3 + u)%Z)).

Lemma bls12_381_modulus_pos : bls12_381_modulus = Z.pos bls12_381_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Lemma prime_bls12_381 : prime bls12_381_modulus.
Proof.
  rewrite bls12_381_modulus_pos.
  simple refine (Pocklington_refl (Pock_certif bls12_381_prime_pos 2
    [(15778400344354997994418419698270088123916926905054652752758194827714659, 1); (2584487767265781317813, 1); (52437899, 1); (859267, 1); (10177, 1); (47, 1); (23, 1); (11, 1); (3, 2); (2, 1)] 1)
  [
  Pock_certif 15778400344354997994418419698270088123916926905054652752758194827714659 2 [(1125266252156850182658904441386709967, 1); (92691255082156974996979, 1); (475709467, 1); (53, 1); (3, 1); (2, 1)] 1;
  Pock_certif 1125266252156850182658904441386709967 5 [(3819663927398918131021, 1); (43670061551, 1); (3373, 1); (2, 1)] 1;
  Pock_certif 92691255082156974996979 3 [(64881703735777, 1); (16447, 1); (467, 1); (31, 1); (3, 1); (2, 1)] 1;
  Pock_certif 3819663927398918131021 6 [(13090036741, 1); (755057, 1); (113, 1); (19, 1); (5, 1); (3, 2); (2, 2)] 1;
  Pock_certif 2584487767265781317813 2 [(7259797099061183477, 1); (89, 1); (2, 2)] 1;
  Pock_certif 7259797099061183477 2 [(1928745244171409, 1); (941, 1); (2, 2)] 1;
  Pock_certif 1928745244171409 3 [(9272813673901, 1); (13, 1); (2, 4)] 1;
  Pock_certif 64881703735777 5 [(927093389, 1); (3, 7); (2, 5)] 1;
  Pock_certif 9272813673901 2 [(582767, 1); (7577, 1); (7, 1); (5, 2); (3, 1); (2, 2)] 1;
  Pock_certif 43670061551 7 [(51376543, 1); (17, 1); (5, 2); (2, 1)] 1;
  Pock_certif 13090036741 10 [(421987, 1); (47, 1); (11, 1); (5, 1); (3, 1); (2, 2)] 1;
  Pock_certif 927093389 3 [(43591, 1); (409, 1); (13, 1); (2, 2)] 1;
  Pock_certif 475709467 2 [(1686913, 1); (47, 1); (3, 1); (2, 1)] 1;
  Pock_certif 52437899 2 [(609743, 1); (43, 1); (2, 1)] 1;
  Pock_certif 51376543 3 [(8101, 1); (151, 1); (7, 1); (3, 1); (2, 1)] 1;
  Pock_certif 1686913 10 [(191, 1); (23, 1); (3, 1); (2, 7)] 1;
  Pock_certif 859267 2 [(47737, 1); (3, 2); (2, 1)] 1;
  Pock_certif 755057 3 [(1151, 1); (41, 1); (2, 4)] 1;
  Pock_certif 609743 5 [(449, 1); (97, 1); (7, 1); (2, 1)] 1;
  Pock_certif 582767 5 [(4349, 1); (67, 1); (2, 1)] 1;
  Pock_certif 421987 2 [(1327, 1); (53, 1); (3, 1); (2, 1)] 1;
  Pock_certif 47737 5 [(17, 1); (13, 1); (3, 3); (2, 3)] 1;
  Pock_certif 43591 11 [(1453, 1); (5, 1); (3, 1); (2, 1)] 1;
  Pock_certif 16447 3 [(2741, 1); (3, 1); (2, 1)] 1;
  Pock_certif 10177 7 [(53, 1); (3, 1); (2, 6)] 1;
  Pock_certif 8101 6 [(5, 2); (3, 4); (2, 2)] 1;
  Pock_certif 7577 3 [(947, 1); (2, 3)] 1;
  Pock_certif 4349 2 [(1087, 1); (2, 2)] 1;
  Pock_certif 3373 5 [(281, 1); (3, 1); (2, 2)] 1;
  Pock_certif 2741 2 [(137, 1); (5, 1); (2, 2)] 1;
  Pock_certif 1453 2 [(11, 2); (3, 1); (2, 2)] 1;
  Pock_certif 1327 3 [(17, 1); (13, 1); (3, 1); (2, 1)] 1;
  Pock_certif 1151 17 [(23, 1); (5, 2); (2, 1)] 1;
  Pock_certif 1087 3 [(181, 1); (3, 1); (2, 1)] 1;
  Pock_certif 947 2 [(43, 1); (11, 1); (2, 1)] 1;
  Pock_certif 941 2 [(47, 1); (5, 1); (2, 2)] 1;
  Pock_certif 467 2 [(233, 1); (2, 1)] 1;
  Pock_certif 449 3 [(7, 1); (2, 6)] 1;
  Pock_certif 409 21 [(17, 1); (3, 1); (2, 3)] 1;
  Pock_certif 281 3 [(7, 1); (5, 1); (2, 3)] 1;
  Pock_certif 233 3 [(29, 1); (2, 3)] 1;
  Pock_certif 191 19 [(19, 1); (5, 1); (2, 1)] 1;
  Pock_certif 181 2 [(5, 1); (3, 2); (2, 2)] 1;
  Pock_certif 151 6 [(5, 2); (3, 1); (2, 1)] 1;
  Pock_certif 137 3 [(17, 1); (2, 3)] 1;
  Pock_certif 113 3 [(7, 1); (2, 4)] 1;
  Pock_certif 97 5 [(3, 1); (2, 5)] 1;
  Pock_certif 89 3 [(11, 1); (2, 3)] 1;
  Pock_certif 67 2 [(11, 1); (3, 1); (2, 1)] 1;
  Pock_certif 53 2 [(13, 1); (2, 2)] 1;
  Pock_certif 47 5 [(23, 1); (2, 1)] 1;
  Pock_certif 43 3 [(7, 1); (3, 1); (2, 1)] 1;
  Pock_certif 41 6 [(5, 1); (2, 3)] 1;
  Pock_certif 31 3 [(5, 1); (3, 1); (2, 1)] 1;
  Pock_certif 29 2 [(7, 1); (2, 2)] 1;
  Pock_certif 23 5 [(11, 1); (2, 1)] 1;
  Pock_certif 19 2 [(3, 2); (2, 1)] 1;
  Pock_certif 17 3 [(2, 4)] 1;
  Pock_certif 13 2 [(3, 1); (2, 2)] 1;
  Pock_certif 11 2 [(5, 1); (2, 1)] 1;
  Pock_certif 7 3 [(3, 1); (2, 1)] 1;
  Pock_certif 5 2 [(2, 2)] 1;
  Proof_certif 3 prime_3;
  Proof_certif 2 prime_2
  ] _).
  vm_compute. reflexivity.
Time Qed.
