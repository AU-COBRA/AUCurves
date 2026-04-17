Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

(* BN446: y^2 = x^3 + 257
   Seed u = 2^110 + 2^36 + 1 = 0x4000000000000000001000000001
   Prime p = 36*u^4 + 36*u^3 + 24*u^2 + 6*u + 1
   p = 102211695604069718983520304652693874995639508460729604902280098199792736381528662976886082950231100101353700265360419596271313339023463
   446 bits, 7 x 64-bit words *)

Definition bn446_u : Z := 0x4000000000000000001000000001%Z.

Definition bn446_p_of_u (u : Z) : Z :=
  (36 * u^4 + 36 * u^3 + 24 * u^2 + 6 * u + 1)%Z.

Definition bn446_modulus : Z :=
  Eval vm_compute in (bn446_p_of_u bn446_u).

Definition bn446_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (bn446_p_of_u bn446_u)).

Lemma bn446_modulus_pos : bn446_modulus = Z.pos bn446_prime_pos.
Proof. vm_compute. reflexivity. Qed.

Definition bn446_r : Z :=
  Eval vm_compute in (36 * bn446_u^4 + 36 * bn446_u^3 + 18 * bn446_u^2 + 6 * bn446_u + 1)%Z.

(* p - 1 = bp * cofactor
   where bp = 1162613844024428196379488035662156878165629976298431286074374686829934969341
   and cofactor = 87915429641075307549374970018188802306988165577943346287582
   bp is 250 bits > cofactor (196 bits), satisfying Pocklington criterion.

   bp - 1 = 2^2 * 5 * 7^2 * 13 * 83 * 109 * 211 * 202817
          * 17637749861772962892695953 * 13363846630225487569485311532818723 *)
Lemma prime_bn446 : prime bn446_modulus.
Proof.
  rewrite bn446_modulus_pos.
  apply (Pocklington_refl
    (Pock_certif bn446_prime_pos 3
      ((1162613844024428196379488035662156878165629976298431286074374686829934969341,1)::(2,1)::nil)
      43957714820537653774687485009094401153494082788971673143791)
    ((Pock_certif 1162613844024428196379488035662156878165629976298431286074374686829934969341 2 ((13363846630225487569485311532818723,1)::(17637749861772962892695953,1)::(202817,1)::(211,1)::(109,1)::(83,1)::(13,1)::(7,2)::(5,1)::(2,2)::nil) 1) ::
     (Pock_certif 13363846630225487569485311532818723 2 ((1383690386811419,1)::(916531658059,1)::(112103,1)::(47,1)::(2,1)::nil) 1) ::
     (Pock_certif 1383690386811419 2 ((171627623,1)::(82267,1)::(7,2)::(2,1)::nil) 1) ::
     (Pock_certif 171627623 5 ((85813811,1)::(2,1)::nil) 1) ::
     (Pock_certif 85813811 2 ((199567,1)::(43,1)::(5,1)::(2,1)::nil) 1) ::
     (Pock_certif 199567 3 ((11087,1)::(3,2)::(2,1)::nil) 1) ::
     (Pock_certif 82267 2 ((13711,1)::(3,1)::(2,1)::nil) 1) ::
     (Pock_certif 916531658059 3 ((843951803,1)::(181,1)::(3,1)::(2,1)::nil) 1) ::
     (Pock_certif 843951803 2 ((3499,1)::(1453,1)::(83,1)::(2,1)::nil) 1) ::
     (Pock_certif 112103 5 ((2437,1)::(23,1)::(2,1)::nil) 1) ::
     (Pock_certif 17637749861772962892695953 5 ((7049474689,1)::(3047567,1)::(6689,1)::(2557,1)::(3,1)::(2,4)::nil) 1) ::
     (Pock_certif 7049474689 7 ((24251,1)::(757,1)::(3,1)::(2,7)::nil) 1) ::
     (Pock_certif 24251 6 ((97,1)::(5,3)::(2,1)::nil) 1) ::
     (Pock_certif 757 2 ((7,1)::(3,3)::(2,2)::nil) 1) ::
     (Pock_certif 3047567 5 ((1523783,1)::(2,1)::nil) 1) ::
     (Pock_certif 1523783 5 ((569,1)::(103,1)::(13,1)::(2,1)::nil) 1) ::
     (Pock_certif 6689 3 ((19,1)::(11,1)::(2,5)::nil) 1) ::
     (Pock_certif 2557 2 ((71,1)::(3,2)::(2,2)::nil) 1) ::
     (Pock_certif 202817 3 ((3169,1)::(2,6)::nil) 1) ::
     (Proof_certif 13711 prime13711) ::
     (Proof_certif 11087 prime11087) ::
     (Proof_certif 3499 prime3499) ::
     (Proof_certif 3169 prime3169) ::
     (Proof_certif 2437 prime2437) ::
     (Proof_certif 1453 prime1453) ::
     (Proof_certif 569 prime569) ::
     (Proof_certif 211 prime211) ::
     (Proof_certif 181 prime181) ::
     (Proof_certif 109 prime109) ::
     (Proof_certif 103 prime103) ::
     (Proof_certif 97 prime97) ::
     (Proof_certif 83 prime83) ::
     (Proof_certif 71 prime71) ::
     (Proof_certif 47 prime47) ::
     (Proof_certif 43 prime43) ::
     (Proof_certif 23 prime23) ::
     (Proof_certif 19 prime19) ::
     (Proof_certif 13 prime13) ::
     (Proof_certif 11 prime11) ::
     (Proof_certif 7 prime7) ::
     (Proof_certif 5 prime5) ::
     (Proof_certif 3 prime_3) ::
     (Proof_certif 2 prime_2) ::
      nil)).
  vm_compute. reflexivity.
Qed.
