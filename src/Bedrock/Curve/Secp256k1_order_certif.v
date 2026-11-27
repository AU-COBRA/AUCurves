(** * Pocklington certificate for the order n of the secp256k1 group.

    n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
      = 115792089237316195423570985008687907852837564279074904382605163141518161494337,

    the number of points of y^2 = x^3 + 7 over F_p (p = 2^256 - 2^32 - 977) and the order of its
    standard generator; the cofactor is 1.  [Secp256k1_prime_certif.v] certifies p; this file
    certifies n.  The certificate is rooted at

      n - 1 = 2^6 * 3 * 149 * 631 * 107361793816595537 * 174723607534414371449
              * 341948486974166000522343609283189

    (sympy [factorint]); every prime above 3 has a sub-certificate of its own, and the leaves
    are [prime_2] and [prime_3] of [Coqprime.PrimalityTest.PocklingtonCertificat].  Witnesses
    were found by a linear search (AUCurves' [scripts/gen_pock_certif.py]).  The kernel checks
    the certificate once, at [Qed] ([vm_cast_no_check]). *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.
From Stdlib Require Import Lists.List. Import ListNotations.
From Coqprime.PrimalityTest Require Import Pocklington PocklingtonCertificat.

Local Open Scope positive_scope.

Definition secp256k1_order_modulus : Z :=
  115792089237316195423570985008687907852837564279074904382605163141518161494337%Z.

Definition secp256k1_order_pos : positive :=
  Eval vm_compute in (Z.to_pos secp256k1_order_modulus).

Lemma secp256k1_order_modulus_pos : secp256k1_order_modulus = Z.pos secp256k1_order_pos.
Proof. vm_compute. reflexivity. Qed.

(** The hexadecimal value of SEC 2. *)
Lemma secp256k1_order_modulus_hex :
  secp256k1_order_modulus
  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141%Z.
Proof. vm_compute. reflexivity. Qed.

Lemma prime_secp256k1_order : prime secp256k1_order_modulus.
Proof.
  rewrite secp256k1_order_modulus_pos.
  simple refine (Pocklington_refl
    (Pock_certif secp256k1_order_pos 7 [(341948486974166000522343609283189, 1); (174723607534414371449, 1); (107361793816595537, 1); (631, 1); (149, 1); (3, 1); (2, 6)] 1)
    [
    Pock_certif 341948486974166000522343609283189 2 [(29047611873442575647497758179, 1); (109, 1); (3, 3); (2, 2)] 1;
    Pock_certif 29047611873442575647497758179 2 [(297159362677, 1); (545358713, 1); (305873, 1); (293, 1); (2, 1)] 1;
    Pock_certif 174723607534414371449 3 [(44706919, 1); (120233, 1); (4051, 1); (59, 1); (17, 1); (2, 3)] 1;
    Pock_certif 107361793816595537 3 [(4681609, 1); (85831, 1); (16699, 1); (2, 4)] 1;
    Pock_certif 297159362677 2 [(1627771, 1); (461, 1); (11, 1); (3, 2); (2, 2)] 1;
    Pock_certif 545358713 5 [(28181, 1); (59, 1); (41, 1); (2, 3)] 1;
    Pock_certif 44706919 6 [(9349, 1); (797, 1); (3, 1); (2, 1)] 1;
    Pock_certif 4681609 23 [(2011, 1); (97, 1); (3, 1); (2, 3)] 1;
    Pock_certif 1627771 3 [(1871, 1); (29, 1); (5, 1); (3, 1); (2, 1)] 1;
    Pock_certif 305873 3 [(2731, 1); (7, 1); (2, 4)] 1;
    Pock_certif 120233 3 [(113, 1); (19, 1); (7, 1); (2, 3)] 1;
    Pock_certif 85831 3 [(2861, 1); (5, 1); (3, 1); (2, 1)] 1;
    Pock_certif 28181 2 [(1409, 1); (5, 1); (2, 2)] 1;
    Pock_certif 16699 3 [(23, 1); (11, 2); (3, 1); (2, 1)] 1;
    Pock_certif 9349 2 [(41, 1); (19, 1); (3, 1); (2, 2)] 1;
    Pock_certif 4051 10 [(5, 2); (3, 4); (2, 1)] 1;
    Pock_certif 2861 2 [(13, 1); (11, 1); (5, 1); (2, 2)] 1;
    Pock_certif 2731 3 [(13, 1); (7, 1); (5, 1); (3, 1); (2, 1)] 1;
    Pock_certif 2011 3 [(67, 1); (5, 1); (3, 1); (2, 1)] 1;
    Pock_certif 1871 14 [(17, 1); (11, 1); (5, 1); (2, 1)] 1;
    Pock_certif 1409 3 [(11, 1); (2, 7)] 1;
    Pock_certif 797 2 [(199, 1); (2, 2)] 1;
    Pock_certif 631 3 [(7, 1); (5, 1); (3, 2); (2, 1)] 1;
    Pock_certif 461 2 [(23, 1); (5, 1); (2, 2)] 1;
    Pock_certif 293 2 [(73, 1); (2, 2)] 1;
    Pock_certif 199 3 [(11, 1); (3, 2); (2, 1)] 1;
    Pock_certif 149 2 [(37, 1); (2, 2)] 1;
    Pock_certif 113 3 [(7, 1); (2, 4)] 1;
    Pock_certif 109 6 [(3, 3); (2, 2)] 1;
    Pock_certif 97 5 [(3, 1); (2, 5)] 1;
    Pock_certif 73 5 [(3, 2); (2, 3)] 1;
    Pock_certif 67 2 [(11, 1); (3, 1); (2, 1)] 1;
    Pock_certif 59 2 [(29, 1); (2, 1)] 1;
    Pock_certif 41 6 [(5, 1); (2, 3)] 1;
    Pock_certif 37 2 [(3, 2); (2, 2)] 1;
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
  vm_cast_no_check (@eq_refl bool true).
Qed.
