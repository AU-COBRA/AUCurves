(** * Pocklington primality certificate for the NIST P-224 prime.

    [p = 2^224 - 2^96 + 1], so

      p - 1 = 2^96 * (2^128 - 1)
            = 2^96 * 3 * 5 * 17 * 257 * 641 * 65537 * 274177 * 6700417
              * 67280421310721,

    a complete factorisation.  Every entry below therefore has cofactor 1
    and needs no [r^2 - 8s] non-square check (the fourth argument of each
    [Pock_certif] is the placeholder 1).

    Consumed by [p224_prime.v], which restates the result as
    [prime p224_modulus]. *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Definition p224_cert_pos : positive :=
  Eval vm_compute in (Z.to_pos ((2^224 - 2^96 + 1)%Z)).

Lemma prime_p224_cert : prime (Z.pos p224_cert_pos).
Proof.
  apply (Pocklington_refl
    (Pock_certif p224_cert_pos 22
      ((67280421310721, 1)::(6700417, 1)::(274177, 1)::(65537, 1)::(641, 1)
        ::(257, 1)::(17, 1)::(5, 1)::(3, 1)::(2, 96)::nil)
      1)
    ((Pock_certif 67280421310721 3
        ((2998279, 1)::(373, 1)::(47, 1)::(5, 1)::(2, 8)::nil) 1) ::
     (Pock_certif 6700417 5
        ((17449, 1)::(3, 1)::(2, 7)::nil) 1) ::
     (Pock_certif 2998279 3
        ((166571, 1)::(3, 2)::(2, 1)::nil) 1) ::
     (Pock_certif 274177 5
        ((17, 1)::(7, 1)::(3, 2)::(2, 8)::nil) 1) ::
     (Pock_certif 166571 2
        ((16657, 1)::(5, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 65537 3
        ((2, 16)::nil) 1) ::
     (Proof_certif 17449 prime17449) ::
     (Proof_certif 16657 prime16657) ::
     (Proof_certif 641 prime641) ::
     (Proof_certif 373 prime373) ::
     (Proof_certif 257 prime257) ::
     (Proof_certif 47 prime47) ::
     (Proof_certif 17 prime17) ::
     (Proof_certif 7 prime7) ::
     (Proof_certif 5 prime5) ::
     (Proof_certif 3 prime3) ::
     (Proof_certif 2 prime2) ::
      nil)).
  vm_cast_no_check (refl_equal true).
Time Qed.
