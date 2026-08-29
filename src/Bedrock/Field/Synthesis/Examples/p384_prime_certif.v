(** * Pocklington primality certificate for the NIST P-384 prime.

    [p = 2^384 - 2^128 - 2^96 + 2^32 - 1] with

      p - 1 = 2 * 19 * 67 * 807145746439 * q,

    where [q] is the 333-bit prime
    [19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097].
    The top-level entry therefore has a fully factored [p - 1] (cofactor 1).

    For [q] itself only a partial factorisation of [q - 1] is used,

      q - 1 = 2^4 * 11^3 * 8389 * 38557 * 312289 * 1357291859799823621 * R,

    with [R] a 212-bit composite left unfactored.  The factored part is
    2^121.1, above the [(q/2)^(1/3)] threshold of Coqprime's extended
    Pocklington test, so the certificate closes with the [r^2 - 8s]
    non-square check; the fourth argument 4604796465254429252001066033541083122
    is [floor (sqrt (r^2 - 8s))].

    Consumed by [p384_prime.v], which restates the result as
    [prime p384_modulus]. *)

From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.
From Coqprime Require Import PocklingtonRefl.

Local Open Scope positive_scope.

Definition p384_cert_pos : positive :=
  Eval vm_compute in (Z.to_pos ((2^384 - 2^128 - 2^96 + 2^32 - 1)%Z)).

Lemma prime_p384_cert : prime (Z.pos p384_cert_pos).
Proof.
  apply (Pocklington_refl
    (Pock_certif p384_cert_pos 19
      ((19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097, 1)
        ::(807145746439, 1)::(67, 1)::(19, 1)::(2, 1)::nil)
      1)
    ((Pock_certif 19173790298027098165721053155794528970226934547887232785722672956982046098136719667167519737147526097 3
        ((1357291859799823621, 1)::(312289, 1)::(38557, 1)::(8389, 1)::(11, 3)::(2, 4)::nil)
        4604796465254429252001066033541083122) ::
     (Pock_certif 1357291859799823621 2
        ((53448597593, 1)::(6317, 1)::(67, 1)::(5, 1)::(3, 1)::(2, 2)::nil) 1) ::
     (Pock_certif 807145746439 3
        ((2862218959, 1)::(47, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 53448597593 3
        ((513928823, 1)::(13, 1)::(2, 3)::nil) 1) ::
     (Pock_certif 2862218959 3
        ((2213, 1)::(1373, 1)::(157, 1)::(3, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 513928823 5
        ((661, 1)::(599, 1)::(59, 1)::(11, 1)::(2, 1)::nil) 1) ::
     (Pock_certif 312289 14
        ((3253, 1)::(3, 1)::(2, 5)::nil) 1) ::
     (Proof_certif 38557 prime38557) ::
     (Proof_certif 8389 prime8389) ::
     (Proof_certif 6317 prime6317) ::
     (Proof_certif 3253 prime3253) ::
     (Proof_certif 2213 prime2213) ::
     (Proof_certif 1373 prime1373) ::
     (Proof_certif 661 prime661) ::
     (Proof_certif 599 prime599) ::
     (Proof_certif 157 prime157) ::
     (Proof_certif 67 prime67) ::
     (Proof_certif 59 prime59) ::
     (Proof_certif 47 prime47) ::
     (Proof_certif 19 prime19) ::
     (Proof_certif 13 prime13) ::
     (Proof_certif 11 prime11) ::
     (Proof_certif 5 prime5) ::
     (Proof_certif 3 prime3) ::
     (Proof_certif 2 prime2) ::
      nil)).
  vm_cast_no_check (refl_equal true).
Time Qed.
