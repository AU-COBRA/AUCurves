(** * P-224 (secp224r1) prime modulus and primality.

    Prime cert file for the Track Q divstep-inversion chain.  Primality
    is discharged by the Coqprime Pocklington certificate in
    [p224_prime_certif.v]; this file only restates it at the [Z] modulus
    used downstream.

    Sibling files in the chain:
      - [P224_FpInv.v]                       (Gallina divstep + iter_invariant)
      - [divsteps_p224.v]                    (cert axiom)
      - [P224_FpInv_closed.v]                (bridge composition)
      - [P224_InvertBoundInstantiation.v]    (parametric Phase 0e template)
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.
Require Import Bedrock.Field.Synthesis.Examples.p224_prime_certif.

Local Open Scope Z_scope.

(** The P-224 base field prime: [2^224 - 2^96 + 1]. *)
Definition p224_modulus : Z :=
  Eval vm_compute in (2^224 - 2^96 + 1)%Z.

Definition p224_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (2^224 - 2^96 + 1))%Z.

Lemma p224_modulus_pos : p224_modulus = Z.pos p224_prime_pos.
Proof. vm_compute. reflexivity. Qed.

(** Primality, from the Pocklington certificate in [p224_prime_certif.v].
    Here [p - 1 = 2^96 * (2^128 - 1)] factors completely, so the
    certificate is an exact-cofactor chain. *)
Lemma prime_p224 : prime p224_modulus.
Proof. rewrite p224_modulus_pos. exact prime_p224_cert. Qed.
