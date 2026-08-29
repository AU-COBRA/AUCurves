(** * P-384 (secp384r1) prime modulus and primality.

    Prime cert file for the Track Q divstep-inversion chain.  Primality
    is discharged by the Coqprime Pocklington certificate in
    [p384_prime_certif.v]; this file only restates it at the [Z] modulus
    used downstream.

    Sibling files in the chain:
      - [P384_FpInv.v]                       (Gallina divstep + iter_invariant)
      - [divsteps_p384.v]                    (cert axiom)
      - [P384_FpInv_closed.v]                (bridge composition)
      - [P384_InvertBoundInstantiation.v]    (parametric Phase 0e template)
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.
Require Import Bedrock.Field.Synthesis.Examples.p384_prime_certif.

Local Open Scope Z_scope.

(** The P-384 base field prime: [2^384 - 2^128 - 2^96 + 2^32 - 1]. *)
Definition p384_modulus : Z :=
  Eval vm_compute in (2^384 - 2^128 - 2^96 + 2^32 - 1)%Z.

Definition p384_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (2^384 - 2^128 - 2^96 + 2^32 - 1))%Z.

Lemma p384_modulus_pos : p384_modulus = Z.pos p384_prime_pos.
Proof. vm_compute. reflexivity. Qed.

(** Primality, from the Pocklington certificate in [p384_prime_certif.v]. *)
Lemma prime_p384 : prime p384_modulus.
Proof. rewrite p384_modulus_pos. exact prime_p384_cert. Qed.
