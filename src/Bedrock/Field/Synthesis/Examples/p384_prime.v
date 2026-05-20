(** * P-384 (secp384r1) prime modulus + axiomatized primality.

    Minimal "prime cert" file for the Track Q divstep-inversion chain.
    Per the Track Q shortcut policy, primality is AXIOMATIZED rather
    than discharged via a Pocklington certificate — producing a fresh
    cert for [2^384 - 2^128 - 2^96 + 2^32 - 1] is not blocking for
    the divstep chain (which only needs [Z.gcd x p = 1] as a hypothesis).

    Sibling files in the chain:
      - [P384_FpInv.v]                       (Gallina divstep + iter_invariant)
      - [divsteps_p384.v]                    (cert axiom)
      - [P384_FpInv_closed.v]                (bridge composition)
      - [P384_InvertBoundInstantiation.v]    (parametric Phase 0e template)
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.

Local Open Scope Z_scope.

(** The P-384 base field prime: [2^384 - 2^128 - 2^96 + 2^32 - 1]. *)
Definition p384_modulus : Z :=
  Eval vm_compute in (2^384 - 2^128 - 2^96 + 2^32 - 1)%Z.

Definition p384_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (2^384 - 2^128 - 2^96 + 2^32 - 1))%Z.

Lemma p384_modulus_pos : p384_modulus = Z.pos p384_prime_pos.
Proof. vm_compute. reflexivity. Qed.

(** Axiomatized primality.  See [p224_prime.v] header for rationale. *)
Axiom prime_p384 : prime p384_modulus.
