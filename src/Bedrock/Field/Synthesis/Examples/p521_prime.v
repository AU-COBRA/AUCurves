(** * P-521 (secp521r1) prime modulus + axiomatized primality.

    Minimal "prime cert" file for the Track Q divstep-inversion chain.
    Per the Track Q shortcut policy, primality is AXIOMATIZED rather
    than discharged via a Pocklington certificate.  The prime
    [2^521 - 1] is a well-known Mersenne prime (M_521); a fresh
    Pocklington/ECPP cert is not blocking for the divstep chain.

    Sibling files in the chain:
      - [P521_FpInv.v]                       (Gallina divstep + iter_invariant)
      - [divsteps_p521.v]                    (cert axiom)
      - [P521_FpInv_closed.v]                (bridge composition)
      - [P521_InvertBoundInstantiation.v]    (parametric Phase 0e template)
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.

Local Open Scope Z_scope.

(** The P-521 base field prime: the Mersenne prime [2^521 - 1]. *)
Definition p521_modulus : Z :=
  Eval vm_compute in (2^521 - 1)%Z.

Definition p521_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (2^521 - 1))%Z.

Lemma p521_modulus_pos : p521_modulus = Z.pos p521_prime_pos.
Proof. vm_compute. reflexivity. Qed.

(** Axiomatized primality (M_521 is a Mersenne prime, well-known
    since 1952; full Lucas–Lehmer cert is outside the Track Q scope). *)
Axiom prime_p521 : prime p521_modulus.
