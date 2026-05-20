(** * P-224 (secp224r1) prime modulus + axiomatized primality.

    Minimal "prime cert" file for the Track Q divstep-inversion chain.
    Per the Track Q shortcut policy, primality is AXIOMATIZED rather
    than discharged via a Pocklington certificate — the certificate
    for [2^224 - 2^96 + 1] is straightforward to produce externally
    but is not blocking for the divstep chain (the chain only needs
    [Z.gcd x p = 1] as a hypothesis, which the user supplies).

    Sibling files in the chain:
      - [P224_FpInv.v]                       (Gallina divstep + iter_invariant)
      - [divsteps_p224.v]                    (cert axiom)
      - [P224_FpInv_closed.v]                (bridge composition)
      - [P224_InvertBoundInstantiation.v]    (parametric Phase 0e template)
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import ZArith.Znumtheory.

Local Open Scope Z_scope.

(** The P-224 base field prime: [2^224 - 2^96 + 1]. *)
Definition p224_modulus : Z :=
  Eval vm_compute in (2^224 - 2^96 + 1)%Z.

Definition p224_prime_pos : positive :=
  Eval vm_compute in (Z.to_pos (2^224 - 2^96 + 1))%Z.

Lemma p224_modulus_pos : p224_modulus = Z.pos p224_prime_pos.
Proof. vm_compute. reflexivity. Qed.

(** Axiomatized primality.  The full Pocklington certificate is
    straightforward (p-1 factors with a single ~190-bit cofactor)
    but is left out per the Track Q "no prime-cert engineering"
    shortcut.  The divstep convergence + Fp inverse correctness
    proofs in [P224_FpInv*.v] do not reduce through this axiom;
    they only need primality to derive [Z.gcd x p = 1] from
    [0 < x < p], and [P224_FpInv_closed.fp_inv_correct_closed]
    takes the gcd hypothesis directly. *)
Axiom prime_p224 : prime p224_modulus.
