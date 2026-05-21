(** * BW6-761 Frobenius constants (precomputed gamma values).

    These are powers of tower nonresidues evaluated modulo p, needed
    by the Frobenius endomorphisms in the final exponentiation.

    Tower structure (M-type):
      Fp3 = Fp[zeta]/(zeta^3 + 4),  cubic nonresidue nr = -4 in Fp
      Fp6 = Fp3[w]/(w^2 - zeta),    quadratic nonresidue = zeta in Fp3

    Gamma constants needed by bw6_fp6_frob (Frobenius pi):
      gamma_fp3 : Fp3 — represents the linear action of pi on Fp3
      gamma_fp6 : Fp3 — equals zeta^{(p-1)/2}

    Gamma constants needed by bw6_fp6_frob_p2 (Frobenius pi^2):
      gamma_fp3_p2 : Fp3
      gamma_fp6_p2 : Fp3

    Gamma constants needed by bw6_fp6_frob_p3 (Frobenius pi^3):
      gamma_fp6_p3 : Fp3 — equals -1 (since p^3 acts trivially on Fp3)

    NOTE: This file provides placeholder constant *values* (all zero
    except where mathematically forced) so that downstream files can
    *reference* the constants and the bedrock2 specs can be discharged
    against them.  Real cryptographic deployment requires populating
    these from a SageMath/gnark-crypto computation against p.  See
    BLS24_509_FrobConsts.v for the analogous fully-populated file. *)

From Stdlib Require Import ZArith.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime_certif.

Local Open Scope Z_scope.

Section FrobeniusConstants.
  Let p_pos : positive := Eval vm_compute in (Z.to_pos bw6_761_prime.m).
  Local Notation Fp := (F p_pos).
  Local Notation Fp3 := (Fp * Fp * Fp)%type.

  Local Notation "[ x ]" := (F.of_Z p_pos x).

  (* ================================================================ *)
  (* Frobenius pi (x -> x^p) constants                                *)
  (*                                                                    *)
  (* gamma_fp3 acts as the linear automorphism of Fp3 induced by pi.   *)
  (* For zeta with minimal polynomial zeta^3 + 4 = 0, pi(zeta) is a    *)
  (* root of the same polynomial; for BW6-761 specifically,            *)
  (* gamma_fp3 = zeta^{p-1}/3 lifted appropriately.                    *)
  (*                                                                    *)
  (* Placeholder values: identity-shaped constants.  See               *)
  (* gnark-crypto/ecc/bw6-761/internal/fptower for the real values.    *)
  (* ================================================================ *)

  Definition gamma_fp3 : Fp3 := ([1], [0], [0]).
  Definition gamma_fp6 : Fp3 := ([1], [0], [0]).

  (* ================================================================ *)
  (* Frobenius pi^2 constants                                          *)
  (* ================================================================ *)

  Definition gamma_fp3_p2 : Fp3 := ([1], [0], [0]).
  Definition gamma_fp6_p2 : Fp3 := ([1], [0], [0]).

  (* ================================================================ *)
  (* Frobenius pi^3 constants                                          *)
  (* p^3 acts trivially on Fp3, and pi^3(w) = -w in Fp6 = Fp3[w].     *)
  (* So gamma_fp6_p3 represents the constant -1 in Fp3.                *)
  (* ================================================================ *)

  Definition gamma_fp6_p3 : Fp3 := ([-1], [0], [0]).

End FrobeniusConstants.
