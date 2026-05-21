(** * BW6-761 Frobenius constants (precomputed gamma values).

    These are powers of tower nonresidues evaluated modulo p,
    needed by the Frobenius endomorphisms in the final
    exponentiation.

    Tower structure (M-type):
      Fp3 = Fp[zeta]/(zeta^3 + 4),  cubic nonresidue nr = -4 in Fp
      Fp6 = Fp3[w]/(w^2 - zeta),    quadratic nonresidue = zeta in Fp3

    Following gnark-crypto/ecc/bw6-761/internal/fptower/frobenius.go,
    Frobenius pi acts on Fp6 = Fp3[w] component-wise:

      pi(B0 + B1 w) = pi_Fp3(B0) + sqrt(alpha) * pi_Fp3(B1) * w

    where pi_Fp3 scales each Fp3 component by powers of
        alpha = (-4)^((p-1)/3) mod p
    a primitive cube root of unity in Fp.

    Concretely if B0 = (a0, a1, a2) and B1 = (b0, b1, b2):
      out.B0 = (a0, alpha * a1, alpha^2 * a2)
      out.B1 = (sqrt(alpha) * b0, sqrt(alpha)*alpha * b1, sqrt(alpha)*alpha^2 * b2)

    So Frobenius pi needs 5 Fp scalars per (input,output) pair:
      gamma_a1_pi, gamma_a2_pi          (apply to c0 components)
      gamma_b0_pi, gamma_b1_pi, gamma_b2_pi  (apply to c1 components)

    Frobenius pi^2 uses the same shape with each scalar squared.

    Frobenius pi^3 acts trivially on Fp3 (alpha^3 = 1), and
    pi^3(w) = -w in Fp6 = Fp3[w], so only the c1 component is
    negated.  We expose this as a single scalar gamma_b_pi3 = -1.

    All scalars are pure Z literals (not F-elements); the bedrock2
    callers wrap them via F.of_Z / from-bytes loads as needed.  *)

From Stdlib Require Import ZArith.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime_certif.

Local Open Scope Z_scope.

Section BW6FrobeniusConstants.

  (* ================================================================ *)
  (* Frobenius pi (x -> x^p) constants (5 Fp scalars)                  *)
  (* ================================================================ *)

  (** alpha = (-4)^((p-1)/3) mod p — a primitive cube root of 1 in Fp. *)
  Definition bw6_gamma_a1_pi_z : Z :=
    4922464560225523242118178942575080391082002530232324381063048548642823052024664478336818169867474395270858391911405337707247735739826664939444490469542109391530482826728203582549674992333383150446779312029624171857054392282775648.

  (** alpha^2 mod p *)
  Definition bw6_gamma_a2_pi_z : Z :=
    1968985824090209297278610739700577151397666382303825728450741611566800370218827257750865013421937292370006175842381275743914023380727582819905021229583192207421122272650305267822868639090213645505120388400344940985710520836292650.

  (** sqrt(alpha) mod p — a chosen square root of alpha.
      (Tonelli-Shanks branch — for this prime sqrt(alpha) happens to
      equal alpha^2 modulo p; equivalently sqrt(alpha)^3 = alpha^3 = 1.) *)
  Definition bw6_gamma_b0_pi_z : Z :=
    1968985824090209297278610739700577151397666382303825728450741611566800370218827257750865013421937292370006175842381275743914023380727582819905021229583192207421122272650305267822868639090213645505120388400344940985710520836292650.

  (** sqrt(alpha) * alpha mod p — equals 1 for our chosen sqrt branch. *)
  Definition bw6_gamma_b1_pi_z : Z := 1.

  (** sqrt(alpha) * alpha^2 mod p — equals alpha for our chosen branch. *)
  Definition bw6_gamma_b2_pi_z : Z :=
    4922464560225523242118178942575080391082002530232324381063048548642823052024664478336818169867474395270858391911405337707247735739826664939444490469542109391530482826728203582549674992333383150446779312029624171857054392282775648.

  (* ================================================================ *)
  (* Frobenius pi^2 (x -> x^{p^2}) constants                           *)
  (* Each gamma_xi_pi2 = (gamma_xi_pi)^2 mod p.                        *)
  (* ================================================================ *)

  Definition bw6_gamma_a1_pi2_z : Z :=
    1968985824090209297278610739700577151397666382303825728450741611566800370218827257750865013421937292370006175842381275743914023380727582819905021229583192207421122272650305267822868639090213645505120388400344940985710520836292650.
  Definition bw6_gamma_a2_pi2_z : Z :=
    4922464560225523242118178942575080391082002530232324381063048548642823052024664478336818169867474395270858391911405337707247735739826664939444490469542109391530482826728203582549674992333383150446779312029624171857054392282775648.
  Definition bw6_gamma_b0_pi2_z : Z :=
    4922464560225523242118178942575080391082002530232324381063048548642823052024664478336818169867474395270858391911405337707247735739826664939444490469542109391530482826728203582549674992333383150446779312029624171857054392282775648.
  Definition bw6_gamma_b1_pi2_z : Z := 1.
  Definition bw6_gamma_b2_pi2_z : Z :=
    1968985824090209297278610739700577151397666382303825728450741611566800370218827257750865013421937292370006175842381275743914023380727582819905021229583192207421122272650305267822868639090213645505120388400344940985710520836292650.

  (* ================================================================ *)
  (* Frobenius pi^3: negation of c1 only (p ≡ 1 mod 3 makes pi^3       *)
  (* trivial on Fp3, but pi^3(w) = -w).                                 *)
  (* ================================================================ *)

  Definition bw6_gamma_b_pi3_z : Z :=
    6891450384315732539396789682275657542479668912536150109513790160209623422243491736087683183289411687640864567753786613451161759120554247759349511699125301598951605099378508850372543631423596795951899700429969112842764913119068298.

End BW6FrobeniusConstants.
