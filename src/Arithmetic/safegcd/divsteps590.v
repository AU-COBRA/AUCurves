(** * Curve25519 divstep convergence certificate (δ₀ = 1/2).

    Proves [ZMap.Empty (N.iter 590 (processDivstep_half p25519) state0_half)],
    matching paper §3.4 / Theorem 1 of the EUROCRYPT 2026 paper of
    Bernstein–Chen–Harrison–Huang–Maxwell–Wang–Wuille–Yang,
    *Accelerating and verifying constant-time modular inversion*.

    This is the δ₀ = 1/2 analogue of [divsteps724.v]: that file proves the
    same statement for the original δ₀ = 1 algorithm at [N = 724] for any
    256-bit modulus; this file specialises to [p25519 = 2^255 − 19] with
    the optimised count [N = 590].

    Cert proof uses [vm_cast_no_check] so [Qed] re-checks the convex-hull
    computation in the kernel. On 256-bit moduli with [native_compute]
    this is "seconds" per [OPTIMIZATION.md] (we use [vm_compute] here for
    portability; native may be faster). *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

(** [p25519 = 2^255 - 19]. *)
Definition p25519 : Z :=
  0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Lemma p25519_correct : p25519 = (2^255 - 19)%Z.
Proof. vm_compute. reflexivity. Qed.

(** **Certificate**: the convex-hull algorithm converges to empty in 590
    divsteps for [p25519] under δ₀ = 1/2.  Composed with a δ₀ = 1/2
    counterpart of [divsteps_theory.v]'s [in_State_step] /
    [processDivstep_correct] (mirror of those proofs against
    [divsteps_base_half] / [divsteps_def_half] — mechanical) this would
    yield convergence of the actual [divsteps_half.step] iteration at
    [N = 590]. *)
Lemma p25519_certificate_590 :
  ZMap.Empty (N.iter 590 (processDivstep_half p25519) state0_half).
Proof.
apply ZMap.is_empty_2.
vm_cast_no_check (refl_equal true).
Time Qed.

Definition p25519_iters : N := 590.
