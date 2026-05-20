(** * O'Connor convex-hull certificate for p25519 with δ₀ = 1/2.

    Mirror of [divsteps_bls12.v]'s axiomatization pattern, but for the
    δ₀=1/2 half framework (EUROCRYPT 2026 paper, Bernstein–Chen–Harrison–
    Huang–Maxwell–Wang–Wuille–Yang, "Accelerating and verifying constant-time
    modular inversion") + p25519.

    The computation
        ZMap.Empty (N.iter 590 (processDivstep_half p25519) state0_half)
    has been independently verified via OCaml extraction
    (`multi_curve_half_driver p25519 590`, ~100s wall, May 2026) —
    converged below the cert bound.

    We axiomatize the result here for parity with the BLS12-381 cert
    (which is also axiomatized in [divsteps_bls12.v] with the same
    "vm_cast Qed is too slow, axiomatize + OCaml-verify" pattern,
    documented in that file's header). *)

From Stdlib Require Import ZArith.
Require Import divsteps_base.
Require Import divsteps_base_half.

Local Open Scope Z_scope.

(** p25519 = 2^255 − 19. *)
Definition p25519 : Z :=
  0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition p25519_M : Z := p25519.

(** O'Connor convex-hull cert: state empties after 590 divsteps starting
    from [state0_half] (δ₀ = 1/2 encoding, [zeta_0 = -1]).  Verified
    externally; axiomatized here for parity with the BLS12-381 cert
    in [divsteps_bls12.v]. *)
Axiom p25519_half_certificate :
  ZMap.Empty (N.iter 590 (processDivstep_half p25519_M) state0_half).

Definition p25519_half_iters : N := 590.
