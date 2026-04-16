(** * FrobConstants: compute Frobenius constants from [CurveParams].

    Given a [CurveParams] record, compute the Frobenius constants
    (gamma1, gamma_y, gamma1_p2, etc.) needed by [PairingSpec.optimal_ate].

    These are xi^{k*(p^i-1)/6} for various k and i, computed via
    [zpow_mod_aux] from [ZModTower.v]. The values are in STANDARD FORM
    (not Montgomery), since [ZModTower] uses standard Z arithmetic.

    The point: the constants are DERIVED from the [CurveParams] data
    (prime [p], nonresidue [xi_re + xi_im * u]), not hardcoded as hex
    limbs. If someone changes the curve seed, the constants update
    automatically. This is how the three wrong BLS12-381 p^2-Frobenius
    constants (found 2026-04-10) should have been caught: by comparing
    the derived constants against the hardcoded limbs.
*)

From Stdlib Require Import ZArith.ZArith.

Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.ZModTower.

Local Open Scope Z_scope.

Section FrobConstants.
  Variable c : CurveParams.
  Let p := prime_p c.
  Let xi : Fp2_Z := (xi_re c, xi_im c).

  (** xi^e in Fp2, computed via [zfp2_mul]. *)
  Fixpoint zfp2_pow (base : Fp2_Z) (e : nat) : Fp2_Z :=
    match e with
    | O => (1, 0)
    | S O => base
    | S e' => zfp2_mul p base (zfp2_pow base e')
    end.

  (** xi^e for large Z exponents (via square-and-multiply). *)
  Definition zfp2_pow_Z (base : Fp2_Z) (e : Z) : Fp2_Z :=
    let fix go (b : Fp2_Z) (exp : positive) (acc : Fp2_Z) : Fp2_Z :=
      match exp with
      | xH => zfp2_mul p acc b
      | xO exp' => go (zfp2_mul p b b) exp' acc
      | xI exp' => go (zfp2_mul p b b) exp' (zfp2_mul p acc b)
      end in
    match e with
    | Z0 => (1, 0)
    | Zpos exp => go base exp (1, 0)
    | Zneg _ => (0, 0)  (* negative exponents not supported *)
    end.

  (** Frobenius pi constants (for Fp12 frobenius_p). *)
  Definition gamma1_val : Fp2_Z := zfp2_pow_Z xi ((p - 1) / 3).
  Definition gamma2_val : Fp2_Z := zfp2_pow_Z xi (2 * (p - 1) / 3).
  Definition w_frob_c1_val : Fp2_Z := zfp2_pow_Z xi ((p - 1) / 6).

  (** Frobenius pi^2 constants (should be in Fp, i.e., imaginary part = 0). *)
  Definition gamma1_p2_val : Fp2_Z := zfp2_pow_Z xi ((p * p - 1) / 3).
  Definition gamma2_p2_val : Fp2_Z := zfp2_pow_Z xi (2 * (p * p - 1) / 3).
  Definition w_frob_p2_c1_val : Fp2_Z := zfp2_pow_Z xi ((p * p - 1) / 6).

  (** Correction constants for Q1 (BN curves). *)
  Definition gamma_y_val : Fp2_Z := zfp2_pow_Z xi ((p - 1) / 2).

End FrobConstants.

(** Smoke test: gamma1 for BN254 should have c0 = a known value.
    This is too expensive for vm_compute (254-bit modular exp in Coq),
    but with native_compute or Extraction it's instant. *)
(* Eval native_compute in gamma1_val bn254_params. *)
(* Would produce: (xi^{(p-1)/3}).c0 = <the expected value> *)
