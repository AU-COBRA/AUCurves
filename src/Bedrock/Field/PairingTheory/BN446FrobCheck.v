(** * BN446FrobCheck: FrobConstants at [bn446_params], and xi non-square, non-cube.

    Every Frobenius constant that [FrobConstants] derives from [bn446_params]
    (xi = 1 + 9u) is computed and compared with the literal of BN446ParamsCheck.v
    (= the values of scripts/bn446/params_check.py).  The three
    p^2-constants have imaginary part 0.  xi^((p^2-1)/2) = -1 and xi^((p^2-1)/3) <> 1:
    xi is neither a square nor a cube in Fp2, so v^3 - xi and w^6 - xi are
    irreducible.  BN446TwistCheck.v checks that these gammas are the Frobenius of the
    D-twist (psi(G2) = [p] G2).

    Each computation is a 446- or 892-bit exponentiation in Fp2 over [Z]; they are
    checked by the kernel's native conversion ([native_cast_no_check]), about 10 s,
    resp. 22 s each (vm_compute would take about 34 s, resp. 68 s, and twice that with a
    tactic-time check). *)

From Stdlib Require Import ZArith.ZArith.

Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.FrobConstants.
Require Import Bedrock.Field.PairingTheory.Curves.BN446_params.
Require Import Bedrock.Field.PairingTheory.BN446ParamsCheck.

Local Open Scope Z_scope.

Lemma bn446_gamma1_val : gamma1_val bn446_params = bn446_gamma1_lit.
Proof. native_cast_no_check (eq_refl bn446_gamma1_lit). Qed.

Lemma bn446_gamma2_val : gamma2_val bn446_params = bn446_gamma2_lit.
Proof. native_cast_no_check (eq_refl bn446_gamma2_lit). Qed.

Lemma bn446_w_frob_c1_val : w_frob_c1_val bn446_params = bn446_w_frob_c1_lit.
Proof. native_cast_no_check (eq_refl bn446_w_frob_c1_lit). Qed.

Lemma bn446_gamma1_p2_val : gamma1_p2_val bn446_params = bn446_gamma1_p2_lit.
Proof. native_cast_no_check (eq_refl bn446_gamma1_p2_lit). Qed.

Lemma bn446_gamma2_p2_val : gamma2_p2_val bn446_params = bn446_gamma2_p2_lit.
Proof. native_cast_no_check (eq_refl bn446_gamma2_p2_lit). Qed.

Lemma bn446_w_frob_p2_c1_val : w_frob_p2_c1_val bn446_params = bn446_w_frob_p2_c1_lit.
Proof. native_cast_no_check (eq_refl bn446_w_frob_p2_c1_lit). Qed.

Lemma bn446_gamma_y_val : gamma_y_val bn446_params = bn446_gamma_y_lit.
Proof. native_cast_no_check (eq_refl bn446_gamma_y_lit). Qed.

(** The p^2-constants lie in Fp. *)
Lemma bn446_p2_constants_in_Fp :
  snd (gamma1_p2_val bn446_params) = 0 /\ snd (gamma2_p2_val bn446_params) = 0 /\
  snd (w_frob_p2_c1_val bn446_params) = 0.
Proof.
  rewrite bn446_gamma1_p2_val, bn446_gamma2_p2_val, bn446_w_frob_p2_c1_val.
  repeat split; reflexivity.
Qed.

(** xi is not a square in Fp2: xi^((p^2-1)/2) = -1. *)
Lemma bn446_xi_nonsquare :
  zfp2_pow_Z bn446_params bn446_chk_xi ((bn446_chk_p * bn446_chk_p - 1) / 2)
  = (bn446_chk_p - 1, 0).
Proof. native_cast_no_check (eq_refl (bn446_chk_p - 1, 0)). Qed.

(** xi is not a cube in Fp2: xi^((p^2-1)/3) = gamma1_p2 <> 1.  (Stated and computed in the
    same form as [bn446_xi_nonsquare]; proving it from [bn446_gamma1_p2_val] by [change] makes
    the unifier evaluate the exponentiation.) *)
Lemma bn446_xi_cube_test :
  zfp2_pow_Z bn446_params bn446_chk_xi ((bn446_chk_p * bn446_chk_p - 1) / 3) = bn446_gamma1_p2_lit.
Proof. native_cast_no_check (eq_refl bn446_gamma1_p2_lit). Qed.

Lemma bn446_xi_noncube :
  zfp2_pow_Z bn446_params bn446_chk_xi ((bn446_chk_p * bn446_chk_p - 1) / 3) <> (1, 0).
Proof. rewrite bn446_xi_cube_test. unfold bn446_gamma1_p2_lit. discriminate. Qed.
