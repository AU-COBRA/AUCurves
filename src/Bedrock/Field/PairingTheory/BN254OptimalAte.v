(** * BN254OptimalAte: the BN254 optimal-ate pairing of [PairingSpec] as a closed function.

    [MillerLoopWP.bn254_optimal_ate_spec] (and its copy in [BN254_PairingRustConcrete.v]) takes the
    three Frobenius constants [gamma1 gamma_y gamma1_p2] as arguments.  This file fixes them to the
    values derived from [bn254_params] by [FrobConstants] ([gamma1_val], [gamma_y_val],
    [gamma1_p2_val]: xi^((p-1)/3), xi^((p-1)/2), xi^((p^2-1)/3) with xi = 9 + u), stated as
    literals and checked against [FrobConstants] by computation, and defines the closed pairing
    [bn254_optimal_ate : Z -> Z -> Fp2_Z -> Fp2_Z -> Fp12_Z].  Its body is the body of
    [bn254_optimal_ate_spec] at these constants (see [BN254OptimalAteBridge.v] for the equality).

    The imports are only [CurveParams], [BN254_params], [Affine], [ZModTower], [FrobConstants] and
    [PairingSpecDefs], so the file can be vendored without the bedrock2 stack.

    The second Frobenius correction of [PairingSpec.apply_corrections] at [bn254_params] uses the
    point [frobenius2_Q] = [(Qx * gamma1_p2, Qy)] = -pi^2(Q) (xi^((p^2-1)/2) = -1), with the entry
    [{| pi_power := 2; negate := false |}]: the optimal-ate line through -pi^2(Q), as the bedrock2
    [bn254_pairing_dsd_optimal] computes it.  (Before that entry was fixed it read [negate := true],
    which negated the point a second time, to pi^2(Q), and the pairing was not bilinear; checked
    numerically outside Rocq.)  With the fix the function agrees with the standard BN254
    optimal-ate pairing (py_ecc's bn128).  No [Admitted], no [Axiom].
*)

From Stdlib Require Import ZArith.ZArith.

Require Import Bedrock.Field.PairingTheory.Affine.
Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.Curves.BN254_params.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.FrobConstants.
Require Import Bedrock.Field.PairingTheory.PairingSpecDefs.

Local Open Scope Z_scope.

(** The Frobenius constants, as literals. *)
Definition bn254_gamma1 : Fp2_Z :=
  (21575463638280843010398324269430826099269044274347216827212613867836435027261,
   10307601595873709700152284273816112264069230130616436755625194854815875713954).
Definition bn254_gamma_y : Fp2_Z :=
  (2821565182194536844548159561693502659359617185244120367078079554186484126554,
   3505843767911556378687030309984248845540243509899259641013678093033130930403).
Definition bn254_gamma1_p2 : Fp2_Z :=
  (21888242871839275220042445260109153167277707414472061641714758635765020556616, 0).

(** They are the constants [FrobConstants] derives from [bn254_params]. *)
Lemma bn254_gamma1_eq : gamma1_val bn254_params = bn254_gamma1.
Proof. vm_cast_no_check (eq_refl bn254_gamma1). Qed.
Lemma bn254_gamma_y_eq : gamma_y_val bn254_params = bn254_gamma_y.
Proof. vm_cast_no_check (eq_refl bn254_gamma_y). Qed.
Lemma bn254_gamma1_p2_eq : gamma1_p2_val bn254_params = bn254_gamma1_p2.
Proof. vm_cast_no_check (eq_refl bn254_gamma1_p2). Qed.

(** The closed BN254 pairing: [PairingSpec.optimal_ate] on the ZModTower instance, with the
    extra tower operations of [MillerLoopWP.bn254_optimal_ate_spec]. *)
Definition bn254_optimal_ate (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
  PairingSpec.optimal_ate
    bn254_zmod_ops
    (zfp12_conj (prime_p bn254_params))
    (zfp12_inv (prime_p bn254_params) (xi_re bn254_params, xi_im bn254_params))
    (zfp12_frob_p2 (prime_p bn254_params) (xi_re bn254_params, xi_im bn254_params))
    (zfp12_pow (prime_p bn254_params) (xi_re bn254_params, xi_im bn254_params))
    (zfp2_conj (prime_p bn254_params))
    (zfp2_mul_const (prime_p bn254_params))
    bn254_params
    bn254_gamma1 bn254_gamma_y bn254_gamma1_p2
    Px Py Qx Qy.

(** Its Miller part (loop and the two Frobenius corrections) and final exponentiation. *)
Definition bn254_miller (Px Py : Z) (Qx Qy : Fp2_Z) : Fp12_Z :=
  let '(f, Tx, Ty) :=
    affine_miller_aux bn254_zmod_ops (loop_abs bn254_params)
      (Z.to_nat (Z.log2 (loop_abs bn254_params)))
      Px Py Qx Qy (fp12_one bn254_zmod_ops) Qx Qy in
  PairingSpec.apply_corrections bn254_zmod_ops
    (zfp2_conj (prime_p bn254_params)) (zfp2_mul_const (prime_p bn254_params))
    (optimal_ate_extras bn254_params) f Tx Ty Px Py Qx Qy
    bn254_gamma1 bn254_gamma_y bn254_gamma1_p2.

Definition bn254_final_exp (f : Fp12_Z) : Fp12_Z :=
  PairingSpec.final_exp bn254_zmod_ops
    (zfp12_conj (prime_p bn254_params))
    (zfp12_inv (prime_p bn254_params) (xi_re bn254_params, xi_im bn254_params))
    (zfp12_frob_p2 (prime_p bn254_params) (xi_re bn254_params, xi_im bn254_params))
    (zfp12_pow (prime_p bn254_params) (xi_re bn254_params, xi_im bn254_params))
    (prime_p bn254_params) (scalar_r bn254_params) f.

Lemma bn254_optimal_ate_split (Px Py : Z) (Qx Qy : Fp2_Z) :
  bn254_optimal_ate Px Py Qx Qy = bn254_final_exp (bn254_miller Px Py Qx Qy).
Proof.
  unfold bn254_optimal_ate, bn254_final_exp, bn254_miller, PairingSpec.optimal_ate.
  destruct (affine_miller_aux bn254_zmod_ops (loop_abs bn254_params)
              (Z.to_nat (Z.log2 (loop_abs bn254_params)))
              Px Py Qx Qy (fp12_one bn254_zmod_ops) Qx Qy) as [[f Tx] Ty].
  reflexivity.
Qed.
