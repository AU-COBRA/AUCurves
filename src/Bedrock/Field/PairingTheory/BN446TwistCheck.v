(** * BN446TwistCheck: the FrobConstants gammas give the Frobenius of the BN446 D-twist.

    psi(Q) = (conj(Qx) gamma1, conj(Qy) gamma_y) is the p-power Frobenius of
    E' : y^2 = x^3 + 257/xi carried to the twist; on G2 it is multiplication by p.
    [frobenius2_Q] (PairingSpecDefs) is (Qx gamma1_p2, Qy) = -pi^2(Q).  Checked at the G2 of
    BN446ParamsCheck.v, first at the literal gammas (one native computation each, about
    41 s and 64 s), then restated with [gamma1_val], [gamma_y_val], [gamma1_p2_val]
    (FrobConstants at [bn446_params]) through BN446FrobCheck.v. *)

From Stdlib Require Import ZArith.ZArith.

Require Import Bedrock.Field.PairingTheory.CurveParams.
Require Import Bedrock.Field.PairingTheory.ZModTower.
Require Import Bedrock.Field.PairingTheory.FrobConstants.
Require Import Bedrock.Field.PairingTheory.Curves.BN446_params.
Require Import Bedrock.Field.PairingTheory.BN446ParamsCheck.
Require Import Bedrock.Field.PairingTheory.BN446FrobCheck.

Local Open Scope Z_scope.

(** psi(G2) = (conj(x) gamma1, conj(y) gamma_y) = [p mod r] G2. *)
Lemma bn446_psi_g2 :
  g2_mul_is bn446_g2_x bn446_g2_y (bn446_chk_p mod bn446_chk_r)
    (zfp2_mul bn446_chk_p (zfp2_conj bn446_chk_p bn446_g2_x) bn446_gamma1_lit)
    (zfp2_mul bn446_chk_p (zfp2_conj bn446_chk_p bn446_g2_y) bn446_gamma_y_lit) = true.
Proof. native_cast_no_check (eq_refl true). Qed.

(** (x gamma1_p2, y) = [-p^2 mod r] G2 = -pi^2(G2). *)
Lemma bn446_frob2_g2 :
  g2_mul_is bn446_g2_x bn446_g2_y ((- (bn446_chk_p * bn446_chk_p)) mod bn446_chk_r)
    (zfp2_mul bn446_chk_p bn446_g2_x bn446_gamma1_p2_lit) bn446_g2_y = true.
Proof. native_cast_no_check (eq_refl true). Qed.

(** psi(G2) = [p mod r] G2, with the FrobConstants gammas. *)
Lemma bn446_psi_g2_frob :
  g2_mul_is bn446_g2_x bn446_g2_y (bn446_chk_p mod bn446_chk_r)
    (zfp2_mul bn446_chk_p (zfp2_conj bn446_chk_p bn446_g2_x) (gamma1_val bn446_params))
    (zfp2_mul bn446_chk_p (zfp2_conj bn446_chk_p bn446_g2_y) (gamma_y_val bn446_params)) = true.
Proof. rewrite bn446_gamma1_val, bn446_gamma_y_val. exact bn446_psi_g2. Qed.

(** frobenius2(G2) = (x gamma1_p2, y) = [-p^2 mod r] G2 = -pi^2(G2), with FrobConstants. *)
Lemma bn446_frob2_g2_frob :
  g2_mul_is bn446_g2_x bn446_g2_y ((- (bn446_chk_p * bn446_chk_p)) mod bn446_chk_r)
    (zfp2_mul bn446_chk_p bn446_g2_x (gamma1_p2_val bn446_params)) bn446_g2_y = true.
Proof. rewrite bn446_gamma1_p2_val. exact bn446_frob2_g2. Qed.
