(** * BN446 curve parameters.

    BN446 is a 446-bit BN curve.
      seed u  = 0x4000000000000000001000000001  (positive, 111 bits)
      |6u+2|  = 0x18000000000000000006000000008  (113 bits, 2 64-bit words)
      curve E :  y^2 = x^3 + 3
      tower   Fp2 = Fp[u]/(u^2 + 1),  xi = 2 + 3*u
      twist   D-twist:  E' :  y^2 = x^3 + 3 / xi

    The xi here is unusual (xi_im = 3 instead of the typical 1) because the
    standard nonresidue 1+u or 9+u doesn't work for this prime; see
    BN446_Pairing.v for the derivation.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Crypto.Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Definition bn446_params : CurveParams := {|
  prime_p          := bn446_modulus;
  scalar_r         := bn446_r;

  curve_a          := 0;
  curve_b          := 3;

  embedding_degree := 12%nat;

  fp2_beta         := -1;
  xi_re            := 2;
  xi_im            := 3;

  twist            := Dtwist;

  (* |6u+2| as a literal (113 bits). Hi limb 0x0001800000000000, lo 0x0000006000000008. *)
  loop_abs         := 0x18000000000000000006000000008;
  loop_neg         := false;

  optimal_ate_extras :=
    [ {| pi_power := 1; negate := false |}
    ; {| pi_power := 2; negate := true  |}
    ];
|}.

Lemma bn446_params_wf : CurveParams_wf bn446_params.
Proof.
  constructor; cbv; reflexivity || lia || (intros; discriminate).
Qed.
