(** * BN256 curve parameters.

    BN256 is a 256-bit BN curve (alt to BN254 / different seed).
      seed u  = 0x5A76AE9AEC588301  (positive, 63 bits)
      |6u+2|  = 0x21EC817A18A131208  (66 bits)
      curve E :  y^2 = x^3 + 3
      tower   Fp2 = Fp[u]/(u^2 + 1),  xi = 3 + u
      twist   D-twist:  E' :  y^2 = x^3 + 3 / xi
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Field.Synthesis.Examples.bn256_prime_certif.
Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Definition bn256_params : CurveParams := {|
  prime_p          := bn256_modulus;
  scalar_r         := bn256_r;

  curve_a          := 0;
  curve_b          := 3;

  embedding_degree := 12%nat;

  fp2_beta         := -1;
  xi_re            := 3;
  xi_im            := 1;

  twist            := Dtwist;

  loop_abs         := 39111536946472751624;  (* |6u+2| = 0x21EC817A18A131208 *)
  loop_neg         := false;

  optimal_ate_extras :=
    [ {| pi_power := 1; negate := false |}
    ; {| pi_power := 2; negate := true  |}
    ];
|}.

Lemma bn256_params_wf : CurveParams_wf bn256_params.
Proof.
  constructor; cbv; reflexivity || lia || (intros; discriminate).
Qed.
