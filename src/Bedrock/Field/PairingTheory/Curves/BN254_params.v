(** * BN254 (alt_bn128) curve parameters.

    See [PairingTheory/CurveParams.v] for what each field means.

    BN254 is the Ethereum precompile curve.
      p = 21888242871839275222246405745257275088696311157297823662689037894645226208583
      r = 21888242871839275222246405745257275088548364400416034343698204186575808495617
      curve   E :  y^2 = x^3 + 3
      tower   Fp2 = Fp[u]/(u^2+1),  xi = 9 + u
      twist   D-twist:  E' :  y^2 = x^3 + 3 / xi
      param   loop = 6u + 2 = 0x19D797039BE763BA8 (65 bits, positive)
      where u_BN = 0x44E992B44A6909F1 is the BN seed.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Definition bn254_params : CurveParams := {|
  prime_p          := 21888242871839275222246405745257275088696311157297823662689037894645226208583;
  scalar_r         := 21888242871839275222246405745257275088548364400416034343698204186575808495617;

  curve_a          := 0;
  curve_b          := 3;

  embedding_degree := 12%nat;

  fp2_beta         := -1;
  xi_re            := 9;
  xi_im            := 1;

  twist            := Dtwist;

  loop_abs         := 29793968203157093288;  (* 6 * u_BN + 2 *)
  loop_neg         := false;

  optimal_ate_extras :=
    [ {| pi_power := 1; negate := false |}    (* +pi(Q) *)
    ; {| pi_power := 2; negate := true  |}    (* -pi^2(Q) *)
    ];
|}.

Lemma bn254_params_wf : CurveParams_wf bn254_params.
Proof.
  constructor; cbv; reflexivity || lia || (intros; discriminate).
Qed.
