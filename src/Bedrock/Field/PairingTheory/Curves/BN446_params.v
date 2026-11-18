(** * BN446 curve parameters.

    BN446 is a 446-bit BN curve (Aranha, Fuentes-Castaneda, Knapp, Menezes,
    Rodriguez-Henriquez, "Implementing pairings at the 192-bit security level").
      seed u  = 0x4000000000000000001000000001 = 2^110 + 2^36 + 1  (positive, 111 bits)
      |6u+2|  = 0x18000000000000000006000000008  (113 bits, 2 64-bit words)
      curve E :  y^2 = x^3 + 257           (#E(Fp) = p + 1 - t = r)
      tower   Fp2 = Fp[u]/(u^2 + 1),  xi = 1 + 9*u
      twist   D-twist:  E' :  y^2 = x^3 + 257 / xi   (r | #E'(Fp2) = r (2p - r))
      G1 = (-1, 16);  a G2 of order r is in BN446ParamsCheck.v.

    History: this record used to say curve_b := 3 and xi := 2 + 3u.  The curve
    y^2 = x^3 + 3 has no point of order r over this p (#E_3(Fp) = p+1+(t-3f)/2),
    and with xi = 2 + 3u the curve b = 257 has its order-r twist on the M side
    (y^2 = x^3 + 257 xi), not the D-twist this record and the D-twist line of
    the spec describe.  xi = 1 + 9u is a non-square and a non-cube in Fp2 (so
    v^3 - xi and w^6 - xi are irreducible) and makes y^2 = x^3 + 257/xi the
    twist with order divisible by r (BN446ParamsCheck.v checks all of this by
    computation).  The xi's with 0 <= a, b <= 12 that do both include 1+9u,
    9+u, 1+11u, 2+5u, 3+6u; 1 + u and 2 + u are squares or cubes.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Field.Synthesis.Examples.bn446_prime_certif.
Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Definition bn446_params : CurveParams := {|
  prime_p          := bn446_modulus;
  scalar_r         := bn446_r;

  curve_a          := 0;
  curve_b          := 257;

  embedding_degree := 12%nat;

  fp2_beta         := -1;
  xi_re            := 1;
  xi_im            := 9;

  twist            := Dtwist;

  (* |6u+2| as a literal (113 bits). Hi limb 0x0001800000000000, lo 0x0000006000000008. *)
  loop_abs         := 0x18000000000000000006000000008;
  loop_neg         := false;

  optimal_ate_extras :=
    [ {| pi_power := 1; negate := false |}    (* +pi(Q) *)
    ; {| pi_power := 2; negate := false |}    (* -pi^2(Q), see below *)
    ];
    (* [frobenius2_Q] returns (Qx * xi^((p^2-1)/3), Qy), which is already -pi^2(Q)
       because xi^((p^2-1)/2) = -1; so no further negation (the optimal-ate line
       goes through -pi^2(Q)). *)
|}.

Lemma bn446_params_wf : CurveParams_wf bn446_params.
Proof.
  constructor; cbv; reflexivity || lia || (intros; discriminate).
Qed.
