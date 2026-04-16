(** * BLS12-381 curve parameters.

    See [PairingTheory/CurveParams.v] for what each field means.

      p =  4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787
      r =  52435875175126190479447740508185965837690552500527637822603658699938581184513
      curve   E :  y^2 = x^3 + 4
      tower   Fp2 = Fp[u]/(u^2+1),  xi = 1 + u
      twist   M-twist:  E' :  y^2 = x^3 + 4 * xi
      param   loop = -|x|, |x| = 0xd201000000010000  (BLS12-381 seed is negative)
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Definition bls12_381_params : CurveParams := {|
  prime_p          := 4002409555221667393417789825735904156556882819939007885332058136124031650490837864442687629129015664037894272559787;
  scalar_r         := 52435875175126190479447740508185965837690552500527637822603658699938581184513;

  curve_a          := 0;
  curve_b          := 4;

  embedding_degree := 12%nat;

  fp2_beta         := -1;
  xi_re            := 1;
  xi_im            := 1;

  twist            := Mtwist;

  loop_abs         := 15132376222941642752;  (* 0xd201000000010000 *)
  loop_neg         := true;                  (* BLS12-381 seed is negative *)

  optimal_ate_extras := [];
|}.

Lemma bls12_381_params_wf : CurveParams_wf bls12_381_params.
Proof.
  constructor; cbv; reflexivity || lia || (intros; discriminate).
Qed.
