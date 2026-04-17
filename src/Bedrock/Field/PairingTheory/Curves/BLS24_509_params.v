(** * BLS24-509 curve parameters.

    BLS24-509 has embedding degree 24 and a *quartic* twist (G2 in Fp4),
    not a sextic twist. The tower is Fp -> Fp2 -> Fp4 -> Fp24, NOT the
    Fp -> Fp2 -> Fp6 -> Fp12 tower used by BN/BLS12 curves.

    For this curve the [CurveParams] record from
    [PairingTheory/CurveParams.v] is a partial fit only:
    [embedding_degree] is correct (24), [loop_abs] / [loop_neg] make sense,
    and the BN-style [optimal_ate_extras] correction list is empty (BLS
    family). But [xi_re] / [xi_im] / [twist] refer to the (Fp2 -> Fp6)
    nonresidue and don't directly model the (Fp4 -> Fp24) sextic step.
    Future work, see PLAN_PAIRING_SPECS.md: extend [CurveParams] with a
    sum over tower shapes so BLS24 (and eventually BLS48 etc.) is covered
    natively.

    Curve data:
      seed z  = -0x800000ffff801   (negative)
      |z|     =  0x800000ffff801    (52 bits)
      curve E :  y^2 = x^3 + 1
      tower   Fp2 = Fp[u]/(u^2 + 1),  Fp4 = Fp2[v]/(v^2 - (1+u)),
              Fp24 = Fp4[w]/(w^6 - v).
      twist   D-type quartic twist
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Field.Synthesis.Examples.bls24_509_prime.
Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

Definition bls24_509_params : CurveParams := {|
  prime_p          := bls24_509_modulus;
  scalar_r         := bls24_509_order;

  curve_a          := 0;
  curve_b          := 1;

  embedding_degree := 24%nat;

  fp2_beta         := -1;
  (* xi_re / xi_im model the (Fp2 -> Fp6) nonresidue, which doesn't apply
     directly to BLS24's Fp4-based tower. Setting to 1+u as a partial
     placeholder. The full Fp4 / Fp24 tower constants need a record
     extension to be captured properly. *)
  xi_re            := 1;
  xi_im            := 1;

  twist            := Dtwist;

  loop_abs         := 0x800000ffff801;   (* |z|, BLS24-509 seed is negative *)
  loop_neg         := true;

  optimal_ate_extras := [];   (* BLS family: no Q1/Q2 corrections *)
|}.

Lemma bls24_509_params_wf : CurveParams_wf bls24_509_params.
Proof.
  constructor; cbv; reflexivity || lia || (intros; discriminate).
Qed.
