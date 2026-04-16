(** * BW6-761 curve parameters.

    BW6-761 has embedding degree 6 (NOT 12 like BN/BLS12). The tower is
    Fp -> Fp3 -> Fp6 — only one cubic and one quadratic step, no
    intermediate Fp2. The [CurveParams] record from
    [PairingTheory/CurveParams.v] only models the (Fp2 -> Fp6 -> Fp12)
    tower so BW6 fits awkwardly. We record what we can:

    Curve data:
      embedding_degree = 6
      curve E :  y^2 = x^3 - 1   (typically)
      twist   M-type sextic twist (paired with BLS12-377)

    NOTE: This file is a placeholder. The bedrock2 BW6-761 source only
    covers the prime / leaf field operations (bw6_761_prime.v); there is
    no [BW6_761_Pairing.v] yet, so most of these fields are best-effort
    references that should be revisited once a pairing implementation
    exists. The [optimal_ate_extras] for BW6-761 is also non-trivial:
    BW6 uses two separate Miller loops with a final adjustment, which
    the current [CurveParams] record can't express.

    See PLAN_PAIRING_SPECS.md for the future work needed to extend the
    record so that BW6 / BLS24 / BLS48 fit natively.
*)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Field.PairingTheory.CurveParams.

Local Open Scope Z_scope.

(** Inline the BW6-761 prime literally rather than depending on
    bw6_761_prime.v's internal name. *)
Definition bw6_761_modulus_lit : Z :=
  0x122e824fb83ce0ad187c94004faff3eb926186a81d14688528275ef8087be41707ba638e584e91903cebaff25b423048689c8ed12f9fd9071dcd3dc73ebff2e98a116c25667a8f8160cf8aeeaf0a437e6913e6870000082f49d00000000008b.

Definition bw6_761_params : CurveParams := {|
  prime_p          := bw6_761_modulus_lit;
  scalar_r         := 0x1ae3a4617c510eacf6b8b5b1c8e8e5c81d8e6c3eb2cb5c8df0e0e3a2bf3e2dd29c4f3eaa4ac0e1d9b1d4d4e9e2e8e9b;
                       (* placeholder — BW6-761 r equals the BLS12-377
                          prime; needs an exact import once the pairing
                          file exists *)

  curve_a          := 0;
  curve_b          := -1;       (* y^2 = x^3 - 1 *)

  embedding_degree := 6%nat;

  fp2_beta         := 0;        (* unused: BW6 has no Fp2 layer *)
  xi_re            := 0;
  xi_im            := 0;

  twist            := Mtwist;   (* M-type sextic twist *)

  loop_abs         := 0xd201000000010000;   (* placeholder: BLS12-377 seed *)
  loop_neg         := true;

  optimal_ate_extras := [];     (* BW6 actually needs *two* miller loops;
                                   not representable in this record *)
|}.

(* No [_wf] lemma for now: the placeholders above mean some fields are
   not actually correct. Mark this file as [Admitted]-equivalent until
   the BW6-761 pairing implementation lands. *)
