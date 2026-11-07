(** * BLS12_G1_CT_Closed — the shipped constant-time G1 scalar multiplication computes k P.

    [g1_scalar_mul_ct_closed]: in an environment holding the printed
    bodies of [BLS12_G1ArenaRust.bls12_g1_funcs] that it calls
    (["g1_scalar_mul_ct"], ["curve_add"], ["msm_curve_double"],
    ["curve_double_a0"], ["store_zero"], ["bls12_three_b"],
    ["bls12_felem_copy"], ["ct_cswap"]) and with only the field-leaf
    contracts as premises (the same as [BLS12_MSM_Closed.g1_scalar_mul_closed]),
    for a point P on y^2 z = x^3 + 4 z^3 with tight coordinates and four
    scalar limbs, ["g1_scalar_mul_ct"] returns a tight triple [pt_eq] to
    [k P], [k] the 256-bit integer of the limbs (not reduced mod r).  The
    three scratch buffers are left holding arbitrary field elements.

    No Admitted, no Axiom. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith Lia List.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_three_b.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.CurveAdd.RcbAnyOut.
Require Import Bedrock.Group.CurveAdd.CtSwap.
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.BLS12_MSM_Wrappers.
Require Import Bedrock.BLS12_G1ArenaRust.
Require Import Bedrock.BLS12_G1_ScalarMul.
Require Import Bedrock.BLS12_G1_ScalarMulCT.
Require Import Bedrock.BLS12_MSM_Closed.
Import ListNotations.
Local Open Scope Z_scope.

Section Closed.
  Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep
    bls12_field_parameters_ok bls12_frep_ok.

  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation add_raw := (ladderstep_triple tb).
  Local Notation dbl_raw := (rcb_double_a0_triple tb).

  Lemma bls12_n_small : Z.of_nat (@felem_size_in_words _ _ _ _ _ bls12_frep) < 2 ^ 64.
  Proof. vm_compute. reflexivity. Qed.

  (** The out-of-place addition ["curve_add"] (any output buffers). *)
  Lemma bls12_curve_add_out_ok (functions : Semantics.env) :
    map.get functions "curve_add" = Some (snd g1_curve_add) ->
    map.get functions "bls12_three_b" = Some (snd g1_three_b) ->
    spec_of_BinOp bin_mul functions ->
    spec_of_BinOp bin_add functions ->
    spec_of_BinOp bin_sub functions ->
    CurveAddOutOK "curve_add" add_raw functions.
  Proof.
    intros Hca Htb Hmul Hadd Hsub.
    pose proof (three_b_loader_ok functions (bls12_three_b_ok functions Htb)) as Hload.
    assert (HaddS : spec_of_ladderstep_anyout three_b_felem functions).
    { eapply ladderstep_anyout_derived.
      all: lazymatch goal with
           | |- @loose_bounds _ _ _ _ _ _ = _ => exact bls12_bounds_eq
           | |- __rupicola_program_marker _ => exact I
           | |- spec_of_BinOp bin_mul _ => exact Hmul
           | |- spec_of_BinOp bin_add _ => exact Hadd
           | |- spec_of_BinOp bin_sub _ => exact Hsub
           | |- spec_of_three_b_loader_anyout _ _ _ => exact Hload
           | |- map.get _ _ = _ => idtac
           | |- ?g => idtac "UNEXPECTED" g
           end.
      all: rewrite ladderstep_body_anyout_eq; exact Hca. }
    cbv [spec_of_ladderstep_anyout] in HaddS.
    intros pX1 pX2 pY1 pY2 pZ1 pZ2 pXo pYo pZo X1 X2 Y1 Y2 Z1 Z2 Xo0 Yo0 Zo0 R tr m Hm.
    eapply Semantics.weaken_call.
    { exact (HaddS pX1 pX2 pY1 pY2 pZ1 pZ2 pXo pYo pZo X1 X2 Y1 Y2 Z1 Z2 Xo0 Yo0 Zo0 R tr m Hm). }
    cbv beta. intros tr' m' rets (Hr & Htr & Xo & Yo & Zo & Hgal & Hm').
    split; [exact Hr|]. split; [exact Htr|].
    cbv [ladderstep_triple tb] in *.
    match goal with |- context [P2.car (P2.cdr ?L)] =>
      assert (HL : L = \<Xo, Yo, Zo\>) by exact Hgal; rewrite HL end.
    cbn [P2.car P2.cdr]. exact Hm'.
  Qed.

  Theorem g1_scalar_mul_ct_closed (functions : Semantics.env) :
    map.get functions "g1_scalar_mul_ct" = Some (snd g1_smul_ct) ->
    map.get functions "ct_cswap" = Some (snd g1_ct_cswap) ->
    map.get functions "msm_curve_add" = Some (snd BLS12_G1ArenaRust.msm_curve_add) ->
    map.get functions "msm_curve_double" = Some (snd BLS12_G1ArenaRust.msm_curve_double) ->
    map.get functions "curve_add" = Some (snd g1_curve_add) ->
    map.get functions "curve_double_a0" = Some (snd g1_curve_double_a0) ->
    map.get functions "store_zero" = Some (snd g1_store_zero) ->
    map.get functions "bls12_three_b" = Some (snd g1_three_b) ->
    map.get functions "bls12_felem_copy" = Some (snd g1_felem_copy) ->
    spec_of_BinOp bin_mul functions ->
    spec_of_BinOp bin_add functions ->
    spec_of_BinOp bin_sub functions ->
    spec_of_store_const "bls12_zero" (F.of_Z M_pos 0) functions ->
    spec_of_store_const "bls12_one" (F.of_Z M_pos 1) functions ->
    forall (outx outy outz tx ty tz sp px py pz : word)
           (outx0 outy0 outz0 tx0 ty0 tz0 X Y Z : F)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      bls12_oncurve (X, Y, Z) ->
      (FElem None outx outx0 * FElem None outy outy0 * FElem None outz outz0
       * FElem None tx tx0 * FElem None ty ty0 * FElem None tz tz0
       * ScalarsArray sp [s]
       * FElem (Some tight_bounds) px X * FElem (Some tight_bounds) py Y
       * FElem (Some tight_bounds) pz Z * R)%sep m ->
      Semantics.call functions "g1_scalar_mul_ct" tr m
        [outx; outy; outz; tx; ty; tz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz tx1 ty1 tz1 : F,
             pt_eq (ox, oy, oz) (smul id_pt add_raw (scalar_value s) (X, Y, Z))
             /\ (FElem (Some tight_bounds) outx ox
                 * FElem (Some tight_bounds) outy oy
                 * FElem (Some tight_bounds) outz oz
                 * FElem None tx tx1 * FElem None ty ty1 * FElem None tz tz1
                 * ScalarsArray sp [s]
                 * FElem (Some tight_bounds) px X * FElem (Some tight_bounds) py Y
                 * FElem (Some tight_bounds) pz Z * R)%sep m').
  Proof.
    intros Hsm Hsw Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub Hz Ho.
    destruct (bls12_g1_callees_ok functions Hmca Hmcd Hca Hcd Hsz Htb Hcp
                Hmul Hadd Hsub Hz Ho) as (_ & HD & HZ).
    assert (HC : CtCallees "curve_add" "msm_curve_double" "store_zero"
                   add_raw dbl_raw (F.of_Z M_pos 0, F.of_Z M_pos 1, F.of_Z M_pos 0) functions).
    { constructor.
      - exact (bls12_curve_add_out_ok functions Hca Htb Hmul Hadd Hsub).
      - exact HD.
      - exact HZ.
      - exact Hsw. }
    pose proof (g1_scalar_mul_ct_ok eq_refl bls12_n_small "curve_add" "msm_curve_double" "store_zero"
                  _ _ _ functions Hsm HC) as Hspec.
    intros outx outy outz tx ty tz sp px py pz outx0 outy0 outz0 tx0 ty0 tz0 X Y Z s R tr m
           Hlen Hon Hsep.
    eapply Semantics.weaken_call.
    { exact (Hspec outx outy outz tx ty tz sp px py pz outx0 outy0 outz0 tx0 ty0 tz0
                   X Y Z s R tr m Hlen Hsep). }
    cbv beta. intros tr' m' rets (Hr & Htr & ox & oy & oz & tx1 & ty1 & tz1 & Hres & Hsep').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists ox, oy, oz, tx1, ty1, tz1. split; [ | exact Hsep' ].
    rewrite Hres. unfold smul_target.
    rewrite (scalar_value_bits s Hlen).
    change (F.of_Z M_pos 0, F.of_Z M_pos 1, F.of_Z M_pos 0) with (@id_pt bls12_field_parameters).
    exact (smul_prog_rcb_correct bls12_M_gt_27 b4 tb bls12_Hthree_b bls12_Hdisc
             bls12_no_two_torsion (List.map word.unsigned s) (X, Y, Z) Hon).
  Qed.
End Closed.
