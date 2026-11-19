(** * BLS12_GLV_Closed — the shipped BLS12-381 GLV Shamir loop computes k1 P + k2 Phi.

    Environment: the printed bodies ["bls12_glv_shamir"] ([BLS12_G1ArenaRust.g1_glv],
    i.e. [BLS12_GLV_ScalarMultBedrock.glv_shamir_func] with callees
    ["msm_curve_add"], ["msm_curve_double"], ["glv_cmov"]), ["shift_scalar"]
    (two words), ["glv_cmov"], and the G1 callees of [BLS12_MSM_Closed]
    (["msm_curve_add"], ["msm_curve_double"], ["curve_add"], ["curve_double_a0"],
    ["store_zero"], ["bls12_three_b"], ["bls12_felem_copy"]).  Premises: only the
    contracts of the field leaves (bls12_mul / add / sub, bls12_zero / one).

    [g1_glv_closed]: for P and Phi on y^2 z = x^3 + 4 z^3 and two-word scalars
    k1, k2 (any value < 2^128), the output is tight and [pt_eq] to
    [k1] P + [k2] Phi (RCB addition from (0 : 1 : 0)).
    [g1_glv_closed_eigen]: with Phi = (omega X, Y, Z) for omega^3 = 1 and
    Phi [pt_eq] [lambda] P, the output is [(k1 + lambda k2)] P; and if
    moreover [r] P is the identity, it is [k] P for every k = k1 + lambda k2 mod r.
    That phi = [lambda] holds is not proved here; for P a multiple of the
    standard generator it is proved in [BLS12_GLV_ClosedGen] ([g1_eigen],
    omega = [BLS12_Endomorphism.bls12_omega_glv] = bls12_omega^2 mod p), and
    [BLS12_GLV_ClosedGen.g1_glv_closed_gen] is this theorem without the eigen
    and order premises. *)

Require Import Rupicola.Lib.Api.
From Stdlib Require Import ZArith Lia List.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Synthesis.Generic.Bignum.
Require Import Crypto.Arithmetic.Partition.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Bedrock.Field.Synthesis.Examples.bls12_prime.
Require Import Bedrock.Field.Synthesis.Examples.bls12_three_b.
Require Import Bedrock.Field.Synthesis.Examples.bls12_felem_copy.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.PointDoubleA0.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.BLS12_G1ArenaRust.
Require Import Bedrock.BLS12_MSM_Wrappers.
Require Import Bedrock.BLS12_MSM_Closed.
Require Import Bedrock.BLS12_GLV_Prog.
Require Import Bedrock.BLS12_GLV_Functional.
Require Import Bedrock.BLS12_GLV_Callees.
Import ListNotations.
Local Open Scope Z_scope.

Section GlvClosed.
  Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep
    bls12_field_parameters_ok bls12_frep_ok.

  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation add_raw := (ladderstep_triple tb).
  Local Notation dbl_raw := (rcb_double_a0_triple tb).
  Local Notation smul := (BLS12_MSM_Functional.smul id_pt add_raw).
  Local Notation eval2 x := (Positional.eval (uweight 64) 2 (List.map word.unsigned x)).

  Lemma eval2_bound (x : list word) :
    length x = 2%nat -> 0 <= eval2 x < 2 ^ 128.
  Proof.
    intros Hx. destruct x as [|w0 [|w1 [|]]]; try discriminate Hx.
    pose proof (word.unsigned_range w0) as H0. pose proof (word.unsigned_range w1) as H1.
    cbn [List.map].
    rewrite Positional.eval_cons by reflexivity.
    rewrite uweight_eval_shift by (cbn; lia || reflexivity).
    rewrite Positional.eval_cons by reflexivity.
    rewrite uweight_eval_shift by (cbn; lia || reflexivity).
    rewrite Positional.eval0.
    rewrite uweight_0, uweight_1. change (2 ^ 64) with 18446744073709551616 in *.
    lia.
  Qed.

  (** The callee contracts of the GLV program, from the shipped bodies. *)
  Lemma glv_callees_ok (functions : Semantics.env) :
    map.get functions "shift_scalar" = Some (snd g1_shift_scalar2) ->
    map.get functions "glv_cmov" = Some (snd g1_glv_cmov) ->
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
    StoreZeroOK functions
    /\ BLS12_GLV_Prog.spec_of_shift_scalar functions
    /\ CmovInplaceOK "glv_cmov" functions
    /\ AddAliasedOK "msm_curve_add" add_raw functions
    /\ DoubleInplaceOK "msm_curve_double" dbl_raw functions.
  Proof.
    intros Hsh Hcm Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub Hz Ho.
    destruct (bls12_g1_callees_ok functions Hmca Hmcd Hca Hcd Hsz Htb Hcp
                Hmul Hadd Hsub Hz Ho) as (HA & HD & HZ).
    split; [ exact HZ | ].
    split; [ exact (shift_scalar2_ok functions Hsh) | ].
    split; [ exact (glv_cmov_ok functions Hcm (felem_copy_ok functions Hcp)) | ].
    split.
    - intros pXo pX2 pYo pY2 pZo pZ2 X Y Z X2 Y2 Z2 R0 tr0 m0 H.
      exact (HA pXo pX2 pYo pY2 pZo pZ2 X X2 Y Y2 Z Z2 R0 tr0 m0 H).
    - exact HD.
  Qed.

  (** The closed theorem: k1 P + k2 Phi up to pt_eq, for on-curve P, Phi. *)
  Theorem g1_glv_closed (functions : Semantics.env) :
    map.get functions "bls12_glv_shamir" = Some (snd g1_glv) ->
    map.get functions "shift_scalar" = Some (snd g1_shift_scalar2) ->
    map.get functions "glv_cmov" = Some (snd g1_glv_cmov) ->
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
    forall (pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2 : word)
           (Outx Outy Outz Px Py Pz Phix Phiy Phiz : F)
           (k1_words k2_words : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length k1_words = 2%nat -> length k2_words = 2%nat ->
      bls12_oncurve (Px, Py, Pz) -> bls12_oncurve (Phix, Phiy, Phiz) ->
      (FElem (Some tight_bounds) pOutx Outx
       * FElem (Some tight_bounds) pOuty Outy
       * FElem (Some tight_bounds) pOutz Outz
       * FElem (Some tight_bounds) pPx Px
       * FElem (Some tight_bounds) pPy Py
       * FElem (Some tight_bounds) pPz Pz
       * FElem (Some tight_bounds) pPhix Phix
       * FElem (Some tight_bounds) pPhiy Phiy
       * FElem (Some tight_bounds) pPhiz Phiz
       * Bignum 2 pk1 k1_words
       * Bignum 2 pk2 k2_words
       * R)%sep m ->
      Semantics.call functions "bls12_glv_shamir" tr m
        [pOutx; pOuty; pOutz; pPx; pPy; pPz; pPhix; pPhiy; pPhiz; pk1; pk2]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
          exists (ox oy oz Pxnew Pynew Pznew Phixnew Phiynew Phiznew : F)
                 (k1new k2new : list word),
            pt_eq (ox, oy, oz)
                  (add_raw (smul (Z.to_nat (eval2 k1_words)) (Px, Py, Pz))
                           (smul (Z.to_nat (eval2 k2_words)) (Phix, Phiy, Phiz)))
            /\ (FElem (Some tight_bounds) pOutx ox
                * FElem (Some tight_bounds) pOuty oy
                * FElem (Some tight_bounds) pOutz oz
                * FElem (Some tight_bounds) pPx Pxnew
                * FElem (Some tight_bounds) pPy Pynew
                * FElem (Some tight_bounds) pPz Pznew
                * FElem (Some tight_bounds) pPhix Phixnew
                * FElem (Some tight_bounds) pPhiy Phiynew
                * FElem (Some tight_bounds) pPhiz Phiznew
                * Bignum 2 pk1 k1new
                * Bignum 2 pk2 k2new
                * R)%sep m').
  Proof.
    intros Hg Hsh Hcm Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub Hz Ho.
    destruct (glv_callees_ok functions Hsh Hcm Hmca Hmcd Hca Hcd Hsz Htb Hcp
                Hmul Hadd Hsub Hz Ho) as (HZ & HS & HC & HA & HD).
    pose proof (@glv_prog_ok _ _ _ _ _ _ _ _ _ _ _ _ _
                  "msm_curve_add" "msm_curve_double" "glv_cmov" add_raw dbl_raw
                  functions Hg HZ HS HC HA HD) as Hspec.
    intros pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
           Outx Outy Outz Px Py Pz Phix Phiy Phiz k1_words k2_words R tr m
           Hl1 Hl2 HP HPhi Hsep.
    pose proof (eval2_bound k1_words Hl1) as Hb1.
    pose proof (eval2_bound k2_words Hl2) as Hb2.
    assert (H128 : 2 ^ 128 < 2 ^ 129) by (vm_compute; reflexivity).
    eapply Semantics.weaken_call.
    { eapply Hspec;
      [ split; [ exact (proj1 Hb1) | eapply Z.lt_trans; [ exact (proj2 Hb1) | exact H128 ] ]
      | split; [ exact (proj1 Hb2) | eapply Z.lt_trans; [ exact (proj2 Hb2) | exact H128 ] ]
      | ].
      change CompilationAbstract.FElem with Compilation2.FElem. exact Hsep. }
    cbv beta. intros tr' m' rets (Hr & Htr & ox & oy & oz & Pxn & Pyn & Pzn
                                  & Phixn & Phiyn & Phizn & k1n & k2n & Hres & Hsep').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists ox, oy, oz, Pxn, Pyn, Pzn, Phixn, Phiyn, Phizn, k1n, k2n.
    split; [ | change CompilationAbstract.FElem with Compilation2.FElem in Hsep'; exact Hsep' ].
    rewrite Hres.
    change (F.of_Z M_pos 0, F.of_Z M_pos 1, F.of_Z M_pos 0) with (@id_pt bls12_field_parameters).
    apply (glv_prog_rcb_correct bls12_M_gt_27 b4 tb bls12_Hthree_b bls12_Hdisc
             bls12_no_two_torsion); [ exact HP | exact HPhi | | ].
    - split; [ exact (proj1 Hb1) | eapply Z.lt_trans; [ exact (proj2 Hb1) | exact H128 ] ].
    - split; [ exact (proj1 Hb2) | eapply Z.lt_trans; [ exact (proj2 Hb2) | exact H128 ] ].
  Qed.

  (** With the endomorphism: Phi = (omega X, Y, Z), omega^3 = 1, Phi = [lambda] P. *)
  Theorem g1_glv_closed_eigen (functions : Semantics.env) (omega : F) (lam : nat) :
    map.get functions "bls12_glv_shamir" = Some (snd g1_glv) ->
    map.get functions "shift_scalar" = Some (snd g1_shift_scalar2) ->
    map.get functions "glv_cmov" = Some (snd g1_glv_cmov) ->
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
    (omega * omega * omega = 1)%F ->
    forall (pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2 : word)
           (Outx Outy Outz Px Py Pz : F)
           (k1_words k2_words : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length k1_words = 2%nat -> length k2_words = 2%nat ->
      bls12_oncurve (Px, Py, Pz) ->
      pt_eq (smul lam (Px, Py, Pz)) ((omega * Px)%F, Py, Pz) ->
      (FElem (Some tight_bounds) pOutx Outx
       * FElem (Some tight_bounds) pOuty Outy
       * FElem (Some tight_bounds) pOutz Outz
       * FElem (Some tight_bounds) pPx Px
       * FElem (Some tight_bounds) pPy Py
       * FElem (Some tight_bounds) pPz Pz
       * FElem (Some tight_bounds) pPhix (omega * Px)%F
       * FElem (Some tight_bounds) pPhiy Py
       * FElem (Some tight_bounds) pPhiz Pz
       * Bignum 2 pk1 k1_words
       * Bignum 2 pk2 k2_words
       * R)%sep m ->
      Semantics.call functions "bls12_glv_shamir" tr m
        [pOutx; pOuty; pOutz; pPx; pPy; pPz; pPhix; pPhiy; pPhiz; pk1; pk2]
        (fun tr' m' rets => rets = [] /\ tr = tr' /\
          exists (ox oy oz Pxnew Pynew Pznew Phixnew Phiynew Phiznew : F)
                 (k1new k2new : list word),
            pt_eq (ox, oy, oz)
                  (smul (Z.to_nat (eval2 k1_words) + Z.to_nat (eval2 k2_words) * lam)%nat
                        (Px, Py, Pz))
            /\ (forall (r k : nat), (0 < r)%nat ->
                  pt_eq (smul r (Px, Py, Pz)) id_pt ->
                  (k mod r = (Z.to_nat (eval2 k1_words) + Z.to_nat (eval2 k2_words) * lam)
                             mod r)%nat ->
                  pt_eq (ox, oy, oz) (smul k (Px, Py, Pz)))
            /\ (FElem (Some tight_bounds) pOutx ox
                * FElem (Some tight_bounds) pOuty oy
                * FElem (Some tight_bounds) pOutz oz
                * FElem (Some tight_bounds) pPx Pxnew
                * FElem (Some tight_bounds) pPy Pynew
                * FElem (Some tight_bounds) pPz Pznew
                * FElem (Some tight_bounds) pPhix Phixnew
                * FElem (Some tight_bounds) pPhiy Phiynew
                * FElem (Some tight_bounds) pPhiz Phiznew
                * Bignum 2 pk1 k1new
                * Bignum 2 pk2 k2new
                * R)%sep m').
  Proof.
    intros Hg Hsh Hcm Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub Hz Ho Hw.
    intros pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
           Outx Outy Outz Px Py Pz k1_words k2_words R tr m
           Hl1 Hl2 HP Heig Hsep.
    pose proof (oncurve_phi b4 omega (Px, Py, Pz) Hw HP) as HPhi. cbv beta iota in HPhi.
    pose proof (pt_eq_Equivalence bls12_M_gt_27 b4 tb bls12_Hthree_b) as Eq.
    eapply Semantics.weaken_call.
    { exact (g1_glv_closed functions Hg Hsh Hcm Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub
               Hz Ho pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
               Outx Outy Outz Px Py Pz (omega * Px)%F Py Pz k1_words k2_words R tr m
               Hl1 Hl2 HP HPhi Hsep). }
    cbv beta. intros tr' m' rets (Hr & Htr & ox & oy & oz & Pxn & Pyn & Pzn
                                  & Phixn & Phiyn & Phizn & k1n & k2n & Hres & Hsep').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists ox, oy, oz, Pxn, Pyn, Pzn, Phixn, Phiyn, Phizn, k1n, k2n.
    assert (Hk : pt_eq (ox, oy, oz)
                   (smul (Z.to_nat (eval2 k1_words) + Z.to_nat (eval2 k2_words) * lam)%nat
                         (Px, Py, Pz))).
    { etransitivity; [ exact Hres | ].
      exact (glv_eigen bls12_M_gt_27 b4 tb bls12_Hthree_b bls12_Hdisc bls12_no_two_torsion
               lam _ _ (Px, Py, Pz) _ HP HPhi Heig). }
    split; [ exact Hk | ]. split; [ | exact Hsep' ].
    intros r k Hr0 Hord Hkmod.
    etransitivity; [ exact Hk | ].
    etransitivity.
    { exact (smul_mod_order bls12_M_gt_27 b4 tb bls12_Hthree_b bls12_Hdisc bls12_no_two_torsion
               r _ (Px, Py, Pz) HP Hr0 Hord). }
    rewrite <- Hkmod. symmetry.
    exact (smul_mod_order bls12_M_gt_27 b4 tb bls12_Hthree_b bls12_Hdisc bls12_no_two_torsion
             r k (Px, Py, Pz) HP Hr0 Hord).
  Qed.
End GlvClosed.
