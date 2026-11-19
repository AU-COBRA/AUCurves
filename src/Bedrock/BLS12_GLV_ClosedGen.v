(** * BLS12_GLV_ClosedGen — the closed GLV theorem for multiples of the G1 generator.

    [g1_phi_gen]: phi(G) [pt_eq] [lambda] G for the standard generator G
    ([g1_gen], affine), lambda = [BLS12_Endomorphism.bls12_lambda] and
    omega = [glv_omega] = [BLS12_Endomorphism.bls12_omega_glv]
    (= bls12_omega^2 mod p; with [bls12_omega] itself phi is [lambda^2]).
    The check is a VM computation through the proved GLV loop
    ([BLS12_GLV_Eigen.glv_prog_single]), never by unfolding the unary
    [smul].
    [g1_order_gen]: [r] G [pt_eq] O, r = [bls12_r], from
    r = 1 + lambda + lambda^2 and G + phi(G) + phi^2(G) = O (a VM check,
    [sum3_check]) by [BLS12_GLV_Eigen.order_of_eigen].
    [g1_eigen]: every on-curve P [pt_eq] [m] G satisfies
    [lambda] P [pt_eq] phi(P)  (no point counting: phi is a homomorphism
    of the raw RCB formulas, [BLS12_GLV_Eigen.eigen_of_multiple]).
    [g1_glv_closed_gen]: [BLS12_GLV_Closed.g1_glv_closed_eigen] without
    the eigen premise, for P [pt_eq] [m] G (any m): the output is
    [k1 + lambda k2] P, and [k] P for every k = k1 + lambda k2 mod r. *)

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
Require Import Bedrock.Field.Synthesis.Examples.BLS12_ScalarReduce.
Require Bedrock.Field.Synthesis.Examples.BLS12_Endomorphism.
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
Require Import Bedrock.BLS12_GLV_Closed.
Require Import Bedrock.BLS12_GLV_Eigen.
Import ListNotations.
Local Open Scope Z_scope.

Section G1Eigen.
  Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep
    bls12_field_parameters_ok bls12_frep_ok.

  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation tb12 := (F.of_Z M_pos 12).
  Local Notation add12 := (ladderstep_triple tb12).
  Local Notation dbl12 := (rcb_double_a0_triple tb12).
  Local Notation smul12 := (BLS12_MSM_Functional.smul id_pt add12).
  Local Notation add_raw := (ladderstep_triple tb).
  Local Notation smul := (BLS12_MSM_Functional.smul id_pt add_raw).
  Local Notation eval2 x := (Positional.eval (uweight 64) 2 (List.map word.unsigned x)).
  Local Notation lam := BLS12_Endomorphism.bls12_lambda.

  Lemma Hthree_b12 : tb12 = (b4 + b4 + b4)%F.
  Proof. rewrite <- tb_eq. exact bls12_Hthree_b. Qed.

  Local Notation W f := (f bls12_M_gt_27 b4 tb12 Hthree_b12 bls12_Hdisc bls12_no_two_torsion).

  (** The standard G1 generator (affine). *)
  Definition g1_gen : F * F * F :=
    (F.of_Z M_pos 0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
     F.of_Z M_pos 0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1,
     F.of_Z M_pos 1).

  (** The cube root of unity paired with [bls12_lambda]. *)
  Definition glv_omega : F := F.of_Z M_pos BLS12_Endomorphism.bls12_omega_glv.

  Lemma glv_omega_cube : (glv_omega * glv_omega * glv_omega = 1)%F.
  Proof. apply F.eq_to_Z_iff. vm_compute. reflexivity. Qed.

  Lemma g1_gen_oncurve : bls12_oncurve g1_gen.
  Proof.
    cbv [bls12_oncurve RcbProjectiveLaws.oncurve g1_gen]. split.
    - apply F.eq_to_Z_iff. vm_compute. reflexivity.
    - intros H. apply (f_equal F.to_Z) in H. vm_compute in H. discriminate H.
  Qed.

  (** *** VM checks *)
  Lemma phi_gen_check :
    pt_eqb (glv_prog_output id_pt add12 dbl12 lam 0 g1_gen g1_gen)
           (phi glv_omega g1_gen) = true.
  Proof. vm_cast_no_check (eq_refl true). Qed.

  (** G + phi(G) + phi(phi(G)) = O: the three points of the curve on the line y = y_G. *)
  Lemma sum3_check :
    Z.eqb (F.to_Z (snd (add12 g1_gen
                     (add12 (phi glv_omega g1_gen) (phi glv_omega (phi glv_omega g1_gen))))))
          0 = true.
  Proof. vm_compute. reflexivity. Qed.

  Lemma r_eq : bls12_r = 1 + (lam + lam * lam).
  Proof. apply Z.eqb_eq. vm_compute. reflexivity. Qed.

  Lemma bound129 (k : Z) : ((0 <=? k) && (k <? 2 ^ 129))%bool = true -> 0 <= k < 2 ^ 129.
  Proof. rewrite Bool.andb_true_iff, Z.leb_le, Z.ltb_lt. tauto. Qed.

  Lemma lam_bound : 0 <= lam < 2 ^ 129.
  Proof. apply bound129. vm_compute. reflexivity. Qed.
  (** *** phi(G) = [lambda] G and r G = O *)
  Theorem g1_phi_gen : pt_eq (phi glv_omega g1_gen) (smul (Z.to_nat lam) g1_gen).
  Proof.
    rewrite tb_eq.
    pose proof (pt_eq_Equivalence bls12_M_gt_27 b4 tb12 Hthree_b12) as Eq.
    symmetry. etransitivity.
    - symmetry. exact ((W glv_prog_single) lam g1_gen g1_gen_oncurve lam_bound).
    - exact (pt_eqb_sound _ _ phi_gen_check).
  Qed.

  Local Notation L := (Z.to_nat lam).
  Local Notation w := glv_omega.
  Local Notation G := g1_gen.
  Local Notation oncurve := (RcbProjectiveLaws.oncurve 0%F b4).

  (** r G = O, from r = 1 + lambda + lambda^2 and G + phi G + phi^2 G = O. *)
  Theorem g1_order_gen : pt_eq (smul (Z.to_nat bls12_r) g1_gen) id_pt.
  Proof.
    rewrite tb_eq.
    assert (E : pt_eq (phi w G) (smul12 L G))
      by (pose proof g1_phi_gen as E; rewrite tb_eq in E; exact E).
    assert (Er : Z.to_nat bls12_r = (1 + (L + L * L))%nat).
    { rewrite r_eq, Z2Nat.inj_add, Z2Nat.inj_add, Z2Nat.inj_mul;
        [ reflexivity | apply Z.leb_le; vm_compute; reflexivity .. ]. }
    rewrite Er.
    exact ((W order_of_eigen) w L G glv_omega_cube g1_gen_oncurve E
             (pt_eq_id_of_z _ (proj1 (Z.eqb_eq _ _) sum3_check))).
  Qed.

  (** *** The eigen property on the multiples of G *)
  Theorem g1_eigen (m : nat) (P : F * F * F) :
    bls12_oncurve P -> pt_eq P (smul m g1_gen) ->
    pt_eq (smul (Z.to_nat lam) P) (phi glv_omega P).
  Proof.
    rewrite tb_eq. intros HP Ep.
    pose proof g1_phi_gen as E. rewrite tb_eq in E.
    exact ((W eigen_of_multiple) glv_omega (Z.to_nat lam) m g1_gen P glv_omega_cube
             g1_gen_oncurve HP E Ep).
  Qed.

  Theorem g1_order (m : nat) (P : F * F * F) :
    bls12_oncurve P -> pt_eq P (smul m g1_gen) ->
    pt_eq (smul (Z.to_nat bls12_r) P) id_pt.
  Proof.
    rewrite tb_eq. intros HP Ep.
    pose proof g1_order_gen as E. rewrite tb_eq in E.
    exact ((W order_of_multiple) (Z.to_nat bls12_r) m g1_gen P g1_gen_oncurve HP E Ep).
  Qed.

  (** ** The closed GLV theorem for multiples of the generator: no eigen premise. *)
  Theorem g1_glv_closed_gen (functions : Semantics.env) :
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
           (Outx Outy Outz Px Py Pz : F)
           (k1_words k2_words : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem)
           (mG : nat),
      length k1_words = 2%nat -> length k2_words = 2%nat ->
      bls12_oncurve (Px, Py, Pz) ->
      pt_eq (Px, Py, Pz) (smul mG g1_gen) ->
      (FElem (Some tight_bounds) pOutx Outx
       * FElem (Some tight_bounds) pOuty Outy
       * FElem (Some tight_bounds) pOutz Outz
       * FElem (Some tight_bounds) pPx Px
       * FElem (Some tight_bounds) pPy Py
       * FElem (Some tight_bounds) pPz Pz
       * FElem (Some tight_bounds) pPhix (glv_omega * Px)%F
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
                  (smul (Z.to_nat (eval2 k1_words) + Z.to_nat (eval2 k2_words) * Z.to_nat lam)%nat
                        (Px, Py, Pz))
            /\ (forall k : Z, 0 <= k ->
                  k mod bls12_r = (eval2 k1_words + eval2 k2_words * lam) mod bls12_r ->
                  pt_eq (ox, oy, oz) (smul (Z.to_nat k) (Px, Py, Pz)))
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
    intros pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
           Outx Outy Outz Px Py Pz k1_words k2_words R tr m mG
           Hl1 Hl2 HP Hm Hsep.
    pose proof (g1_eigen mG (Px, Py, Pz) HP Hm) as Heig.
    pose proof (g1_order mG (Px, Py, Pz) HP Hm) as Hord.
    eapply Semantics.weaken_call.
    { exact (g1_glv_closed_eigen functions glv_omega (Z.to_nat lam)
               Hg Hsh Hcm Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub Hz Ho glv_omega_cube
               pOutx pOuty pOutz pPx pPy pPz pPhix pPhiy pPhiz pk1 pk2
               Outx Outy Outz Px Py Pz k1_words k2_words R tr m Hl1 Hl2 HP Heig Hsep). }
    cbv beta. intros tr' m' rets (Hr & Htr & ox & oy & oz & Pxn & Pyn & Pzn
                                  & Phixn & Phiyn & Phizn & k1n & k2n & Hk & Hmod & Hsep').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists ox, oy, oz, Pxn, Pyn, Pzn, Phixn, Phiyn, Phizn, k1n, k2n.
    split; [ exact Hk | ]. split; [ | exact Hsep' ].
    intros k Hk0 Hkm.
    pose proof (eval2_bound k1_words Hl1) as B1.
    pose proof (eval2_bound k2_words Hl2) as B2.
    pose proof (proj1 lam_bound) as Bl.
    pose proof bls12_r_pos as Br.
    apply (Hmod (Z.to_nat bls12_r) (Z.to_nat k)); [ change 0%nat with (Z.to_nat 0); apply Z2Nat.inj_lt;
          [ apply Z.le_refl | apply Z.lt_le_incl, Br | exact Br ] | exact Hord | ].
    rewrite <- (Z2Nat.inj_mul (eval2 k2_words) lam) by (apply B2 || exact Bl).
    rewrite <- (Z2Nat.inj_add (eval2 k1_words) (eval2 k2_words * lam))
      by (apply B1 || (apply Z.mul_nonneg_nonneg; [ apply B2 | exact Bl ])).
    rewrite <- !Z2Nat.inj_mod
      by (exact Hk0 || apply Z.lt_le_incl, Br
          || (apply Z.add_nonneg_nonneg; [ apply B1 | apply Z.mul_nonneg_nonneg; [ apply B2 | exact Bl ] ])).
    rewrite Hkm. reflexivity.
  Qed.
End G1Eigen.
