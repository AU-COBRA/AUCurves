(** * BLS12_MSM_Closed — the shipped BLS12-381 G1 MSM computes sum k_i P_i.

    The functions are those of [BLS12_G1ArenaRust.bls12_g1_funcs], which
    [scripts/emit_bls12_g1_rust.sh] prints as
    [bls12-381-safe-rust/src/g1_msm_extracted.rs]:
    ["msm_bls12"], ["msm_curve_add"], ["msm_curve_double"], ["curve_add"],
    ["curve_double_a0"], ["store_zero"], ["bls12_three_b"],
    ["bls12_felem_copy"].  [msm_bls12_closed] assumes an environment that
    contains exactly these bodies, plus contracts for the field leaves
    that the Rust runtime supplies and that are not printed: fiat-crypto's
    [spec_of_BinOp] for ["bls12_mul"] / ["bls12_add"] / ["bls12_sub"],
    and [spec_of_store_const] for ["bls12_zero"] / ["bls12_one"].

    Conclusion: on [n] points that satisfy the curve equation
    y^2 z = x^3 + 4 z^3 (homogeneous, not (0:0:0)) and [n] scalars of
    four 64-bit limbs, [msm_bls12] terminates, preserves the inputs and
    returns a tight triple [pt_eq] (projectively equal) to
    [sum_i k_i P_i], where [k_i] is the 256-bit integer of the limbs
    (not reduced mod r) and the sum is formed with the same complete
    RCB addition from (0 : 1 : 0).  By [RcbProjectiveLaws] that addition
    is fiat-crypto's [Projective.add], i.e. the affine group law.

    The one curve fact needed (no F-rational point of order 2) is
    proved here by the cubic-residue criterion: (-4)^((p-1)/3) <> 1. *)

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
Require Import Bedrock.BLS12_MSM.
Require Import Bedrock.BLS12_MSM_Functional.
Require Import Bedrock.BLS12_MSM_Wrappers.
Require Import Bedrock.BLS12_G1ArenaRust.
Require Import Bedrock.BLS12_G1_ScalarMul.
Import ListNotations.
Local Open Scope Z_scope.

Section Closed.
  Existing Instances Bitwidth64.BW64 bls12_field_parameters bls12_frep
    bls12_field_parameters_ok bls12_frep_ok.

  Local Notation F := (F M_pos).
  Local Notation FElem := (Compilation2.FElem).

  #[local] Instance prime_bls12_M : Znumtheory.prime (Z.pos M_pos) := M_prime.

  Add Ring Fp_ring_closed : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  Lemma bls12_bounds_eq : @loose_bounds _ _ _ _ _ bls12_frep = tight_bounds.
  Proof. reflexivity. Qed.

  Definition tb : F := feval (proj1_sig three_b_felem).
  Definition b4 : F := F.of_Z M_pos 4.

  Lemma tb_eq : tb = F.of_Z M_pos 12.
  Proof. exact feval_three_b_words. Qed.

  Lemma bls12_M_gt_27 : (27 < M_pos)%positive.
  Proof. vm_compute. reflexivity. Qed.

  Lemma bls12_Hthree_b : tb = (b4 + b4 + b4)%F.
  Proof.
    rewrite tb_eq. apply F.eq_to_Z_iff. vm_compute. reflexivity.
  Qed.

  Lemma bls12_Hdisc : id
    ((((1 + 1 + 1 + 1) * 0 * 0 * 0
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b4 * b4) <> 0)%F).
  Proof.
    cbv [id]. intros H. apply (f_equal F.to_Z) in H. vm_compute in H. discriminate H.
  Qed.

  (** No point of order two: x^3 + 4 has no root mod p.  If x^3 = -4
      then x <> 0 and (-4)^((p-1)/3) = x^(p-1) = 1 (Fermat), but the
      left side computes to a value other than 1. *)
  Definition k3 : N := Z.to_N ((Z.pos M_pos - 1) / 3).

  (** Checked by [vm_compute] on the goal, so that the kernel replays
      it with the VM (about 7 s); the same check run on a hypothesis is
      re-done by the kernel's default conversion (measured: 159 s). *)
  Lemma minus4_not_cube_b : Z.eqb (F.to_Z (F.pow (F.opp b4) k3)) 1 = false.
  Proof. vm_compute. reflexivity. Qed.

  Lemma minus4_not_cube : (F.pow (F.opp b4) k3 <> 1)%F.
  Proof.
    intros H. pose proof minus4_not_cube_b as Hb. rewrite H in Hb.
    vm_compute in Hb. discriminate Hb.
  Qed.

  Lemma bls12_no_two_torsion : no_two_torsion 0%F b4.
  Proof.
    cbv [no_two_torsion]. intros x Hx.
    assert (Hx3 : (x * x * x = F.opp b4)%F).
    { assert (E : (x * x * x = (x * x * x + 0 * x + b4) - b4)%F) by ring.
      rewrite Hx in E. rewrite E. ring. }
    assert (Hx0 : x <> 0%F).
    { intros ->. apply (f_equal F.to_Z) in Hx. vm_compute in Hx. discriminate Hx. }
    apply minus4_not_cube.
    rewrite <- Hx3, <- F.pow_3_r, F.pow_pow_l.
    assert (Hexp : (3 * k3 = N.pred (Z.to_N (Z.pos M_pos)))%N) by (vm_compute; reflexivity).
    rewrite Hexp.
    assert (H2q : 2 < Z.pos M_pos) by (vm_compute; reflexivity).
    pose proof (@F.Fq_inv_fermat M_pos M_prime H2q x) as Hinv.
    replace (N.pred (Z.to_N (Z.pos M_pos))) with (N.succ (Z.to_N (Z.pos M_pos - 2)))
      by (vm_compute; reflexivity).
    rewrite F.pow_succ_r, <- Hinv.
    apply (@Field.right_multiplicative_inverse _ _ _ _ _ _ _ _ _ _ (F.field_modulo M_pos)). exact Hx0.
  Qed.

  (** ** Leaf contract adapters *)

  (** [bls12_three_b_ok] (felem layer) gives the loader contract the
      re-derived addition/doubling bodies call. *)
  Lemma three_b_loader_ok (functions : Semantics.env) :
    spec_of_bls12_three_b functions ->
    spec_of_three_b_loader_anyout three_b_felem "bls12_three_b" functions.
  Proof.
    intros Hspec. cbv [spec_of_three_b_loader_anyout].
    change CompilationAbstract.FElem with Compilation2.FElem.
    intros pout outold Rout tr m Hm.
    destruct (NistWnafWrappers.FElem2_elim_frame _ _ _ _ _ Hm) as (x & _ & _ & Hx).
    eapply Semantics.weaken_call; [ exact (Hspec pout x Rout tr m Hx) | ].
    intros tr' m' rets (Hr & out & Hfe & Htr & Hbd & Hm').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    apply (NistWnafWrappers.FElem2_intro_frame _ pout out); [ | exact Hbd | exact Hm' ].
    rewrite Hfe. symmetry. exact tb_eq.
  Qed.

  (** ** The scalars as integers *)

  Definition scalar_value (s : list word) : nat :=
    match List.map word.unsigned s with
    | [l0; l1; l2; l3] => Z.to_nat (limbsZ l0 l1 l2 l3)
    | _ => O
    end.

  Local Notation add_raw := (ladderstep_triple tb).
  Local Notation dbl_raw := (rcb_double_a0_triple tb).

  (** [sum_i k_i P_i], with [k P] = P + ... + P (k times) and the sum
      formed with the complete RCB addition from (0 : 1 : 0). *)
  Definition msm_sum (ks : list nat) (ps : list (F * F * F)) : F * F * F :=
    gsum id_pt add_raw
      (List.map (fun kp => smul id_pt add_raw (fst kp) (snd kp)) (combine ks ps)).

  Lemma msm_ref_value (scalars : list (list word)) (ps : list (F * F * F)) :
    Forall (fun s => length s = 4%nat) scalars ->
    msm_ref id_pt add_raw 9 29 (scalars_to_Z scalars) ps
    = msm_sum (List.map scalar_value scalars) ps.
  Proof.
    unfold msm_ref, msm_sum, scalars_to_Z.
    intros Hall. revert ps.
    induction Hall as [|s ss Hs Hss IH]; intros [|p ps]; try reflexivity.
    cbn [List.map combine fst snd gsum fold_right] in *.
    specialize (IH ps). unfold gsum in IH. rewrite IH. f_equal. f_equal.
    destruct s as [|w0 [|w1 [|w2 [|w3 [|]]]]]; try discriminate Hs.
    cbn [scalar_to_Z scalar_value List.map].
    pose proof (word.unsigned_range w0). pose proof (word.unsigned_range w1).
    pose proof (word.unsigned_range w2). pose proof (word.unsigned_range w3).
    apply wval_limbs; assumption.
  Qed.

  Definition bls12_oncurve : F * F * F -> Prop := RcbProjectiveLaws.oncurve 0%F b4.

  (** ** The callee contracts of the shipped functions

      From the bodies of [bls12_g1_funcs] and the field-leaf contracts:
      the copy-out wrappers satisfy [CurveAddAliasedOK] /
      [CurveDoubleInplaceOK] for the RCB formulas, and ["store_zero"]
      satisfies [StoreZero3OK] for (0 : 1 : 0). *)
  Lemma bls12_g1_callees_ok (functions : Semantics.env) :
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
    CurveAddAliasedOK "msm_curve_add" add_raw functions
    /\ CurveDoubleInplaceOK "msm_curve_double" dbl_raw functions
    /\ StoreZero3OK "store_zero" (F.of_Z M_pos 0, F.of_Z M_pos 1, F.of_Z M_pos 0) functions.
  Proof.
    intros Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub Hz Ho.
    pose proof (felem_copy_ok functions Hcp) as Hcopy.
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
    assert (HdblS : spec_of_rcb_double_a0_anyout three_b_felem functions).
    { eapply rcb_double_a0_anyout_derived.
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
      all: rewrite rcb_double_a0_body_anyout_eq; exact Hcd. }
    split; [ exact (copy_out_add_ok three_b_felem functions Hmca HaddS Hcopy) | ].
    split; [ exact (copy_out_double_ok three_b_felem functions Hmcd HdblS Hcopy) | ].
    exact (store_zero_ok3 "bls12_zero" "bls12_one" functions Hsz Hz Ho).
  Qed.

  (** ** The closed theorem *)

  Theorem msm_bls12_closed (functions : Semantics.env) :
    map.get functions "msm_bls12" = Some (snd g1_msm) ->
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
    forall (outx outy outz scalars_p ppx ppy ppz n_w : word)
           (outx0 outy0 outz0 : F) (scalars : list (list word))
           (px py pz : list F) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      word.unsigned n_w = Z.of_nat (length scalars) ->
      length scalars = length px ->
      length px = length py ->
      length py = length pz ->
      Forall (fun s => length s = 4%nat) scalars ->
      Forall bls12_oncurve (points_of px py pz) ->
      (FElem None outx outx0 * FElem None outy outy0 * FElem None outz outz0
       * ScalarsArray scalars_p scalars
       * G1Array3 ppx ppy ppz px py pz * R)%sep m ->
      Semantics.call functions "msm_bls12" tr m
        [outx; outy; outz; scalars_p; ppx; ppy; ppz; n_w]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz : F,
             pt_eq (ox, oy, oz)
                   (msm_sum (List.map scalar_value scalars) (points_of px py pz))
             /\ (FElem (Some tight_bounds) outx ox
                 * FElem (Some tight_bounds) outy oy
                 * FElem (Some tight_bounds) outz oz
                 * ScalarsArray scalars_p scalars
                 * G1Array3 ppx ppy ppz px py pz * R)%sep m').
  Proof.
    intros Hmsm Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub Hz Ho.
    destruct (bls12_g1_callees_ok functions Hmca Hmcd Hca Hcd Hsz Htb Hcp
                Hmul Hadd Hsub Hz Ho) as (HA & HD & HZ).
    pose proof (msm_bls12_prog_ok eq_refl "msm_curve_add" "msm_curve_double" "store_zero"
                  _ _ _ functions Hmsm HA HD HZ) as Hspec.
    cbv [spec_of_msm_bls12_prog] in Hspec.
    intros outx outy outz scalars_p ppx ppy ppz n_w outx0 outy0 outz0 scalars px py pz R tr m
           Hn Hl1 Hl2 Hl3 H4 Hon Hsep.
    eapply Semantics.weaken_call.
    { exact (Hspec outx outy outz scalars_p ppx ppy ppz n_w outx0 outy0 outz0
                   scalars px py pz R tr m (conj Hn (conj Hl1 (conj Hl2 (conj Hl3 Hsep))))). }
    cbv beta. intros tr' m' rets (Hr & Htr & ox & oy & oz & Hpt & Hsep').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists ox, oy, oz. split; [ | exact Hsep' ].
    change (ox, oy, oz) with (mk_point ox oy oz). rewrite Hpt.
    rewrite <- msm_ref_value by exact H4.
    exact (msm_prog_rcb_correct bls12_M_gt_27 b4 tb bls12_Hthree_b bls12_Hdisc
             bls12_no_two_torsion 9 29 (scalars_to_Z scalars) (points_of px py pz) Hon).
  Qed.
  (** ** Scalar multiplication *)

  Lemma scalar_value_bits (s : list word) :
    length s = 4%nat ->
    scalar_value s = low_bits (List.map word.unsigned s) 256.
  Proof.
    intros Hs.
    destruct s as [|w0 [|w1 [|w2 [|w3 [|]]]]]; try discriminate Hs.
    cbn [scalar_value List.map].
    pose proof (word.unsigned_range w0). pose proof (word.unsigned_range w1).
    pose proof (word.unsigned_range w2). pose proof (word.unsigned_range w3).
    symmetry. apply bits_limbs; assumption.
  Qed.

  (** [g1_scalar_mul] (double-and-add over the copy-out wrappers) returns
      a tight triple projectively equal to [k P], [k] the 256-bit integer
      of the four scalar limbs, for any point P on y^2 z = x^3 + 4 z^3. *)
  Theorem g1_scalar_mul_closed (functions : Semantics.env) :
    map.get functions "g1_scalar_mul" = Some (snd g1_smul) ->
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
    forall (outx outy outz sp px py pz : word) (outx0 outy0 outz0 X Y Z : F)
           (s : list word) (R : mem -> Prop) (tr : Semantics.trace) (m : mem),
      length s = 4%nat ->
      bls12_oncurve (X, Y, Z) ->
      (FElem None outx outx0 * FElem None outy outy0 * FElem None outz outz0
       * ScalarsArray sp [s]
       * FElem (Some tight_bounds) px X * FElem (Some tight_bounds) py Y
       * FElem (Some tight_bounds) pz Z * R)%sep m ->
      Semantics.call functions "g1_scalar_mul" tr m [outx; outy; outz; sp; px; py; pz]
        (fun tr' m' rets =>
           rets = [] /\ tr = tr' /\
           exists ox oy oz : F,
             pt_eq (ox, oy, oz) (smul id_pt add_raw (scalar_value s) (X, Y, Z))
             /\ (FElem (Some tight_bounds) outx ox
                 * FElem (Some tight_bounds) outy oy
                 * FElem (Some tight_bounds) outz oz
                 * ScalarsArray sp [s]
                 * FElem (Some tight_bounds) px X * FElem (Some tight_bounds) py Y
                 * FElem (Some tight_bounds) pz Z * R)%sep m').
  Proof.
    intros Hsm Hmca Hmcd Hca Hcd Hsz Htb Hcp Hmul Hadd Hsub Hz Ho.
    destruct (bls12_g1_callees_ok functions Hmca Hmcd Hca Hcd Hsz Htb Hcp
                Hmul Hadd Hsub Hz Ho) as (HA & HD & HZ).
    pose proof (g1_scalar_mul_ok eq_refl "msm_curve_add" "msm_curve_double" "store_zero"
                  _ _ _ functions Hsm HA HD HZ) as Hspec.
    intros outx outy outz sp px py pz outx0 outy0 outz0 X Y Z s R tr m Hlen Hon Hsep.
    eapply Semantics.weaken_call.
    { exact (Hspec outx outy outz sp px py pz outx0 outy0 outz0 X Y Z s R tr m Hlen Hsep). }
    cbv beta. intros tr' m' rets (Hr & Htr & ox & oy & oz & Hres & Hsep').
    split; [ exact Hr | ]. split; [ exact Htr | ].
    exists ox, oy, oz. split; [ | exact Hsep' ].
    rewrite Hres. unfold smul_target.
    rewrite (scalar_value_bits s Hlen).
    change (F.of_Z M_pos 0, F.of_Z M_pos 1, F.of_Z M_pos 0) with (@id_pt bls12_field_parameters).
    exact (smul_prog_rcb_correct bls12_M_gt_27 b4 tb bls12_Hthree_b bls12_Hdisc
             bls12_no_two_torsion (List.map word.unsigned s) (X, Y, Z) Hon).
  Qed.
End Closed.
