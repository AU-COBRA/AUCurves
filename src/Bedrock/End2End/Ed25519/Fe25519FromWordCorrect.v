(** * Fe25519FromWordCorrect — functional correctness of
 *  [fe25519_from_word_body].
 *
 *  Companion to [Fe25519FromWordBody.v].  Mirrors the section-
 *  parameterised pattern from [Fe25519AddSubCorrect.v]: abstract over
 *  the [Fp25519_holds] slot predicate plus a limb-level decoder
 *  hypothesis that the canonical [w, 0, 0, 0, 0] limb list decodes to
 *  [F.of_Z w].
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_from_word_body_correct] : Qed, via Lemma
 *    [from_word_inline_correct] discharged mechanically against the
 *    limb-level hypotheses ([Fp25519_holds_intro] /
 *     [Fp25519_holds_set_other] / [feval_limbwise_from_word_mask64]).
 *    Five [rexec_limb_store_fp25519] inversions threaded through the
 *    abstract limb decoder; only [Fp25519_holds_intro] is needed —
 *    no source-side elim required.
 *
 *  No new GLOBAL axioms.  At instantiation time the limb-level
 *  hypothesis discharges from fiat-crypto's [Positional.eval] formula
 *  for the radix-2^51 [[w, 0, 0, 0, 0]] list.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519FromWordBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters                                            *)
(* ================================================================ *)

Section Fe25519FromWordCorrect.

  Variable Fp25519_holds : rust_state_ed -> String.string -> F p -> Prop.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  Definition fp_frame_fw (rs1 rs2 : rust_state_ed) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude -> Fp25519_holds rs1 y v -> Fp25519_holds rs2 y v.

  Variable feval : list Z -> F p.

  Hypothesis Fp25519_holds_intro :
    forall (rs : rust_state_ed) (v : String.string) (limbs : list Z) (x : F p),
      rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs)) ->
      length limbs = 5%nat ->
      feval limbs = x ->
      Fp25519_holds rs v x.

  Hypothesis Fp25519_holds_set_other :
    forall (rs : rust_state_ed) (x : String.string) (tv : tval_ed)
           (y : String.string) (vp : F p),
      y <> x ->
      Fp25519_holds rs y vp ->
      Fp25519_holds (rs_set_tower_ed rs x tv) y vp.

  (** Algebraic hypothesis for from_word: the radix-2^51 limb list
      [[mask64 w; mask64 0; mask64 0; mask64 0; mask64 0]] decodes to
      [F.of_Z w] in [F p].  Mask64 of a value in [0, 2^64) is the
      identity; mask64 0 = 0.  Concrete instantiations discharge this
      from fiat-crypto's [Positional.eval] applied to a single-limb
      input. *)
  Hypothesis feval_limbwise_from_word_mask64 :
    forall (w : Z),
      0 <= w < 2^64 ->
      feval [mask64 w; mask64 0; mask64 0; mask64 0; mask64 0] = F.of_Z _ w.

(* ================================================================ *)
(* §2. Internal lemmas: rs_get_tower / rs_set_tower bookkeeping      *)
(* ================================================================ *)

  Lemma rs_get_set_tower_eq_fw :
    forall rs x tv, rs_get_tower_ed (rs_set_tower_ed rs x tv) x = Some tv.
  Proof.
    intros rs x tv. unfold rs_get_tower_ed, rs_set_tower_ed; cbn.
    induction (rs_tower_ed rs) as [|[k v] rest IH]; cbn.
    - rewrite String.eqb_refl. reflexivity.
    - destruct (String.eqb k x) eqn:Hk; cbn.
      + apply String.eqb_eq in Hk; subst.
        rewrite String.eqb_refl. reflexivity.
      + apply String.eqb_neq in Hk.
        destruct (String.eqb x k) eqn:Hxk.
        * apply String.eqb_eq in Hxk; congruence.
        * exact IH.
  Qed.

  Lemma rs_set_tower_preserves_scalar_fw :
    forall rs x tv w,
      rs_get_scalar_ed (rs_set_tower_ed rs x tv) w =
      rs_get_scalar_ed rs w.
  Proof.
    intros rs x tv w. unfold rs_get_scalar_ed, rs_set_tower_ed; cbn. reflexivity.
  Qed.

  Lemma tval_some_vfp25519_inj_fw :
    forall l1 l2 : list Z,
      Some (exist_tval_ed TFp25519 (VFp25519 l1))
      = Some (exist_tval_ed TFp25519 (VFp25519 l2)) ->
      l1 = l2.
  Proof.
    intros l1 l2 H. injection H as H'. exact H'.
  Qed.

  Lemma eval_SVar_fw :
    forall rs w wv,
      rs_get_scalar_ed rs w = Some wv ->
      eval_sexpr_ed rs (SVar w) = Some wv.
  Proof.
    intros rs w wv Hg. cbn. exact Hg.
  Qed.

  Lemma eval_SLit_fw :
    forall rs z, eval_sexpr_ed rs (SLit z) = Some (mask64 z).
  Proof. intros; cbn; reflexivity. Qed.

  Lemma rexec_limb_store_inv_fw :
    forall loc i e rs1 rs2,
      Hexec (REdLimbStore loc i e) rs1 rs2 ->
      loc.(loc_type) = TFp25519 ->
      exists val_v limbs_old,
        eval_sexpr_ed rs1 e = Some val_v
        /\ rs_get_tower_ed rs1 loc.(loc_var) =
             Some (exist_tval_ed TFp25519 (VFp25519 limbs_old))
        /\ length limbs_old = 5%nat
        /\ (i < 5)%nat
        /\ rs2 = rs_set_tower_ed rs1 loc.(loc_var)
                   (exist_tval_ed TFp25519
                      (VFp25519 (list_set i val_v limbs_old))).
  Proof.
    intros loc i e rs1 rs2 Hexec_n _Hty.
    inversion Hexec_n; subst.
    eexists; eexists; repeat split; eauto.
  Qed.

  Lemma seq_inv_fw c1 c2 rs1 rs3 :
    Hexec (REdSeq c1 c2) rs1 rs3 ->
    exists rs2, Hexec c1 rs1 rs2 /\ Hexec c2 rs2 rs3.
  Proof.
    intros Hexec_seq. inversion Hexec_seq; subst.
    eexists; eauto.
  Qed.

(* ================================================================ *)
(* §3. Limb-list bookkeeping                                         *)
(* ================================================================ *)

  Lemma list_set_nth_same_fw :
    forall {A} i (x : A) xs d,
      (i < length xs)%nat ->
      List.nth i (list_set i x xs) d = x.
  Proof.
    intros A i. induction i; intros x xs d Hlen; destruct xs; cbn in *; try lia.
    - reflexivity.
    - apply IHi. lia.
  Qed.

  Lemma list_set_nth_other_fw :
    forall {A} i j (x : A) xs d,
      i <> j ->
      List.nth j (list_set i x xs) d = List.nth j xs d.
  Proof.
    intros A i. induction i; intros j x xs d Hne; destruct xs, j; cbn; try reflexivity; try lia.
    - apply IHi; lia.
  Qed.

(* ================================================================ *)
(* §4. from_word_inline_correct as a Lemma                           *)
(* ================================================================ *)

  Lemma from_word_inline_correct :
    forall (dest w_loc : located_ed) (rs1 rs2 : rust_state_ed) (wv : Z),
      dest.(loc_type) = TFp25519 ->
      rs_get_scalar_ed rs1 w_loc.(loc_var) = Some wv ->
      0 <= wv < 2^64 ->
      Hexec
        (REdSeq
           (REdLimbStore dest 0%nat (SVar w_loc.(loc_var)))
           (REdSeq
             (REdLimbStore dest 1%nat (SLit 0))
             (REdSeq
               (REdLimbStore dest 2%nat (SLit 0))
               (REdSeq
                 (REdLimbStore dest 3%nat (SLit 0))
                 (REdLimbStore dest 4%nat (SLit 0)))))) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.of_Z _ wv) /\
      fp_frame_fw rs1 rs2 dest.(loc_var).
  Proof.
    intros dest w_loc rs1 rs2 wv Hdt Hgwv Hwv_bnd Hexec_n.
    apply seq_inv_fw in Hexec_n. destruct Hexec_n as [rs01 [Hs0 Htail0]].
    apply seq_inv_fw in Htail0. destruct Htail0 as [rs12 [Hs1 Htail1]].
    apply seq_inv_fw in Htail1. destruct Htail1 as [rs23 [Hs2 Htail2]].
    apply seq_inv_fw in Htail2. destruct Htail2 as [rs34 [Hs3 Hs4]].
    pose proof (rexec_limb_store_inv_fw _ _ _ _ _ Hs0 Hdt) as
      [v0 [limbs_d0 [Hv0_eval [Hd0_get [Hd0_len [_ Hrs01_eq]]]]]].
    pose proof (rexec_limb_store_inv_fw _ _ _ _ _ Hs1 Hdt) as
      [v1 [limbs_d1 [Hv1_eval [Hd1_get [Hd1_len [_ Hrs12_eq]]]]]].
    pose proof (rexec_limb_store_inv_fw _ _ _ _ _ Hs2 Hdt) as
      [v2 [limbs_d2 [Hv2_eval [Hd2_get [Hd2_len [_ Hrs23_eq]]]]]].
    pose proof (rexec_limb_store_inv_fw _ _ _ _ _ Hs3 Hdt) as
      [v3 [limbs_d3 [Hv3_eval [Hd3_get [Hd3_len [_ Hrs34_eq]]]]]].
    pose proof (rexec_limb_store_inv_fw _ _ _ _ _ Hs4 Hdt) as
      [v4 [limbs_d4 [Hv4_eval [Hd4_get [Hd4_len [_ Hrs2_eq]]]]]].
    (* Step 0: SVar w_loc on rs1 returns wv (a 64-bit value). *)
    rewrite (eval_SVar_fw rs1 _ _ Hgwv) in Hv0_eval.
    injection Hv0_eval as Hv0_eq. subst v0. subst rs01.
    (* Step 1: SLit 0 evaluates to mask64 0 = 0. *)
    rewrite eval_SLit_fw in Hv1_eval.
    injection Hv1_eval as Hv1_eq. subst v1.
    rewrite rs_get_set_tower_eq_fw in Hd1_get.
    apply tval_some_vfp25519_inj_fw in Hd1_get.
    subst limbs_d1. subst rs12.
    (* Step 2. *)
    rewrite eval_SLit_fw in Hv2_eval.
    injection Hv2_eval as Hv2_eq. subst v2.
    rewrite rs_get_set_tower_eq_fw in Hd2_get.
    apply tval_some_vfp25519_inj_fw in Hd2_get.
    subst limbs_d2. subst rs23.
    (* Step 3. *)
    rewrite eval_SLit_fw in Hv3_eval.
    injection Hv3_eval as Hv3_eq. subst v3.
    rewrite rs_get_set_tower_eq_fw in Hd3_get.
    apply tval_some_vfp25519_inj_fw in Hd3_get.
    subst limbs_d3. subst rs34.
    (* Step 4. *)
    rewrite eval_SLit_fw in Hv4_eval.
    injection Hv4_eval as Hv4_eq. subst v4.
    rewrite rs_get_set_tower_eq_fw in Hd4_get.
    apply tval_some_vfp25519_inj_fw in Hd4_get.
    subst limbs_d4. subst rs2.
    (* The final limbs list is the 4-step list_set on [limbs_d0]. *)
    set (limbs_final :=
      list_set 4%nat (mask64 0)
        (list_set 3%nat (mask64 0)
          (list_set 2%nat (mask64 0)
            (list_set 1%nat (mask64 0)
              (list_set 0%nat wv limbs_d0))))).
    assert (Hlen_final : length limbs_final = 5%nat).
    { unfold limbs_final. repeat rewrite list_set_length. exact Hd0_len. }
    (* Each input limb in radix-2^51 stays in [0, 2^54), so [mask64 wv]
       equals [wv] when [wv ∈ [0, 2^64)] — which is the [SVar] return
       bound.  But our IR threads SVar through unmasked, so [v0 = wv]
       directly.  The first limb is therefore [wv], not [mask64 wv].
       Combined with [Hwv_bnd : 0 <= wv < 2^64], we have [mask64 wv = wv].

       For the algebraic hypothesis we expose limbs as
       [[mask64 wv; mask64 0; ...; mask64 0]]; we use the fact that
       [mask64 wv = wv] when [wv ∈ [0, 2^64)] to bridge. *)
    assert (Hmask_wv : mask64 wv = wv).
    { unfold mask64. rewrite Z.land_ones by lia.
      rewrite Z.mod_small by exact Hwv_bnd. reflexivity. }
    (* Show limbs_final equals the canonical limb list. *)
    assert (Hfinal_eq : limbs_final = [wv; mask64 0; mask64 0; mask64 0; mask64 0]).
    { unfold limbs_final.
      (* limbs_d0 has length 5; let's destruct it. *)
      destruct limbs_d0 as [|l0 [|l1 [|l2 [|l3 [|l4 [|]]]]]]; cbn in Hd0_len; try lia.
      cbn. reflexivity. }
    assert (Hfeval_final : feval limbs_final = F.of_Z _ wv).
    { rewrite Hfinal_eq.
      rewrite <- Hmask_wv at 1.
      apply feval_limbwise_from_word_mask64.
      exact Hwv_bnd. }
    split.
    + eapply Fp25519_holds_intro;
        [| exact Hlen_final | exact Hfeval_final].
      apply rs_get_set_tower_eq_fw.
    + intros y vy Hne Hy.
      eapply Fp25519_holds_set_other; [exact Hne|].
      eapply Fp25519_holds_set_other; [exact Hne|].
      eapply Fp25519_holds_set_other; [exact Hne|].
      eapply Fp25519_holds_set_other; [exact Hne|].
      eapply Fp25519_holds_set_other; [exact Hne|].
      exact Hy.
  Qed.

(* ================================================================ *)
(* §5. Headline theorem                                              *)
(* ================================================================ *)

  Theorem fe25519_from_word_body_correct :
    forall (rs1 rs2 : rust_state_ed) (w_loc dest : located_ed) (wv : Z),
      dest.(loc_type) = TFp25519 ->
      rs_get_scalar_ed rs1 w_loc.(loc_var) = Some wv ->
      0 <= wv < 2^64 ->
      Hexec (fe25519_from_word_body dest [w_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.of_Z _ wv) /\
      fp_frame_fw rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 w_loc dest wv Hdt Hgwv Hwv_bnd Hexec_n.
    cbn [fe25519_from_word_body] in Hexec_n.
    apply (from_word_inline_correct dest w_loc rs1 rs2 wv); assumption.
  Qed.

End Fe25519FromWordCorrect.

(** Sanity check: list assumptions.  No new GLOBAL axioms. *)
Print Assumptions fe25519_from_word_body_correct.
