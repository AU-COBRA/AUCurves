(** * Fe25519CopyCorrect — functional correctness of [fe25519_copy_body].
 *
 *  Companion to [Fe25519CopyBody.v].  Mirrors the section-parameterised
 *  pattern from [Fe25519AddSubCorrect.v]: abstract over the
 *  [Fp25519_holds] slot predicate plus a per-limb decoder hypothesis,
 *  then derive algebraic correctness of the wrapped function.
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_copy_body_correct] : Qed, via Lemma [copy_inline_correct]
 *    discharged mechanically against limb-level hypotheses
 *    ([Fp25519_holds_intro] / [Fp25519_holds_elim] /
 *     [Fp25519_holds_set_other] / [feval_limbwise_copy_mask64]).
 *    Five [rexec_limb_store_fp25519] inversions threaded through the
 *    abstract limb decoder.
 *
 *  No new GLOBAL axioms.  The Section hypotheses become Π-quantified
 *  parameters of the closed theorem and discharge to fiat-crypto's
 *  [copy_correct] / radix-2^51 limb-bound regime at instantiation
 *  time.
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
Require Import Bedrock.End2End.Ed25519.Fe25519CopyBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters                                            *)
(* ================================================================ *)

Section Fe25519CopyCorrect.

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

  Definition fp_frame_copy (rs1 rs2 : rust_state_ed) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude -> Fp25519_holds rs1 y v -> Fp25519_holds rs2 y v.

  Variable feval : list Z -> F p.

  Hypothesis Fp25519_holds_elim :
    forall (rs : rust_state_ed) (v : String.string) (x : F p),
      Fp25519_holds rs v x ->
      exists limbs : list Z,
        rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
        /\ length limbs = 5%nat
        /\ feval limbs = x.

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

  (** Algebraic hypothesis for copy: the limb-wise [mask64] copy of a
      valid limb list decodes to the same field element.  Concrete
      instantiations discharge this from the radix-2^51 limb-bound
      regime (each limb in [0, 2^54), so [mask64] is identity), or
      simply because [feval] only depends on the values modulo 2^64
      and [mask64] is reduction mod 2^64.

      [build_limb_list_copy la] is the limbwise-mask64 of [la], matching
      the IR semantics: each [REdLimbStore dest i (SLimb a i)] writes
      [mask64 (nth i la 0)] into limb [i] of [dest]. *)
  Definition build_limb_list_copy (la : list Z) : list Z :=
    List.map (fun i => mask64 (List.nth i la 0)) (List.seq 0 5).

  Hypothesis feval_limbwise_copy_mask64 :
    forall (la : list Z),
      length la = 5%nat ->
      feval (build_limb_list_copy la) = feval la.

(* ================================================================ *)
(* §2. Internal lemmas: rs_get_tower / rs_set_tower bookkeeping      *)
(* ================================================================ *)

  Lemma rs_get_set_tower_eq_copy :
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

  Lemma rs_get_set_tower_other_copy :
    forall rs x y tv,
      x <> y ->
      rs_get_tower_ed (rs_set_tower_ed rs x tv) y =
      rs_get_tower_ed rs y.
  Proof.
    intros rs x y tv Hne.
    unfold rs_get_tower_ed, rs_set_tower_ed; cbn.
    induction (rs_tower_ed rs) as [|[k v] rest IH]; cbn.
    - destruct (String.eqb y x) eqn:Hyx; [|reflexivity].
      apply String.eqb_eq in Hyx; subst; congruence.
    - destruct (String.eqb k x) eqn:Hk; cbn.
      + apply String.eqb_eq in Hk; subst.
        destruct (String.eqb y x) eqn:Hyx; cbn; [|reflexivity].
        apply String.eqb_eq in Hyx; subst; congruence.
      + destruct (String.eqb y k) eqn:Hyk; cbn.
        * reflexivity.
        * exact IH.
  Qed.

  Lemma tval_some_vfp25519_inj_copy :
    forall l1 l2 : list Z,
      Some (exist_tval_ed TFp25519 (VFp25519 l1))
      = Some (exist_tval_ed TFp25519 (VFp25519 l2)) ->
      l1 = l2.
  Proof.
    intros l1 l2 H. injection H as H'. exact H'.
  Qed.

  Lemma eval_SLimb_VFp25519_copy :
    forall rs v i limbs,
      rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs)) ->
      (i < 5)%nat ->
      length limbs = 5%nat ->
      eval_sexpr_ed rs (SLimb v i) = Some (mask64 (List.nth i limbs 0)).
  Proof.
    intros rs v i limbs Hget Hi Hlen. cbn.
    rewrite Hget.
    assert (Hnth : List.nth_error limbs i = Some (List.nth i limbs 0)).
    { apply List.nth_error_nth'. lia. }
    rewrite Hnth. reflexivity.
  Qed.

  Lemma rexec_limb_store_inv_copy :
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

  Lemma seq_inv_copy c1 c2 rs1 rs3 :
    Hexec (REdSeq c1 c2) rs1 rs3 ->
    exists rs2, Hexec c1 rs1 rs2 /\ Hexec c2 rs2 rs3.
  Proof.
    intros Hexec_seq. inversion Hexec_seq; subst.
    eexists; eauto.
  Qed.

(* ================================================================ *)
(* §3. Limb-list bookkeeping                                         *)
(* ================================================================ *)

  Lemma list_set_nth_same_copy :
    forall {A} i (x : A) xs d,
      (i < length xs)%nat ->
      List.nth i (list_set i x xs) d = x.
  Proof.
    intros A i. induction i; intros x xs d Hlen; destruct xs; cbn in *; try lia.
    - reflexivity.
    - apply IHi. lia.
  Qed.

  Lemma list_set_nth_other_copy :
    forall {A} i j (x : A) xs d,
      i <> j ->
      List.nth j (list_set i x xs) d = List.nth j xs d.
  Proof.
    intros A i. induction i; intros j x xs d Hne; destruct xs, j; cbn; try reflexivity; try lia.
    - apply IHi; lia.
  Qed.

  (** The "5-limb copy result" predicate. *)
  Definition is_copy5 (out la : list Z) : Prop :=
    length out = 5%nat
    /\ forall i, (i < 5)%nat ->
         List.nth i out 0 = mask64 (List.nth i la 0).

  Lemma build_limb_list_copy_nth :
    forall la i,
      (i < 5)%nat ->
      List.nth i (build_limb_list_copy la) 0 = mask64 (List.nth i la 0).
  Proof.
    intros la i Hi.
    destruct i as [|[|[|[|[|i']]]]];
      cbv [build_limb_list_copy List.map List.seq List.nth];
      try reflexivity; try (exfalso; lia).
  Qed.

  Lemma build_limb_list_copy_length :
    forall la, length (build_limb_list_copy la) = 5%nat.
  Proof.
    intros la. cbv [build_limb_list_copy]. rewrite List.length_map.
    rewrite List.length_seq. reflexivity.
  Qed.

  Lemma is_copy5_eq_build :
    forall out la,
      is_copy5 out la ->
      out = build_limb_list_copy la.
  Proof.
    intros out la [Hlen Hnth].
    apply (List.nth_ext _ _ 0 0).
    - rewrite Hlen, build_limb_list_copy_length. reflexivity.
    - intros i Hi. rewrite Hlen in Hi.
      assert (Hi5 : (i < 5)%nat) by lia.
      rewrite Hnth by lia.
      rewrite build_limb_list_copy_nth by lia.
      reflexivity.
  Qed.

(* ================================================================ *)
(* §4. copy_inline_correct as a Lemma                                *)
(* ================================================================ *)

  Lemma copy_inline_correct :
    forall (dest a : located_ed) (rs1 rs2 : rust_state_ed) (xa : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Hexec
        (REdSeq
           (REdLimbStore dest 0%nat (SLimb a.(loc_var) 0%nat))
           (REdSeq
             (REdLimbStore dest 1%nat (SLimb a.(loc_var) 1%nat))
             (REdSeq
               (REdLimbStore dest 2%nat (SLimb a.(loc_var) 2%nat))
               (REdSeq
                 (REdLimbStore dest 3%nat (SLimb a.(loc_var) 3%nat))
                 (REdLimbStore dest 4%nat (SLimb a.(loc_var) 4%nat)))))) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) xa /\
      fp_frame_copy rs1 rs2 dest.(loc_var).
  Proof.
    intros dest a rs1 rs2 xa Hdt Hat Hdne_a Hxa Hexec_n.
    destruct (Fp25519_holds_elim _ _ _ Hxa) as [la [Hga [Hla Hfa]]].
    apply seq_inv_copy in Hexec_n. destruct Hexec_n as [rs01 [Hs0 Htail0]].
    apply seq_inv_copy in Htail0. destruct Htail0 as [rs12 [Hs1 Htail1]].
    apply seq_inv_copy in Htail1. destruct Htail1 as [rs23 [Hs2 Htail2]].
    apply seq_inv_copy in Htail2. destruct Htail2 as [rs34 [Hs3 Hs4]].
    pose proof (rexec_limb_store_inv_copy _ _ _ _ _ Hs0 Hdt) as
      [v0 [limbs_d0 [Hv0_eval [Hd0_get [Hd0_len [_ Hrs01_eq]]]]]].
    pose proof (rexec_limb_store_inv_copy _ _ _ _ _ Hs1 Hdt) as
      [v1 [limbs_d1 [Hv1_eval [Hd1_get [Hd1_len [_ Hrs12_eq]]]]]].
    pose proof (rexec_limb_store_inv_copy _ _ _ _ _ Hs2 Hdt) as
      [v2 [limbs_d2 [Hv2_eval [Hd2_get [Hd2_len [_ Hrs23_eq]]]]]].
    pose proof (rexec_limb_store_inv_copy _ _ _ _ _ Hs3 Hdt) as
      [v3 [limbs_d3 [Hv3_eval [Hd3_get [Hd3_len [_ Hrs34_eq]]]]]].
    pose proof (rexec_limb_store_inv_copy _ _ _ _ _ Hs4 Hdt) as
      [v4 [limbs_d4 [Hv4_eval [Hd4_get [Hd4_len [_ Hrs2_eq]]]]]].
    (* Step 0: SLimb a 0 read from rs1. *)
    rewrite (eval_SLimb_VFp25519_copy rs1 a.(loc_var) 0%nat la
              Hga ltac:(lia) Hla) in Hv0_eval.
    injection Hv0_eval as Hv0_eq. subst v0. subst rs01.
    (* Step 1. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d1)) |- _ =>
      assert (Hga01 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other_copy by exact Hdne_a; exact Hga)
    end.
    rewrite (eval_SLimb_VFp25519_copy _ _ 1%nat la
              Hga01 ltac:(lia) Hla) in Hv1_eval.
    injection Hv1_eval as Hv1_eq. subst v1.
    rewrite rs_get_set_tower_eq_copy in Hd1_get.
    apply tval_some_vfp25519_inj_copy in Hd1_get.
    subst limbs_d1. subst rs12.
    (* Step 2. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d2)) |- _ =>
      assert (Hga12 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other_copy by exact Hdne_a; exact Hga)
    end.
    rewrite (eval_SLimb_VFp25519_copy _ _ 2%nat la
              Hga12 ltac:(lia) Hla) in Hv2_eval.
    injection Hv2_eval as Hv2_eq. subst v2.
    rewrite rs_get_set_tower_eq_copy in Hd2_get.
    apply tval_some_vfp25519_inj_copy in Hd2_get.
    subst limbs_d2. subst rs23.
    (* Step 3. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d3)) |- _ =>
      assert (Hga23 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other_copy by exact Hdne_a; exact Hga)
    end.
    rewrite (eval_SLimb_VFp25519_copy _ _ 3%nat la
              Hga23 ltac:(lia) Hla) in Hv3_eval.
    injection Hv3_eval as Hv3_eq. subst v3.
    rewrite rs_get_set_tower_eq_copy in Hd3_get.
    apply tval_some_vfp25519_inj_copy in Hd3_get.
    subst limbs_d3. subst rs34.
    (* Step 4. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d4)) |- _ =>
      assert (Hga34 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other_copy by exact Hdne_a; exact Hga)
    end.
    rewrite (eval_SLimb_VFp25519_copy _ _ 4%nat la
              Hga34 ltac:(lia) Hla) in Hv4_eval.
    injection Hv4_eval as Hv4_eq. subst v4.
    rewrite rs_get_set_tower_eq_copy in Hd4_get.
    apply tval_some_vfp25519_inj_copy in Hd4_get.
    subst limbs_d4. subst rs2.
    set (m_i := fun i => mask64 (List.nth i la 0)).
    set (limbs_final :=
      list_set 4%nat (m_i 4%nat)
        (list_set 3%nat (m_i 3%nat)
          (list_set 2%nat (m_i 2%nat)
            (list_set 1%nat (m_i 1%nat)
              (list_set 0%nat (m_i 0%nat) limbs_d0))))).
    assert (Hlen_final : length limbs_final = 5%nat).
    { unfold limbs_final. repeat rewrite list_set_length. exact Hd0_len. }
    assert (His5 : is_copy5 limbs_final la).
    { unfold is_copy5. split; [exact Hlen_final|].
      intros i Hi. unfold limbs_final.
      destruct i as [|[|[|[|[|i']]]]]; try (exfalso; lia).
      - rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_same_copy.
        + reflexivity.
        + rewrite Hd0_len; lia.
      - rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_same_copy.
        + reflexivity.
        + repeat rewrite list_set_length. rewrite Hd0_len; lia.
      - rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_same_copy.
        + reflexivity.
        + repeat rewrite list_set_length. rewrite Hd0_len; lia.
      - rewrite list_set_nth_other_copy by lia.
        rewrite list_set_nth_same_copy.
        + reflexivity.
        + repeat rewrite list_set_length. rewrite Hd0_len; lia.
      - rewrite list_set_nth_same_copy.
        + reflexivity.
        + repeat rewrite list_set_length. rewrite Hd0_len; lia. }
    pose proof (is_copy5_eq_build _ _ His5) as Hfinal_eq.
    assert (Hfeval_final : feval limbs_final = xa).
    { rewrite Hfinal_eq.
      rewrite feval_limbwise_copy_mask64 by assumption.
      exact Hfa. }
    split.
    + eapply Fp25519_holds_intro;
        [| exact Hlen_final | exact Hfeval_final].
      apply rs_get_set_tower_eq_copy.
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

  Theorem fe25519_copy_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_copy_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) xa /\
      fp_frame_copy rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa Hat Hdt Hdne_a Hxa Hexec_n.
    cbn [fe25519_copy_body] in Hexec_n.
    apply (copy_inline_correct dest a_loc rs1 rs2 xa); assumption.
  Qed.

End Fe25519CopyCorrect.

(** Sanity check: list assumptions.  No new GLOBAL axioms. *)
Print Assumptions fe25519_copy_body_correct.
