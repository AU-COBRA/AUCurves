(** * Fe25519SquareCorrect — functional correctness of
 *  [fe25519_square_body].
 *
 *  Companion to [Fe25519SquareBody.v].  Mirrors the section-parameterised
 *  pattern used by [Fe25519AddSubCorrect.v]: abstract over the
 *  [Fp25519_holds] slot predicate plus a single limb-level algebraic
 *  oracle on the symmetric schoolbook, then derive functional
 *  correctness of the wrapped function by threading 5 [REdLimbStore]
 *  inversions through the abstract limb decoder.
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_square_body_correct] :  Qed, via Lemma
 *    [square_inline_correct] discharged mechanically against the
 *    limb-level hypotheses ([Fp25519_holds_intro] / [_elim] /
 *    [_set_other] / [feval_limbwise_square_mask64]).  Five
 *    [rexec_limb_store_inv] inversions threaded through the abstract
 *    limb decoder, then collapsed via [is_square5_eq_build].
 *  - [feval_limbwise_square_mask64] : Section [Hypothesis] — the
 *    algebraic content of fiat-crypto's [Positional.squaremod]
 *    specialised to radix-2^51 with the limbwise mask64 schoolbook.
 *    Discharge through fiat-crypto's [eval_carry_squaremod] is the
 *    Phase 0d / 0e follow-up (mirrors the deferred
 *    [feval_limbwise_mul_mask64] hypothesis for [fe25519_mul]).
 *
 *  History
 *  =======
 *  Phase 0c (this file): replaced the coarse-grained
 *  [square_inline_correct] hypothesis with a Lemma factored over
 *  three limb-level hypotheses on the abstract decoder [feval] (intro,
 *  elim, set_other) shared with [Fe25519AddSubCorrect] + one algebraic
 *  hypothesis [feval_limbwise_square_mask64] on the symmetric
 *  schoolbook.  Same structural shape as the A31 [add_inline_correct]
 *  port.  No new GLOBAL axioms; the Section parameters remain
 *  section-quantified after [End].
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
Require Import Bedrock.End2End.Ed25519.Fe25519SquareBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + limb-     *)
(*     level decoder hypotheses.                                     *)
(* ================================================================ *)

Section Fe25519SquareCorrect.

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

  (** Frame: non-[exclude] variables keep their Fp values. *)
  Definition fp_frame (rs1 rs2 : rust_state_ed) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude -> Fp25519_holds rs1 y v -> Fp25519_holds rs2 y v.

  (** Abstract decoder: how a 5-limb radix-2^51 representation projects
      to the field [F p].  Same shape as in [Fe25519AddSubCorrect]. *)
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

  (** [build_limb_list_square la] is the 5-limb output of the
      symmetric schoolbook squaring, with each limb taken modulo
      2^64 via [mask64] to match the IR's [eval_sexpr_ed] semantics
      on [SMul] / [SAdd] (nested mask64 applications come from each
      arithmetic node).

      Layout — see [Fe25519SquareBody.v] §2 for the closed-form sums.
      Each output limb is a sum of three partial products; each
      partial product (diagonal or scaled cross) carries its own
      [mask64] wrappers reflecting one [SMul] and possibly one [SLit]
      step.  Diagonal a_i² evaluates as
        [mask64 (mask64 (nth i la 0) * mask64 (nth i la 0))]
      Scaled diag a_i² * k:
        [mask64 (mask64 k * mask64 (mask64 (nth i la 0) * mask64 (nth i la 0)))]
      Scaled cross a_i*a_j * k:
        [mask64 (mask64 k *
                 mask64 (mask64 (nth i la 0) * mask64 (nth j la 0)))]
      And each [SAdd P1 (SAdd P2 P3)] sum wraps the result in [mask64]
      once for the inner add and once for the outer add. *)
  Definition pp_diag (la : list Z) (i : nat) : Z :=
    mask64 (mask64 (List.nth i la 0) * mask64 (List.nth i la 0)).

  Definition pp_diag_scaled (la : list Z) (i : nat) (k : Z) : Z :=
    mask64 (mask64 k * mask64 (mask64 (List.nth i la 0)
                                * mask64 (List.nth i la 0))).

  Definition pp_cross_scaled (la : list Z) (i j : nat) (k : Z) : Z :=
    mask64 (mask64 k * mask64 (mask64 (List.nth i la 0)
                                * mask64 (List.nth j la 0))).

  (** The sum-of-three-partial-products layout per output limb, as
      evaluated by [eval_sexpr_ed] on the IR tree [SAdd P1 (SAdd P2 P3)]:
      inner add masks once, outer add masks once more. *)
  Definition sum3 (p1 p2 p3 : Z) : Z :=
    mask64 (p1 + mask64 (p2 + p3)).

  Definition build_limb_list_square (la : list Z) : list Z :=
    [ sum3 (pp_diag la 0)
           (pp_cross_scaled la 1 4 38)
           (pp_cross_scaled la 2 3 38)
    ; sum3 (pp_cross_scaled la 0 1 2)
           (pp_cross_scaled la 2 4 38)
           (pp_diag_scaled la 3 19)
    ; sum3 (pp_cross_scaled la 0 2 2)
           (pp_diag la 1)
           (pp_cross_scaled la 3 4 38)
    ; sum3 (pp_cross_scaled la 0 3 2)
           (pp_cross_scaled la 1 2 2)
           (pp_diag_scaled la 4 19)
    ; sum3 (pp_cross_scaled la 0 4 2)
           (pp_cross_scaled la 1 3 2)
           (pp_diag la 2)
    ].

  (** Algebraic content of fiat-crypto's [carry_square_op] correctness
      at the limb level — the symmetric schoolbook with embedded mask64s
      decodes to [F.mul xa xa] when fed valid limb lists.  Mirrors the
      [feval_limbwise_add_mask64] hypothesis in [Fe25519AddSubCorrect]
      but with the larger sum-of-products body (cf. fiat-crypto's
      [eval_carry_squaremod]).  Discharge through fiat-crypto's
      [Positional.squaremod] is the Phase 0d / 0e follow-up; we expose
      it as a single Hypothesis here at the level used by callers. *)
  Hypothesis feval_limbwise_square_mask64 :
    forall (la : list Z),
      length la = 5%nat ->
      feval (build_limb_list_square la) = F.mul (feval la) (feval la).

(* ================================================================ *)
(* §2. Internal lemmas: rs_get_tower / rs_set_tower bookkeeping      *)
(*     and eval-of-sexpr-tree under a valid 5-limb VFp25519 slot.    *)
(* ================================================================ *)

  Lemma rs_get_set_tower_eq :
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

  Lemma rs_get_set_tower_other :
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

  Lemma tval_some_vfp25519_inj :
    forall l1 l2 : list Z,
      Some (exist_tval_ed TFp25519 (VFp25519 l1))
      = Some (exist_tval_ed TFp25519 (VFp25519 l2)) ->
      l1 = l2.
  Proof.
    intros l1 l2 H. injection H as H'. exact H'.
  Qed.

  Lemma eval_SLimb_VFp25519 :
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

  (** Eval of [ssq_diag av i] = [SMul (SLimb av i) (SLimb av i)] on a
      valid 5-limb VFp25519 slot. *)
  Lemma eval_ssq_diag :
    forall rs av i la,
      rs_get_tower_ed rs av = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      (i < 5)%nat ->
      length la = 5%nat ->
      eval_sexpr_ed rs (ssq_diag av i) = Some (pp_diag la i).
  Proof.
    intros rs av i la Hg Hi Hlen.
    cbv [ssq_diag pp_diag].
    change (eval_sexpr_ed rs (SMul (SLimb av i) (SLimb av i)))
      with (match eval_sexpr_ed rs (SLimb av i), eval_sexpr_ed rs (SLimb av i) with
            | Some va, Some vb => Some (mask64 (va * vb))
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hg Hi Hlen).
    reflexivity.
  Qed.

  (** Eval of [ssq_diag_scaled av i k] = [SMul (SLit k) (SMul (SLimb av i) (SLimb av i))]. *)
  Lemma eval_ssq_diag_scaled :
    forall rs av i k la,
      rs_get_tower_ed rs av = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      (i < 5)%nat ->
      length la = 5%nat ->
      eval_sexpr_ed rs (ssq_diag_scaled av i k) = Some (pp_diag_scaled la i k).
  Proof.
    intros rs av i k la Hg Hi Hlen.
    cbv [ssq_diag_scaled pp_diag_scaled].
    change (eval_sexpr_ed rs
              (SMul (SLit k) (SMul (SLimb av i) (SLimb av i))))
      with (match eval_sexpr_ed rs (SLit k),
                  eval_sexpr_ed rs (SMul (SLimb av i) (SLimb av i)) with
            | Some va, Some vb => Some (mask64 (va * vb))
            | _, _ => None
            end).
    cbn [eval_sexpr_ed].
    rewrite Hg.
    assert (Hnth : List.nth_error la i = Some (List.nth i la 0)).
    { apply List.nth_error_nth'. lia. }
    rewrite Hnth.
    reflexivity.
  Qed.

  (** Eval of [ssq_cross_scaled av i j k] = [SMul (SLit k) (SMul (SLimb av i) (SLimb av j))]. *)
  Lemma eval_ssq_cross_scaled :
    forall rs av i j k la,
      rs_get_tower_ed rs av = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      (i < 5)%nat ->
      (j < 5)%nat ->
      length la = 5%nat ->
      eval_sexpr_ed rs (ssq_cross_scaled av i j k) = Some (pp_cross_scaled la i j k).
  Proof.
    intros rs av i j k la Hg Hi Hj Hlen.
    cbv [ssq_cross_scaled pp_cross_scaled].
    change (eval_sexpr_ed rs
              (SMul (SLit k) (SMul (SLimb av i) (SLimb av j))))
      with (match eval_sexpr_ed rs (SLit k),
                  eval_sexpr_ed rs (SMul (SLimb av i) (SLimb av j)) with
            | Some va, Some vb => Some (mask64 (va * vb))
            | _, _ => None
            end).
    cbn [eval_sexpr_ed].
    rewrite Hg.
    assert (Hnthi : List.nth_error la i = Some (List.nth i la 0)).
    { apply List.nth_error_nth'. lia. }
    assert (Hnthj : List.nth_error la j = Some (List.nth j la 0)).
    { apply List.nth_error_nth'. lia. }
    rewrite Hnthi, Hnthj.
    reflexivity.
  Qed.

  (** Eval of [SAdd P1 (SAdd P2 P3)] given each partial-product
      evaluation.  Wraps the sum once per add node in [mask64], matching
      the [sum3] arrangement in [build_limb_list_square]. *)
  Lemma eval_sum3 :
    forall rs e1 e2 e3 v1 v2 v3,
      eval_sexpr_ed rs e1 = Some v1 ->
      eval_sexpr_ed rs e2 = Some v2 ->
      eval_sexpr_ed rs e3 = Some v3 ->
      eval_sexpr_ed rs (SAdd e1 (SAdd e2 e3)) = Some (sum3 v1 v2 v3).
  Proof.
    intros rs e1 e2 e3 v1 v2 v3 H1 H2 H3.
    cbv [sum3].
    change (eval_sexpr_ed rs (SAdd e1 (SAdd e2 e3)))
      with (match eval_sexpr_ed rs e1, eval_sexpr_ed rs (SAdd e2 e3) with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    change (eval_sexpr_ed rs (SAdd e2 e3))
      with (match eval_sexpr_ed rs e2, eval_sexpr_ed rs e3 with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    rewrite H1, H2, H3.
    reflexivity.
  Qed.

  (** Inversion for a single [REdLimbStore loc i e] step. *)
  Lemma rexec_limb_store_inv :
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

  Lemma seq_inv c1 c2 rs1 rs3 :
    Hexec (REdSeq c1 c2) rs1 rs3 ->
    exists rs2, Hexec c1 rs1 rs2 /\ Hexec c2 rs2 rs3.
  Proof.
    intros Hexec_seq. inversion Hexec_seq; subst.
    eexists; eauto.
  Qed.

(* ================================================================ *)
(* §3. Limb-list bookkeeping                                         *)
(* ================================================================ *)

  Lemma list_set_nth_same :
    forall {A} i (x : A) xs d,
      (i < length xs)%nat ->
      List.nth i (list_set i x xs) d = x.
  Proof.
    intros A i. induction i; intros x xs d Hlen; destruct xs; cbn in *; try lia.
    - reflexivity.
    - apply IHi. lia.
  Qed.

  Lemma list_set_nth_other :
    forall {A} i j (x : A) xs d,
      i <> j ->
      List.nth j (list_set i x xs) d = List.nth j xs d.
  Proof.
    intros A i. induction i; intros j x xs d Hne; destruct xs, j; cbn; try reflexivity; try lia.
    - apply IHi; lia.
  Qed.

  (** The "5-limb square result" predicate: a list [out] of length 5
      whose [i]-th limb is the [sum3] of three partial products
      computed from [la], matching the per-limb formula in
      [build_limb_list_square]. *)
  Definition is_square5 (out la : list Z) : Prop :=
    length out = 5%nat
    /\ List.nth 0 out 0 = sum3 (pp_diag la 0)
                                (pp_cross_scaled la 1 4 38)
                                (pp_cross_scaled la 2 3 38)
    /\ List.nth 1 out 0 = sum3 (pp_cross_scaled la 0 1 2)
                                (pp_cross_scaled la 2 4 38)
                                (pp_diag_scaled la 3 19)
    /\ List.nth 2 out 0 = sum3 (pp_cross_scaled la 0 2 2)
                                (pp_diag la 1)
                                (pp_cross_scaled la 3 4 38)
    /\ List.nth 3 out 0 = sum3 (pp_cross_scaled la 0 3 2)
                                (pp_cross_scaled la 1 2 2)
                                (pp_diag_scaled la 4 19)
    /\ List.nth 4 out 0 = sum3 (pp_cross_scaled la 0 4 2)
                                (pp_cross_scaled la 1 3 2)
                                (pp_diag la 2).

  Lemma build_limb_list_square_length :
    forall la, length (build_limb_list_square la) = 5%nat.
  Proof. intros la. reflexivity. Qed.

  Lemma is_square5_eq_build :
    forall out la,
      is_square5 out la ->
      out = build_limb_list_square la.
  Proof.
    intros out la [Hlen [H0 [H1 [H2 [H3 H4]]]]].
    apply (List.nth_ext _ _ 0 0).
    - rewrite Hlen, build_limb_list_square_length. reflexivity.
    - intros i Hi. rewrite Hlen in Hi.
      destruct i as [|[|[|[|[|i']]]]]; try (exfalso; lia).
      + rewrite H0; reflexivity.
      + rewrite H1; reflexivity.
      + rewrite H2; reflexivity.
      + rewrite H3; reflexivity.
      + rewrite H4; reflexivity.
  Qed.

(* ================================================================ *)
(* §4. square_inline_correct as a Lemma                              *)
(* ================================================================ *)

  (** Internal: chain through the 5 [REdLimbStore]s of the inline
      schoolbook and prove the destination slot ends as a [VFp25519]
      whose limbs match [is_square5].  Factors the "shape of the
      inline square chain" from the "feval decodes the schoolbook to
      F.mul xa xa" algebra ([feval_limbwise_square_mask64]). *)
  Lemma square_inline_correct :
    forall (dest a : located_ed) (rs1 rs2 : rust_state_ed) (xa : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Hexec
        (REdSeq
           (REdLimbStore dest 0%nat
              (SAdd (ssq_diag a.(loc_var) 0)
                (SAdd (ssq_cross_scaled a.(loc_var) 1 4 38)
                      (ssq_cross_scaled a.(loc_var) 2 3 38))))
           (REdSeq
             (REdLimbStore dest 1%nat
                (SAdd (ssq_cross_scaled a.(loc_var) 0 1 2)
                  (SAdd (ssq_cross_scaled a.(loc_var) 2 4 38)
                        (ssq_diag_scaled a.(loc_var) 3 19))))
             (REdSeq
               (REdLimbStore dest 2%nat
                  (SAdd (ssq_cross_scaled a.(loc_var) 0 2 2)
                    (SAdd (ssq_diag a.(loc_var) 1)
                          (ssq_cross_scaled a.(loc_var) 3 4 38))))
               (REdSeq
                 (REdLimbStore dest 3%nat
                    (SAdd (ssq_cross_scaled a.(loc_var) 0 3 2)
                      (SAdd (ssq_cross_scaled a.(loc_var) 1 2 2)
                            (ssq_diag_scaled a.(loc_var) 4 19))))
                 (REdLimbStore dest 4%nat
                    (SAdd (ssq_cross_scaled a.(loc_var) 0 4 2)
                      (SAdd (ssq_cross_scaled a.(loc_var) 1 3 2)
                            (ssq_diag a.(loc_var) 2))))))))
        rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xa) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros dest a rs1 rs2 xa Hdt Hat Hdne_a Hxa Hexec_n.
    destruct (Fp25519_holds_elim _ _ _ Hxa) as [la [Hga [Hla Hfa]]].
    apply seq_inv in Hexec_n. destruct Hexec_n as [rs01 [Hs0 Htail0]].
    apply seq_inv in Htail0. destruct Htail0 as [rs12 [Hs1 Htail1]].
    apply seq_inv in Htail1. destruct Htail1 as [rs23 [Hs2 Htail2]].
    apply seq_inv in Htail2. destruct Htail2 as [rs34 [Hs3 Hs4]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs0 Hdt) as
      [v0 [limbs_d0 [Hv0_eval [Hd0_get [Hd0_len [_ Hrs01_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs1 Hdt) as
      [v1 [limbs_d1 [Hv1_eval [Hd1_get [Hd1_len [_ Hrs12_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs2 Hdt) as
      [v2 [limbs_d2 [Hv2_eval [Hd2_get [Hd2_len [_ Hrs23_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs3 Hdt) as
      [v3 [limbs_d3 [Hv3_eval [Hd3_get [Hd3_len [_ Hrs34_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs4 Hdt) as
      [v4 [limbs_d4 [Hv4_eval [Hd4_get [Hd4_len [_ Hrs2_eq]]]]]].
    (* Step 0: eval against rs1. *)
    pose proof (eval_ssq_diag rs1 a.(loc_var) 0%nat la Hga ltac:(lia) Hla) as Hp0a.
    pose proof (eval_ssq_cross_scaled rs1 a.(loc_var) 1%nat 4%nat 38 la Hga ltac:(lia) ltac:(lia) Hla) as Hp0b.
    pose proof (eval_ssq_cross_scaled rs1 a.(loc_var) 2%nat 3%nat 38 la Hga ltac:(lia) ltac:(lia) Hla) as Hp0c.
    rewrite (eval_sum3 _ _ _ _ _ _ _ Hp0a Hp0b Hp0c) in Hv0_eval.
    injection Hv0_eval as Hv0_eq. subst v0. subst rs01.
    (* Step 1: read [a] from rs1[dest<-...]; slot a preserved (dest <> a). *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d1)) |- _ =>
      assert (Hga01 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga)
    end.
    pose proof (eval_ssq_cross_scaled _ a.(loc_var) 0%nat 1%nat 2 la Hga01 ltac:(lia) ltac:(lia) Hla) as Hp1a.
    pose proof (eval_ssq_cross_scaled _ a.(loc_var) 2%nat 4%nat 38 la Hga01 ltac:(lia) ltac:(lia) Hla) as Hp1b.
    pose proof (eval_ssq_diag_scaled _ a.(loc_var) 3%nat 19 la Hga01 ltac:(lia) Hla) as Hp1c.
    rewrite (eval_sum3 _ _ _ _ _ _ _ Hp1a Hp1b Hp1c) in Hv1_eval.
    injection Hv1_eval as Hv1_eq. subst v1.
    rewrite rs_get_set_tower_eq in Hd1_get.
    apply tval_some_vfp25519_inj in Hd1_get.
    subst limbs_d1. subst rs12.
    (* Step 2. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d2)) |- _ =>
      assert (Hga12 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga)
    end.
    pose proof (eval_ssq_cross_scaled _ a.(loc_var) 0%nat 2%nat 2 la Hga12 ltac:(lia) ltac:(lia) Hla) as Hp2a.
    pose proof (eval_ssq_diag _ a.(loc_var) 1%nat la Hga12 ltac:(lia) Hla) as Hp2b.
    pose proof (eval_ssq_cross_scaled _ a.(loc_var) 3%nat 4%nat 38 la Hga12 ltac:(lia) ltac:(lia) Hla) as Hp2c.
    rewrite (eval_sum3 _ _ _ _ _ _ _ Hp2a Hp2b Hp2c) in Hv2_eval.
    injection Hv2_eval as Hv2_eq. subst v2.
    rewrite rs_get_set_tower_eq in Hd2_get.
    apply tval_some_vfp25519_inj in Hd2_get.
    subst limbs_d2. subst rs23.
    (* Step 3. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d3)) |- _ =>
      assert (Hga23 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga)
    end.
    pose proof (eval_ssq_cross_scaled _ a.(loc_var) 0%nat 3%nat 2 la Hga23 ltac:(lia) ltac:(lia) Hla) as Hp3a.
    pose proof (eval_ssq_cross_scaled _ a.(loc_var) 1%nat 2%nat 2 la Hga23 ltac:(lia) ltac:(lia) Hla) as Hp3b.
    pose proof (eval_ssq_diag_scaled _ a.(loc_var) 4%nat 19 la Hga23 ltac:(lia) Hla) as Hp3c.
    rewrite (eval_sum3 _ _ _ _ _ _ _ Hp3a Hp3b Hp3c) in Hv3_eval.
    injection Hv3_eval as Hv3_eq. subst v3.
    rewrite rs_get_set_tower_eq in Hd3_get.
    apply tval_some_vfp25519_inj in Hd3_get.
    subst limbs_d3. subst rs34.
    (* Step 4. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d4)) |- _ =>
      assert (Hga34 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga)
    end.
    pose proof (eval_ssq_cross_scaled _ a.(loc_var) 0%nat 4%nat 2 la Hga34 ltac:(lia) ltac:(lia) Hla) as Hp4a.
    pose proof (eval_ssq_cross_scaled _ a.(loc_var) 1%nat 3%nat 2 la Hga34 ltac:(lia) ltac:(lia) Hla) as Hp4b.
    pose proof (eval_ssq_diag _ a.(loc_var) 2%nat la Hga34 ltac:(lia) Hla) as Hp4c.
    rewrite (eval_sum3 _ _ _ _ _ _ _ Hp4a Hp4b Hp4c) in Hv4_eval.
    injection Hv4_eval as Hv4_eq. subst v4.
    rewrite rs_get_set_tower_eq in Hd4_get.
    apply tval_some_vfp25519_inj in Hd4_get.
    subst limbs_d4. subst rs2.
    (* Final state: rs1 chained through 5 list_set's at dest.  Compute
       the final limb list and show it matches build_limb_list_square. *)
    set (h0 := sum3 (pp_diag la 0)
                    (pp_cross_scaled la 1 4 38)
                    (pp_cross_scaled la 2 3 38)).
    set (h1 := sum3 (pp_cross_scaled la 0 1 2)
                    (pp_cross_scaled la 2 4 38)
                    (pp_diag_scaled la 3 19)).
    set (h2 := sum3 (pp_cross_scaled la 0 2 2)
                    (pp_diag la 1)
                    (pp_cross_scaled la 3 4 38)).
    set (h3 := sum3 (pp_cross_scaled la 0 3 2)
                    (pp_cross_scaled la 1 2 2)
                    (pp_diag_scaled la 4 19)).
    set (h4 := sum3 (pp_cross_scaled la 0 4 2)
                    (pp_cross_scaled la 1 3 2)
                    (pp_diag la 2)).
    set (limbs_final :=
      list_set 4%nat h4
        (list_set 3%nat h3
          (list_set 2%nat h2
            (list_set 1%nat h1
              (list_set 0%nat h0 limbs_d0))))).
    assert (Hlen_final : length limbs_final = 5%nat).
    { unfold limbs_final.
      repeat rewrite list_set_length. exact Hd0_len. }
    assert (His5 : is_square5 limbs_final la).
    { unfold is_square5, limbs_final.
      split; [exact Hlen_final|].
      repeat split.
      - rewrite list_set_nth_other by lia.
        rewrite list_set_nth_other by lia.
        rewrite list_set_nth_other by lia.
        rewrite list_set_nth_other by lia.
        rewrite list_set_nth_same.
        + reflexivity.
        + rewrite Hd0_len; lia.
      - rewrite list_set_nth_other by lia.
        rewrite list_set_nth_other by lia.
        rewrite list_set_nth_other by lia.
        rewrite list_set_nth_same.
        + reflexivity.
        + repeat rewrite list_set_length. rewrite Hd0_len; lia.
      - rewrite list_set_nth_other by lia.
        rewrite list_set_nth_other by lia.
        rewrite list_set_nth_same.
        + reflexivity.
        + repeat rewrite list_set_length. rewrite Hd0_len; lia.
      - rewrite list_set_nth_other by lia.
        rewrite list_set_nth_same.
        + reflexivity.
        + repeat rewrite list_set_length. rewrite Hd0_len; lia.
      - rewrite list_set_nth_same.
        + reflexivity.
        + repeat rewrite list_set_length. rewrite Hd0_len; lia. }
    pose proof (is_square5_eq_build _ _ His5) as Hfinal_eq.
    assert (Hfeval_final : feval limbs_final = F.mul xa xa).
    { rewrite Hfinal_eq.
      rewrite feval_limbwise_square_mask64 by assumption.
      rewrite Hfa. reflexivity. }
    split.
    + eapply Fp25519_holds_intro;
        [| exact Hlen_final | exact Hfeval_final].
      apply rs_get_set_tower_eq.
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

  Theorem fe25519_square_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_square_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xa) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa Hat Hdt Hdne Hxa Hexec_n.
    cbn [fe25519_square_body] in Hexec_n.
    apply (square_inline_correct dest a_loc rs1 rs2 xa); assumption.
  Qed.

End Fe25519SquareCorrect.

(** Sanity check: list assumptions of the headline theorem.  Inside
    the Section, the [Variable] / [Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_square_body_correct.
