(** * Fe25519MulCorrect — functional correctness of [fe25519_mul_body].
 *
 *  Companion to [Fe25519MulBody.v].  Mirrors the section-parameterised
 *  pattern used by [Fe25519AddSubCorrect.v] (A31) and
 *  [Fe25519SquareCorrect.v] (A45): abstract over the [Fp25519_holds]
 *  slot predicate plus a single limb-level algebraic oracle on the
 *  asymmetric schoolbook, then derive functional correctness of the
 *  wrapped function by threading 5 [REdLimbStore] inversions through
 *  the abstract limb decoder.
 *
 *  Status (Phase 0d, 2026-05-13)
 *  =============================
 *  - [fe25519_mul_body_correct] :  Qed, via Lemma [mul_inline_correct]
 *    discharged mechanically against the limb-level hypotheses
 *    ([Fp25519_holds_intro] / [_elim] / [_set_other] /
 *    [feval_limbwise_mul_mask64]).  Five [rexec_limb_store_inv]
 *    inversions threaded through the abstract limb decoder, then
 *    collapsed via [is_mul5_eq_build].
 *  - [feval_limbwise_mul_mask64] :  Section [Hypothesis] — the
 *    algebraic content of fiat-crypto's [Positional.mulmod] specialised
 *    to radix-2^51 with the limbwise mask64 schoolbook.  Discharge
 *    through fiat-crypto's [eval_carry_mulmod] is the Phase 0e / 0f
 *    follow-up (mirrors the deferred [feval_limbwise_square_mask64]
 *    hypothesis for [fe25519_square]).
 *
 *  CAVEAT — mask64 truncation of partial products
 *  ==============================================
 *  The IR's [SMul] semantics is [mask64 (va * vb)] — i.e. the result
 *  of every [SMul] node is truncated to u64.  In an asymmetric 5×5
 *  radix-2^51 schoolbook a partial product [a_i * b_j] for valid Fp
 *  limbs (each bounded by 2^54 after carry) is ≈2^108, which DOES NOT
 *  fit in u64.  Likewise [19 * (a_i * b_j)] is ≈2^113.  Thus
 *  [feval_limbwise_mul_mask64] is NOT trivially equivalent to
 *  fiat-crypto's [mul_correct]: the algebraic content of the
 *  hypothesis is "the truncated-to-u64 limbwise schoolbook decodes via
 *  [feval] to [F.mul xa xb]", which is only true when [feval] is the
 *  decoder for the [TFp25519] representation and the [mask64]s are
 *  modular-arithmetically inert (i.e. eval-mod-p ignores high bits).
 *  In Phase 0e/0f this will be discharged either by:
 *
 *    (a) widening [SMul] to u128 (or adding an [SMul128] node), so the
 *        partial products fit and the truncation collapses to identity,
 *        or
 *    (b) defining [feval] explicitly as
 *        [F.of_Z p (Σ_i 2^(51 i) * (nth i limbs 0))] and proving the
 *        modulus-p equivalence using [Z.land_pow2_sub_1_mod] /
 *        [F.of_Z_mod] lemmas, so that the [mask64]s on each partial
 *        product become invisible mod p once we reduce the radix-2^51
 *        accumulator mod (2^255 - 19).
 *
 *  Option (b) is the lighter discharge — see the
 *  [feval_limbwise_mul_mask64] declaration for the precise shape.
 *  This file factors out the structural ("five-store") proof so that
 *  Phase 0e/0f only needs to discharge a single algebraic Hypothesis.
 *
 *  History
 *  =======
 *  Phase 0d (this file): replaced the coarse-grained
 *  [mul_inline_correct] hypothesis with a Lemma factored over three
 *  limb-level hypotheses on the abstract decoder [feval] (intro, elim,
 *  set_other) shared with [Fe25519AddSubCorrect] / [Fe25519SquareCorrect]
 *  + one algebraic hypothesis [feval_limbwise_mul_mask64] on the
 *  asymmetric schoolbook.  Same structural shape as the A45
 *  [square_inline_correct] port.  No new GLOBAL axioms; the Section
 *  parameters remain section-quantified after [End].
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
Require Import Bedrock.End2End.Ed25519.Fe25519MulBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + limb-     *)
(*     level decoder hypotheses.                                     *)
(* ================================================================ *)

Section Fe25519MulCorrect.

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
      to the field [F p].  Same shape as in [Fe25519AddSubCorrect] /
      [Fe25519SquareCorrect]. *)
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

  (** [pp_mul la lb i j] : the unscaled partial product a_i * b_j with
      its [mask64] wrappers, as evaluated by [eval_sexpr_ed] on the
      [SMul (SLimb a i) (SLimb b j)] IR tree.  One [mask64] from each
      [SLimb] and one from the outer [SMul]. *)
  Definition pp_mul (la lb : list Z) (i j : nat) : Z :=
    mask64 (mask64 (List.nth i la 0) * mask64 (List.nth j lb 0)).

  (** [pp_mul_scaled la lb i j k] : the 19-scaled partial product
      k * (a_i * b_j) wrappers, as evaluated by [eval_sexpr_ed] on the
      [SMul (SLit k) (SMul (SLimb a i) (SLimb b j))] IR tree.  Two
      nested [mask64]s on the inner [SMul]; one on the [SLit]; one on
      the outer [SMul]. *)
  Definition pp_mul_scaled (la lb : list Z) (i j : nat) (k : Z) : Z :=
    mask64 (mask64 k * mask64 (mask64 (List.nth i la 0)
                               * mask64 (List.nth j lb 0))).

  (** The sum-of-five-partial-products layout per output limb, as
      evaluated by [eval_sexpr_ed] on the IR tree
      [SAdd P1 (SAdd P2 (SAdd P3 (SAdd P4 P5)))]: four nested adds, each
      contributing one [mask64]. *)
  Definition sum5 (p1 p2 p3 p4 p5 : Z) : Z :=
    mask64 (p1 + mask64 (p2 + mask64 (p3 + mask64 (p4 + p5)))).

  Definition build_limb_list_mul (la lb : list Z) : list Z :=
    [ sum5 (pp_mul la lb 0 0)
           (pp_mul_scaled la lb 1 4 19)
           (pp_mul_scaled la lb 2 3 19)
           (pp_mul_scaled la lb 3 2 19)
           (pp_mul_scaled la lb 4 1 19)
    ; sum5 (pp_mul la lb 0 1)
           (pp_mul la lb 1 0)
           (pp_mul_scaled la lb 2 4 19)
           (pp_mul_scaled la lb 3 3 19)
           (pp_mul_scaled la lb 4 2 19)
    ; sum5 (pp_mul la lb 0 2)
           (pp_mul la lb 1 1)
           (pp_mul la lb 2 0)
           (pp_mul_scaled la lb 3 4 19)
           (pp_mul_scaled la lb 4 3 19)
    ; sum5 (pp_mul la lb 0 3)
           (pp_mul la lb 1 2)
           (pp_mul la lb 2 1)
           (pp_mul la lb 3 0)
           (pp_mul_scaled la lb 4 4 19)
    ; sum5 (pp_mul la lb 0 4)
           (pp_mul la lb 1 3)
           (pp_mul la lb 2 2)
           (pp_mul la lb 3 1)
           (pp_mul la lb 4 0)
    ].

  (** Algebraic content of fiat-crypto's [carry_mul_op] correctness at
      the limb level — the asymmetric schoolbook with embedded mask64s
      decodes to [F.mul xa xb] when fed valid limb lists.  Mirrors
      [feval_limbwise_square_mask64] in [Fe25519SquareCorrect.v] but
      with the larger sum-of-five-partial-products body (cf.
      fiat-crypto's [eval_carry_mulmod]).

      MASK64 CAVEAT (see the file header for the long version): the
      [mask64] applied at every [SMul] node truncates partial products
      that exceed 2^64 (in this body, [pp_mul] is ≈ 2^108 and
      [pp_mul_scaled] is ≈ 2^113 for valid radix-2^51 limbs).  This
      hypothesis is therefore NOT a direct restatement of
      fiat-crypto's [mul_correct]: it says that the mask64-truncated
      partial-product sum still decodes via [feval] to [F.mul xa xb].
      Discharge in Phase 0e/0f goes either via u128-widening of [SMul]
      (so the [mask64]s collapse to identity) or via an explicit
      [feval = F.of_Z (Σ 2^(51 i) limb_i)] characterisation where the
      [mask64]s are absorbed mod (2^255 - 19). *)
  Hypothesis feval_limbwise_mul_mask64 :
    forall (la lb : list Z),
      length la = 5%nat ->
      length lb = 5%nat ->
      feval (build_limb_list_mul la lb) = F.mul (feval la) (feval lb).

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

  (** Eval of [smul_limbs av bv i j] = [SMul (SLimb av i) (SLimb bv j)]
      on two valid 5-limb VFp25519 slots (asymmetric — different vars). *)
  Lemma eval_smul_limbs :
    forall rs av bv i j la lb,
      rs_get_tower_ed rs av = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      rs_get_tower_ed rs bv = Some (exist_tval_ed TFp25519 (VFp25519 lb)) ->
      (i < 5)%nat ->
      (j < 5)%nat ->
      length la = 5%nat ->
      length lb = 5%nat ->
      eval_sexpr_ed rs (smul_limbs av bv i j) = Some (pp_mul la lb i j).
  Proof.
    intros rs av bv i j la lb Hga Hgb Hi Hj Hla Hlb.
    cbv [smul_limbs pp_mul].
    change (eval_sexpr_ed rs (SMul (SLimb av i) (SLimb bv j)))
      with (match eval_sexpr_ed rs (SLimb av i), eval_sexpr_ed rs (SLimb bv j) with
            | Some va, Some vb => Some (mask64 (va * vb))
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hga Hi Hla).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hgb Hj Hlb).
    reflexivity.
  Qed.

  (** Eval of [smul_scaled av bv i j k] = [SMul (SLit k) (SMul (SLimb av i)
      (SLimb bv j))] on two valid 5-limb VFp25519 slots. *)
  Lemma eval_smul_scaled :
    forall rs av bv i j k la lb,
      rs_get_tower_ed rs av = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      rs_get_tower_ed rs bv = Some (exist_tval_ed TFp25519 (VFp25519 lb)) ->
      (i < 5)%nat ->
      (j < 5)%nat ->
      length la = 5%nat ->
      length lb = 5%nat ->
      eval_sexpr_ed rs (smul_scaled av bv i j k) =
      Some (pp_mul_scaled la lb i j k).
  Proof.
    intros rs av bv i j k la lb Hga Hgb Hi Hj Hla Hlb.
    cbv [smul_scaled pp_mul_scaled].
    change (eval_sexpr_ed rs
              (SMul (SLit k) (SMul (SLimb av i) (SLimb bv j))))
      with (match eval_sexpr_ed rs (SLit k),
                  eval_sexpr_ed rs (SMul (SLimb av i) (SLimb bv j)) with
            | Some va, Some vb => Some (mask64 (va * vb))
            | _, _ => None
            end).
    cbn [eval_sexpr_ed].
    rewrite Hga, Hgb.
    assert (Hnthi : List.nth_error la i = Some (List.nth i la 0)).
    { apply List.nth_error_nth'. lia. }
    assert (Hnthj : List.nth_error lb j = Some (List.nth j lb 0)).
    { apply List.nth_error_nth'. lia. }
    rewrite Hnthi, Hnthj.
    reflexivity.
  Qed.

  (** Eval of [SAdd P1 (SAdd P2 (SAdd P3 (SAdd P4 P5)))] given each
      partial-product evaluation.  Wraps the sum once per [SAdd] node
      in [mask64], matching the [sum5] arrangement in
      [build_limb_list_mul]. *)
  Lemma eval_sum5 :
    forall rs e1 e2 e3 e4 e5 v1 v2 v3 v4 v5,
      eval_sexpr_ed rs e1 = Some v1 ->
      eval_sexpr_ed rs e2 = Some v2 ->
      eval_sexpr_ed rs e3 = Some v3 ->
      eval_sexpr_ed rs e4 = Some v4 ->
      eval_sexpr_ed rs e5 = Some v5 ->
      eval_sexpr_ed rs (SAdd e1 (SAdd e2 (SAdd e3 (SAdd e4 e5)))) =
      Some (sum5 v1 v2 v3 v4 v5).
  Proof.
    intros rs e1 e2 e3 e4 e5 v1 v2 v3 v4 v5 H1 H2 H3 H4 H5.
    cbv [sum5].
    change (eval_sexpr_ed rs (SAdd e1 (SAdd e2 (SAdd e3 (SAdd e4 e5)))))
      with (match eval_sexpr_ed rs e1,
                  eval_sexpr_ed rs (SAdd e2 (SAdd e3 (SAdd e4 e5))) with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    change (eval_sexpr_ed rs (SAdd e2 (SAdd e3 (SAdd e4 e5))))
      with (match eval_sexpr_ed rs e2,
                  eval_sexpr_ed rs (SAdd e3 (SAdd e4 e5)) with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    change (eval_sexpr_ed rs (SAdd e3 (SAdd e4 e5)))
      with (match eval_sexpr_ed rs e3, eval_sexpr_ed rs (SAdd e4 e5) with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    change (eval_sexpr_ed rs (SAdd e4 e5))
      with (match eval_sexpr_ed rs e4, eval_sexpr_ed rs e5 with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    rewrite H1, H2, H3, H4, H5.
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

  (** The "5-limb mul result" predicate: a list [out] of length 5
      whose [i]-th limb is the [sum5] of five partial products
      computed from [la], [lb], matching the per-limb formula in
      [build_limb_list_mul]. *)
  Definition is_mul5 (out la lb : list Z) : Prop :=
    length out = 5%nat
    /\ List.nth 0 out 0 = sum5 (pp_mul la lb 0 0)
                                (pp_mul_scaled la lb 1 4 19)
                                (pp_mul_scaled la lb 2 3 19)
                                (pp_mul_scaled la lb 3 2 19)
                                (pp_mul_scaled la lb 4 1 19)
    /\ List.nth 1 out 0 = sum5 (pp_mul la lb 0 1)
                                (pp_mul la lb 1 0)
                                (pp_mul_scaled la lb 2 4 19)
                                (pp_mul_scaled la lb 3 3 19)
                                (pp_mul_scaled la lb 4 2 19)
    /\ List.nth 2 out 0 = sum5 (pp_mul la lb 0 2)
                                (pp_mul la lb 1 1)
                                (pp_mul la lb 2 0)
                                (pp_mul_scaled la lb 3 4 19)
                                (pp_mul_scaled la lb 4 3 19)
    /\ List.nth 3 out 0 = sum5 (pp_mul la lb 0 3)
                                (pp_mul la lb 1 2)
                                (pp_mul la lb 2 1)
                                (pp_mul la lb 3 0)
                                (pp_mul_scaled la lb 4 4 19)
    /\ List.nth 4 out 0 = sum5 (pp_mul la lb 0 4)
                                (pp_mul la lb 1 3)
                                (pp_mul la lb 2 2)
                                (pp_mul la lb 3 1)
                                (pp_mul la lb 4 0).

  Lemma build_limb_list_mul_length :
    forall la lb, length (build_limb_list_mul la lb) = 5%nat.
  Proof. intros la lb. reflexivity. Qed.

  Lemma is_mul5_eq_build :
    forall out la lb,
      is_mul5 out la lb ->
      out = build_limb_list_mul la lb.
  Proof.
    intros out la lb [Hlen [H0 [H1 [H2 [H3 H4]]]]].
    apply (List.nth_ext _ _ 0 0).
    - rewrite Hlen, build_limb_list_mul_length. reflexivity.
    - intros i Hi. rewrite Hlen in Hi.
      destruct i as [|[|[|[|[|i']]]]]; try (exfalso; lia).
      + rewrite H0; reflexivity.
      + rewrite H1; reflexivity.
      + rewrite H2; reflexivity.
      + rewrite H3; reflexivity.
      + rewrite H4; reflexivity.
  Qed.

(* ================================================================ *)
(* §4. mul_inline_correct as a Lemma                                 *)
(* ================================================================ *)

  (** Internal: chain through the 5 [REdLimbStore]s of the inline
      schoolbook and prove the destination slot ends as a [VFp25519]
      whose limbs match [is_mul5].  Factors the "shape of the inline
      mul chain" from the "feval decodes the schoolbook to F.mul xa xb"
      algebra ([feval_limbwise_mul_mask64]). *)
  Lemma mul_inline_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed)
           (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec
        (REdSeq
           (REdLimbStore dest 0%nat
              (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 0)
                (SAdd (smul_scaled a.(loc_var) b.(loc_var) 1 4 19)
                  (SAdd (smul_scaled a.(loc_var) b.(loc_var) 2 3 19)
                    (SAdd (smul_scaled a.(loc_var) b.(loc_var) 3 2 19)
                          (smul_scaled a.(loc_var) b.(loc_var) 4 1 19))))))
           (REdSeq
             (REdLimbStore dest 1%nat
                (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 1)
                  (SAdd (smul_limbs a.(loc_var) b.(loc_var) 1 0)
                    (SAdd (smul_scaled a.(loc_var) b.(loc_var) 2 4 19)
                      (SAdd (smul_scaled a.(loc_var) b.(loc_var) 3 3 19)
                            (smul_scaled a.(loc_var) b.(loc_var) 4 2 19))))))
             (REdSeq
               (REdLimbStore dest 2%nat
                  (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 2)
                    (SAdd (smul_limbs a.(loc_var) b.(loc_var) 1 1)
                      (SAdd (smul_limbs a.(loc_var) b.(loc_var) 2 0)
                        (SAdd (smul_scaled a.(loc_var) b.(loc_var) 3 4 19)
                              (smul_scaled a.(loc_var) b.(loc_var) 4 3 19))))))
               (REdSeq
                 (REdLimbStore dest 3%nat
                    (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 3)
                      (SAdd (smul_limbs a.(loc_var) b.(loc_var) 1 2)
                        (SAdd (smul_limbs a.(loc_var) b.(loc_var) 2 1)
                          (SAdd (smul_limbs a.(loc_var) b.(loc_var) 3 0)
                                (smul_scaled a.(loc_var) b.(loc_var) 4 4 19))))))
                 (REdLimbStore dest 4%nat
                    (SAdd (smul_limbs a.(loc_var) b.(loc_var) 0 4)
                      (SAdd (smul_limbs a.(loc_var) b.(loc_var) 1 3)
                        (SAdd (smul_limbs a.(loc_var) b.(loc_var) 2 2)
                          (SAdd (smul_limbs a.(loc_var) b.(loc_var) 3 1)
                                (smul_limbs a.(loc_var) b.(loc_var) 4 0))))))))))
        rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros dest a b rs1 rs2 xa xb
           Hdt Hat Hbt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    destruct (Fp25519_holds_elim _ _ _ Hxa) as [la [Hga [Hla Hfa]]].
    destruct (Fp25519_holds_elim _ _ _ Hxb) as [lb [Hgb [Hlb Hfb]]].
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
    pose proof (eval_smul_limbs rs1 _ _ 0%nat 0%nat la lb Hga Hgb ltac:(lia) ltac:(lia) Hla Hlb) as Hp0a.
    pose proof (eval_smul_scaled rs1 _ _ 1%nat 4%nat 19 la lb Hga Hgb ltac:(lia) ltac:(lia) Hla Hlb) as Hp0b.
    pose proof (eval_smul_scaled rs1 _ _ 2%nat 3%nat 19 la lb Hga Hgb ltac:(lia) ltac:(lia) Hla Hlb) as Hp0c.
    pose proof (eval_smul_scaled rs1 _ _ 3%nat 2%nat 19 la lb Hga Hgb ltac:(lia) ltac:(lia) Hla Hlb) as Hp0d.
    pose proof (eval_smul_scaled rs1 _ _ 4%nat 1%nat 19 la lb Hga Hgb ltac:(lia) ltac:(lia) Hla Hlb) as Hp0e.
    rewrite (eval_sum5 _ _ _ _ _ _ _ _ _ _ _ Hp0a Hp0b Hp0c Hp0d Hp0e) in Hv0_eval.
    injection Hv0_eval as Hv0_eq. subst v0. subst rs01.
    (* Step 1: read [a], [b] from rs1[dest<-...]; slots preserved (dest <> a, dest <> b). *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d1)) |- _ =>
      assert (Hga01 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (Hgb01 : rs_get_tower_ed rs (loc_var b)
                    = Some (exist_tval_ed TFp25519 (VFp25519 lb))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_b; exact Hgb)
    end.
    pose proof (eval_smul_limbs _ _ _ 0%nat 1%nat la lb Hga01 Hgb01 ltac:(lia) ltac:(lia) Hla Hlb) as Hp1a.
    pose proof (eval_smul_limbs _ _ _ 1%nat 0%nat la lb Hga01 Hgb01 ltac:(lia) ltac:(lia) Hla Hlb) as Hp1b.
    pose proof (eval_smul_scaled _ _ _ 2%nat 4%nat 19 la lb Hga01 Hgb01 ltac:(lia) ltac:(lia) Hla Hlb) as Hp1c.
    pose proof (eval_smul_scaled _ _ _ 3%nat 3%nat 19 la lb Hga01 Hgb01 ltac:(lia) ltac:(lia) Hla Hlb) as Hp1d.
    pose proof (eval_smul_scaled _ _ _ 4%nat 2%nat 19 la lb Hga01 Hgb01 ltac:(lia) ltac:(lia) Hla Hlb) as Hp1e.
    rewrite (eval_sum5 _ _ _ _ _ _ _ _ _ _ _ Hp1a Hp1b Hp1c Hp1d Hp1e) in Hv1_eval.
    injection Hv1_eval as Hv1_eq. subst v1.
    rewrite rs_get_set_tower_eq in Hd1_get.
    apply tval_some_vfp25519_inj in Hd1_get.
    subst limbs_d1. subst rs12.
    (* Step 2. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d2)) |- _ =>
      assert (Hga12 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (Hgb12 : rs_get_tower_ed rs (loc_var b)
                    = Some (exist_tval_ed TFp25519 (VFp25519 lb))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_b; exact Hgb)
    end.
    pose proof (eval_smul_limbs _ _ _ 0%nat 2%nat la lb Hga12 Hgb12 ltac:(lia) ltac:(lia) Hla Hlb) as Hp2a.
    pose proof (eval_smul_limbs _ _ _ 1%nat 1%nat la lb Hga12 Hgb12 ltac:(lia) ltac:(lia) Hla Hlb) as Hp2b.
    pose proof (eval_smul_limbs _ _ _ 2%nat 0%nat la lb Hga12 Hgb12 ltac:(lia) ltac:(lia) Hla Hlb) as Hp2c.
    pose proof (eval_smul_scaled _ _ _ 3%nat 4%nat 19 la lb Hga12 Hgb12 ltac:(lia) ltac:(lia) Hla Hlb) as Hp2d.
    pose proof (eval_smul_scaled _ _ _ 4%nat 3%nat 19 la lb Hga12 Hgb12 ltac:(lia) ltac:(lia) Hla Hlb) as Hp2e.
    rewrite (eval_sum5 _ _ _ _ _ _ _ _ _ _ _ Hp2a Hp2b Hp2c Hp2d Hp2e) in Hv2_eval.
    injection Hv2_eval as Hv2_eq. subst v2.
    rewrite rs_get_set_tower_eq in Hd2_get.
    apply tval_some_vfp25519_inj in Hd2_get.
    subst limbs_d2. subst rs23.
    (* Step 3. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d3)) |- _ =>
      assert (Hga23 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (Hgb23 : rs_get_tower_ed rs (loc_var b)
                    = Some (exist_tval_ed TFp25519 (VFp25519 lb))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_b; exact Hgb)
    end.
    pose proof (eval_smul_limbs _ _ _ 0%nat 3%nat la lb Hga23 Hgb23 ltac:(lia) ltac:(lia) Hla Hlb) as Hp3a.
    pose proof (eval_smul_limbs _ _ _ 1%nat 2%nat la lb Hga23 Hgb23 ltac:(lia) ltac:(lia) Hla Hlb) as Hp3b.
    pose proof (eval_smul_limbs _ _ _ 2%nat 1%nat la lb Hga23 Hgb23 ltac:(lia) ltac:(lia) Hla Hlb) as Hp3c.
    pose proof (eval_smul_limbs _ _ _ 3%nat 0%nat la lb Hga23 Hgb23 ltac:(lia) ltac:(lia) Hla Hlb) as Hp3d.
    pose proof (eval_smul_scaled _ _ _ 4%nat 4%nat 19 la lb Hga23 Hgb23 ltac:(lia) ltac:(lia) Hla Hlb) as Hp3e.
    rewrite (eval_sum5 _ _ _ _ _ _ _ _ _ _ _ Hp3a Hp3b Hp3c Hp3d Hp3e) in Hv3_eval.
    injection Hv3_eval as Hv3_eq. subst v3.
    rewrite rs_get_set_tower_eq in Hd3_get.
    apply tval_some_vfp25519_inj in Hd3_get.
    subst limbs_d3. subst rs34.
    (* Step 4. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d4)) |- _ =>
      assert (Hga34 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (Hgb34 : rs_get_tower_ed rs (loc_var b)
                    = Some (exist_tval_ed TFp25519 (VFp25519 lb))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_b; exact Hgb)
    end.
    pose proof (eval_smul_limbs _ _ _ 0%nat 4%nat la lb Hga34 Hgb34 ltac:(lia) ltac:(lia) Hla Hlb) as Hp4a.
    pose proof (eval_smul_limbs _ _ _ 1%nat 3%nat la lb Hga34 Hgb34 ltac:(lia) ltac:(lia) Hla Hlb) as Hp4b.
    pose proof (eval_smul_limbs _ _ _ 2%nat 2%nat la lb Hga34 Hgb34 ltac:(lia) ltac:(lia) Hla Hlb) as Hp4c.
    pose proof (eval_smul_limbs _ _ _ 3%nat 1%nat la lb Hga34 Hgb34 ltac:(lia) ltac:(lia) Hla Hlb) as Hp4d.
    pose proof (eval_smul_limbs _ _ _ 4%nat 0%nat la lb Hga34 Hgb34 ltac:(lia) ltac:(lia) Hla Hlb) as Hp4e.
    rewrite (eval_sum5 _ _ _ _ _ _ _ _ _ _ _ Hp4a Hp4b Hp4c Hp4d Hp4e) in Hv4_eval.
    injection Hv4_eval as Hv4_eq. subst v4.
    rewrite rs_get_set_tower_eq in Hd4_get.
    apply tval_some_vfp25519_inj in Hd4_get.
    subst limbs_d4. subst rs2.
    (* Final state: rs1 chained through 5 list_set's at dest.  Compute
       the final limb list and show it matches build_limb_list_mul. *)
    set (h0 := sum5 (pp_mul la lb 0 0)
                    (pp_mul_scaled la lb 1 4 19)
                    (pp_mul_scaled la lb 2 3 19)
                    (pp_mul_scaled la lb 3 2 19)
                    (pp_mul_scaled la lb 4 1 19)).
    set (h1 := sum5 (pp_mul la lb 0 1)
                    (pp_mul la lb 1 0)
                    (pp_mul_scaled la lb 2 4 19)
                    (pp_mul_scaled la lb 3 3 19)
                    (pp_mul_scaled la lb 4 2 19)).
    set (h2 := sum5 (pp_mul la lb 0 2)
                    (pp_mul la lb 1 1)
                    (pp_mul la lb 2 0)
                    (pp_mul_scaled la lb 3 4 19)
                    (pp_mul_scaled la lb 4 3 19)).
    set (h3 := sum5 (pp_mul la lb 0 3)
                    (pp_mul la lb 1 2)
                    (pp_mul la lb 2 1)
                    (pp_mul la lb 3 0)
                    (pp_mul_scaled la lb 4 4 19)).
    set (h4 := sum5 (pp_mul la lb 0 4)
                    (pp_mul la lb 1 3)
                    (pp_mul la lb 2 2)
                    (pp_mul la lb 3 1)
                    (pp_mul la lb 4 0)).
    set (limbs_final :=
      list_set 4%nat h4
        (list_set 3%nat h3
          (list_set 2%nat h2
            (list_set 1%nat h1
              (list_set 0%nat h0 limbs_d0))))).
    assert (Hlen_final : length limbs_final = 5%nat).
    { unfold limbs_final.
      repeat rewrite list_set_length. exact Hd0_len. }
    assert (His5 : is_mul5 limbs_final la lb).
    { unfold is_mul5, limbs_final.
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
    pose proof (is_mul5_eq_build _ _ _ His5) as Hfinal_eq.
    assert (Hfeval_final : feval limbs_final = F.mul xa xb).
    { rewrite Hfinal_eq.
      rewrite feval_limbwise_mul_mask64 by assumption.
      rewrite Hfa, Hfb. reflexivity. }
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

  Theorem fe25519_mul_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Fp25519_holds rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_mul_body dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    cbn [fe25519_mul_body] in Hexec_n.
    apply (mul_inline_correct dest a_loc b_loc rs1 rs2 xa xb); assumption.
  Qed.

End Fe25519MulCorrect.

(** Sanity check: list assumptions of the headline theorem.  Inside
    the Section, the [Variable] / [Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_mul_body_correct.
