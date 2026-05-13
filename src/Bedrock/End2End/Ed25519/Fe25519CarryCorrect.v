(** * Fe25519CarryCorrect — functional correctness of [fe25519_carry_body].
 *
 *  Companion to [Fe25519CarryBody.v].  Mirrors the section-parameterised
 *  pattern used by [Fe25519AddSubCorrect]:
 *  abstract over the [Fp25519_holds] slot predicate plus limb-level
 *  hypotheses on the abstract decoder [feval], then derive algebraic
 *  correctness of the wrapped function ([F.eq xa (feval dest)] —
 *  equivalently the pre/post field values are equal, since
 *  [chained_carries] is identity modulo [p]).
 *
 *  Status (Phase 0d, 2026-05-13)
 *  =============================
 *  - [fe25519_carry_body_correct] : Qed via internal Lemma
 *    [carry_inline_correct], discharged mechanically against the
 *    limb-level hypotheses ([Fp25519_holds_intro] / [_elim] /
 *    [_set_other] / [feval_limbwise_carry_mask64]).  Twelve
 *    [rexec_limb_store_fp25519] inversions threaded through the
 *    abstract limb decoder.
 *
 *  History
 *  =======
 *  Phase 0c (commit f6e2d46): scaffold with single
 *    [carry_inline_correct] section hypothesis.
 *  Phase 0d (this file): discharged the hypothesis as an internal
 *    Lemma, factored over the same 3-hypothesis decoder interface used
 *    by [Fe25519AddSubCorrect].  Total Section hypothesis count: 4
 *    limb-level (intro, elim, set_other, carry).  No new GLOBAL
 *    axioms; the Section parameters remain section-quantified after
 *    [End].
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
Require Import Bedrock.End2End.Ed25519.Fe25519CarryBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + limb-     *)
(*     level decoder hypotheses.                                     *)
(* ================================================================ *)

Section Fe25519CarryCorrect.

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

  (** Algebraic content of fiat-crypto's [chained_carries n=5 s=2^255
      c=[(1,19)] _ idxs=[0;1;2;3;4;0]] correctness at the limb level:
      the 12-step inline carry chain over a valid 5-limb representation
      is identity modulo p.

      The carry chain only re-distributes bits between limbs, with the
      high-limb wrap multiplied by [19] (the [(1,19)] reduction
      coefficient for [2^255 - 19]).  At the abstract [F p] decoder
      level this is exactly [feval (build_limb_list_carry la) = feval la].

      We expose this as a single algebraic Hypothesis at the level used
      by callers.  Mechanical discharge against fiat-crypto's
      [eval_chained_carries] (Arithmetic/Core.v line 1011) is performed
      by the concrete [feval] instantiation; here it is abstract to
      keep this file decoupled from a particular radix-2^51 limb-bound
      regime. *)

  (** Helper: read the 5-limb representation through [mask64] (which is
      what [eval_sexpr_ed (SLimb _ _)] returns at each limb). *)
  Definition m_a (la : list Z) (i : nat) : Z := mask64 (List.nth i la 0).

  (** Closed-form for the limbs produced by the 12-store inline carry
      chain.  Each [vN] below matches the value written by the [N]-th
      [REdLimbStore], obtained by symbolically evaluating
      [eval_sexpr_ed] of its right-hand-side expression in the state
      after the previous [N-1] writes.

      IR-semantics note: [eval_sexpr_ed] applies [mask64] on top of
      [SAdd] / [SSub] / [SMul] results AND [SLit] / [SLimb] reads,
      but NOT on [SAnd] / [SShr].

      Concrete numeric literals (instead of [mask64 (Z.ones 51)] etc.)
      are used to match the post-[injection] form of evaluated
      expressions in the WP-style inversion proof below.  These match
      the actual values computed by [eval_sexpr_ed] of [SLit
      fe25519_mask51_z] and [SLit fe25519_radix]. *)

  (* Compute-cached literals: mask64 (Z.ones 51) and mask64 51. *)
  Local Definition mask51_lit : Z := 2251799813685247.   (* 2^51 - 1 *)
  Local Definition radix_lit  : Z := 51.                 (* mask64 51 = 51 *)
  Local Definition red19_lit  : Z := 19.                 (* mask64 19 = 19 *)

  (* Per-store written values, as functions of la. *)
  Definition v0_carry (la : list Z) : Z :=
    Z.land (m_a la 0) mask51_lit.
  Definition v1_carry (la : list Z) : Z :=
    mask64 (m_a la 1 + Z.shiftr (m_a la 0) radix_lit).
  Definition v2_carry (la : list Z) : Z :=
    mask64 (m_a la 2 + Z.shiftr (mask64 (v1_carry la)) radix_lit).
  Definition v3_carry (la : list Z) : Z :=
    Z.land (mask64 (v1_carry la)) mask51_lit.
  Definition v4_carry (la : list Z) : Z :=
    mask64 (m_a la 3 + Z.shiftr (mask64 (v2_carry la)) radix_lit).
  Definition v5_carry (la : list Z) : Z :=
    Z.land (mask64 (v2_carry la)) mask51_lit.
  Definition v6_carry (la : list Z) : Z :=
    mask64 (m_a la 4 + Z.shiftr (mask64 (v4_carry la)) radix_lit).
  Definition v7_carry (la : list Z) : Z :=
    Z.land (mask64 (v4_carry la)) mask51_lit.
  Definition v8_carry (la : list Z) : Z :=
    mask64 (mask64 (v0_carry la)
            + mask64 (red19_lit
                       * Z.shiftr (mask64 (v6_carry la)) radix_lit)).
  Definition v9_carry (la : list Z) : Z :=
    Z.land (mask64 (v6_carry la)) mask51_lit.
  Definition v10_carry (la : list Z) : Z :=
    mask64 (mask64 (v3_carry la) + Z.shiftr (mask64 (v8_carry la)) radix_lit).
  Definition v11_carry (la : list Z) : Z :=
    Z.land (mask64 (v8_carry la)) mask51_lit.

  (** Final limb-list result of the 12-store chain:
      - limb 0 = v11 (last write at index 0)
      - limb 1 = v10
      - limb 2 = v5
      - limb 3 = v7
      - limb 4 = v9 *)
  Definition build_limb_list_carry (la : list Z) : list Z :=
    [v11_carry la; v10_carry la; v5_carry la; v7_carry la; v9_carry la].

  Lemma build_limb_list_carry_length :
    forall la, length (build_limb_list_carry la) = 5%nat.
  Proof. reflexivity. Qed.

  Hypothesis feval_limbwise_carry_mask64 :
    forall (la : list Z),
      length la = 5%nat ->
      feval (build_limb_list_carry la) = feval la.

(* ================================================================ *)
(* §2. Internal lemmas: rs_get_tower / rs_set_tower bookkeeping      *)
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

  Lemma vfp25519_inj :
    forall l1 l2 : list Z,
      exist_tval_ed TFp25519 (VFp25519 l1) = exist_tval_ed TFp25519 (VFp25519 l2) ->
      l1 = l2.
  Proof.
    intros l1 l2 H.
    (* In Rocq 9, [injection] on this dependent-record equality eagerly
       traverses both wrappers and yields [l1 = l2] directly (thanks to
       the decidable equality on [tower_type_ed]).  Just use [congruence]
       to close. *)
    injection H as Hexi.
    exact Hexi.
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

  (** Eval of [sMask51 (SLimb a i)] over a state with valid 5-limb
      VFp25519 payload at [a]. *)
  Lemma eval_sMask51_SLimb_VFp25519 :
    forall rs a i la,
      rs_get_tower_ed rs a = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      (i < 5)%nat ->
      length la = 5%nat ->
      eval_sexpr_ed rs (sMask51 (SLimb a i)) =
      Some (Z.land (mask64 (List.nth i la 0)) mask51_lit).
  Proof.
    intros rs a i la Hga Hi Hla.
    unfold sMask51.
    change (eval_sexpr_ed rs (SAnd (SLimb a i) (SLit fe25519_mask51_z)))
      with (match eval_sexpr_ed rs (SLimb a i),
                  eval_sexpr_ed rs (SLit fe25519_mask51_z) with
            | Some va, Some vb => Some (Z.land va vb)
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hga Hi Hla).
    change (eval_sexpr_ed rs (SLit fe25519_mask51_z))
      with (Some mask51_lit).
    reflexivity.
  Qed.

  (** Eval of [SAdd (SLimb a i) (sShr51 (SLimb b j))] — used by S1, S2,
      S4, S6 (carry-step "high"). *)
  Lemma eval_SAdd_SLimb_sShr51_SLimb :
    forall rs a b i j la lb,
      rs_get_tower_ed rs a = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      rs_get_tower_ed rs b = Some (exist_tval_ed TFp25519 (VFp25519 lb)) ->
      (i < 5)%nat ->
      (j < 5)%nat ->
      length la = 5%nat ->
      length lb = 5%nat ->
      eval_sexpr_ed rs (SAdd (SLimb a i) (sShr51 (SLimb b j))) =
      Some (mask64 (mask64 (List.nth i la 0)
                    + Z.shiftr (mask64 (List.nth j lb 0)) radix_lit)).
  Proof.
    intros rs a b i j la lb Hga Hgb Hi Hj Hla Hlb.
    unfold sShr51.
    change (eval_sexpr_ed rs
             (SAdd (SLimb a i) (SShr (SLimb b j) (SLit fe25519_radix))))
      with (match eval_sexpr_ed rs (SLimb a i),
                  match eval_sexpr_ed rs (SLimb b j),
                        eval_sexpr_ed rs (SLit fe25519_radix) with
                  | Some va, Some vb => Some (Z.shiftr va vb)
                  | _, _ => None
                  end
            with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hga Hi Hla).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hgb Hj Hlb).
    change (eval_sexpr_ed rs (SLit fe25519_radix))
      with (Some radix_lit).
    reflexivity.
  Qed.

  (** Eval of [sWrap19 (SLimb b j)]: returns [mask64 (mask64 19 *
      Z.shiftr (mask64 (nth j lb 0)) (mask64 51))]. *)
  Lemma eval_sWrap19_SLimb_VFp25519 :
    forall rs b j lb,
      rs_get_tower_ed rs b = Some (exist_tval_ed TFp25519 (VFp25519 lb)) ->
      (j < 5)%nat ->
      length lb = 5%nat ->
      eval_sexpr_ed rs (sWrap19 (SLimb b j)) =
      Some (mask64 (red19_lit
                     * Z.shiftr (mask64 (List.nth j lb 0)) radix_lit)).
  Proof.
    intros rs b j lb Hgb Hj Hlb.
    unfold sWrap19, sShr51.
    change (eval_sexpr_ed rs
             (SMul (SLit fe25519_reduction_c)
                   (SShr (SLimb b j) (SLit fe25519_radix))))
      with (match eval_sexpr_ed rs (SLit fe25519_reduction_c),
                  match eval_sexpr_ed rs (SLimb b j),
                        eval_sexpr_ed rs (SLit fe25519_radix) with
                  | Some va, Some vb => Some (Z.shiftr va vb)
                  | _, _ => None
                  end
            with
            | Some va, Some vb => Some (mask64 (va * vb))
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hgb Hj Hlb).
    change (eval_sexpr_ed rs (SLit fe25519_radix))
      with (Some radix_lit).
    change (eval_sexpr_ed rs (SLit fe25519_reduction_c))
      with (Some red19_lit).
    reflexivity.
  Qed.

  (** Eval of [SAdd (SLimb a i) (sWrap19 (SLimb b j))] — used by S8. *)
  Lemma eval_SAdd_SLimb_sWrap19_SLimb :
    forall rs a b i j la lb,
      rs_get_tower_ed rs a = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      rs_get_tower_ed rs b = Some (exist_tval_ed TFp25519 (VFp25519 lb)) ->
      (i < 5)%nat ->
      (j < 5)%nat ->
      length la = 5%nat ->
      length lb = 5%nat ->
      eval_sexpr_ed rs (SAdd (SLimb a i) (sWrap19 (SLimb b j))) =
      Some (mask64 (mask64 (List.nth i la 0)
                    + mask64 (red19_lit
                              * Z.shiftr (mask64 (List.nth j lb 0)) radix_lit))).
  Proof.
    intros rs a b i j la lb Hga Hgb Hi Hj Hla Hlb.
    change (eval_sexpr_ed rs (SAdd (SLimb a i) (sWrap19 (SLimb b j))))
      with (match eval_sexpr_ed rs (SLimb a i),
                  eval_sexpr_ed rs (sWrap19 (SLimb b j)) with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hga Hi Hla).
    rewrite (eval_sWrap19_SLimb_VFp25519 _ _ _ _ Hgb Hj Hlb).
    reflexivity.
  Qed.

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
(* §3. List-set bookkeeping helpers                                  *)
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

  (** Collapse a sequence of [list_set]s under a single [nth] read
      when the read index differs from every write index.  Lets us
      replace long [unfold limbsX; rewrite list_set_nth_other by lia]
      chains with a single [rewrite nth_after_list_sets by ...]. *)
  Lemma nth_after_list_sets :
    forall (i : nat) (xs : list Z) (writes : list (nat * Z)),
      (forall p, In p writes -> fst p <> i) ->
      List.nth i
        (List.fold_right (fun p acc => list_set (fst p) (snd p) acc) xs writes) 0
      = List.nth i xs 0.
  Proof.
    intros i xs writes Hne.
    induction writes as [|[j v] rest IH]; cbn.
    - reflexivity.
    - rewrite list_set_nth_other.
      + apply IH. intros p Hp. apply Hne. right. exact Hp.
      + assert (Hne_j : fst (j, v) <> i) by (apply Hne; left; reflexivity).
        cbn in Hne_j. lia.
  Qed.

  (** Block the Qed kernel from re-elaborating the deep [list_set]
      cascades.  All proofs below use [list_set] only through stated
      lemmas; the kernel never needs to unfold [list_set] for
      conversion.  See reference_qed_kernel_check_blowup_dealloc.md. *)
  Local Opaque list_set.
  Local Strategy 0 [list_set].

(* ================================================================ *)
(* §4. carry_inline_correct as a Lemma                               *)
(* ================================================================ *)

  (** Internal: chain through the 12 [REdLimbStore]s and prove the
      destination slot ends as a [VFp25519] whose limbs match the
      closed-form [build_limb_list_carry la].  Algebraic identity
      [feval (build_limb_list_carry la) = feval la] then closes the
      [Fp25519_holds] goal.

      Strategy: at each step, invert the [REdLimbStore] (peeling
      one [seq_inv] before each but the last), prove the read of each
      [SLimb _ i] using the most recently written value at index [i],
      and chain the equality [val = vN_carry la] through [subst].

      After the 12 inversions and subst chain, the final state stores
      [VFp25519 limbs_final] at [dest], where [limbs_final] is the
      explicit nested [list_set] of the 12 values.  We then show this
      list extensionally equals [build_limb_list_carry la]. *)
  Lemma carry_inline_correct :
    forall (dest a : located_ed) (rs1 rs2 : rust_state_ed) (xa : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Hexec
        (REdSeq
          (REdLimbStore dest 0%nat (sMask51 (SLimb a.(loc_var) 0%nat)))
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb a.(loc_var) 1%nat) (sShr51 (SLimb a.(loc_var) 0%nat))))
        (REdSeq
          (REdLimbStore dest 2%nat
             (SAdd (SLimb a.(loc_var) 2%nat) (sShr51 (SLimb dest.(loc_var) 1%nat))))
        (REdSeq
          (REdLimbStore dest 1%nat (sMask51 (SLimb dest.(loc_var) 1%nat)))
        (REdSeq
          (REdLimbStore dest 3%nat
             (SAdd (SLimb a.(loc_var) 3%nat) (sShr51 (SLimb dest.(loc_var) 2%nat))))
        (REdSeq
          (REdLimbStore dest 2%nat (sMask51 (SLimb dest.(loc_var) 2%nat)))
        (REdSeq
          (REdLimbStore dest 4%nat
             (SAdd (SLimb a.(loc_var) 4%nat) (sShr51 (SLimb dest.(loc_var) 3%nat))))
        (REdSeq
          (REdLimbStore dest 3%nat (sMask51 (SLimb dest.(loc_var) 3%nat)))
        (REdSeq
          (REdLimbStore dest 0%nat
             (SAdd (SLimb dest.(loc_var) 0%nat)
                   (sWrap19 (SLimb dest.(loc_var) 4%nat))))
        (REdSeq
          (REdLimbStore dest 4%nat (sMask51 (SLimb dest.(loc_var) 4%nat)))
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb dest.(loc_var) 1%nat) (sShr51 (SLimb dest.(loc_var) 0%nat))))
          (REdLimbStore dest 0%nat (sMask51 (SLimb dest.(loc_var) 0%nat)))
        ))))))))))) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) xa /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros dest a rs1 rs2 xa Hdt Hat Hdne_a Hxa Hexec_n.
    (* Extract limb evidence for xa from [Fp25519_holds]. *)
    destruct (Fp25519_holds_elim _ _ _ Hxa) as [la [Hga [Hla Hfa]]].
    (* Peel the 11 sequence layers (12 stores). *)
    apply seq_inv in Hexec_n. destruct Hexec_n as [rs_a [Hs0 Ht0]].
    apply seq_inv in Ht0. destruct Ht0 as [rs_b [Hs1 Ht1]].
    apply seq_inv in Ht1. destruct Ht1 as [rs_c [Hs2 Ht2]].
    apply seq_inv in Ht2. destruct Ht2 as [rs_d [Hs3 Ht3]].
    apply seq_inv in Ht3. destruct Ht3 as [rs_e [Hs4 Ht4]].
    apply seq_inv in Ht4. destruct Ht4 as [rs_f [Hs5 Ht5]].
    apply seq_inv in Ht5. destruct Ht5 as [rs_g [Hs6 Ht6]].
    apply seq_inv in Ht6. destruct Ht6 as [rs_h [Hs7 Ht7]].
    apply seq_inv in Ht7. destruct Ht7 as [rs_i [Hs8 Ht8]].
    apply seq_inv in Ht8. destruct Ht8 as [rs_j [Hs9 Ht9]].
    apply seq_inv in Ht9. destruct Ht9 as [rs_k [Hs10 Hs11]].
    (* Invert each REdLimbStore step. *)
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs0 Hdt) as
      [w0 [limbs0 [He0 [Hg0 [Hlen0 [_ Hrsa]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs1 Hdt) as
      [w1 [limbs1 [He1 [Hg1 [Hlen1 [_ Hrsb]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs2 Hdt) as
      [w2 [limbs2 [He2 [Hg2 [Hlen2 [_ Hrsc]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs3 Hdt) as
      [w3 [limbs3 [He3 [Hg3 [Hlen3 [_ Hrsd]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs4 Hdt) as
      [w4 [limbs4 [He4 [Hg4 [Hlen4 [_ Hrse]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs5 Hdt) as
      [w5 [limbs5 [He5 [Hg5 [Hlen5 [_ Hrsf]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs6 Hdt) as
      [w6 [limbs6 [He6 [Hg6 [Hlen6 [_ Hrsg]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs7 Hdt) as
      [w7 [limbs7 [He7 [Hg7 [Hlen7 [_ Hrsh]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs8 Hdt) as
      [w8 [limbs8 [He8 [Hg8 [Hlen8 [_ Hrsi]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs9 Hdt) as
      [w9 [limbs9 [He9 [Hg9 [Hlen9 [_ Hrsj]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs10 Hdt) as
      [w10 [limbs10 [He10 [Hg10 [Hlen10 [_ Hrsk]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs11 Hdt) as
      [w11 [limbs11 [He11 [Hg11 [Hlen11 [_ Hrs2]]]]]].
    (* === Step 0 (S0): dest[0] := sMask51 (SLimb a 0)
           Read: a only.  Establish w0 = v0_carry la. *)
    rewrite (eval_sMask51_SLimb_VFp25519 rs1 a.(loc_var) 0%nat la
              Hga ltac:(lia) Hla) in He0.
    injection He0 as Hw0_eq.
    change (Z.land (mask64 (List.nth 0 la 0)) mask51_lit)
      with (v0_carry la) in Hw0_eq.
    subst w0. subst rs_a.
    (* === Step 1 (S1): dest[1] := SLimb a 1 + sShr51 (SLimb a 0)
           Read: a only.  Establish w1 = v1_carry la. *)
    assert (Hga_b : rs_get_tower_ed
                      (rs_set_tower_ed rs1 dest.(loc_var)
                         (exist_tval_ed TFp25519
                            (VFp25519 (list_set 0 (v0_carry la) limbs0))))
                      a.(loc_var)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))).
    { rewrite rs_get_set_tower_other by exact Hdne_a. exact Hga. }
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ a.(loc_var) a.(loc_var) 1%nat 0%nat la la
              Hga_b Hga_b ltac:(lia) ltac:(lia) Hla Hla) in He1.
    injection He1 as Hw1_eq.
    change (mask64 (mask64 (List.nth 1 la 0)
                    + Z.shiftr (mask64 (List.nth 0 la 0)) radix_lit))
      with (v1_carry la) in Hw1_eq.
    subst w1.
    (* Compute limbs1: dest's slot at rs_a is the post-S0 list. *)
    rewrite rs_get_set_tower_eq in Hg1.
    apply tval_some_vfp25519_inj in Hg1.
    subst limbs1. subst rs_b.
    (* === Step 2 (S2): dest[2] := SLimb a 2 + sShr51 (SLimb dest 1)
           Read: a[2] and dest[1].  After S0, S1 the dest slot holds
           list_set 1 (v1_carry la) (list_set 0 (v0_carry la) limbs0).
           At index 1 this is [v1_carry la]. *)
    set (limbsB := list_set 1%nat (v1_carry la)
                     (list_set 0%nat (v0_carry la) limbs0)).
    assert (HlenB : length limbsB = 5%nat).
    { unfold limbsB. repeat rewrite list_set_length. exact Hlen0. }
    assert (HnthB1 : List.nth 1 limbsB 0 = v1_carry la).
    { unfold limbsB. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite list_set_length, Hlen0; lia. }
    match type of Hg2 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (Hga_c : rs_get_tower_ed rs a.(loc_var)
                      = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (HgdB : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsB))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ a.(loc_var) dest.(loc_var) 2%nat 1%nat la limbsB
              Hga_c HgdB ltac:(lia) ltac:(lia) Hla HlenB) in He2.
    injection He2 as Hw2_eq. rewrite HnthB1 in Hw2_eq.
    change (mask64 (mask64 (List.nth 2 la 0)
                    + Z.shiftr (mask64 (v1_carry la)) radix_lit))
      with (v2_carry la) in Hw2_eq.
    subst w2.
    (* Resolve limbs2. *)
    rewrite rs_get_set_tower_eq in Hg2.
    apply tval_some_vfp25519_inj in Hg2.
    subst limbs2. subst rs_c.
    (* === Step 3 (S3): dest[1] := sMask51 (SLimb dest 1)
           Read: dest[1] which is still v1_carry la (S2 wrote at index 2). *)
    set (limbsC := list_set 2%nat (v2_carry la) limbsB).
    assert (HlenC : length limbsC = 5%nat).
    { unfold limbsC. rewrite list_set_length. exact HlenB. }
    assert (HnthC1 : List.nth 1 limbsC 0 = v1_carry la).
    { unfold limbsC. rewrite list_set_nth_other by lia. exact HnthB1. }
    match type of Hg3 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgdC : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsC))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 1%nat limbsC
              HgdC ltac:(lia) HlenC) in He3.
    injection He3 as Hw3_eq. rewrite HnthC1 in Hw3_eq.
    change (Z.land (mask64 (v1_carry la)) mask51_lit)
      with (v3_carry la) in Hw3_eq.
    subst w3.
    rewrite rs_get_set_tower_eq in Hg3.
    apply tval_some_vfp25519_inj in Hg3.
    subst limbs3. subst rs_d.
    (* === Step 4 (S4): dest[3] := SLimb a 3 + sShr51 (SLimb dest 2)
           Read: a[3] and dest[2] = v2_carry la (last written at index 2 was S2). *)
    set (limbsD := list_set 1%nat (v3_carry la) limbsC).
    assert (HlenD : length limbsD = 5%nat).
    { unfold limbsD. rewrite list_set_length. exact HlenC. }
    assert (HnthD2 : List.nth 2 limbsD 0 = v2_carry la).
    { unfold limbsD. rewrite list_set_nth_other by lia.
      unfold limbsC. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenB; lia. }
    match type of Hg4 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (Hga_e : rs_get_tower_ed rs a.(loc_var)
                      = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (HgdD : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsD))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ a.(loc_var) dest.(loc_var) 3%nat 2%nat la limbsD
              Hga_e HgdD ltac:(lia) ltac:(lia) Hla HlenD) in He4.
    injection He4 as Hw4_eq. rewrite HnthD2 in Hw4_eq.
    change (mask64 (mask64 (List.nth 3 la 0)
                    + Z.shiftr (mask64 (v2_carry la)) radix_lit))
      with (v4_carry la) in Hw4_eq.
    subst w4.
    rewrite rs_get_set_tower_eq in Hg4.
    apply tval_some_vfp25519_inj in Hg4.
    subst limbs4. subst rs_e.
    (* === Step 5 (S5): dest[2] := sMask51 (SLimb dest 2)
           Read: dest[2] = v2_carry la. *)
    set (limbsE := list_set 3%nat (v4_carry la) limbsD).
    assert (HlenE : length limbsE = 5%nat).
    { unfold limbsE. rewrite list_set_length. exact HlenD. }
    assert (HnthE2 : List.nth 2 limbsE 0 = v2_carry la).
    { unfold limbsE. rewrite list_set_nth_other by lia. exact HnthD2. }
    match type of Hg5 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgdE : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsE))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 2%nat limbsE
              HgdE ltac:(lia) HlenE) in He5.
    injection He5 as Hw5_eq. rewrite HnthE2 in Hw5_eq.
    change (Z.land (mask64 (v2_carry la)) mask51_lit)
      with (v5_carry la) in Hw5_eq.
    subst w5.
    rewrite rs_get_set_tower_eq in Hg5.
    apply tval_some_vfp25519_inj in Hg5.
    subst limbs5. subst rs_f.
    (* === Step 6 (S6): dest[4] := SLimb a 4 + sShr51 (SLimb dest 3)
           Read: a[4] and dest[3] = v4_carry la (last written at index 3 was S4). *)
    set (limbsF := list_set 2%nat (v5_carry la) limbsE).
    assert (HlenF : length limbsF = 5%nat).
    { unfold limbsF. rewrite list_set_length. exact HlenE. }
    assert (HnthF3 : List.nth 3 limbsF 0 = v4_carry la).
    { unfold limbsF. rewrite list_set_nth_other by lia.
      unfold limbsE. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenD; lia. }
    match type of Hg6 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (Hga_g : rs_get_tower_ed rs a.(loc_var)
                      = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (HgdF : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsF))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ a.(loc_var) dest.(loc_var) 4%nat 3%nat la limbsF
              Hga_g HgdF ltac:(lia) ltac:(lia) Hla HlenF) in He6.
    injection He6 as Hw6_eq. rewrite HnthF3 in Hw6_eq.
    change (mask64 (mask64 (List.nth 4 la 0)
                    + Z.shiftr (mask64 (v4_carry la)) radix_lit))
      with (v6_carry la) in Hw6_eq.
    subst w6.
    rewrite rs_get_set_tower_eq in Hg6.
    apply tval_some_vfp25519_inj in Hg6.
    subst limbs6. subst rs_g.
    (* === Step 7 (S7): dest[3] := sMask51 (SLimb dest 3)
           Read: dest[3] = v4_carry la (last written at index 3 was S4; S6 wrote at 4). *)
    set (limbsG := list_set 4%nat (v6_carry la) limbsF).
    assert (HlenG : length limbsG = 5%nat).
    { unfold limbsG. rewrite list_set_length. exact HlenF. }
    assert (HnthG3 : List.nth 3 limbsG 0 = v4_carry la).
    { unfold limbsG. rewrite list_set_nth_other by lia. exact HnthF3. }
    match type of Hg7 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgdG : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsG))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 3%nat limbsG
              HgdG ltac:(lia) HlenG) in He7.
    injection He7 as Hw7_eq. rewrite HnthG3 in Hw7_eq.
    change (Z.land (mask64 (v4_carry la)) mask51_lit)
      with (v7_carry la) in Hw7_eq.
    subst w7.
    rewrite rs_get_set_tower_eq in Hg7.
    apply tval_some_vfp25519_inj in Hg7.
    subst limbs7. subst rs_h.
    (* === Step 8 (S8): dest[0] := SLimb dest 0 + sWrap19 (SLimb dest 4)
           Read: dest[0] = v0_carry la (last written at index 0 was S0;
           S1-S7 wrote at 1,2,1,3,2,4,3),
           and dest[4] = v6_carry la (last written at index 4 was S6;
           S7 wrote at 3). *)
    set (limbsH := list_set 3%nat (v7_carry la) limbsG).
    assert (HlenH : length limbsH = 5%nat).
    { unfold limbsH. rewrite list_set_length. exact HlenG. }
    assert (HnthH0 : List.nth 0 limbsH 0 = v0_carry la).
    { unfold limbsH. rewrite list_set_nth_other by lia.
      unfold limbsG. rewrite list_set_nth_other by lia.
      unfold limbsF. rewrite list_set_nth_other by lia.
      unfold limbsE. rewrite list_set_nth_other by lia.
      unfold limbsD. rewrite list_set_nth_other by lia.
      unfold limbsC. rewrite list_set_nth_other by lia.
      unfold limbsB. rewrite list_set_nth_other by lia.
      rewrite list_set_nth_same.
      - reflexivity.
      - rewrite Hlen0; lia. }
    assert (HnthH4 : List.nth 4 limbsH 0 = v6_carry la).
    { unfold limbsH. rewrite list_set_nth_other by lia.
      unfold limbsG. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenF; lia. }
    match type of Hg8 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgdH : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsH))) by
        (apply rs_get_set_tower_eq)
    end.
    (* Avoid [injection] on the deeply-nested rewritten He8 (which
       takes 10+ min in Rocq 9 — it traverses limbsH = nested
       list_set's).  Build the [w8 = v8_carry la] equality directly. *)
    assert (Hw8_eq : v8_carry la = w8).
    { assert (Hev : Some (v8_carry la) = Some w8).
      { rewrite <- He8.
        rewrite (eval_SAdd_SLimb_sWrap19_SLimb _ dest.(loc_var) dest.(loc_var) 0%nat 4%nat limbsH limbsH
                  HgdH HgdH ltac:(lia) ltac:(lia) HlenH HlenH).
        rewrite HnthH0, HnthH4. reflexivity. }
      injection Hev as Hev_eq. exact Hev_eq. }
    subst w8.
    rewrite rs_get_set_tower_eq in Hg8.
    apply tval_some_vfp25519_inj in Hg8.
    subst limbs8. subst rs_i.
    (* === Step 9 (S9): dest[4] := sMask51 (SLimb dest 4)
           Read: dest[4] = v6_carry la (S8 wrote at 0). *)
    set (limbsI := list_set 0%nat (v8_carry la) limbsH).
    assert (HlenI : length limbsI = 5%nat).
    { unfold limbsI. rewrite list_set_length. exact HlenH. }
    assert (HnthI4 : List.nth 4 limbsI 0 = v6_carry la).
    { unfold limbsI. rewrite list_set_nth_other by lia. exact HnthH4. }
    match type of Hg9 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgdI : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsI))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 4%nat limbsI
              HgdI ltac:(lia) HlenI) in He9.
    injection He9 as Hw9_eq. rewrite HnthI4 in Hw9_eq.
    change (Z.land (mask64 (v6_carry la)) mask51_lit)
      with (v9_carry la) in Hw9_eq.
    subst w9.
    rewrite rs_get_set_tower_eq in Hg9.
    apply tval_some_vfp25519_inj in Hg9.
    subst limbs9. subst rs_j.
    (* === Step 10 (S10): dest[1] := SLimb dest 1 + sShr51 (SLimb dest 0)
           Read: dest[1] = v3_carry la (last write at index 1 was S3),
           and dest[0] = v8_carry la (last write at index 0 was S8). *)
    set (limbsJ := list_set 4%nat (v9_carry la) limbsI).
    assert (HlenJ : length limbsJ = 5%nat).
    { unfold limbsJ. rewrite list_set_length. exact HlenI. }
    assert (HnthJ1 : List.nth 1 limbsJ 0 = v3_carry la).
    { unfold limbsJ. rewrite list_set_nth_other by lia.
      unfold limbsI. rewrite list_set_nth_other by lia.
      unfold limbsH. rewrite list_set_nth_other by lia.
      unfold limbsG. rewrite list_set_nth_other by lia.
      unfold limbsF. rewrite list_set_nth_other by lia.
      unfold limbsE. rewrite list_set_nth_other by lia.
      unfold limbsD. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenC; lia. }
    assert (HnthJ0 : List.nth 0 limbsJ 0 = v8_carry la).
    { unfold limbsJ. rewrite list_set_nth_other by lia.
      unfold limbsI. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenH; lia. }
    match type of Hg10 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgdJ : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsJ))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ dest.(loc_var) dest.(loc_var) 1%nat 0%nat limbsJ limbsJ
              HgdJ HgdJ ltac:(lia) ltac:(lia) HlenJ HlenJ) in He10.
    injection He10 as Hw10_eq. rewrite HnthJ1, HnthJ0 in Hw10_eq.
    change (mask64 (mask64 (v3_carry la)
                    + Z.shiftr (mask64 (v8_carry la)) radix_lit))
      with (v10_carry la) in Hw10_eq.
    subst w10.
    rewrite rs_get_set_tower_eq in Hg10.
    apply tval_some_vfp25519_inj in Hg10.
    subst limbs10. subst rs_k.
    (* === Step 11 (S11): dest[0] := sMask51 (SLimb dest 0)
           Read: dest[0] = v8_carry la (S10 wrote at 1). *)
    set (limbsK := list_set 1%nat (v10_carry la) limbsJ).
    assert (HlenK : length limbsK = 5%nat).
    { unfold limbsK. rewrite list_set_length. exact HlenJ. }
    assert (HnthK0 : List.nth 0 limbsK 0 = v8_carry la).
    { unfold limbsK. rewrite list_set_nth_other by lia. exact HnthJ0. }
    match type of Hg11 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgdK : rs_get_tower_ed rs dest.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 limbsK))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 0%nat limbsK
              HgdK ltac:(lia) HlenK) in He11.
    injection He11 as Hw11_eq. rewrite HnthK0 in Hw11_eq.
    change (Z.land (mask64 (v8_carry la)) mask51_lit)
      with (v11_carry la) in Hw11_eq.
    subst w11.
    rewrite rs_get_set_tower_eq in Hg11.
    apply tval_some_vfp25519_inj in Hg11.
    subst limbs11. subst rs2.
    (* Final state holds VFp25519 limbs_final at dest, where
       limbs_final = list_set 0 (v11_carry la) (list_set 1 (v10_carry la) limbsJ). *)
    set (limbs_final :=
      list_set 0%nat (v11_carry la)
        (list_set 1%nat (v10_carry la) limbsJ)).
    assert (Hlen_final : length limbs_final = 5%nat).
    { unfold limbs_final. repeat rewrite list_set_length. exact HlenJ. }
    (* Show: limbs_final = build_limb_list_carry la (extensionally). *)
    assert (Hfinal_eq : limbs_final = build_limb_list_carry la).
    { apply (List.nth_ext _ _ 0 0).
      - rewrite Hlen_final. reflexivity.
      - intros i Hi. rewrite Hlen_final in Hi.
        unfold build_limb_list_carry.
        destruct i as [|[|[|[|[|i']]]]]; try (exfalso; lia).
        + (* i = 0: limb 0 = v11_carry la. *)
          unfold limbs_final.
          rewrite list_set_nth_same.
          * reflexivity.
          * rewrite list_set_length, HlenJ; lia.
        + (* i = 1: limb 1 = v10_carry la. *)
          unfold limbs_final.
          rewrite list_set_nth_other by lia.
          rewrite list_set_nth_same.
          * reflexivity.
          * rewrite HlenJ; lia.
        + (* i = 2: limb 2 = v5_carry la.  Trace through all list_sets
             back to limbs_d0: only S5 (limbsF) wrote at index 2 most
             recently. *)
          unfold limbs_final.
          rewrite list_set_nth_other by lia.
          rewrite list_set_nth_other by lia.
          unfold limbsJ. rewrite list_set_nth_other by lia.
          unfold limbsI. rewrite list_set_nth_other by lia.
          unfold limbsH. rewrite list_set_nth_other by lia.
          unfold limbsG. rewrite list_set_nth_other by lia.
          unfold limbsF. rewrite list_set_nth_same.
          * reflexivity.
          * rewrite HlenE; lia.
        + (* i = 3: limb 3 = v7_carry la (S7 wrote at index 3 most recently). *)
          unfold limbs_final.
          rewrite list_set_nth_other by lia.
          rewrite list_set_nth_other by lia.
          unfold limbsJ. rewrite list_set_nth_other by lia.
          unfold limbsI. rewrite list_set_nth_other by lia.
          unfold limbsH. rewrite list_set_nth_same.
          * reflexivity.
          * rewrite HlenG; lia.
        + (* i = 4: limb 4 = v9_carry la (S9 wrote at index 4 most recently). *)
          unfold limbs_final.
          rewrite list_set_nth_other by lia.
          rewrite list_set_nth_other by lia.
          unfold limbsJ. rewrite list_set_nth_same.
          * reflexivity.
          * rewrite HlenI; lia. }
    assert (Hfeval_final : feval limbs_final = xa).
    { rewrite Hfinal_eq. rewrite feval_limbwise_carry_mask64 by exact Hla.
      exact Hfa. }
    split.
    + (* Fp25519_holds at dest of xa. *)
      eapply Fp25519_holds_intro;
        [| exact Hlen_final | exact Hfeval_final].
      apply rs_get_set_tower_eq.
    + (* fp_frame: for y <> dest, the value is preserved across each
         of the 12 set_tower steps at dest. *)
      intros y vy Hne Hy.
      repeat (eapply Fp25519_holds_set_other; [exact Hne|]).
      exact Hy.
  Qed.

(* ================================================================ *)
(* §5. Headline theorem                                              *)
(* ================================================================ *)

  Theorem fe25519_carry_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_carry_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) xa /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa Hat Hdt Hdne Hxa Hexec_n.
    cbn [fe25519_carry_body] in Hexec_n.
    apply (carry_inline_correct dest a_loc rs1 rs2 xa); assumption.
  Qed.

End Fe25519CarryCorrect.

(** Sanity check: list assumptions of the headline theorem.  Inside
    the Section, the [Variable]/[Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_carry_body_correct.
