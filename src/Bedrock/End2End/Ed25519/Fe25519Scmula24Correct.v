(** * Fe25519Scmula24Correct — functional correctness of
 *  [fe25519_scmula24_body].
 *
 *  Companion to [Fe25519Scmula24Body.v].  Mirrors the
 *  section-parameterised pattern used by [Fe25519CarryCorrect] /
 *  [Fe25519AddSubCorrect]: abstract over the [Fp25519_holds] slot
 *  predicate plus three limb-level decoder hypotheses
 *  ([Fp25519_holds_intro] / [_elim] / [_set_other]) and a single
 *  algebraic identity ([feval_limbwise_scmula24_mask64]) on the
 *  abstract decoder [feval], then derive algebraic correctness of
 *  the wrapped function ([F.eq (F.mul a24 xa) (feval dest)]).
 *
 *  Status (Phase 0d, 2026-05-13)
 *  =============================
 *  - [fe25519_scmula24_body_correct] : Qed via internal Lemma
 *    [scmula24_inline_correct], discharged mechanically against the
 *    limb-level hypotheses ([Fp25519_holds_intro] / [_elim] /
 *    [_set_other] / [feval_limbwise_scmula24_mask64]).  Seventeen
 *    [rexec_limb_store_inv] inversions (5 multiply + 12 carry)
 *    threaded through the abstract limb decoder.
 *
 *  History
 *  =======
 *  Phase 0c (commit 1dff2bc): scaffold with single
 *    [scmula24_inline_correct] section hypothesis.
 *  Phase 0d (this file): discharged the hypothesis as an internal
 *    Lemma, factored over the same 3-hypothesis decoder interface
 *    used by [Fe25519CarryCorrect] / [Fe25519AddSubCorrect] plus
 *    one algebraic identity hypothesis matching the structure of
 *    [feval_limbwise_carry_mask64].  Total Section hypothesis
 *    count: 4 limb-level (intro, elim, set_other, scmula24).
 *    No new GLOBAL axioms; the Section parameters remain
 *    section-quantified after [End].
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
Require Import Bedrock.End2End.Ed25519.Fe25519Scmula24Body.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + limb-     *)
(*     level decoder hypotheses.                                     *)
(* ================================================================ *)

Section Fe25519Scmula24Correct.

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

  (** The scalar constant [a24] in [F p], as an [F]-element.  Equals
      [F.of_Z _ 121665] (this is the literal value of [(A - 2) / 4]
      in [F p] where [A = 486662]). *)
  Definition fe25519_a24 : F p := F.of_Z _ fe25519_a24_z.

  (** Abstract decoder: how a 5-limb radix-2^51 representation projects
      to the field [F p].  Concrete instantiations use fiat-crypto's
      [Positional.eval] composed with [F.of_Z]. *)
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

  (** Compute-cached literals (same as in [Fe25519CarryCorrect]). *)
  Local Definition mask51_lit : Z := 2251799813685247.   (* 2^51 - 1 *)
  Local Definition radix_lit  : Z := 51.                 (* mask64 51 = 51 *)
  Local Definition red19_lit  : Z := 19.                 (* mask64 19 = 19 *)
  Local Definition a24_lit    : Z := fe25519_a24_z.      (* 121665 *)

  (** Helper: read the i-th limb of [la] through [mask64]. *)
  Definition m_a (la : list Z) (i : nat) : Z := mask64 (List.nth i la 0).

  (** Phase A — limbwise multiply-by-constant.  After 5 multiplies,
      dest holds [mul_a24 la := [m0; m1; m2; m3; m4]] where
      [mi := mask64 (m_a la i * mask64 fe25519_a24_z)]. *)
  Definition mul_a24_limb (la : list Z) (i : nat) : Z :=
    mask64 (m_a la i * a24_lit).

  Definition mul_a24 (la : list Z) : list Z :=
    [ mul_a24_limb la 0%nat
    ; mul_a24_limb la 1%nat
    ; mul_a24_limb la 2%nat
    ; mul_a24_limb la 3%nat
    ; mul_a24_limb la 4%nat ].

  Lemma mul_a24_length :
    forall la, length (mul_a24 la) = 5%nat.
  Proof. reflexivity. Qed.

  (** Phase B — per-store written values for the 12-store carry chain,
      operating on a 5-limb base list [lb] (which will be [mul_a24 la]
      in the discharge).  These are the same closed-form values as in
      [Fe25519CarryCorrect], lifted to take the base list as an
      explicit argument. *)
  Definition v0_c  (lb : list Z) : Z := Z.land (m_a lb 0) mask51_lit.
  Definition v1_c  (lb : list Z) : Z :=
    mask64 (m_a lb 1 + Z.shiftr (m_a lb 0) radix_lit).
  Definition v2_c  (lb : list Z) : Z :=
    mask64 (m_a lb 2 + Z.shiftr (mask64 (v1_c lb)) radix_lit).
  Definition v3_c  (lb : list Z) : Z :=
    Z.land (mask64 (v1_c lb)) mask51_lit.
  Definition v4_c  (lb : list Z) : Z :=
    mask64 (m_a lb 3 + Z.shiftr (mask64 (v2_c lb)) radix_lit).
  Definition v5_c  (lb : list Z) : Z :=
    Z.land (mask64 (v2_c lb)) mask51_lit.
  Definition v6_c  (lb : list Z) : Z :=
    mask64 (m_a lb 4 + Z.shiftr (mask64 (v4_c lb)) radix_lit).
  Definition v7_c  (lb : list Z) : Z :=
    Z.land (mask64 (v4_c lb)) mask51_lit.
  Definition v8_c  (lb : list Z) : Z :=
    mask64 (mask64 (v0_c lb)
            + mask64 (red19_lit
                       * Z.shiftr (mask64 (v6_c lb)) radix_lit)).
  Definition v9_c  (lb : list Z) : Z :=
    Z.land (mask64 (v6_c lb)) mask51_lit.
  Definition v10_c (lb : list Z) : Z :=
    mask64 (mask64 (v3_c lb) + Z.shiftr (mask64 (v8_c lb)) radix_lit).
  Definition v11_c (lb : list Z) : Z :=
    Z.land (mask64 (v8_c lb)) mask51_lit.

  Definition build_limb_list_scmula24 (la : list Z) : list Z :=
    let lb := mul_a24 la in
    [v11_c lb; v10_c lb; v5_c lb; v7_c lb; v9_c lb].

  Lemma build_limb_list_scmula24_length :
    forall la, length (build_limb_list_scmula24 la) = 5%nat.
  Proof. reflexivity. Qed.

  (** Single algebraic identity discharging the whole scmula24 chain:
      [feval (build_limb_list_scmula24 la) = F.mul fe25519_a24 (feval la)].

      Mechanical discharge against fiat-crypto's
      [UnsaturatedSolinas.carry_scmul_const_correct] +
      [Positional.eval_carry_scmul_const] is performed at the concrete
      [feval] instantiation site; kept abstract here for the same
      reason as [feval_limbwise_carry_mask64]. *)
  Hypothesis feval_limbwise_scmula24_mask64 :
    forall (la : list Z),
      length la = 5%nat ->
      feval (build_limb_list_scmula24 la) = F.mul fe25519_a24 (feval la).

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
    intros l1 l2 H. injection H as Hexi. exact Hexi.
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

  (** Eval of [sScmulA24 a i] = [SMul (SLimb a i) (SLit fe25519_a24_z)]. *)
  Lemma eval_sScmulA24_SLimb_VFp25519 :
    forall rs a i la,
      rs_get_tower_ed rs a = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      (i < 5)%nat ->
      length la = 5%nat ->
      eval_sexpr_ed rs (sScmulA24 a i) =
      Some (mask64 (mask64 (List.nth i la 0) * a24_lit)).
  Proof.
    intros rs a i la Hga Hi Hla.
    unfold sScmulA24.
    change (eval_sexpr_ed rs (SMul (SLimb a i) (SLit fe25519_a24_z)))
      with (match eval_sexpr_ed rs (SLimb a i),
                  eval_sexpr_ed rs (SLit fe25519_a24_z) with
            | Some va, Some vb => Some (mask64 (va * vb))
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hga Hi Hla).
    change (eval_sexpr_ed rs (SLit fe25519_a24_z))
      with (Some a24_lit).
    reflexivity.
  Qed.

  (** Eval of [sMask51 (SLimb a i)] — same as in carry. *)
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

(* ================================================================ *)
(* §4. scmula24_inline_correct as a Lemma                            *)
(* ================================================================ *)

  (** Internal: chain through the 17 [REdLimbStore]s of
      [fe25519_scmula24_body].  Phase A (5 multiplies) reads slot [a]
      only; Phase B (12 carry stores) reads slot [dest] only.

      Strategy: at each step, invert the [REdLimbStore], evaluate the
      RHS using a single [eval_*_VFp25519] lemma against the most
      recent value at each read index, and chain through [subst].

      At end of Phase A, the dest slot stores [mul_a24 la].  Phase B
      is structurally identical to [carry_inline_correct] but with
      the base list [mul_a24 la] in place of [la]. *)
  Lemma scmula24_inline_correct :
    forall (dest a : located_ed) (rs1 rs2 : rust_state_ed) (xa : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Hexec
        (* ---- Phase A: 5 limbwise multiplies ---- *)
        (REdSeq
          (REdLimbStore dest 0%nat (sScmulA24 a.(loc_var) 0%nat))
        (REdSeq
          (REdLimbStore dest 1%nat (sScmulA24 a.(loc_var) 1%nat))
        (REdSeq
          (REdLimbStore dest 2%nat (sScmulA24 a.(loc_var) 2%nat))
        (REdSeq
          (REdLimbStore dest 3%nat (sScmulA24 a.(loc_var) 3%nat))
        (REdSeq
          (REdLimbStore dest 4%nat (sScmulA24 a.(loc_var) 4%nat))
        (* ---- Phase B: 12-store carry chain ---- *)
        (REdSeq
          (REdLimbStore dest 1%nat
             (SAdd (SLimb dest.(loc_var) 1%nat)
                   (sShr51 (SLimb dest.(loc_var) 0%nat))))
        (REdSeq
          (REdLimbStore dest 0%nat (sMask51 (SLimb dest.(loc_var) 0%nat)))
        (REdSeq
          (REdLimbStore dest 2%nat
             (SAdd (SLimb dest.(loc_var) 2%nat)
                   (sShr51 (SLimb dest.(loc_var) 1%nat))))
        (REdSeq
          (REdLimbStore dest 1%nat (sMask51 (SLimb dest.(loc_var) 1%nat)))
        (REdSeq
          (REdLimbStore dest 3%nat
             (SAdd (SLimb dest.(loc_var) 3%nat)
                   (sShr51 (SLimb dest.(loc_var) 2%nat))))
        (REdSeq
          (REdLimbStore dest 2%nat (sMask51 (SLimb dest.(loc_var) 2%nat)))
        (REdSeq
          (REdLimbStore dest 4%nat
             (SAdd (SLimb dest.(loc_var) 4%nat)
                   (sShr51 (SLimb dest.(loc_var) 3%nat))))
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
             (SAdd (SLimb dest.(loc_var) 1%nat)
                   (sShr51 (SLimb dest.(loc_var) 0%nat))))
          (REdLimbStore dest 0%nat (sMask51 (SLimb dest.(loc_var) 0%nat)))
        )))))))))))))))) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul fe25519_a24 xa) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros dest a rs1 rs2 xa Hdt Hat Hdne_a Hxa Hexec_n.
    (* Extract limb evidence for xa from [Fp25519_holds]. *)
    destruct (Fp25519_holds_elim _ _ _ Hxa) as [la [Hga [Hla Hfa]]].
    (* Peel the 16 sequence layers (17 stores). *)
    apply seq_inv in Hexec_n. destruct Hexec_n as [rsA0 [HsA0 Ht]].
    apply seq_inv in Ht. destruct Ht as [rsA1 [HsA1 Ht]].
    apply seq_inv in Ht. destruct Ht as [rsA2 [HsA2 Ht]].
    apply seq_inv in Ht. destruct Ht as [rsA3 [HsA3 Ht]].
    apply seq_inv in Ht. destruct Ht as [rsA4 [HsA4 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_a [Hs0 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_b [Hs1 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_c [Hs2 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_d [Hs3 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_e [Hs4 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_f [Hs5 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_g [Hs6 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_h [Hs7 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_i [Hs8 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_j [Hs9 Ht]].
    apply seq_inv in Ht. destruct Ht as [rs_k [Hs10 Hs11]].
    (* Invert each REdLimbStore step. *)
    pose proof (rexec_limb_store_inv _ _ _ _ _ HsA0 Hdt) as
      [wA0 [limbsA0 [HeA0 [HgA0 [HlenA0 [_ HrsA0_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ HsA1 Hdt) as
      [wA1 [limbsA1 [HeA1 [HgA1 [HlenA1 [_ HrsA1_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ HsA2 Hdt) as
      [wA2 [limbsA2 [HeA2 [HgA2 [HlenA2 [_ HrsA2_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ HsA3 Hdt) as
      [wA3 [limbsA3 [HeA3 [HgA3 [HlenA3 [_ HrsA3_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ HsA4 Hdt) as
      [wA4 [limbsA4 [HeA4 [HgA4 [HlenA4 [_ Hrs_a_eq]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs0 Hdt) as
      [w0 [limbs0 [He0 [Hg0 [Hlen0 [_ Hrsb]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs1 Hdt) as
      [w1 [limbs1 [He1 [Hg1 [Hlen1 [_ Hrsc]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs2 Hdt) as
      [w2 [limbs2 [He2 [Hg2 [Hlen2 [_ Hrsd]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs3 Hdt) as
      [w3 [limbs3 [He3 [Hg3 [Hlen3 [_ Hrse]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs4 Hdt) as
      [w4 [limbs4 [He4 [Hg4 [Hlen4 [_ Hrsf]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs5 Hdt) as
      [w5 [limbs5 [He5 [Hg5 [Hlen5 [_ Hrsg]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs6 Hdt) as
      [w6 [limbs6 [He6 [Hg6 [Hlen6 [_ Hrsh]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs7 Hdt) as
      [w7 [limbs7 [He7 [Hg7 [Hlen7 [_ Hrsi]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs8 Hdt) as
      [w8 [limbs8 [He8 [Hg8 [Hlen8 [_ Hrsj]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs9 Hdt) as
      [w9 [limbs9 [He9 [Hg9 [Hlen9 [_ Hrsk]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs10 Hdt) as
      [w10 [limbs10 [He10 [Hg10 [Hlen10 [_ Hrs_l]]]]]].
    pose proof (rexec_limb_store_inv _ _ _ _ _ Hs11 Hdt) as
      [w11 [limbs11 [He11 [Hg11 [Hlen11 [_ Hrs2]]]]]].

    (* =================================================== *)
    (* === Phase A: 5 limbwise multiplies                === *)
    (* =================================================== *)

    (* --- A0: dest[0] := SMul (SLimb a 0) (SLit fe25519_a24_z).  Read: a. *)
    rewrite (eval_sScmulA24_SLimb_VFp25519 rs1 a.(loc_var) 0%nat la
              Hga ltac:(lia) Hla) in HeA0.
    injection HeA0 as HwA0_eq.
    change (mask64 (mask64 (List.nth 0 la 0) * a24_lit))
      with (mul_a24_limb la 0%nat) in HwA0_eq.
    subst wA0. subst rsA0.

    (* --- A1: dest[1] := SMul (SLimb a 1) (SLit fe25519_a24_z).  Read: a. *)
    assert (Hga_A1 : rs_get_tower_ed
                       (rs_set_tower_ed rs1 dest.(loc_var)
                          (exist_tval_ed TFp25519
                             (VFp25519 (list_set 0 (mul_a24_limb la 0%nat) limbsA0))))
                       a.(loc_var)
                     = Some (exist_tval_ed TFp25519 (VFp25519 la))).
    { rewrite rs_get_set_tower_other by exact Hdne_a. exact Hga. }
    rewrite (eval_sScmulA24_SLimb_VFp25519 _ a.(loc_var) 1%nat la
              Hga_A1 ltac:(lia) Hla) in HeA1.
    injection HeA1 as HwA1_eq.
    change (mask64 (mask64 (List.nth 1 la 0) * a24_lit))
      with (mul_a24_limb la 1%nat) in HwA1_eq.
    subst wA1.
    rewrite rs_get_set_tower_eq in HgA1.
    apply tval_some_vfp25519_inj in HgA1.
    subst limbsA1. subst rsA1.

    (* --- A2: dest[2] := SMul (SLimb a 2) (SLit fe25519_a24_z).  Read: a. *)
    match type of HgA2 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (Hga_A2 : rs_get_tower_ed rs a.(loc_var)
                      = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga)
    end.
    rewrite (eval_sScmulA24_SLimb_VFp25519 _ a.(loc_var) 2%nat la
              Hga_A2 ltac:(lia) Hla) in HeA2.
    injection HeA2 as HwA2_eq.
    change (mask64 (mask64 (List.nth 2 la 0) * a24_lit))
      with (mul_a24_limb la 2%nat) in HwA2_eq.
    subst wA2.
    rewrite rs_get_set_tower_eq in HgA2.
    apply tval_some_vfp25519_inj in HgA2.
    subst limbsA2. subst rsA2.

    (* --- A3: dest[3] := SMul (SLimb a 3) (SLit fe25519_a24_z).  Read: a. *)
    match type of HgA3 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (Hga_A3 : rs_get_tower_ed rs a.(loc_var)
                      = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga)
    end.
    rewrite (eval_sScmulA24_SLimb_VFp25519 _ a.(loc_var) 3%nat la
              Hga_A3 ltac:(lia) Hla) in HeA3.
    injection HeA3 as HwA3_eq.
    change (mask64 (mask64 (List.nth 3 la 0) * a24_lit))
      with (mul_a24_limb la 3%nat) in HwA3_eq.
    subst wA3.
    rewrite rs_get_set_tower_eq in HgA3.
    apply tval_some_vfp25519_inj in HgA3.
    subst limbsA3. subst rsA3.

    (* --- A4: dest[4] := SMul (SLimb a 4) (SLit fe25519_a24_z).  Read: a. *)
    match type of HgA4 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (Hga_A4 : rs_get_tower_ed rs a.(loc_var)
                      = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga)
    end.
    rewrite (eval_sScmulA24_SLimb_VFp25519 _ a.(loc_var) 4%nat la
              Hga_A4 ltac:(lia) Hla) in HeA4.
    injection HeA4 as HwA4_eq.
    change (mask64 (mask64 (List.nth 4 la 0) * a24_lit))
      with (mul_a24_limb la 4%nat) in HwA4_eq.
    subst wA4.
    rewrite rs_get_set_tower_eq in HgA4.
    apply tval_some_vfp25519_inj in HgA4.
    subst limbsA4. subst rsA4.

    (* End of Phase A: dest now holds [limbs_postA] (5 list_sets on
       limbsA0).  We need to extract its i-th element for the carry
       chain's SLimb reads to evaluate. *)
    set (limbs_postA :=
           list_set 4%nat (mul_a24_limb la 4%nat)
             (list_set 3%nat (mul_a24_limb la 3%nat)
               (list_set 2%nat (mul_a24_limb la 2%nat)
                 (list_set 1%nat (mul_a24_limb la 1%nat)
                   (list_set 0%nat (mul_a24_limb la 0%nat) limbsA0))))).
    assert (Hlen_postA : length limbs_postA = 5%nat).
    { unfold limbs_postA. repeat rewrite list_set_length. exact HlenA0. }
    (* For each i in 0..4, [nth i limbs_postA 0 = mul_a24_limb la i =
       m_a (mul_a24 la) i]. *)
    assert (HnthA0 : List.nth 0 limbs_postA 0 = mul_a24_limb la 0%nat).
    { unfold limbs_postA.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenA0; lia. }
    assert (HnthA1 : List.nth 1 limbs_postA 0 = mul_a24_limb la 1%nat).
    { unfold limbs_postA.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_same.
      - reflexivity.
      - repeat rewrite list_set_length. rewrite HlenA0; lia. }
    assert (HnthA2 : List.nth 2 limbs_postA 0 = mul_a24_limb la 2%nat).
    { unfold limbs_postA.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_same.
      - reflexivity.
      - repeat rewrite list_set_length. rewrite HlenA0; lia. }
    assert (HnthA3 : List.nth 3 limbs_postA 0 = mul_a24_limb la 3%nat).
    { unfold limbs_postA.
      rewrite list_set_nth_other by lia.
      rewrite list_set_nth_same.
      - reflexivity.
      - repeat rewrite list_set_length. rewrite HlenA0; lia. }
    assert (HnthA4 : List.nth 4 limbs_postA 0 = mul_a24_limb la 4%nat).
    { unfold limbs_postA.
      rewrite list_set_nth_same.
      - reflexivity.
      - repeat rewrite list_set_length. rewrite HlenA0; lia. }

    (* Let lb := mul_a24 la.  Equation: for each i in 0..4,
       m_a limbs_postA i = m_a lb i.  We need this to translate from
       the carry-chain closed-forms (which use lb) to nth in
       limbs_postA. *)
    set (lb := mul_a24 la).
    assert (Hma0 : m_a limbs_postA 0%nat = m_a lb 0%nat).
    { unfold m_a, lb, mul_a24. rewrite HnthA0. cbn [List.nth]. reflexivity. }
    assert (Hma1 : m_a limbs_postA 1%nat = m_a lb 1%nat).
    { unfold m_a, lb, mul_a24. rewrite HnthA1. cbn [List.nth]. reflexivity. }
    assert (Hma2 : m_a limbs_postA 2%nat = m_a lb 2%nat).
    { unfold m_a, lb, mul_a24. rewrite HnthA2. cbn [List.nth]. reflexivity. }
    assert (Hma3 : m_a limbs_postA 3%nat = m_a lb 3%nat).
    { unfold m_a, lb, mul_a24. rewrite HnthA3. cbn [List.nth]. reflexivity. }
    assert (Hma4 : m_a limbs_postA 4%nat = m_a lb 4%nat).
    { unfold m_a, lb, mul_a24. rewrite HnthA4. cbn [List.nth]. reflexivity. }

    (* =================================================== *)
    (* === Phase B: 12-store carry chain on dest         === *)
    (* =================================================== *)

    (* The carry chain reads only [dest], with [dest] holding
       [limbs_postA] at the start of Phase B.  All semantics evaluate
       through [m_a limbs_postA i = m_a lb i], translating the
       closed-form values [vN_c lb] into the per-store written values. *)

    (* === Step 0 (S0): dest[1] := SAdd (SLimb dest 1) (sShr51 (SLimb dest 0)).
           Read: dest[1] = mul_a24_limb la 1; dest[0] = mul_a24_limb la 0.
           Write: w0 = v1_c lb. *)
    (* Resolve limbs0 = limbs_postA from Hg0 (the carry-step inversion). *)
    rewrite rs_get_set_tower_eq in Hg0.
    apply tval_some_vfp25519_inj in Hg0.
    fold limbs_postA in Hg0.
    subst limbs0.
    (* Now we have a generic [Hg<n>] for the current state holding
       [limbs_postA] at dest.  But Hg0 was already consumed.  Re-derive
       a clean Hg_postA from the inversion of Hs0 (rs after Phase A is
       the LHS of Hs0). *)
    match type of Hs0 with
    | Hexec _ ?rs _ =>
      assert (Hg_postA : rs_get_tower_ed rs dest.(loc_var)
                      = Some (exist_tval_ed TFp25519 (VFp25519 limbs_postA))) by
        (apply rs_get_set_tower_eq)
    end.
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ dest.(loc_var) dest.(loc_var) 1%nat 0%nat
              limbs_postA limbs_postA Hg_postA Hg_postA ltac:(lia) ltac:(lia)
              Hlen_postA Hlen_postA) in He0.
    injection He0 as Hw0_eq.
    change (mask64 (mask64 (List.nth 1 limbs_postA 0)
                    + Z.shiftr (mask64 (List.nth 0 limbs_postA 0)) radix_lit))
      with (mask64 (m_a limbs_postA 1%nat
                    + Z.shiftr (m_a limbs_postA 0%nat) radix_lit)) in Hw0_eq.
    rewrite Hma1, Hma0 in Hw0_eq.
    change (mask64 (m_a lb 1%nat + Z.shiftr (m_a lb 0%nat) radix_lit))
      with (v1_c lb) in Hw0_eq.
    subst w0.
    subst rs_a.

    (* === Step 1 (S1): dest[0] := sMask51 (SLimb dest 0).
           Read: dest[0] = mul_a24_limb la 0 (S0 wrote at index 1).
           Write: w1 = v0_c lb. *)
    set (limbsB := list_set 1%nat (v1_c lb) limbs_postA).
    match type of Hg1 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgB : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsB))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenB : length limbsB = 5%nat).
    { unfold limbsB. rewrite list_set_length. exact Hlen_postA. }
    assert (HnthB0 : List.nth 0 limbsB 0 = mul_a24_limb la 0%nat).
    { unfold limbsB. rewrite list_set_nth_other by lia. exact HnthA0. }
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 0%nat limbsB
              HgB ltac:(lia) HlenB) in He1.
    injection He1 as Hw1_eq.
    rewrite HnthB0 in Hw1_eq.
    (* The eval form is [Z.land (mask64 (mul_a24_limb la 0)) mask51_lit].
       Note [mask64 (mul_a24_limb la 0) = mask64 (nth 0 lb 0) = m_a lb 0]
       by [lb := mul_a24 la].  This holds definitionally after unfolding. *)
    change (mask64 (mul_a24_limb la 0%nat)) with (m_a lb 0%nat) in Hw1_eq.
    change (Z.land (m_a lb 0%nat) mask51_lit)
      with (v0_c lb) in Hw1_eq.
    subst w1.
    rewrite rs_get_set_tower_eq in Hg1.
    apply tval_some_vfp25519_inj in Hg1.
    subst limbs1. subst rs_b.

    (* === Step 2 (S2): dest[2] := SAdd (SLimb dest 2) (sShr51 (SLimb dest 1)).
           Read: dest[2] = mul_a24_limb la 2; dest[1] = v1_c lb.
           Write: w2 = v2_c lb. *)
    set (limbsC := list_set 0%nat (v0_c lb) limbsB).
    match type of Hg2 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgC : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsC))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenC : length limbsC = 5%nat).
    { unfold limbsC. rewrite list_set_length. exact HlenB. }
    assert (HnthC2 : List.nth 2 limbsC 0 = mul_a24_limb la 2%nat).
    { unfold limbsC. rewrite list_set_nth_other by lia.
      unfold limbsB. rewrite list_set_nth_other by lia. exact HnthA2. }
    assert (HnthC1 : List.nth 1 limbsC 0 = v1_c lb).
    { unfold limbsC. rewrite list_set_nth_other by lia.
      unfold limbsB. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite Hlen_postA; lia. }
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ dest.(loc_var) dest.(loc_var) 2%nat 1%nat
              limbsC limbsC HgC HgC ltac:(lia) ltac:(lia) HlenC HlenC) in He2.
    injection He2 as Hw2_eq.
    rewrite HnthC2, HnthC1 in Hw2_eq.
    change (mask64 (mul_a24_limb la 2%nat)) with (m_a lb 2%nat) in Hw2_eq.
    change (mask64 (m_a lb 2%nat + Z.shiftr (mask64 (v1_c lb)) radix_lit))
      with (v2_c lb) in Hw2_eq.
    subst w2.
    rewrite rs_get_set_tower_eq in Hg2.
    apply tval_some_vfp25519_inj in Hg2.
    subst limbs2. subst rs_c.

    (* === Step 3 (S3): dest[1] := sMask51 (SLimb dest 1).
           Read: dest[1] = v1_c lb (S2 wrote at index 2).
           Write: w3 = v3_c lb. *)
    set (limbsD := list_set 2%nat (v2_c lb) limbsC).
    match type of Hg3 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgD : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsD))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenD : length limbsD = 5%nat).
    { unfold limbsD. rewrite list_set_length. exact HlenC. }
    assert (HnthD1 : List.nth 1 limbsD 0 = v1_c lb).
    { unfold limbsD. rewrite list_set_nth_other by lia. exact HnthC1. }
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 1%nat limbsD
              HgD ltac:(lia) HlenD) in He3.
    injection He3 as Hw3_eq. rewrite HnthD1 in Hw3_eq.
    change (Z.land (mask64 (v1_c lb)) mask51_lit)
      with (v3_c lb) in Hw3_eq.
    subst w3.
    rewrite rs_get_set_tower_eq in Hg3.
    apply tval_some_vfp25519_inj in Hg3.
    subst limbs3. subst rs_d.

    (* === Step 4 (S4): dest[3] := SAdd (SLimb dest 3) (sShr51 (SLimb dest 2)).
           Read: dest[3] = mul_a24_limb la 3; dest[2] = v2_c lb.
           Write: w4 = v4_c lb. *)
    set (limbsE := list_set 1%nat (v3_c lb) limbsD).
    match type of Hg4 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgE : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsE))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenE : length limbsE = 5%nat).
    { unfold limbsE. rewrite list_set_length. exact HlenD. }
    assert (HnthE3 : List.nth 3 limbsE 0 = mul_a24_limb la 3%nat).
    { unfold limbsE. rewrite list_set_nth_other by lia.
      unfold limbsD. rewrite list_set_nth_other by lia.
      unfold limbsC. rewrite list_set_nth_other by lia.
      unfold limbsB. rewrite list_set_nth_other by lia. exact HnthA3. }
    assert (HnthE2 : List.nth 2 limbsE 0 = v2_c lb).
    { unfold limbsE. rewrite list_set_nth_other by lia.
      unfold limbsD. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenC; lia. }
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ dest.(loc_var) dest.(loc_var) 3%nat 2%nat
              limbsE limbsE HgE HgE ltac:(lia) ltac:(lia) HlenE HlenE) in He4.
    injection He4 as Hw4_eq. rewrite HnthE3, HnthE2 in Hw4_eq.
    change (mask64 (mul_a24_limb la 3%nat)) with (m_a lb 3%nat) in Hw4_eq.
    change (mask64 (m_a lb 3%nat + Z.shiftr (mask64 (v2_c lb)) radix_lit))
      with (v4_c lb) in Hw4_eq.
    subst w4.
    rewrite rs_get_set_tower_eq in Hg4.
    apply tval_some_vfp25519_inj in Hg4.
    subst limbs4. subst rs_e.

    (* === Step 5 (S5): dest[2] := sMask51 (SLimb dest 2).
           Read: dest[2] = v2_c lb (S4 wrote at index 3).
           Write: w5 = v5_c lb. *)
    set (limbsF := list_set 3%nat (v4_c lb) limbsE).
    match type of Hg5 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgF : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsF))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenF : length limbsF = 5%nat).
    { unfold limbsF. rewrite list_set_length. exact HlenE. }
    assert (HnthF2 : List.nth 2 limbsF 0 = v2_c lb).
    { unfold limbsF. rewrite list_set_nth_other by lia. exact HnthE2. }
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 2%nat limbsF
              HgF ltac:(lia) HlenF) in He5.
    injection He5 as Hw5_eq. rewrite HnthF2 in Hw5_eq.
    change (Z.land (mask64 (v2_c lb)) mask51_lit)
      with (v5_c lb) in Hw5_eq.
    subst w5.
    rewrite rs_get_set_tower_eq in Hg5.
    apply tval_some_vfp25519_inj in Hg5.
    subst limbs5. subst rs_f.

    (* === Step 6 (S6): dest[4] := SAdd (SLimb dest 4) (sShr51 (SLimb dest 3)).
           Read: dest[4] = mul_a24_limb la 4; dest[3] = v4_c lb.
           Write: w6 = v6_c lb. *)
    set (limbsG := list_set 2%nat (v5_c lb) limbsF).
    match type of Hg6 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgG : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsG))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenG : length limbsG = 5%nat).
    { unfold limbsG. rewrite list_set_length. exact HlenF. }
    assert (HnthG4 : List.nth 4 limbsG 0 = mul_a24_limb la 4%nat).
    { unfold limbsG. rewrite list_set_nth_other by lia.
      unfold limbsF. rewrite list_set_nth_other by lia.
      unfold limbsE. rewrite list_set_nth_other by lia.
      unfold limbsD. rewrite list_set_nth_other by lia.
      unfold limbsC. rewrite list_set_nth_other by lia.
      unfold limbsB. rewrite list_set_nth_other by lia. exact HnthA4. }
    assert (HnthG3 : List.nth 3 limbsG 0 = v4_c lb).
    { unfold limbsG. rewrite list_set_nth_other by lia.
      unfold limbsF. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenE; lia. }
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ dest.(loc_var) dest.(loc_var) 4%nat 3%nat
              limbsG limbsG HgG HgG ltac:(lia) ltac:(lia) HlenG HlenG) in He6.
    injection He6 as Hw6_eq. rewrite HnthG4, HnthG3 in Hw6_eq.
    change (mask64 (mul_a24_limb la 4%nat)) with (m_a lb 4%nat) in Hw6_eq.
    change (mask64 (m_a lb 4%nat + Z.shiftr (mask64 (v4_c lb)) radix_lit))
      with (v6_c lb) in Hw6_eq.
    subst w6.
    rewrite rs_get_set_tower_eq in Hg6.
    apply tval_some_vfp25519_inj in Hg6.
    subst limbs6. subst rs_g.

    (* === Step 7 (S7): dest[3] := sMask51 (SLimb dest 3).
           Read: dest[3] = v4_c lb (S6 wrote at index 4).
           Write: w7 = v7_c lb. *)
    set (limbsH := list_set 4%nat (v6_c lb) limbsG).
    match type of Hg7 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgH : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsH))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenH : length limbsH = 5%nat).
    { unfold limbsH. rewrite list_set_length. exact HlenG. }
    assert (HnthH3 : List.nth 3 limbsH 0 = v4_c lb).
    { unfold limbsH. rewrite list_set_nth_other by lia. exact HnthG3. }
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 3%nat limbsH
              HgH ltac:(lia) HlenH) in He7.
    injection He7 as Hw7_eq. rewrite HnthH3 in Hw7_eq.
    change (Z.land (mask64 (v4_c lb)) mask51_lit)
      with (v7_c lb) in Hw7_eq.
    subst w7.
    rewrite rs_get_set_tower_eq in Hg7.
    apply tval_some_vfp25519_inj in Hg7.
    subst limbs7. subst rs_h.

    (* === Step 8 (S8): dest[0] := SAdd (SLimb dest 0) (sWrap19 (SLimb dest 4)).
           Read: dest[0] = v0_c lb (S1 wrote at index 0), dest[4] = v6_c lb (S6).
           Write: w8 = v8_c lb. *)
    set (limbsI := list_set 3%nat (v7_c lb) limbsH).
    match type of Hg8 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgI : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsI))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenI : length limbsI = 5%nat).
    { unfold limbsI. rewrite list_set_length. exact HlenH. }
    assert (HnthI0 : List.nth 0 limbsI 0 = v0_c lb).
    { unfold limbsI. rewrite list_set_nth_other by lia.
      unfold limbsH. rewrite list_set_nth_other by lia.
      unfold limbsG. rewrite list_set_nth_other by lia.
      unfold limbsF. rewrite list_set_nth_other by lia.
      unfold limbsE. rewrite list_set_nth_other by lia.
      unfold limbsD. rewrite list_set_nth_other by lia.
      unfold limbsC. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenB; lia. }
    assert (HnthI4 : List.nth 4 limbsI 0 = v6_c lb).
    { unfold limbsI. rewrite list_set_nth_other by lia.
      unfold limbsH. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenG; lia. }
    rewrite (eval_SAdd_SLimb_sWrap19_SLimb _ dest.(loc_var) dest.(loc_var) 0%nat 4%nat
              limbsI limbsI HgI HgI ltac:(lia) ltac:(lia) HlenI HlenI) in He8.
    injection He8 as Hw8_eq.
    rewrite HnthI0, HnthI4 in Hw8_eq.
    change (mask64 (mask64 (v0_c lb)
                    + mask64 (red19_lit
                              * Z.shiftr (mask64 (v6_c lb)) radix_lit)))
      with (v8_c lb) in Hw8_eq.
    subst w8.
    rewrite rs_get_set_tower_eq in Hg8.
    apply tval_some_vfp25519_inj in Hg8.
    subst limbs8. subst rs_i.

    (* === Step 9 (S9): dest[4] := sMask51 (SLimb dest 4).
           Read: dest[4] = v6_c lb (S8 wrote at index 0).
           Write: w9 = v9_c lb. *)
    set (limbsJ := list_set 0%nat (v8_c lb) limbsI).
    match type of Hg9 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgJ : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsJ))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenJ : length limbsJ = 5%nat).
    { unfold limbsJ. rewrite list_set_length. exact HlenI. }
    assert (HnthJ4 : List.nth 4 limbsJ 0 = v6_c lb).
    { unfold limbsJ. rewrite list_set_nth_other by lia. exact HnthI4. }
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 4%nat limbsJ
              HgJ ltac:(lia) HlenJ) in He9.
    injection He9 as Hw9_eq. rewrite HnthJ4 in Hw9_eq.
    change (Z.land (mask64 (v6_c lb)) mask51_lit)
      with (v9_c lb) in Hw9_eq.
    subst w9.
    rewrite rs_get_set_tower_eq in Hg9.
    apply tval_some_vfp25519_inj in Hg9.
    subst limbs9. subst rs_j.

    (* === Step 10 (S10): dest[1] := SAdd (SLimb dest 1) (sShr51 (SLimb dest 0)).
           Read: dest[1] = v3_c lb (S3 wrote at 1), dest[0] = v8_c lb (S8 wrote at 0).
           Write: w10 = v10_c lb. *)
    set (limbsK := list_set 4%nat (v9_c lb) limbsJ).
    match type of Hg10 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgK : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsK))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenK : length limbsK = 5%nat).
    { unfold limbsK. rewrite list_set_length. exact HlenJ. }
    assert (HnthK1 : List.nth 1 limbsK 0 = v3_c lb).
    { unfold limbsK. rewrite list_set_nth_other by lia.
      unfold limbsJ. rewrite list_set_nth_other by lia.
      unfold limbsI. rewrite list_set_nth_other by lia.
      unfold limbsH. rewrite list_set_nth_other by lia.
      unfold limbsG. rewrite list_set_nth_other by lia.
      unfold limbsF. rewrite list_set_nth_other by lia.
      unfold limbsE. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenD; lia. }
    assert (HnthK0 : List.nth 0 limbsK 0 = v8_c lb).
    { unfold limbsK. rewrite list_set_nth_other by lia.
      unfold limbsJ. rewrite list_set_nth_same.
      - reflexivity.
      - rewrite HlenI; lia. }
    rewrite (eval_SAdd_SLimb_sShr51_SLimb _ dest.(loc_var) dest.(loc_var) 1%nat 0%nat
              limbsK limbsK HgK HgK ltac:(lia) ltac:(lia) HlenK HlenK) in He10.
    injection He10 as Hw10_eq. rewrite HnthK1, HnthK0 in Hw10_eq.
    change (mask64 (mask64 (v3_c lb)
                    + Z.shiftr (mask64 (v8_c lb)) radix_lit))
      with (v10_c lb) in Hw10_eq.
    subst w10.
    rewrite rs_get_set_tower_eq in Hg10.
    apply tval_some_vfp25519_inj in Hg10.
    subst limbs10. subst rs_k.

    (* === Step 11 (S11): dest[0] := sMask51 (SLimb dest 0).
           Read: dest[0] = v8_c lb (S10 wrote at index 1).
           Write: w11 = v11_c lb. *)
    set (limbsL := list_set 1%nat (v10_c lb) limbsK).
    match type of Hg11 with
    | rs_get_tower_ed ?rs _ = _ =>
      assert (HgL : rs_get_tower_ed rs dest.(loc_var)
                  = Some (exist_tval_ed TFp25519 (VFp25519 limbsL))) by
        (apply rs_get_set_tower_eq)
    end.
    assert (HlenL : length limbsL = 5%nat).
    { unfold limbsL. rewrite list_set_length. exact HlenK. }
    assert (HnthL0 : List.nth 0 limbsL 0 = v8_c lb).
    { unfold limbsL. rewrite list_set_nth_other by lia. exact HnthK0. }
    rewrite (eval_sMask51_SLimb_VFp25519 _ dest.(loc_var) 0%nat limbsL
              HgL ltac:(lia) HlenL) in He11.
    injection He11 as Hw11_eq. rewrite HnthL0 in Hw11_eq.
    change (Z.land (mask64 (v8_c lb)) mask51_lit)
      with (v11_c lb) in Hw11_eq.
    subst w11.
    rewrite rs_get_set_tower_eq in Hg11.
    apply tval_some_vfp25519_inj in Hg11.
    subst limbs11. subst rs2.

    (* Final state stores VFp25519 limbs_final at dest, where
       limbs_final = list_set 0 (v11_c lb) (list_set 1 (v10_c lb) limbsK). *)
    set (limbs_final :=
      list_set 0%nat (v11_c lb)
        (list_set 1%nat (v10_c lb) limbsK)).
    assert (Hlen_final : length limbs_final = 5%nat).
    { unfold limbs_final. repeat rewrite list_set_length. exact HlenK. }
    (* Show: limbs_final = build_limb_list_scmula24 la. *)
    assert (Hfinal_eq : limbs_final = build_limb_list_scmula24 la).
    { apply (List.nth_ext _ _ 0 0).
      - rewrite Hlen_final. reflexivity.
      - intros i Hi. rewrite Hlen_final in Hi.
        unfold build_limb_list_scmula24.
        fold lb.
        destruct i as [|[|[|[|[|i']]]]]; try (exfalso; lia).
        + (* i = 0: limb 0 = v11_c lb. *)
          unfold limbs_final.
          rewrite list_set_nth_same.
          * reflexivity.
          * rewrite list_set_length, HlenK; lia.
        + (* i = 1: limb 1 = v10_c lb. *)
          unfold limbs_final.
          rewrite list_set_nth_other by lia.
          rewrite list_set_nth_same.
          * reflexivity.
          * rewrite HlenK; lia.
        + (* i = 2: limb 2 = v5_c lb (S5 wrote at index 2 most recently). *)
          unfold limbs_final.
          rewrite list_set_nth_other by lia.
          rewrite list_set_nth_other by lia.
          unfold limbsK. rewrite list_set_nth_other by lia.
          unfold limbsJ. rewrite list_set_nth_other by lia.
          unfold limbsI. rewrite list_set_nth_other by lia.
          unfold limbsH. rewrite list_set_nth_other by lia.
          unfold limbsG. rewrite list_set_nth_same.
          * reflexivity.
          * rewrite HlenF; lia.
        + (* i = 3: limb 3 = v7_c lb (S7 wrote at index 3 most recently). *)
          unfold limbs_final.
          rewrite list_set_nth_other by lia.
          rewrite list_set_nth_other by lia.
          unfold limbsK. rewrite list_set_nth_other by lia.
          unfold limbsJ. rewrite list_set_nth_other by lia.
          unfold limbsI. rewrite list_set_nth_same.
          * reflexivity.
          * rewrite HlenH; lia.
        + (* i = 4: limb 4 = v9_c lb (S9 wrote at index 4 most recently). *)
          unfold limbs_final.
          rewrite list_set_nth_other by lia.
          rewrite list_set_nth_other by lia.
          unfold limbsK. rewrite list_set_nth_same.
          * reflexivity.
          * rewrite HlenJ; lia. }
    assert (Hfeval_final : feval limbs_final = F.mul fe25519_a24 xa).
    { rewrite Hfinal_eq.
      rewrite feval_limbwise_scmula24_mask64 by exact Hla.
      rewrite Hfa. reflexivity. }
    split.
    + (* Fp25519_holds at dest of F.mul fe25519_a24 xa. *)
      eapply Fp25519_holds_intro;
        [| exact Hlen_final | exact Hfeval_final].
      apply rs_get_set_tower_eq.
    + (* fp_frame: for y <> dest, the value is preserved across each
         of the 17 set_tower steps at dest. *)
      intros y vy Hne Hy.
      repeat (eapply Fp25519_holds_set_other; [exact Hne|]).
      exact Hy.
  Qed.

(* ================================================================ *)
(* §5. Headline theorem                                              *)
(* ================================================================ *)

  Theorem fe25519_scmula24_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (xa : F p),
      a_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Hexec (fe25519_scmula24_body dest [a_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.mul fe25519_a24 xa) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc dest xa Hat Hdt Hdne Hxa Hexec_n.
    cbn [fe25519_scmula24_body] in Hexec_n.
    apply (scmula24_inline_correct dest a_loc rs1 rs2 xa); assumption.
  Qed.

End Fe25519Scmula24Correct.

(** Sanity check: list assumptions of the headline theorem.  Inside
    the Section, the [Variable]/[Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_scmula24_body_correct.
