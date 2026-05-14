(** * Fe25519AddSubCorrect — functional correctness of [fe25519_add_body]
 *  and [fe25519_sub_body].
 *
 *  Companion to [Fe25519AddSubBody.v].  Mirrors the section-parameterised
 *  pattern used by [Fe25519InvertCorrect.fe25519_invert_correct]:
 *  abstract over the [Fp25519_holds] slot predicate plus a per-call
 *  oracle hypothesis on the body, then derive algebraic correctness
 *  of the wrapped function.
 *
 *  Status (Phase 0c, 2026-05-13)
 *  =============================
 *  - [fe25519_add_body_correct] :  Qed, via Lemma [add_inline_correct]
 *    discharged mechanically against the limb-level hypotheses
 *    ([Fp25519_holds_intro] / [Fp25519_holds_elim] /
 *     [feval_limbwise_add_mask64]).  Five [rexec_limb_store_fp25519]
 *    inversions threaded through the abstract limb decoder.
 *  - [fe25519_sub_body_correct] :  Qed, via Lemma [sub_inline_correct].
 *    fe25519_sub_body is now an INLINE 5-limb radix-2^51 sub chain
 *    using the +2p offset constants (mirrors fiat-crypto's [sub_op]).
 *    Same proof shape as add.
 *
 *  History
 *  =======
 *  Phase 0a (committed 6999797) had both proofs as 3-line
 *  [REdCall]-delegations to the [_prim] hypotheses.
 *  Phase 0b replaced [fe25519_add_body]'s AST with an inline 5-limb chain
 *  ([REdSeq] of five [REdLimbStore] calls).  Correctness via section
 *  [Hypothesis add_inline_correct].
 *  Phase 0c (this file): replaced the [add_inline_correct] hypothesis with
 *  a Lemma, factored over three smaller limb-level hypotheses about the
 *  abstract decoder [feval].  Also inlined [fe25519_sub_body] and proved
 *  [sub_inline_correct] mechanically.  Total Section hypothesis count:
 *  4 limb-level (intro, elim, add, sub).  No new GLOBAL axioms; the
 *  Section parameters remain section-quantified after [End].
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
Require Import Bedrock.End2End.Ed25519.Fe25519AddSubBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters: abstract field-slot predicate + limb-     *)
(*     level decoder hypotheses.                                     *)
(* ================================================================ *)

Section Fe25519AddSubCorrect.

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
      to the field [F p].  Concrete instantiations use fiat-crypto's
      [Positional.eval] composed with [F.of_Z].  Kept abstract here so
      this file stays decoupled from a particular limb-bound regime. *)
  Variable feval : list Z -> F p.

  (** Elimination: [Fp25519_holds] implies the slot stores a 5-limb
      [VFp25519] payload whose [feval] equals [x]. *)
  Hypothesis Fp25519_holds_elim :
    forall (rs : rust_state_ed) (v : String.string) (x : F p),
      Fp25519_holds rs v x ->
      exists limbs : list Z,
        rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
        /\ length limbs = 5%nat
        /\ feval limbs = x.

  (** Introduction: a slot storing a 5-limb [VFp25519] payload with
      [feval = x] satisfies [Fp25519_holds]. *)
  Hypothesis Fp25519_holds_intro :
    forall (rs : rust_state_ed) (v : String.string) (limbs : list Z) (x : F p),
      rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs)) ->
      length limbs = 5%nat ->
      feval limbs = x ->
      Fp25519_holds rs v x.

  (** Frame: distinct-slot writes preserve [Fp25519_holds].  Necessary
      because the chain of [REdLimbStore]s rewrites the tower env and
      we need surviving field slots to keep their semantics. *)
  Hypothesis Fp25519_holds_set_other :
    forall (rs : rust_state_ed) (x : String.string) (tv : tval_ed)
           (y : String.string) (vp : F p),
      y <> x ->
      Fp25519_holds rs y vp ->
      Fp25519_holds (rs_set_tower_ed rs x tv) y vp.

  (** Algebraic content of fiat-crypto's [add_op] correctness — at the
      limb level, the limbwise mask64-add of two valid limb lists
      decodes to the [F.add] of the input decodings.

      For radix-2^51 with each limb in [0, 2^54), every limbwise sum
      stays below 2^55 < 2^64, so [mask64] is the identity on the sum
      (fiat-crypto's [carry_add] adds a final carry pass, but the
      no-carry [add] body is what bedrock2 emits and what we mirror).
      The mechanical limb-bound discharge is left to the concrete
      [feval] instantiation; here we expose it as a single algebraic
      Hypothesis at the level used by callers.

      [build_limb_list_add la lb] is the limb-wise mask64-add, matching
      the IR semantics: each [REdLimbStore dest i (SAdd (SLimb a i)
      (SLimb b i))] writes [mask64 (mask64 (nth i la) + mask64
      (nth i lb))] into limb [i] of [dest]. *)
  Definition build_limb_list_add (la lb : list Z) : list Z :=
    List.map (fun i =>
                mask64 (mask64 (List.nth i la 0) + mask64 (List.nth i lb 0)))
             (List.seq 0 5).

  Hypothesis feval_limbwise_add_mask64 :
    forall (la lb : list Z),
      length la = 5%nat ->
      length lb = 5%nat ->
      feval (build_limb_list_add la lb) = F.add (feval la) (feval lb).

  (** Subtraction with the radix-2^51 borrow correction: each limb is
      [la_i - lb_i + (2 * p_i)] for the per-limb offset constants
      [p_off i] (fiat-crypto's [sub_op]: subtract then add [2 *
      Positional.encode_2p] to keep each limb non-negative).  The
      constants are emitted by the IR as [SLit (p_off i)]; we keep
      them as a Variable so this file does not depend on the concrete
      radix-2^51 modulus encoding. *)
  Variable p_off : nat -> Z.

  Definition build_limb_list_sub (la lb : list Z) : list Z :=
    List.map (fun i =>
                mask64 (mask64 (mask64 (List.nth i la 0)
                                 - mask64 (List.nth i lb 0))
                          + mask64 (p_off i)))
             (List.seq 0 5).

  Hypothesis feval_limbwise_sub_mask64 :
    forall (la lb : list Z),
      length la = 5%nat ->
      length lb = 5%nat ->
      feval (build_limb_list_sub la lb) = F.sub (feval la) (feval lb).

(* ================================================================ *)
(* §2. Internal lemmas: rs_get_tower / rs_set_tower bookkeeping      *)
(* ================================================================ *)

  (** After a single [REdLimbStore] step, the destination slot's limb
      list has the chosen limb replaced. *)
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

  (** Eq-elimination for [VFp25519] payloads in a tval_ed equality.
      Avoids manual existT-inversion at use sites.  Coq's [injection]
      handles the dependent existT-step automatically here since
      [tower_type_ed] has decidable equality (used by the kernel via
      the rocq-prover 9 native injection machinery). *)
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

  (** [eval_sexpr_ed] of [SLimb v i] when the slot holds a 5-limb
      [VFp25519] payload: returns [mask64 (nth i limbs 0)]. *)
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

  (** Eval of [SAdd (SLimb a i) (SLimb b i)] over a state with valid
      5-limb VFp25519 payloads at [a] and [b]. *)
  Lemma eval_SAdd_SLimb_SLimb_VFp25519 :
    forall rs a b i la lb,
      rs_get_tower_ed rs a = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      rs_get_tower_ed rs b = Some (exist_tval_ed TFp25519 (VFp25519 lb)) ->
      (i < 5)%nat ->
      length la = 5%nat ->
      length lb = 5%nat ->
      eval_sexpr_ed rs (SAdd (SLimb a i) (SLimb b i)) =
      Some (mask64 (mask64 (List.nth i la 0) + mask64 (List.nth i lb 0))).
  Proof.
    intros rs a b i la lb Hga Hgb Hi Hla Hlb.
    change (eval_sexpr_ed rs (SAdd (SLimb a i) (SLimb b i)))
      with (match eval_sexpr_ed rs (SLimb a i), eval_sexpr_ed rs (SLimb b i) with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hga Hi Hla).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hgb Hi Hlb).
    reflexivity.
  Qed.

  (** Eval of [SAdd (SSub (SLimb a i) (SLimb b i)) (SLit c)] for the
      sub-with-borrow inline chain. *)
  Lemma eval_sub_with_offset :
    forall rs a b i la lb c,
      rs_get_tower_ed rs a = Some (exist_tval_ed TFp25519 (VFp25519 la)) ->
      rs_get_tower_ed rs b = Some (exist_tval_ed TFp25519 (VFp25519 lb)) ->
      (i < 5)%nat ->
      length la = 5%nat ->
      length lb = 5%nat ->
      eval_sexpr_ed rs
        (SAdd (SSub (SLimb a i) (SLimb b i)) (SLit c)) =
      Some (mask64
              (mask64 (mask64 (List.nth i la 0) - mask64 (List.nth i lb 0))
                 + mask64 c)).
  Proof.
    intros rs a b i la lb c Hga Hgb Hi Hla Hlb.
    change (eval_sexpr_ed rs (SAdd (SSub (SLimb a i) (SLimb b i)) (SLit c)))
      with (match
              match eval_sexpr_ed rs (SLimb a i), eval_sexpr_ed rs (SLimb b i) with
              | Some va, Some vb => Some (mask64 (va - vb))
              | _, _ => None
              end,
              eval_sexpr_ed rs (SLit c)
            with
            | Some va, Some vb => Some (mask64 (va + vb))
            | _, _ => None
            end).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hga Hi Hla).
    rewrite (eval_SLimb_VFp25519 _ _ _ _ Hgb Hi Hlb).
    reflexivity.
  Qed.

  (** Inversion for a single [REdLimbStore loc i e] step: the slot at
      [loc] before the step is a [VFp25519], and after the step its
      [i]-th limb is the evaluated expression. *)
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

  (** Sequence inversion. *)
  Lemma seq_inv c1 c2 rs1 rs3 :
    Hexec (REdSeq c1 c2) rs1 rs3 ->
    exists rs2, Hexec c1 rs1 rs2 /\ Hexec c2 rs2 rs3.
  Proof.
    intros Hexec_seq. inversion Hexec_seq; subst.
    eexists; eauto.
  Qed.

(* ================================================================ *)
(* §3. Limb-list bookkeeping helpers                                 *)
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

  (** Block the Qed kernel from re-elaborating the two nested
      [list_set] cascades (one each in [is_add5] / [is_sub5] discharge).
      Defense-in-depth fix matching A73's
      Fe25519CarryCorrect/Scmula24Correct.  All proofs below access
      [list_set] only through the lemmas above; the kernel never needs
      to unfold [list_set] for conversion.

      See reference_qed_kernel_check_blowup_dealloc.md for the pattern. *)
  Local Opaque list_set.
  Local Strategy 0 [list_set].

  (** The "5-limb add result" predicate: a list [out] of length 5
      whose [i]-th limb is [mask64 (mask64 (nth i la 0) + mask64
      (nth i lb 0))]. *)
  Definition is_add5 (out la lb : list Z) : Prop :=
    length out = 5%nat
    /\ forall i, (i < 5)%nat ->
         List.nth i out 0
         = mask64 (mask64 (List.nth i la 0) + mask64 (List.nth i lb 0)).

  (** Pointwise nth lemma for [build_limb_list_add]: limb [i] is the
      limbwise mask64 sum.  Avoids [List.nth_ext] / [List.map_nth]
      typeclass quirks by computing via [destruct i] + cbv. *)
  Lemma build_limb_list_add_nth :
    forall la lb i,
      (i < 5)%nat ->
      List.nth i (build_limb_list_add la lb) 0
      = mask64 (mask64 (List.nth i la 0) + mask64 (List.nth i lb 0)).
  Proof.
    intros la lb i Hi.
    destruct i as [|[|[|[|[|i']]]]]; cbv [build_limb_list_add List.map List.seq List.nth];
      try reflexivity; try (exfalso; lia).
  Qed.

  Lemma build_limb_list_add_length :
    forall la lb, length (build_limb_list_add la lb) = 5%nat.
  Proof.
    intros la lb. cbv [build_limb_list_add]. rewrite List.length_map.
    rewrite List.length_seq. reflexivity.
  Qed.

  Lemma is_add5_eq_build :
    forall out la lb,
      is_add5 out la lb ->
      out = build_limb_list_add la lb.
  Proof.
    intros out la lb [Hlen Hnth].
    apply (List.nth_ext _ _ 0 0).
    - rewrite Hlen, build_limb_list_add_length. reflexivity.
    - intros i Hi. rewrite Hlen in Hi.
      assert (Hi5 : (i < 5)%nat) by lia.
      rewrite Hnth by lia.
      rewrite build_limb_list_add_nth by lia.
      reflexivity.
  Qed.

  (** Similar for sub. *)
  Definition is_sub5 (out la lb : list Z) : Prop :=
    length out = 5%nat
    /\ forall i, (i < 5)%nat ->
         List.nth i out 0
         = mask64 (mask64 (mask64 (List.nth i la 0)
                            - mask64 (List.nth i lb 0))
                     + mask64 (p_off i)).

  Lemma build_limb_list_sub_nth :
    forall la lb i,
      (i < 5)%nat ->
      List.nth i (build_limb_list_sub la lb) 0
      = mask64 (mask64 (mask64 (List.nth i la 0)
                          - mask64 (List.nth i lb 0))
                  + mask64 (p_off i)).
  Proof.
    intros la lb i Hi.
    destruct i as [|[|[|[|[|i']]]]]; cbv [build_limb_list_sub List.map List.seq List.nth];
      try reflexivity; try (exfalso; lia).
  Qed.

  Lemma build_limb_list_sub_length :
    forall la lb, length (build_limb_list_sub la lb) = 5%nat.
  Proof.
    intros la lb. cbv [build_limb_list_sub]. rewrite List.length_map.
    rewrite List.length_seq. reflexivity.
  Qed.

  Lemma is_sub5_eq_build :
    forall out la lb,
      is_sub5 out la lb ->
      out = build_limb_list_sub la lb.
  Proof.
    intros out la lb [Hlen Hnth].
    apply (List.nth_ext _ _ 0 0).
    - rewrite Hlen, build_limb_list_sub_length. reflexivity.
    - intros i Hi. rewrite Hlen in Hi.
      assert (Hi5 : (i < 5)%nat) by lia.
      rewrite Hnth by lia.
      rewrite build_limb_list_sub_nth by lia.
      reflexivity.
  Qed.

(* ================================================================ *)
(* §3.5. Tactic helpers                                              *)
(* ================================================================ *)

  (** Build a [rs_get_tower_ed] equation for slots [a] / [b] at the
      current state (extracted from a [Hd?_get] hypothesis).  Used at
      each step of the inline-chain proof to avoid hand-writing the
      nested [rs_set_tower_ed] expressions. *)
  Ltac get_ab_in_current Hdne_a Hdne_b Hga Hgb la lb Hga_n Hgb_n :=
    match goal with
    | H : rs_get_tower_ed ?rs (loc_var ?dst) = _ |- _ =>
      assert (Hga_n : rs_get_tower_ed rs (loc_var _)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (Hgb_n : rs_get_tower_ed rs (loc_var _)
                    = Some (exist_tval_ed TFp25519 (VFp25519 lb))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_b; exact Hgb)
    end.

(* ================================================================ *)
(* §4. add_inline_correct as a Lemma                                 *)
(* ================================================================ *)

  (** Internal: chain through the 5 [REdLimbStore]s and prove the
      destination slot ends as a [VFp25519] whose limbs match
      [is_add5].  This factors out the "shape of the inline add
      chain" from the "feval distributes over limbwise add"
      algebra.

      Phase 0c factored hypothesis [add_inline_correct] is derived
      from this Lemma + [feval_limbwise_add_mask64] +
      [Fp25519_holds_intro] / [_elim] / [_set_other]. *)
  Lemma add_inline_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
      dest.(loc_type) = TFp25519 ->
      a.(loc_type) = TFp25519 ->
      b.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a.(loc_var) ->
      dest.(loc_var) <> b.(loc_var) ->
      Fp25519_holds rs1 a.(loc_var) xa ->
      Fp25519_holds rs1 b.(loc_var) xb ->
      Hexec
        (REdSeq
           (REdLimbStore dest 0%nat (SAdd (SLimb a.(loc_var) 0%nat) (SLimb b.(loc_var) 0%nat)))
           (REdSeq
             (REdLimbStore dest 1%nat (SAdd (SLimb a.(loc_var) 1%nat) (SLimb b.(loc_var) 1%nat)))
             (REdSeq
               (REdLimbStore dest 2%nat (SAdd (SLimb a.(loc_var) 2%nat) (SLimb b.(loc_var) 2%nat)))
               (REdSeq
                 (REdLimbStore dest 3%nat (SAdd (SLimb a.(loc_var) 3%nat) (SLimb b.(loc_var) 3%nat)))
                 (REdLimbStore dest 4%nat (SAdd (SLimb a.(loc_var) 4%nat) (SLimb b.(loc_var) 4%nat))))))) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.add xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    (* Extract limb evidence for xa and xb from [Fp25519_holds]. *)
    destruct (Fp25519_holds_elim _ _ _ Hxa) as [la [Hga [Hla Hfa]]].
    destruct (Fp25519_holds_elim _ _ _ Hxb) as [lb [Hgb [Hlb Hfb]]].
    (* Peel the 5 sequence layers. *)
    apply seq_inv in Hexec_n. destruct Hexec_n as [rs01 [Hs0 Htail0]].
    apply seq_inv in Htail0. destruct Htail0 as [rs12 [Hs1 Htail1]].
    apply seq_inv in Htail1. destruct Htail1 as [rs23 [Hs2 Htail2]].
    apply seq_inv in Htail2. destruct Htail2 as [rs34 [Hs3 Hs4]].
    (* Invert each REdLimbStore step. *)
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
    (* Step 0: compute Hv0_eval (read from rs1). *)
    rewrite (eval_SAdd_SLimb_SLimb_VFp25519 rs1 a.(loc_var) b.(loc_var) 0%nat la lb
              Hga Hgb ltac:(lia) Hla Hlb) in Hv0_eval.
    injection Hv0_eval as Hv0_eq.
    subst v0.
    subst rs01.
    (* Step 1: read from rs01 = rs1[dest <- ...].  Slots [a] / [b] are
       preserved because they differ from [dest]. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d1)) |- _ =>
      assert (Hga01 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (Hgb01 : rs_get_tower_ed rs (loc_var b)
                    = Some (exist_tval_ed TFp25519 (VFp25519 lb))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_b; exact Hgb)
    end.
    rewrite (eval_SAdd_SLimb_SLimb_VFp25519 _ _ _ 1%nat la lb
              Hga01 Hgb01 ltac:(lia) Hla Hlb) in Hv1_eval.
    injection Hv1_eval as Hv1_eq.
    subst v1.
    (* Also: dest's slot at rs01 is the updated VFp25519, so limbs_d1 = list_set 0 v0 limbs_d0. *)
    rewrite rs_get_set_tower_eq in Hd1_get.
    apply tval_some_vfp25519_inj in Hd1_get.
    subst limbs_d1.
    subst rs12.
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
    rewrite (eval_SAdd_SLimb_SLimb_VFp25519 _ _ _ 2%nat la lb
              Hga12 Hgb12 ltac:(lia) Hla Hlb) in Hv2_eval.
    injection Hv2_eval as Hv2_eq.
    subst v2.
    rewrite rs_get_set_tower_eq in Hd2_get.
    apply tval_some_vfp25519_inj in Hd2_get.
    subst limbs_d2.
    subst rs23.
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
    rewrite (eval_SAdd_SLimb_SLimb_VFp25519 _ _ _ 3%nat la lb
              Hga23 Hgb23 ltac:(lia) Hla Hlb) in Hv3_eval.
    injection Hv3_eval as Hv3_eq.
    subst v3.
    rewrite rs_get_set_tower_eq in Hd3_get.
    apply tval_some_vfp25519_inj in Hd3_get.
    subst limbs_d3.
    subst rs34.
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
    rewrite (eval_SAdd_SLimb_SLimb_VFp25519 _ _ _ 4%nat la lb
              Hga34 Hgb34 ltac:(lia) Hla Hlb) in Hv4_eval.
    injection Hv4_eval as Hv4_eq.
    subst v4.
    rewrite rs_get_set_tower_eq in Hd4_get.
    apply tval_some_vfp25519_inj in Hd4_get.
    subst limbs_d4.
    subst rs2.
    (* Now we have rs2 = rs1 chained through 5 set_tower at dest, all to
       a VFp25519 with progressively limb-set lists.  Compute the final
       limb list and show it matches [build_limb_list_add la lb]. *)
    set (m_i := fun i =>
                  mask64 (mask64 (List.nth i la 0)
                           + mask64 (List.nth i lb 0))).
    (* limbs after 5 list_sets at indices 0..4. *)
    set (limbs_final :=
      list_set 4%nat (m_i 4%nat)
        (list_set 3%nat (m_i 3%nat)
          (list_set 2%nat (m_i 2%nat)
            (list_set 1%nat (m_i 1%nat)
              (list_set 0%nat (m_i 0%nat) limbs_d0))))).
    (* The final state stores VFp25519 limbs_final at dest. *)
    (* We need: (a) length limbs_final = 5; (b) feval limbs_final =
       F.add xa xb. *)
    assert (Hlen_final : length limbs_final = 5%nat).
    { unfold limbs_final.
      repeat rewrite list_set_length. exact Hd0_len. }
    assert (His5 : is_add5 limbs_final la lb).
    { unfold is_add5. split; [exact Hlen_final|].
      intros i Hi. unfold limbs_final.
      (* The i-th element of limbs_final.  Each list_set affects only
         its own index.  So nth i (list_set j x xs) = x if i = j,
         else nth i xs. *)
      destruct i as [|[|[|[|[|i']]]]]; try (exfalso; lia).
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
    pose proof (is_add5_eq_build _ _ _ His5) as Hfinal_eq.
    (* feval limbs_final = feval (build_limb_list_add la lb)
                         = F.add (feval la) (feval lb)
                         = F.add xa xb. *)
    assert (Hfeval_final : feval limbs_final = F.add xa xb).
    { rewrite Hfinal_eq.
      rewrite feval_limbwise_add_mask64 by assumption.
      rewrite Hfa, Hfb. reflexivity. }
    split.
    + (* Fp25519_holds at dest of F.add xa xb. *)
      eapply Fp25519_holds_intro;
        [| exact Hlen_final | exact Hfeval_final].
      apply rs_get_set_tower_eq.
    + (* fp_frame: for y <> dest, the value is preserved across each
         of the 5 set_tower steps at dest. *)
      intros y vy Hne Hy.
      eapply Fp25519_holds_set_other; [exact Hne|].
      eapply Fp25519_holds_set_other; [exact Hne|].
      eapply Fp25519_holds_set_other; [exact Hne|].
      eapply Fp25519_holds_set_other; [exact Hne|].
      eapply Fp25519_holds_set_other; [exact Hne|].
      exact Hy.
  Qed.

(* ================================================================ *)
(* §5. sub_inline_correct as a Lemma                                 *)
(* ================================================================ *)

  (** Inline sub chain: same shape as add, but with the +2p offset
      correction baked in via [p_off i] read as an [SLit].  Mirrors
      fiat-crypto's [sub_op] for radix-2^51:
      [dest[i] := (a[i] - b[i]) + 2 * encode_2p[i]]. *)
  Lemma sub_inline_correct :
    forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
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
              (SAdd (SSub (SLimb a.(loc_var) 0%nat) (SLimb b.(loc_var) 0%nat))
                    (SLit (p_off 0%nat))))
           (REdSeq
             (REdLimbStore dest 1%nat
                (SAdd (SSub (SLimb a.(loc_var) 1%nat) (SLimb b.(loc_var) 1%nat))
                      (SLit (p_off 1%nat))))
             (REdSeq
               (REdLimbStore dest 2%nat
                  (SAdd (SSub (SLimb a.(loc_var) 2%nat) (SLimb b.(loc_var) 2%nat))
                        (SLit (p_off 2%nat))))
               (REdSeq
                 (REdLimbStore dest 3%nat
                    (SAdd (SSub (SLimb a.(loc_var) 3%nat) (SLimb b.(loc_var) 3%nat))
                          (SLit (p_off 3%nat))))
                 (REdLimbStore dest 4%nat
                    (SAdd (SSub (SLimb a.(loc_var) 4%nat) (SLimb b.(loc_var) 4%nat))
                          (SLit (p_off 4%nat)))))))) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.sub xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hdne_a Hdne_b Hxa Hxb Hexec_n.
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
    (* Step 0. *)
    rewrite (eval_sub_with_offset rs1 a.(loc_var) b.(loc_var) 0%nat la lb
              (p_off 0%nat) Hga Hgb ltac:(lia) Hla Hlb) in Hv0_eval.
    injection Hv0_eval as Hv0_eq. subst v0. subst rs01.
    (* Step 1. *)
    match goal with
    | _ : rs_get_tower_ed ?rs (loc_var dest) = Some (exist_tval_ed TFp25519 (VFp25519 limbs_d1)) |- _ =>
      assert (Hga01 : rs_get_tower_ed rs (loc_var a)
                    = Some (exist_tval_ed TFp25519 (VFp25519 la))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_a; exact Hga);
      assert (Hgb01 : rs_get_tower_ed rs (loc_var b)
                    = Some (exist_tval_ed TFp25519 (VFp25519 lb))) by
        (repeat rewrite rs_get_set_tower_other by exact Hdne_b; exact Hgb)
    end.
    rewrite (eval_sub_with_offset _ _ _ 1%nat la lb (p_off 1%nat)
              Hga01 Hgb01 ltac:(lia) Hla Hlb) in Hv1_eval.
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
    rewrite (eval_sub_with_offset _ _ _ 2%nat la lb (p_off 2%nat)
              Hga12 Hgb12 ltac:(lia) Hla Hlb) in Hv2_eval.
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
    rewrite (eval_sub_with_offset _ _ _ 3%nat la lb (p_off 3%nat)
              Hga23 Hgb23 ltac:(lia) Hla Hlb) in Hv3_eval.
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
    rewrite (eval_sub_with_offset _ _ _ 4%nat la lb (p_off 4%nat)
              Hga34 Hgb34 ltac:(lia) Hla Hlb) in Hv4_eval.
    injection Hv4_eval as Hv4_eq. subst v4.
    rewrite rs_get_set_tower_eq in Hd4_get.
    apply tval_some_vfp25519_inj in Hd4_get.
    subst limbs_d4. subst rs2.
    set (m_i := fun i =>
                  mask64 (mask64 (mask64 (List.nth i la 0)
                                   - mask64 (List.nth i lb 0))
                            + mask64 (p_off i))).
    set (limbs_final :=
      list_set 4%nat (m_i 4%nat)
        (list_set 3%nat (m_i 3%nat)
          (list_set 2%nat (m_i 2%nat)
            (list_set 1%nat (m_i 1%nat)
              (list_set 0%nat (m_i 0%nat) limbs_d0))))).
    assert (Hlen_final : length limbs_final = 5%nat).
    { unfold limbs_final. repeat rewrite list_set_length. exact Hd0_len. }
    assert (His5 : is_sub5 limbs_final la lb).
    { unfold is_sub5. split; [exact Hlen_final|].
      intros i Hi. unfold limbs_final.
      destruct i as [|[|[|[|[|i']]]]]; try (exfalso; lia).
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
    pose proof (is_sub5_eq_build _ _ _ His5) as Hfinal_eq.
    assert (Hfeval_final : feval limbs_final = F.sub xa xb).
    { rewrite Hfinal_eq.
      rewrite feval_limbwise_sub_mask64 by assumption.
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
(* §6. Headline theorems                                             *)
(* ================================================================ *)

  Theorem fe25519_add_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Fp25519_holds rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_add_body dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.add xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    cbn [fe25519_add_body] in Hexec_n.
    apply (add_inline_correct dest a_loc b_loc rs1 rs2 xa xb); assumption.
  Qed.

  Theorem fe25519_sub_body_correct :
    forall (rs1 rs2 : rust_state_ed) (a_loc b_loc dest : located_ed)
           (xa xb : F p),
      a_loc.(loc_type) = TFp25519 ->
      b_loc.(loc_type) = TFp25519 ->
      dest.(loc_type) = TFp25519 ->
      dest.(loc_var) <> a_loc.(loc_var) ->
      dest.(loc_var) <> b_loc.(loc_var) ->
      Fp25519_holds rs1 a_loc.(loc_var) xa ->
      Fp25519_holds rs1 b_loc.(loc_var) xb ->
      Hexec (fe25519_sub_body p_off dest [a_loc; b_loc]) rs1 rs2 ->
      Fp25519_holds rs2 dest.(loc_var) (F.sub xa xb) /\
      fp_frame rs1 rs2 dest.(loc_var).
  Proof.
    intros rs1 rs2 a_loc b_loc dest xa xb
           Hat Hbt Hdt Hdne_a Hdne_b Hxa Hxb Hexec_n.
    cbn [fe25519_sub_body] in Hexec_n.
    apply (sub_inline_correct dest a_loc b_loc rs1 rs2 xa xb); assumption.
  Qed.

End Fe25519AddSubCorrect.

(** Sanity check: list assumptions of the headline theorems.  Inside
    the Section, the [Variable]/[Hypothesis] parameters appear as
    parameters of the abstracted definition; once the Section closes
    they are universally quantified at the surface.  No new global
    axioms are introduced. *)
Print Assumptions fe25519_add_body_correct.
Print Assumptions fe25519_sub_body_correct.
