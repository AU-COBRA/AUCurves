(** * RustCmdRupicola — Rupicola-style compile framework for [rust_cmd_ed]
 *
 * Parallel to [fiat-crypto/rupicola/src/Rupicola/Lib/Compiler.v], but
 * targeting our typed-slot AST [rust_cmd_ed] (see [SafeRustEd25519Sim.v])
 * rather than bedrock2's [Syntax.cmd].
 *
 * Why a separate compile framework?  See
 * [docs/bedrock2-vs-rustcmd.md] for the architectural argument.
 *
 * Status (2026-05-10): foundational framework + 10 core compile lemmas
 * giving 100% coverage of [rust_cmd_ed]: skip, seq, let-zero, let-u64,
 * scalar-set, call, if-nz, while-nz (well-founded measure + invariant),
 * byte-store, byte-load.  Parallel to Rupicola's [compile_skip],
 * [compile_seq], etc.
 *
 * Tier 2 (2026-05-10): Rupicola-style pattern lemmas — all Qed.
 * [compile_red_nlet], [compile_red_unset],
 * [compile_red_downto], [compile_red_ranged_for].
 * The downto/ranged-for lemmas carry an explicit frame premise
 * asserting that the loop body preserves the counter slot
 * [i_var]; with that premise the trailing decrement/increment
 * [REdScalarSet] evaluates correctly and the inductive step closes.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Arith.Wf_nat.
From Stdlib Require Import Arith.PeanoNat.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. Gallina nlet bookkeeping                                       *)
(* ================================================================ *)

(** Rupicola-style let-binding wrapper.  The [vars] argument is purely
    documentation (records the source-level variable name for
    pretty-printing / proof-search hints); semantically [nlet_red vars
    v k] is just [k v].

    Mirrors Rupicola's [nlet] in [fiat-crypto/rupicola/src/Rupicola/Lib/Core.v]. *)
Definition nlet_red {A B : Type} (vars : list String.string) (v : A)
                    (k : A -> B) : B := k v.

(* ================================================================ *)
(* §1. Hoare-style triple over rust_exec_ed                           *)
(* ================================================================ *)

Section RustTriple.
  Context (callee_post : String.string -> list located_ed -> located_ed ->
                         rust_state_ed -> rust_state_ed -> Prop).
  Context (callee_post_n : String.string -> list located_ed -> list located_ed ->
                           rust_state_ed -> rust_state_ed -> Prop).
  Context (function_table : function_table_ed).

  Definition rpred := rust_state_ed -> Prop.

  (** Hoare-style triple: starting from [rs], executing [c] yields
      a state satisfying [pred]. *)
  Definition rhoare (rs : rust_state_ed) (c : rust_cmd_ed) (pred : rpred) : Prop :=
    forall rs', rust_exec_ed callee_post callee_post_n function_table c rs rs' -> pred rs'.

  (* ================================================================ *)
  (* §2. Core compile lemmas                                            *)
  (* ================================================================ *)

  Lemma compile_red_skip :
    forall (rs : rust_state_ed) (pred : rpred),
      pred rs ->
      rhoare rs REdSkip pred.
  Proof.
    intros rs pred Hpred rs' Hexec.
    inversion Hexec; subst. exact Hpred.
  Qed.

  Lemma compile_red_seq :
    forall (rs : rust_state_ed) (c0 c1 : rust_cmd_ed) (pred0 pred1 : rpred),
      rhoare rs c0 pred0 ->
      (forall rs_mid, pred0 rs_mid -> rhoare rs_mid c1 pred1) ->
      rhoare rs (REdSeq c0 c1) pred1.
  Proof.
    intros rs c0 c1 pred0 pred1 H0 H1 rs' Hexec.
    inversion Hexec; subst.
    apply H1 with (rs_mid := rs2).
    - apply H0. assumption.
    - assumption.
  Qed.

  (** Path B (post-2026-05-09): rexec_let_zero is parametric over the
      initial value. For Rupicola usage, the body's triple typically
      doesn't depend on the initial value (the first REdCall to that
      slot overwrites it), so the forall is satisfied uniformly. *)
  Lemma compile_red_let_zero :
    forall (rs : rust_state_ed) (x : var) (t : tower_type_ed)
           (body : rust_cmd_ed) (pred : rpred),
      (forall v, well_formed_ed v ->
                 rhoare (rs_set_tower_ed rs x (exist_tval_ed t v)) body pred) ->
      rhoare rs (REdLetZero x t body) pred.
  Proof.
    intros rs x t body pred Hbody rs' Hexec.
    inversion Hexec; subst.
    eapply Hbody; eassumption.
  Qed.

  Lemma compile_red_let_u64 :
    forall (rs : rust_state_ed) (x : var) (e : sexpr_ed) (v : Z)
           (body : rust_cmd_ed) (pred : rpred),
      eval_sexpr_ed rs e = Some v ->
      rhoare (rs_set_scalar_ed rs x v) body pred ->
      rhoare rs (REdLetU64 x e body) pred.
  Proof.
    intros rs x e v body pred Heval Hbody rs' Hexec.
    inversion Hexec; subst.
    match goal with H : eval_sexpr_ed _ _ = Some _ |- _ =>
      rewrite Heval in H; inversion H; subst end.
    apply Hbody. assumption.
  Qed.

  Lemma compile_red_scalar_set :
    forall (rs : rust_state_ed) (x : var) (e : sexpr_ed) (v : Z) (pred : rpred),
      eval_sexpr_ed rs e = Some v ->
      pred (rs_set_scalar_ed rs x v) ->
      rhoare rs (REdScalarSet x e) pred.
  Proof.
    intros rs x e v pred Heval Hpred rs' Hexec.
    inversion Hexec; subst.
    match goal with H : eval_sexpr_ed _ _ = Some _ |- _ =>
      rewrite Heval in H; inversion H; subst end.
    exact Hpred.
  Qed.

  Lemma compile_red_call :
    forall (rs : rust_state_ed) (fname : String.string)
           (dst : located_ed) (args : list located_ed) (pred : rpred),
      (forall rs', callee_post fname args dst rs rs' -> pred rs') ->
      rhoare rs (REdCall fname dst args) pred.
  Proof.
    intros rs fname dst args pred Hcp rs' Hexec.
    inversion Hexec; subst. apply Hcp. assumption.
  Qed.

  Lemma compile_red_if_nz :
    forall (rs : rust_state_ed) (e : sexpr_ed) (c1 c2 : rust_cmd_ed)
           (pred : rpred),
      (forall v, eval_sexpr_ed rs e = Some v -> v <> 0 ->
                 rhoare rs c1 pred) ->
      (eval_sexpr_ed rs e = Some 0 -> rhoare rs c2 pred) ->
      rhoare rs (REdIfNz e c1 c2) pred.
  Proof.
    intros rs e c1 c2 pred Hnz Hz rs' Hexec.
    inversion Hexec; subst.
    - apply Hz; assumption.
    - eapply Hnz; eauto.
  Qed.

  (** Loop with measure + invariant.  Mirrors bedrock2's
      [wp_bridge_while_nz] in [SafeRustEd25519WPBridge.v]: a
      well-founded measure [lt] on [M] plus a per-step invariant
      [inv : M -> rust_state_ed -> Prop] suffices to discharge the
      [REdWhileNz] case.

      At each iteration: evaluating the condition either yields 0
      (loop exits, invariant gives [pred rs]) or a non-zero value
      (the body's transition produces a new state with smaller
      measure, and we apply the inductive hypothesis). *)
  Lemma compile_red_while_nz :
    forall (M : Type) (lt : M -> M -> Prop) (inv : M -> rust_state_ed -> Prop)
           (rs : rust_state_ed) (e : sexpr_ed) (body : rust_cmd_ed)
           (pred : rpred) (m0 : M),
      well_founded lt ->
      inv m0 rs ->
      (forall m rs_i,
         inv m rs_i ->
         (forall vc, eval_sexpr_ed rs_i e = Some vc -> vc <> 0 ->
            forall rs_after, rust_exec_ed callee_post callee_post_n function_table body rs_i rs_after ->
                             exists m', inv m' rs_after /\ lt m' m) /\
         (eval_sexpr_ed rs_i e = Some 0 -> pred rs_i)) ->
      rhoare rs (REdWhileNz e body) pred.
  Proof.
    intros M lt inv rs e body pred m0 Hwf Hinv0 Hstep.
    revert rs Hinv0.
    induction m0 as [m0 IH] using (well_founded_ind Hwf).
    intros rs Hinv_rs rs' Hexec.
    inversion Hexec; subst.
    - (* while_zero: condition evaluates to 0 *)
      destruct (Hstep m0 rs' Hinv_rs) as [_ Hzero].
      apply Hzero. assumption.
    - (* while_nonzero: body steps, then loop continues *)
      destruct (Hstep m0 rs Hinv_rs) as [Hnz _].
      specialize (Hnz v ltac:(assumption) ltac:(assumption) rs2 ltac:(assumption)).
      destruct Hnz as [m' [Hinv_m' Hlt_m']].
      eapply IH; eauto.
  Qed.

  Lemma compile_red_byte_store :
    forall (rs : rust_state_ed) (loc : located_ed) (idx_e val_e : sexpr_ed)
           (idx_v val_v : Z) (n : nat) (bs_old : list Byte.byte) (pred : rpred),
      eval_sexpr_ed rs idx_e = Some idx_v ->
      eval_sexpr_ed rs val_e = Some val_v ->
      loc.(loc_type) = TBytes n ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed (TBytes n) (VBytes n bs_old)) ->
      pred (rs_set_tower_ed rs loc.(loc_var)
              (exist_tval_ed (TBytes n)
                 (VBytes n (list_set_byte (Z.to_nat idx_v) (Z_to_byte val_v) bs_old)))) ->
      rhoare rs (REdByteStore loc idx_e val_e) pred.
  Proof.
    intros rs loc idx_e val_e idx_v val_v n bs_old pred
           Hidx Hval Hlt Hget Hpred rs' Hexec.
    inversion Hexec; subst.
    match goal with H : eval_sexpr_ed rs idx_e = Some _ |- _ =>
      rewrite Hidx in H; inversion H; subst end.
    match goal with H : eval_sexpr_ed rs val_e = Some _ |- _ =>
      rewrite Hval in H; inversion H; subst end.
    match goal with H : loc_type loc = TBytes _ |- _ =>
      rewrite Hlt in H; inversion H; subst end.
    match goal with H : rs_get_tower_ed rs (loc_var loc) = Some _ |- _ =>
      rewrite Hget in H; inversion H; subst end.
    exact Hpred.
  Qed.

  Lemma compile_red_byte_load :
    forall (rs : rust_state_ed) (x : var) (loc : located_ed) (idx_e : sexpr_ed)
           (idx_v : Z) (n : nat) (bs : list Byte.byte) (b : Byte.byte) (pred : rpred),
      eval_sexpr_ed rs idx_e = Some idx_v ->
      loc.(loc_type) = TBytes n ->
      rs_get_tower_ed rs loc.(loc_var) =
        Some (exist_tval_ed (TBytes n) (VBytes n bs)) ->
      List.nth_error bs (Z.to_nat idx_v) = Some b ->
      pred (rs_set_scalar_ed rs x (Z.of_N (Byte.to_N b))) ->
      rhoare rs (REdByteLoad x loc idx_e) pred.
  Proof.
    intros rs x loc idx_e idx_v n bs b pred
           Hidx Hlt Hget Hnth Hpred rs' Hexec.
    inversion Hexec; subst.
    match goal with H : eval_sexpr_ed rs idx_e = Some _ |- _ =>
      rewrite Hidx in H; inversion H; subst end.
    match goal with H : loc_type loc = TBytes _ |- _ =>
      rewrite Hlt in H; inversion H; subst end.
    match goal with H : rs_get_tower_ed rs (loc_var loc) = Some _ |- _ =>
      rewrite Hget in H; inversion H; subst end.
    match goal with H : nth_error _ (Z.to_nat _) = Some _ |- _ =>
      rewrite Hnth in H; inversion H; subst end.
    exact Hpred.
  Qed.

  (* ================================================================ *)
  (* §2.5. Tier 2 — Rupicola-style pattern lemmas                       *)
  (* ================================================================ *)

  (** [compile_red_nlet]: discharge a triple whose post is wrapped in
      [nlet_red].  Since [nlet_red vars v k] reduces to [k v], the
      triple is equivalent to the unwrapped one.  This is the analogue
      of Rupicola's [compile_nlet_as_nlet_eq] up to the obvious
      simplification (we don't need an equational hypothesis because
      the post is fixed, not derived). *)
  Lemma compile_red_nlet :
    forall rs c (A : Type) (vars : list String.string) (v : A)
           (k : A -> rpred),
      rhoare rs c (k v) ->
      rhoare rs c (fun rs' => nlet_red vars v k rs').
  Proof.
    intros rs c A vars v k Hk rs' Hexec.
    unfold nlet_red. apply Hk. exact Hexec.
  Qed.

  (** [compile_red_unset]: drop a no-longer-needed slot from the post.
      Since [rust_state_ed] doesn't have an explicit "remove" op, this
      is a semantic no-op that exists for symmetry with Rupicola's
      [compile_unsets].  At proof time it's just a weakening that lets
      the user state a stronger post (mentioning [x]) when only a
      weaker one is needed. *)
  Lemma compile_red_unset :
    forall rs c (x : var) (pred : rpred),
      rhoare rs c pred ->
      rhoare rs c (fun rs' => exists v, rs_get_scalar_ed rs' x = v /\ pred rs').
  Proof.
    intros rs c x pred Htrip rs' Hexec.
    exists (rs_get_scalar_ed rs' x). split.
    - reflexivity.
    - apply Htrip. exact Hexec.
  Qed.

  (** [compile_red_downto]: bounded countdown loop driven by a u64
      counter [i_var] that starts at [n0] and decrements to 0.  The
      loop body must (a) re-establish the user's invariant for the
      decremented index and (b) update the [i_var] slot to the new
      value (typically via the standard tail
      [REdScalarSet i_var (i_var - 1)]).

      Discharged structurally via [compile_red_while_nz] using the
      counter value as a well-founded measure on [nat]. *)
  Lemma compile_red_downto :
    forall (rs : rust_state_ed) (n0 : nat) (i_var : var)
           (body : rust_cmd_ed)
           (Acc : Type) (acc_inv : Acc -> nat -> rust_state_ed -> Prop)
           (acc0 : Acc) (pred : rpred),
      acc_inv acc0 n0 rs ->
      rs_get_scalar_ed rs i_var = Some (Z.of_nat n0) ->
      (Z.of_nat n0 < 2^64) ->
      (forall i acc rs_i,
         (i > 0)%nat ->
         (Z.of_nat i < 2^64) ->
         acc_inv acc i rs_i ->
         rs_get_scalar_ed rs_i i_var = Some (Z.of_nat i) ->
         forall rs_after,
           rust_exec_ed callee_post callee_post_n function_table body rs_i rs_after ->
           (* Frame condition: body preserves the loop counter slot.
              Without this, the trailing [REdScalarSet i_var (SSub
              (SVar i_var) (SLit 1))] could compute from a
              body-clobbered value. *)
           rs_get_scalar_ed rs_after i_var = Some (Z.of_nat i) /\
           exists acc',
             acc_inv acc' (i - 1)%nat
               (rs_set_scalar_ed rs_after i_var (Z.of_nat (i - 1)))
             /\ rs_get_scalar_ed
                  (rs_set_scalar_ed rs_after i_var (Z.of_nat (i - 1)))
                  i_var = Some (Z.of_nat (i - 1))) ->
      (forall acc rs_final,
         acc_inv acc 0%nat rs_final ->
         rs_get_scalar_ed rs_final i_var = Some 0%Z ->
         pred rs_final) ->
      rhoare rs
        (REdWhileNz (SLt (SLit 0) (SVar i_var))
           (REdSeq body (REdScalarSet i_var (SSub (SVar i_var) (SLit 1)))))
        pred.
  Proof.
    intros rs n0 i_var body Acc acc_inv acc0 pred
           Hinv0 Hcnt0 Hbnd0 Hstep Hfinish.
    (* Invariant for compile_red_while_nz: track current counter +
       acc_inv at that counter. *)
    set (inv :=
      fun (i : nat) (rs_i : rust_state_ed) =>
        (Z.of_nat i < 2^64) /\
        rs_get_scalar_ed rs_i i_var = Some (Z.of_nat i) /\
        exists acc, acc_inv acc i rs_i).
    eapply compile_red_while_nz with
      (M := nat) (lt := Peano.lt) (inv := inv) (m0 := n0).
    - exact Nat.lt_wf_0.
    - subst inv. cbn.
      split; [exact Hbnd0|].
      split; [exact Hcnt0|].
      exists acc0. exact Hinv0.
    - intros m rs_i Hinv_m.
      destruct Hinv_m as [Hbnd_m [Hcnt_m [acc_m Hacc_m]]].
      split.
      + (* nonzero condition: derive that m > 0, step body+decrement *)
        intros vc Heval Hvc rs_after Hexec.
        (* Heval : eval_sexpr_ed rs_i (SLt (SLit 0) (SVar i_var)) = Some vc *)
        simpl in Heval.
        rewrite Hcnt_m in Heval.
        change (mask64 0) with 0 in Heval.
        assert (Hmpos : (m > 0)%nat).
        { destruct m as [|m']; [|lia].
          simpl in Heval. inversion Heval; subst.
          exfalso. apply Hvc. reflexivity. }
        (* Body+decrement step: invert the REdSeq.  Inversion on
           [rust_exec_ed callee_post (REdSeq body decr) rs_i rs_after]
           yields [rs2] (post-body), [H1] (body executed to rs2), and
           [H4] (decrement executed at rs2 to rs_after). *)
        inversion Hexec; subst.
        (* Apply Hstep at (m, acc_m, rs_i).  Yields the frame
           condition Hframe : rs2(i_var) = Some (Z.of_nat m) and the
           inv-step witness for (m - 1). *)
        specialize (Hstep m acc_m rs_i Hmpos Hbnd_m Hacc_m Hcnt_m rs2 H1).
        destruct Hstep as [Hframe [acc' [Hacc' Hcnt']]].
        (* Invert the trailing REdScalarSet: rs_after =
           rs_set_scalar_ed rs2 i_var v, where
           v = mask64 (Z.of_nat m - 1) = Z.of_nat (m - 1). *)
        inversion H4; subst.
        match goal with
        | H : eval_sexpr_ed rs2 (SSub (SVar i_var) (SLit 1)) = Some _ |- _ =>
          simpl in H;
          rewrite Hframe in H;
          change (mask64 1) with 1 in H;
          inversion H; subst; clear H
        end.
        (* The new state is rs_set_scalar_ed rs2 i_var
           (mask64 (Z.of_nat m - 1)).  Rewrite to Z.of_nat (m - 1). *)
        assert (Hmask : mask64 (Z.of_nat m - 1) = Z.of_nat (m - 1)).
        { unfold mask64. rewrite Z.land_ones by lia.
          rewrite Z.mod_small by lia.
          rewrite Nat2Z.inj_sub by lia. cbn. lia. }
        rewrite Hmask.
        exists (m - 1)%nat. split.
        * subst inv. cbn.
          split; [lia|].
          split; [exact Hcnt' | exists acc'; exact Hacc'].
        * lia.
      + (* zero condition: m = 0, finish using Hfinish *)
        intros Heval0.
        simpl in Heval0.
        rewrite Hcnt_m in Heval0.
        change (mask64 0) with 0 in Heval0.
        assert (Hm0 : m = 0%nat).
        { destruct m as [|m']; [reflexivity|].
          exfalso.
          assert (Hpos : (0 <? Z.of_nat (S m'))%Z = true) by (apply Z.ltb_lt; lia).
          rewrite Hpos in Heval0. inversion Heval0. }
        subst m.
        eapply Hfinish; [exact Hacc_m | exact Hcnt_m].
  Qed.

  (** [compile_red_ranged_for]: bounded for-loop counting up from 0 to
      a fixed bound [n].  Symmetric to [compile_red_downto].

      The form here uses [REdWhileNz (SLt (SVar i_var) (SLit (Z.of_nat n)))].
      Body must update [i_var] to [i + 1] (typically via
      [REdScalarSet i_var (i_var + 1)]).

      Same structural reduction to [compile_red_while_nz] with measure
      [n - i] on [nat].  Identical gap to [compile_red_downto] in
      identifying the post-body counter value. *)
  Lemma compile_red_ranged_for :
    forall (rs : rust_state_ed) (n : nat) (i_var : var)
           (body : rust_cmd_ed)
           (Acc : Type) (acc_inv : Acc -> nat -> rust_state_ed -> Prop)
           (acc0 : Acc) (pred : rpred),
      acc_inv acc0 0%nat rs ->
      rs_get_scalar_ed rs i_var = Some 0%Z ->
      (Z.of_nat n < 2^64) ->
      (forall i acc rs_i,
         (i < n)%nat ->
         acc_inv acc i rs_i ->
         rs_get_scalar_ed rs_i i_var = Some (Z.of_nat i) ->
         forall rs_after,
           rust_exec_ed callee_post callee_post_n function_table body rs_i rs_after ->
           (* Frame condition: body preserves the loop counter slot.
              Without this, the trailing [REdScalarSet i_var (SAdd
              (SVar i_var) (SLit 1))] could compute from a
              body-clobbered value. *)
           rs_get_scalar_ed rs_after i_var = Some (Z.of_nat i) /\
           exists acc',
             acc_inv acc' (i + 1)%nat
               (rs_set_scalar_ed rs_after i_var (Z.of_nat (i + 1)))
             /\ rs_get_scalar_ed
                  (rs_set_scalar_ed rs_after i_var (Z.of_nat (i + 1)))
                  i_var = Some (Z.of_nat (i + 1))) ->
      (forall acc rs_final,
         acc_inv acc n rs_final ->
         rs_get_scalar_ed rs_final i_var = Some (Z.of_nat n) ->
         pred rs_final) ->
      rhoare rs
        (REdWhileNz (SLt (SVar i_var) (SLit (Z.of_nat n)))
           (REdSeq body (REdScalarSet i_var (SAdd (SVar i_var) (SLit 1)))))
        pred.
  Proof.
    intros rs n i_var body Acc acc_inv acc0 pred
           Hinv0 Hcnt0 Hbnd Hstep Hfinish.
    set (inv :=
      fun (m : nat) (rs_i : rust_state_ed) =>
        let i := (n - m)%nat in
        (m <= n)%nat /\
        rs_get_scalar_ed rs_i i_var = Some (Z.of_nat i) /\
        exists acc, acc_inv acc i rs_i).
    eapply compile_red_while_nz with
      (M := nat) (lt := Peano.lt) (inv := inv) (m0 := n).
    - exact Nat.lt_wf_0.
    - subst inv. cbn.
      replace (n - n)%nat with 0%nat by lia.
      split; [lia|].
      split; [exact Hcnt0|].
      exists acc0. exact Hinv0.
    - intros m rs_i Hinv_m.
      destruct Hinv_m as [Hmle [Hcnt_m [acc_m Hacc_m]]].
      set (i := (n - m)%nat) in *.
      split.
      + (* nonzero condition *)
        intros vc Heval Hvc rs_after Hexec.
        (* Heval :
           Some (if Z.of_nat i <? mask64 (Z.of_nat n) then 1 else 0) = Some vc
           Since vc <> 0, deduce i < n. *)
        simpl in Heval.
        rewrite Hcnt_m in Heval.
        unfold mask64 in Heval.
        rewrite Z.land_ones in Heval by lia.
        rewrite (Z.mod_small (Z.of_nat n) (2^64)) in Heval by lia.
        assert (Hilt : (i < n)%nat).
        { destruct (Nat.ltb i n) eqn:Hlt.
          - apply Nat.ltb_lt; assumption.
          - exfalso. apply Nat.ltb_ge in Hlt.
            assert (Hge : (Z.of_nat i <? Z.of_nat n) = false)
              by (apply Z.ltb_ge; lia).
            rewrite Hge in Heval. inversion Heval; subst.
            apply Hvc. reflexivity. }
        (* Body+increment step: invert the REdSeq. *)
        inversion Hexec; subst.
        (* Apply Hstep at (i, acc_m, rs_i). *)
        specialize (Hstep i acc_m rs_i Hilt Hacc_m Hcnt_m rs2 H1).
        destruct Hstep as [Hframe [acc' [Hacc' Hcnt']]].
        (* Invert the trailing REdScalarSet. *)
        inversion H4; subst.
        match goal with
        | H : eval_sexpr_ed rs2 (SAdd (SVar i_var) (SLit 1)) = Some _ |- _ =>
          simpl in H;
          rewrite Hframe in H;
          change (mask64 1) with 1 in H;
          inversion H; subst; clear H
        end.
        (* mask64 (Z.of_nat i + 1) = Z.of_nat (i + 1). *)
        assert (Hmask : mask64 (Z.of_nat i + 1) = Z.of_nat (i + 1)).
        { unfold mask64. rewrite Z.land_ones by lia.
          rewrite Z.mod_small by lia.
          rewrite Nat2Z.inj_add. cbn. lia. }
        rewrite Hmask.
        (* New measure m' = m - 1, so n - m' = n - m + 1 = i + 1. *)
        exists (m - 1)%nat. split.
        * subst inv. cbn.
          assert (Hieq : (n - (m - 1))%nat = (i + 1)%nat).
          { unfold i. lia. }
          rewrite Hieq.
          split; [lia|].
          split; [exact Hcnt' | exists acc'; exact Hacc'].
        * lia.
      + (* zero condition: i = n, finish via Hfinish *)
        intros Heval0.
        simpl in Heval0.
        rewrite Hcnt_m in Heval0.
        unfold mask64 in Heval0.
        rewrite Z.land_ones in Heval0 by lia.
        rewrite (Z.mod_small (Z.of_nat n) (2^64)) in Heval0 by lia.
        assert (Him : (i >= n)%nat).
        { destruct (Nat.ltb i n) eqn:Hlt.
          - exfalso. apply Nat.ltb_lt in Hlt.
            assert (Hpos : (Z.of_nat i <? Z.of_nat n)%Z = true)
              by (apply Z.ltb_lt; lia).
            rewrite Hpos in Heval0. inversion Heval0.
          - apply Nat.ltb_ge in Hlt. lia. }
        assert (Hi : i = n).
        { unfold i. unfold i in Him. lia. }
        eapply Hfinish.
        * rewrite <- Hi. exact Hacc_m.
        * rewrite Hcnt_m. f_equal. f_equal. exact Hi.
  Qed.

  (** [compile_red_for]: bounded for-loop driven by the new [REdFor x n
      body] AST constructor (no fuel; [n] is structurally decreasing).
      Body sees the iteration variable [x] take values [n-1, n-2, ..., 0]
      in order, matching the inductive semantics
      [rexec_for_zero] / [rexec_for_succ] (see [SafeRustEd25519Sim.v]).

      Unlike [compile_red_downto] / [compile_red_ranged_for], this lemma
      drives an [REdFor] directly — no manual counter management or
      condition-evaluation ladder, since the AST encodes the bound [n]
      structurally.  Proof is by induction on [n]. *)
  Lemma compile_red_for :
    forall (x : var) (n : nat) (body : rust_cmd_ed)
           (Acc : Type) (acc_inv : Acc -> nat -> rust_state_ed -> Prop)
           (acc0 : Acc) (pred : rpred) (rs : rust_state_ed),
      acc_inv acc0 n rs ->
      (forall i acc rs_i,
         (i < n)%nat ->
         acc_inv acc (S i) rs_i ->
         forall rs_after,
           rust_exec_ed callee_post callee_post_n function_table body
             (rs_set_scalar_ed rs_i x (Z.of_nat i)) rs_after ->
           exists acc', acc_inv acc' i rs_after) ->
      (forall acc rs_final, acc_inv acc 0%nat rs_final -> pred rs_final) ->
      rhoare rs (REdFor x n body) pred.
  Proof.
    intros x n body Acc acc_inv acc0 pred rs Hinv0 Hstep Hfinish.
    (* Generalize on the quantitative part of the hypotheses so the
       induction on n can rewrap the residual loop trip count. *)
    revert rs acc0 Hinv0 Hstep.
    induction n as [|n IH]; intros rs acc0 Hinv0 Hstep rs' Hexec.
    - (* n = 0 : REdFor x 0 body executes trivially *)
      inversion Hexec; subst.
      eapply Hfinish; eauto.
    - (* n = S n' : body runs once with x := n', then REdFor x n' body *)
      inversion Hexec as
        [ | | | | | | | | | | | | | ? n_inv body_inv rs_pre rs_mid rs_post
                                       Hbody Hloop | | | | | | | | ];
        subst.
      pose proof (Hstep n acc0 rs ltac:(lia) Hinv0 _ Hbody) as Hacc'_ex.
      destruct Hacc'_ex as [acc' Hacc'].
      eapply IH with (acc0 := acc'); [exact Hacc' | | exact Hloop].
      intros i acc rs_i Hilt Hai rs_after Hexec_body.
      eapply Hstep with (i := i) (acc := acc) (rs_i := rs_i);
        [lia | exact Hai | exact Hexec_body].
  Qed.

  (* ================================================================ *)
  (* §3. Weakening                                                      *)
  (* ================================================================ *)

  (** [compile_red_select]: constant-time conditional move.  Given a
      Rupicola-level predicate that handles BOTH branches of [cond]
      (cond zero -> if_f copied; cond non-zero -> if_t copied), the
      [REdSelect] compiles to a state where the predicate holds.

      Unlike [compile_red_if_nz], the [REdSelect] AST commits to a
      single tower update at [dest.(loc_var)] regardless of cond, so
      the post-state shape is always
      [rs_set_tower_ed rs dest.(loc_var) tv]
      where [tv] is the source tval at [if_t.(loc_var)] (cond ≠ 0)
      or [if_f.(loc_var)] (cond = 0). *)
  Lemma compile_red_select :
    forall (cond : sexpr_ed) (if_t if_f dest : located_ed)
           (rs : rust_state_ed) (pred : rpred),
      (forall cond_v src tv,
         eval_sexpr_ed rs cond = Some cond_v ->
         src = (if Z.eqb cond_v 0 then if_f else if_t) ->
         if_t.(loc_type) = dest.(loc_type) ->
         if_f.(loc_type) = dest.(loc_type) ->
         rs_get_tower_ed rs src.(loc_var) = Some tv ->
         pred (rs_set_tower_ed rs dest.(loc_var) tv)) ->
      rhoare rs (REdSelect cond if_t if_f dest) pred.
  Proof.
    intros cond if_t if_f dest rs pred Hpred rs' Hexec.
    inversion Hexec; subst.
    eapply Hpred; eauto.
  Qed.

  Lemma rhoare_weaken :
    forall rs c (pred1 pred2 : rpred),
      (forall rs', pred1 rs' -> pred2 rs') ->
      rhoare rs c pred1 ->
      rhoare rs c pred2.
  Proof.
    intros rs c pred1 pred2 Himpl Htrip rs' Hexec.
    apply Himpl. apply Htrip. exact Hexec.
  Qed.

  (** [compile_red_calln]: multi-output FFI call.  Given any
      callee_post_n hypothesis ensuring rs1 → rs2 implies the post
      predicate, the [REdCallN] compiles via direct inversion on
      [rust_exec_ed] (single rule [rexec_calln]). *)
  Lemma compile_red_calln :
    forall (rs : rust_state_ed) (fname : String.string)
           (dests args : list located_ed) (pred : rpred),
      (forall rs', callee_post_n fname dests args rs rs' -> pred rs') ->
      rhoare rs (REdCallN fname dests args) pred.
  Proof.
    intros rs fname dests args pred Hcpn rs' Hexec.
    inversion Hexec; subst. apply Hcpn. assumption.
  Qed.

  (** [compile_red_callfn]: verified-helper-function call.  Given that
      [fname] resolves to [body] in the function_table AND that the
      body's rhoare triple holds for [pred], the [REdCallFn] compiles
      via inversion on [rexec_callfn].  This is the bridge from a
      verifiable function body to a callsite — replacing the
      axiomatic [callee_post]-style discharge with one mechanized in
      this framework. *)
  Lemma compile_red_callfn :
    forall (rs : rust_state_ed) (fname : String.string)
           (dest : located_ed) (args : list located_ed)
           (body : function_body_ed) (pred : rpred),
      List.find (fun p => String.eqb (fst p) fname) function_table = Some (fname, body) ->
      rhoare rs (body dest args) pred ->
      rhoare rs (REdCallFn fname dest args) pred.
  Proof.
    intros rs fname dest args body pred Hfind Hbody rs' Hexec.
    inversion Hexec; subst.
    (* Inversion gives a witness body0 with [List.find ... = Some (fname, body0)].
       Combined with our [Hfind] hypothesis (same lookup, body), the pair
       Some-constructor injectivity forces body0 = body. *)
    match goal with
    | Hfind' : List.find _ _ = Some (_, ?body0) |- _ =>
        rewrite Hfind in Hfind';
        injection Hfind' as Hbeq;
        subst body0
    end.
    apply Hbody. assumption.
  Qed.

  (** [compile_red_block]: scoped-allocation block.  [REdBlock body]
      is semantically transparent — running it from [rs] is the same
      as running [body] from [rs] — so its [rhoare] triple reduces
      to the body's.  The Rust / C emitters wrap [body] in [{ ... }]
      so that any [REdLetZero] decls inside have their lifetime end
      at the closing brace. *)
  Lemma compile_red_block :
    forall (rs : rust_state_ed) (body : rust_cmd_ed) (pred : rpred),
      rhoare rs body pred ->
      rhoare rs (REdBlock body) pred.
  Proof.
    intros rs body pred Hbody rs' Hexec.
    inversion Hexec; subst.
    apply Hbody. assumption.
  Qed.

End RustTriple.

(* ================================================================ *)
(* §3.5. Scalar-env helper (used by §4 demo)                          *)
(* ================================================================ *)

(** Lookup at the just-updated key. *)
Lemma lookup_s_ed_update_at : forall env x v,
  lookup_s_ed (update_in_place_s_ed env x v) x = Some v.
Proof.
  induction env as [| [y w] rest IH]; intros x v.
  - cbn. rewrite String.eqb_refl. reflexivity.
  - cbn. destruct (String.eqb y x) eqn:Hyx.
    + cbn. rewrite String.eqb_refl. reflexivity.
    + cbn. destruct (String.eqb x y) eqn:Hxy.
      * apply String.eqb_eq in Hxy; subst.
        rewrite String.eqb_refl in Hyx; discriminate.
      * apply IH.
Qed.

(* ================================================================ *)
(* §4. Demo: verified helper-function dispatch                       *)
(* ================================================================ *)

(** A 2-instruction verified helper that doubles a u64-typed slot
    by writing [x + x] into the dest's scalar binding.  Body shape:

      REdLetU64 "tmp" (SAdd (SVar x_var) (SVar x_var))
        (REdScalarSet "dest_var" (SVar "tmp"))

    The slot read uses [SVar (loc_var of args.(0))].  Since the
    [function_body_ed] type takes [dest] / [args] positionally, the
    body decodes the slot names from those. *)
Definition double_u64_body_ed : function_body_ed :=
  fun (dest : located_ed) (args : list located_ed) =>
    match args with
    | x :: _ =>
        REdLetU64 "double_tmp"
          (SAdd (SVar x.(loc_var)) (SVar x.(loc_var)))
          (REdScalarSet dest.(loc_var) (SVar "double_tmp"))
    | [] => REdSkip
    end.

(** Sample function table containing the double helper. *)
Definition demo_function_table : function_table_ed :=
  [("double_u64"%string, double_u64_body_ed)].

(** Demonstration: a [compile_red_callfn] application discharges
    [rhoare] for a [REdCallFn "double_u64"] callsite by inlining
    the body and applying the existing [compile_red_*] lemmas.

    The post-condition asserts that after the call, the destination
    slot holds [mask64 (v+v)] where [v] is the original input value. *)
Lemma compile_red_callfn_demo :
  forall (callee_post :
            String.string -> list located_ed -> located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (rs : rust_state_ed) (x_var : String.string) (v : Z),
    rs_get_scalar_ed rs x_var = Some v ->
    rhoare callee_post callee_post_n demo_function_table rs
      (REdCallFn "double_u64"%string {| loc_var := "dest_var"%string; loc_type := TU64 |}
                 [{| loc_var := x_var; loc_type := TU64 |}])
      (fun rs' => rs_get_scalar_ed rs' "dest_var"%string = Some (mask64 (v + v))).
Proof.
  intros callee_post callee_post_n rs x_var v Hget.
  eapply (compile_red_callfn _ _ demo_function_table rs "double_u64"%string
            {| loc_var := "dest_var"; loc_type := TU64 |}
            [{| loc_var := x_var; loc_type := TU64 |}] double_u64_body_ed);
    [reflexivity|].
  cbn [double_u64_body_ed].
  eapply compile_red_let_u64.
  { cbn. rewrite Hget. reflexivity. }
  intros rs' Hexec.
  inversion Hexec as [| | | | ? ? ? ? Heval | | | | | | | | | | | | | | | | |]; subst.
  (* Heval: eval_sexpr_ed of (SVar "double_tmp") in post-let_u64 state = Some v0.
     Reduce via [lookup_s_ed_update_at] to force v0 = mask64 (v+v). *)
  cbn in Heval.
  unfold rs_get_scalar_ed, rs_set_scalar_ed in Heval. cbn in Heval.
  rewrite lookup_s_ed_update_at in Heval. inversion Heval; subst.
  unfold rs_get_scalar_ed, rs_set_scalar_ed; cbn.
  rewrite lookup_s_ed_update_at. reflexivity.
Qed.

(* ================================================================ *)
(* §5. Demo: scoped-allocation block (REdBlock)                       *)
(* ================================================================ *)

(** Demonstration of [compile_red_block]: a scoped block containing a
    fresh [REdLetZero] tower slot.  Inside the block, the body
    declares a [TBytes 32] slot named ["tmp"] and runs [REdSkip].
    On block exit, the tmp slot's lifetime formally ends.  The post
    asserts only that the block ran (any [rs_well_formed]-respecting
    state is acceptable here). *)
Lemma compile_red_block_demo :
  forall (callee_post :
            String.string -> list located_ed -> located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (callee_post_n :
            String.string -> list located_ed -> list located_ed ->
            rust_state_ed -> rust_state_ed -> Prop)
         (function_table : function_table_ed)
         (rs : rust_state_ed),
    rhoare callee_post callee_post_n function_table rs
      (REdBlock (REdLetZero "tmp"%string (TBytes 32) REdSkip))
      (fun _ => True).
Proof.
  intros callee_post callee_post_n function_table rs.
  apply compile_red_block.
  apply compile_red_let_zero.
  intros v Hwf.
  apply compile_red_skip.
  exact I.
Qed.

(** ** Roadmap / status

    Tier 1: 10 core compile lemmas Qed: skip, seq, let_zero, let_u64,
    scalar_set, call, if_nz, while_nz, byte_store, byte_load —
    100% coverage of [rust_cmd_ed] constructors.

    Tier 2 (2026-05-10):
    - [compile_red_nlet] (Qed) — Gallina nlet pattern bookkeeping.
    - [compile_red_unset] (Qed) — drop a slot from the post (semantic
      no-op since [rust_state_ed] has no remove op).
    - [compile_red_downto] (Qed) — bounded countdown via
      [compile_red_while_nz]; carries a frame premise asserting the
      body preserves [i_var].
    - [compile_red_ranged_for] (Qed) — bounded for-loop, same
      frame-premise pattern as [compile_red_downto].

    Next steps:
    - Per-callee compile lemmas matching strong_callee_post's branches
      (compile_red_call_sha512, compile_red_call_scalar_reduce, etc.).
    - [Derive ... SuchThat ... As ...] skeleton analogous to
      bedrock2's, driving compile by reflection.
    - `compile_step` tactic that destructs lets and tries each
      [compile_red_*] hint.
    - End-to-end example: small protocol verified in this framework.

    Each step is bounded mechanical work; ~2-4 weeks for full feature
    parity with Rupicola, then per-protocol use is one [compile]
    tactic invocation.

    See [docs/bedrock2-vs-rustcmd.md] for the architectural argument
    and [docs/rustcmd-rupicola-roadmap.md] for the detailed plan. *)
