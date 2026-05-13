(** * BuildCombTableCorrect — functional correctness for the
 *     windowed comb-table initialiser.
 *
 *  Proves that after [build_comb_table_body], every cell
 *  [cells[i*16 + d]] (for [i ∈ 0..63], [d ∈ 0..15]) holds the
 *  Edwards-affine point [d · 16^i · B].
 *
 *  Architecture
 *  ============
 *  Following the [Fe25519InvertCorrect.v] / [Scalar25519FromWideCorrect.v]
 *  pattern: a Section parameterised by a [Cell_holds] predicate
 *  (which abstracts the per-element field encoding of the table)
 *  plus a [Fp_holds] predicate for the running base-point slot,
 *  with leaf-correctness [Hypothesis]es for [comb_cell_set],
 *  [point_mul16], and [fe25519_copy].
 *
 *  The proof structure relies on a generic [rfor_invariant] lemma
 *  for [REdFor] (analogous to the bedrock2 [while_invariant]),
 *  introduced in this file as a Section helper.  The lemma is
 *  reusable across other [REdFor] proofs.
 *
 *  Status: STATED.  The rfor_invariant helper is proved (Qed).
 *  The headline theorem [build_comb_table_correct] is stated and
 *  PARTIALLY DISCHARGED via the rfor_invariant skeleton.  The
 *  remaining 2× nested-loop bookkeeping (running the invariant for
 *  the inner loop is a separate rfor_invariant call) is documented
 *  in commentary and ADMITTED at the depth of the inner-loop
 *  invariant proof.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Init.Byte.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.BuildCombTableBody.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §1. Section parameters                                            *)
(* ================================================================ *)

Section BuildCombTableCorrect.

  Local Notation p := Curve25519.p.

  (** Abstract Edwards-point type.  At this layer we keep it
      [Type]-parametric; the bridge layer will instantiate it with
      [E.point] from [Curve25519.E]. *)
  Variable EPoint : Type.
  Variable epoint_zero : EPoint.
  Variable epoint_add : EPoint -> EPoint -> EPoint.
  Variable epoint_smul : Z -> EPoint -> EPoint.
  Variable B : EPoint.

  (** Cell predicate: [Cell_holds rs cells_slot i pt] iff the i-th
      element of the array slot [cells_slot] in [rs] decodes to the
      Edwards-affine point [pt]. *)
  Variable Cell_holds :
    rust_state_ed -> String.string -> nat -> EPoint -> Prop.

  (** Single-slot Fp encoding for the running base point. *)
  Variable Fp_holds : rust_state_ed -> String.string -> EPoint -> Prop.

  Variable callee_post :
    String.string -> list located_ed -> located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable callee_post_n :
    String.string -> list located_ed -> list located_ed ->
    rust_state_ed -> rust_state_ed -> Prop.
  Variable function_table : function_table_ed.

  Local Notation Hexec :=
    (rust_exec_ed callee_post callee_post_n function_table).

  (* ================================================================ *)
  (* §2.  Generic rfor_invariant helper                                *)
  (* ================================================================ *)

  (** Invariant-based reasoning for [REdFor]: if [I k] holds for
      [k ≤ n] when each loop step preserves [I], then [I n] holds
      after the loop.

      Iteration order (from [REdFor]'s [rexec_for_succ]): body runs
      first with [x := n] (the largest), then [REdFor x n body]
      runs (which runs body with [x := n-1], then [REdFor x (n-1)
      body], ...).  After [REdFor x m body], the variable [x] sees
      values [m-1, m-2, ..., 0] in order.

      The invariant [I k] should be read as "after running body
      for the [k] values [m-k, m-k-1, ..., m-1] (i.e., the [k] largest
      values up through [m-1])".  Equivalently, after [k]
      iterations from a starting point of [m], [I k] holds.

      Lemma signature: for any starting [rs1] with [I 0] in [rs1],
      after [REdFor x m body] terminates in [rs2], [I m] holds in
      [rs2]; provided each step preserves [I].  We state the step
      condition in terms of the executed value [v ∈ {0, ..., m-1}].
  *)
  Lemma rfor_invariant
        (x : String.string)
        (n : nat)
        (body : rust_cmd_ed)
        (I : nat -> rust_state_ed -> Prop)
        (step :
          forall k rs rs',
            (k < n)%nat ->
            I k rs ->
            Hexec body (rs_set_scalar_ed rs x (Z.of_nat (n - S k))) rs' ->
            I (S k) rs') :
    forall rs1 rs2,
      I 0%nat rs1 ->
      Hexec (REdFor x n body) rs1 rs2 ->
      I n rs2.
  Proof.
    assert (Hstrong :
      forall m,
        (m <= n)%nat ->
        forall s1 s2,
          I (n - m)%nat s1 ->
          Hexec (REdFor x m body) s1 s2 ->
          I n s2).
    { induction m as [|m IH]; intros Hmn s1 s2 HIk Hexec_m.
      - inversion Hexec_m; subst.
        rewrite Nat.sub_0_r in HIk. exact HIk.
      - inversion Hexec_m; subst.
        assert (Hkbound : (n - S m < n)%nat) by lia.
        assert (Hsub_eq : (n - S (n - S m) = m)%nat) by lia.
        pose proof
          (step (n - S m)%nat s1 rs2 Hkbound HIk
                (eq_rect _ (fun z => Hexec body
                              (rs_set_scalar_ed s1 x (Z.of_nat z)) rs2)
                         H4 _ (eq_sym Hsub_eq))) as HI_succ.
        apply (IH (Nat.lt_le_incl _ _ Hmn) rs2 s2).
        + replace (n - m)%nat with (S (n - S m))%nat by lia.
          exact HI_succ.
        + exact H5. }
    intros rs1 rs2 HI0 Hexec_for.
    apply (Hstrong n (le_n n) rs1 rs2).
    - rewrite Nat.sub_diag. exact HI0.
    - exact Hexec_for.
  Qed.

  (* ================================================================ *)
  (* §3.  Top-level theorem (stated)                                   *)
  (* ================================================================ *)

  (** [comb_cell_set] leaf: at iteration where the loop variable
      [i_v=i] (taking values 63, 62, …, 0 from [REdFor]) carries the
      iteration index, and the running base
      [base_i = 16^(63 - i) · B] is in scope, sets
      cells[(63 - i)*16 + d] to [d · 16^(63 - i) · B] and preserves
      all other cells.

      Equivalently, writing [k = 63 - i] (so [k] runs 0, 1, …, 63),
      the leaf writes cells[k*16+d] := d · 16^k · B.  This is the
      table layout the spec expects.

      Stated as a [Hypothesis] over the multi-output [REdCallN]
      semantics — [cells] is the single (in-place) destination. *)
  Hypothesis comb_cell_set_correct :
    forall (cells base_i : located_ed) (i_slot d_slot : String.string)
           (rs1 rs2 : rust_state_ed) (i d : nat) (cells_state : nat -> EPoint)
           (base_i_pt : EPoint),
      cells.(loc_type) = TArr 1024 TFp25519 ->
      base_i.(loc_type) = TFp25519 ->
      (i < 64)%nat ->
      (d < 16)%nat ->
      base_i_pt = epoint_smul (16 ^ Z.of_nat (63 - i))%Z B ->
      Fp_holds rs1 base_i.(loc_var) base_i_pt ->
      rs_get_scalar_ed rs1 i_slot = Some (Z.of_nat i) ->
      rs_get_scalar_ed rs1 d_slot = Some (Z.of_nat d) ->
      (forall j, (j < 1024)%nat -> Cell_holds rs1 cells.(loc_var) j (cells_state j)) ->
      Hexec (REdCallN "comb_cell_set" [cells]
              [{| loc_var := i_slot; loc_type := TU64 |}
              ;{| loc_var := d_slot; loc_type := TU64 |}
              ; base_i]) rs1 rs2 ->
      (* Post: cells[(63 - i)*16+d] = d · 16^(63 - i) · B; other cells preserved;
         base_i and the scalars preserved. *)
      Cell_holds rs2 cells.(loc_var) ((63 - i) * 16 + d)%nat
        (epoint_smul (Z.of_nat d) base_i_pt) /\
      (forall j, (j < 1024)%nat -> j <> ((63 - i) * 16 + d)%nat ->
                 Cell_holds rs2 cells.(loc_var) j (cells_state j)) /\
      Fp_holds rs2 base_i.(loc_var) base_i_pt /\
      rs_get_scalar_ed rs2 i_slot = Some (Z.of_nat i) /\
      rs_get_scalar_ed rs2 d_slot = Some (Z.of_nat d).

  (** [point_mul16] leaf: in-place [base_i := 16 · base_i]; preserves
      the cells array (idx-major) and all scalar slots. *)
  Hypothesis point_mul16_correct :
    forall (base_i : located_ed) (rs1 rs2 : rust_state_ed)
           (base_i_pt : EPoint),
      base_i.(loc_type) = TFp25519 ->
      Fp_holds rs1 base_i.(loc_var) base_i_pt ->
      Hexec (REdCall "point_mul16" base_i [base_i]) rs1 rs2 ->
      Fp_holds rs2 base_i.(loc_var) (epoint_smul 16 base_i_pt) /\
      (* Cells preserved. *)
      (forall cells_var j v,
          Cell_holds rs1 cells_var j v -> Cell_holds rs2 cells_var j v).

  (** [fe25519_copy] leaf: dest := src (Fp encoding). *)
  Hypothesis copy_correct :
    forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (pt : EPoint),
      dest.(loc_type) = TFp25519 ->
      src.(loc_type) = TFp25519 ->
      dest.(loc_var) <> src.(loc_var) ->
      Fp_holds rs1 src.(loc_var) pt ->
      Hexec (REdCall "fe25519_copy" dest [src]) rs1 rs2 ->
      Fp_holds rs2 dest.(loc_var) pt /\
      (forall cells_var j v,
          Cell_holds rs1 cells_var j v -> Cell_holds rs2 cells_var j v).

  (** [REdLetZero] of a TArr 1024 TFp25519 / TU64 / TFp25519 slot
      preserves the cell/fp predicates at a distinct slot name. *)
  Hypothesis let_zero_preserves_cell :
    forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
           (v : rust_val_ed t) (cells_var : String.string)
           (j : nat) (pt : EPoint),
      cells_var <> x ->
      Cell_holds rs cells_var j pt ->
      Cell_holds (rs_set_tower_ed rs x (exist_tval_ed t v)) cells_var j pt.

  Hypothesis let_zero_preserves_fp :
    forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
           (v : rust_val_ed t) (y : String.string) (pt : EPoint),
      y <> x ->
      Fp_holds rs y pt ->
      Fp_holds (rs_set_tower_ed rs x (exist_tval_ed t v)) y pt.

  (** [rs_set_scalar_ed] preserves Cell_holds and Fp_holds, since both
      predicates depend only on the tower component of the state. *)
  Hypothesis scalar_set_preserves_cell :
    forall (rs : rust_state_ed) (x : String.string) (z : Z)
           (cells_var : String.string) (j : nat) (pt : EPoint),
      Cell_holds rs cells_var j pt ->
      Cell_holds (rs_set_scalar_ed rs x z) cells_var j pt.

  Hypothesis scalar_set_preserves_fp :
    forall (rs : rust_state_ed) (x : String.string) (z : Z)
           (y : String.string) (pt : EPoint),
      Fp_holds rs y pt ->
      Fp_holds (rs_set_scalar_ed rs x z) y pt.

  (** [rs_set_scalar_ed] obviously sets the scalar at [x]; these two
      lemmas are provable directly from the [list]-based store
      definition.  Kept inside the section as plain [Lemma]s. *)
  Lemma scalar_set_get_same :
    forall (rs : rust_state_ed) (x : String.string) (z : Z),
      rs_get_scalar_ed (rs_set_scalar_ed rs x z) x = Some z.
  Proof.
    intros rs x z. unfold rs_get_scalar_ed, rs_set_scalar_ed; cbn.
    induction (rs_scalar_ed rs) as [|[y w] tail IH]; cbn.
    - now rewrite String.eqb_refl.
    - destruct (String.eqb y x) eqn:Hyx.
      + apply String.eqb_eq in Hyx. subst y. cbn. now rewrite String.eqb_refl.
      + cbn. rewrite (String.eqb_sym x y), Hyx. exact IH.
  Qed.

  Lemma scalar_set_get_other :
    forall (rs : rust_state_ed) (x y : String.string) (z : Z),
      x <> y ->
      rs_get_scalar_ed (rs_set_scalar_ed rs x z) y =
      rs_get_scalar_ed rs y.
  Proof.
    intros rs x y z Hne.
    unfold rs_get_scalar_ed, rs_set_scalar_ed; cbn.
    induction (rs_scalar_ed rs) as [|[w u] tail IH]; cbn.
    - destruct (String.eqb y x) eqn:Hyx; [|reflexivity].
      apply String.eqb_eq in Hyx. subst y. exfalso; apply Hne; reflexivity.
    - destruct (String.eqb w x) eqn:Hwx; cbn.
      + apply String.eqb_eq in Hwx. subst w.
        destruct (String.eqb y x) eqn:Hyx; cbn.
        * apply String.eqb_eq in Hyx. subst y. exfalso; apply Hne; reflexivity.
        * reflexivity.
      + destruct (String.eqb y w) eqn:Hyw; cbn.
        * reflexivity.
        * exact IH.
  Qed.

  (** Algebraic Hypotheses on the abstract scalar multiplication.  These
      are properties that any sensible group implementation will
      satisfy ([epoint_smul] = scalar multiplication by Z, instantiated
      at the bridge layer by [E.mul] / [Z.to_nat] over the Edwards
      curve).  Kept as Section [Hypothesis]es so the section stays
      group-agnostic; they will be discharged at the bridge instantiation. *)

  Hypothesis epoint_smul_one :
    epoint_smul 1%Z B = B.

  Hypothesis epoint_smul_compose :
    forall (a b : Z) (X : EPoint),
      epoint_smul a (epoint_smul b X) = epoint_smul (a * b)%Z X.

  (** Cells / Fp predicates respect equality of the held point —
      needed to push algebraic rewrites through opaque predicates. *)
  Hypothesis Cell_holds_eq :
    forall rs cv j p p',
      p = p' -> Cell_holds rs cv j p -> Cell_holds rs cv j p'.

  Hypothesis Fp_holds_eq :
    forall rs y p p',
      p = p' -> Fp_holds rs y p -> Fp_holds rs y p'.

  (* ================================================================ *)
  (* §4.  Headline statement                                           *)
  (* ================================================================ *)

  (** The headline correctness claim: after [build_comb_table_body
      _dest [cells_loc; B_loc]] with input [B_loc] holding the base
      point [B], every cell holds the expected scalar multiple.

      Status: STRUCTURAL proof skeleton closes everything down to the
      outer-step [Hstep_outer] sub-lemma.  The outer step itself
      requires a NESTED [rfor_invariant] over the 16-iteration inner
      loop, with a 6-conjunct [I_inner] invariant.  The inner-loop
      step lemma involves a [cells_state] reconstruction that
      requires non-trivial [j = (j/16)*16 + j mod 16] arithmetic
      reasoning; closing it cleanly without a TermErr cascade is left
      as a single [Admitted] hypothesis below.  Once that single
      hypothesis is discharged (we sketch it in commentary), the
      [Qed] above closes mechanically.

      We use one [Admitted Hstep_outer_admit] hypothesis — the outer
      step lemma — chosen so that the discharge is local: closing it
      does not require restating any global Section invariant. *)
  Theorem build_comb_table_correct :
    forall (rs1 rs2 : rust_state_ed)
           (cells_loc B_loc dest : located_ed),
      cells_loc.(loc_type) = TArr 1024 TFp25519 ->
      B_loc.(loc_type) = TFp25519 ->
      (* Pre: cells start as the zero point in every cell, B_loc
         holds B, and the named scratch slots are fresh. *)
      Fp_holds rs1 B_loc.(loc_var) B ->
      (forall j, (j < 1024)%nat ->
                 Cell_holds rs1 cells_loc.(loc_var) j epoint_zero) ->
      cells_loc.(loc_var) <> "base_i" ->
      cells_loc.(loc_var) <> "i_v" ->
      cells_loc.(loc_var) <> "d_v" ->
      B_loc.(loc_var) <> "base_i" ->
      B_loc.(loc_var) <> "i_v" ->
      B_loc.(loc_var) <> "d_v" ->
      cells_loc.(loc_var) <> B_loc.(loc_var) ->
      Hexec (build_comb_table_body dest [cells_loc; B_loc]) rs1 rs2 ->
      (* Post: every cell holds the expected scalar-multiple of B. *)
      forall (i d : nat),
        (i < 64)%nat ->
        (d < 16)%nat ->
        Cell_holds rs2 cells_loc.(loc_var) (i * 16 + d)%nat
          (epoint_smul (Z.of_nat d * (16 ^ Z.of_nat i))%Z B).
  Proof.
    intros rs1 rs2 cells_loc B_loc dest Hct Hbt HB Hzero
           Hcb Hci Hcd HBb HBi HBd HcB Hexec_n i d Hi Hd.
    cbn [build_comb_table_body] in Hexec_n.
    (* Peel REdLetZero "base_i" *)
    inversion Hexec_n; subst; clear Hexec_n.
    set (rs_a := rs_set_tower_ed rs1 "base_i" (exist_tval_ed TFp25519 v)) in *.
    assert (HB_a : Fp_holds rs_a (loc_var B_loc) B)
      by (unfold rs_a; apply let_zero_preserves_fp; auto).
    assert (Hzero_a : forall j, (j < 1024)%nat ->
                                Cell_holds rs_a (loc_var cells_loc) j epoint_zero)
      by (intros j Hj; unfold rs_a; apply let_zero_preserves_cell; auto).
    clearbody rs_a. clear H4 rs1 HB Hzero v. rename H5 into Hexec_n.
    (* Peel REdLetZero "i_v" *)
    inversion Hexec_n; subst; clear Hexec_n.
    set (rs_b := rs_set_tower_ed rs_a "i_v" (exist_tval_ed TU64 v)) in *.
    assert (HB_b : Fp_holds rs_b (loc_var B_loc) B)
      by (unfold rs_b; apply let_zero_preserves_fp; auto).
    assert (Hzero_b : forall j, (j < 1024)%nat ->
                                Cell_holds rs_b (loc_var cells_loc) j epoint_zero)
      by (intros j Hj; unfold rs_b; apply let_zero_preserves_cell; auto).
    clearbody rs_b. clear H4 rs_a HB_a Hzero_a v. rename H5 into Hexec_n.
    (* Peel REdLetZero "d_v" *)
    inversion Hexec_n; subst; clear Hexec_n.
    set (rs_c := rs_set_tower_ed rs_b "d_v" (exist_tval_ed TU64 v)) in *.
    assert (HB_c : Fp_holds rs_c (loc_var B_loc) B)
      by (unfold rs_c; apply let_zero_preserves_fp; auto).
    assert (Hzero_c : forall j, (j < 1024)%nat ->
                                Cell_holds rs_c (loc_var cells_loc) j epoint_zero)
      by (intros j Hj; unfold rs_c; apply let_zero_preserves_cell; auto).
    clearbody rs_c. clear H4 rs_b HB_b Hzero_b v. rename H5 into Hexec_n.
    (* Peel REdSeq: fe25519_copy then REdFor *)
    inversion Hexec_n; subst; clear Hexec_n.
    rename H1 into Hcpy. rename H4 into Hfor.
    pose proof (copy_correct (LFp "base_i") B_loc rs_c rs0 B
                eq_refl Hbt) as Hcpy_post.
    cbn [LFp loc_var loc_type] in Hcpy_post.
    specialize (Hcpy_post (ltac:(intro Heq; symmetry in Heq; contradiction))
                 HB_c Hcpy).
    destruct Hcpy_post as [Hbase_i_0 Hcells_frame_0].
    assert (Hzero_0 : forall j, (j < 1024)%nat ->
                                Cell_holds rs0 (loc_var cells_loc) j epoint_zero)
      by (intros j Hj; apply Hcells_frame_0; apply Hzero_c; assumption).
    clear Hzero_c Hcpy Hcells_frame_0 HB_c.
    (* Set up the outer-loop invariant *)
    pose (I_outer := fun (k : nat) (rs : rust_state_ed) =>
      Fp_holds rs "base_i" (epoint_smul (16 ^ Z.of_nat k)%Z B) /\
      (forall i' d', (i' < k)%nat -> (d' < 16)%nat ->
          Cell_holds rs cells_loc.(loc_var) (i' * 16 + d')%nat
            (epoint_smul (Z.of_nat d' * 16 ^ Z.of_nat i')%Z B)) /\
      (forall j, (k * 16 <= j < 1024)%nat ->
          Cell_holds rs cells_loc.(loc_var) j epoint_zero)).
    assert (Hinit_outer : I_outer 0%nat rs0).
    { unfold I_outer.
      split; [|split].
      - replace (16 ^ Z.of_nat 0)%Z with 1%Z by reflexivity.
        eapply Fp_holds_eq; [|exact Hbase_i_0]. symmetry; apply epoint_smul_one.
      - intros; lia.
      - intros j Hj; apply Hzero_0; lia. }
    clear Hbase_i_0 Hzero_0.
    (* The big outer step: prove the invariant is preserved.  The
       inner [REdFor] runs an inner [rfor_invariant] underneath. *)
    assert (Hstep_outer : forall k rs rs',
      (k < 64)%nat ->
      I_outer k rs ->
      Hexec (outer_loop_cmd "i_v" "d_v" cells_loc (LFp "base_i"))
        (rs_set_scalar_ed rs "i_v" (Z.of_nat (64 - S k))) rs' ->
      I_outer (S k) rs').
    { intros k rs rs' Hk HI Hexec_body.
      unfold I_outer in HI. destruct HI as [Hbase_k [Hwritten_k Hzero_k]].
      unfold outer_loop_cmd in Hexec_body.
      inversion Hexec_body; subst; clear Hexec_body.
      rename H1 into Hexec_inner. rename H4 into Hexec_mul.
      set (rs_pre := rs_set_scalar_ed rs "i_v" (Z.of_nat (64 - S k))) in *.
      (* The scalar set preserves all tower-based predicates. *)
      assert (Hbase_pre : Fp_holds rs_pre "base_i"
                              (epoint_smul (16 ^ Z.of_nat k)%Z B))
        by (unfold rs_pre; apply scalar_set_preserves_fp; assumption).
      assert (Hwritten_pre : forall i' d', (i' < k)%nat -> (d' < 16)%nat ->
            Cell_holds rs_pre (loc_var cells_loc) (i' * 16 + d')%nat
              (epoint_smul (Z.of_nat d' * 16 ^ Z.of_nat i')%Z B))
        by (intros; unfold rs_pre; apply scalar_set_preserves_cell;
            apply Hwritten_k; lia).
      assert (Hzero_pre : forall j, (k * 16 <= j < 1024)%nat ->
            Cell_holds rs_pre (loc_var cells_loc) j epoint_zero)
        by (intros; unfold rs_pre; apply scalar_set_preserves_cell;
            apply Hzero_k; lia).
      assert (Hiv_pre : rs_get_scalar_ed rs_pre "i_v"
                          = Some (Z.of_nat (63 - k))).
      { unfold rs_pre. replace (64 - S k)%nat with (63 - k)%nat by lia.
        apply scalar_set_get_same. }
      clear Hbase_k Hwritten_k Hzero_k.
      (* ====================================================== *)
      (* The inner-loop discharge requires a 6-conjunct          *)
      (* invariant + a [cells_state] reconstruction using        *)
      (* [j = (j/16)*16 + j mod 16] arithmetic.  Closing it      *)
      (* cleanly without breaking under unification cascades     *)
      (* requires careful sub-lemmas.  We leave this single      *)
      (* inner-step admit; the structural outer skeleton above   *)
      (* is fully discharged.                                    *)
      (* ====================================================== *)
      admit. }
    (* Apply rfor_invariant to the outer loop. *)
    pose proof (rfor_invariant "i_v" 64%nat
                  (outer_loop_cmd "i_v" "d_v" cells_loc (LFp "base_i"))
                  I_outer Hstep_outer rs0 rs2 Hinit_outer Hfor)
      as Hfinal_outer.
    unfold I_outer in Hfinal_outer.
    destruct Hfinal_outer as [_ [Hwritten _]].
    apply Hwritten; lia.
  Admitted.

End BuildCombTableCorrect.

(* Sanity check. *)
Print Assumptions build_comb_table_correct.
