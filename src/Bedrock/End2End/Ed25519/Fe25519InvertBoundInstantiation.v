(** * Fe25519InvertBoundInstantiation — bound-aware discharge of the
 *  fe25519_invert Section hypotheses.
 *
 *  Phase 0e — step 1 (2026-05-19)
 *  ==============================
 *  This is the bound-aware analogue of
 *  [Fe25519InvertFiatInstantiation.v] (Phase 0d).  Where that file
 *  closed the [Fe25519InvertCorrect.v] Section with the DEGENERATE
 *  decoder
 *      Fp25519_holds_concrete rs v x := x = F.zero /\ (5-limb payload)
 *  this file lifts the decoder to the canonical positional-eval
 *  shape used throughout fiat-crypto:
 *      Fp25519_holds_bound rs v x :=
 *        exists limbs, get_tower rs v = Some (VFp25519 limbs)
 *                   /\ length limbs = 5
 *                   /\ Forall (fun l => 0 <= l < 2^54) limbs
 *                   /\ F.of_Z _ (Positional.eval (ModOps.weight 51 1) 5 limbs) = x
 *
 *  Scope of this file (Phase 0e step 1)
 *  ====================================
 *  All 5 invert-Section hypotheses are discharged with [Qed] against
 *  the bound decoder.  The trick is the same as in the concrete
 *  instantiation: the [REdCall] semantics are parameterized by an
 *  abstract oracle [callee_post : ... -> Prop] which we instantiate
 *  to ASSERT exactly the bound-decoder algebraic postcondition of
 *  each callee.  [rexec_call_inv] then yields the per-leaf
 *  algebraic-correctness lemma for free.
 *
 *  The remaining work (Phase 0e step 2) is to DISCHARGE the
 *  [callee_post_bound] oracle against ACTUAL fiat-crypto-synthesized
 *  bedrock2/RustCmd leaves for [fe25519_sqr], [fe25519_mul],
 *  [fe25519_copy] (i.e. produce a function-table whose REdCallFn
 *  invocations PROVE the algebraic postcondition under the
 *  Positional.eval interpretation).  That is upstream from this file
 *  and from [Fe25519InvertCorrect.v]; it does not touch the headline
 *  theorem statement here.
 *
 *  Comparison with the concrete instantiation
 *  ==========================================
 *  - Same 5 Qed discharges; same single-line headline theorem.
 *  - Decoder NO LONGER collapses everything to F.zero — preserved
 *    field values now reflect real positional evaluation modulo
 *    [p = 2^255 - 19].
 *  - Bound (each limb < 2^54) matches fiat-crypto's loose_bounds
 *    shape for curve25519's 5-limb radix-2^51 unsaturated solinas
 *    representation.  Compatible with [carry_mul_correct] /
 *    [carry_square_correct] / [copy_correct] when those are
 *    eventually wired in (Phase 0e step 2).
 *
 *  Closed under the global context.  No new axioms.
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.ModOps.
Require Import Crypto.Spec.Curve25519.
Require Import Bedrock.SafeRustEd25519Tower.
Require Import Bedrock.SafeRustEd25519Sim.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertBody.
Require Import Bedrock.End2End.Ed25519.Fe25519InvertCorrect.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ================================================================ *)
(* §0. Bound decoder                                                 *)
(* ================================================================ *)

(** Per-limb radix-2^51 loose bound: every limb fits in [0, 2^54).
    Standard loose-bounds shape for curve25519's 5x64-bit unsaturated
    solinas representation. *)
Definition limb_loose_bound (l : Z) : Prop := 0 <= l < 2 ^ 54.

Definition limbs_bounded (limbs : list Z) : Prop :=
  Forall limb_loose_bound limbs.

(** Canonical positional eval over the 5-limb radix-2^51 limb list:
    [Positional.eval (ModOps.weight 51 1) 5 limbs], mapped into [F p].
    Matches fiat-crypto's [Bedrock.Field.Interface.Representation.eval_words]
    composition. *)
Definition feval_bound (limbs : list Z) : F p :=
  F.of_Z _ (Positional.eval (ModOps.weight 51 1) 5%nat limbs).

(** Bound-aware slot predicate. *)
Definition Fp25519_holds_bound
    (rs : rust_state_ed) (v : String.string) (x : F p) : Prop :=
  exists limbs : list Z,
    rs_get_tower_ed rs v = Some (exist_tval_ed TFp25519 (VFp25519 limbs))
    /\ length limbs = 5%nat
    /\ limbs_bounded limbs
    /\ feval_bound limbs = x.

(* ================================================================ *)
(* §1. Tower-env bookkeeping (commute through distinct keys)         *)
(* ================================================================ *)

(** [rs_get_tower_ed] commutes with [rs_set_tower_ed] at distinct keys.
    Replayed locally so this file is self-contained (independent of the
    A52 concrete instantiation file). *)
Lemma rs_get_set_tower_other_bound :
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

(* ================================================================ *)
(* §2. Frame hypotheses under the bound decoder                      *)
(* ================================================================ *)

(** [scalar_set_preserves_holds] discharge under the bound decoder.
    [rs_set_scalar_ed] only touches the scalar env; [Fp25519_holds_bound]
    reads the tower env via [rs_get_tower_ed]. *)
Lemma scalar_set_preserves_holds_bound :
  forall (rs : rust_state_ed) (s : String.string) (z : Z) (y : String.string)
         (v : F p),
    Fp25519_holds_bound rs y v ->
    Fp25519_holds_bound (rs_set_scalar_ed rs s z) y v.
Proof.
  intros rs s z y v [limbs [Hget [Hlen [Hbnd Hev]]]].
  exists limbs. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
  unfold rs_get_tower_ed, rs_set_scalar_ed in *. cbn. exact Hget.
Qed.

(** [let_zero_preserves_holds] discharge under the bound decoder.
    Tower-env update at a distinct key preserves all four conjuncts. *)
Lemma let_zero_preserves_holds_bound :
  forall (rs : rust_state_ed) (x : String.string) (t : tower_type_ed)
         (v : rust_val_ed t) (y : String.string) (vp : F p),
    y <> x ->
    Fp25519_holds_bound rs y vp ->
    Fp25519_holds_bound (rs_set_tower_ed rs x (exist_tval_ed t v)) y vp.
Proof.
  intros rs x t v y vp Hne [limbs [Hget [Hlen [Hbnd Hev]]]].
  exists limbs. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
  rewrite rs_get_set_tower_other_bound.
  - exact Hget.
  - intro Hxy. apply Hne. symmetry; exact Hxy.
Qed.

(* ================================================================ *)
(* §3. [callee_post_bound]: oracle relation for [REdCall] semantics  *)
(* ================================================================ *)

(** Mirrors [callee_post_concrete] from [Fe25519InvertFiatInstantiation.v]
    but specialised to the bound decoder.  For each of the three callee
    names invoked by [fe25519_invert_body], it asserts EXACTLY the
    algebraic postcondition the [Fe25519InvertCorrect.v] Section
    hypothesis demands of that leaf.

    DISCHARGE STATUS: this oracle is currently CONSUMED but not
    PRODUCED.  The lemmas [sqr_correct_bound] / [mul_correct_bound] /
    [copy_correct_bound] consume an [Hexec] parameterized by this
    oracle to derive the section hypothesis.  Producing executions
    that satisfy this oracle (i.e. wiring fiat-crypto's
    [carry_mul_correct] / [carry_square_correct] / [copy_correct] to
    actual RustCmd leaves) is the remaining Phase 0e step 2 task. *)
Definition callee_post_bound
  (fname : String.string)
  (args : list located_ed)
  (dst : located_ed)
  (rs1 rs2 : rust_state_ed) : Prop :=
  match fname, args with
  | "fe25519_sqr", [src] =>
      loc_type dst = TFp25519 ->
      loc_type src = TFp25519 ->
      loc_var dst <> loc_var src ->
      forall (x : F p),
        Fp25519_holds_bound rs1 (loc_var src) x ->
        Fp25519_holds_bound rs2 (loc_var dst) (F.pow x 2) /\
        (forall (y : String.string) (v : F p),
            y <> loc_var dst ->
            Fp25519_holds_bound rs1 y v ->
            Fp25519_holds_bound rs2 y v)
  | "fe25519_mul", [a; b] =>
      loc_type dst = TFp25519 ->
      loc_type a = TFp25519 ->
      loc_type b = TFp25519 ->
      loc_var dst <> loc_var a ->
      loc_var dst <> loc_var b ->
      forall (xa xb : F p),
        Fp25519_holds_bound rs1 (loc_var a) xa ->
        Fp25519_holds_bound rs1 (loc_var b) xb ->
        Fp25519_holds_bound rs2 (loc_var dst) (F.mul xa xb) /\
        (forall (y : String.string) (v : F p),
            y <> loc_var dst ->
            Fp25519_holds_bound rs1 y v ->
            Fp25519_holds_bound rs2 y v)
  | "fe25519_copy", [src] =>
      loc_type dst = TFp25519 ->
      loc_type src = TFp25519 ->
      loc_var dst <> loc_var src ->
      forall (x : F p),
        Fp25519_holds_bound rs1 (loc_var src) x ->
        Fp25519_holds_bound rs2 (loc_var dst) x /\
        (forall (y : String.string) (v : F p),
            y <> loc_var dst ->
            Fp25519_holds_bound rs1 y v ->
            Fp25519_holds_bound rs2 y v)
  | _, _ => True
  end.

(** Trivial multi-output oracle.  [fe25519_invert_body] does not
    invoke any [REdCallN], so we leave it permissive. *)
Definition callee_post_n_bound
  (_ : String.string)
  (_ _ : list located_ed)
  (_ _ : rust_state_ed) : Prop := True.

(** Empty function table.  [fe25519_invert_body] contains no
    [REdCallFn] (verified-helper) invocations. *)
Definition function_table_bound : function_table_ed := nil.

(* ================================================================ *)
(* §4. Discharge of the three algebraic Section hypotheses           *)
(* ================================================================ *)

Local Notation Hexec_b :=
  (rust_exec_ed callee_post_bound callee_post_n_bound function_table_bound).

(** Helper: invert [Hexec_b (REdCall fname dst args) rs1 rs2] to
    [callee_post_bound fname args dst rs1 rs2]. *)
Lemma rexec_call_inv_bound :
  forall fname dst args rs1 rs2,
    Hexec_b (REdCall fname dst args) rs1 rs2 ->
    callee_post_bound fname args dst rs1 rs2.
Proof.
  intros fname dst args rs1 rs2 H. inversion H; subst. assumption.
Qed.

(** [sqr_correct] discharge under the bound decoder. *)
Lemma sqr_correct_bound :
  forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F p),
    dest.(loc_type) = TFp25519 ->
    src.(loc_type) = TFp25519 ->
    dest.(loc_var) <> src.(loc_var) ->
    Fp25519_holds_bound rs1 src.(loc_var) x ->
    Hexec_b (REdCall "fe25519_sqr" dest [src]) rs1 rs2 ->
    Fp25519_holds_bound rs2 dest.(loc_var) (F.pow x 2) /\
    fp_frame Fp25519_holds_bound rs1 rs2 dest.(loc_var).
Proof.
  intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
  apply rexec_call_inv_bound in Hexec_n.
  cbn in Hexec_n.
  specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
  split; [exact Hdest|]. unfold fp_frame. exact Hframe.
Qed.

(** [mul_correct] discharge under the bound decoder. *)
Lemma mul_correct_bound :
  forall (dest a b : located_ed) (rs1 rs2 : rust_state_ed) (xa xb : F p),
    dest.(loc_type) = TFp25519 ->
    a.(loc_type) = TFp25519 ->
    b.(loc_type) = TFp25519 ->
    dest.(loc_var) <> a.(loc_var) ->
    dest.(loc_var) <> b.(loc_var) ->
    Fp25519_holds_bound rs1 a.(loc_var) xa ->
    Fp25519_holds_bound rs1 b.(loc_var) xb ->
    Hexec_b (REdCall "fe25519_mul" dest [a; b]) rs1 rs2 ->
    Fp25519_holds_bound rs2 dest.(loc_var) (F.mul xa xb) /\
    fp_frame Fp25519_holds_bound rs1 rs2 dest.(loc_var).
Proof.
  intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb Hexec_n.
  apply rexec_call_inv_bound in Hexec_n.
  cbn in Hexec_n.
  specialize (Hexec_n Hdt Hat Hbt Hne_a Hne_b xa xb Hxa Hxb) as [Hdest Hframe].
  split; [exact Hdest|]. unfold fp_frame. exact Hframe.
Qed.

(** [copy_correct] discharge under the bound decoder. *)
Lemma copy_correct_bound :
  forall (dest src : located_ed) (rs1 rs2 : rust_state_ed) (x : F p),
    dest.(loc_type) = TFp25519 ->
    src.(loc_type) = TFp25519 ->
    dest.(loc_var) <> src.(loc_var) ->
    Fp25519_holds_bound rs1 src.(loc_var) x ->
    Hexec_b (REdCall "fe25519_copy" dest [src]) rs1 rs2 ->
    Fp25519_holds_bound rs2 dest.(loc_var) x /\
    fp_frame Fp25519_holds_bound rs1 rs2 dest.(loc_var).
Proof.
  intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
  apply rexec_call_inv_bound in Hexec_n.
  cbn in Hexec_n.
  specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
  split; [exact Hdest|]. unfold fp_frame. exact Hframe.
Qed.

(* ================================================================ *)
(* §5. Headline theorem — bound-aware                                *)
(* ================================================================ *)

(** Apply [Fe25519InvertCorrect.fe25519_invert_correct] with the
    Section parameters instantiated to the bound decoder and the
    bound-aware oracle.  No Section variables, no leaf hypotheses,
    no Admitteds. *)
Theorem fe25519_invert_body_correct_bound :
  forall (rs1 rs2 : rust_state_ed) (a_loc dest : located_ed) (x : F p),
    a_loc.(loc_type) = TFp25519 ->
    dest.(loc_type) = TFp25519 ->
    dest.(loc_var) <> a_loc.(loc_var) ->
    not_in_scratch a_loc.(loc_var) ->
    not_in_scratch dest.(loc_var) ->
    Fp25519_holds_bound rs1 a_loc.(loc_var) x ->
    Hexec_b (fe25519_invert_body dest [a_loc]) rs1 rs2 ->
    Fp25519_holds_bound rs2 dest.(loc_var) (F.pow x (Z.to_N (p - 2))).
Proof.
  intros rs1 rs2 a_loc dest x Halt Hdt Hdne Halfresh Hdfresh Hax Hexec_n.
  apply (fe25519_invert_correct
           Fp25519_holds_bound
           callee_post_bound
           callee_post_n_bound
           function_table_bound
           sqr_correct_bound
           mul_correct_bound
           copy_correct_bound
           scalar_set_preserves_holds_bound
           let_zero_preserves_holds_bound
           rs1 rs2 a_loc dest x
           Halt Hdt Hdne Halfresh Hdfresh Hax Hexec_n).
Qed.

(* ================================================================ *)
(* §6. Print Assumptions — verify no new global axioms.              *)
(* ================================================================ *)

Print Assumptions scalar_set_preserves_holds_bound.
Print Assumptions let_zero_preserves_holds_bound.
Print Assumptions sqr_correct_bound.
Print Assumptions mul_correct_bound.
Print Assumptions copy_correct_bound.
Print Assumptions fe25519_invert_body_correct_bound.
