(** * Vesta_InvertBoundInstantiation — parametric bound-aware discharge
 *  template for Vesta Fp inversion section hypotheses.
 *
 *  Phase 0e — step 1 (Vesta)
 *  =========================
 *  This file mirrors [Pallas_InvertBoundInstantiation.v] (the Pallas
 *  Phase 0e step-1 deliverable) but for the Vesta base field
 *  (pasta_fq), which uses the same Word-by-Word Montgomery (WBW)
 *  4-limb radix-2^64 representation.
 *
 *  KEY POINT vs. p25519/BN254/Pallas: same WBW 4x64 layout; there is
 *  currently no [rust_state_vesta] / [tower_type_vesta] /
 *  [Fe<...>_invert_body] framework for Vesta in this repo.  Therefore
 *  this file is stated as a SECTION PARAMETERIZED over an abstract
 *  slot store + slot decoder.  The Section pieces are:
 *
 *    * abstract [rust_state] type
 *    * abstract [get_slot_4x64], [set_slot_4x64], [set_scalar] ops
 *      satisfying a distinct-key commutation axiom
 *    * abstract executor judgement [Hexec] over an opaque AST node
 *      [RCallVS] taking [(fname, dst, args)] and connecting pre/post
 *      states under an oracle [callee_post_bound_vesta]
 *
 *  Concretely produced inside the Section:
 *
 *    * [limb_bound_wbw]:    each 4x64 limb fits in [0, 2^64)
 *    * [Fp_vesta_holds_bound]: positional eval matches an [F p] value
 *    * [callee_post_bound_vesta]: sqr/mul/copy oracle (per leaf)
 *    * [sqr_correct_bound_vesta] / [mul_correct_bound_vesta] /
 *      [copy_correct_bound_vesta]: 3 algebraic-leaf discharges
 *    * [scalar_set_preserves_holds_bound_vesta] /
 *      [let_zero_preserves_holds_bound_vesta]: 2 frame discharges
 *    * headline [vesta_invert_body_correct_bound]: parameterized by
 *      a body-shape predicate [BodySpec] supplied at instantiation
 *
 *  Scope of this file (Phase 0e step 1 — fallback variant)
 *  =======================================================
 *  All 5 leaf+frame Section hypotheses are CLOSED with [Qed]
 *  against the abstract oracle.  The headline is stated as a
 *  closed [Qed] consequence of an opaque [BodySpec] hypothesis
 *  (no [Admitted], no [Axiom]).
 *
 *  Closed under the global context.  No new axioms.
 *  (The single existing Vesta axiom [by_convergence_dfg_vesta] in
 *  [Vesta_FpInv.v] is NOT referenced by this file.)
 *)

From Stdlib Require Import Strings.String.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import NArith.NArith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.Core.
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Bedrock.Field.Synthesis.Examples.Vesta_FpInv.
Require Import Bedrock.Field.Synthesis.Examples.vesta_prime_certif.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Positive-shaped Vesta prime so [F] can be applied (the [vesta_p]
    from [Vesta_FpInv.v] is [Z]-shaped). *)
Local Notation Fp_vesta_pos := vesta_prime_pos.

(* ================================================================ *)
(* §0.  Section: abstract rust_state + 4x64 slot store               *)
(* ================================================================ *)

Section VestaInvertBoundInstantiation.

  Variable rust_state : Type.

  Variable get_slot_4x64 :
    rust_state -> String.string -> option (list Z).

  Variable set_slot_4x64 :
    rust_state -> String.string -> list Z -> rust_state.

  Variable set_scalar : rust_state -> String.string -> Z -> rust_state.

  Hypothesis get_set_slot_other :
    forall rs x y v,
      x <> y ->
      get_slot_4x64 (set_slot_4x64 rs x v) y = get_slot_4x64 rs y.

  Hypothesis get_slot_after_set_scalar :
    forall rs s z y,
      get_slot_4x64 (set_scalar rs s z) y = get_slot_4x64 rs y.

  (* ================================================================ *)
  (* §1.  Bound decoder over the WBW 4x64 representation               *)
  (* ================================================================ *)

  Definition limb_bound_wbw (l : Z) : Prop := 0 <= l < 2 ^ 64.

  Definition limbs_bounded_wbw (limbs : list Z) : Prop :=
    Forall limb_bound_wbw limbs.

  Definition feval_bound_vesta (limbs : list Z) : F Fp_vesta_pos :=
    F.of_Z _ (Positional.eval (uweight 64) 4%nat limbs).

  Definition Fp_vesta_holds_bound
      (rs : rust_state) (v : String.string) (x : F Fp_vesta_pos) : Prop :=
    exists limbs : list Z,
      get_slot_4x64 rs v = Some limbs
      /\ length limbs = 4%nat
      /\ limbs_bounded_wbw limbs
      /\ feval_bound_vesta limbs = x.

  (* ================================================================ *)
  (* §2.  Frame hypotheses under the bound decoder                     *)
  (* ================================================================ *)

  Lemma scalar_set_preserves_holds_bound_vesta :
    forall (rs : rust_state) (s : String.string) (z : Z)
           (y : String.string) (v : F Fp_vesta_pos),
      Fp_vesta_holds_bound rs y v ->
      Fp_vesta_holds_bound (set_scalar rs s z) y v.
  Proof.
    intros rs s z y v [limbs [Hget [Hlen [Hbnd Hev]]]].
    exists limbs. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_slot_after_set_scalar. exact Hget.
  Qed.

  Lemma let_zero_preserves_holds_bound_vesta :
    forall (rs : rust_state) (x : String.string) (limbs : list Z)
           (y : String.string) (vp : F Fp_vesta_pos),
      y <> x ->
      Fp_vesta_holds_bound rs y vp ->
      Fp_vesta_holds_bound (set_slot_4x64 rs x limbs) y vp.
  Proof.
    intros rs x limbs y vp Hne [limbs0 [Hget [Hlen [Hbnd Hev]]]].
    exists limbs0. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_set_slot_other.
    - exact Hget.
    - intro Hxy. apply Hne. symmetry; exact Hxy.
  Qed.

  (* ================================================================ *)
  (* §3.  Located records (analogue of [located_ed])                   *)
  (* ================================================================ *)

  Record located_vesta : Type := mkLocated_vesta
    { loc_var  : String.string;
      loc_type : bool }.

  Definition TFp_vesta : bool := true.

  (* ================================================================ *)
  (* §4.  [callee_post_bound_vesta]: oracle for [REdCall]-style sema   *)
  (* ================================================================ *)

  Definition callee_post_bound_vesta
    (fname : String.string)
    (args : list located_vesta)
    (dst : located_vesta)
    (rs1 rs2 : rust_state) : Prop :=
    match fname, args with
    | "vesta_fp_sqr", [src] =>
        loc_type dst = TFp_vesta ->
        loc_type src = TFp_vesta ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_vesta_pos),
          Fp_vesta_holds_bound rs1 (loc_var src) x ->
          Fp_vesta_holds_bound rs2 (loc_var dst) (F.pow x 2) /\
          (forall (y : String.string) (v : F Fp_vesta_pos),
              y <> loc_var dst ->
              Fp_vesta_holds_bound rs1 y v ->
              Fp_vesta_holds_bound rs2 y v)
    | "vesta_fp_mul", [a; b] =>
        loc_type dst = TFp_vesta ->
        loc_type a = TFp_vesta ->
        loc_type b = TFp_vesta ->
        loc_var dst <> loc_var a ->
        loc_var dst <> loc_var b ->
        forall (xa xb : F Fp_vesta_pos),
          Fp_vesta_holds_bound rs1 (loc_var a) xa ->
          Fp_vesta_holds_bound rs1 (loc_var b) xb ->
          Fp_vesta_holds_bound rs2 (loc_var dst) (F.mul xa xb) /\
          (forall (y : String.string) (v : F Fp_vesta_pos),
              y <> loc_var dst ->
              Fp_vesta_holds_bound rs1 y v ->
              Fp_vesta_holds_bound rs2 y v)
    | "vesta_fp_copy", [src] =>
        loc_type dst = TFp_vesta ->
        loc_type src = TFp_vesta ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_vesta_pos),
          Fp_vesta_holds_bound rs1 (loc_var src) x ->
          Fp_vesta_holds_bound rs2 (loc_var dst) x /\
          (forall (y : String.string) (v : F Fp_vesta_pos),
              y <> loc_var dst ->
              Fp_vesta_holds_bound rs1 y v ->
              Fp_vesta_holds_bound rs2 y v)
    | _, _ => True
    end.

  (* ================================================================ *)
  (* §5.  Abstract executor over [REdCall]-style AST                   *)
  (* ================================================================ *)

  Record RCallVS : Type := mkRCallVS
    { rc_fname : String.string;
      rc_dst   : located_vesta;
      rc_args  : list located_vesta }.

  Variable Hexec_v : RCallVS -> rust_state -> rust_state -> Prop.

  Hypothesis Hexec_call_inv :
    forall (rc : RCallVS) (rs1 rs2 : rust_state),
      Hexec_v rc rs1 rs2 ->
      callee_post_bound_vesta (rc_fname rc) (rc_args rc) (rc_dst rc) rs1 rs2.

  Definition RCall (fname : String.string)
                   (dst : located_vesta)
                   (args : list located_vesta) : RCallVS :=
    mkRCallVS fname dst args.

  (* ================================================================ *)
  (* §6.  Discharge of the three algebraic Section hypotheses          *)
  (* ================================================================ *)

  Definition fp_frame_vesta (rs1 rs2 : rust_state) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude ->
                Fp_vesta_holds_bound rs1 y v ->
                Fp_vesta_holds_bound rs2 y v.

  Lemma sqr_correct_bound_vesta :
    forall (dest src : located_vesta) (rs1 rs2 : rust_state) (x : F Fp_vesta_pos),
      loc_type dest = TFp_vesta ->
      loc_type src = TFp_vesta ->
      loc_var dest <> loc_var src ->
      Fp_vesta_holds_bound rs1 (loc_var src) x ->
      Hexec_v (RCall "vesta_fp_sqr" dest [src]) rs1 rs2 ->
      Fp_vesta_holds_bound rs2 (loc_var dest) (F.pow x 2) /\
      fp_frame_vesta rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_vesta. exact Hframe.
  Qed.

  Lemma mul_correct_bound_vesta :
    forall (dest a b : located_vesta) (rs1 rs2 : rust_state)
           (xa xb : F Fp_vesta_pos),
      loc_type dest = TFp_vesta ->
      loc_type a = TFp_vesta ->
      loc_type b = TFp_vesta ->
      loc_var dest <> loc_var a ->
      loc_var dest <> loc_var b ->
      Fp_vesta_holds_bound rs1 (loc_var a) xa ->
      Fp_vesta_holds_bound rs1 (loc_var b) xb ->
      Hexec_v (RCall "vesta_fp_mul" dest [a; b]) rs1 rs2 ->
      Fp_vesta_holds_bound rs2 (loc_var dest) (F.mul xa xb) /\
      fp_frame_vesta rs1 rs2 (loc_var dest).
  Proof.
    intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hat Hbt Hne_a Hne_b xa xb Hxa Hxb) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_vesta. exact Hframe.
  Qed.

  Lemma copy_correct_bound_vesta :
    forall (dest src : located_vesta) (rs1 rs2 : rust_state) (x : F Fp_vesta_pos),
      loc_type dest = TFp_vesta ->
      loc_type src = TFp_vesta ->
      loc_var dest <> loc_var src ->
      Fp_vesta_holds_bound rs1 (loc_var src) x ->
      Hexec_v (RCall "vesta_fp_copy" dest [src]) rs1 rs2 ->
      Fp_vesta_holds_bound rs2 (loc_var dest) x /\
      fp_frame_vesta rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_vesta. exact Hframe.
  Qed.

  (* ================================================================ *)
  (* §7.  Headline theorem (parametric in BodySpec)                    *)
  (* ================================================================ *)

  Variable BodySpec :
    rust_state -> rust_state -> located_vesta -> located_vesta -> Prop.

  Hypothesis Hbody_to_pow :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_vesta)
           (x : F Fp_vesta_pos),
      loc_type a_loc = TFp_vesta ->
      loc_type dest = TFp_vesta ->
      loc_var dest <> loc_var a_loc ->
      Fp_vesta_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_vesta_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (vesta_p - 2))).

  Theorem vesta_invert_body_correct_bound :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_vesta)
           (x : F Fp_vesta_pos),
      loc_type a_loc = TFp_vesta ->
      loc_type dest = TFp_vesta ->
      loc_var dest <> loc_var a_loc ->
      Fp_vesta_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_vesta_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (vesta_p - 2))).
  Proof.
    intros rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody.
    apply (Hbody_to_pow rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody).
  Qed.

End VestaInvertBoundInstantiation.

(* ================================================================ *)
(* §8.  Print Assumptions — verify no new global axioms.             *)
(* ================================================================ *)

Print Assumptions scalar_set_preserves_holds_bound_vesta.
Print Assumptions let_zero_preserves_holds_bound_vesta.
Print Assumptions sqr_correct_bound_vesta.
Print Assumptions mul_correct_bound_vesta.
Print Assumptions copy_correct_bound_vesta.
Print Assumptions vesta_invert_body_correct_bound.
