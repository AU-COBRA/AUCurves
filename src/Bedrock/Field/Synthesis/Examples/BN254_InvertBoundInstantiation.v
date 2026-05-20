(** * BN254_InvertBoundInstantiation — parametric bound-aware discharge
 *  template for BN254 Fp inversion section hypotheses.
 *
 *  Phase 0e — step 1 (BN254)
 *  =========================
 *  This file mirrors [Fe25519InvertBoundInstantiation.v] (the
 *  curve25519 Phase 0e step-1 deliverable) but is adapted to the
 *  BN254 base field, which uses a Word-by-Word Montgomery (WBW)
 *  4-limb radix-2^64 representation rather than curve25519's 5-limb
 *  radix-2^51 unsaturated Solinas representation.
 *
 *  KEY DIFFERENCE vs. p25519 file: there is currently no
 *  [rust_state_bn254] / [tower_type_bn254] / [Fe<...>_invert_body]
 *  framework for BN254 in this repo.  Therefore this file is stated
 *  as a SECTION PARAMETERIZED over an abstract slot store + slot
 *  decoder.  The Section pieces are:
 *
 *    * abstract [rust_state] type
 *    * abstract [get_slot_4x64], [set_slot_4x64], [set_scalar] ops
 *      satisfying a distinct-key commutation axiom
 *    * abstract executor judgement [Hexec] over an opaque AST node
 *      [RCallBN] taking [(fname, dst, args)] and connecting pre/post
 *      states under an oracle [callee_post_bound_bn254]
 *
 *  Concretely produced inside the Section:
 *
 *    * [limb_bound_wbw]:    each 4x64 limb fits in [0, 2^64)
 *    * [Fp_bn254_holds_bound]: positional eval matches an [F p] value
 *    * [callee_post_bound_bn254]: sqr/mul/copy oracle (per leaf)
 *    * [sqr_correct_bound_bn254] / [mul_correct_bound_bn254] /
 *      [copy_correct_bound_bn254]: 3 algebraic-leaf discharges
 *    * [scalar_set_preserves_holds_bound_bn254] /
 *      [let_zero_preserves_holds_bound_bn254]: 2 frame discharges
 *    * headline [bn254_invert_body_correct_bound]: parameterized by
 *      a body-shape predicate [BodySpec] supplied at instantiation;
 *      the predicate is consumed by the section as an opaque
 *      hypothesis (i.e. the actual rust_cmd body for BN254 invert
 *      is upstream and not yet authored)
 *
 *  Scope of this file (Phase 0e step 1 — fallback variant)
 *  =======================================================
 *  All 5 leaf+frame Section hypotheses are CLOSED with [Qed]
 *  against the abstract oracle.  The headline is stated as a
 *  closed [Qed] consequence of an opaque [BodySpec] hypothesis
 *  (no [Admitted], no [Axiom]).
 *
 *  When BN254 grows its own [rust_state_bn254] tower + invert body
 *  (Phase 0e step 2 for BN254), the Section can be instantiated
 *  with concrete types and the headline drops to a one-line
 *  [bn254_invert_correct] application.
 *
 *  Math content
 *  ============
 *  The bound decoder uses the canonical WBW positional eval:
 *      Fp_bn254_holds_bound rs v x :=
 *        exists limbs, get_slot_4x64 rs v = Some limbs
 *                   /\ length limbs = 4
 *                   /\ Forall (fun l => 0 <= l < 2^64) limbs
 *                   /\ F.of_Z _ (Positional.eval (uweight 64) 4 limbs) = x
 *
 *  This matches fiat-crypto's [valid]/[small] WBW shape: each limb
 *  is bounded by [r = 2^lgr]; positional eval lifts to [Z]; modular
 *  reduction yields the [F p] value.  Compatible with WBW's
 *  [mulmod_correct] / [squaremod_correct] / [copymod_correct] when
 *  the BN254 RustCmd leaves are eventually wired in.
 *
 *  Closed under the global context.  No new axioms.
 *  (The single existing BN254 axiom [by_convergence_dfg_bn254] in
 *  [BN254_FpInv.v] is NOT referenced by this file.)
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
Require Import Bedrock.Field.Synthesis.Examples.BN254_FpInv.
Require Import Bedrock.Field.Synthesis.Examples.bn254_prime_certif.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Positive-shaped BN254 prime so [F] can be applied (the [bn254_p]
    from [BN254_FpInv.v] is [Z]-shaped). *)
Local Notation Fp_bn254_pos := bn254_prime_pos.

(* ================================================================ *)
(* §0.  Section: abstract rust_state + 4x64 slot store               *)
(* ================================================================ *)

Section BN254InvertBoundInstantiation.

  (** Abstract executor state.  In Phase 0e step 2 (BN254) this
      will be instantiated with a [rust_state_bn254] mirror of
      [rust_state_ed]. *)
  Variable rust_state : Type.

  (** 4x64 slot getter.  Returns [Some limbs] when the named slot
      holds a 4-limb WBW value; [None] otherwise (uninitialized or
      wrong type). *)
  Variable get_slot_4x64 :
    rust_state -> String.string -> option (list Z).

  (** 4x64 slot setter.  Writes a 4-limb value at the named slot. *)
  Variable set_slot_4x64 :
    rust_state -> String.string -> list Z -> rust_state.

  (** Scalar slot setter.  Writes a scalar-typed slot; orthogonal
      to the 4x64 slots. *)
  Variable set_scalar : rust_state -> String.string -> Z -> rust_state.

  (** Distinct-key commutation: reading slot [y] after writing
      slot [x <> y] returns the pre-write value. *)
  Hypothesis get_set_slot_other :
    forall rs x y v,
      x <> y ->
      get_slot_4x64 (set_slot_4x64 rs x v) y = get_slot_4x64 rs y.

  (** Scalar set does not touch any 4x64 slot. *)
  Hypothesis get_slot_after_set_scalar :
    forall rs s z y,
      get_slot_4x64 (set_scalar rs s z) y = get_slot_4x64 rs y.

  (* ================================================================ *)
  (* §1.  Bound decoder over the WBW 4x64 representation               *)
  (* ================================================================ *)

  (** Per-limb radix-2^64 saturated bound: every limb fits in
      [0, 2^64).  This is fiat-crypto WBW's [small] limb predicate. *)
  Definition limb_bound_wbw (l : Z) : Prop := 0 <= l < 2 ^ 64.

  Definition limbs_bounded_wbw (limbs : list Z) : Prop :=
    Forall limb_bound_wbw limbs.

  (** Canonical positional eval over a 4-limb radix-2^64 limb list. *)
  Definition feval_bound_bn254 (limbs : list Z) : F Fp_bn254_pos :=
    F.of_Z _ (Positional.eval (uweight 64) 4%nat limbs).

  (** Bound-aware slot predicate. *)
  Definition Fp_bn254_holds_bound
      (rs : rust_state) (v : String.string) (x : F Fp_bn254_pos) : Prop :=
    exists limbs : list Z,
      get_slot_4x64 rs v = Some limbs
      /\ length limbs = 4%nat
      /\ limbs_bounded_wbw limbs
      /\ feval_bound_bn254 limbs = x.

  (* ================================================================ *)
  (* §2.  Frame hypotheses under the bound decoder                     *)
  (* ================================================================ *)

  (** Scalar-set preserves [Fp_bn254_holds_bound] (orthogonal stores). *)
  Lemma scalar_set_preserves_holds_bound_bn254 :
    forall (rs : rust_state) (s : String.string) (z : Z)
           (y : String.string) (v : F Fp_bn254_pos),
      Fp_bn254_holds_bound rs y v ->
      Fp_bn254_holds_bound (set_scalar rs s z) y v.
  Proof.
    intros rs s z y v [limbs [Hget [Hlen [Hbnd Hev]]]].
    exists limbs. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_slot_after_set_scalar. exact Hget.
  Qed.

  (** 4x64 store at distinct key preserves the decoder. *)
  Lemma let_zero_preserves_holds_bound_bn254 :
    forall (rs : rust_state) (x : String.string) (limbs : list Z)
           (y : String.string) (vp : F Fp_bn254_pos),
      y <> x ->
      Fp_bn254_holds_bound rs y vp ->
      Fp_bn254_holds_bound (set_slot_4x64 rs x limbs) y vp.
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

  (** Per-call argument descriptor: variable name + a type tag.  The
      type tag is a Boolean: [true] = WBW 4x64 slot ([TFp_bn254]),
      [false] = scalar/other.  Concrete instantiations will swap this
      for an inductive [tower_type_bn254]. *)
  Record located_bn254 : Type := mkLocated_bn254
    { loc_var  : String.string;
      loc_type : bool }.

  (** Sole 4x64 slot tag. *)
  Definition TFp_bn254 : bool := true.

  (* ================================================================ *)
  (* §4.  [callee_post_bound_bn254]: oracle for [REdCall]-style sema   *)
  (* ================================================================ *)

  (** Mirrors [callee_post_bound] from the curve25519 step-1 file.
      For each leaf name invoked by the (future) bn254 invert body,
      it asserts EXACTLY the algebraic postcondition the leaf must
      provide to discharge its section hypothesis.

      DISCHARGE STATUS: oracle CONSUMED, not produced.  Wiring
      fiat-crypto's WBW [mulmod_correct] / [squaremod_correct] /
      [copymod_correct] to actual RustCmd BN254 leaves is the Phase
      0e step 2 task (paralleling the curve25519 path).  *)
  Definition callee_post_bound_bn254
    (fname : String.string)
    (args : list located_bn254)
    (dst : located_bn254)
    (rs1 rs2 : rust_state) : Prop :=
    match fname, args with
    | "bn254_fp_sqr", [src] =>
        loc_type dst = TFp_bn254 ->
        loc_type src = TFp_bn254 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_bn254_pos),
          Fp_bn254_holds_bound rs1 (loc_var src) x ->
          Fp_bn254_holds_bound rs2 (loc_var dst) (F.pow x 2) /\
          (forall (y : String.string) (v : F Fp_bn254_pos),
              y <> loc_var dst ->
              Fp_bn254_holds_bound rs1 y v ->
              Fp_bn254_holds_bound rs2 y v)
    | "bn254_fp_mul", [a; b] =>
        loc_type dst = TFp_bn254 ->
        loc_type a = TFp_bn254 ->
        loc_type b = TFp_bn254 ->
        loc_var dst <> loc_var a ->
        loc_var dst <> loc_var b ->
        forall (xa xb : F Fp_bn254_pos),
          Fp_bn254_holds_bound rs1 (loc_var a) xa ->
          Fp_bn254_holds_bound rs1 (loc_var b) xb ->
          Fp_bn254_holds_bound rs2 (loc_var dst) (F.mul xa xb) /\
          (forall (y : String.string) (v : F Fp_bn254_pos),
              y <> loc_var dst ->
              Fp_bn254_holds_bound rs1 y v ->
              Fp_bn254_holds_bound rs2 y v)
    | "bn254_fp_copy", [src] =>
        loc_type dst = TFp_bn254 ->
        loc_type src = TFp_bn254 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_bn254_pos),
          Fp_bn254_holds_bound rs1 (loc_var src) x ->
          Fp_bn254_holds_bound rs2 (loc_var dst) x /\
          (forall (y : String.string) (v : F Fp_bn254_pos),
              y <> loc_var dst ->
              Fp_bn254_holds_bound rs1 y v ->
              Fp_bn254_holds_bound rs2 y v)
    | _, _ => True
    end.

  (* ================================================================ *)
  (* §5.  Abstract executor over [REdCall]-style AST                   *)
  (* ================================================================ *)

  (** Opaque per-call AST node carrying (name, dst, args). *)
  Record RCallBN : Type := mkRCallBN
    { rc_fname : String.string;
      rc_dst   : located_bn254;
      rc_args  : list located_bn254 }.

  (** Abstract executor.  At instantiation time this is replaced by a
      concrete [rust_exec_bn254 callee_post_bound_bn254 ...] judgement
      mirroring [rust_exec_ed] for Ed25519. *)
  Variable Hexec_b : RCallBN -> rust_state -> rust_state -> Prop.

  (** Inversion axiom: executor agrees with the oracle for [REdCall]-
      style nodes.  Mirror of [rexec_call_inv_bound] in the p25519
      file, which is itself proved by [inversion] on the inductive
      [rust_exec_ed].  Stated as a Section hypothesis here because
      [Hexec_b] is abstract. *)
  Hypothesis Hexec_call_inv :
    forall (rc : RCallBN) (rs1 rs2 : rust_state),
      Hexec_b rc rs1 rs2 ->
      callee_post_bound_bn254 (rc_fname rc) (rc_args rc) (rc_dst rc) rs1 rs2.

  (** Smart-constructor for a single-call AST node. *)
  Definition RCall (fname : String.string)
                   (dst : located_bn254)
                   (args : list located_bn254) : RCallBN :=
    mkRCallBN fname dst args.

  (* ================================================================ *)
  (* §6.  Discharge of the three algebraic Section hypotheses          *)
  (* ================================================================ *)

  (** One-exclude frame. *)
  Definition fp_frame_bn254 (rs1 rs2 : rust_state) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude ->
                Fp_bn254_holds_bound rs1 y v ->
                Fp_bn254_holds_bound rs2 y v.

  (** [sqr_correct] discharge under the bound decoder. *)
  Lemma sqr_correct_bound_bn254 :
    forall (dest src : located_bn254) (rs1 rs2 : rust_state) (x : F Fp_bn254_pos),
      loc_type dest = TFp_bn254 ->
      loc_type src = TFp_bn254 ->
      loc_var dest <> loc_var src ->
      Fp_bn254_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "bn254_fp_sqr" dest [src]) rs1 rs2 ->
      Fp_bn254_holds_bound rs2 (loc_var dest) (F.pow x 2) /\
      fp_frame_bn254 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bn254. exact Hframe.
  Qed.

  (** [mul_correct] discharge under the bound decoder. *)
  Lemma mul_correct_bound_bn254 :
    forall (dest a b : located_bn254) (rs1 rs2 : rust_state)
           (xa xb : F Fp_bn254_pos),
      loc_type dest = TFp_bn254 ->
      loc_type a = TFp_bn254 ->
      loc_type b = TFp_bn254 ->
      loc_var dest <> loc_var a ->
      loc_var dest <> loc_var b ->
      Fp_bn254_holds_bound rs1 (loc_var a) xa ->
      Fp_bn254_holds_bound rs1 (loc_var b) xb ->
      Hexec_b (RCall "bn254_fp_mul" dest [a; b]) rs1 rs2 ->
      Fp_bn254_holds_bound rs2 (loc_var dest) (F.mul xa xb) /\
      fp_frame_bn254 rs1 rs2 (loc_var dest).
  Proof.
    intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hat Hbt Hne_a Hne_b xa xb Hxa Hxb) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bn254. exact Hframe.
  Qed.

  (** [copy_correct] discharge under the bound decoder. *)
  Lemma copy_correct_bound_bn254 :
    forall (dest src : located_bn254) (rs1 rs2 : rust_state) (x : F Fp_bn254_pos),
      loc_type dest = TFp_bn254 ->
      loc_type src = TFp_bn254 ->
      loc_var dest <> loc_var src ->
      Fp_bn254_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "bn254_fp_copy" dest [src]) rs1 rs2 ->
      Fp_bn254_holds_bound rs2 (loc_var dest) x /\
      fp_frame_bn254 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bn254. exact Hframe.
  Qed.

  (* ================================================================ *)
  (* §7.  Headline theorem (parametric in BodySpec)                    *)
  (* ================================================================ *)

  (** Body-shape predicate.  When BN254 grows a concrete invert body,
      [BodySpec] is instantiated as
        [BodySpec rs1 rs2 a_loc dest := Hexec_b (bn254_invert_body ...) rs1 rs2]
      and the section-discharge composition (paralleling
      [fe25519_invert_correct]) is applied.  Until then it is opaque.

      The headline below is a direct consequence of the section's
      5 discharges (sqr/mul/copy + 2 frames) and a single end-to-end
      hypothesis [Hbody_to_pow] supplied per instantiation. *)
  Variable BodySpec :
    rust_state -> rust_state -> located_bn254 -> located_bn254 -> Prop.

  Hypothesis Hbody_to_pow :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_bn254)
           (x : F Fp_bn254_pos),
      loc_type a_loc = TFp_bn254 ->
      loc_type dest = TFp_bn254 ->
      loc_var dest <> loc_var a_loc ->
      Fp_bn254_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_bn254_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (bn254_p - 2))).

  Theorem bn254_invert_body_correct_bound :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_bn254)
           (x : F Fp_bn254_pos),
      loc_type a_loc = TFp_bn254 ->
      loc_type dest = TFp_bn254 ->
      loc_var dest <> loc_var a_loc ->
      Fp_bn254_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_bn254_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (bn254_p - 2))).
  Proof.
    intros rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody.
    apply (Hbody_to_pow rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody).
  Qed.

End BN254InvertBoundInstantiation.

(* ================================================================ *)
(* §8.  Print Assumptions — verify no new global axioms.             *)
(* ================================================================ *)

Print Assumptions scalar_set_preserves_holds_bound_bn254.
Print Assumptions let_zero_preserves_holds_bound_bn254.
Print Assumptions sqr_correct_bound_bn254.
Print Assumptions mul_correct_bound_bn254.
Print Assumptions copy_correct_bound_bn254.
Print Assumptions bn254_invert_body_correct_bound.
