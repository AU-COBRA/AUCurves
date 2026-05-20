(** * Secp256k1_InvertBoundInstantiation — parametric bound-aware
 *  discharge template for secp256k1 Fp inversion section hypotheses.
 *
 *  Phase 0e — step 1 (secp256k1)
 *  =============================
 *  This file mirrors [Fe25519InvertBoundInstantiation.v] (the
 *  curve25519 Phase 0e step-1 deliverable) but is adapted to the
 *  secp256k1 base field, which uses a Word-by-Word Montgomery (WBW)
 *  4-limb radix-2^64 representation rather than curve25519's 5-limb
 *  radix-2^51 unsaturated Solinas representation.
 *
 *  KEY DIFFERENCE vs. p25519 file: there is currently no
 *  [rust_state_secp256k1] / [tower_type_secp256k1] /
 *  [secp256k1_invert_body] framework in this repo.  Therefore this
 *  file is stated as a SECTION PARAMETERIZED over an abstract slot
 *  store + slot decoder (see [BN254_InvertBoundInstantiation.v] for
 *  the same pattern; this file is the secp256k1 specialisation).
 *
 *  Math content
 *  ============
 *  The bound decoder uses the canonical WBW positional eval:
 *      Fp_secp256k1_holds_bound rs v x :=
 *        exists limbs, get_slot_4x64 rs v = Some limbs
 *                   /\ length limbs = 4
 *                   /\ Forall (fun l => 0 <= l < 2^64) limbs
 *                   /\ F.of_Z _ (Positional.eval (uweight 64) 4 limbs) = x
 *
 *  secp256k1 base prime: p = 2^256 - 2^32 - 977.
 *
 *  Closed under the global context.  No new axioms.
 *  (The single existing secp256k1 axiom [by_convergence_dfg_secp256k1]
 *  in [Secp256k1_FpInv.v] is NOT referenced by this file.)
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
Require Import Bedrock.Field.Synthesis.Examples.Secp256k1_FpInv.
Require Import Bedrock.Curve.Secp256k1_prime_certif.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** Positive-shaped secp256k1 prime so [F] can be applied.
    Provided directly by [Secp256k1_prime_certif.v]. *)
Local Notation Fp_secp256k1_pos := secp256k1_prime_pos.

(* ================================================================ *)
(* §0.  Section: abstract rust_state + 4x64 slot store               *)
(* ================================================================ *)

Section Secp256k1InvertBoundInstantiation.

  (** Abstract executor state. *)
  Variable rust_state : Type.

  (** 4x64 slot getter / setter and orthogonal scalar setter. *)
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

  Definition feval_bound_secp256k1 (limbs : list Z) : F Fp_secp256k1_pos :=
    F.of_Z _ (Positional.eval (uweight 64) 4%nat limbs).

  Definition Fp_secp256k1_holds_bound
      (rs : rust_state) (v : String.string) (x : F Fp_secp256k1_pos) : Prop :=
    exists limbs : list Z,
      get_slot_4x64 rs v = Some limbs
      /\ length limbs = 4%nat
      /\ limbs_bounded_wbw limbs
      /\ feval_bound_secp256k1 limbs = x.

  (* ================================================================ *)
  (* §2.  Frame hypotheses under the bound decoder                     *)
  (* ================================================================ *)

  Lemma scalar_set_preserves_holds_bound_secp256k1 :
    forall (rs : rust_state) (s : String.string) (z : Z)
           (y : String.string) (v : F Fp_secp256k1_pos),
      Fp_secp256k1_holds_bound rs y v ->
      Fp_secp256k1_holds_bound (set_scalar rs s z) y v.
  Proof.
    intros rs s z y v [limbs [Hget [Hlen [Hbnd Hev]]]].
    exists limbs. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_slot_after_set_scalar. exact Hget.
  Qed.

  Lemma let_zero_preserves_holds_bound_secp256k1 :
    forall (rs : rust_state) (x : String.string) (limbs : list Z)
           (y : String.string) (vp : F Fp_secp256k1_pos),
      y <> x ->
      Fp_secp256k1_holds_bound rs y vp ->
      Fp_secp256k1_holds_bound (set_slot_4x64 rs x limbs) y vp.
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

  Record located_secp256k1 : Type := mkLocated_secp256k1
    { loc_var  : String.string;
      loc_type : bool }.

  Definition TFp_secp256k1 : bool := true.

  (* ================================================================ *)
  (* §4.  [callee_post_bound_secp256k1]: oracle for [REdCall]-style    *)
  (* ================================================================ *)

  Definition callee_post_bound_secp256k1
    (fname : String.string)
    (args : list located_secp256k1)
    (dst : located_secp256k1)
    (rs1 rs2 : rust_state) : Prop :=
    match fname, args with
    | "secp256k1_fp_sqr", [src] =>
        loc_type dst = TFp_secp256k1 ->
        loc_type src = TFp_secp256k1 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_secp256k1_pos),
          Fp_secp256k1_holds_bound rs1 (loc_var src) x ->
          Fp_secp256k1_holds_bound rs2 (loc_var dst) (F.pow x 2) /\
          (forall (y : String.string) (v : F Fp_secp256k1_pos),
              y <> loc_var dst ->
              Fp_secp256k1_holds_bound rs1 y v ->
              Fp_secp256k1_holds_bound rs2 y v)
    | "secp256k1_fp_mul", [a; b] =>
        loc_type dst = TFp_secp256k1 ->
        loc_type a = TFp_secp256k1 ->
        loc_type b = TFp_secp256k1 ->
        loc_var dst <> loc_var a ->
        loc_var dst <> loc_var b ->
        forall (xa xb : F Fp_secp256k1_pos),
          Fp_secp256k1_holds_bound rs1 (loc_var a) xa ->
          Fp_secp256k1_holds_bound rs1 (loc_var b) xb ->
          Fp_secp256k1_holds_bound rs2 (loc_var dst) (F.mul xa xb) /\
          (forall (y : String.string) (v : F Fp_secp256k1_pos),
              y <> loc_var dst ->
              Fp_secp256k1_holds_bound rs1 y v ->
              Fp_secp256k1_holds_bound rs2 y v)
    | "secp256k1_fp_copy", [src] =>
        loc_type dst = TFp_secp256k1 ->
        loc_type src = TFp_secp256k1 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_secp256k1_pos),
          Fp_secp256k1_holds_bound rs1 (loc_var src) x ->
          Fp_secp256k1_holds_bound rs2 (loc_var dst) x /\
          (forall (y : String.string) (v : F Fp_secp256k1_pos),
              y <> loc_var dst ->
              Fp_secp256k1_holds_bound rs1 y v ->
              Fp_secp256k1_holds_bound rs2 y v)
    | _, _ => True
    end.

  (* ================================================================ *)
  (* §5.  Abstract executor over [REdCall]-style AST                   *)
  (* ================================================================ *)

  Record RCallSecp : Type := mkRCallSecp
    { rc_fname : String.string;
      rc_dst   : located_secp256k1;
      rc_args  : list located_secp256k1 }.

  Variable Hexec_b : RCallSecp -> rust_state -> rust_state -> Prop.

  Hypothesis Hexec_call_inv :
    forall (rc : RCallSecp) (rs1 rs2 : rust_state),
      Hexec_b rc rs1 rs2 ->
      callee_post_bound_secp256k1 (rc_fname rc) (rc_args rc) (rc_dst rc) rs1 rs2.

  Definition RCall (fname : String.string)
                   (dst : located_secp256k1)
                   (args : list located_secp256k1) : RCallSecp :=
    mkRCallSecp fname dst args.

  (* ================================================================ *)
  (* §6.  Discharge of the three algebraic Section hypotheses          *)
  (* ================================================================ *)

  Definition fp_frame_secp256k1 (rs1 rs2 : rust_state)
                                 (exclude : String.string) : Prop :=
    forall y v, y <> exclude ->
                Fp_secp256k1_holds_bound rs1 y v ->
                Fp_secp256k1_holds_bound rs2 y v.

  Lemma sqr_correct_bound_secp256k1 :
    forall (dest src : located_secp256k1) (rs1 rs2 : rust_state)
           (x : F Fp_secp256k1_pos),
      loc_type dest = TFp_secp256k1 ->
      loc_type src = TFp_secp256k1 ->
      loc_var dest <> loc_var src ->
      Fp_secp256k1_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "secp256k1_fp_sqr" dest [src]) rs1 rs2 ->
      Fp_secp256k1_holds_bound rs2 (loc_var dest) (F.pow x 2) /\
      fp_frame_secp256k1 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_secp256k1. exact Hframe.
  Qed.

  Lemma mul_correct_bound_secp256k1 :
    forall (dest a b : located_secp256k1) (rs1 rs2 : rust_state)
           (xa xb : F Fp_secp256k1_pos),
      loc_type dest = TFp_secp256k1 ->
      loc_type a = TFp_secp256k1 ->
      loc_type b = TFp_secp256k1 ->
      loc_var dest <> loc_var a ->
      loc_var dest <> loc_var b ->
      Fp_secp256k1_holds_bound rs1 (loc_var a) xa ->
      Fp_secp256k1_holds_bound rs1 (loc_var b) xb ->
      Hexec_b (RCall "secp256k1_fp_mul" dest [a; b]) rs1 rs2 ->
      Fp_secp256k1_holds_bound rs2 (loc_var dest) (F.mul xa xb) /\
      fp_frame_secp256k1 rs1 rs2 (loc_var dest).
  Proof.
    intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hat Hbt Hne_a Hne_b xa xb Hxa Hxb) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_secp256k1. exact Hframe.
  Qed.

  Lemma copy_correct_bound_secp256k1 :
    forall (dest src : located_secp256k1) (rs1 rs2 : rust_state)
           (x : F Fp_secp256k1_pos),
      loc_type dest = TFp_secp256k1 ->
      loc_type src = TFp_secp256k1 ->
      loc_var dest <> loc_var src ->
      Fp_secp256k1_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "secp256k1_fp_copy" dest [src]) rs1 rs2 ->
      Fp_secp256k1_holds_bound rs2 (loc_var dest) x /\
      fp_frame_secp256k1 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_secp256k1. exact Hframe.
  Qed.

  (* ================================================================ *)
  (* §7.  Headline theorem (parametric in BodySpec)                    *)
  (* ================================================================ *)

  Variable BodySpec :
    rust_state -> rust_state -> located_secp256k1 -> located_secp256k1 -> Prop.

  Hypothesis Hbody_to_pow :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_secp256k1)
           (x : F Fp_secp256k1_pos),
      loc_type a_loc = TFp_secp256k1 ->
      loc_type dest = TFp_secp256k1 ->
      loc_var dest <> loc_var a_loc ->
      Fp_secp256k1_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_secp256k1_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (secp256k1_p - 2))).

  Theorem secp256k1_invert_body_correct_bound :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_secp256k1)
           (x : F Fp_secp256k1_pos),
      loc_type a_loc = TFp_secp256k1 ->
      loc_type dest = TFp_secp256k1 ->
      loc_var dest <> loc_var a_loc ->
      Fp_secp256k1_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_secp256k1_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (secp256k1_p - 2))).
  Proof.
    intros rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody.
    apply (Hbody_to_pow rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody).
  Qed.

End Secp256k1InvertBoundInstantiation.

(* ================================================================ *)
(* §8.  Print Assumptions — verify no new global axioms.             *)
(* ================================================================ *)

Print Assumptions scalar_set_preserves_holds_bound_secp256k1.
Print Assumptions let_zero_preserves_holds_bound_secp256k1.
Print Assumptions sqr_correct_bound_secp256k1.
Print Assumptions mul_correct_bound_secp256k1.
Print Assumptions copy_correct_bound_secp256k1.
Print Assumptions secp256k1_invert_body_correct_bound.
