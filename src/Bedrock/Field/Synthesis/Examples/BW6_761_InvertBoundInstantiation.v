(** * BW6_761_InvertBoundInstantiation — parametric bound-aware discharge
 *  template for BW6-761 Fp inversion section hypotheses.
 *
 *  Phase 0e — step 1 (BW6-761), mirrors [BN254_InvertBoundInstantiation.v].
 *  WBW 12x64 layout (12 limbs of 64 bits for the 761-bit prime).
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
Require Import Bedrock.Field.Synthesis.Examples.BW6_761_FpInv.
Require Import Bedrock.Field.Synthesis.Examples.bw6_761_prime_certif.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation Fp_bw6_761_pos := bw6_761_prime_pos.

Section BW6_761InvertBoundInstantiation.

  Variable rust_state : Type.
  Variable get_slot_12x64 :
    rust_state -> String.string -> option (list Z).
  Variable set_slot_12x64 :
    rust_state -> String.string -> list Z -> rust_state.
  Variable set_scalar : rust_state -> String.string -> Z -> rust_state.

  Hypothesis get_set_slot_other :
    forall rs x y v,
      x <> y ->
      get_slot_12x64 (set_slot_12x64 rs x v) y = get_slot_12x64 rs y.

  Hypothesis get_slot_after_set_scalar :
    forall rs s z y,
      get_slot_12x64 (set_scalar rs s z) y = get_slot_12x64 rs y.

  Definition limb_bound_wbw (l : Z) : Prop := 0 <= l < 2 ^ 64.

  Definition limbs_bounded_wbw (limbs : list Z) : Prop :=
    Forall limb_bound_wbw limbs.

  Definition feval_bound_bw6_761 (limbs : list Z) : F Fp_bw6_761_pos :=
    F.of_Z _ (Positional.eval (uweight 64) 12%nat limbs).

  Definition Fp_bw6_761_holds_bound
      (rs : rust_state) (v : String.string) (x : F Fp_bw6_761_pos) : Prop :=
    exists limbs : list Z,
      get_slot_12x64 rs v = Some limbs
      /\ length limbs = 12%nat
      /\ limbs_bounded_wbw limbs
      /\ feval_bound_bw6_761 limbs = x.

  Lemma scalar_set_preserves_holds_bound_bw6_761 :
    forall (rs : rust_state) (s : String.string) (z : Z)
           (y : String.string) (v : F Fp_bw6_761_pos),
      Fp_bw6_761_holds_bound rs y v ->
      Fp_bw6_761_holds_bound (set_scalar rs s z) y v.
  Proof.
    intros rs s z y v [limbs [Hget [Hlen [Hbnd Hev]]]].
    exists limbs. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_slot_after_set_scalar. exact Hget.
  Qed.

  Lemma let_zero_preserves_holds_bound_bw6_761 :
    forall (rs : rust_state) (x : String.string) (limbs : list Z)
           (y : String.string) (vp : F Fp_bw6_761_pos),
      y <> x ->
      Fp_bw6_761_holds_bound rs y vp ->
      Fp_bw6_761_holds_bound (set_slot_12x64 rs x limbs) y vp.
  Proof.
    intros rs x limbs y vp Hne [limbs0 [Hget [Hlen [Hbnd Hev]]]].
    exists limbs0. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_set_slot_other.
    - exact Hget.
    - intro Hxy. apply Hne. symmetry; exact Hxy.
  Qed.

  Record located_bw6_761 : Type := mkLocated_bw6_761
    { loc_var  : String.string;
      loc_type : bool }.

  Definition TFp_bw6_761 : bool := true.

  Definition callee_post_bound_bw6_761
    (fname : String.string)
    (args : list located_bw6_761)
    (dst : located_bw6_761)
    (rs1 rs2 : rust_state) : Prop :=
    match fname, args with
    | "bw6_761_fp_sqr", [src] =>
        loc_type dst = TFp_bw6_761 ->
        loc_type src = TFp_bw6_761 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_bw6_761_pos),
          Fp_bw6_761_holds_bound rs1 (loc_var src) x ->
          Fp_bw6_761_holds_bound rs2 (loc_var dst) (F.pow x 2) /\
          (forall (y : String.string) (v : F Fp_bw6_761_pos),
              y <> loc_var dst ->
              Fp_bw6_761_holds_bound rs1 y v ->
              Fp_bw6_761_holds_bound rs2 y v)
    | "bw6_761_fp_mul", [a; b] =>
        loc_type dst = TFp_bw6_761 ->
        loc_type a = TFp_bw6_761 ->
        loc_type b = TFp_bw6_761 ->
        loc_var dst <> loc_var a ->
        loc_var dst <> loc_var b ->
        forall (xa xb : F Fp_bw6_761_pos),
          Fp_bw6_761_holds_bound rs1 (loc_var a) xa ->
          Fp_bw6_761_holds_bound rs1 (loc_var b) xb ->
          Fp_bw6_761_holds_bound rs2 (loc_var dst) (F.mul xa xb) /\
          (forall (y : String.string) (v : F Fp_bw6_761_pos),
              y <> loc_var dst ->
              Fp_bw6_761_holds_bound rs1 y v ->
              Fp_bw6_761_holds_bound rs2 y v)
    | "bw6_761_fp_copy", [src] =>
        loc_type dst = TFp_bw6_761 ->
        loc_type src = TFp_bw6_761 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_bw6_761_pos),
          Fp_bw6_761_holds_bound rs1 (loc_var src) x ->
          Fp_bw6_761_holds_bound rs2 (loc_var dst) x /\
          (forall (y : String.string) (v : F Fp_bw6_761_pos),
              y <> loc_var dst ->
              Fp_bw6_761_holds_bound rs1 y v ->
              Fp_bw6_761_holds_bound rs2 y v)
    | _, _ => True
    end.

  Record RCallBN : Type := mkRCallBN
    { rc_fname : String.string;
      rc_dst   : located_bw6_761;
      rc_args  : list located_bw6_761 }.

  Variable Hexec_b : RCallBN -> rust_state -> rust_state -> Prop.

  Hypothesis Hexec_call_inv :
    forall (rc : RCallBN) (rs1 rs2 : rust_state),
      Hexec_b rc rs1 rs2 ->
      callee_post_bound_bw6_761 (rc_fname rc) (rc_args rc) (rc_dst rc) rs1 rs2.

  Definition RCall (fname : String.string)
                   (dst : located_bw6_761)
                   (args : list located_bw6_761) : RCallBN :=
    mkRCallBN fname dst args.

  Definition fp_frame_bw6_761 (rs1 rs2 : rust_state) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude ->
                Fp_bw6_761_holds_bound rs1 y v ->
                Fp_bw6_761_holds_bound rs2 y v.

  Lemma sqr_correct_bound_bw6_761 :
    forall (dest src : located_bw6_761) (rs1 rs2 : rust_state) (x : F Fp_bw6_761_pos),
      loc_type dest = TFp_bw6_761 ->
      loc_type src = TFp_bw6_761 ->
      loc_var dest <> loc_var src ->
      Fp_bw6_761_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "bw6_761_fp_sqr" dest [src]) rs1 rs2 ->
      Fp_bw6_761_holds_bound rs2 (loc_var dest) (F.pow x 2) /\
      fp_frame_bw6_761 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bw6_761. exact Hframe.
  Qed.

  Lemma mul_correct_bound_bw6_761 :
    forall (dest a b : located_bw6_761) (rs1 rs2 : rust_state)
           (xa xb : F Fp_bw6_761_pos),
      loc_type dest = TFp_bw6_761 ->
      loc_type a = TFp_bw6_761 ->
      loc_type b = TFp_bw6_761 ->
      loc_var dest <> loc_var a ->
      loc_var dest <> loc_var b ->
      Fp_bw6_761_holds_bound rs1 (loc_var a) xa ->
      Fp_bw6_761_holds_bound rs1 (loc_var b) xb ->
      Hexec_b (RCall "bw6_761_fp_mul" dest [a; b]) rs1 rs2 ->
      Fp_bw6_761_holds_bound rs2 (loc_var dest) (F.mul xa xb) /\
      fp_frame_bw6_761 rs1 rs2 (loc_var dest).
  Proof.
    intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hat Hbt Hne_a Hne_b xa xb Hxa Hxb) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bw6_761. exact Hframe.
  Qed.

  Lemma copy_correct_bound_bw6_761 :
    forall (dest src : located_bw6_761) (rs1 rs2 : rust_state) (x : F Fp_bw6_761_pos),
      loc_type dest = TFp_bw6_761 ->
      loc_type src = TFp_bw6_761 ->
      loc_var dest <> loc_var src ->
      Fp_bw6_761_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "bw6_761_fp_copy" dest [src]) rs1 rs2 ->
      Fp_bw6_761_holds_bound rs2 (loc_var dest) x /\
      fp_frame_bw6_761 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bw6_761. exact Hframe.
  Qed.

  Variable BodySpec :
    rust_state -> rust_state -> located_bw6_761 -> located_bw6_761 -> Prop.

  Hypothesis Hbody_to_pow :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_bw6_761)
           (x : F Fp_bw6_761_pos),
      loc_type a_loc = TFp_bw6_761 ->
      loc_type dest = TFp_bw6_761 ->
      loc_var dest <> loc_var a_loc ->
      Fp_bw6_761_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_bw6_761_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (bw6_761_p - 2))).

  Theorem bw6_761_invert_body_correct_bound :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_bw6_761)
           (x : F Fp_bw6_761_pos),
      loc_type a_loc = TFp_bw6_761 ->
      loc_type dest = TFp_bw6_761 ->
      loc_var dest <> loc_var a_loc ->
      Fp_bw6_761_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_bw6_761_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (bw6_761_p - 2))).
  Proof.
    intros rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody.
    apply (Hbody_to_pow rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody).
  Qed.

End BW6_761InvertBoundInstantiation.

Print Assumptions scalar_set_preserves_holds_bound_bw6_761.
Print Assumptions let_zero_preserves_holds_bound_bw6_761.
Print Assumptions sqr_correct_bound_bw6_761.
Print Assumptions mul_correct_bound_bw6_761.
Print Assumptions copy_correct_bound_bw6_761.
Print Assumptions bw6_761_invert_body_correct_bound.
