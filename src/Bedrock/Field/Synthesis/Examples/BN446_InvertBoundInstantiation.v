(** * BN446_InvertBoundInstantiation — parametric bound-aware discharge
 *  template for BN446 Fp inversion section hypotheses.
 *
 *  Phase 0e — step 1 (BN446), mirrors [BN254_InvertBoundInstantiation.v].
 *  WBW 7x64 layout (7 limbs of 64 bits for the 446-bit prime).
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
Require Import Bedrock.Field.Synthesis.Examples.BN446_FpInv.
Require Import Bedrock.Field.Synthesis.Examples.bn446_prime_certif.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation Fp_bn446_pos := bn446_prime_pos.

Section BN446InvertBoundInstantiation.

  Variable rust_state : Type.
  Variable get_slot_7x64 :
    rust_state -> String.string -> option (list Z).
  Variable set_slot_7x64 :
    rust_state -> String.string -> list Z -> rust_state.
  Variable set_scalar : rust_state -> String.string -> Z -> rust_state.

  Hypothesis get_set_slot_other :
    forall rs x y v,
      x <> y ->
      get_slot_7x64 (set_slot_7x64 rs x v) y = get_slot_7x64 rs y.

  Hypothesis get_slot_after_set_scalar :
    forall rs s z y,
      get_slot_7x64 (set_scalar rs s z) y = get_slot_7x64 rs y.

  Definition limb_bound_wbw (l : Z) : Prop := 0 <= l < 2 ^ 64.

  Definition limbs_bounded_wbw (limbs : list Z) : Prop :=
    Forall limb_bound_wbw limbs.

  Definition feval_bound_bn446 (limbs : list Z) : F Fp_bn446_pos :=
    F.of_Z _ (Positional.eval (uweight 64) 7%nat limbs).

  Definition Fp_bn446_holds_bound
      (rs : rust_state) (v : String.string) (x : F Fp_bn446_pos) : Prop :=
    exists limbs : list Z,
      get_slot_7x64 rs v = Some limbs
      /\ length limbs = 7%nat
      /\ limbs_bounded_wbw limbs
      /\ feval_bound_bn446 limbs = x.

  Lemma scalar_set_preserves_holds_bound_bn446 :
    forall (rs : rust_state) (s : String.string) (z : Z)
           (y : String.string) (v : F Fp_bn446_pos),
      Fp_bn446_holds_bound rs y v ->
      Fp_bn446_holds_bound (set_scalar rs s z) y v.
  Proof.
    intros rs s z y v [limbs [Hget [Hlen [Hbnd Hev]]]].
    exists limbs. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_slot_after_set_scalar. exact Hget.
  Qed.

  Lemma let_zero_preserves_holds_bound_bn446 :
    forall (rs : rust_state) (x : String.string) (limbs : list Z)
           (y : String.string) (vp : F Fp_bn446_pos),
      y <> x ->
      Fp_bn446_holds_bound rs y vp ->
      Fp_bn446_holds_bound (set_slot_7x64 rs x limbs) y vp.
  Proof.
    intros rs x limbs y vp Hne [limbs0 [Hget [Hlen [Hbnd Hev]]]].
    exists limbs0. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_set_slot_other.
    - exact Hget.
    - intro Hxy. apply Hne. symmetry; exact Hxy.
  Qed.

  Record located_bn446 : Type := mkLocated_bn446
    { loc_var  : String.string;
      loc_type : bool }.

  Definition TFp_bn446 : bool := true.

  Definition callee_post_bound_bn446
    (fname : String.string)
    (args : list located_bn446)
    (dst : located_bn446)
    (rs1 rs2 : rust_state) : Prop :=
    match fname, args with
    | "bn446_fp_sqr", [src] =>
        loc_type dst = TFp_bn446 ->
        loc_type src = TFp_bn446 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_bn446_pos),
          Fp_bn446_holds_bound rs1 (loc_var src) x ->
          Fp_bn446_holds_bound rs2 (loc_var dst) (F.pow x 2) /\
          (forall (y : String.string) (v : F Fp_bn446_pos),
              y <> loc_var dst ->
              Fp_bn446_holds_bound rs1 y v ->
              Fp_bn446_holds_bound rs2 y v)
    | "bn446_fp_mul", [a; b] =>
        loc_type dst = TFp_bn446 ->
        loc_type a = TFp_bn446 ->
        loc_type b = TFp_bn446 ->
        loc_var dst <> loc_var a ->
        loc_var dst <> loc_var b ->
        forall (xa xb : F Fp_bn446_pos),
          Fp_bn446_holds_bound rs1 (loc_var a) xa ->
          Fp_bn446_holds_bound rs1 (loc_var b) xb ->
          Fp_bn446_holds_bound rs2 (loc_var dst) (F.mul xa xb) /\
          (forall (y : String.string) (v : F Fp_bn446_pos),
              y <> loc_var dst ->
              Fp_bn446_holds_bound rs1 y v ->
              Fp_bn446_holds_bound rs2 y v)
    | "bn446_fp_copy", [src] =>
        loc_type dst = TFp_bn446 ->
        loc_type src = TFp_bn446 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_bn446_pos),
          Fp_bn446_holds_bound rs1 (loc_var src) x ->
          Fp_bn446_holds_bound rs2 (loc_var dst) x /\
          (forall (y : String.string) (v : F Fp_bn446_pos),
              y <> loc_var dst ->
              Fp_bn446_holds_bound rs1 y v ->
              Fp_bn446_holds_bound rs2 y v)
    | _, _ => True
    end.

  Record RCallBN : Type := mkRCallBN
    { rc_fname : String.string;
      rc_dst   : located_bn446;
      rc_args  : list located_bn446 }.

  Variable Hexec_b : RCallBN -> rust_state -> rust_state -> Prop.

  Hypothesis Hexec_call_inv :
    forall (rc : RCallBN) (rs1 rs2 : rust_state),
      Hexec_b rc rs1 rs2 ->
      callee_post_bound_bn446 (rc_fname rc) (rc_args rc) (rc_dst rc) rs1 rs2.

  Definition RCall (fname : String.string)
                   (dst : located_bn446)
                   (args : list located_bn446) : RCallBN :=
    mkRCallBN fname dst args.

  Definition fp_frame_bn446 (rs1 rs2 : rust_state) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude ->
                Fp_bn446_holds_bound rs1 y v ->
                Fp_bn446_holds_bound rs2 y v.

  Lemma sqr_correct_bound_bn446 :
    forall (dest src : located_bn446) (rs1 rs2 : rust_state) (x : F Fp_bn446_pos),
      loc_type dest = TFp_bn446 ->
      loc_type src = TFp_bn446 ->
      loc_var dest <> loc_var src ->
      Fp_bn446_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "bn446_fp_sqr" dest [src]) rs1 rs2 ->
      Fp_bn446_holds_bound rs2 (loc_var dest) (F.pow x 2) /\
      fp_frame_bn446 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bn446. exact Hframe.
  Qed.

  Lemma mul_correct_bound_bn446 :
    forall (dest a b : located_bn446) (rs1 rs2 : rust_state)
           (xa xb : F Fp_bn446_pos),
      loc_type dest = TFp_bn446 ->
      loc_type a = TFp_bn446 ->
      loc_type b = TFp_bn446 ->
      loc_var dest <> loc_var a ->
      loc_var dest <> loc_var b ->
      Fp_bn446_holds_bound rs1 (loc_var a) xa ->
      Fp_bn446_holds_bound rs1 (loc_var b) xb ->
      Hexec_b (RCall "bn446_fp_mul" dest [a; b]) rs1 rs2 ->
      Fp_bn446_holds_bound rs2 (loc_var dest) (F.mul xa xb) /\
      fp_frame_bn446 rs1 rs2 (loc_var dest).
  Proof.
    intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hat Hbt Hne_a Hne_b xa xb Hxa Hxb) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bn446. exact Hframe.
  Qed.

  Lemma copy_correct_bound_bn446 :
    forall (dest src : located_bn446) (rs1 rs2 : rust_state) (x : F Fp_bn446_pos),
      loc_type dest = TFp_bn446 ->
      loc_type src = TFp_bn446 ->
      loc_var dest <> loc_var src ->
      Fp_bn446_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "bn446_fp_copy" dest [src]) rs1 rs2 ->
      Fp_bn446_holds_bound rs2 (loc_var dest) x /\
      fp_frame_bn446 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_bn446. exact Hframe.
  Qed.

  Variable BodySpec :
    rust_state -> rust_state -> located_bn446 -> located_bn446 -> Prop.

  Hypothesis Hbody_to_pow :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_bn446)
           (x : F Fp_bn446_pos),
      loc_type a_loc = TFp_bn446 ->
      loc_type dest = TFp_bn446 ->
      loc_var dest <> loc_var a_loc ->
      Fp_bn446_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_bn446_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (bn446_p - 2))).

  Theorem bn446_invert_body_correct_bound :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_bn446)
           (x : F Fp_bn446_pos),
      loc_type a_loc = TFp_bn446 ->
      loc_type dest = TFp_bn446 ->
      loc_var dest <> loc_var a_loc ->
      Fp_bn446_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_bn446_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (bn446_p - 2))).
  Proof.
    intros rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody.
    apply (Hbody_to_pow rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody).
  Qed.

End BN446InvertBoundInstantiation.

Print Assumptions scalar_set_preserves_holds_bound_bn446.
Print Assumptions let_zero_preserves_holds_bound_bn446.
Print Assumptions sqr_correct_bound_bn446.
Print Assumptions mul_correct_bound_bn446.
Print Assumptions copy_correct_bound_bn446.
Print Assumptions bn446_invert_body_correct_bound.
