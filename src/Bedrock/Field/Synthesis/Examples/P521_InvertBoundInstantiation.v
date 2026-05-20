(** * P521_InvertBoundInstantiation — parametric bound-aware discharge
 *  template for NIST P-521 Fp inversion section hypotheses.
 *
 *  Mirrors [P256_InvertBoundInstantiation.v] for P-521.  9-limb radix-2^64
 *  saturated representation (P-521 = 521 bits fits in 9 * 64 = 576 bits;
 *  the high limb holds 9 bits).
 *
 *  Bound decoder (9 limbs):
 *      Fp_p521_holds_bound rs v x :=
 *        exists limbs, get_slot_9x64 rs v = Some limbs
 *                   /\ length limbs = 9
 *                   /\ Forall (fun l => 0 <= l < 2^64) limbs
 *                   /\ F.of_Z _ (Positional.eval (uweight 64) 9 limbs) = x
 *
 *  P-521 base prime: p = 2^521 - 1 (Mersenne).
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
Require Import Crypto.Arithmetic.UniformWeight.
Require Import Bedrock.Field.Synthesis.Examples.P521_FpInv.

Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Definition p521_prime_pos : positive :=
  Eval vm_compute in
    Z.to_pos (2^521 - 1)%Z.

Local Notation Fp_p521_pos := p521_prime_pos.

Lemma p521_prime_pos_eq : Z.pos p521_prime_pos = p521_p.
Proof. vm_compute. reflexivity. Qed.

Section P521InvertBoundInstantiation.

  Variable rust_state : Type.

  Variable get_slot_9x64 :
    rust_state -> String.string -> option (list Z).
  Variable set_slot_9x64 :
    rust_state -> String.string -> list Z -> rust_state.
  Variable set_scalar : rust_state -> String.string -> Z -> rust_state.

  Hypothesis get_set_slot_other :
    forall rs x y v,
      x <> y ->
      get_slot_9x64 (set_slot_9x64 rs x v) y = get_slot_9x64 rs y.

  Hypothesis get_slot_after_set_scalar :
    forall rs s z y,
      get_slot_9x64 (set_scalar rs s z) y = get_slot_9x64 rs y.

  Definition limb_bound_wbw (l : Z) : Prop := 0 <= l < 2 ^ 64.

  Definition limbs_bounded_wbw (limbs : list Z) : Prop :=
    Forall limb_bound_wbw limbs.

  Definition feval_bound_p521 (limbs : list Z) : F Fp_p521_pos :=
    F.of_Z _ (Positional.eval (uweight 64) 9%nat limbs).

  Definition Fp_p521_holds_bound
      (rs : rust_state) (v : String.string) (x : F Fp_p521_pos) : Prop :=
    exists limbs : list Z,
      get_slot_9x64 rs v = Some limbs
      /\ length limbs = 9%nat
      /\ limbs_bounded_wbw limbs
      /\ feval_bound_p521 limbs = x.

  Lemma scalar_set_preserves_holds_bound_p521 :
    forall (rs : rust_state) (s : String.string) (z : Z)
           (y : String.string) (v : F Fp_p521_pos),
      Fp_p521_holds_bound rs y v ->
      Fp_p521_holds_bound (set_scalar rs s z) y v.
  Proof.
    intros rs s z y v [limbs [Hget [Hlen [Hbnd Hev]]]].
    exists limbs. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_slot_after_set_scalar. exact Hget.
  Qed.

  Lemma let_zero_preserves_holds_bound_p521 :
    forall (rs : rust_state) (x : String.string) (limbs : list Z)
           (y : String.string) (vp : F Fp_p521_pos),
      y <> x ->
      Fp_p521_holds_bound rs y vp ->
      Fp_p521_holds_bound (set_slot_9x64 rs x limbs) y vp.
  Proof.
    intros rs x limbs y vp Hne [limbs0 [Hget [Hlen [Hbnd Hev]]]].
    exists limbs0. split; [|split; [exact Hlen|split; [exact Hbnd|exact Hev]]].
    rewrite get_set_slot_other.
    - exact Hget.
    - intro Hxy. apply Hne. symmetry; exact Hxy.
  Qed.

  Record located_p521 : Type := mkLocated_p521
    { loc_var  : String.string;
      loc_type : bool }.

  Definition TFp_p521 : bool := true.

  Definition callee_post_bound_p521
    (fname : String.string)
    (args : list located_p521)
    (dst : located_p521)
    (rs1 rs2 : rust_state) : Prop :=
    match fname, args with
    | "p521_fp_sqr", [src] =>
        loc_type dst = TFp_p521 ->
        loc_type src = TFp_p521 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_p521_pos),
          Fp_p521_holds_bound rs1 (loc_var src) x ->
          Fp_p521_holds_bound rs2 (loc_var dst) (F.pow x 2) /\
          (forall (y : String.string) (v : F Fp_p521_pos),
              y <> loc_var dst ->
              Fp_p521_holds_bound rs1 y v ->
              Fp_p521_holds_bound rs2 y v)
    | "p521_fp_mul", [a; b] =>
        loc_type dst = TFp_p521 ->
        loc_type a = TFp_p521 ->
        loc_type b = TFp_p521 ->
        loc_var dst <> loc_var a ->
        loc_var dst <> loc_var b ->
        forall (xa xb : F Fp_p521_pos),
          Fp_p521_holds_bound rs1 (loc_var a) xa ->
          Fp_p521_holds_bound rs1 (loc_var b) xb ->
          Fp_p521_holds_bound rs2 (loc_var dst) (F.mul xa xb) /\
          (forall (y : String.string) (v : F Fp_p521_pos),
              y <> loc_var dst ->
              Fp_p521_holds_bound rs1 y v ->
              Fp_p521_holds_bound rs2 y v)
    | "p521_fp_copy", [src] =>
        loc_type dst = TFp_p521 ->
        loc_type src = TFp_p521 ->
        loc_var dst <> loc_var src ->
        forall (x : F Fp_p521_pos),
          Fp_p521_holds_bound rs1 (loc_var src) x ->
          Fp_p521_holds_bound rs2 (loc_var dst) x /\
          (forall (y : String.string) (v : F Fp_p521_pos),
              y <> loc_var dst ->
              Fp_p521_holds_bound rs1 y v ->
              Fp_p521_holds_bound rs2 y v)
    | _, _ => True
    end.

  Record RCallP521 : Type := mkRCallP521
    { rc_fname : String.string;
      rc_dst   : located_p521;
      rc_args  : list located_p521 }.

  Variable Hexec_b : RCallP521 -> rust_state -> rust_state -> Prop.

  Hypothesis Hexec_call_inv :
    forall (rc : RCallP521) (rs1 rs2 : rust_state),
      Hexec_b rc rs1 rs2 ->
      callee_post_bound_p521 (rc_fname rc) (rc_args rc) (rc_dst rc) rs1 rs2.

  Definition RCall (fname : String.string)
                   (dst : located_p521)
                   (args : list located_p521) : RCallP521 :=
    mkRCallP521 fname dst args.

  Definition fp_frame_p521 (rs1 rs2 : rust_state) (exclude : String.string) :
      Prop :=
    forall y v, y <> exclude ->
                Fp_p521_holds_bound rs1 y v ->
                Fp_p521_holds_bound rs2 y v.

  Lemma sqr_correct_bound_p521 :
    forall (dest src : located_p521) (rs1 rs2 : rust_state) (x : F Fp_p521_pos),
      loc_type dest = TFp_p521 ->
      loc_type src = TFp_p521 ->
      loc_var dest <> loc_var src ->
      Fp_p521_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "p521_fp_sqr" dest [src]) rs1 rs2 ->
      Fp_p521_holds_bound rs2 (loc_var dest) (F.pow x 2) /\
      fp_frame_p521 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_p521. exact Hframe.
  Qed.

  Lemma mul_correct_bound_p521 :
    forall (dest a b : located_p521) (rs1 rs2 : rust_state)
           (xa xb : F Fp_p521_pos),
      loc_type dest = TFp_p521 ->
      loc_type a = TFp_p521 ->
      loc_type b = TFp_p521 ->
      loc_var dest <> loc_var a ->
      loc_var dest <> loc_var b ->
      Fp_p521_holds_bound rs1 (loc_var a) xa ->
      Fp_p521_holds_bound rs1 (loc_var b) xb ->
      Hexec_b (RCall "p521_fp_mul" dest [a; b]) rs1 rs2 ->
      Fp_p521_holds_bound rs2 (loc_var dest) (F.mul xa xb) /\
      fp_frame_p521 rs1 rs2 (loc_var dest).
  Proof.
    intros dest a b rs1 rs2 xa xb Hdt Hat Hbt Hne_a Hne_b Hxa Hxb Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hat Hbt Hne_a Hne_b xa xb Hxa Hxb) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_p521. exact Hframe.
  Qed.

  Lemma copy_correct_bound_p521 :
    forall (dest src : located_p521) (rs1 rs2 : rust_state) (x : F Fp_p521_pos),
      loc_type dest = TFp_p521 ->
      loc_type src = TFp_p521 ->
      loc_var dest <> loc_var src ->
      Fp_p521_holds_bound rs1 (loc_var src) x ->
      Hexec_b (RCall "p521_fp_copy" dest [src]) rs1 rs2 ->
      Fp_p521_holds_bound rs2 (loc_var dest) x /\
      fp_frame_p521 rs1 rs2 (loc_var dest).
  Proof.
    intros dest src rs1 rs2 x Hdt Hst Hne Hsx Hexec_n.
    apply Hexec_call_inv in Hexec_n.
    cbn in Hexec_n.
    specialize (Hexec_n Hdt Hst Hne x Hsx) as [Hdest Hframe].
    split; [exact Hdest|]. unfold fp_frame_p521. exact Hframe.
  Qed.

  Variable BodySpec :
    rust_state -> rust_state -> located_p521 -> located_p521 -> Prop.

  Hypothesis Hbody_to_pow :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_p521)
           (x : F Fp_p521_pos),
      loc_type a_loc = TFp_p521 ->
      loc_type dest = TFp_p521 ->
      loc_var dest <> loc_var a_loc ->
      Fp_p521_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_p521_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (p521_p - 2))).

  Theorem p521_invert_body_correct_bound :
    forall (rs1 rs2 : rust_state) (a_loc dest : located_p521)
           (x : F Fp_p521_pos),
      loc_type a_loc = TFp_p521 ->
      loc_type dest = TFp_p521 ->
      loc_var dest <> loc_var a_loc ->
      Fp_p521_holds_bound rs1 (loc_var a_loc) x ->
      BodySpec rs1 rs2 a_loc dest ->
      Fp_p521_holds_bound rs2 (loc_var dest)
        (F.pow x (Z.to_N (p521_p - 2))).
  Proof.
    intros rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody.
    apply (Hbody_to_pow rs1 rs2 a_loc dest x Halt Hdt Hdne Hax Hbody).
  Qed.

End P521InvertBoundInstantiation.

Print Assumptions scalar_set_preserves_holds_bound_p521.
Print Assumptions let_zero_preserves_holds_bound_p521.
Print Assumptions sqr_correct_bound_p521.
Print Assumptions mul_correct_bound_p521.
Print Assumptions copy_correct_bound_p521.
Print Assumptions p521_invert_body_correct_bound.
