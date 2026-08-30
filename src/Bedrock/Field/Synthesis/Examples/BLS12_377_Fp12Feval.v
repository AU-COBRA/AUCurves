(** * Fp12 feval bridge lemmas for BLS12-377.
 *
 *  Bridges Fp12.v operations (bedrock2 model, uses fp6_mul x x in sqr)
 *  against a "spec" Fp12 that uses fp6_sqr (Chung-Hasan SQR3) directly.
 *
 *  BLS12-377 uses beta=-5, xi=(0,1) vs BLS12-381's beta=-1, xi=(1,1).
 *  All Fp6/Fp2 operations are from the parameterized Fp6.v, not from
 *  Pairing.v (which hard-codes beta=-1).
 *
 *  Key hypotheses (from BLS12_377_Fp6Feval.v):
 *  - fp6_mul_self_eq_sqr: Fp6.fp6_mul a a = Fp6.fp6_sqr a
 *
 *  The key lemmas (fp12_sqr_eq, fp12_inv_eq) are non-trivial because
 *  Fp12.fp12_sqr uses fp6_mul x x while the spec uses fp6_sqr.
 *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Spec.BLS12Pairing.Fp6.
Require Import Spec.BLS12Pairing.Fp12.

Local Open Scope Z_scope.

Local Opaque Fp6.fp6_add Fp6.fp6_sub Fp6.fp6_neg Fp6.fp6_mul
  Fp6.fp6_sqr Fp6.fp6_mul_by_v Fp6.fp6_inv Fp6.fp6_mul_fp2
  Fp6.fp6_frobenius Fp6.fp6_frobenius_p2.

Section Fp12Bridge377.
  Variable p : positive.

  Local Notation Fp := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp6' := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12' := (Fp6' * Fp6')%type.

  Variable beta : Fp.
  Variable xi_re xi_im : Fp.

  (* Frobenius constants *)
  Variable fg1 fg2 fg1_p2 fg2_p2 : Fp2.
  Variable w_frob_c1 w_frob_p2_c1 : Fp2.

  (* Abbreviations for readability *)
  Let fp6_add := Fp6.fp6_add p.
  Let fp6_sub := Fp6.fp6_sub p.
  Let fp6_neg := Fp6.fp6_neg p.
  Let fp6_mul := Fp6.fp6_mul p beta xi_re xi_im.
  Let fp6_sqr := Fp6.fp6_sqr p beta xi_re xi_im.
  Let fp6_mul_by_v := Fp6.fp6_mul_by_v p beta xi_re xi_im.
  Let fp6_inv := Fp6.fp6_inv p beta xi_re xi_im.
  Let fp6_mul_fp2 := Fp6.fp6_mul_fp2 p beta.
  Let fp6_frobenius := Fp6.fp6_frobenius p beta fg1 fg2.
  Let fp6_frobenius_p2 := Fp6.fp6_frobenius_p2 p beta fg1_p2 fg2_p2.

  (* ================================================================ *)
  (** ** "Spec" Fp12 operations                                       *)
  (* ================================================================ *)

  (** Spec Fp12 operations use fp6_sqr instead of fp6_mul x x.
      This matches Pairing.v's convention and is the verification target. *)

  Definition spec_fp12_mul (a b : Fp12') : Fp12' :=
    let a0 := fst a in let a1 := snd a in
    let b0 := fst b in let b1 := snd b in
    let v0 := fp6_mul a0 b0 in
    let v1 := fp6_mul a1 b1 in
    let c0 := fp6_add v0 (fp6_mul_by_v v1) in
    let c1 := fp6_sub (fp6_sub (fp6_mul (fp6_add a0 a1) (fp6_add b0 b1))
                                v0) v1 in
    (c0, c1).

  Definition spec_fp12_sqr (a : Fp12') : Fp12' :=
    let a0 := fst a in let a1 := snd a in
    let a0_sq := fp6_sqr a0 in     (* uses fp6_sqr, not fp6_mul x x *)
    let a1_sq := fp6_sqr a1 in
    let cross := fp6_mul a0 a1 in
    let c0 := fp6_add a0_sq (fp6_mul_by_v a1_sq) in
    let c1 := fp6_add cross cross in
    (c0, c1).

  Definition spec_fp12_conjugate (a : Fp12') : Fp12' :=
    (fst a, fp6_neg (snd a)).

  Definition spec_fp12_inv (a : Fp12') : Fp12' :=
    let a0 := fst a in let a1 := snd a in
    let a0_sq := fp6_sqr a0 in     (* uses fp6_sqr *)
    let a1_sq := fp6_sqr a1 in
    let norm := fp6_sub a0_sq (fp6_mul_by_v a1_sq) in
    let norm_inv := fp6_inv norm in
    (fp6_mul a0 norm_inv, fp6_neg (fp6_mul a1 norm_inv)).

  Definition spec_fp12_frobenius (a : Fp12') : Fp12' :=
    let c0' := fp6_frobenius (fst a) in
    let c1' := fp6_mul_fp2 (fp6_frobenius (snd a)) w_frob_c1 in
    (c0', c1').

  Definition spec_fp12_frobenius_p2 (a : Fp12') : Fp12' :=
    let c0' := fp6_frobenius_p2 (fst a) in
    let c1' := fp6_mul_fp2 (fp6_frobenius_p2 (snd a)) w_frob_p2_c1 in
    (c0', c1').

  (* ================================================================ *)
  (** ** Bridge hypotheses                                             *)
  (* ================================================================ *)

  (** The only non-trivial hypothesis: schoolbook squaring = Chung-Hasan. *)
  Hypothesis fp6_mul_self_eq_sqr : forall a : Fp6',
    Fp6.fp6_mul p beta xi_re xi_im a a = Fp6.fp6_sqr p beta xi_re xi_im a.

  (* ================================================================ *)
  (** ** Fp12 bridge lemmas                                            *)
  (* ================================================================ *)

  Lemma fp12_mul_eq : forall a b : Fp12',
    Fp12.fp12_mul p beta xi_re xi_im a b = spec_fp12_mul a b.
  Proof.
    intros [a0 a1] [b0 b1].
    unfold Fp12.fp12_mul, spec_fp12_mul,
           Fp12.fp12_c0, Fp12.fp12_c1, Fp12.mk_fp12; simpl fst; simpl snd.
    reflexivity.
  Qed.

  Lemma fp12_sqr_eq : forall a : Fp12',
    Fp12.fp12_sqr p beta xi_re xi_im a = spec_fp12_sqr a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_sqr, spec_fp12_sqr,
           Fp12.fp12_c0, Fp12.fp12_c1, Fp12.mk_fp12; simpl fst; simpl snd.
    unfold fp6_sqr, fp6_mul, fp6_add, fp6_mul_by_v.
    rewrite !fp6_mul_self_eq_sqr. reflexivity.
  Qed.

  Lemma fp12_conjugate_eq : forall a : Fp12',
    Fp12.fp12_conjugate p a = spec_fp12_conjugate a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_conjugate, spec_fp12_conjugate,
           Fp12.fp12_c0, Fp12.fp12_c1, Fp12.mk_fp12; simpl fst; simpl snd.
    reflexivity.
  Qed.

  Lemma fp12_inv_eq : forall a : Fp12',
    Fp12.fp12_inv p beta xi_re xi_im a = spec_fp12_inv a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_inv, spec_fp12_inv,
           Fp12.fp12_c0, Fp12.fp12_c1, Fp12.mk_fp12; simpl fst; simpl snd.
    unfold fp6_sqr, fp6_mul, fp6_sub, fp6_neg, fp6_mul_by_v, fp6_inv.
    rewrite !fp6_mul_self_eq_sqr. reflexivity.
  Qed.

  Lemma fp12_frobenius_eq : forall a : Fp12',
    Fp12.fp12_frobenius p beta fg1 fg2 w_frob_c1 a =
    spec_fp12_frobenius a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_frobenius, spec_fp12_frobenius,
           Fp12.fp12_c0, Fp12.fp12_c1, Fp12.mk_fp12; simpl fst; simpl snd.
    reflexivity.
  Qed.

  Lemma fp12_frobenius_p2_eq : forall a : Fp12',
    Fp12.fp12_frobenius_p2 p beta fg1_p2 fg2_p2 w_frob_p2_c1 a =
    spec_fp12_frobenius_p2 a.
  Proof.
    intros [a0 a1].
    unfold Fp12.fp12_frobenius_p2, spec_fp12_frobenius_p2,
           Fp12.fp12_c0, Fp12.fp12_c1, Fp12.mk_fp12; simpl fst; simpl snd.
    reflexivity.
  Qed.

  (* ================================================================ *)
  (** ** Binary exponentiation                                         *)
  (* ================================================================ *)

  (** Spec pow_bits_aux uses spec_fp12_sqr and spec_fp12_mul. *)
  Fixpoint spec_pow_bits_aux (base : Fp12') (bits : list bool)
    (acc : Fp12') (started : bool) : Fp12' :=
    match bits with
    | [] => acc
    | b :: rest =>
      let acc' := if started then spec_fp12_sqr acc else acc in
      if b then
        let acc'' := if started then spec_fp12_mul acc' base else base in
        spec_pow_bits_aux base rest acc'' true
      else
        spec_pow_bits_aux base rest acc' started
    end.

  (** Bedrock2 pow_bits_aux uses Fp12.fp12_sqr and Fp12.fp12_mul. *)
  Fixpoint bedrock2_pow_bits_aux (base : Fp12') (bits : list bool)
    (acc : Fp12') (started : bool) : Fp12' :=
    match bits with
    | [] => acc
    | b :: rest =>
      let acc' := if started then Fp12.fp12_sqr p beta xi_re xi_im acc
                  else acc in
      if b then
        let acc'' := if started
                     then Fp12.fp12_mul p beta xi_re xi_im acc' base
                     else base in
        bedrock2_pow_bits_aux base rest acc'' true
      else
        bedrock2_pow_bits_aux base rest acc' started
    end.

  Lemma pow_bits_aux_feval : forall bits base acc started,
    bedrock2_pow_bits_aux base bits acc started =
    spec_pow_bits_aux base bits acc started.
  Proof.
    induction bits as [|b bs IH]; intros base acc started.
    - abstract reflexivity.
    - simpl bedrock2_pow_bits_aux. simpl spec_pow_bits_aux.
      rewrite fp12_sqr_eq, fp12_mul_eq. destruct b; apply IH.
  Qed.

  (** Helper: bit extraction, same as Pairing.Z_to_bits. *)
  Definition Z_to_bits (width : nat) (z : Z) : list bool :=
    List.map (fun i => Z.testbit z (Z.of_nat i))
             (List.rev (List.seq 0 width)).

  Definition bedrock2_pow_Z (base : Fp12') (exp : Z) (width : nat) : Fp12' :=
    bedrock2_pow_bits_aux base (Z_to_bits width exp)
      (Fp12.fp12_one p) false.

  Definition spec_pow_Z (base : Fp12') (exp : Z) (width : nat) : Fp12' :=
    spec_pow_bits_aux base (Z_to_bits width exp)
      (Fp12.fp12_one p) false.

  Lemma pow_Z_feval : forall base exp width,
    bedrock2_pow_Z base exp width = spec_pow_Z base exp width.
  Proof.
    intros.
    unfold bedrock2_pow_Z, spec_pow_Z.
    apply pow_bits_aux_feval.
  Qed.

  (* ================================================================ *)
  (** ** Power-by-BLS-parameter for BLS12-377                          *)
  (* ================================================================ *)

  (** BLS12-377 parameter: u = 0x8508c00000000001 (positive, 64 bits). *)
  Let bls377_x : Z := 0x8508c00000000001.

  Definition bedrock2_pow_bls_x (f : Fp12') : Fp12' :=
    bedrock2_pow_Z f bls377_x 64.

  Definition spec_pow_bls_x (f : Fp12') : Fp12' :=
    spec_pow_Z f bls377_x 64.

  Lemma pow_bls_x_feval : forall f,
    bedrock2_pow_bls_x f = spec_pow_bls_x f.
  Proof.
    intro. unfold bedrock2_pow_bls_x, spec_pow_bls_x.
    apply pow_Z_feval.
  Qed.

  (** For BLS12-377, x is POSITIVE, so pow_bls_x_signed is NOT conjugated.
      (Unlike BLS12-381 where x is negative.)
      However, the DSD formula uses conjugation for certain sub-expressions,
      so we still provide the signed version. *)
  Definition bedrock2_pow_bls_x_signed (f : Fp12') : Fp12' :=
    bedrock2_pow_bls_x f.

  Definition spec_pow_bls_x_signed (f : Fp12') : Fp12' :=
    spec_pow_bls_x f.

  Lemma pow_bls_x_signed_feval : forall f,
    bedrock2_pow_bls_x_signed f = spec_pow_bls_x_signed f.
  Proof.
    intro f. unfold bedrock2_pow_bls_x_signed, spec_pow_bls_x_signed.
    apply pow_bls_x_feval.
  Qed.

  Definition bedrock2_pow_bls_x_half (f : Fp12') : Fp12' :=
    bedrock2_pow_Z f (bls377_x / 2) 63.

  Definition spec_pow_bls_x_half (f : Fp12') : Fp12' :=
    spec_pow_Z f (bls377_x / 2) 63.

  Lemma pow_bls_x_half_feval : forall f,
    bedrock2_pow_bls_x_half f = spec_pow_bls_x_half f.
  Proof.
    intro. unfold bedrock2_pow_bls_x_half, spec_pow_bls_x_half.
    apply pow_Z_feval.
  Qed.

  Definition bedrock2_pow_bls_x_half_signed (f : Fp12') : Fp12' :=
    bedrock2_pow_bls_x_half f.

  Definition spec_pow_bls_x_half_signed (f : Fp12') : Fp12' :=
    spec_pow_bls_x_half f.

  Lemma pow_bls_x_half_signed_feval : forall f,
    bedrock2_pow_bls_x_half_signed f = spec_pow_bls_x_half_signed f.
  Proof.
    intro f.
    unfold bedrock2_pow_bls_x_half_signed, spec_pow_bls_x_half_signed.
    apply pow_bls_x_half_feval.
  Qed.

End Fp12Bridge377.
