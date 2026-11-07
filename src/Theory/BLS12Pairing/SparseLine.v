(** * Sparse multiplication by the Miller-loop line values (Pairing.v tower).

    [Pairing.make_line] has three nonzero Fp2 coefficients out of six:
      c0.c0 = lambda x_T - y_T,  c0.c1 = -lambda x_P,  c1.c1 = (y_P, 0)
    (indices 0, 1 and 4 in memory order), [line_of b0 b1 b4].

    - [mul_by_line6]: the product of f (six coefficients) with [line_of b0 b1 b4], in place on the
      coefficients of f as the bedrock2 function [bls12_Fp12_mul_by_line] computes it
      ([MulByLineAF.af_mul_by_line_gallina]): 13 Fp2 multiplications instead of 18;
    - [fp12_mul_by_line_eq]: it is [Pairing.fp12_mul f (line_of b0 b1 b4)] (ring identity, any p);
    - [sparse_part]: keeps the three slots of a line, [sparse_part_make_line]: the identity on
      the values of [make_line];
    - [miller_loop_sparse]: [Pairing.miller_loop] with the line multiplications done by
      [fp12_mul_by_line] on the coefficients of the line; equal to [Pairing.miller_loop]
      ([miller_loop_sparse_eq]).
*)

From Stdlib Require Import ZArith List Bool.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Module P := Theory.BLS12Pairing.Pairing.

Local Ltac split12 :=
  apply injective_projections; cbn [fst snd];
  (apply injective_projections; cbn [fst snd]; [apply injective_projections; cbn [fst snd] |]).

Section SparseLine.
  Context {p : positive}.

  Local Notation F := (F p).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  Add Ring Fp_ring : (@Fp_ring_theory p).
  Add Ring fp2_ring : (@fp2_ring_theory p).

  Local Notation fp2_add := (P.fp2_add p).
  Local Notation fp2_sub := (P.fp2_sub p).
  Local Notation fp2_mul := (P.fp2_mul p).
  Local Notation mul_xi := (P.fp2_mul_xi p).
  Local Notation fp2_zero := (P.fp2_zero p).

  Definition line_of (b0 b1 b4 : Fp2) : Fp12 :=
    P.fp12_build p (P.fp6_build p b0 b1 fp2_zero) (P.fp6_build p fp2_zero b4 fp2_zero).

  (** f = a0 + a1 w, a0 = (x0, x1, x2), a1 = (x3, x4, x5); line B0 + B1 w,
      B0 = (b0, b1, 0), B1 = (0, b4, 0). *)
  Definition mul_by_line6 (x0 x1 x2 x3 x4 x5 b0 b1 b4 : Fp2) : Fp12 :=
    (* T0 = a0 B0 = (s0, t, s1) *)
    let s0 := fp2_mul x0 b0 in
    let s1 := fp2_mul x1 b1 in
    let t := fp2_add x0 x1 in
    let u := fp2_add b0 b1 in
    let t := fp2_mul t u in
    let t := fp2_sub t s0 in
    let t := fp2_sub t s1 in
    let w := fp2_mul x2 b1 in
    let w := mul_xi w in
    let s0 := fp2_add s0 w in
    let w := fp2_mul x2 b0 in
    let s1 := fp2_add s1 w in
    (* T1 = a1 B1 = (r0, r1, r2) *)
    let r0 := fp2_mul x5 b4 in
    let r0 := mul_xi r0 in
    let r1 := fp2_mul x3 b4 in
    let r2 := fp2_mul x4 b4 in
    (* a0 + a1 *)
    let x3 := fp2_add x0 x3 in
    let x4 := fp2_add x1 x4 in
    let x5 := fp2_add x2 x5 in
    (* U = (a0 + a1)(B0 + B1) = (w, z, q) *)
    let u := fp2_add b1 b4 in
    let w := fp2_mul x3 b0 in
    let q := fp2_mul x4 u in
    let z := fp2_add x3 x4 in
    let e := fp2_add b0 u in
    let z := fp2_mul z e in
    let z := fp2_sub z w in
    let z := fp2_sub z q in
    let e := fp2_mul x5 u in
    let e := mul_xi e in
    let w := fp2_add w e in
    let e := fp2_mul x5 b0 in
    let q := fp2_add q e in
    (* c1 = U - T0 - T1 *)
    let x3 := fp2_sub w s0 in
    let x3 := fp2_sub x3 r0 in
    let x4 := fp2_sub z t in
    let x4 := fp2_sub x4 r1 in
    let x5 := fp2_sub q s1 in
    let x5 := fp2_sub x5 r2 in
    (* c0 = T0 + v T1 *)
    let e := mul_xi r2 in
    let x0 := fp2_add s0 e in
    let x1 := fp2_add t r0 in
    let x2 := fp2_add s1 r1 in
    ((x0, x1, x2), (x3, x4, x5)).

  Definition fp12_mul_by_line (f : Fp12) (b0 b1 b4 : Fp2) : Fp12 :=
    let '((x0, x1, x2), (x3, x4, x5)) := f in mul_by_line6 x0 x1 x2 x3 x4 x5 b0 b1 b4.

  Theorem fp12_mul_by_line_eq : forall f b0 b1 b4,
    fp12_mul_by_line f b0 b1 b4 = P.fp12_mul p f (line_of b0 b1 b4).
  Proof.
    intros [[[x0 x1] x2] [[x3 x4] x5]] b0 b1 b4.
    cbv [fp12_mul_by_line mul_by_line6 line_of
         P.fp12_mul P.fp12_build P.fp12_c0 P.fp12_c1
         P.fp6_add P.fp6_sub P.fp6_mul P.fp6_mul_by_v P.fp6_build
         P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
    rewrite !fp2_mul_xi_eq.
    split12; ring.
  Qed.

  (** The three slots of a line value. *)
  Definition sparse_part (l : Fp12) : Fp12 :=
    line_of (fst (fst (fst l))) (snd (fst (fst l))) (snd (fst (snd l))).

  Lemma sparse_part_line_of : forall b0 b1 b4, sparse_part (line_of b0 b1 b4) = line_of b0 b1 b4.
  Proof. reflexivity. Qed.

  Lemma sparse_part_make_line : forall lam xt yt xp yp,
    sparse_part (P.make_line p lam xt yt xp yp) = P.make_line p lam xt yt xp yp.
  Proof. reflexivity. Qed.

  Lemma fp12_mul_sparse_part : forall f l,
    P.fp12_mul p f (sparse_part l) =
    fp12_mul_by_line f (fst (fst (fst l))) (snd (fst (fst l))) (snd (fst (snd l))).
  Proof. intros. rewrite fp12_mul_by_line_eq. reflexivity. Qed.

  (* ================================================================ *)
  (** ** The Miller loop with sparse line multiplications               *)
  (* ================================================================ *)

  (** The three coefficients of [Pairing.make_line]. *)
  Definition make_line_coeffs (lambda x_t y_t : Fp2) (x_p y_p : F) : Fp2 * Fp2 * Fp2 :=
    (fp2_sub (fp2_mul lambda x_t) y_t,
     P.fp2_neg p (P.fp2_mul_fp p lambda x_p),
     P.fp_to_fp2 p y_p).

  Lemma make_line_coeffs_eq : forall lambda x_t y_t x_p y_p,
    let '(b0, b1, b4) := make_line_coeffs lambda x_t y_t x_p y_p in
    line_of b0 b1 b4 = P.make_line p lambda x_t y_t x_p y_p.
  Proof. reflexivity. Qed.

  Definition mul_by_make_line (f : Fp12) (lambda x_t y_t : Fp2) (x_p y_p : F) : Fp12 :=
    let '(b0, b1, b4) := make_line_coeffs lambda x_t y_t x_p y_p in
    fp12_mul_by_line f b0 b1 b4.

  Lemma mul_by_make_line_eq : forall f lambda x_t y_t x_p y_p,
    mul_by_make_line f lambda x_t y_t x_p y_p =
    P.fp12_mul p f (P.make_line p lambda x_t y_t x_p y_p).
  Proof. intros. cbv [mul_by_make_line make_line_coeffs]. apply fp12_mul_by_line_eq. Qed.

  (** [Pairing.miller_loop_step] with [mul_by_make_line] for [fp12_mul _ (make_line ..)]. *)
  Definition miller_loop_step_sparse (q_x q_y : Fp2) (x_p y_p : F)
    (state : Fp12 * (Fp2 * Fp2)) (bit : bool) : Fp12 * (Fp2 * Fp2) :=
    let '(f, (t_x, t_y)) := state in
    let x_t_sq := P.fp2_sqr p t_x in
    let three_x_t_sq := fp2_add (fp2_add x_t_sq x_t_sq) x_t_sq in
    let two_y_t := fp2_add t_y t_y in
    let lambda_d := fp2_mul three_x_t_sq (P.fp2_inv p two_y_t) in
    let f' := mul_by_make_line (P.fp12_sqr p f) lambda_d t_x t_y x_p y_p in
    let '(new_t_x, new_t_y) := P.ec2_double_with_lambda p t_x t_y lambda_d in
    if bit then
      let lambda_a := fp2_mul (fp2_sub q_y new_t_y) (P.fp2_inv p (fp2_sub q_x new_t_x)) in
      let f'' := mul_by_make_line f' lambda_a new_t_x new_t_y x_p y_p in
      let '(add_t_x, add_t_y) := P.ec2_add_with_lambda p new_t_x new_t_y q_x lambda_a in
      (f'', (add_t_x, add_t_y))
    else
      (f', (new_t_x, new_t_y)).

  Definition miller_loop_sparse (P0 : P.G1Affine p) (Q0 : P.G2Affine p) : Fp12 :=
    if (P.g1_infinity p P0 || P.g2_infinity p Q0)%bool then
      P.fp12_one p
    else
      fst (fold_left
             (miller_loop_step_sparse (P.g2_x p Q0) (P.g2_y p Q0) (P.g1_x p P0) (P.g1_y p P0))
             P.bls_x_bits
             (P.fp12_one p, (P.g2_x p Q0, P.g2_y p Q0))).

  Lemma miller_loop_step_sparse_eq : forall q_x q_y x_p y_p st bit,
    miller_loop_step_sparse q_x q_y x_p y_p st bit = P.miller_loop_step p q_x q_y x_p y_p st bit.
  Proof.
    intros q_x q_y x_p y_p [f [t_x t_y]] bit.
    cbv [miller_loop_step_sparse P.miller_loop_step].
    rewrite !mul_by_make_line_eq.
    destruct (P.ec2_double_with_lambda p t_x t_y _) as [nx ny].
    destruct bit; [| reflexivity].
    rewrite !mul_by_make_line_eq.
    reflexivity.
  Qed.

  Lemma fold_left_ext {A B} (g h : A -> B -> A) (l : list B) :
    (forall a b, g a b = h a b) -> forall a, fold_left g l a = fold_left h l a.
  Proof.
    intros H. induction l as [|b l IH]; intros a; cbn [fold_left]; [reflexivity |].
    rewrite H. apply IH.
  Qed.

  Theorem miller_loop_sparse_eq : forall P0 Q0,
    miller_loop_sparse P0 Q0 = P.miller_loop p P0 Q0.
  Proof.
    intros P0 Q0. cbv [miller_loop_sparse P.miller_loop].
    destruct (P.g1_infinity p P0 || P.g2_infinity p Q0)%bool; [reflexivity |].
    refine (f_equal fst (fold_left_ext _ _ _ _ _)).
    intros. apply miller_loop_step_sparse_eq.
  Qed.

End SparseLine.
