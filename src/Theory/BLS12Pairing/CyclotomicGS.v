(** * Granger-Scott cyclotomic squaring for the tower of Pairing.v.

    Granger and Scott (PKC 2010, "Faster squaring in the cyclotomic subgroup of sixth degree
    extensions"), in the form of blst's [cyclotomic_sqr_fp12]: view
    Fp12 = Fp4[s]/(s^3 - t) with s = w, t = w^3 = v w and Fp4 = Fp2[t]/(t^2 - xi), so that
      f = g0 + g1 s + g2 s^2,   g0 = (c0.c0, c1.c1), g1 = (c1.c0, c0.c2), g2 = (c0.c1, c1.c2).
    On the subgroup of order p^4 - p^2 + 1 the square is
      f^2 = (3 g0^2 - 2 conj g0) + (3 t g2^2 + 2 conj g1) s + (3 g1^2 - 2 conj g2) s^2
    (conj: t -> -t): three Fp4 squarings, nine Fp2 squarings in all.

    - [fp12_cyclotomic_square]: that chain, step for step as the bedrock2 function
      [bls12_Fp12_cyclotomic_square] computes it ([CycSqrAF.af_cyc_sqr_gallina]).
    - [fp12_cyc_adj]: the adjugate of f over Fp4 (f * adj f lies in Fp4); the squaring
      identity [cyclotomic_square_adj] (a ring identity, any p):
        fp12_cyclotomic_square f = f^2 + 2 (adj f - conj f),
      so [cyclotomic_square_eq]: adj f = conj f -> fp12_cyclotomic_square f = fp12_sqr f.

    For BLS12-381 (p = p381, the Frobenius constants of Frob381.v):
    - [gs f]: sigma f * sigma (sigma f) = conj f, sigma = the p^4-power map (pw f (p^4)).
      It holds on the subgroup of order p^4 - p^2 + 1, and:
    - [gs_adj]: gs f -> adj f = conj f, from [sigma_adj] (sigma f sigma^2 f = adj f for every f:
      sigma multiplies the coefficient of w^j by omega^j, omega a primitive cube root of unity;
      a computation with the constants), hence [gs_cyclotomic_square];
    - closure: [gs_one], [gs_mul], [gs_conj], [gs_pw], [gs_frob], [gs_frob2],
      [gs_pow_bls_x_signed], [gs_pow_bls_c_signed];
    - [gs_easy_part]: the output of the easy part of the final exponentiation is in gs
      (from frob_p2^3 = conj, [frob2_cubed], and the unitarity of conj f / f);
    - the hard part with cyclotomic squarings, [final_exp_hard_dsd_cyc], equals
      [Pairing.final_exp_hard_dsd] on gs ([final_exp_hard_dsd_cyc_eq]), and
      [final_exponentiation_dsd_cyc] equals [Pairing.final_exponentiation] for invertible f
      ([final_exponentiation_dsd_cyc_correct]).
*)

From Stdlib Require Import ZArith NArith BinPos List Lia.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Theory.BLS12Pairing.Pairing.
Require Import Theory.BLS12Pairing.Fp12Ring.
Require Import Theory.BLS12Pairing.Cyclotomic.
Require Import Theory.BLS12Pairing.CycExpModel.
Require Import Theory.BLS12Pairing.Frobenius.
Require Import Theory.BLS12Pairing.Prime381.
Require Import Theory.BLS12Pairing.FinalExpFunctional.
Require Import Theory.BLS12Pairing.Frob381.
Module P := Theory.BLS12Pairing.Pairing.

(** [pw] iterates multiplication: never let conversion unfold it on a 381-bit exponent. *)
Local Opaque Fp12Ring.pw.

(* ================================================================ *)
(** ** The squaring chain and the adjugate (any p)                   *)
(* ================================================================ *)

(** Split an Fp12 equality into its six Fp2 coefficients. *)
Local Ltac split12 :=
  apply injective_projections; cbn [fst snd];
  (apply injective_projections; cbn [fst snd]; [apply injective_projections; cbn [fst snd] |]).

Section GS.
  Context {p : positive}.

  Local Notation F := (F p).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  Add Ring Fp_ring : (@Fp_ring_theory p).
  Add Ring fp2_ring : (@fp2_ring_theory p).
  Add Ring fp6_ring : (@fp6_ring_theory p).
  Add Ring fp12_ring : (@fp12_ring_theory p).

  Local Notation fp2_add := (P.fp2_add p).
  Local Notation fp2_sub := (P.fp2_sub p).
  Local Notation fp2_mul := (P.fp2_mul p).
  Local Notation fp2_neg := (P.fp2_neg p).
  Local Notation mul_xi := (P.fp2_mul_xi p).
  Local Notation fp12_add := (P.fp12_add p).
  Local Notation fp12_sub := (P.fp12_sub p).
  Local Notation fp12_mul := (P.fp12_mul p).
  Local Notation conj := (P.fp12_conjugate p).

  (** The chain on the six Fp2 coefficients in memory order
      x0 = c0.c0, x1 = c0.c1, x2 = c0.c2, x3 = c1.c0, x4 = c1.c1, x5 = c1.c2, written in place
      as the bedrock2 function does: g0 = (x0, x4), g1 = (x3, x2), g2 = (x1, x5). *)
  Definition cyc_sqr6 (x0 x1 x2 x3 x4 x5 : Fp2) : Fp12 :=
    (* g0^2 = (t0, t2) *)
    let t0 := fp2_mul x0 x0 in
    let t1 := fp2_mul x4 x4 in
    let t2 := fp2_add x0 x4 in
    let t2 := fp2_mul t2 t2 in
    let t2 := fp2_sub t2 t0 in
    let t2 := fp2_sub t2 t1 in
    let t1 := mul_xi t1 in
    let t0 := fp2_add t0 t1 in
    (* g1^2 = (t3, t5) *)
    let t3 := fp2_mul x3 x3 in
    let t4 := fp2_mul x2 x2 in
    let t5 := fp2_add x3 x2 in
    let t5 := fp2_mul t5 t5 in
    let t5 := fp2_sub t5 t3 in
    let t5 := fp2_sub t5 t4 in
    let t4 := mul_xi t4 in
    let t3 := fp2_add t3 t4 in
    (* g2^2 = (t1, t6) *)
    let t1 := fp2_mul x1 x1 in
    let t4 := fp2_mul x5 x5 in
    let t6 := fp2_add x1 x5 in
    let t6 := fp2_mul t6 t6 in
    let t6 := fp2_sub t6 t1 in
    let t6 := fp2_sub t6 t4 in
    let t4 := mul_xi t4 in
    let t1 := fp2_add t1 t4 in
    (* new g0 = 3 g0^2 - 2 conj g0 *)
    let x0 := fp2_sub t0 x0 in let x0 := fp2_add x0 x0 in let x0 := fp2_add x0 t0 in
    let x4 := fp2_add t2 x4 in let x4 := fp2_add x4 x4 in let x4 := fp2_add x4 t2 in
    (* new g2 = 3 g1^2 - 2 conj g2 *)
    let x1 := fp2_sub t3 x1 in let x1 := fp2_add x1 x1 in let x1 := fp2_add x1 t3 in
    let x5 := fp2_add t5 x5 in let x5 := fp2_add x5 x5 in let x5 := fp2_add x5 t5 in
    (* new g1 = 3 t g2^2 + 2 conj g1 *)
    let t6 := mul_xi t6 in
    let x3 := fp2_add t6 x3 in let x3 := fp2_add x3 x3 in let x3 := fp2_add x3 t6 in
    let x2 := fp2_sub t1 x2 in let x2 := fp2_add x2 x2 in let x2 := fp2_add x2 t1 in
    ((x0, x1, x2), (x3, x4, x5)).

  Definition fp12_cyclotomic_square (f : Fp12) : Fp12 :=
    let '((x0, x1, x2), (x3, x4, x5)) := f in cyc_sqr6 x0 x1 x2 x3 x4 x5.

  (** The adjugate over Fp4, coefficient of w^k (A_j = coefficient of w^j:
      A0 = c0.c0, A1 = c1.c0, A2 = c0.c1, A3 = c1.c1, A4 = c0.c2, A5 = c1.c2). *)
  Definition fp12_cyc_adj (f : Fp12) : Fp12 :=
    let '((A0, A2, A4), (A1, A3, A5)) := f in
    let two x := fp2_add x x in
    let d0 := fp2_add (fp2_mul A0 A0)
                (mul_xi (fp2_sub (fp2_sub (fp2_mul A3 A3) (fp2_mul A1 A5)) (fp2_mul A2 A4))) in
    let d1 := fp2_add (fp2_neg (fp2_mul A0 A1))
                (mul_xi (fp2_sub (two (fp2_mul A2 A5)) (fp2_mul A3 A4))) in
    let d2 := fp2_add (fp2_sub (fp2_mul A1 A1) (fp2_mul A0 A2))
                (mul_xi (fp2_sub (fp2_mul A4 A4) (fp2_mul A3 A5))) in
    let d3 := fp2_sub (fp2_sub (two (fp2_mul A0 A3)) (fp2_mul A1 A2)) (mul_xi (fp2_mul A4 A5)) in
    let d4 := fp2_add (fp2_sub (fp2_sub (fp2_mul A2 A2) (fp2_mul A0 A4)) (fp2_mul A1 A3))
                (mul_xi (fp2_mul A5 A5)) in
    let d5 := fp2_sub (fp2_sub (two (fp2_mul A1 A4)) (fp2_mul A0 A5)) (fp2_mul A2 A3) in
    ((d0, d2, d4), (d1, d3, d5)).

  Lemma cyclotomic_square_adj : forall f,
    fp12_cyclotomic_square f =
    fp12_add (fp12_mul f f)
      (fp12_add (fp12_sub (fp12_cyc_adj f) (conj f)) (fp12_sub (fp12_cyc_adj f) (conj f))).
  Proof.
    intros [[[x0 x1] x2] [[x3 x4] x5]].
    cbv [fp12_cyclotomic_square cyc_sqr6 fp12_cyc_adj
         P.fp12_add P.fp12_sub P.fp12_mul P.fp12_conjugate P.fp12_build P.fp12_c0 P.fp12_c1
         P.fp6_add P.fp6_sub P.fp6_neg P.fp6_mul P.fp6_mul_by_v P.fp6_build
         P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
    rewrite !fp2_mul_xi_eq.
    split12; ring.
  Qed.

  Lemma cyclotomic_square_eq : forall f, fp12_cyc_adj f = conj f ->
    fp12_cyclotomic_square f = P.fp12_sqr p f.
  Proof.
    intros f H. rewrite cyclotomic_square_adj, H, fp12_sqr_eq. ring.
  Qed.

  (** Coefficientwise product (both operands as coefficient vectors). *)
  Definition hadamard (d x : Fp12) : Fp12 :=
    let '((d0, d1, d2), (d3, d4, d5)) := d in
    let '((x0, x1, x2), (x3, x4, x5)) := x in
    ((fp2_mul d0 x0, fp2_mul d1 x1, fp2_mul d2 x2),
     (fp2_mul d3 x3, fp2_mul d4 x4, fp2_mul d5 x5)).

  Lemma hadamard_assoc : forall d e x, hadamard d (hadamard e x) = hadamard (hadamard d e) x.
  Proof.
    intros [[[? ?] ?] [[? ?] ?]] [[[? ?] ?] [[? ?] ?]] [[[? ?] ?] [[? ?] ?]].
    cbv [hadamard]. split12; ring.
  Qed.

  (** fp12_frobenius_p2 is the coefficientwise product by (1, g1, g2, c, g1 c, g2 c). *)
  Definition frob2_vec (g1 g2 c : Fp2) : Fp12 :=
    ((P.fp2_one p, g1, g2), (c, fp2_mul g1 c, fp2_mul g2 c)).

  Lemma frob2_hadamard : forall g1 g2 c x,
    P.fp12_frobenius_p2 p g1 g2 c x = hadamard (frob2_vec g1 g2 c) x.
  Proof.
    intros g1 g2 c [[[? ?] ?] [[? ?] ?]].
    cbv [P.fp12_frobenius_p2 P.fp6_frobenius_p2 P.fp6_mul_fp2 frob2_vec hadamard
         P.fp12_build P.fp12_c0 P.fp12_c1 P.fp6_build P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
    split12; ring.
  Qed.

  (** The product of two coefficientwise multiples of f, with the 21 cross coefficients
      [kk] (i < j) and [dd] (i = j) left as subterms (indices are powers of w). *)
  Definition kk (di ej dj ei : Fp2) : Fp2 := fp2_add (fp2_mul di ej) (fp2_mul dj ei).
  Definition dd (di ei : Fp2) : Fp2 := fp2_mul di ei.

  Definition prod_gen (d e f : Fp12) : Fp12 :=
    let '((D0, D2, D4), (D1, D3, D5)) := d in
    let '((E0, E2, E4), (E1, E3, E5)) := e in
    let '((A0, A2, A4), (A1, A3, A5)) := f in
    let m k a b := fp2_mul k (fp2_mul a b) in
    let r0 := fp2_add (m (dd D0 E0) A0 A0)
                (mul_xi (fp2_add (fp2_add (m (kk D1 E5 D5 E1) A1 A5) (m (kk D2 E4 D4 E2) A2 A4))
                                 (m (dd D3 E3) A3 A3))) in
    let r1 := fp2_add (m (kk D0 E1 D1 E0) A0 A1)
                (mul_xi (fp2_add (m (kk D2 E5 D5 E2) A2 A5) (m (kk D3 E4 D4 E3) A3 A4))) in
    let r2 := fp2_add (fp2_add (m (kk D0 E2 D2 E0) A0 A2) (m (dd D1 E1) A1 A1))
                (mul_xi (fp2_add (m (kk D3 E5 D5 E3) A3 A5) (m (dd D4 E4) A4 A4))) in
    let r3 := fp2_add (fp2_add (m (kk D0 E3 D3 E0) A0 A3) (m (kk D1 E2 D2 E1) A1 A2))
                (mul_xi (m (kk D4 E5 D5 E4) A4 A5)) in
    let r4 := fp2_add (fp2_add (fp2_add (m (kk D0 E4 D4 E0) A0 A4) (m (kk D1 E3 D3 E1) A1 A3))
                               (m (dd D2 E2) A2 A2))
                (mul_xi (m (dd D5 E5) A5 A5)) in
    let r5 := fp2_add (fp2_add (m (kk D0 E5 D5 E0) A0 A5) (m (kk D1 E4 D4 E1) A1 A4))
                (m (kk D2 E3 D3 E2) A2 A3) in
    ((r0, r2, r4), (r1, r3, r5)).

  Lemma prod_hadamard : forall d e f,
    fp12_mul (hadamard d f) (hadamard e f) = prod_gen d e f.
  Proof.
    intros [[[? ?] ?] [[? ?] ?]] [[[? ?] ?] [[? ?] ?]] [[[? ?] ?] [[? ?] ?]].
    cbv [prod_gen kk dd hadamard
         P.fp12_mul P.fp12_build P.fp12_c0 P.fp12_c1
         P.fp6_add P.fp6_sub P.fp6_mul P.fp6_mul_by_v P.fp6_build
         P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
    rewrite !fp2_mul_xi_eq.
    split12; ring.
  Qed.

  (** With the coefficients of sigma and sigma^2 (omega^j and omega^(2j), omega^3 = 1,
      1 + omega + omega^2 = 0): dd = 1, kk = 2 for j = i + 3 and -1 otherwise. *)
  Lemma prod_gen_adj : forall d e f,
    let one := P.fp2_one p in let two := fp2_add one one in let m1 := fp2_neg one in
    let '((D0, D2, D4), (D1, D3, D5)) := d in
    let '((E0, E2, E4), (E1, E3, E5)) := e in
    dd D0 E0 = one -> dd D1 E1 = one -> dd D2 E2 = one ->
    dd D3 E3 = one -> dd D4 E4 = one -> dd D5 E5 = one ->
    kk D0 E3 D3 E0 = two -> kk D1 E4 D4 E1 = two -> kk D2 E5 D5 E2 = two ->
    kk D0 E1 D1 E0 = m1 -> kk D0 E2 D2 E0 = m1 -> kk D0 E4 D4 E0 = m1 -> kk D0 E5 D5 E0 = m1 ->
    kk D1 E2 D2 E1 = m1 -> kk D1 E3 D3 E1 = m1 -> kk D1 E5 D5 E1 = m1 ->
    kk D2 E3 D3 E2 = m1 -> kk D2 E4 D4 E2 = m1 ->
    kk D3 E4 D4 E3 = m1 -> kk D3 E5 D5 E3 = m1 ->
    kk D4 E5 D5 E4 = m1 ->
    prod_gen d e f = fp12_cyc_adj f.
  Proof.
    intros [[[D0 D2] D4] [[D1 D3] D5]] [[[E0 E2] E4] [[E1 E3] E5]] f.
    cbv zeta. intros.
    destruct f as [[[A0 A2] A4] [[A1 A3] A5]].
    cbv [prod_gen fp12_cyc_adj].
    repeat match goal with H : kk _ _ _ _ = _ |- _ => rewrite H; clear H end.
    repeat match goal with H : dd _ _ = _ |- _ => rewrite H; clear H end.
    rewrite !fp2_mul_xi_eq.
    split12; ring.
  Qed.

End GS.

(* ================================================================ *)
(** ** BLS12-381                                                     *)
(* ================================================================ *)

Section GS381.
  Local Notation p := p381.
  Local Notation F := (F p381).
  Local Notation Fp2 := (F * F)%type.
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.
  Local Notation Fp12 := (Fp6 * Fp6)%type.
  Local Open Scope Z_scope.

  Add Ring Fp_ring381 : (@Fp_ring_theory p381).
  Add Ring fp2_ring381 : (@fp2_ring_theory p381).
  Add Ring fp6_ring381 : (@fp6_ring_theory p381).
  Add Ring fp12_ring381 : (@fp12_ring_theory p381).

  Local Notation fp12_mul := (P.fp12_mul p).
  Local Notation fp12_one := (P.fp12_one p).
  Local Notation conj := (P.fp12_conjugate p).
  Local Notation pw := (@pw p).
  Local Notation frob := (P.fp12_frobenius p gamma1_381 gamma2_381 c1_381).
  Local Notation frob2 := (P.fp12_frobenius_p2 p gamma1_p2_381 gamma2_p2_381 c1_p2_381).

  (** ** The constants as Z pairs *)

  Definition zadd2 (a b : Z * Z) : Z * Z :=
    ((fst a + fst b) mod Z.pos p, (snd a + snd b) mod Z.pos p).

  Lemma fp2_ofZ_add : forall a b, fp2_ofZ (zadd2 a b) = P.fp2_add p (fp2_ofZ a) (fp2_ofZ b).
  Proof.
    intros [a0 a1] [b0 b1]. cbv [fp2_ofZ zadd2 P.fp2_add fst snd].
    rewrite <- !F.of_Z_mod.
    pose proof (F.ring_morph p) as M.
    rewrite !(Ring_theory.morph_add M).
    reflexivity.
  Qed.

  Lemma fp2_one_ofZ : P.fp2_one p = fp2_ofZ (1, 0).
  Proof. reflexivity. Qed.

  Lemma fp2_ofZ_two : fp2_ofZ (2, 0) = P.fp2_add p (P.fp2_one p) (P.fp2_one p).
  Proof. rewrite fp2_one_ofZ, <- fp2_ofZ_add. reflexivity. Qed.

  Lemma fp2_ofZ_m1 : fp2_ofZ (Z.pos p - 1, 0) = P.fp2_neg p (P.fp2_one p).
  Proof.
    cbv [fp2_ofZ P.fp2_neg P.fp2_one fst snd].
    f_equal; apply F.eq_to_Z_iff; vm_compute; reflexivity.
  Qed.

  (** The vector of [frob2] in Z. *)
  Definition frob2_vecZ : (Z * Z) * (Z * Z) * (Z * Z) * ((Z * Z) * (Z * Z) * (Z * Z)) :=
    ((1, 0), gamma1_p2_381_Z, gamma2_p2_381_Z,
     (c1_p2_381_Z, zmul2 gamma1_p2_381_Z c1_p2_381_Z, zmul2 gamma2_p2_381_Z c1_p2_381_Z)).

  Definition fp12_ofZ (z : (Z * Z) * (Z * Z) * (Z * Z) * ((Z * Z) * (Z * Z) * (Z * Z))) : Fp12 :=
    let '((z0, z1, z2), (z3, z4, z5)) := z in
    ((fp2_ofZ z0, fp2_ofZ z1, fp2_ofZ z2), (fp2_ofZ z3, fp2_ofZ z4, fp2_ofZ z5)).

  Definition hadamardZ (d e : (Z * Z) * (Z * Z) * (Z * Z) * ((Z * Z) * (Z * Z) * (Z * Z))) :=
    let '((d0, d1, d2), (d3, d4, d5)) := d in
    let '((e0, e1, e2), (e3, e4, e5)) := e in
    ((zmul2 d0 e0, zmul2 d1 e1, zmul2 d2 e2), (zmul2 d3 e3, zmul2 d4 e4, zmul2 d5 e5)).

  Lemma hadamard_ofZ : forall d e,
    hadamard (fp12_ofZ d) (fp12_ofZ e) = fp12_ofZ (hadamardZ d e).
  Proof.
    intros [[[? ?] ?] [[? ?] ?]] [[[? ?] ?] [[? ?] ?]].
    cbv [hadamard hadamardZ fp12_ofZ]. rewrite !fp2_ofZ_mul. reflexivity.
  Qed.

  Lemma frob2_vec_ofZ : frob2_vec gamma1_p2_381 gamma2_p2_381 c1_p2_381 = fp12_ofZ frob2_vecZ.
  Proof.
    cbv [frob2_vec frob2_vecZ fp12_ofZ gamma1_p2_381 gamma2_p2_381 c1_p2_381].
    rewrite !fp2_ofZ_mul. reflexivity.
  Qed.

  Lemma frob2_ofZ : forall x, frob2 x = hadamard (fp12_ofZ frob2_vecZ) x.
  Proof. intros x. rewrite frob2_hadamard, frob2_vec_ofZ. reflexivity. Qed.

  Definition L2Z := Eval vm_compute in hadamardZ frob2_vecZ frob2_vecZ.
  Definition L3Z := Eval vm_compute in hadamardZ frob2_vecZ L2Z.
  Definition L4Z := Eval vm_compute in hadamardZ L2Z L2Z.

  Lemma frob2_2 : forall x, frob2 (frob2 x) = hadamard (fp12_ofZ L2Z) x.
  Proof.
    intros x. rewrite !frob2_ofZ, hadamard_assoc, hadamard_ofZ. reflexivity.
  Qed.

  Lemma frob2_3 : forall x, frob2 (frob2 (frob2 x)) = hadamard (fp12_ofZ L3Z) x.
  Proof.
    intros x. rewrite frob2_2, frob2_ofZ, hadamard_assoc, hadamard_ofZ. reflexivity.
  Qed.

  Lemma frob2_4 : forall x, frob2 (frob2 (frob2 (frob2 x))) = hadamard (fp12_ofZ L4Z) x.
  Proof.
    intros x. rewrite !frob2_2, hadamard_assoc, hadamard_ofZ. reflexivity.
  Qed.

  (** frob_p2^3 is the conjugation (the p^6-power map). *)
  Lemma frob2_cubed : forall x, frob2 (frob2 (frob2 x)) = conj x.
  Proof.
    intros x. rewrite frob2_3.
    change L3Z with ((1, 0), (1, 0), (1, 0), ((Z.pos p - 1, 0), (Z.pos p - 1, 0), (Z.pos p - 1, 0))).
    cbv [fp12_ofZ]. rewrite fp2_ofZ_m1, <- fp2_one_ofZ.
    destruct x as [[[? ?] ?] [[? ?] ?]].
    cbv [hadamard P.fp12_conjugate P.fp12_build P.fp12_c0 P.fp12_c1 P.fp6_neg P.fp6_build
         P.fp6_c0 P.fp6_c1 P.fp6_c2 fst snd].
    split12; ring.
  Qed.

  (** sigma = frob_p2^2 = p^4-power; sigma f * sigma^2 f is the adjugate. *)
  Lemma frob2_adj : forall x,
    fp12_mul (frob2 (frob2 x)) (frob2 (frob2 (frob2 (frob2 x)))) = fp12_cyc_adj x.
  Proof.
    intros x. rewrite frob2_4, frob2_2, prod_hadamard.
    pose proof (@prod_gen_adj p (fp12_ofZ L2Z) (fp12_ofZ L4Z) x) as H.
    cbv [L2Z L4Z fp12_ofZ] in H |- *.
    apply H; clear H;
      cbv [kk dd]; rewrite <- ?fp2_ofZ_mul; rewrite <- ?fp2_ofZ_add;
      rewrite <- ?fp2_ofZ_m1; rewrite ?fp2_one_ofZ; rewrite <- ?fp2_ofZ_add;
      f_equal; vm_compute; reflexivity.
  Qed.

  (** ** The predicate gs *)

  Definition p4 : positive := (p * p * (p * p))%positive.
  Definition sigma (x : Fp12) : Fp12 := pw x (Npos p4).

  Definition gs (x : Fp12) : Prop := fp12_mul (sigma x) (sigma (sigma x)) = conj x.

  Lemma sigma_frob2 : forall x, sigma x = frob2 (frob2 x).
  Proof.
    intros x. cbv [sigma p4]. rewrite !frobenius_p2_381_is_pow, <- pw_mul. reflexivity.
  Qed.

  Lemma sigma_adj : forall x, fp12_mul (sigma x) (sigma (sigma x)) = fp12_cyc_adj x.
  Proof. intros x. rewrite !sigma_frob2. exact (frob2_adj x). Qed.

  Lemma gs_adj : forall x, gs x -> fp12_cyc_adj x = conj x.
  Proof. intros x H. cbv [gs] in H. rewrite <- sigma_adj. exact H. Qed.

  Theorem gs_cyclotomic_square : forall x, gs x -> fp12_cyclotomic_square x = P.fp12_sqr p x.
  Proof. intros x H. apply cyclotomic_square_eq, gs_adj, H. Qed.

  (** ** Closure *)

  Lemma sigma_mul : forall x y, sigma (fp12_mul x y) = fp12_mul (sigma x) (sigma y).
  Proof. intros. cbv [sigma]. exact (pw_mul_base x y (Npos p4)). Qed.

  Lemma sigma_conj : forall x, sigma (conj x) = conj (sigma x).
  Proof. intros. cbv [sigma]. rewrite pw_conj. reflexivity. Qed.

  Lemma sigma_one : sigma fp12_one = fp12_one.
  Proof. cbv [sigma]. exact (pw_one (Npos p4)). Qed.

  Lemma sigma_pw : forall x n, sigma (pw x n) = pw (sigma x) n.
  Proof. intros. cbv [sigma]. rewrite <- !pw_mul, N.mul_comm. reflexivity. Qed.

  Lemma gs_one : gs fp12_one.
  Proof. cbv [gs]. rewrite !sigma_one, conj_one. ring. Qed.

  Lemma gs_mul : forall x y, gs x -> gs y -> gs (fp12_mul x y).
  Proof.
    cbv [gs]. intros x y Hx Hy. rewrite !sigma_mul, conj_mul, <- Hx, <- Hy. ring.
  Qed.

  Lemma gs_conj : forall x, gs x -> gs (conj x).
  Proof.
    cbv [gs]. intros x Hx. rewrite !sigma_conj, <- conj_mul, Hx. reflexivity.
  Qed.

  Lemma gs_pw : forall x n, gs x -> gs (pw x n).
  Proof.
    intros x n Hx. induction n using N.peano_ind.
    - rewrite pw_0. exact gs_one.
    - rewrite pw_succ. apply gs_mul; assumption.
  Qed.

  Lemma gs_frob : forall x, gs x -> gs (frob x).
  Proof. intros x Hx. rewrite frobenius_381_is_pow. apply gs_pw, Hx. Qed.

  Lemma gs_frob2 : forall x, gs x -> gs (frob2 x).
  Proof. intros x Hx. rewrite frobenius_p2_381_is_pow. apply gs_pw, Hx. Qed.

  Lemma gs_pow_bls_x_signed : forall x, gs x -> gs (P.fp12_pow_bls_x_signed p x).
  Proof. intros x Hx. rewrite pow_bls_x_signed_pw. apply gs_conj, gs_pw, Hx. Qed.

  Lemma gs_pow_bls_c_signed : forall x, gs x -> gs (P.fp12_pow_bls_c_signed p x).
  Proof. intros x Hx. rewrite pow_bls_c_signed_pw. apply gs_conj, gs_pw, Hx. Qed.

  (** ** The easy part lands in gs *)

  Lemma frob2_mul : forall x y, frob2 (fp12_mul x y) = fp12_mul (frob2 x) (frob2 y).
  Proof. intros. rewrite !frobenius_p2_381_is_pow. exact (pw_mul_base x y _). Qed.

  Lemma frob2_one : frob2 fp12_one = fp12_one.
  Proof. rewrite frobenius_p2_381_is_pow. exact (pw_one _). Qed.

  Lemma frob2_conj : forall x, frob2 (conj x) = conj (frob2 x).
  Proof. intros. rewrite !frobenius_p2_381_is_pow, pw_conj. reflexivity. Qed.

  (** For a unitary g, m = frob2 g * g satisfies m * sigma m * sigma^2 m = 1:
      the product of the six conjugates frob2^k g, k = 0..5, grouped as g * conj g and
      its images under frob2 and frob2^2 (frob2^3 = conj). *)
  Lemma gs_frob2_mul_unitary : forall g,
    fp12_mul g (conj g) = fp12_one -> cyclotomic (fp12_mul (frob2 g) g) ->
    gs (fp12_mul (frob2 g) g).
  Proof.
    intros g Hg Hm. cbv [gs]. rewrite !sigma_frob2.
    set (m := fp12_mul (frob2 g) g) in *.
    assert (Hprod : fp12_mul m (fp12_mul (frob2 (frob2 m)) (frob2 (frob2 (frob2 (frob2 m)))))
                    = fp12_one).
    { subst m. rewrite !frob2_mul, !frob2_cubed, !frob2_conj, ?frob2_cubed, ?conj_conj.
      transitivity (fp12_mul (fp12_mul g (conj g))
                     (fp12_mul (frob2 (fp12_mul g (conj g)))
                               (frob2 (frob2 (fp12_mul g (conj g)))))).
      - rewrite !frob2_mul, !frob2_conj. ring.
      - rewrite Hg, !frob2_one. ring. }
    cbv [cyclotomic] in Hm. fold m in Hm.
    transitivity (fp12_mul (fp12_mul m (conj m))
                    (fp12_mul (frob2 (frob2 m)) (frob2 (frob2 (frob2 (frob2 m)))))).
    - rewrite Hm. ring.
    - transitivity (fp12_mul (conj m)
                      (fp12_mul m (fp12_mul (frob2 (frob2 m)) (frob2 (frob2 (frob2 (frob2 m))))))).
      + ring.
      + rewrite Hprod. ring.
  Qed.

  Theorem gs_easy_part : forall f, fp12_mul f (P.fp12_inv p f) = fp12_one ->
    gs (easy_part gamma1_p2_381 gamma2_p2_381 c1_p2_381 f).
  Proof.
    intros f Hf.
    pose proof (easy_part_cyclotomic p381_prime p381_mod4 p381_mod3 _ _ _
                  H381_gamma2_p2 H381_gamma1_p2 H381_c1_p2 f Hf) as Hm.
    assert (Hg : cyclotomic (fp12_mul (conj f) (P.fp12_inv p f))).
    { eapply cyc_easy_first. all: first [exact Hf | exact p381_prime | exact p381_mod4
                                        | exact p381_mod3]. }
    cbv [easy_part] in *.
    apply gs_frob2_mul_unitary; [exact Hg | exact Hm].
  Qed.

  (** ** The square-and-multiply step with the cyclotomic square *)

  Lemma gs_cyclotomic_square_pw : forall B n, gs B ->
    fp12_cyclotomic_square (pw B n) = pw B (2 * n).
  Proof.
    intros B n HB. rewrite gs_cyclotomic_square by (apply gs_pw, HB).
    rewrite fp12_sqr_eq, <- pw_add. f_equal. lia.
  Qed.

  (** One iteration of the loop of [BLS12_Pairing.cyc_exp_neg_fn] (MSB first), as
      [CycExpModel.cyc_exp_step] with the Granger-Scott square. *)
  Lemma gs_cyc_exp_step : forall B (e : Z) (k : nat), 0 <= e -> gs B ->
    (if Z.testbit e (Z.of_nat k)
     then fp12_mul (fp12_cyclotomic_square (pw B (Z.to_N (Z.shiftr e (Z.of_nat (S k)))))) B
     else fp12_cyclotomic_square (pw B (Z.to_N (Z.shiftr e (Z.of_nat (S k))))))
    = pw B (Z.to_N (Z.shiftr e (Z.of_nat k))).
  Proof.
    intros B e k He HB.
    rewrite (shiftr_step e k He), gs_cyclotomic_square_pw by exact HB.
    destruct (Z.testbit e (Z.of_nat k)).
    - rewrite pw_add, pw_1. ring.
    - rewrite N.add_0_r. reflexivity.
  Qed.

  (** ** The hard part with cyclotomic squarings *)

  Fixpoint fp12_pow_bits_cyc_aux (base : Fp12) (bits : list bool)
    (acc : Fp12) (started : bool) : Fp12 :=
    match bits with
    | [] => acc
    | b :: rest =>
      let acc' := if started then fp12_cyclotomic_square acc else acc in
      if b then
        let acc'' := if started then fp12_mul acc' base else base in
        fp12_pow_bits_cyc_aux base rest acc'' true
      else
        fp12_pow_bits_cyc_aux base rest acc' started
    end.

  Definition fp12_pow_Z_cyc (base : Fp12) (exp : Z) (width : nat) : Fp12 :=
    fp12_pow_bits_cyc_aux base (P.Z_to_bits width exp) fp12_one false.

  Definition fp12_pow_bls_x_signed_cyc (f : Fp12) : Fp12 := conj (fp12_pow_Z_cyc f P.bls_x 64).
  Definition fp12_pow_bls_c_signed_cyc (f : Fp12) : Fp12 := conj (fp12_pow_Z_cyc f P.bls_c 63).

  Lemma pow_bits_cyc_aux_eq : forall base bits acc started, gs base -> gs acc ->
    fp12_pow_bits_cyc_aux base bits acc started = P.fp12_pow_bits_aux p base bits acc started.
  Proof.
    intros base bits. induction bits as [|b rest IH]; intros acc started Hb Ha; [reflexivity |].
    cbn [fp12_pow_bits_cyc_aux P.fp12_pow_bits_aux].
    assert (Hsq : (if started then fp12_cyclotomic_square acc else acc)
                  = (if started then P.fp12_sqr p acc else acc)).
    { destruct started; [apply gs_cyclotomic_square, Ha | reflexivity]. }
    assert (Ha' : gs (if started then P.fp12_sqr p acc else acc)).
    { destruct started; [rewrite fp12_sqr_eq; apply gs_mul; assumption | exact Ha]. }
    rewrite Hsq.
    destruct b; apply IH; try assumption.
    destruct started; [apply gs_mul; assumption | exact Hb].
  Qed.

  Lemma pow_Z_cyc_eq : forall base e w, gs base ->
    fp12_pow_Z_cyc base e w = P.fp12_pow_Z p base e w.
  Proof. intros. apply pow_bits_cyc_aux_eq; [assumption | exact gs_one]. Qed.

  Lemma pow_bls_x_signed_cyc_eq : forall f, gs f ->
    fp12_pow_bls_x_signed_cyc f = P.fp12_pow_bls_x_signed p f.
  Proof.
    intros f Hf. cbv [fp12_pow_bls_x_signed_cyc P.fp12_pow_bls_x_signed P.fp12_pow_bls_x].
    rewrite pow_Z_cyc_eq by exact Hf. reflexivity.
  Qed.

  Lemma pow_bls_c_signed_cyc_eq : forall f, gs f ->
    fp12_pow_bls_c_signed_cyc f = P.fp12_pow_bls_c_signed p f.
  Proof.
    intros f Hf. cbv [fp12_pow_bls_c_signed_cyc P.fp12_pow_bls_c_signed P.fp12_pow_bls_c].
    rewrite pow_Z_cyc_eq by exact Hf. reflexivity.
  Qed.

  (** [Pairing.final_exp_hard_dsd] with the exponentiations by -c and -|x| done with the
      cyclotomic square (what [bls12_final_exp_hard_dsd] computes). *)
  Definition final_exp_hard_dsd_cyc (g1p2 g2p2 c1p2 : Fp2) (f : Fp12) : Fp12 :=
    let t1 := fp12_pow_bls_c_signed_cyc f in
    let t2 := fp12_pow_bls_x_signed_cyc t1 in
    let t1 := conj t1 in
    let t1 := fp12_mul t1 t2 in
    let t2 := fp12_pow_bls_x_signed_cyc t1 in
    let t0 := frob t1 in
    let t1 := fp12_mul t0 t2 in
    let t0 := fp12_pow_bls_x_signed_cyc t1 in
    let t2 := fp12_pow_bls_x_signed_cyc t0 in
    let t0 := P.fp12_frobenius_p2 p g1p2 g2p2 c1p2 t1 in
    let t1 := conj t1 in
    let t1 := fp12_mul t1 t2 in
    let t1 := fp12_mul t1 t0 in
    fp12_mul f t1.

  Theorem final_exp_hard_dsd_cyc_eq : forall g1p2 g2p2 c1p2 f, gs f ->
    final_exp_hard_dsd_cyc g1p2 g2p2 c1p2 f =
    P.final_exp_hard_dsd p gamma1_381 gamma2_381 g1p2 g2p2 c1_381 c1p2 f.
  Proof.
    intros g1p2 g2p2 c1p2 f Hf.
    cbv beta zeta delta [final_exp_hard_dsd_cyc P.final_exp_hard_dsd].
    pose proof (gs_pow_bls_c_signed f Hf) as C1.
    rewrite (pow_bls_c_signed_cyc_eq f Hf).
    set (a1 := P.fp12_pow_bls_c_signed p f) in *.
    rewrite (pow_bls_x_signed_cyc_eq a1 C1).
    set (a2 := P.fp12_pow_bls_x_signed p a1).
    assert (C4 : gs (fp12_mul (conj a1) a2))
      by (apply gs_mul; [apply gs_conj, C1 | apply gs_pow_bls_x_signed, C1]).
    rewrite (pow_bls_x_signed_cyc_eq _ C4).
    set (a4 := fp12_mul (conj a1) a2) in *.
    assert (C7 : gs (fp12_mul (frob a4) (P.fp12_pow_bls_x_signed p a4)))
      by (apply gs_mul; [apply gs_frob, C4 | apply gs_pow_bls_x_signed, C4]).
    rewrite (pow_bls_x_signed_cyc_eq _ C7).
    set (a7 := fp12_mul (frob a4) (P.fp12_pow_bls_x_signed p a4)) in *.
    pose proof (gs_pow_bls_x_signed a7 C7) as C8.
    rewrite (pow_bls_x_signed_cyc_eq _ C8).
    reflexivity.
  Qed.

  Definition final_exponentiation_dsd_cyc (f : Fp12) : Fp12 :=
    let f_conj := conj f in
    let f_inv := P.fp12_inv p f in
    let result := fp12_mul f_conj f_inv in
    let result_p2 := frob2 result in
    let result' := fp12_mul result_p2 result in
    final_exp_hard_dsd_cyc gamma1_p2_381 gamma2_p2_381 c1_p2_381 result'.

  Theorem final_exponentiation_dsd_cyc_correct : forall f,
    fp12_mul f (P.fp12_inv p f) = fp12_one ->
    final_exponentiation_dsd_cyc f =
    P.final_exponentiation p gamma1_p2_381 gamma2_p2_381 c1_p2_381 f.
  Proof.
    intros f Hf.
    rewrite <- (final_exponentiation_dsd_381_correct f Hf).
    cbv beta zeta delta [final_exponentiation_dsd_cyc P.final_exponentiation_dsd].
    apply final_exp_hard_dsd_cyc_eq.
    exact (gs_easy_part f Hf).
  Qed.

  (** ** The side conditions of the hard part, one call at a time
      (the gs versions of [BLS12_FinalExpModel381.cyc_step_*] and [easy_cyc_381]). *)

  Lemma gs_step_cs (f a1 : Fp12) : gs f -> a1 = P.fp12_pow_bls_c_signed p f -> gs a1.
  Proof. intros Hf ->. apply gs_pow_bls_c_signed, Hf. Qed.

  Lemma gs_step_xs (a b : Fp12) : gs a -> b = P.fp12_pow_bls_x_signed p a -> gs b.
  Proof. intros Ha ->. apply gs_pow_bls_x_signed, Ha. Qed.

  Lemma gs_step_a4 (a1 a2 a3 a4 : Fp12) : gs a1 ->
    a2 = P.fp12_pow_bls_x_signed p a1 -> a3 = conj a1 -> a4 = fp12_mul a3 a2 -> gs a4.
  Proof.
    intros C1 -> -> ->. apply gs_mul; [apply gs_conj, C1 | apply gs_pow_bls_x_signed, C1].
  Qed.

  Lemma gs_step_a7 (a4 a5 a6 a7 : Fp12) : gs a4 ->
    a5 = P.fp12_pow_bls_x_signed p a4 -> a6 = frob a4 -> a7 = fp12_mul a6 a5 -> gs a7.
  Proof.
    intros C4 -> -> ->. apply gs_mul; [apply gs_frob, C4 | apply gs_pow_bls_x_signed, C4].
  Qed.

  Lemma easy_gs_381 (f b1 b2 b3 b4 b5 : Fp12) :
    fp12_mul f (P.fp12_inv p f) = fp12_one ->
    b1 = conj f -> b2 = P.fp12_inv p f -> b3 = fp12_mul b1 b2 ->
    b4 = frob2 b3 -> b5 = fp12_mul b4 b3 -> gs b5.
  Proof.
    intros Hinv E1 E2 E3 E4 E5. subst.
    exact (gs_easy_part f Hinv).
  Qed.

End GS381.
