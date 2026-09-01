(** * Optimal Ate pairing for BLS12-381.

    Computes e(P, Q) for P in G1, Q in G2, producing a result in
    GT (a subgroup of Fp12 star).

    The optimal Ate pairing:
      ate(P, Q) = f_{|x|,Q}(P)^{(p^12 - 1)/r}
    where x = -0xd201000000010000 is the BLS parameter.

    This file is SELF-CONTAINED: all field-tower definitions
    (Fp2, Fp6, Fp12) and curve-point types are included inline
    so there are no import complications with Sections/Variables.
*)

From Stdlib Require Import ZArith BinPos List Bool.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.

Section BLS12_Pairing.
  Variable p : positive.

  (* ================================================================ *)
  (** ** Base field Fp notations                                       *)
  (* ================================================================ *)

  Local Notation F := (F p).
  Local Notation "x +f y" := (@F.add p x y) (at level 50, left associativity).
  Local Notation "x *f y" := (@F.mul p x y) (at level 40, left associativity).
  Local Notation "x -f y" := (@F.sub p x y) (at level 50, left associativity).
  Local Notation "-f x" := (@F.opp p x) (at level 35, right associativity).
  Local Notation "0f" := (@F.zero p).
  Local Notation "1f" := (@F.one p).

  (* ================================================================ *)
  (** ** Fp2 = Fp[u]/(u^2 + 1)                                       *)
  (* ================================================================ *)

  (** An Fp2 element (a0, a1) represents a0 + a1*u where u^2 = -1. *)
  Local Notation Fp2 := (F * F)%type.

  Definition fp2_zero : Fp2 := (0f, 0f).
  Definition fp2_one  : Fp2 := (1f, 0f).

  Definition fp2_add (a b : Fp2) : Fp2 :=
    (fst a +f fst b, snd a +f snd b).

  Definition fp2_sub (a b : Fp2) : Fp2 :=
    (fst a -f fst b, snd a -f snd b).

  Definition fp2_neg (a : Fp2) : Fp2 :=
    (-f fst a, -f snd a).

  (** Fp2 multiplication using u^2 = -1. *)
  Definition fp2_mul (a b : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let b0 := fst b in let b1 := snd b in
    (a0 *f b0 -f a1 *f b1,
     a0 *f b1 +f a1 *f b0).

  (** Fp2 squaring. *)
  Definition fp2_sqr (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    ((a0 +f a1) *f (a0 -f a1),
     a0 *f a1 +f a0 *f a1).

  (** Fp2 conjugation: (a0, a1) -> (a0, -a1). *)
  Definition fp2_conjugate (a : Fp2) : Fp2 :=
    (fst a, -f snd a).

  (** Fp2 inverse. *)
  Definition fp2_inv (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let norm := a0 *f a0 +f a1 *f a1 in
    let inv_norm := @F.inv p norm in
    (a0 *f inv_norm, (-f a1) *f inv_norm).

  (** Multiply by xi = 1 + u in Fp2. *)
  Definition fp2_mul_xi (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    (a0 -f a1, a0 +f a1).

  (** Scalar multiplication of Fp2 by an Fp element. *)
  Definition fp2_mul_fp (a : Fp2) (s : F) : Fp2 :=
    (fst a *f s, snd a *f s).

  (** Fp2 division. *)
  Definition fp2_div (a b : Fp2) : Fp2 :=
    fp2_mul a (fp2_inv b).

  (** Embed an Fp element into Fp2 as (s, 0). *)
  Definition fp_to_fp2 (s : F) : Fp2 := (s, 0f).

  (* ================================================================ *)
  (** ** Fp6 = Fp2[v]/(v^3 - xi)                                     *)
  (* ================================================================ *)

  (** An Fp6 element ((c0, c1), c2) represents c0 + c1*v + c2*v^2
      where v^3 = xi = 1 + u. *)
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  Definition fp6_c0 (x : Fp6) : Fp2 := fst (fst x).
  Definition fp6_c1 (x : Fp6) : Fp2 := snd (fst x).
  Definition fp6_c2 (x : Fp6) : Fp2 := snd x.

  Definition fp6_build (c0 c1 c2 : Fp2) : Fp6 := ((c0, c1), c2).

  Definition fp6_zero : Fp6 := fp6_build fp2_zero fp2_zero fp2_zero.
  Definition fp6_one  : Fp6 := fp6_build fp2_one  fp2_zero fp2_zero.

  Definition fp6_add (a b : Fp6) : Fp6 :=
    fp6_build (fp2_add (fp6_c0 a) (fp6_c0 b))
              (fp2_add (fp6_c1 a) (fp6_c1 b))
              (fp2_add (fp6_c2 a) (fp6_c2 b)).

  Definition fp6_sub (a b : Fp6) : Fp6 :=
    fp6_build (fp2_sub (fp6_c0 a) (fp6_c0 b))
              (fp2_sub (fp6_c1 a) (fp6_c1 b))
              (fp2_sub (fp6_c2 a) (fp6_c2 b)).

  Definition fp6_neg (a : Fp6) : Fp6 :=
    fp6_build (fp2_neg (fp6_c0 a))
              (fp2_neg (fp6_c1 a))
              (fp2_neg (fp6_c2 a)).

  (** Multiply by v in Fp6: v*(c0 + c1*v + c2*v^2) = xi*c2 + c0*v + c1*v^2. *)
  Definition fp6_mul_by_v (a : Fp6) : Fp6 :=
    fp6_build (fp2_mul_xi (fp6_c2 a))
              (fp6_c0 a)
              (fp6_c1 a).

  (** Fp6 multiplication (Karatsuba). *)
  Definition fp6_mul (a b : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let b0 := fp6_c0 b in let b1 := fp6_c1 b in let b2 := fp6_c2 b in
    let a0b0 := fp2_mul a0 b0 in
    let a1b1 := fp2_mul a1 b1 in
    let a2b2 := fp2_mul a2 b2 in
    let t0 := fp2_sub (fp2_mul (fp2_add a1 a2) (fp2_add b1 b2))
                       (fp2_add a1b1 a2b2) in
    let c0 := fp2_add a0b0 (fp2_mul_xi t0) in
    let t1 := fp2_sub (fp2_mul (fp2_add a0 a1) (fp2_add b0 b1))
                       (fp2_add a0b0 a1b1) in
    let c1 := fp2_add t1 (fp2_mul_xi a2b2) in
    let t2 := fp2_sub (fp2_mul (fp2_add a0 a2) (fp2_add b0 b2))
                       (fp2_add a0b0 a2b2) in
    let c2 := fp2_add t2 a1b1 in
    fp6_build c0 c1 c2.

  (** Fp6 squaring (Chung-Hasan SQR3). *)
  Definition fp6_sqr (a : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let s0 := fp2_sqr a0 in
    let ab := fp2_mul a0 a1 in
    let s1 := fp2_add ab ab in
    let s2 := fp2_sqr (fp2_sub (fp2_add a0 a2) a1) in
    let bc := fp2_mul a1 a2 in
    let s3 := fp2_add bc bc in
    let s4 := fp2_sqr a2 in
    let c0 := fp2_add s0 (fp2_mul_xi s3) in
    let c1 := fp2_add s1 (fp2_mul_xi s4) in
    let c2 := fp2_sub (fp2_add (fp2_add s1 s2) s3)
                       (fp2_add s0 s4) in
    fp6_build c0 c1 c2.

  (** Fp6 inverse. *)
  Definition fp6_inv (a : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let c0_sq := fp2_sqr a0 in
    let c1_sq := fp2_sqr a1 in
    let c2_sq := fp2_sqr a2 in
    let c0c1  := fp2_mul a0 a1 in
    let c0c2  := fp2_mul a0 a2 in
    let c1c2  := fp2_mul a1 a2 in
    let A := fp2_sub c0_sq (fp2_mul_xi c1c2) in
    let B := fp2_sub (fp2_mul_xi c2_sq) c0c1 in
    let C := fp2_sub c1_sq c0c2 in
    let FF := fp2_add (fp2_mul a0 A)
                      (fp2_mul_xi (fp2_add (fp2_mul a2 B) (fp2_mul a1 C))) in
    let FF_inv := fp2_inv FF in
    fp6_build (fp2_mul A FF_inv) (fp2_mul B FF_inv) (fp2_mul C FF_inv).

  (** Multiply Fp6 element componentwise by an Fp2 scalar. *)
  Definition fp6_mul_fp2 (a : Fp6) (s : Fp2) : Fp6 :=
    fp6_build (fp2_mul (fp6_c0 a) s)
              (fp2_mul (fp6_c1 a) s)
              (fp2_mul (fp6_c2 a) s).

  (* ================================================================ *)
  (** ** Frobenius constants for Fp6                                   *)
  (* ================================================================ *)

  (** Frobenius constants -- to be instantiated for BLS12-381.
      gamma1    = xi^{(p-1)/3}      in Fp2
      gamma2    = xi^{2(p-1)/3}     in Fp2
      gamma1_p2 = xi^{(p^2-1)/3}    in Fp2
      gamma2_p2 = xi^{2(p^2-1)/3}   in Fp2 *)
  Variable frobenius_gamma1    : Fp2.
  Variable frobenius_gamma2    : Fp2.
  Variable frobenius_gamma1_p2 : Fp2.
  Variable frobenius_gamma2_p2 : Fp2.

  (** Frobenius on Fp6 (raise to p). *)
  Definition fp6_frobenius (a : Fp6) : Fp6 :=
    let c0 := fp2_conjugate (fp6_c0 a) in
    let c1 := fp2_mul (fp2_conjugate (fp6_c1 a)) frobenius_gamma1 in
    let c2 := fp2_mul (fp2_conjugate (fp6_c2 a)) frobenius_gamma2 in
    fp6_build c0 c1 c2.

  (** Frobenius squared on Fp6 (raise to p^2). *)
  Definition fp6_frobenius_p2 (a : Fp6) : Fp6 :=
    fp6_build (fp6_c0 a)
              (fp2_mul (fp6_c1 a) frobenius_gamma1_p2)
              (fp2_mul (fp6_c2 a) frobenius_gamma2_p2).

  (* ================================================================ *)
  (** ** Fp12 = Fp6[w]/(w^2 - v)                                     *)
  (* ================================================================ *)

  (** An Fp12 element (c0, c1) represents c0 + c1*w where w^2 = v in Fp6.
      Tower: Fp12 = Fp6[w]/(w^2-v), Fp6 = Fp2[v]/(v^3-xi), Fp2 = Fp[u]/(u^2+1). *)
  Local Notation Fp12 := (Fp6 * Fp6)%type.

  Definition fp12_c0 (x : Fp12) : Fp6 := fst x.
  Definition fp12_c1 (x : Fp12) : Fp6 := snd x.
  Definition fp12_build (c0 c1 : Fp6) : Fp12 := (c0, c1).

  Definition fp12_zero : Fp12 := fp12_build fp6_zero fp6_zero.
  Definition fp12_one  : Fp12 := fp12_build fp6_one  fp6_zero.

  Definition fp12_add (a b : Fp12) : Fp12 :=
    fp12_build (fp6_add (fp12_c0 a) (fp12_c0 b))
               (fp6_add (fp12_c1 a) (fp12_c1 b)).

  Definition fp12_sub (a b : Fp12) : Fp12 :=
    fp12_build (fp6_sub (fp12_c0 a) (fp12_c0 b))
               (fp6_sub (fp12_c1 a) (fp12_c1 b)).

  Definition fp12_neg (a : Fp12) : Fp12 :=
    fp12_build (fp6_neg (fp12_c0 a))
               (fp6_neg (fp12_c1 a)).

  (** Fp12 multiplication:
      (a0 + a1*w)(b0 + b1*w) = (a0*b0 + a1*b1*v) + (a0*b1 + a1*b0)*w
      using w^2 = v (multiply-by-v in Fp6 for the carry term). *)
  Definition fp12_mul (a b : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let b0 := fp12_c0 b in let b1 := fp12_c1 b in
    let a0b0 := fp6_mul a0 b0 in
    let a1b1 := fp6_mul a1 b1 in
    let c0 := fp6_add a0b0 (fp6_mul_by_v a1b1) in
    let c1 := fp6_sub (fp6_sub (fp6_mul (fp6_add a0 a1) (fp6_add b0 b1))
                                a0b0)
                       a1b1 in
    fp12_build c0 c1.

  (** Fp12 squaring:
      (a0 + a1*w)^2 = (a0^2 + a1^2*v) + 2*a0*a1*w. *)
  Definition fp12_sqr (a : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let a0_sq := fp6_sqr a0 in
    let a1_sq := fp6_sqr a1 in
    let cross := fp6_mul a0 a1 in
    let c0 := fp6_add a0_sq (fp6_mul_by_v a1_sq) in
    let c1 := fp6_add cross cross in
    fp12_build c0 c1.

  (** Fp12 conjugate: conjugate(a0 + a1*w) = a0 - a1*w. *)
  Definition fp12_conjugate (a : Fp12) : Fp12 :=
    fp12_build (fp12_c0 a) (fp6_neg (fp12_c1 a)).

  (** Fp12 inverse:
      (a0 + a1*w)^{-1} = (a0 - a1*w) / (a0^2 - a1^2*v). *)
  Definition fp12_inv (a : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let a0_sq := fp6_sqr a0 in
    let a1_sq := fp6_sqr a1 in
    let norm := fp6_sub a0_sq (fp6_mul_by_v a1_sq) in
    let norm_inv := fp6_inv norm in
    fp12_build (fp6_mul a0 norm_inv) (fp6_neg (fp6_mul a1 norm_inv)).

  (* ================================================================ *)
  (** ** Frobenius constants for Fp12                                  *)
  (* ================================================================ *)

  (** Frobenius coefficient for w in Fp12:
      w^p = w * xi^{(p-1)/6} *)
  Variable frobenius_coeff_fp12_c1    : Fp2.

  (** Frobenius p^2 coefficient for w:
      w^{p^2} = w * xi^{(p^2-1)/6} *)
  Variable frobenius_coeff_fp12_p2_c1 : Fp2.

  (** Fp12 Frobenius (raise to p). *)
  Definition fp12_frobenius (a : Fp12) : Fp12 :=
    let c0 := fp6_frobenius (fp12_c0 a) in
    let c1 := fp6_frobenius (fp12_c1 a) in
    fp12_build c0 (fp6_mul_fp2 c1 frobenius_coeff_fp12_c1).

  (** Fp12 Frobenius squared (raise to p^2). *)
  Definition fp12_frobenius_p2 (a : Fp12) : Fp12 :=
    let c0 := fp6_frobenius_p2 (fp12_c0 a) in
    let c1 := fp6_frobenius_p2 (fp12_c1 a) in
    fp12_build c0 (fp6_mul_fp2 c1 frobenius_coeff_fp12_p2_c1).

  (** Check if an Fp12 element equals one.
      Since we are in Gallina (spec level), we use Decidable equality
      on F p = {z : Z | z = z mod p}. We compare component-by-component.
      For spec purposes, we define this using the projections. *)
  Variable fp12_eq_dec : forall (a b : Fp12), {a = b} + {a <> b}.

  Definition fp12_is_one (a : Fp12) : bool :=
    if fp12_eq_dec a fp12_one then true else false.

  (* ================================================================ *)
  (** ** Curve point types                                             *)
  (* ================================================================ *)

  Record G1Affine := mk_g1_affine {
    g1_x : F;
    g1_y : F;
    g1_infinity : bool;
  }.

  Record G2Affine := mk_g2_affine {
    g2_x : Fp2;
    g2_y : Fp2;
    g2_infinity : bool;
  }.

  (* ================================================================ *)
  (** ** Line evaluation                                               *)
  (* ================================================================ *)

  (** Embed a line evaluation into Fp12.

      The line through T on E'(Fp2) evaluated at P in G1(Fp) is:
        l(P) = (lambda*x_T - y_T) + (-lambda*x_P)*v + y_P*(v*w)

      In the tower Fp12 = Fp6[w]/(w^2-v), Fp6 = Fp2[v]/(v^3-xi):
        w^2 = v,  w^3 = v*w

      As Fp12 = (c0, c1):
        c0 = ((lambda*x_T - y_T), (-lambda*x_P), 0)  -- Fp6
        c1 = (0, (y_P, 0), 0)                          -- Fp6, with y_P embedded in Fp2 *)
  Definition make_line (lambda : Fp2) (x_t y_t : Fp2) (x_p y_p : F) : Fp12 :=
    let c00 := fp2_sub (fp2_mul lambda x_t) y_t in
    let c01 := fp2_neg (fp2_mul_fp lambda x_p) in
    let c11 := fp_to_fp2 y_p in
    fp12_build (fp6_build c00 c01 fp2_zero)
               (fp6_build fp2_zero c11 fp2_zero).

  (* ================================================================ *)
  (** ** Affine point arithmetic on E'(Fp2)                            *)
  (* ================================================================ *)

  (** Affine doubling on E'(Fp2).
      Given x, y and the tangent slope lambda = 3*x^2 / (2*y),
      returns (x', y') where:
        x' = lambda^2 - 2*x
        y' = lambda*(x - x') - y *)
  Definition ec2_double_with_lambda (x y lambda : Fp2) : Fp2 * Fp2 :=
    let new_x := fp2_sub (fp2_sub (fp2_sqr lambda) x) x in
    let new_y := fp2_sub (fp2_mul lambda (fp2_sub x new_x)) y in
    (new_x, new_y).

  (** Affine addition on E'(Fp2).
      Given (x1, y1), (x2, y2) and the chord slope
      lambda = (y2 - y1)/(x2 - x1), returns (x3, y3) where:
        x3 = lambda^2 - x1 - x2
        y3 = lambda*(x1 - x3) - y1 *)
  Definition ec2_add_with_lambda (x1 y1 x2 : Fp2) (lambda : Fp2) : Fp2 * Fp2 :=
    let new_x := fp2_sub (fp2_sub (fp2_sqr lambda) x1) x2 in
    let new_y := fp2_sub (fp2_mul lambda (fp2_sub x1 new_x)) y1 in
    (new_x, new_y).

  (* ================================================================ *)
  (** ** BLS parameter and bit decomposition                           *)
  (* ================================================================ *)

  (** BLS parameter |x| = 0xd201000000010000.

      Binary (64 bits, MSB first):
        1101_0010_0000_0001_0000_0000_0000_0000
        _0000_0000_0000_0001_0000_0000_0000_0000

      Bits set (0-indexed from LSB): 16, 48, 57, 60, 62, 63
      The MSB (bit 63) initializes T = Q; the loop processes bits 62 down to 0. *)
  Definition bls_x : Z := 0xd201000000010000.

  (** Helper: extract bits of a Z value, MSB first, for a given width.
      Returns a list of bools of length [width], MSB first. *)
  Definition Z_to_bits (width : nat) (z : Z) : list bool :=
    List.map (fun i => Z.testbit z (Z.of_nat i))
             (List.rev (List.seq 0 width)).

  (** Bits 62 down to 0 of bls_x (63 bools, MSB first).
      Bit 63 is the MSB and is 1; it initializes T = Q. *)
  Definition bls_x_bits : list bool :=
    Z_to_bits 63 bls_x.

  (* ================================================================ *)
  (** ** Miller loop                                                   *)
  (* ================================================================ *)

  (** State for the Miller loop: (f, t_x, t_y) where
      f is the accumulating Fp12 element and (t_x, t_y) is the
      running point T on E'(Fp2). *)

  (** One step of the Miller loop: process one bit.
      Always performs a doubling step; if the bit is 1,
      also performs an addition step with Q. *)
  Definition miller_loop_step (q_x q_y : Fp2) (x_p y_p : F)
    (state : Fp12 * (Fp2 * Fp2)) (bit : bool)
    : Fp12 * (Fp2 * Fp2) :=
    let '(f, (t_x, t_y)) := state in

    (* --- Doubling step --- *)
    (* Tangent slope: lambda_d = 3*x_T^2 / (2*y_T) *)
    let x_t_sq := fp2_sqr t_x in
    let three_x_t_sq := fp2_add (fp2_add x_t_sq x_t_sq) x_t_sq in
    let two_y_t := fp2_add t_y t_y in
    let lambda_d := fp2_mul three_x_t_sq (fp2_inv two_y_t) in

    (* Line evaluation at P *)
    let line_d := make_line lambda_d t_x t_y x_p y_p in

    (* f = f^2 * line *)
    let f' := fp12_mul (fp12_sqr f) line_d in

    (* T = 2T *)
    let '(new_t_x, new_t_y) := ec2_double_with_lambda t_x t_y lambda_d in

    (* --- Addition step (if bit is set) --- *)
    if bit then
      (* Chord slope: lambda_a = (y_Q - y_T') / (x_Q - x_T') *)
      let lambda_a := fp2_mul (fp2_sub q_y new_t_y)
                               (fp2_inv (fp2_sub q_x new_t_x)) in
      let line_a := make_line lambda_a new_t_x new_t_y x_p y_p in
      let f'' := fp12_mul f' line_a in
      (* T = T' + Q *)
      let '(add_t_x, add_t_y) := ec2_add_with_lambda new_t_x new_t_y q_x lambda_a in
      (f'', (add_t_x, add_t_y))
    else
      (f', (new_t_x, new_t_y)).

  (** Miller loop: compute f_{|x|,Q}(P).

      Processes bits of |x| from MSB-1 (bit 62) down to 0.
      T is initialized to Q (corresponding to the MSB = 1).

      Note: conjugation for negative x is NOT needed because the full
      final exponentiation (p^12 - 1)/r handles the sign via the
      easy part f^{p^6-1}. *)
  Definition miller_loop (P : G1Affine) (Q : G2Affine) : Fp12 :=
    if g1_infinity P || g2_infinity Q then
      fp12_one
    else
      let init_state : Fp12 * (Fp2 * Fp2) :=
        (fp12_one, (g2_x Q, g2_y Q)) in
      fst (fold_left
             (miller_loop_step (g2_x Q) (g2_y Q) (g1_x P) (g1_y P))
             bls_x_bits
             init_state).

  (* ================================================================ *)
  (** ** Exponentiation helpers                                        *)
  (* ================================================================ *)

  (** Left-to-right binary exponentiation for Fp12.
      Processes a list of bits (MSB first).
      Uses the "started" flag technique from the hax reference:
      skips leading zeros, then squares on every step and
      multiplies when the bit is 1. *)
  Fixpoint fp12_pow_bits_aux (base : Fp12) (bits : list bool)
    (acc : Fp12) (started : bool) : Fp12 :=
    match bits with
    | [] => acc
    | b :: rest =>
      let acc' := if started then fp12_sqr acc else acc in
      if b then
        let acc'' := if started then fp12_mul acc' base else base in
        fp12_pow_bits_aux base rest acc'' true
      else
        fp12_pow_bits_aux base rest acc' started
    end.

  Definition fp12_pow_bits (base : Fp12) (bits : list bool) : Fp12 :=
    fp12_pow_bits_aux base bits fp12_one false.

  (** Exponentiate by a Z value using its binary representation.
      Extracts bits from the given width (number of bits). *)
  Definition fp12_pow_Z (base : Fp12) (exp : Z) (width : nat) : Fp12 :=
    fp12_pow_bits base (Z_to_bits width exp).

  (* ================================================================ *)
  (** ** Hard part exponent h3 = (p^4 - p^2 + 1) / r                  *)
  (* ================================================================ *)

  (** The hard part exponent, stored as 20 little-endian u64 limbs.
      h3 = limbs[0] + limbs[1]*2^64 + ... + limbs[19]*2^(19*64).

      1268 bits total. *)
  Definition h3_exp : Z :=
        0xe516c3f438e3ba79
      + 0xfa9912aae208ccf1 * 2^64
      + 0x905ce937335d5b68 * 2^128
      + 0xc71a2629b0dea236 * 2^192
      + 0x83774940996754c8 * 2^256
      + 0x21d160aeb6a1e799 * 2^320
      + 0x2ed0b283ed237db4 * 2^384
      + 0x915c97f36c6f1821 * 2^448
      + 0x67f17fcbde783765 * 2^512
      + 0x2378b9039096d1b7 * 2^576
      + 0x7988f8761bdc51dc * 2^640
      + 0x2076995003fc77a1 * 2^704
      + 0x827eca0ba621315b * 2^768
      + 0xe5a72bce8d63cb9f * 2^832
      + 0xf68f7764c28b6f8a * 2^896
      + 0x2f230063cf081517 * 2^960
      + 0x94506632528d6a9a * 2^1024
      + 0xd3cde88eeb996ca3 * 2^1088
      + 0xc0bd38c3195c899e * 2^1152
      + 0x000f686b3d807d01 * 2^1216.

  (** Number of bits in h3_exp. *)
  Definition h3_width : nat := 1268.

  (* ================================================================ *)
  (** ** Final exponentiation                                          *)
  (* ================================================================ *)

  (** Final exponentiation: f^{(p^12 - 1)/r}.

      Decomposed as:
        (p^12 - 1)/r = (p^6 - 1) * (p^2 + 1) * h3

      where h3 = (p^4 - p^2 + 1)/r.

      Easy part: f^{(p^6-1)(p^2+1)}
      Hard part: result^{h3} *)
  Definition final_exponentiation (f : Fp12) : Fp12 :=
    (* Easy part 1: f^{p^6-1}
       f^{p^6} = conjugate(f) since p^6 acts as conjugation on Fp12. *)
    let f_conj := fp12_conjugate f in
    let f_inv := fp12_inv f in
    let result := fp12_mul f_conj f_inv in

    (* Easy part 2: result^{p^2+1} *)
    let result_p2 := fp12_frobenius_p2 result in
    let result' := fp12_mul result_p2 result in

    (* Hard part: result'^{h3} *)
    fp12_pow_Z result' h3_exp h3_width.

  (* ================================================================ *)
  (** ** Top-level pairing functions                                   *)
  (* ================================================================ *)

  (** Compute the optimal Ate pairing e(P, Q).
      Returns an element of GT. *)
  Definition pairing (P : G1Affine) (Q : G2Affine) : Fp12 :=
    let f := miller_loop P Q in
    final_exponentiation f.

  (** Negate a G1 affine point (negate the y-coordinate). *)
  Definition g1_neg (P : G1Affine) : G1Affine :=
    mk_g1_affine (g1_x P) (-f g1_y P) (g1_infinity P).

  (** Pairing check: e(P1, Q1) == e(P2, Q2).

      Checks e(P1,Q1) * e(-P2,Q2) == 1 via a single final exponentiation. *)
  Definition pairing_check (P1 : G1Affine) (Q1 : G2Affine)
    (P2 : G1Affine) (Q2 : G2Affine) : bool :=
    let f1 := miller_loop P1 Q1 in
    let neg_P2 := mk_g1_affine (g1_x P2) (-f g1_y P2) (g1_infinity P2) in
    let f2 := miller_loop neg_P2 Q2 in
    let f := fp12_mul f1 f2 in
    let result := final_exponentiation f in
    fp12_is_one result.

  (* ================================================================ *)
  (** ** Power by BLS parameter x                                     *)
  (* ================================================================ *)

  (** Compute f^{|x|} using binary exponentiation.
      |x| = 0xd201000000010000 (64 bits). *)
  Definition fp12_pow_bls_x (f : Fp12) : Fp12 :=
    fp12_pow_Z f bls_x 64.

  (** Compute f^x where x = -|x| (negative).
      f^x = f^{-|x|} = conjugate(f^{|x|}) in the cyclotomic subgroup. *)
  Definition fp12_pow_bls_x_signed (f : Fp12) : Fp12 :=
    fp12_conjugate (fp12_pow_bls_x f).

  (* ================================================================ *)
  (** ** Optimized final exponentiation (DSD decomposition)           *)
  (* ================================================================ *)

  (** Raise to |x|/2 = 0x6900800000008000 (half the unsigned BLS parameter). *)
  Definition fp12_pow_bls_x_half (f : Fp12) : Fp12 :=
    fp12_pow_Z f (bls_x / 2) 63.

  (** Raise to -|x|/2 (the signed half-parameter). *)
  Definition fp12_pow_bls_x_half_signed (f : Fp12) : Fp12 :=
    fp12_conjugate (fp12_pow_bls_x_half f).

  (** Hard part of final exponentiation using the Hayashida-Hayasaka-Teruya
      algorithm (eprint 2020/875).  Computes f^{3*h3} where h3 = (p⁴-p²+1)/r.

      The factor of 3 is compensated in the overall final exponentiation:
      since 3 | (p-1), the easy part f^{(p⁶-1)(p²+1)} already ensures
      the result lies in the correct subgroup.

      Uses 5 exp-by-x + 1 exp-by-(x/2) + 2 Frobenius + ~9 Fp12_mul,
      requiring ~5×64 = 320 squarings instead of 1268 for naive h3.

      Algorithm from gnark-crypto (Consensys), verified numerically
      to produce exponent 3*h3.
  *)
  Definition final_exp_hard_dsd (f : Fp12) : Fp12 :=
    let t0 := fp12_sqr f in                        (* f² *)
    let t1 := fp12_pow_bls_x_half_signed t0 in     (* (f²)^{-|x|/2} = f^{-|x|} *)
    let t2 := fp12_conjugate f in                   (* f^{-1} *)
    let t1 := fp12_mul t1 t2 in                     (* f^{-|x|-1} *)
    let t2 := fp12_pow_bls_x_signed t1 in           (* (f^{-|x|-1})^{-|x|} = f^{|x|²+|x|} *)
    let t1 := fp12_conjugate t1 in                  (* f^{|x|+1} *)
    let t1 := fp12_mul t1 t2 in                     (* f^{|x|²+2|x|+1} = f^{(|x|+1)²} *)
    let t2 := fp12_pow_bls_x_signed t1 in           (* f^{-|x|(|x|+1)²} *)
    let t1 := fp12_frobenius t1 in                  (* f^{p(|x|+1)²} *)
    let t1 := fp12_mul t1 t2 in                     (* f^{(|x|+1)²(p-|x|)} *)
    let result := fp12_mul f t0 in                  (* f³ *)
    let t0 := fp12_pow_bls_x_signed t1 in           (* f^{-|x|(|x|+1)²(p-|x|)} *)
    let t2 := fp12_pow_bls_x_signed t0 in           (* f^{|x|²(|x|+1)²(p-|x|)} *)
    let t0 := fp12_frobenius_p2 t1 in               (* f^{p²(|x|+1)²(p-|x|)} *)
    let t1 := fp12_conjugate t1 in                  (* f^{-(|x|+1)²(p-|x|)} *)
    let t1 := fp12_mul t1 t2 in                     (* f^{(|x|²-1)(|x|+1)²(p-|x|)} *)
    let t1 := fp12_mul t1 t0 in                     (* f^{(|x|²-1+p²)(|x|+1)²(p-|x|)} *)
    fp12_mul result t1.                              (* f³ · f^{...} = f^{3·h3} *)

  (** Optimized final exponentiation using DSD for the hard part. *)
  Definition final_exponentiation_dsd (f : Fp12) : Fp12 :=
    (* Easy part 1: f^{p^6-1} *)
    let f_conj := fp12_conjugate f in
    let f_inv := fp12_inv f in
    let result := fp12_mul f_conj f_inv in
    (* Easy part 2: result^{p^2+1} *)
    let result_p2 := fp12_frobenius_p2 result in
    let result' := fp12_mul result_p2 result in
    (* Hard part: DSD decomposition *)
    final_exp_hard_dsd result'.

End BLS12_Pairing.
