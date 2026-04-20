(** * Optimal Ate pairing specification for BLS24-509.

    Computes e(P, Q) for P in G1 subset E(Fp), Q in G2 subset E'(Fp4),
    producing a result in GT, a subgroup of the multiplicative group of Fp24.

    The optimal Ate pairing:
      ate(P, Q) = f_{|z|,Q}(P)^{(p^24 - 1)/r}
    where z = -0x800000ffff801 is the BLS24 seed.

    Tower:
      Fp2  = Fp[u]  / (u^2 + 1)
      Fp4  = Fp2[v] / (v^2 - (1+u))
      Fp8  = Fp4[w] / (w^2 - v)
      Fp24 = Fp8[t] / (t^3 - w)

    Twist:
      Sextic M-type twist using t (where t^6 = v in Fp4).
      E'(Fp4): y^2 = x^3 + 1/v
      Isomorphism psi: (x', y') -> (x'*t^2, y'*t^3)

    This file imports tower arithmetic from Tower.v and defines:
    - Point types for G1 and G2
    - Line evaluation for the optimal ate pairing
    - Miller loop iterating over bits of |z|
    - Final exponentiation: easy part + hard part
    - Top-level pairing function
*)

From Coq Require Import ZArith BinPos List Bool.
Import ListNotations.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Bedrock.Spec.BLS24Pairing.Tower.

Section BLS24_Pairing.
  Variable p : positive.

  (* ================================================================ *)
  (** ** Notations for the tower operations from Tower.v               *)
  (* ================================================================ *)

  Local Notation Fp  := (F p).
  Local Notation Fp2 := (Fp * Fp)%type.
  Local Notation Fp4 := (Fp2 * Fp2)%type.
  Local Notation Fp8 := (Fp4 * Fp4)%type.
  Local Notation Fp24 := (Fp8 * Fp8 * Fp8)%type.

  (* Fp operations *)
  Local Notation "x +f y" := (@F.add p x y) (at level 50, left associativity).
  Local Notation "x *f y" := (@F.mul p x y) (at level 40, left associativity).
  Local Notation "x -f y" := (@F.sub p x y) (at level 50, left associativity).
  Local Notation "-f x"   := (@F.opp p x) (at level 35, right associativity).
  Local Notation "0f"     := (@F.zero p).
  Local Notation "1f"     := (@F.one p).

  (* ================================================================ *)
  (** ** Embedding helpers                                             *)
  (* ================================================================ *)

  (** Embed Fp into Fp2 as (s, 0). *)
  Definition fp_to_fp2 (s : Fp) : Fp2 := (s, 0f).

  (** Embed Fp into Fp4 as ((s, 0), (0, 0)). *)
  Definition fp_to_fp4 (s : Fp) : Fp4 := (fp_to_fp2 s, fp2_zero p).

  (** Embed Fp2 into Fp4 as (a, (0,0)). *)
  Definition fp2_to_fp4 (a : Fp2) : Fp4 := (a, fp2_zero p).

  (** Embed Fp4 into Fp8 as (a, 0). *)
  Definition fp4_to_fp8 (a : Fp4) : Fp8 := (a, fp4_zero p).

  (** Embed Fp8 into Fp24 as (a, 0, 0). *)
  Definition fp8_to_fp24 (a : Fp8) : Fp24 := fp24_build p a (fp8_zero p) (fp8_zero p).

  (** Scale an Fp4 element by an Fp scalar: multiply each component. *)
  Definition fp4_mul_fp (a : Fp4) (s : Fp) : Fp4 :=
    let a0 := fst a in let a1 := snd a in
    (fp2_mul p a0 (fp_to_fp2 s), fp2_mul p a1 (fp_to_fp2 s)).

  (** Fp4 squaring. *)
  Definition fp4_sqr (a : Fp4) : Fp4 := fp4_mul p a a.

  (** Fp24 squaring. *)
  Definition fp24_sqr (a : Fp24) : Fp24 := fp24_mul p a a.

  (** Fp24 inverse:
      For the spec, define using the conjugate-and-norm approach.
      For a = a0 + a1*t + a2*t^2, the inverse uses the norm in the
      cubic extension. *)
  Definition fp24_inv (a : Fp24) : Fp24 :=
    let a0 := fp24_c0 p a in
    let a1 := fp24_c1 p a in
    let a2 := fp24_c2 p a in
    (* Compute cofactor matrix entries *)
    let v0 := fp8_sub p (fp8_mul p a0 a0) (fp8_mul_by_w p (fp8_mul p a1 a2)) in
    let v1 := fp8_sub p (fp8_mul_by_w p (fp8_mul p a2 a2)) (fp8_mul p a0 a1) in
    let v2 := fp8_sub p (fp8_mul p a1 a1) (fp8_mul p a0 a2) in
    (* Norm = a0*v0 + w*(a1*v2 + a2*v1) *)
    let norm := fp8_add p (fp8_mul p a0 v0)
                  (fp8_mul_by_w p (fp8_add p (fp8_mul p a2 v1)
                                              (fp8_mul p a1 v2))) in
    let norm_inv := fp8_inv p norm in
    fp24_build p (fp8_mul p v0 norm_inv)
                 (fp8_mul p v1 norm_inv)
                 (fp8_mul p v2 norm_inv).

  (* ================================================================ *)
  (** ** Frobenius endomorphism on Fp24                                *)
  (* ================================================================ *)

  (** The Frobenius endomorphism pi: x -> x^p on Fp24 requires
      precomputed constants (gamma values).

      For Fp24 = Fp8[t]/(t^3 - w), raising to p gives:
        (a0 + a1*t + a2*t^2)^p = a0^p + a1^p * t^p + a2^p * t^{2p}

      where t^p = t * gamma_1 and t^{2p} = t^2 * gamma_2,
      with gamma_1 = w^{(p-1)/3} and gamma_2 = w^{2(p-1)/3} in Fp8.

      The Frobenius on Fp8 itself (a^p for a in Fp8) decomposes
      through the tower. For the spec, we take these as parameters.

      In practice, the gamma values and sub-tower Frobenius maps
      are precomputed from the prime p. *)

  (** Frobenius on Fp2: conjugation (a0, a1) -> (a0, -a1) since u^p = -u. *)
  Definition fp2_frob (a : Fp2) : Fp2 := fp2_conjugate p a.

  (** Frobenius on Fp4 requires the constant xi_2^{(p-1)/2} in Fp2.
      Since Fp4 = Fp2[v]/(v^2 - xi_2):
        (a0 + a1*v)^p = a0^p + a1^p * v^p
      where v^p = v * xi_2^{(p-1)/2}. *)
  Variable gamma_fp4 : Fp2.  (* = xi_2^{(p-1)/2} where xi_2 = 1+u *)

  Definition fp4_frob (a : Fp4) : Fp4 :=
    (fp2_frob (fst a), fp2_mul p (fp2_frob (snd a)) gamma_fp4).

  (** Frobenius on Fp8 requires xi_4^{(p-1)/2} in Fp4.
      Since Fp8 = Fp4[w]/(w^2 - v):
        (a0 + a1*w)^p = a0^p + a1^p * w^p
      where w^p = w * v^{(p-1)/2}. *)
  Variable gamma_fp8 : Fp4.  (* = v^{(p-1)/2} in Fp4 *)

  Definition fp8_frob (a : Fp8) : Fp8 :=
    (fp4_frob (fst a), fp4_mul p (fp4_frob (snd a)) gamma_fp8).

  (** Frobenius on Fp24 requires w^{(p-1)/3} and w^{2(p-1)/3} in Fp8.
      Since Fp24 = Fp8[t]/(t^3 - w):
        (a0 + a1*t + a2*t^2)^p = a0^p + a1^p * t^p + a2^p * t^{2p}
      where t^p = t * w^{(p-1)/3}, t^{2p} = t^2 * w^{2(p-1)/3}. *)
  Variable gamma_fp24_1 : Fp8.  (* = w^{(p-1)/3} *)
  Variable gamma_fp24_2 : Fp8.  (* = w^{2(p-1)/3} *)

  Definition fp24_frob (a : Fp24) : Fp24 :=
    let c0 := fp8_frob (fp24_c0 p a) in
    let c1 := fp8_mul p (fp8_frob (fp24_c1 p a)) gamma_fp24_1 in
    let c2 := fp8_mul p (fp8_frob (fp24_c2 p a)) gamma_fp24_2 in
    fp24_build p c0 c1 c2.

  (** Frobenius squared (raise to p^2).
      Requires p^2-versions of the gamma constants. *)
  Variable gamma_fp4_p2  : Fp2.  (* = xi_2^{(p^2-1)/2} *)
  Variable gamma_fp8_p2  : Fp4.  (* = v^{(p^2-1)/2} *)
  Variable gamma_fp24_p2_1 : Fp8.  (* = w^{(p^2-1)/3} *)
  Variable gamma_fp24_p2_2 : Fp8.  (* = w^{2(p^2-1)/3} *)

  Definition fp4_frob_p2 (a : Fp4) : Fp4 :=
    (fst a, fp2_mul p (snd a) gamma_fp4_p2).

  Definition fp8_frob_p2 (a : Fp8) : Fp8 :=
    (fp4_frob_p2 (fst a), fp4_mul p (fp4_frob_p2 (snd a)) gamma_fp8_p2).

  Definition fp24_frob_p2 (a : Fp24) : Fp24 :=
    let c0 := fp8_frob_p2 (fp24_c0 p a) in
    let c1 := fp8_mul p (fp8_frob_p2 (fp24_c1 p a)) gamma_fp24_p2_1 in
    let c2 := fp8_mul p (fp8_frob_p2 (fp24_c2 p a)) gamma_fp24_p2_2 in
    fp24_build p c0 c1 c2.

  (** Frobenius to the 4th power (raise to p^4). *)
  Variable gamma_fp4_p4  : Fp2.
  Variable gamma_fp8_p4  : Fp4.
  Variable gamma_fp24_p4_1 : Fp8.
  Variable gamma_fp24_p4_2 : Fp8.

  Definition fp4_frob_p4 (a : Fp4) : Fp4 :=
    (fst a, fp2_mul p (snd a) gamma_fp4_p4).

  Definition fp8_frob_p4 (a : Fp8) : Fp8 :=
    (fp4_frob_p4 (fst a), fp4_mul p (fp4_frob_p4 (snd a)) gamma_fp8_p4).

  Definition fp24_frob_p4 (a : Fp24) : Fp24 :=
    let c0 := fp8_frob_p4 (fp24_c0 p a) in
    let c1 := fp8_mul p (fp8_frob_p4 (fp24_c1 p a)) gamma_fp24_p4_1 in
    let c2 := fp8_mul p (fp8_frob_p4 (fp24_c2 p a)) gamma_fp24_p4_2 in
    fp24_build p c0 c1 c2.

  (* ================================================================ *)
  (** ** Curve point types                                             *)
  (* ================================================================ *)

  (** G1 affine point on E(Fp): y^2 = x^3 + 1. *)
  Record G1Affine := mk_g1_affine {
    g1_x : Fp;
    g1_y : Fp;
    g1_infinity : bool;
  }.

  (** G2 affine point on the twist E'(Fp4): y^2 = x^3 + 1/v. *)
  Record G2Affine := mk_g2_affine {
    g2_x : Fp4;
    g2_y : Fp4;
    g2_infinity : bool;
  }.

  (* ================================================================ *)
  (** ** Line evaluation                                               *)
  (* ================================================================ *)

  (** Line evaluation for the optimal ate pairing with sextic twist.

      The twist is M-type sextic using t (where t^6 = v in Fp4):
        psi: E'(Fp4) -> E(Fp24), (x', y') -> (x'*t^2, y'*t^3)

      The tangent/chord line on E'(Fp4) at T = (xT, yT) with slope lambda
      is: l(X, Y) = lambda*(X - xT) - (Y - yT).

      Evaluating at the untwisted P = (xP, yP) in E(Fp), we compute
      l'(P) at psi^{-1}(P) = (xP/t^2, yP/t^3) and multiply by t^3 = w
      to clear denominators:

        l(P) * w = lambda*xP*t - lambda*xT*w - yP + yT*w

      In Fp24 = Fp8[t]/(t^3 - w) with Fp8 = Fp4[w]/(w^2 - v):
        c0 = (-yP,  yT - lambda*xT) in Fp8 = (Fp4, Fp4)
        c1 = (lambda*xP,  0)         in Fp8 = (Fp4, Fp4)
        c2 = (0, 0)                   in Fp8

      This is a sparse element with 3 nonzero Fp4 components
      (out of 6 total). *)
  Definition make_line (lambda : Fp4) (xT yT : Fp4) (xP yP : Fp) : Fp24 :=
    let c0_0 := fp4_neg p (fp_to_fp4 yP) in
    let c0_1 := fp4_sub p yT (fp4_mul p lambda xT) in
    let c0 : Fp8 := (c0_0, c0_1) in
    let c1_0 := fp4_mul_fp lambda xP in
    let c1 : Fp8 := (c1_0, fp4_zero p) in
    fp24_build p c0 c1 (fp8_zero p).

  (* ================================================================ *)
  (** ** Affine point arithmetic on E'(Fp4)                            *)
  (* ================================================================ *)

  (** Affine doubling on E'(Fp4).
      For the curve y^2 = x^3 + b' (a = 0):
        lambda = 3*x^2 / (2*y)
        x' = lambda^2 - 2*x
        y' = lambda*(x - x') - y *)
  Definition ec2_double_affine (x y : Fp4) : Fp4 * Fp4 * Fp4 :=
    let x_sq := fp4_sqr x in
    let three_x_sq := fp4_add p (fp4_add p x_sq x_sq) x_sq in
    let two_y := fp4_add p y y in
    let lambda := fp4_mul p three_x_sq (fp4_inv p two_y) in
    let new_x := fp4_sub p (fp4_sub p (fp4_sqr lambda) x) x in
    let new_y := fp4_sub p (fp4_mul p lambda (fp4_sub p x new_x)) y in
    (new_x, new_y, lambda).

  (** Affine addition on E'(Fp4).
      Given (x1, y1) and (x2, y2):
        lambda = (y2 - y1) / (x2 - x1)
        x3 = lambda^2 - x1 - x2
        y3 = lambda*(x1 - x3) - y1 *)
  Definition ec2_add_affine (x1 y1 x2 y2 : Fp4) : Fp4 * Fp4 * Fp4 :=
    let lambda := fp4_mul p (fp4_sub p y2 y1) (fp4_inv p (fp4_sub p x2 x1)) in
    let new_x := fp4_sub p (fp4_sub p (fp4_sqr lambda) x1) x2 in
    let new_y := fp4_sub p (fp4_mul p lambda (fp4_sub p x1 new_x)) y1 in
    (new_x, new_y, lambda).

  (* ================================================================ *)
  (** ** BLS24 seed and bit decomposition                              *)
  (* ================================================================ *)

  (** |z| = 0x800000ffff801 = 2^51 + 2^28 - 2^11 + 1.
      Binary representation (52 bits, MSB first):
        1000_0000_0000_0000_0000_0001_0000_0000_0000_0000_0000_0000_0000_0001

      Bits set: 0, 51, and bits 11..27 inverted (for NAF).

      For the simple binary approach, we iterate over bits of |z|.
      52 bits total; bit 51 is the MSB (=1), loop processes bits 50..0. *)

  Definition bls24_abs_z : Z := 0x800000ffff801.

  (** Helper: extract bits of a Z value, MSB first, for a given width. *)
  Definition Z_to_bits (width : nat) (z : Z) : list bool :=
    List.map (fun i => Z.testbit z (Z.of_nat i))
             (List.rev (List.seq 0 width)).

  (** Bits 50 down to 0 of |z| (51 bools, MSB first).
      Bit 51 is the MSB and initializes T = Q. *)
  Definition bls24_z_bits : list bool :=
    Z_to_bits 51 bls24_abs_z.

  (* ================================================================ *)
  (** ** Miller loop                                                   *)
  (* ================================================================ *)

  (** State: (f, t_x, t_y) where f is the Fp24 accumulator and
      (t_x, t_y) is the running point T on E'(Fp4). *)

  (** One step of the Miller loop: process one bit.
      Always double; conditionally add if the bit is 1. *)
  Definition miller_loop_step (qx qy : Fp4) (xP yP : Fp)
    (state : Fp24 * (Fp4 * Fp4)) (bit : bool)
    : Fp24 * (Fp4 * Fp4) :=
    let '(f, (tx, ty)) := state in

    (* --- Doubling step --- *)
    let '(new_tx, new_ty, lambda_d) := ec2_double_affine tx ty in
    let line_d := make_line lambda_d tx ty xP yP in
    let f' := fp24_mul p (fp24_sqr f) line_d in

    (* --- Addition step (if bit is set) --- *)
    if bit then
      let '(add_tx, add_ty, lambda_a) := ec2_add_affine new_tx new_ty qx qy in
      let line_a := make_line lambda_a new_tx new_ty xP yP in
      let f'' := fp24_mul p f' line_a in
      (f'', (add_tx, add_ty))
    else
      (f', (new_tx, new_ty)).

  (** Miller loop: compute f_{|z|,Q}(P).

      Iterates over bits of |z| from MSB-1 (bit 50) down to bit 0.
      T is initialized to Q (corresponding to the MSB = 1).

      Since z is negative, the final result is conjugated:
        f_{z,Q}(P) = conjugate(f_{|z|,Q}(P))
      because negating the exponent in the ate pairing inverts the
      Miller function value, and for elements that will be raised to
      (p^24-1)/r, inversion equals conjugation. *)
  Definition miller_loop (P : G1Affine) (Q : G2Affine) : Fp24 :=
    if g1_infinity P || g2_infinity Q then
      fp24_one p
    else
      let init_state : Fp24 * (Fp4 * Fp4) :=
        (fp24_one p, (g2_x Q, g2_y Q)) in
      let result :=
        fst (fold_left
               (miller_loop_step (g2_x Q) (g2_y Q) (g1_x P) (g1_y P))
               bls24_z_bits
               init_state) in
      (* Negate for z < 0: conjugate the result *)
      fp24_conjugate p result.

  (* ================================================================ *)
  (** ** Exponentiation helpers                                        *)
  (* ================================================================ *)

  (** Left-to-right binary exponentiation for Fp24.
      Skips leading zeros using the "started" flag. *)
  Fixpoint fp24_pow_bits_aux (base : Fp24) (bits : list bool)
    (acc : Fp24) (started : bool) : Fp24 :=
    match bits with
    | [] => acc
    | b :: rest =>
      let acc' := if started then fp24_sqr acc else acc in
      if b then
        let acc'' := if started then fp24_mul p acc' base else base in
        fp24_pow_bits_aux base rest acc'' true
      else
        fp24_pow_bits_aux base rest acc' started
    end.

  Definition fp24_pow_bits (base : Fp24) (bits : list bool) : Fp24 :=
    fp24_pow_bits_aux base bits (fp24_one p) false.

  (** Exponentiate by a Z value. *)
  Definition fp24_pow_Z (base : Fp24) (exp : Z) (width : nat) : Fp24 :=
    fp24_pow_bits base (Z_to_bits width exp).

  (** Compute f^{|z|} using binary exponentiation.
      |z| = 0x800000ffff801 (52 bits). *)
  Definition fp24_pow_abs_z (f : Fp24) : Fp24 :=
    fp24_pow_Z f bls24_abs_z 52.

  (** Compute f^z where z = -|z| (negative).
      f^z = f^{-|z|} = conjugate(f^{|z|}) in the cyclotomic subgroup. *)
  Definition fp24_pow_z (f : Fp24) : Fp24 :=
    fp24_conjugate p (fp24_pow_abs_z f).

  (* ================================================================ *)
  (** ** Final exponentiation                                          *)
  (* ================================================================ *)

  (** Final exponentiation: f^{(p^24 - 1)/r}.

      Factorization:
        (p^24 - 1)/r = (p^12 - 1) * (p^4 + 1) * (p^8 - p^4 + 1)/r

      Easy part: f^{(p^12 - 1) * (p^4 + 1)}
        - p^12 - 1: use f^{p^12} = conjugate(f) since
          the p^12 Frobenius acts as conjugation on Fp24
          (Fp24 is degree 2 over the fixed field of p^12).
        - p^4 + 1: use Frobenius-p^4 + identity.

      Hard part: result^{(p^8 - p^4 + 1)/r}
        Using the Hayashida-Hayasaka-Teruya formula (ePrint 2020/875):
          3 * (p^8 - p^4 + 1)/r
            = (u-1)^2 * (u+p) * (u^2+p^2) * (u^4+p^4-1) + 3

        The cofactor 3 is absorbed because 3 | (p-1) and the
        easy part already ensures the result is in the correct subgroup. *)

  (** Easy part: f^{(p^12 - 1) * (p^4 + 1)}.

      Step 1: f^{p^12 - 1} = conjugate(f) * f^{-1}
      Step 2: result^{p^4 + 1} = frobenius_p4(result) * result *)
  Definition final_exp_easy (f : Fp24) : Fp24 :=
    (* f^{p^12 - 1} *)
    let f_conj := fp24_conjugate p f in
    let f_inv := fp24_inv f in
    let r1 := fp24_mul p f_conj f_inv in
    (* r1^{p^4 + 1} *)
    let r1_p4 := fp24_frob_p4 r1 in
    fp24_mul p r1_p4 r1.

  (** Hard part using the addition chain decomposition:
        3 * (p^8 - p^4 + 1)/r = (u-1)^2 * (u+p) * (u^2+p^2) * (u^4+p^4-1) + 3 *)
  Definition final_exp_hard (f : Fp24) : Fp24 :=
    let t0 := fp24_pow_z f in
    let t1 := fp24_mul p t0 (fp24_conjugate p f) in
    let t2 := fp24_pow_z t1 in
    let t3 := fp24_mul p t2 (fp24_conjugate p t1) in
    let t4 := fp24_pow_z t3 in
    let t5 := fp24_frob t3 in
    let t6 := fp24_mul p t4 t5 in
    let t7 := fp24_pow_z t6 in
    let t8 := fp24_pow_z t7 in
    let t9 := fp24_frob_p2 t6 in
    let t10 := fp24_mul p t8 t9 in
    let t11 := fp24_pow_z t10 in
    let t12 := fp24_pow_z t11 in
    let t13 := fp24_pow_z t12 in
    let t14 := fp24_pow_z t13 in
    let t15 := fp24_frob_p4 t10 in
    let t16 := fp24_mul p t14 t15 in
    let t17 := fp24_conjugate p t10 in
    let t18 := fp24_mul p t16 t17 in
    let f_sq := fp24_sqr f in
    let f_cubed := fp24_mul p f_sq f in
    fp24_mul p t18 f_cubed.

  (** Complete final exponentiation: easy part followed by hard part. *)
  Definition final_exponentiation (f : Fp24) : Fp24 :=
    let easy := final_exp_easy f in
    final_exp_hard easy.

  (* ================================================================ *)
  (** ** Top-level pairing function                                    *)
  (* ================================================================ *)

  (** Compute the optimal Ate pairing e(P, Q).
      Returns an element of GT, a subgroup of the multiplicative group of Fp24. *)
  Definition pairing (P : G1Affine) (Q : G2Affine) : Fp24 :=
    let f := miller_loop P Q in
    final_exponentiation f.

  (** Negate a G1 affine point (negate the y-coordinate). *)
  Definition g1_neg (P : G1Affine) : G1Affine :=
    mk_g1_affine (g1_x P) (-f g1_y P) (g1_infinity P).

  (** Negate a G2 affine point (negate the y-coordinate). *)
  Definition g2_neg (Q : G2Affine) : G2Affine :=
    mk_g2_affine (g2_x Q) (fp4_neg p (g2_y Q)) (g2_infinity Q).

  (** Pairing check: e(P1, Q1) == e(P2, Q2).
      Computed as e(P1, Q1) * e(-P2, Q2) == 1, using a single
      final exponentiation on the product of Miller loop values. *)
  Variable fp24_eq_dec : forall (a b : Fp24), {a = b} + {a <> b}.

  Definition fp24_is_one (a : Fp24) : bool :=
    if fp24_eq_dec a (fp24_one p) then true else false.

  Definition pairing_check (P1 : G1Affine) (Q1 : G2Affine)
    (P2 : G1Affine) (Q2 : G2Affine) : bool :=
    let f1 := miller_loop P1 Q1 in
    let f2 := miller_loop (g1_neg P2) Q2 in
    let f := fp24_mul p f1 f2 in
    let result := final_exponentiation f in
    fp24_is_one result.

End BLS24_Pairing.
