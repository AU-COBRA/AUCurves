(** * Fp6 = Fp2[v]/(v^3 - xi) arithmetic, parameterized by β and ξ.

    Elements are triples (c0, c1, c2) representing c0 + c1*v + c2*v^2
    where v^3 = xi in Fp2.

    The base field Fp2 = Fp[u]/(u^2 - β) with quadratic non-residue β.
    For BLS12-381: β = -1, ξ = 1+u = (1,1).
    For BLS12-377: β = -5, ξ = u = (0,1).
*)

From Stdlib Require Import ZArith.
Require Import Crypto.Spec.ModularArithmetic.

Section BLS12_Fp6.
  Variable p : positive.

  (** Fp2 extension parameters:
      β is the quadratic non-residue (u^2 = β in Fp2).
      ξ = (xi_re, xi_im) is the cubic non-residue in Fp2 (v^3 = ξ in Fp6). *)
  Variable beta : F p.
  Variable xi_re : F p.
  Variable xi_im : F p.

  (** Notations for base field Fp arithmetic. *)
  Local Notation F := (F p).
  Local Notation "x +f y" := (@F.add p x y) (at level 50, left associativity).
  Local Notation "x *f y" := (@F.mul p x y) (at level 40, left associativity).
  Local Notation "x -f y" := (@F.sub p x y) (at level 50, left associativity).
  Local Notation "-f x" := (@F.opp p x) (at level 35, right associativity).
  Local Notation "0f" := (@F.zero p).
  Local Notation "1f" := (@F.one p).

  (* ================================================================ *)
  (** ** Fp2 = Fp[u]/(u^2 - β)                                       *)
  (* ================================================================ *)

  (** An Fp2 element (a0, a1) represents a0 + a1*u where u^2 = β. *)
  Local Notation Fp2 := (F * F)%type.

  Definition fp2_zero : Fp2 := (0f, 0f).
  Definition fp2_one  : Fp2 := (1f, 0f).

  Definition fp2_add (a b : Fp2) : Fp2 :=
    (fst a +f fst b, snd a +f snd b).

  Definition fp2_sub (a b : Fp2) : Fp2 :=
    (fst a -f fst b, snd a -f snd b).

  Definition fp2_neg (a : Fp2) : Fp2 :=
    (-f fst a, -f snd a).

  (** Fp2 multiplication: (a0 + a1*u)(b0 + b1*u) = (a0*b0 + β*a1*b1) + (a0*b1 + a1*b0)*u
      using u^2 = β. *)
  Definition fp2_mul (a b : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let b0 := fst b in let b1 := snd b in
    (a0 *f b0 +f beta *f a1 *f b1,
     a0 *f b1 +f a1 *f b0).

  (** Fp2 squaring: (a0 + a1*u)^2 = (a0^2 + β*a1^2) + 2*a0*a1*u. *)
  Definition fp2_sqr (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    (a0 *f a0 +f beta *f a1 *f a1,
     a0 *f a1 +f a0 *f a1).

  (** Fp2 conjugation (Frobenius on Fp2): (a0, a1) -> (a0, -a1). *)
  Definition fp2_conjugate (a : Fp2) : Fp2 :=
    (fst a, -f snd a).

  (** Fp2 inverse: (a0 + a1*u)^{-1} = (a0, -a1) / (a0^2 - β*a1^2).
      The norm is a0^2 - β*a1^2. *)
  Definition fp2_inv (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    let norm := a0 *f a0 -f beta *f a1 *f a1 in
    let inv_norm := @F.inv p norm in
    (a0 *f inv_norm, (-f a1) *f inv_norm).

  (** Multiply by ξ = (xi_re, xi_im) in Fp2.
      (a0 + a1*u)(xi_re + xi_im*u) = (a0*xi_re + β*a1*xi_im) + (a0*xi_im + a1*xi_re)*u. *)
  Definition fp2_mul_xi (a : Fp2) : Fp2 :=
    let a0 := fst a in let a1 := snd a in
    (a0 *f xi_re +f beta *f a1 *f xi_im,
     a0 *f xi_im +f a1 *f xi_re).

  (** Scalar multiplication of Fp2 by an Fp element.
      (a0 + a1*u) * s = (a0*s) + (a1*s)*u. *)
  Definition fp2_mul_fp (a : Fp2) (s : F) : Fp2 :=
    (fst a *f s, snd a *f s).

  (** Fp2 division. *)
  Definition fp2_div (a b : Fp2) : Fp2 :=
    fp2_mul a (fp2_inv b).

  (* ================================================================ *)
  (** ** Fp6 = Fp2[v]/(v^3 - xi)                                     *)
  (* ================================================================ *)

  (** An Fp6 element ((c0, c1), c2) represents c0 + c1*v + c2*v^2
      where v^3 = xi = 1 + u.

      Note: (Fp2 * Fp2 * Fp2)%type is left-associated, i.e., ((Fp2 * Fp2) * Fp2).
      So for x : Fp6:
        c0 = fst (fst x)
        c1 = snd (fst x)
        c2 = snd x *)
  Local Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  (** Projections for readability. *)
  Definition fp6_c0 (x : Fp6) : Fp2 := fst (fst x).
  Definition fp6_c1 (x : Fp6) : Fp2 := snd (fst x).
  Definition fp6_c2 (x : Fp6) : Fp2 := snd x.

  (** Constructor. *)
  Definition fp6_build (c0 c1 c2 : Fp2) : Fp6 := ((c0, c1), c2).

  Definition fp6_zero : Fp6 := fp6_build fp2_zero fp2_zero fp2_zero.
  Definition fp6_one  : Fp6 := fp6_build fp2_one  fp2_zero fp2_zero.

  (** Componentwise addition. *)
  Definition fp6_add (a b : Fp6) : Fp6 :=
    fp6_build (fp2_add (fp6_c0 a) (fp6_c0 b))
              (fp2_add (fp6_c1 a) (fp6_c1 b))
              (fp2_add (fp6_c2 a) (fp6_c2 b)).

  (** Componentwise subtraction. *)
  Definition fp6_sub (a b : Fp6) : Fp6 :=
    fp6_build (fp2_sub (fp6_c0 a) (fp6_c0 b))
              (fp2_sub (fp6_c1 a) (fp6_c1 b))
              (fp2_sub (fp6_c2 a) (fp6_c2 b)).

  (** Componentwise negation. *)
  Definition fp6_neg (a : Fp6) : Fp6 :=
    fp6_build (fp2_neg (fp6_c0 a))
              (fp2_neg (fp6_c1 a))
              (fp2_neg (fp6_c2 a)).

  (** Multiply by v in Fp6.
      v * (c0 + c1*v + c2*v^2) = ξ*c2 + c0*v + c1*v^2
      since v^3 = ξ. *)
  Definition fp6_mul_by_v (a : Fp6) : Fp6 :=
    fp6_build (fp2_mul_xi (fp6_c2 a))
              (fp6_c0 a)
              (fp6_c1 a).

  (** Fp6 multiplication using Karatsuba-like formula.

      (a0 + a1*v + a2*v^2)(b0 + b1*v + b2*v^2):
        c0 = a0*b0 + xi*((a1+a2)(b1+b2) - a1*b1 - a2*b2)
        c1 = (a0+a1)(b0+b1) - a0*b0 - a1*b1 + xi*(a2*b2)
        c2 = (a0+a2)(b0+b2) - a0*b0 - a2*b2 + a1*b1 *)
  Definition fp6_mul (a b : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let b0 := fp6_c0 b in let b1 := fp6_c1 b in let b2 := fp6_c2 b in
    let a0b0 := fp2_mul a0 b0 in
    let a1b1 := fp2_mul a1 b1 in
    let a2b2 := fp2_mul a2 b2 in
    (* c0 = a0*b0 + xi*((a1+a2)(b1+b2) - a1*b1 - a2*b2) *)
    let t0 := fp2_sub (fp2_sub (fp2_mul (fp2_add a1 a2) (fp2_add b1 b2))
                                a1b1) a2b2 in
    let c0 := fp2_add a0b0 (fp2_mul_xi t0) in
    (* c1 = (a0+a1)(b0+b1) - a0*b0 - a1*b1 + xi*(a2*b2) *)
    let t1 := fp2_sub (fp2_sub (fp2_mul (fp2_add a0 a1) (fp2_add b0 b1))
                                a0b0) a1b1 in
    let c1 := fp2_add t1 (fp2_mul_xi a2b2) in
    (* c2 = (a0+a2)(b0+b2) - a0*b0 - a2*b2 + a1*b1 *)
    let t2 := fp2_sub (fp2_sub (fp2_mul (fp2_add a0 a2) (fp2_add b0 b2))
                                a0b0) a2b2 in
    let c2 := fp2_add t2 a1b1 in
    fp6_build c0 c1 c2.

  (** Fp6 squaring using Chung-Hasan SQR3 formula.

      For a = a0 + a1*v + a2*v^2:
        s0 = a0^2
        s1 = 2*a0*a1
        s2 = (a0 - a1 + a2)^2
        s3 = 2*a1*a2
        s4 = a2^2
        c0 = s0 + xi*s3
        c1 = s1 + xi*s4
        c2 = s1 + s2 + s3 - s0 - s4 *)
  Definition fp6_sqr (a : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let s0 := fp2_mul a0 a0 in
    let ab := fp2_mul a0 a1 in
    let s1 := fp2_add ab ab in                                   (* 2*a0*a1 *)
    let s2 := fp2_mul (fp2_add (fp2_sub a0 a1) a2)              (* (a0 - a1 + a2)^2 *)
                      (fp2_add (fp2_sub a0 a1) a2) in
    let bc := fp2_mul a1 a2 in
    let s3 := fp2_add bc bc in                                   (* 2*a1*a2 *)
    let s4 := fp2_mul a2 a2 in
    let c0 := fp2_add s0 (fp2_mul_xi s3) in
    let c1 := fp2_add s1 (fp2_mul_xi s4) in
    let c2 := fp2_sub (fp2_sub (fp2_add (fp2_add s1 s2) s3) s0) s4 in
    fp6_build c0 c1 c2.

  (** Fp6 inverse using the cubic extension inverse formula.

      For a = a0 + a1*v + a2*v^2:
        A = a0^2 - xi*(a1*a2)
        B = xi*(a2^2) - a0*a1
        C = a1^2 - a0*a2
        F = a0*A + xi*(a2*B + a1*C)
        result = (A/F, B/F, C/F) *)
  Definition fp6_inv (a : Fp6) : Fp6 :=
    let a0 := fp6_c0 a in let a1 := fp6_c1 a in let a2 := fp6_c2 a in
    let c0_sq := fp2_mul a0 a0 in
    let c1_sq := fp2_mul a1 a1 in
    let c2_sq := fp2_mul a2 a2 in
    let c0c1  := fp2_mul a0 a1 in
    let c0c2  := fp2_mul a0 a2 in
    let c1c2  := fp2_mul a1 a2 in
    (* A = a0^2 - xi*(a1*a2) *)
    let A := fp2_sub c0_sq (fp2_mul_xi c1c2) in
    (* B = xi*(a2^2) - a0*a1 *)
    let B := fp2_sub (fp2_mul_xi c2_sq) c0c1 in
    (* C = a1^2 - a0*a2 *)
    let C := fp2_sub c1_sq c0c2 in
    (* F = a0*A + xi*(a2*B + a1*C) *)
    let FF := fp2_add (fp2_mul a0 A)
                      (fp2_mul_xi (fp2_add (fp2_mul a2 B) (fp2_mul a1 C))) in
    let FF_inv := fp2_inv FF in
    fp6_build (fp2_mul A FF_inv) (fp2_mul B FF_inv) (fp2_mul C FF_inv).

  (** Fp6 division. *)
  Definition fp6_div (a b : Fp6) : Fp6 :=
    fp6_mul a (fp6_inv b).

  (** Multiply Fp6 element componentwise by an Fp2 scalar. *)
  Definition fp6_mul_fp2 (a : Fp6) (s : Fp2) : Fp6 :=
    fp6_build (fp2_mul (fp6_c0 a) s)
              (fp2_mul (fp6_c1 a) s)
              (fp2_mul (fp6_c2 a) s).

  (* ================================================================ *)
  (** ** Frobenius endomorphisms                                      *)
  (* ================================================================ *)

  (** Frobenius constants -- to be instantiated for BLS12-381.

      gamma1   = xi^{(p-1)/3}      in Fp2    (for Frobenius)
      gamma2   = xi^{2(p-1)/3}     in Fp2    (for Frobenius)
      gamma1_p2 = xi^{(p^2-1)/3}   in Fp2    (for Frobenius squared)
      gamma2_p2 = xi^{2(p^2-1)/3}  in Fp2    (for Frobenius squared) *)
  Variable frobenius_gamma1    : Fp2.
  Variable frobenius_gamma2    : Fp2.
  Variable frobenius_gamma1_p2 : Fp2.
  Variable frobenius_gamma2_p2 : Fp2.

  (** Frobenius endomorphism (raise to p-th power) on Fp6.

      For a = c0 + c1*v + c2*v^2:
        phi(a) = conj(c0) + conj(c1)*gamma1*v + conj(c2)*gamma2*v^2

      where conj is the Fp2 conjugation (Frobenius on Fp2). *)
  Definition fp6_frobenius (a : Fp6) : Fp6 :=
    let c0 := fp2_conjugate (fp6_c0 a) in
    let c1 := fp2_mul (fp2_conjugate (fp6_c1 a)) frobenius_gamma1 in
    let c2 := fp2_mul (fp2_conjugate (fp6_c2 a)) frobenius_gamma2 in
    fp6_build c0 c1 c2.

  (** Frobenius squared (raise to p^2) on Fp6.

      For a = c0 + c1*v + c2*v^2:
        phi^2(a) = c0 + c1*gamma1_p2*v + c2*gamma2_p2*v^2

      The Fp2 conjugation applied twice is the identity, so c0, c1, c2
      are unchanged except for multiplication by the gamma constants. *)
  Definition fp6_frobenius_p2 (a : Fp6) : Fp6 :=
    fp6_build (fp6_c0 a)
              (fp2_mul (fp6_c1 a) frobenius_gamma1_p2)
              (fp2_mul (fp6_c2 a) frobenius_gamma2_p2).

End BLS12_Fp6.
