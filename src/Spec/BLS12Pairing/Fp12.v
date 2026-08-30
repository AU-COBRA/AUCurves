(* Fp12 = Fp6[w]/(w^2 - v) arithmetic, parameterized by β and ξ.
 *
 * Imports Fp2 and Fp6 definitions from Fp6.v to ensure definitional
 * equality between BLS12Fp12Spec.fp6_* and BLS12Fp6Spec.fp6_*.
 *
 * Tower of extensions:
 *   Fp2 = Fp[u]/(u^2 - β)
 *   Fp6 = Fp2[v]/(v^3 - ξ)
 *   Fp12 = Fp6[w]/(w^2 - v)
 *)

From Stdlib Require Import ZArith BinPos List.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Algebra.Ring.
Require Import Spec.BLS12Pairing.Fp6.

Import ListNotations.

Section BLS12_Fp12.
  Variable p : positive.
  Variable beta : F p.
  Variable xi_re : F p.
  Variable xi_im : F p.

  (* Re-export Fp2/Fp6 types and operations from Fp6.v *)
  Notation F := (F p).
  Notation Fp2 := (F * F)%type.
  Notation Fp6 := (Fp2 * Fp2 * Fp2)%type.

  (* Re-export Fp2 operations from Fp6.v *)
  Let fp2_zero := Fp6.fp2_zero p.
  Let fp2_one  := Fp6.fp2_one p.
  Let fp2_add  := Fp6.fp2_add p.
  Let fp2_sub  := Fp6.fp2_sub p.
  Let fp2_neg  := Fp6.fp2_neg p.
  Let fp2_mul  := Fp6.fp2_mul p beta.
  Let fp2_sqr  := Fp6.fp2_sqr p beta.
  Let fp2_inv  := Fp6.fp2_inv p beta.
  Let fp2_conjugate := Fp6.fp2_conjugate p.
  Let fp2_mul_xi := Fp6.fp2_mul_xi p beta xi_re xi_im.
  Let fp2_mul_fp := Fp6.fp2_mul_fp p.

  (* Re-export Fp6 operations from Fp6.v *)
  Let fp6_c0 := Fp6.fp6_c0 p.
  Let fp6_c1 := Fp6.fp6_c1 p.
  Let fp6_c2 := Fp6.fp6_c2 p.
  Let mk_fp6 := Fp6.fp6_build p.
  Let fp6_zero := Fp6.fp6_zero p.
  Let fp6_one  := Fp6.fp6_one p.
  Let fp6_add  := Fp6.fp6_add p.
  Let fp6_sub  := Fp6.fp6_sub p.
  Let fp6_neg  := Fp6.fp6_neg p.
  Let fp6_mul_by_v := Fp6.fp6_mul_by_v p beta xi_re xi_im.
  Let fp6_mul  := Fp6.fp6_mul p beta xi_re xi_im.
  Let fp6_sqr  := Fp6.fp6_sqr p beta xi_re xi_im.
  Let fp6_mul_fp2 := Fp6.fp6_mul_fp2 p beta.
  Let fp6_inv  := Fp6.fp6_inv p beta xi_re xi_im.

  (* Frobenius constants *)
  Variable frobenius_gamma1 : Fp2.
  Variable frobenius_gamma2 : Fp2.
  Variable frobenius_gamma1_p2 : Fp2.
  Variable frobenius_gamma2_p2 : Fp2.

  Let fp6_frobenius := Fp6.fp6_frobenius p beta frobenius_gamma1 frobenius_gamma2.
  Let fp6_frobenius_p2 := Fp6.fp6_frobenius_p2 p beta frobenius_gamma1_p2 frobenius_gamma2_p2.

  (* ================================================================== *)
  (* Fp12 = Fp6[w]/(w^2 - v)                                           *)
  (* Elements: c0 + c1*w  stored as (c0, c1)                           *)
  (* Key relation: w^2 = v (the "v" element of Fp6)                    *)
  (* ================================================================== *)

  Notation Fp12 := (Fp6 * Fp6)%type.

  Definition fp12_c0 (x : Fp12) : Fp6 := fst x.
  Definition fp12_c1 (x : Fp12) : Fp6 := snd x.
  Definition mk_fp12 (c0 c1 : Fp6) : Fp12 := (c0, c1).

  Definition fp12_zero : Fp12 := mk_fp12 fp6_zero fp6_zero.
  Definition fp12_one  : Fp12 := mk_fp12 fp6_one fp6_zero.

  Definition fp12_add (a b : Fp12) : Fp12 :=
    mk_fp12 (fp6_add (fp12_c0 a) (fp12_c0 b))
             (fp6_add (fp12_c1 a) (fp12_c1 b)).

  Definition fp12_sub (a b : Fp12) : Fp12 :=
    mk_fp12 (fp6_sub (fp12_c0 a) (fp12_c0 b))
             (fp6_sub (fp12_c1 a) (fp12_c1 b)).

  Definition fp12_neg (a : Fp12) : Fp12 :=
    mk_fp12 (fp6_neg (fp12_c0 a))
             (fp6_neg (fp12_c1 a)).

  (* Fp12 multiplication using Karatsuba:
       v0 = a0*b0, v1 = a1*b1
       c0 = v0 + mul_by_v(v1)       -- since w^2 = v
       c1 = (a0+a1)(b0+b1) - v0 - v1 *)
  Definition fp12_mul (a b : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let b0 := fp12_c0 b in let b1 := fp12_c1 b in
    let v0 := fp6_mul a0 b0 in
    let v1 := fp6_mul a1 b1 in
    let c0 := fp6_add v0 (fp6_mul_by_v v1) in
    let c1 := fp6_sub (fp6_sub (fp6_mul (fp6_add a0 a1)
                                         (fp6_add b0 b1))
                                v0) v1 in
    mk_fp12 c0 c1.

  (* Fp12 squaring:
       c0 = a0^2 + mul_by_v(a1^2)
       c1 = 2*a0*a1 *)
  (* Note: uses fp6_mul x x instead of fp6_sqr x to match the
     AbstractField.Fsquare = fun x => Fmul x x definition used by
     the WP proofs. Correctness is the same. *)
  Definition fp12_sqr (a : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let a0_sq := fp6_mul a0 a0 in
    let a1_sq := fp6_mul a1 a1 in
    let cross := fp6_mul a0 a1 in
    let c0 := fp6_add a0_sq (fp6_mul_by_v a1_sq) in
    let c1 := fp6_add cross cross in
    mk_fp12 c0 c1.

  (* Conjugation: (a0, -a1) — cheap inverse for cyclotomic subgroup *)
  Definition fp12_conjugate (a : Fp12) : Fp12 :=
    mk_fp12 (fp12_c0 a) (fp6_neg (fp12_c1 a)).

  (* Full Fp12 inverse using quadratic norm:
       norm = a0^2 - v*a1^2
       result = (a0 * norm_inv, -a1 * norm_inv) *)
  Definition fp12_inv (a : Fp12) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let norm := fp6_sub (fp6_mul a0 a0) (fp6_mul_by_v (fp6_mul a1 a1)) in
    let norm_inv := fp6_inv norm in
    mk_fp12 (fp6_mul a0 norm_inv)
             (fp6_neg (fp6_mul a1 norm_inv)).

  (* ================================================================== *)
  (* Frobenius endomorphisms on Fp12                                    *)
  (* ================================================================== *)

  Variable w_frobenius_c1     : Fp2.  (* xi^{(p-1)/6}   *)
  Variable w_frobenius_p2_c1  : Fp2.  (* xi^{(p^2-1)/6} *)
  Variable w_frobenius_p3_c1  : Fp2.  (* xi^{(p^3-1)/6} *)

  Definition fp12_frobenius (a : Fp12) : Fp12 :=
    let c0' := fp6_frobenius (fp12_c0 a) in
    let c1' := fp6_mul_fp2 (fp6_frobenius (fp12_c1 a)) w_frobenius_c1 in
    mk_fp12 c0' c1'.

  Definition fp12_frobenius_p2 (a : Fp12) : Fp12 :=
    let c0' := fp6_frobenius_p2 (fp12_c0 a) in
    let c1' := fp6_mul_fp2 (fp6_frobenius_p2 (fp12_c1 a)) w_frobenius_p2_c1 in
    mk_fp12 c0' c1'.

  Definition fp12_frobenius_p3 (a : Fp12) : Fp12 :=
    let c0' := fp6_frobenius (fp6_frobenius_p2 (fp12_c0 a)) in
    let c1' := fp6_mul_fp2 (fp6_frobenius (fp6_frobenius_p2 (fp12_c1 a)))
                            w_frobenius_p3_c1 in
    mk_fp12 c0' c1'.

  (* ================================================================== *)
  (* Exponentiation                                                     *)
  (* ================================================================== *)

  Fixpoint fp12_pow_pos (base : Fp12) (e : positive) : Fp12 :=
    match e with
    | xH => base
    | xO e' => fp12_sqr (fp12_pow_pos base e')
    | xI e' => fp12_mul base (fp12_sqr (fp12_pow_pos base e'))
    end.

  Definition fp12_pow_nat (base : Fp12) (n : nat) : Fp12 :=
    match n with
    | O => fp12_one
    | S _ => fp12_pow_pos base (Pos.of_nat n)
    end.

  Definition fp12_pow_N (base : Fp12) (n : N) : Fp12 :=
    match n with
    | N0 => fp12_one
    | Npos e => fp12_pow_pos base e
    end.

  Definition fp12_pow_Z (base : Fp12) (z : Z) : Fp12 :=
    match z with
    | Z0 => fp12_one
    | Zpos e => fp12_pow_pos base e
    | Zneg e => fp12_inv (fp12_pow_pos base e)
    end.

  (* ================================================================== *)
  (* BLS12-381 parameter and power-by-x                                 *)
  (* ================================================================== *)

  Definition bls_x : Z := 0xd201000000010000.
  Definition bls_x_pos : positive := 0xd201000000010000%positive.

  Definition fp12_pow_bls_x (a : Fp12) : Fp12 :=
    fp12_pow_pos a bls_x_pos.

  Definition fp12_pow_bls_x_signed (a : Fp12) : Fp12 :=
    fp12_conjugate (fp12_pow_bls_x a).

  (* Cyclotomic squaring for elements in the cyclotomic subgroup.
     Uses the constraint f * conj(f) = 1, equivalently:
       c0^2 - v * c1^2 = 1
     to compute f^2 as:
       new_c0 = 1 + 2*v*c1^2
       new_c1 = 2*c0*c1

     This saves 1 Fp6_sqr compared to standard fp12_sqr.
     For elements NOT in the cyclotomic subgroup, this gives a WRONG result.
     It is only used inside pow_x after the easy part of final exponentiation
     has placed the element in the cyclotomic subgroup. *)
  Definition fp12_cyclotomic_sqr (f : Fp12) : Fp12 :=
    let c0 := fp12_c0 f in
    let c1 := fp12_c1 f in
    let c1_sq := fp6_mul c1 c1 in         (* c1^2 *)
    let cross := fp6_mul c0 c1 in         (* c0*c1 *)
    let v_c1_sq := fp6_mul_by_v c1_sq in  (* v*c1^2 *)
    let two_v_c1_sq := fp6_add v_c1_sq v_c1_sq in  (* 2*v*c1^2 *)
    let new_c0 := fp6_add fp6_one two_v_c1_sq in    (* 1 + 2*v*c1^2 *)
    let new_c1 := fp6_add cross cross in             (* 2*c0*c1 *)
    mk_fp12 new_c0 new_c1.

  (* Correctness of cyclotomic squaring:
     For f in the cyclotomic subgroup (f * conj(f) = fp12_one),
     cyclotomic_sqr f = fp12_sqr f.

     Proof sketch: The cyclotomic constraint gives
       c0^2 - v*c1^2 = 1
     Standard squaring gives:
       new_c0 = c0^2 + v*c1^2 = (1 + v*c1^2) + v*c1^2 = 1 + 2*v*c1^2
     which matches cyclotomic_sqr. For c1: both give 2*c0*c1. *)
  (* Register the ring tactic for F p *)
  Local Lemma Fp_ring_theory : Ring_theory.ring_theory (F.zero) (F.one) (@F.add p) (@F.mul p) (@F.sub p) (@F.opp p) eq.
  Proof. exact (Algebra.Ring.ring_theory_for_stdlib_tactic (zero:=F.zero) (one:=F.one)). Qed.
  Add Ring Fp_ring : Fp_ring_theory.

  (* Fp6 ring lemma: x * (-y) = -(x * y).
     Proved by unfolding to Fp2 components and using Fp ring. *)
  Local Lemma fp6_mul_neg_r : forall x y,
    fp6_mul x (fp6_neg y) = fp6_neg (fp6_mul x y).
  Proof.
    intros [[xa xb] xc] [[ya yb] yc].
    unfold fp6_mul, fp6_neg, fp6_add, fp6_sub, fp6_mul_by_v,
           Fp6.fp6_mul, Fp6.fp6_neg, Fp6.fp6_add, Fp6.fp6_sub, Fp6.fp6_mul_by_v,
           Fp6.fp6_c0, Fp6.fp6_c1, Fp6.fp6_c2, fp6_build, Fp6.fp6_build.
    unfold fp2_add, fp2_sub, fp2_neg, fp2_mul, fp2_mul_xi,
           Fp6.fp2_add, Fp6.fp2_sub, Fp6.fp2_neg, Fp6.fp2_mul, Fp6.fp2_mul_xi.
    destruct xa as [a0 a1]. destruct xb as [a2 a3]. destruct xc as [a4 a5].
    destruct ya as [b0 b1]. destruct yb as [b2 b3]. destruct yc as [b4 b5].
    simpl fst. simpl snd.
    repeat (f_equal; try ring).
  Qed.

  Local Lemma fp6_mul_by_v_neg : forall x,
    fp6_mul_by_v (fp6_neg x) = fp6_neg (fp6_mul_by_v x).
  Proof.
    intros [[xa xb] xc].
    unfold fp6_mul_by_v, fp6_neg, Fp6.fp6_mul_by_v, Fp6.fp6_neg,
           Fp6.fp6_c0, Fp6.fp6_c1, Fp6.fp6_c2, fp6_build, Fp6.fp6_build.
    unfold fp2_neg, fp2_mul_xi, Fp6.fp2_neg, Fp6.fp2_mul_xi.
    destruct xa as [a0 a1]. destruct xb as [a2 a3]. destruct xc as [a4 a5].
    simpl fst. simpl snd.
    repeat (f_equal; try ring).
  Qed.

  Local Lemma fp6_add_neg_is_sub : forall x y, fp6_add x (fp6_neg y) = fp6_sub x y.
  Proof.
    intros [[xa xb] xc] [[ya yb] yc].
    unfold fp6_add, fp6_neg, fp6_sub, Fp6.fp6_add, Fp6.fp6_neg, Fp6.fp6_sub,
           Fp6.fp6_c0, Fp6.fp6_c1, Fp6.fp6_c2, fp6_build, Fp6.fp6_build,
           fp2_add, fp2_neg, fp2_sub, Fp6.fp2_add, Fp6.fp2_neg, Fp6.fp2_sub.
    destruct xa as [a0 a1]. destruct xb as [a2 a3]. destruct xc as [a4 a5].
    destruct ya as [b0 b1]. destruct yb as [b2 b3]. destruct yc as [b4 b5].
    simpl fst. simpl snd.
    repeat (f_equal; try ring).
  Qed.

  (* Fp6 lemmas needed for cyclotomic proof — avoid unfolding fp6_mul *)
  Local Lemma fp6_sub_eq_add : forall a b c,
    fp6_sub a b = c -> a = fp6_add c b.
  Proof.
    intros [[xa xb] xc] [[ya yb] yc] [[za zb] zc] H.
    unfold fp6_sub, fp6_add, Fp6.fp6_sub, Fp6.fp6_add,
           Fp6.fp6_c0, Fp6.fp6_c1, Fp6.fp6_c2, fp6_build, Fp6.fp6_build,
           fp2_sub, fp2_add, Fp6.fp2_sub, Fp6.fp2_add in *.
    destruct xa as [a0 a1]. destruct xb as [a2 a3]. destruct xc as [a4 a5].
    destruct ya as [b0 b1]. destruct yb as [b2 b3]. destruct yc as [b4 b5].
    destruct za as [c0 c1]. destruct zb as [c2 c3]. destruct zc as [c4 c5].
    simpl in *.
    injection H as H0 H1 H2 H3 H4 H5. subst.
    f_equal; [f_equal |]; f_equal; ring.
  Qed.

  Local Lemma fp6_add_assoc : forall a b c,
    fp6_add a (fp6_add b c) = fp6_add (fp6_add a b) c.
  Proof.
    intros [[xa xb] xc] [[ya yb] yc] [[za zb] zc].
    unfold fp6_add, Fp6.fp6_add, Fp6.fp6_c0, Fp6.fp6_c1, Fp6.fp6_c2,
           fp6_build, Fp6.fp6_build, fp2_add, Fp6.fp2_add.
    destruct xa as [a0 a1]. destruct xb as [a2 a3]. destruct xc as [a4 a5].
    destruct ya as [b0 b1]. destruct yb as [b2 b3]. destruct yc as [b4 b5].
    destruct za as [c0 c1]. destruct zb as [c2 c3]. destruct zc as [c4 c5].
    simpl in *.
    f_equal; [f_equal |]; f_equal; ring.
  Qed.

  Lemma fp12_cyclotomic_sqr_correct : forall f,
    fp12_mul f (fp12_conjugate f) = mk_fp12 fp6_one fp6_zero ->
    fp12_cyclotomic_sqr f = fp12_sqr f.
  Proof.
    intros f Hcyc.
    unfold fp12_cyclotomic_sqr, fp12_sqr, fp12_mul, fp12_conjugate, mk_fp12,
           fp12_c0, fp12_c1 in *.
    simpl fst in *. simpl snd in *.
    (* c1 components are identical *)
    f_equal.
    (* c0: need 1 + 2*v*c1² = c0² + v*c1² *)
    apply (f_equal fst) in Hcyc. simpl fst in Hcyc.
    rewrite fp6_mul_neg_r in Hcyc.
    rewrite fp6_mul_by_v_neg in Hcyc.
    rewrite fp6_add_neg_is_sub in Hcyc.
    (* Hcyc: fp6_sub c0² (v*c1²) = 1 *)
    apply fp6_sub_eq_add in Hcyc.
    (* Hcyc: c0² = fp6_add 1 (v*c1²) *)
    rewrite Hcyc.
    (* Goal: fp6_add 1 (fp6_add (v*c1²) (v*c1²)) = fp6_add (fp6_add 1 (v*c1²)) (v*c1²) *)
    apply fp6_add_assoc.
  Qed.

  (* ================================================================== *)
  (* Sparse multiplication (for pairing line functions)                 *)
  (* ================================================================== *)

  Definition fp12_mul_by_024 (a : Fp12) (ell0 ell2 ell4 : Fp2) : Fp12 :=
    let a0 := fp12_c0 a in let a1 := fp12_c1 a in
    let b := mk_fp6 ell0 ell2 fp2_zero in
    let b1_c0 := ell4 in
    let t0 := fp6_mul a0 b in
    let t1 := fp6_mul_fp2 a1 b1_c0 in
    let c0 := fp6_add t0 (fp6_mul_by_v t1) in
    let t2 := fp6_mul a1 b in
    let t3 := fp6_mul_fp2 a0 b1_c0 in
    let c1 := fp6_add t2 t3 in
    mk_fp12 c0 c1.

End BLS12_Fp12.
