(** * Projective.v — curve-generic PROJECTIVE Miller loop in Gallina.

    Sibling of [Affine.v].  Same parameters ([FieldOps]), same loop
    structure, but the running point [T] carries projective coordinates
    [(X, Y, Z)] instead of affine [(x, y)].  This eliminates the
    [Fp2_inv] inside every doubling and addition step — the dominant
    algorithmic cost of [affine_miller] on BN254 (~1 us per step *
    ~70 steps * 2 = ~140 us, i.e.\ most of the 12.5x Miller-loop gap
    vs.\ arkworks; see the BN254 evaluation in the report).

    The line is now a function of the projective coordinates of [T]
    AND the slope, so [FieldOps] grows a [make_line_proj] companion
    to the existing [make_line] (we keep the latter so [Affine.v]
    instances still build).

    Two more additions to [FieldOps]:
    - [fp12_mul_by_line]: sparse multiplication
        Fp12 * (sparse Fp12 from a line) -> Fp12
      Lines have non-zero entries in only 6 of 12 Fp components, so a
      specialised multiplier is roughly 2x faster than the generic
      [fp12_mul].  Curves that have not yet implemented a sparse
      multiplier can pass the dense [fp12_mul] composed with
      [make_line_proj] — they pay the speed penalty but the
      correctness theorem still goes through.

    Equivalence with [affine_miller] (and through it, with the L1
    divisor-theoretic Miller function from [MillerFunction.v]) is
    stated in [MillerEquiv.v] as
      [projective_miller_eq_affine].
    The proof obligations are: (a) projective ↔ affine point equality
    after each step (standard E projective formulas), and (b)
    [fp12_mul_by_line] = [fp12_mul ∘ make_line_proj] (a per-instance
    sparse-vs-dense soundness lemma). *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.
Require Import Bedrock.Field.PairingTheory.Affine.

Local Open Scope Z_scope.

(** Extra projective field ops, on top of [FieldOps] from [Affine.v].
    A curve whose [feval_ops : FieldOps Fp Fp2 Fp12] already exists
    builds a [ProjFieldOps] by adding three functions.

    Doubling and addition need separate line builders because the
    affine slope ([3X^2 / 2Y] vs.\ [(Qy - Ty) / (Qx - Tx)]) has a
    different denominator structure in projective coordinates: doubling
    divides by [2YZ], addition by [Qx*Z^2 - X].  Splitting the line
    builder along that boundary lets each curve's spec implementation
    apply the right normalisation, and lets the fast (sparse) instance
    use the optimal Bernstein--Lange line formula for each. *)
Record ProjFieldOps (Fp Fp2 Fp12 : Type) : Type := {
  base_ops : FieldOps Fp Fp2 Fp12;

  (** Doubling line builder.
      Inputs: T_old = (TX, TY, TZ) projective (3 * Fp2),
              T_new = (NX, NY, NZ) projective (3 * Fp2) — the doubled point,
              P = (Px, Py) affine (2 * Fp).
      Output: Fp12 line in the curve's twist basis. *)
  make_line_proj_double :
    Fp2 -> Fp2 -> Fp2 ->
    Fp2 -> Fp2 -> Fp2 ->
    Fp -> Fp -> Fp12;

  (** Mixed-addition line builder.
      Inputs: T_old = (TX, TY, TZ) projective (3 * Fp2),
              Q = (Qx, Qy) affine (2 * Fp2),
              T_new = (NX, NY, NZ) projective (3 * Fp2) — the sum point,
              P = (Px, Py) affine (2 * Fp). *)
  make_line_proj_add :
    Fp2 -> Fp2 -> Fp2 ->
    Fp2 -> Fp2 ->
    Fp2 -> Fp2 -> Fp2 ->
    Fp -> Fp -> Fp12;

  (** Sparse Fp12 mul.  [fp12_mul_by_line a sparse_b] computes
      [a * sparse_b] in the same basis the line builders use,
      skipping the 6 zero components of [sparse_b]. *)
  fp12_mul_by_line : Fp12 -> Fp12 -> Fp12;
}.

Arguments base_ops {Fp Fp2 Fp12} _.
Arguments make_line_proj_double {Fp Fp2 Fp12} _ _ _ _ _ _ _ _ _.
Arguments make_line_proj_add {Fp Fp2 Fp12} _ _ _ _ _ _ _ _ _ _.
Arguments fp12_mul_by_line {Fp Fp2 Fp12} _ _ _.

Section ProjectiveMiller.

  Context {Fp Fp2 Fp12 : Type}.
  Context (pops : ProjFieldOps Fp Fp2 Fp12).

  Let ops := base_ops pops.

  Local Notation "x +2 y" := (fp2_add  ops x y) (at level 50).
  Local Notation "x -2 y" := (fp2_sub  ops x y) (at level 50).
  Local Notation "x *2 y" := (fp2_mul  ops x y) (at level 40).
  Local Notation "x ^^2"  := (fp2_sqr  ops x)   (at level 30).

  (** Doubling step on E' in projective coordinates.
      Standard short-Weierstrass formulas (Bernstein--Lange) — no [b]
      term because the twist E' has the curve constant absorbed into
      the [3*X^2] tangent.  This matches the affine formula for a
      curve [y^2 = x^3 + a*x + b] with [a = 0] (BN/BLS family).

        A = X^2,  B = Y^2,  C = B^2
        D = 2*((X+B)^2 - A - C)
        E = 3*A
        F = E^2
        X' = F - 2*D
        Y' = E*(D - X') - 8*C
        Z' = 2*Y*Z

      The line for evaluation at P is [E*(X - X') - F + 8*C] in the
      x coordinate component, scaled by [Z'].  We delegate basis layout
      to [make_line_proj] and pass the slope numerator [E = 3*A] and
      the new [(X', Y', Z')] for it to encode. *)
  Definition double_step_proj
      (f : Fp12) (TX TY TZ : Fp2) (Px Py : Fp)
    : Fp12 * Fp2 * Fp2 * Fp2 :=
    let a   := TX ^^2 in
    let b   := TY ^^2 in
    let c   := b ^^2 in
    let xb  := TX +2 b in
    let d0  := xb ^^2 -2 a -2 c in
    let d   := d0 +2 d0 in
    let e   := a +2 a +2 a in
    let g   := e ^^2 in
    let nx  := g -2 d -2 d in
    let ny  := e *2 (d -2 nx) -2 (c +2 c +2 c +2 c +2 c +2 c +2 c +2 c) in
    let nz  := (TY +2 TZ) ^^2 -2 b -2 (TZ ^^2) in
    let line := make_line_proj_double pops TX TY TZ nx ny nz Px Py in
    let f2  := fp12_mul_by_line pops (fp12_sqr ops f) line in
    (f2, nx, ny, nz).

  (** Mixed addition on E' in projective coordinates: T (proj) + Q (affine).
      Bernstein--Lange mixed-addition formulas:

        Z1Z1 = TZ^2
        U2   = QX * Z1Z1
        S2   = QY * TZ * Z1Z1
        H    = U2 - TX
        HH   = H^2
        I    = 4*HH
        J    = H*I
        r    = 2*(S2 - TY)
        V    = TX*I
        X3   = r^2 - J - 2*V
        Y3   = r*(V - X3) - 2*TY*J
        Z3   = (TZ + H)^2 - Z1Z1 - HH

      The line numerator for [make_line_proj] is the chord slope
      [r] (= 2*(S2 - TY)). *)
  Definition add_step_proj
      (f : Fp12) (TX TY TZ Qx Qy : Fp2) (Px Py : Fp)
    : Fp12 * Fp2 * Fp2 * Fp2 :=
    let z1z1 := TZ ^^2 in
    let u2   := Qx *2 z1z1 in
    let s2   := Qy *2 TZ *2 z1z1 in
    let h    := u2 -2 TX in
    let hh   := h ^^2 in
    let i    := hh +2 hh +2 hh +2 hh in
    let j    := h *2 i in
    let r    := (s2 -2 TY) +2 (s2 -2 TY) in
    let v    := TX *2 i in
    let nx   := r ^^2 -2 j -2 v -2 v in
    let ny   := r *2 (v -2 nx) -2 ((TY *2 j) +2 (TY *2 j)) in
    let nz   := (TZ +2 h) ^^2 -2 z1z1 -2 hh in
    let line := make_line_proj_add pops TX TY TZ Qx Qy nx ny nz Px Py in
    let f'   := fp12_mul_by_line pops f line in
    (f', nx, ny, nz).

  (** [projective_miller_aux] is structurally identical to
      [affine_miller_aux] but threads three Fp2 components through the
      loop instead of two. *)
  Fixpoint projective_miller_aux
      (n : Z) (i : nat)
      (Px Py : Fp) (Qx Qy : Fp2)
      (f : Fp12) (TX TY TZ : Fp2)
    : Fp12 * Fp2 * Fp2 * Fp2 :=
    match i with
    | O => (f, TX, TY, TZ)
    | S i' =>
      let '(f1, TX1, TY1, TZ1) := double_step_proj f TX TY TZ Px Py in
      let '(f2, TX2, TY2, TZ2) :=
        if Z.testbit n (Z.of_nat i') then
          add_step_proj f1 TX1 TY1 TZ1 Qx Qy Px Py
        else
          (f1, TX1, TY1, TZ1)
      in
      projective_miller_aux n i' Px Py Qx Qy f2 TX2 TY2 TZ2
    end.

  (** Top-level projective Miller.  Initial T is Q lifted to projective
      coordinates: [(Qx, Qy, 1)].  All other arguments match
      [affine_miller]. *)
  Definition projective_miller
      (n : Z) (Px Py : Fp) (Qx Qy : Fp2) : Fp12 :=
    let nbits := Z.to_nat (Z.log2 n) in
    let '(f, _, _, _) :=
      projective_miller_aux n nbits Px Py Qx Qy
        (fp12_one ops) Qx Qy (fp2_one ops)
    in f.

End ProjectiveMiller.

(** ** Equivalence to [affine_miller] (statement; proof = future work).

    The two extra [ProjFieldOps] fields impose two soundness obligations
    on a concrete instance:

    Side condition 1 — [make_line_proj] agrees with [make_line] after
    Z-normalisation:
      [make_line_proj pops lambda TX TY TZ Px Py
        = make_line ops lambda (TX/TZ^2) (TY/TZ^3) Px Py]
      whenever TZ <> 0.

    Side condition 2 — [fp12_mul_by_line] is sound:
      [fp12_mul_by_line pops a (make_line_proj pops ...)
        = fp12_mul ops a (make_line_proj pops ...)].

    Together with the standard projective-vs-affine point identity
    after each [double_step] / [add_step], these imply
      [projective_miller pops n Px Py Qx Qy
        = affine_miller ops n Px Py Qx Qy]
    for any [n > 0] and [Q] not at infinity.  Stated and (eventually)
    discharged in [MillerEquiv.v]. *)
