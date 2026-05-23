(** * GnarkDoubleCorrect.v — gnark homogeneous doubleStep formula is the
    standard affine doubling, over an abstract field (Alternative-2 to
    the #14 equivalence: reuse fiat-crypto's field/fsatz machinery to
    discharge the curve-formula correctness, rather than proving the
    group law from scratch).

    We prove, over any field of characteristic ≥ 5 and a short
    Weierstrass curve [y² = x³ + b] (a = 0), that gnark's projective
    [doubleStep] formula on a homogeneous point [(X:Y:Z)] dehomogenises
    to the affine tangent-doubling [(λ²-2x, λ(x-x')-y)] with
    [λ = 3x²/2y], [x = X/Z], [y = Y/Z].

    This is the pure abstract-field core of [double_simulates] in
    [ProjAffineMultibase]; the BW6 instance discharges the field axioms
    for Fp3 and supplies the concrete G2 [b] (needs the BW6 tower, hence
    the prime — done separately). *)

Require Import Crypto.Util.Decidable Crypto.Algebra.Field.
Require Import Crypto.Util.Notations Crypto.Util.FixCoqMistakes.

Module GnarkDouble.
Section GnarkDouble.
  Context {F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {field:@Algebra.Hierarchy.field
                   F Feq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}
          {char_ge_5:@Ring.char_ge
                       F Feq Fzero Fone Fopp Fadd Fsub Fmul (BinPos.Pos.of_succ_nat 4)}
          {Feq_dec:DecidableRel Feq}.
  Local Infix "=" := Feq : type_scope.
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := Fzero.  Local Notation "1" := Fone.
  Local Infix "+" := Fadd.  Local Infix "-" := Fsub.
  Local Infix "*" := Fmul.  Local Infix "/" := Fdiv.

  (** gnark's projective [doubleStep] new point (X:Y:Z) -> (nx:ny:nz),
      transcribed from [bw6_761_g2_double_step] (half = 1/2).  The
      bedrock body has [E = 12C] = [b_twist·3C] with the BW6 G2 twist
      constant [b_twist = 4] baked in, so this holds for the curve
      [y² = x³ + 4] (a = 0, b = 4); the KATs confirm b_twist = 4. *)
  Lemma gnark_double_dehomog (X Y Z : F)
      (HZ : Z <> 0) (HY : Y <> 0)
      (Hon : Y * Y * Z = X * X * X + (1 + 1 + 1 + 1) * (Z * Z * Z)) :
    let half := Finv (1 + 1) in
    let B  := Y * Y in
    let C  := Z * Z in
    let D  := (C + C) + C in            (* 3C  *)
    let E  := (D + D) + (D + D) in      (* 12C *)
    let Fc := (E + E) + E in            (* 36C *)
    let G  := (B + Fc) * half in
    let H  := ((Y + Z) * (Y + Z)) - B - C in
    let EE := E * E in
    let K  := (EE + EE) + EE in
    let A  := (X * Y) * half in
    let nx := (B - Fc) * A in
    let ny := (G * G) - K in
    let nz := B * H in
    let x := X / Z in
    let y := Y / Z in
    let lam := ((X * X) + (X * X) + (X * X)) / ((Y + Y) * Z) in  (* 3x²/2y *)
    let new_x := (lam * lam) - x - x in
    (nx / nz = new_x) /\
    (ny / nz = lam * (x - new_x) - y).
  Proof.
    cbv beta zeta. split; fsatz.
  Qed.

  (** gnark's projective [addMixedStep]: T=(X:Y:Z) (proj) + A=(ax,ay)
      (affine) -> (nx:ny:nz), transcribed from [bw6_761_g2_add_step].
      The mixed-addition formula is curve-constant-free (a=0 chord
      addition), so it holds with no on-curve hypothesis — only [Z<>0]
      and distinct x-coords ([ax*Z <> X], i.e. the chord is not
      vertical). *)
  Lemma gnark_add_dehomog (X Y Z ax ay : F)
      (HZ : Z <> 0) (HL : ax * Z <> X) :
    let Y2Z1 := ay * Z in
    let O  := Y - Y2Z1 in
    let X2Z1 := ax * Z in
    let L  := X - X2Z1 in
    let C  := O * O in
    let D  := L * L in
    let E  := L * D in
    let Fc := Z * C in
    let G  := X * D in
    let H  := (E + Fc) - (G + G) in
    let t1 := Y * E in
    let nx := L * H in
    let ny := ((G - H) * O) - t1 in
    let nz := E * Z in
    let x := X / Z in
    let y := Y / Z in
    let lam := (ay - y) / (ax - x) in
    let new_x := (lam * lam) - x - ax in
    (nx / nz = new_x) /\
    (ny / nz = lam * (x - new_x) - y).
  Proof.
    cbv beta zeta. split; fsatz.
  Qed.

  (** On-curve preservation: the doubled point stays on [y²=x³+4]
      (homogeneous), so the dehomogenisation relation [rel] (which
      carries the on-curve invariant) is preserved across iterations. *)
  Lemma gnark_double_oncurve (X Y Z : F)
      (Hon : Y * Y * Z = X * X * X + (1 + 1 + 1 + 1) * (Z * Z * Z)) :
    let half := Finv (1 + 1) in
    let B  := Y * Y in
    let C  := Z * Z in
    let D  := (C + C) + C in
    let E  := (D + D) + (D + D) in
    let Fc := (E + E) + E in
    let G  := (B + Fc) * half in
    let H  := ((Y + Z) * (Y + Z)) - B - C in
    let EE := E * E in
    let K  := (EE + EE) + EE in
    let A  := (X * Y) * half in
    let nx := (B - Fc) * A in
    let ny := (G * G) - K in
    let nz := B * H in
    ny * ny * nz = nx * nx * nx + (1 + 1 + 1 + 1) * (nz * nz * nz).
  Proof.
    cbv beta zeta. fsatz.
  Qed.

  (** On-curve preservation for mixed addition (needs both T and the
      affine point A on the curve). *)
  Lemma gnark_add_oncurve (X Y Z ax ay : F)
      (HZ : Z <> 0)
      (HonT : Y * Y * Z = X * X * X + (1 + 1 + 1 + 1) * (Z * Z * Z))
      (HonA : ay * ay = ax * ax * ax + (1 + 1 + 1 + 1)) :
    let Y2Z1 := ay * Z in
    let O  := Y - Y2Z1 in
    let X2Z1 := ax * Z in
    let L  := X - X2Z1 in
    let C  := O * O in
    let D  := L * L in
    let E  := L * D in
    let Fc := Z * C in
    let G  := X * D in
    let H  := (E + Fc) - (G + G) in
    let t1 := Y * E in
    let nx := L * H in
    let ny := ((G - H) * O) - t1 in
    let nz := E * Z in
    ny * ny * nz = nx * nx * nx + (1 + 1 + 1 + 1) * (nz * nz * nz).
  Proof.
    cbv beta zeta. fsatz.
  Qed.

  (** New Z-coordinate is nonzero (so the next iteration's
      dehomogenisation is well-defined): for doubling [nz = 2 Y³ Z]. *)
  Lemma gnark_double_nz (Y Z : F) (HZ : Z <> 0) (HY : Y <> 0) :
    let B := Y * Y in
    let C := Z * Z in
    let H := ((Y + Z) * (Y + Z)) - B - C in
    B * H <> 0.
  Proof.
    cbv beta zeta. fsatz.
  Qed.

  (** For mixed addition [nz = L³ Z], nonzero given [Z<>0] and distinct
      x-coords. *)
  Lemma gnark_add_nz (X Z ax : F) (HZ : Z <> 0) (HL : ax * Z <> X) :
    let X2Z1 := ax * Z in
    let L := X - X2Z1 in
    let D := L * L in
    let E := L * D in
    E * Z <> 0.
  Proof.
    cbv beta zeta. fsatz.
  Qed.

End GnarkDouble.
End GnarkDouble.
