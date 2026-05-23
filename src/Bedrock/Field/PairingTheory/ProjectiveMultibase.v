(** * ProjectiveMultibase.v — Gallina reference model for a gnark-style
    5-symbol optimal-ate Miller loop in PROJECTIVE (homogeneous)
    coordinates.

    Sibling of [AffineMultibase.v].  Same 5-symbol dispatch over the
    alphabet {-3,-1,0,1,3}, but the running point [T] carries
    homogeneous projective coordinates [(X, Y, Z)] and the per-step
    formulas are gnark's [doubleStep] / [addMixedStep] / [lineCompute]
    (no field inversion), with the line assembled from three Fp-tower
    coefficients [(r0, r1, r2)] via a sparse [Fp12] builder.

    This is the value-faithful model of the bedrock2 functions
    [g2_double_step], [g2_add_step], [g2_line_compute] and
    [sparse_line_eval]: each per-step definition below is the exact
    arithmetic those bodies perform, transcribed call-for-call.

    Genericity.  The model is parameterised over [FieldOps] (from
    [Affine.v]) plus three tower constructors/accessors:
      - [fp3_mk]  : build an Fp2 (= the first extension) from 3 Fp slots
      - [fp3_c0]  : read the 0th Fp slot of an Fp2
      - [fp6_mk]  : build an Fp12 (= the top field) from 2 Fp2 blocks
    so it instantiates for any tower whose second extension is built as
    a pair of first-extension blocks (BW6-761: Fp6 = Fp3[w]/(w^2 - zeta)
    over Fp3 = Fp[zeta]/(zeta^3 + 4)).

    The connection to the abstract pairing (this projective model equals
    the affine [AffineMultibase.affine_miller_optimal_ate] after
    Z-normalisation, then the true pairing after final exponentiation)
    is the [MillerEquiv]-style obligation and is NOT discharged here. *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lists.List. Import ListNotations.

Require Import Bedrock.Field.PairingTheory.Affine.

Local Open Scope Z_scope.

Section ProjectiveMultibase.

  Context {Fp Fp2 Fp12 : Type}.
  Context (ops : FieldOps Fp Fp2 Fp12).

  (** Tower constructors/accessors not present in [FieldOps]. *)
  Context (fp3_mk : Fp -> Fp -> Fp -> Fp2).
  Context (fp3_c0 : Fp2 -> Fp).
  Context (fp6_mk : Fp2 -> Fp2 -> Fp12).

  Local Notation "x +2 y" := (fp2_add  ops x y) (at level 50).
  Local Notation "x -2 y" := (fp2_sub  ops x y) (at level 50).
  Local Notation "x *2 y" := (fp2_mul  ops x y) (at level 40).

  (** ** gnark [doubleStep] on the homogeneous projective point.

      Transcribed from [bw6_761_g2_double_step]:
        A = (x*y)/2,  B = y^2,  C = z^2,  D = 3C,  E = 4D = 12C,
        F = 3E = 36C,  G = (B+F)/2,  H = (y+z)^2 - B - C,
        J = x^2,  EE = E^2,  K = 3*EE
        x' = (B-F)*A,  y' = G^2 - K,  z' = B*H
      Line coefficients: r0 = E-B,  r1 = 3J,  r2 = -H.
      The "/2" is multiplication by the supplied [half] (= (p+1)/2). *)
  Definition proj_double_step
      (x y z : Fp2) (half : Fp)
    : (Fp2 * Fp2 * Fp2) * (Fp2 * Fp2 * Fp2) :=
    let A  := fp2_mul_fp ops (x *2 y) half in
    let B  := fp2_sqr ops y in
    let C  := fp2_sqr ops z in
    let D  := (C +2 C) +2 C in
    let E  := let e1 := D +2 D in e1 +2 e1 in
    let Fc := let f1 := E +2 E in f1 +2 E in
    let G  := fp2_mul_fp ops (B +2 Fc) half in
    let H  := let h1 := fp2_sqr ops (y +2 z) in (h1 -2 B) -2 C in
    let J  := fp2_sqr ops x in
    let EE := fp2_sqr ops E in
    let K  := (EE +2 EE) +2 EE in
    let nx := (B -2 Fc) *2 A in
    let ny := (fp2_sqr ops G) -2 K in
    let nz := B *2 H in
    let r0 := E -2 B in
    let r1 := (J +2 J) +2 J in
    let r2 := fp2_neg ops H in
    ((nx, ny, nz), (r0, r1, r2)).

  (** ** gnark [addMixedStep]: T (proj) + A (affine), transcribed from
      [bw6_761_g2_add_step].
        Y2Z1 = ay*z,  O = y - Y2Z1,  X2Z1 = ax*z,  L = x - X2Z1,
        C = O^2,  D = L^2,  E = L*D,  F = z*C,  G = x*D,
        H = E + F - 2G,  t1 = y*E,
        x' = L*H,  y' = (G-H)*O - t1,  z' = E*z
      Line coefficients: r0 = ax*O - ay*L,  r1 = -O,  r2 = L. *)
  Definition proj_add_step
      (x y z ax ay : Fp2)
    : (Fp2 * Fp2 * Fp2) * (Fp2 * Fp2 * Fp2) :=
    let Y2Z1 := ay *2 z in
    let O    := y -2 Y2Z1 in
    let X2Z1 := ax *2 z in
    let L    := x -2 X2Z1 in
    let C    := fp2_sqr ops O in
    let D    := fp2_sqr ops L in
    let E    := L *2 D in
    let Fc   := z *2 C in
    let G    := x *2 D in
    let H    := (E +2 Fc) -2 (G +2 G) in
    let t1   := y *2 E in
    let nx   := L *2 H in
    let ny   := ((G -2 H) *2 O) -2 t1 in
    let nz   := E *2 z in
    let r0   := (ax *2 O) -2 (ay *2 L) in
    let r1   := fp2_neg ops O in
    let r2   := L in
    ((nx, ny, nz), (r0, r1, r2)).

  (** ** gnark [lineCompute]: line through T at A, NO point update.
      Transcribed from [bw6_761_g2_line_compute]. *)
  Definition proj_line_compute
      (x y z ax ay : Fp2)
    : (Fp2 * Fp2 * Fp2) :=
    let Y2Z1 := ay *2 z in
    let O    := y -2 Y2Z1 in
    let X2Z1 := ax *2 z in
    let L    := x -2 X2Z1 in
    let r0   := (ax *2 O) -2 (ay *2 L) in
    let r1   := fp2_neg ops O in
    let r2   := L in
    (r0, r1, r2).

  (** ** Sparse Fp12 line, transcribed from [bw6_761_sparse_line_eval].
      Builds the Fp12 with non-zero slots only at
        B0 = (r0.c0, (r1*Px).c0, 0),  B1 = (0, (r2*Py).c0, 0).
      [(r1*Px).c0 = (fp2_mul_fp r1 Px).c0] and similarly for [r2*Py]. *)
  Definition proj_sparse_line
      (r0 r1 r2 : Fp2) (Px Py : Fp) : Fp12 :=
    let z0 := fp_zero ops in
    fp6_mk
      (fp3_mk (fp3_c0 r0) (fp3_c0 (fp2_mul_fp ops r1 Px)) z0)
      (fp3_mk z0 (fp3_c0 (fp2_mul_fp ops r2 Py)) z0).

  (** ** One main-loop iteration, transcribed from [miller_iter_body j].

      [f := f^2 * line_double]; then for j <> 0 also
      [f := f * line_add] against the j-selected affine point:
        j =  1 : (Q0x, Q0y)     j = -1 : (Q0x, Q0yNeg)
        j =  3 : (Q1x, Q1y)     j = -3 : (Q1x, Q1yNeg)
      Returns (f', T'). *)
  Definition proj_multibase_iter
      (Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg : Fp2)
      (Px Py : Fp) (half : Fp)
      (j : Z) (f : Fp12) (x y z : Fp2)
    : Fp12 * (Fp2 * Fp2 * Fp2) :=
    let fsq := fp12_sqr ops f in
    let '((x1, y1, z1), (r0d, r1d, r2d)) := proj_double_step x y z half in
    let line_d := proj_sparse_line r0d r1d r2d Px Py in
    let f1 := fp12_mul ops fsq line_d in
    if Z.eqb j 0 then
      (f1, (x1, y1, z1))
    else
      let '(ax, ay) :=
        match j with
        | 1   => (Q0x, Q0y)
        | -1  => (Q0x, Q0yNeg)
        | 3   => (Q1x, Q1y)
        | -3  => (Q1x, Q1yNeg)
        | _   => (Q0x, Q0y)
        end
      in
      let '((x2, y2, z2), (r0a, r1a, r2a)) := proj_add_step x1 y1 z1 ax ay in
      let line_a := proj_sparse_line r0a r1a r2a Px Py in
      let f2 := fp12_mul ops f1 line_a in
      (f2, (x2, y2, z2)).

  (** ** Main 5-symbol projective loop body (mirrors
      [affine_miller_5symbol_aux]). *)
  Fixpoint proj_miller_5symbol_aux
      (alphabet : nat -> Z) (i : nat)
      (Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg : Fp2)
      (Px Py : Fp) (half : Fp)
      (f : Fp12) (x y z : Fp2)
    : Fp12 * (Fp2 * Fp2 * Fp2) :=
    match i with
    | O => (f, (x, y, z))
    | S i' =>
      let '(f', (x', y', z')) :=
        proj_multibase_iter
          Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half
          (alphabet i') f x y z
      in
      proj_miller_5symbol_aux alphabet i'
        Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half
        f' x' y' z'
    end.

  (** Main-loop entry: [f := 1], [T := (Qx, Qy, 1)].  [Q1] (the digit-3
      target, = phi(Q) for BW6) seeds the running point. *)
  Definition proj_miller_5symbol
      (n_iters : nat) (alphabet : nat -> Z)
      (Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg : Fp2)
      (Px Py : Fp) (half : Fp)
      (Tx0 Ty0 Tz0 : Fp2)
    : Fp12 * (Fp2 * Fp2 * Fp2) :=
    proj_miller_5symbol_aux alphabet n_iters
      Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half
      (fp12_one ops) Tx0 Ty0 Tz0.

  (** ** Final adjustment (i = 0), transcribed from [miller_iter_final]:
      square, double (with its line), then a line-only step against
      (Q1x, Q1yNeg) with NO point update. *)
  Definition proj_final_adjustment
      (f : Fp12) (x y z : Fp2)
      (Q1x Q1yNeg : Fp2) (Px Py : Fp) (half : Fp)
    : Fp12 :=
    let fsq := fp12_sqr ops f in
    let '((x1, y1, z1), (r0d, r1d, r2d)) := proj_double_step x y z half in
    let line_d := proj_sparse_line r0d r1d r2d Px Py in
    let f1 := fp12_mul ops fsq line_d in
    let '(r0a, r1a, r2a) := proj_line_compute x1 y1 z1 Q1x Q1yNeg in
    let line_a := proj_sparse_line r0a r1a r2a Px Py in
    fp12_mul ops f1 line_a.

  (** ** Top-level: main loop then final adjustment. *)
  Definition proj_miller_optimal_ate
      (n_iters : nat) (alphabet : nat -> Z)
      (Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg : Fp2)
      (Px Py : Fp) (half : Fp)
      (Tx0 Ty0 Tz0 : Fp2)
    : Fp12 :=
    let '(f, (x, y, z)) :=
      proj_miller_5symbol n_iters alphabet
        Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half
        Tx0 Ty0 Tz0
    in
    proj_final_adjustment f x y z Q1x Q1yNeg Px Py half.

  (** ** Initial iteration (mirrors the bedrock [miller_iter_init], i=188):
      double [T] and assign the doubling line directly to [f] (no square,
      no add — correct because the running [f] is 1 at entry). *)
  Definition proj_init_step
      (Px Py : Fp) (half : Fp) (x y z : Fp2)
    : Fp12 * (Fp2 * Fp2 * Fp2) :=
    let '((x1, y1, z1), (r0d, r1d, r2d)) := proj_double_step x y z half in
    let line_d := proj_sparse_line r0d r1d r2d Px Py in
    (line_d, (x1, y1, z1)).

  (** ** Main loop as a fold over the explicit digit list (mirrors the
      bedrock [emit_iters]: one [proj_multibase_iter] per list element,
      processed front-to-back).  The per-iteration invariant's step peels
      the head digit off [js]. *)
  Fixpoint proj_main_loop
      (js : list Z)
      (Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg : Fp2)
      (Px Py : Fp) (half : Fp)
      (f : Fp12) (x y z : Fp2)
    : Fp12 * (Fp2 * Fp2 * Fp2) :=
    match js with
    | [] => (f, (x, y, z))
    | j :: rest =>
      let '(f', (x', y', z')) :=
        proj_multibase_iter
          Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half j f x y z
      in
      proj_main_loop rest Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half
        f' x' y' z'
    end.

End ProjectiveMultibase.

(** ** Dispatcher consistency lemmas.

    Analogues of [AffineMultibase.multibase_iter_step_jX]: at each
    concrete digit the iteration reduces to the double-(then-add) form
    with the right affine target.  All hold definitionally. *)

Section ProjectiveMultibaseLemmas.

  Context {Fp Fp2 Fp12 : Type}.
  Context (ops : FieldOps Fp Fp2 Fp12).
  Context (fp3_mk : Fp -> Fp -> Fp -> Fp2).
  Context (fp3_c0 : Fp2 -> Fp).
  Context (fp6_mk : Fp2 -> Fp2 -> Fp12).

  Local Notation iter :=
    (proj_multibase_iter ops fp3_mk fp3_c0 fp6_mk).
  Local Notation dbl  := (proj_double_step ops).
  Local Notation adds := (proj_add_step ops).
  Local Notation sline := (proj_sparse_line ops fp3_mk fp3_c0 fp6_mk).

  (** [j = 0]: doubling only, line absorbed into [f^2]. *)
  Lemma proj_multibase_iter_j0 :
    forall Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z,
      iter Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half 0 f x y z
      = let '((x1, y1, z1), (r0d, r1d, r2d)) := dbl x y z half in
        let line_d := sline r0d r1d r2d Px Py in
        (fp12_mul ops (fp12_sqr ops f) line_d, (x1, y1, z1)).
  Proof.
    intros; cbv [proj_multibase_iter].
    destruct (dbl x y z half) as [[[x1 y1] z1] [[r0d r1d] r2d]];
      reflexivity.
  Qed.

  (** Helper: at a nonzero digit the iteration does double, then adds the
      [j]-selected affine point. *)
  Lemma proj_multibase_iter_add :
    forall Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half j f x y z ax ay,
      j <> 0 ->
      (match j with
       | 1 => (Q0x, Q0y) | -1 => (Q0x, Q0yNeg)
       | 3 => (Q1x, Q1y) | -3 => (Q1x, Q1yNeg)
       | _ => (Q0x, Q0y) end) = (ax, ay) ->
      iter Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half j f x y z
      = let '((x1, y1, z1), (r0d, r1d, r2d)) := dbl x y z half in
        let line_d := sline r0d r1d r2d Px Py in
        let f1 := fp12_mul ops (fp12_sqr ops f) line_d in
        let '((x2, y2, z2), (r0a, r1a, r2a)) := adds x1 y1 z1 ax ay in
        let line_a := sline r0a r1a r2a Px Py in
        (fp12_mul ops f1 line_a, (x2, y2, z2)).
  Proof.
    intros Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half j f x y z ax ay Hj Hsel.
    cbv [proj_multibase_iter].
    destruct (Z.eqb_spec j 0) as [->|_]; [contradiction|].
    rewrite Hsel.
    destruct (dbl x y z half) as [[[x1 y1] z1] [[r0d r1d] r2d]].
    destruct (adds x1 y1 z1 ax ay) as [[[x2 y2] z2] [[r0a r1a] r2a]].
    reflexivity.
  Qed.

  Lemma proj_multibase_iter_j1 :
    forall Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z,
      iter Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half 1 f x y z
      = let '((x1, y1, z1), (r0d, r1d, r2d)) := dbl x y z half in
        let line_d := sline r0d r1d r2d Px Py in
        let f1 := fp12_mul ops (fp12_sqr ops f) line_d in
        let '((x2, y2, z2), (r0a, r1a, r2a)) := adds x1 y1 z1 Q0x Q0y in
        let line_a := sline r0a r1a r2a Px Py in
        (fp12_mul ops f1 line_a, (x2, y2, z2)).
  Proof.
    intros; eapply proj_multibase_iter_add; [discriminate | reflexivity].
  Qed.

  Lemma proj_multibase_iter_jm1 :
    forall Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z,
      iter Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half (-1) f x y z
      = let '((x1, y1, z1), (r0d, r1d, r2d)) := dbl x y z half in
        let line_d := sline r0d r1d r2d Px Py in
        let f1 := fp12_mul ops (fp12_sqr ops f) line_d in
        let '((x2, y2, z2), (r0a, r1a, r2a)) := adds x1 y1 z1 Q0x Q0yNeg in
        let line_a := sline r0a r1a r2a Px Py in
        (fp12_mul ops f1 line_a, (x2, y2, z2)).
  Proof.
    intros; eapply proj_multibase_iter_add; [discriminate | reflexivity].
  Qed.

  Lemma proj_multibase_iter_j3 :
    forall Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z,
      iter Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half 3 f x y z
      = let '((x1, y1, z1), (r0d, r1d, r2d)) := dbl x y z half in
        let line_d := sline r0d r1d r2d Px Py in
        let f1 := fp12_mul ops (fp12_sqr ops f) line_d in
        let '((x2, y2, z2), (r0a, r1a, r2a)) := adds x1 y1 z1 Q1x Q1y in
        let line_a := sline r0a r1a r2a Px Py in
        (fp12_mul ops f1 line_a, (x2, y2, z2)).
  Proof.
    intros; eapply proj_multibase_iter_add; [discriminate | reflexivity].
  Qed.

  Lemma proj_multibase_iter_jm3 :
    forall Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half f x y z,
      iter Q0x Q0y Q0yNeg Q1x Q1y Q1yNeg Px Py half (-3) f x y z
      = let '((x1, y1, z1), (r0d, r1d, r2d)) := dbl x y z half in
        let line_d := sline r0d r1d r2d Px Py in
        let f1 := fp12_mul ops (fp12_sqr ops f) line_d in
        let '((x2, y2, z2), (r0a, r1a, r2a)) := adds x1 y1 z1 Q1x Q1yNeg in
        let line_a := sline r0a r1a r2a Px Py in
        (fp12_mul ops f1 line_a, (x2, y2, z2)).
  Proof.
    intros; eapply proj_multibase_iter_add; [discriminate | reflexivity].
  Qed.

End ProjectiveMultibaseLemmas.
