(** * BW6-761 G2 affine + projective group law (Gallina, over Fp3).

    Mirror of [BW6_761Curve_G1.v] but for the M-type cubic twist:

        E'(Fp3): y^2 = x^3 + b'      where  b' = -1 / zeta

    Here [Fp3 = Fp[zeta]/(zeta^3 + 4)] with cubic non-residue [nr = -4],
    and the BW6-761 G2 curve is the M-type twist of [E: y^2 = x^3 - 1].

    This file is the Gallina ("math") layer: it defines

      - the affine and projective Weierstrass group operations on E'
        as a record over an abstract ring [R] with [Rinv] (so the same
        body can be re-used for Fp3 with any choice of [Fmul], whether
        Montgomery, fiat-crypto reified, or symbolic),

      - the BW6-specific constants ([b'] = [-1/zeta] in Fp3), and

      - the projective add formula specialised to [a = 0] (which holds
        for BW6 G2 just as it does for G1).

    The bedrock2 implementation + WP proofs are deferred (see
    BW6_761Curve_G2_bedrock.v stub).  Hash-to-G2 and scalar multiplication
    are deferred as separate files; this file is the math layer they
    depend on.

    Conventions: we keep the projective add formula structurally identical
    to [BLS12_add_Gallina_spec_a_0] in [MontgomeryCurveSpecs.v] so that the
    G1 → G2 transport is purely a swap of base ring (Fp ↦ Fp3, [my_*] ↦
    [ce_*]). *)

From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import micromega.Lia.

Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Field.FieldExtensions.Theory.CubicExtensionsAbstract.

Local Open Scope Z_scope.

Section BW6_G2.

  (** ** Abstract Fp + Fp3 layer *)

  (** We work over an abstract base field [F] with its AbstractField
      operations.  The cubic non-residue [nr] is a function [F -> F]
      computing [(-nr) * x] for the chosen cubic non-residue (matches
      [CubicExtensionsAbstract]).  For BW6-761 we will instantiate
      [F := F bw6_M_pos] and [mul_by_nr := bw6_Fp_mul_by_nr_model]. *)
  Context {F : Type} {fp : FieldParameters F}.
  Variable mul_by_nr : F -> F.

  Local Notation Fp3 := (F * F * F)%type.

  (** Lift [ce_*] from [CubicExtensionsAbstract] into local notation.
      Section auto-generalisation only includes Variables that the def
      mentions, so e.g. [ce_zero] does NOT take [mul_by_nr] but
      [ce_mul] does (cf. [GenericCubicSpecs.v]: [@ce_zero _ base_fp]
      vs [@ce_mul _ base_fp mul_by_nr]).  We use unhashed [ce_*] and
      let elaboration insert the args. *)
  Local Notation fp3_zero  := (ce_zero  (F := F)).
  Local Notation fp3_one   := (ce_one   (F := F)).
  Local Notation fp3_add   := (ce_add   (F := F)).
  Local Notation fp3_sub   := (ce_sub   (F := F)).
  Local Notation fp3_opp   := (ce_opp   (F := F)).
  Local Notation fp3_mul   := (ce_mul   (F := F) mul_by_nr).
  Local Notation fp3_sqr   := (ce_sqr   (F := F) mul_by_nr).
  Local Notation fp3_inv   := (ce_inv   (F := F) mul_by_nr).
  Local Notation fp3_div   := (ce_div   (F := F) mul_by_nr).
  Local Notation mk_fp3    := (ce_build (F := F)).

  Local Infix "+f" := fp3_add (at level 50).
  Local Infix "-f" := fp3_sub (at level 50).
  Local Infix "*f" := fp3_mul (at level 40).

  (** ** Curve constants (Fp3 level) *)

  (** [b'] = [-1 / zeta] in Fp3, where [zeta = (0, 1, 0)] is the cubic
      generator.  We compute it abstractly via [fp3_inv] so the same
      expression specialises correctly once [F] is bound. *)
  Definition bw6_G2_zeta : Fp3 := mk_fp3 Fzero Fone Fzero.

  Definition bw6_G2_b : Fp3 :=
    fp3_opp (fp3_inv bw6_G2_zeta).

  (** [three_b'] = 3 * b'. *)
  Definition bw6_G2_three_b : Fp3 :=
    bw6_G2_b +f bw6_G2_b +f bw6_G2_b.

  (** ** Affine group law

      Standard Weierstrass affine add/double over Fp3 with [a = 0]. *)

  Inductive G2_affine : Type :=
  | G2_affine_inf : G2_affine
  | G2_affine_pt  : Fp3 -> Fp3 -> G2_affine.   (* x, y *)

  Definition G2_affine_neg (P : G2_affine) : G2_affine :=
    match P with
    | G2_affine_inf      => G2_affine_inf
    | G2_affine_pt x y   => G2_affine_pt x (fp3_opp y)
    end.

  (** Doubling slope λ = 3·x² / (2·y).  Returns [None] at [y = 0]. *)
  Definition G2_affine_dbl_slope (x y : Fp3) : Fp3 :=
    let three_x2 := let x2 := fp3_sqr x in x2 +f x2 +f x2 in
    let two_y    := y +f y in
    fp3_mul three_x2 (fp3_inv two_y).

  Definition G2_affine_chord_slope (x1 y1 x2 y2 : Fp3) : Fp3 :=
    fp3_mul (y2 -f y1) (fp3_inv (x2 -f x1)).

  Definition G2_affine_double (P : G2_affine) : G2_affine :=
    match P with
    | G2_affine_inf => G2_affine_inf
    | G2_affine_pt x y =>
        let lambda := G2_affine_dbl_slope x y in
        let x3 := (fp3_sqr lambda) -f (x +f x) in
        let y3 := (fp3_mul lambda (x -f x3)) -f y in
        G2_affine_pt x3 y3
    end.

  Definition G2_affine_add_distinct (x1 y1 x2 y2 : Fp3) : G2_affine :=
    let lambda := G2_affine_chord_slope x1 y1 x2 y2 in
    let x3 := (fp3_sqr lambda) -f (x1 +f x2) in
    let y3 := (fp3_mul lambda (x1 -f x3)) -f y1 in
    G2_affine_pt x3 y3.

  (** ** Projective group law (a=0 specialised) — matches G1 byte-for-byte
        modulo the base ring. *)

  (** Same formula as [BW6_761_add_Gallina_spec_a_0] in G1.v but with the
      base operations being Fp3 instead of Fp. *)
  Definition BW6_G2_add_Gallina_spec_a_0
    (X1 Y1 Z1 X2 Y2 Z2 : Fp3) : Fp3 * Fp3 * Fp3 :=
    let t0 := X1 *f X2 in
    let t1 := Y1 *f Y2 in
    let t2 := Z1 *f Z2 in
    let t3 := X1 +f Y1 in
    let t4 := X2 +f Y2 in
    let t3 := t3 *f t4 in
    let t4 := t0 +f t1 in
    let t3 := t3 -f t4 in
    let t4 := X1 +f Z1 in
    let t5 := X2 +f Z2 in
    let t4 := t4 *f t5 in
    let t5 := t0 +f t2 in
    let t4 := t4 -f t5 in
    let t5 := Y1 +f Z1 in
    let X3 := Y2 +f Z2 in
    let t5 := t5 *f X3 in
    let X3 := t1 +f t2 in
    let t5 := t5 -f X3 in
    let Z3 := bw6_G2_three_b *f t2 in
    let X3 := t1 -f Z3 in
    let Z3 := t1 +f Z3 in
    let Y3 := X3 *f Z3 in
    let t1 := t0 +f t0 in
    let t1 := t1 +f t0 in
    let t4 := bw6_G2_three_b *f t4 in
    let t0 := t1 *f t4 in
    let Y3 := Y3 +f t0 in
    let t0 := t5 *f t4 in
    let X3 := t3 *f X3 in
    let X3 := X3 -f t0 in
    let t0 := t3 *f t1 in
    let Z3 := t5 *f Z3 in
    let Z3 := Z3 +f t0 in
    (X3, Y3, Z3).

  (** Doubling on the projective spec (a=0): can be obtained by passing
      the same point twice, but a specialised body saves multiplications. *)
  Definition BW6_G2_dbl_Gallina_spec_a_0
    (X Y Z : Fp3) : Fp3 * Fp3 * Fp3 :=
    let t0 := fp3_sqr Y in
    let Z3 := t0 +f t0 in
    let Z3 := Z3 +f Z3 in
    let Z3 := Z3 +f Z3 in
    let t1 := Y *f Z in
    let t2 := fp3_sqr Z in
    let t2 := bw6_G2_three_b *f t2 in
    let X3 := t2 *f Z3 in
    let Y3 := t0 +f t2 in
    let Z3 := t1 *f Z3 in
    let t1 := t2 +f t2 in
    let t2 := t1 +f t2 in
    let t0 := t0 -f t2 in
    let Y3 := t0 *f Y3 in
    let Y3 := X3 +f Y3 in
    let t1 := X *f Y in
    let X3 := t0 *f t1 in
    let X3 := X3 +f X3 in
    (X3, Y3, Z3).

  (** ** Scalar multiplication (double-and-add) — Gallina reference *)

  (** Affine scalar mult by a positive integer [n], using [G2_affine_double]
      and [G2_affine_add_distinct].  This is the reference model; the
      production version is wNAF-based and lives in a separate file once
      Phase 3 lands. *)
  Fixpoint G2_affine_smul_pos (n : positive) (P : G2_affine) : G2_affine :=
    match n with
    | xH       => P
    | xO n'    => G2_affine_double (G2_affine_smul_pos n' P)
    | xI n'    =>
        let dbl := G2_affine_double (G2_affine_smul_pos n' P) in
        match dbl, P with
        | G2_affine_inf, _ => P
        | _, G2_affine_inf => dbl
        | G2_affine_pt x1 y1, G2_affine_pt x2 y2 =>
            G2_affine_add_distinct x1 y1 x2 y2
        end
    end.

  Definition G2_affine_smul (n : Z) (P : G2_affine) : G2_affine :=
    match n with
    | Z0     => G2_affine_inf
    | Zpos p => G2_affine_smul_pos p P
    | Zneg p => G2_affine_neg (G2_affine_smul_pos p P)
    end.

End BW6_G2.

(** ** Public re-exports *)

(** The downstream files in [src/Bedrock/Field/Synthesis/Examples/BW6_761_*]
    can [Require Import] this file and obtain [BW6_G2_add_Gallina_spec_a_0]
    + [G2_affine_*] specialised to [F := F bw6_M_pos] by passing the BW6
    [bw6_Fp_mul_by_nr_model] for [mul_by_nr] and the BW6 [FieldParameters]
    instance.  See [BW6_761Curve_G2_BignumSpecs.v] for the wired
    bedrock2-side spec. *)
