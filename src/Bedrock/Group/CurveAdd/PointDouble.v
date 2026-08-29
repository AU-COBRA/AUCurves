(** * Dedicated point doubling for short Weierstrass curves y² = x³ + b (a=0).

    Uses the dbl-2009-l formula (1M + 5S + 8add), which is ~2x faster
    than calling the complete addition with P1 = P2.

    Uses F.pow x 2 for squaring (triggers Rupicola's compile_square),
    and F.mul for the one non-square multiplication.

    ** DEFECT: WRONG COORDINATE SYSTEM.  SUPERSEDED BY PointDoubleA0.v. **

    dbl-2009-l is a JACOBIAN formula: it reads (X : Y : Z) as
    (X/Z², Y/Z³).  Every other component of the a = 0 chain is
    HOMOGENEOUS -- [CurveAdd.ladderstep_gallina] is fiat-crypto's
    [Projective.add] ([BN254_wNAF_Laws.bn254_curve_add_is_cadd]),
    [StoreZero] writes the homogeneous identity, and
    [RcbProjectiveLaws.oncurve] is the homogeneous curve equation.
    Fed a genuine Jacobian representative (X t², Y t³, t) of a point
    P, [point_double_gallina] returns 2P for every t, as dbl-2009-l
    should.  Fed the homogeneous representative (X t, Y t, t) that the
    a = 0 chain actually produces, it returns a triple that is 2P in
    NEITHER reading, for every t <> 1 -- while
    [ladderstep_gallina P P] returns 2P for every t.

    The output Z is 2YZ, a Jacobian Z, so reading the result
    homogeneously fails even at t = 1: a Z = 1 vector read in the
    chain's own coordinates does expose this.  What hides it is
    reading the output as Jacobian, which is correct at every t.
    So it is not a missing equivalence proof but a wrong answer, and
    [BN254_wNAF_Instance.HCurveDouble], whose postcondition is
    literally [curve_add (X,Y,Z) (X,Y,Z)], cannot be discharged from
    it.

    Reach: [bn254_point_double], [bn256_point_double] and
    [bn446_point_double] bind [point_double_body] to the
    "curve_double" key of their function tables, and
    [bn254_point_double_correct] is Qed -- but it only proves the body
    computes [point_double_gallina], never that
    [point_double_gallina] doubles.  Nothing downstream consumes it:
    no Rust or Jasmin artifact in this tree contains a
    "curve_double", so the defect has not shipped.

    Replacement: [PointDoubleA0.v] derives RCB 2015 Algorithm 9, the
    homogeneous a = 0 doubling, and proves
    [rcb_double_a0_eq_ladderstep] -- equality with the addition on a
    repeated argument, coordinate for coordinate, for every on-curve
    input.  It is also cheaper than this body (18 field operations /
    9 multiplications against 24 / 8), and much cheaper than the
    addition on a repeated argument (33 / 14).

    This file is kept, unmodified apart from this note, because
    [point_double_correct] is a Qed'd Rupicola derivation whose
    aliased-binop shapes [PointDoubleA0.v]'s PORT-CHECK (A) cites as
    precedent.  Do not wire it into a homogeneous chain. *)

Require Import Rupicola.Lib.Api. Import bedrock2.WeakestPrecondition.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Local Open Scope Z_scope.

Local Notation function_t := (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section Gallina.

Context {field_parameters : FieldParameters}.
Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
Context {field_representation : FieldRepresentation}.

Local Notation F := (F M_pos).
Local Infix "+F" := (@F.add M_pos) (at level 100).
Local Infix "-F" := (@F.sub M_pos) (at level 100).
Local Infix "*F" := (@F.mul M_pos) (at level 90).
Local Notation "x ^2" := (@F.pow M_pos x 2) (at level 80).

  (** Dedicated doubling for a=0. Uses F.pow for squares. *)
  Definition point_double_gallina (X Y Z : F) : \<< F, F, F \>> :=
    let/n A := stack (X ^2) in              (* X² *)
    let/n B := stack (Y ^2) in              (* Y² *)
    let/n C := stack (B ^2) in              (* B² = Y⁴ *)
    let/n t := stack (X +F B) in
    let/n t := (t ^2) in                    (* (X+B)² *)
    let/n t := (t -F A) in
    let/n t := (t -F C) in                  (* (X+B)² - A - C *)
    let/n D := stack (t +F t) in            (* D = 2·XB *)
    let/n E := stack (A +F A) in
    let/n E := (E +F A) in                  (* E = 3A *)
    let/n Xout := (E ^2) in                  (* E² → output ptr *)
    let/n Xout := (Xout -F D) in
    let/n Xout := (Xout -F D) in            (* X3 = E² - 2D *)
    let/n t := (D -F Xout) in               (* D - X3 *)
    let/n Yout := (E *F t) in               (* E·(D-X3) → output ptr *)
    let/n t := (C +F C) in                  (* 2C *)
    let/n t := (t +F t) in                  (* 4C *)
    let/n t := (t +F t) in                  (* 8C *)
    let/n Yout := (Yout -F t) in            (* Y3 = E·(D-X3) - 8C *)
    let/n t := (Y +F Z) in
    let/n Zout := (t ^2) in                 (* (Y+Z)² → output ptr *)
    let/n Zout := (Zout -F B) in            (* (Y+Z)² - B *)
    let/n t := stack (Z ^2) in              (* Z² → temp *)
    let/n Zout := (Zout -F t) in            (* Z3 = (Y+Z)² - B - Z² *)
    \<Xout, Yout, Zout\>.

End Gallina.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.

  Context {field_representation : FieldRepresentation}
          {field_representation_ok : FieldRepresentation_ok}.

  Local Notation F := (F M_pos).

  #[local] Hint Resolve relax_bounds : compiler.
  Existing Instance felem_alloc.

  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Lemma tighten_bounds_FElem x_ptr x
    : Lift1Prop.impl1 (FElem (Some loose_bounds) x_ptr x)
                      (FElem (Some tight_bounds) x_ptr x).
  Proof. rewrite Hbounds_eq. reflexivity. Qed.
  Local Hint Immediate tighten_bounds_FElem : ecancel_impl.

  Instance spec_of_point_double : spec_of "curve_double" :=
    fnspec! "curve_double"
          (pXin pYin pZin pXout pYout pZout : word)
          / (X Y Z Xold Yold Zold : F) R,
    { requires tr mem :=
        (FElem (Some tight_bounds) pXin X
         * FElem (Some tight_bounds) pYin Y
         * FElem (Some tight_bounds) pZin Z
         * FElem (Some tight_bounds) pXout Xold
         * FElem (Some tight_bounds) pYout Yold
         * FElem (Some tight_bounds) pZout Zold * R)%sep mem;
      ensures tr' mem' :=
        tr = tr'
        /\ (let '\<Xo, Yo, Zo\> := @point_double_gallina _ X Y Z in
           (FElem (Some tight_bounds) pXin X
            * FElem (Some tight_bounds) pYin Y
            * FElem (Some tight_bounds) pZin Z
            * FElem (Some tight_bounds) pXout Xo
            * FElem (Some tight_bounds) pYout Yo
            * FElem (Some tight_bounds) pZout Zo * R)%sep mem') }.

  Local Ltac ecancel_assumption ::= ecancel_assumption_impl.

  Derive point_double_body SuchThat
         (defn! "curve_double"
                ("Xin", "Yin", "Zin", "Xout", "Yout", "Zout")
              { point_double_body },
           implements @point_double_gallina _
                      using [square; mul; add; sub])
         As point_double_correct.
  Proof. compile. Qed.

End __.

#[global] Existing Instance spec_of_point_double.
