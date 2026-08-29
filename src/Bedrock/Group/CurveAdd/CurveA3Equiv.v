(** * The a = -3 RCB chains ARE the general-a chains at a = -3.

    Two identities, both unconditional in the field:

      rcb_add_a3_gallina    b P Q  =  rcb_add_general_gallina    (-3) (3b) P Q
      rcb_double_a3_gallina b P    =  rcb_double_general_gallina (-3) (3b) P

    i.e. Algorithm 4 = Algorithm 1 and Algorithm 6 = Algorithm 3 of
    Renes-Costello-Batina 2015 (ePrint 2015/1060) once a := -3 and the
    general chain's constant 3b is the triple of this chain's b.

    ** What is and is not claimed **

    These are POLYNOMIAL identities in F[X1,Y1,Z1,X2,Y2,Z2,b] (resp.
    F[X,Y,Z,b]).  No on-curve hypothesis, no non-degeneracy, no
    primality, no characteristic bound is used — [ring] over
    [F.ring_theory M_pos] closes each of the six coordinate goals.
    In particular the identities hold for the (0,0,0) outputs that the
    RCB chains produce on exceptional inputs, so the specialised
    bodies inherit the general chain's exceptional behaviour exactly,
    not merely on the curve.

    That is what makes the specialisation drop-in.  Everything already
    proved about the general-a chain transfers by rewriting:

    - [RcbProjectiveLaws.cadd_is_Padd] and the group laws built on it
      (that file's [cadd] is the general chain at its section
      constants [a] [three_b]; instantiate at a = -3, three_b = 3b and
      rewrite with [rcb_add_a3_is_general_triple]);
    - the Z-level chain specs [CurveAddGeneralA_GallinaToZ] /
      [CurveDoubleGeneralA_GallinaToZ] and the per-curve Bignum
      bridges built from them;
    - the wNAF instances, which consume the group laws only.

    None of those files is edited or re-proved.

    ** Cost, honestly **

    The specialisation is NOT fewer field operations.  It is fewer
    MULTIPLICATIONS, bought with more additions:

      addition   Alg 1 (gen a)  40 ops = 17 mul + 23 add/sub, 2 constants
                 Alg 4 (a=-3)   43 ops = 14 mul + 29 add/sub, 1 constant
      doubling   Alg 3 (gen a)  31 ops = 16 mul + 15 add/sub, 2 constants
                 Alg 6 (a=-3)   34 ops = 13 mul + 21 add/sub, 1 constant

    Three multiplications traded for six additions in each case, plus
    one saved stack buffer.  On word-by-word-Montgomery fields a
    multiplication is n^2 word multiplications plus a reduction and an
    addition is n word additions plus a conditional subtraction, so
    the trade is favourable at every limb count used here (n = 4 for
    P-224/P-256, n = 6 for P-384) — but it is a ~15-20% reduction in
    multiplication count, not a factor.  It does not by itself account
    for the whole measured gap against RustCrypto on P-256, which runs
    a different field backend; on P-384, where both sides run the same
    fiat-crypto backend, the measured 1.13x gap is of the size this
    trade explains.

    Honesty ledger (this file): 0 Admitted, 0 Axiom. *)

From Stdlib Require Import ZArith.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveAddA3.
Require Import Bedrock.Group.CurveAdd.CurveDoubleGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveDoubleA3.

(** Congruence for Rupicola's output tuple: [\<x, y, z\>] is
    [P2.pair x (P2.pair y z)] (Rupicola/Lib/Core.v:30, a record with
    primitive projections), so plain [f_equal] does not always fire on
    it; this states the two-argument congruence explicitly.
    Cost: one [subst], one [reflexivity]. *)
Lemma p2_pair_eq {A B} (a1 a2 : A) (b1 b2 : B) :
  a1 = a2 -> b1 = b2 -> P2.pair a1 b1 = P2.pair a2 b2.
Proof. intros Ha Hb; subst; reflexivity. Qed.

Section A3Equiv.

  Context {field_parameters : FieldParameters}.

  Local Notation F := (F M_pos).

  (** Same ring registration as [RcbProjectiveLaws]; it needs no
      primality and no characteristic hypothesis. *)
  Add Ring Fp_ring : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  (** a = -3 and 3b, written with [F.one] / [F.add] / [F.opp] rather
      than a numeral so that no [F_scope] numeral notation and no
      [F.of_Z] constant recognition is on the critical path of
      [ring]. *)
  Local Notation Fthree := (F.add (F.add F.one F.one) F.one).
  Local Notation Fminus_three := (F.opp Fthree).
  Local Notation Ftriple b := (F.add (F.add b b) b).

  (* ================================================================ *)
  (** ** 1. Addition: Algorithm 4 = Algorithm 1 at a = -3             *)
  (* ================================================================ *)

  (** Where the specialisation comes from, step by step (paper line
      numbers; xz, yy, zz, xx are the RCB intermediates):

        general A19-A21   Z3 := a*xz + 3b*zz
                          = -3*xz + 3b*zz = -3*(xz - b*zz)
        Alg 4  A19-A22    X3 := 3*(xz - b*zz)
      so the general chain's [t1 - Z3] is Alg 4's [t1 + X3] and vice
      versa (steps 22-24 on both sides), and likewise

        general S28-S32   t4 := 3b*xz + a*(xx - a*zz)
                          = 3b*xz - 3*xx - 9*zz = 3*(b*xz - xx - 3*zz)
        Alg 4  A25-A31    Y3 := 3*(b*xz - 3*zz - xx)
        general S25-S29   t1 := 3*xx + a*zz = 3*xx - 3*zz
        Alg 4  A32-A34    t0 := 3*xx - 3*zz

      The three products that close the formula are then the same
      three products on both sides, which is why [ring] closes each
      coordinate without case analysis. *)
  Theorem rcb_add_a3_is_general (b X1 Y1 Z1 X2 Y2 Z2 : F) :
    rcb_add_a3_gallina (b_val := b) X1 Y1 Z1 X2 Y2 Z2
    = rcb_add_general_gallina
        (a_val := Fminus_three) (three_b_val := Ftriple b)
        X1 Y1 Z1 X2 Y2 Z2.
  Proof.
    cbv [rcb_add_a3_gallina rcb_add_general_gallina nlet stack].
    apply p2_pair_eq; [| apply p2_pair_eq].
    - Timeout 120 ring.
    - Timeout 120 ring.
    - Timeout 120 ring.
  Qed.

  (** The same statement in the plain-triple shape used by
      [RcbProjectiveLaws.cadd] and by
      [NistWnafWrappers.curve_add_general_triple]. *)
  Corollary rcb_add_a3_is_general_triple (b X1 Y1 Z1 X2 Y2 Z2 : F) :
    (let '\<x, y, z\> :=
       rcb_add_a3_gallina (b_val := b) X1 Y1 Z1 X2 Y2 Z2 in (x, y, z))
    = (let '\<x, y, z\> :=
         rcb_add_general_gallina
           (a_val := Fminus_three) (three_b_val := Ftriple b)
           X1 Y1 Z1 X2 Y2 Z2 in (x, y, z)).
  Proof. rewrite rcb_add_a3_is_general. reflexivity. Qed.

  (* ================================================================ *)
  (** ** 2. Doubling: Algorithm 6 = Algorithm 3 at a = -3             *)
  (* ================================================================ *)

  (** Both chains compute Z3 = 8*Y^3*Z, i.e. both already use the
      curve equation in the same place; the identity below is
      therefore still unconditional, and it does NOT assert that
      either chain equals [add(P, P)] — that claim is separate and is
      not made here or in CurveDoubleGeneralA.v. *)
  Theorem rcb_double_a3_is_general (b X1 Y1 Z1 : F) :
    rcb_double_a3_gallina (b_val := b) X1 Y1 Z1
    = rcb_double_general_gallina
        (a_val := Fminus_three) (three_b_val := Ftriple b)
        X1 Y1 Z1.
  Proof.
    cbv [rcb_double_a3_gallina rcb_double_general_gallina nlet stack].
    apply p2_pair_eq; [| apply p2_pair_eq].
    - Timeout 120 ring.
    - Timeout 120 ring.
    - Timeout 120 ring.
  Qed.

  Corollary rcb_double_a3_is_general_triple (b X1 Y1 Z1 : F) :
    (let '\<x, y, z\> :=
       rcb_double_a3_gallina (b_val := b) X1 Y1 Z1 in (x, y, z))
    = (let '\<x, y, z\> :=
         rcb_double_general_gallina
           (a_val := Fminus_three) (three_b_val := Ftriple b)
           X1 Y1 Z1 in (x, y, z)).
  Proof. rewrite rcb_double_a3_is_general. reflexivity. Qed.

End A3Equiv.
