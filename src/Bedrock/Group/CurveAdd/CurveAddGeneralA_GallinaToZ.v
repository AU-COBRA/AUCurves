(** * The F-level RCB chain of [rcb_add_general_gallina] implies the
      Z-level [BLS12_add_Gallina_spec].

    Stated once, over variables of [F M_pos] and abstract Z-lists, so
    that the algebra (F.to_Z pushed through the forty field operations,
    mod-idempotence normalisation, [ring]) never sees a concrete field
    representation: every atom is [F.to_Z v] for a variable [v], which
    no unifier or conversion check can unfold.  The per-curve bridges
    (CurveAddGeneralA_P256.v and siblings) instantiate it with
    [X1 := feval wX1] etc. and discharge the eleven premises by the
    curve's feval/Montgomery-decoding lemmas.

    Honesty ledger (this file): 0 Admitted. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.

Local Open Scope Z_scope.

Section GallinaToZ.
  Context {field_parameters : FieldParameters}.
  Context (m bw : Z) (n : nat) (m' a three_b : Z).
  Context (Hm : Z.pos M_pos = m).

  Local Notation F := (F M_pos).
  Local Notation eval := (@WordByWordMontgomery.eval bw n).
  Local Notation evfrom x :=
    (@WordByWordMontgomery.eval bw n
       (@WordByWordMontgomery.from_montgomerymod bw n m m' x)).

  (** [F.to_Z] through the field operations, with the modulus [m]. *)
  Lemma to_Z_mul_m (x y : F) :
    F.to_Z (F.mul x y) = (F.to_Z x * F.to_Z y) mod m.
  Proof. rewrite F.to_Z_mul, Hm. reflexivity. Qed.

  Lemma to_Z_add_m (x y : F) :
    F.to_Z (F.add x y) = (F.to_Z x + F.to_Z y) mod m.
  Proof. rewrite F.to_Z_add, Hm. reflexivity. Qed.

  Lemma to_Z_sub_m (x y : F) :
    F.to_Z (F.sub x y) = (F.to_Z x - F.to_Z y) mod m.
  Proof.
    cbv [F.sub]. rewrite F.to_Z_add, F.to_Z_opp, Zdiv.Zplus_mod_idemp_r, Hm.
    rewrite Z.add_opp_r. reflexivity.
  Qed.

  (** The eleven premises: the Montgomery decodings of the nine lists
      are the [F.to_Z] of the nine field values, and the [eval] of the
      two constant partitions are the [F.to_Z] of the two constant
      field values.  The conclusion is the Gallina spec of
      [MontgomeryCurveSpecs] at these lists. *)
  Theorem rcb_general_a_gallina_to_Z
          (aF tbF X1 Y1 Z1 X2 Y2 Z2 ox oy oz : F)
          (lX1 lY1 lZ1 lX2 lY2 lZ2 lox loy loz : list Z) :
    evfrom lX1 = F.to_Z X1 -> evfrom lY1 = F.to_Z Y1 -> evfrom lZ1 = F.to_Z Z1 ->
    evfrom lX2 = F.to_Z X2 -> evfrom lY2 = F.to_Z Y2 -> evfrom lZ2 = F.to_Z Z2 ->
    evfrom lox = F.to_Z ox -> evfrom loy = F.to_Z oy -> evfrom loz = F.to_Z oz ->
    eval (MontgomeryCurveSpecs.a_list bw n a) = F.to_Z aF ->
    eval (MontgomeryCurveSpecs.three_b_list bw n three_b) = F.to_Z tbF ->
    @rcb_add_general_gallina field_parameters aF tbF X1 Y1 Z1 X2 Y2 Z2
    = \<ox, oy, oz\> ->
    MontgomeryCurveSpecs.BLS12_add_Gallina_spec m bw n m' a three_b
      lX1 lY1 lZ1 lX2 lY2 lZ2 lox loy loz.
  Proof.
    intros HX1 HY1 HZ1 HX2 HY2 HZ2 Hox Hoy Hoz Ha Htb Hgal.
    Timeout 600 cbv [MontgomeryCurveSpecs.BLS12_add_Gallina_spec
                     MontgomeryCurveSpecs.my_mul MontgomeryCurveSpecs.my_add
                     MontgomeryCurveSpecs.my_sub].
    Timeout 600 rewrite HX1, HY1, HZ1, HX2, HY2, HZ2, Hox, Hoy, Hoz, Ha, Htb.
    Timeout 600 cbv [rcb_add_general_gallina nlet stack] in Hgal.
    pose proof (f_equal P2.car Hgal) as HX.
    pose proof (f_equal (fun q => P2.car (P2.cdr q)) Hgal) as HY.
    pose proof (f_equal (fun q => P2.cdr (P2.cdr q)) Hgal) as HZ.
    Timeout 600 cbv [P2.car P2.cdr] in HX.
    Timeout 600 cbv [P2.car P2.cdr] in HY.
    Timeout 600 cbv [P2.car P2.cdr] in HZ.
    clear Hgal.
    Timeout 600 rewrite <- HX, <- HY, <- HZ.
    clear HX HY HZ.
    Timeout 600 repeat first [ rewrite to_Z_mul_m | rewrite to_Z_add_m
                             | rewrite to_Z_sub_m ].
    (* every atom is now [F.to_Z v] for a variable [v]; name them *)
    generalize (F.to_Z aF) as ca; generalize (F.to_Z tbF) as cb;
    generalize (F.to_Z X1) as x1; generalize (F.to_Z Y1) as y1;
    generalize (F.to_Z Z1) as z1; generalize (F.to_Z X2) as x2;
    generalize (F.to_Z Y2) as y2; generalize (F.to_Z Z2) as z2;
    intros z2 y2 x2 z1 y1 x1 cb ca.
    Timeout 600 repeat first
      [ rewrite Zdiv.Zmult_mod_idemp_l | rewrite Zdiv.Zmult_mod_idemp_r
      | rewrite Zdiv.Zplus_mod_idemp_l | rewrite Zdiv.Zplus_mod_idemp_r
      | rewrite Zdiv.Zminus_mod_idemp_l | rewrite Zdiv.Zminus_mod_idemp_r ].
    Timeout 600 (apply pair_equal_spec; split; [apply pair_equal_spec; split|]).
    all: timeout 600 (f_equal; ring).
  Qed.

End GallinaToZ.
