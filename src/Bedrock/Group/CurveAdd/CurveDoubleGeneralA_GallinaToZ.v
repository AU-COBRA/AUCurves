(** * The F-level RCB doubling chain of [rcb_double_general_gallina]
      implies its Z-level Gallina spec [rcb_double_general_Z_spec].

    Doubling analogue of CurveAddGeneralA_GallinaToZ.v, same style:
    stated once over variables of [F M_pos] and abstract Z-lists, so
    that the algebra (F.to_Z pushed through the 31 field operations,
    mod-idempotence normalisation, [ring]) never sees a concrete field
    representation.  The per-curve bridges
    (CurveDoubleGeneralA_P256.v and siblings) instantiate it with
    [X := feval wX] etc. and discharge the eight premises by the
    curve's feval/Montgomery-decoding lemmas.

    §1 defines the Z-level spec.  MontgomeryCurveSpecs.v has no
    doubling spec (only [BLS12_add_Gallina_spec]), so it is stated
    here, in the same style and over the same section parameters
    (m bw n m' a three_b) so that a per-curve
    [PXXX_double_Gallina_spec := rcb_double_general_Z_spec m bw n m' a three_b]
    parallels [PXXX_add_Gallina_spec := BLS12_add_Gallina_spec m bw n m' a three_b]
    of PXXXCurve_G1.v.  It is the line-by-line transcription of RCB
    2015 Algorithm 3 (see CurveDoubleGeneralA.v for the mapping), not
    the addition formula at P1 = P2.

    Honesty ledger (this file): 0 Admitted intended; the proof of
    [rcb_double_general_gallina_to_Z] is the replay of the attested
    addition script and has not been run through the compiler. *)

Require Import Stdlib.ZArith.ZArith.
Require Import Stdlib.Lists.List.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Arithmetic.ModularArithmeticTheorems.
Require Import Crypto.Arithmetic.WordByWordMontgomery.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Theory.WordByWordMontgomery.MontgomeryCurveSpecs.
Require Import Bedrock.Group.CurveAdd.CurveDoubleGeneralA.

Local Open Scope Z_scope.

(* ================================================================== *)
(* §1. The Z-level doubling spec                                       *)
(* ================================================================== *)

Section DoubleZSpec.
  Context (m bw : Z) (n : nat) (m' a three_b : Z).

  Local Notation eval := (@WordByWordMontgomery.eval bw n).
  Local Notation from_mont := (@WordByWordMontgomery.from_montgomerymod bw n m m').
  Local Notation evfrom x := (eval (from_mont x)).

  (** [my_mul]/[my_add]/[my_sub] of MontgomeryCurveSpecs depend on
      the section variable [m] only; [a_list]/[three_b_list] on
      [bw n a] / [bw n three_b] (the argument shapes used by
      CurveAddGeneralA_P256.v §5a). *)
  Local Infix "*'" := (MontgomeryCurveSpecs.my_mul m) (at level 70).
  Local Infix "+'" := (MontgomeryCurveSpecs.my_add m) (at level 80).
  Local Infix "-'" := (MontgomeryCurveSpecs.my_sub m) (at level 80).

  (** Z-level RCB Algorithm 3, in the variable names of the paper
      (t0..t3, X3, Y3, Z3), one line per D-step of
      [rcb_double_general_gallina]. *)
  Definition rcb_double_general_Z_spec (X Y Z outx outy outz : list Z) : Prop :=
    let X := evfrom X in
    let Y := evfrom Y in
    let Z := evfrom Z in
    let t0 := X*'X in                                                  (* D1 *)
    let t1 := Y*'Y in                                                  (* D2 *)
    let t2 := Z*'Z in                                                  (* D3 *)
    let t3 := X*'Y in                                                  (* D4 *)
    let t3 := t3+'t3 in                                                (* D5 *)
    let Z3 := X*'Z in                                                  (* D6 *)
    let Z3 := Z3+'Z3 in                                                (* D7 *)
    let X3 := eval (MontgomeryCurveSpecs.a_list bw n a)*'Z3 in         (* D8 *)
    let Y3 := eval (MontgomeryCurveSpecs.three_b_list bw n three_b)*'t2 in (* D9 *)
    let Y3 := X3+'Y3 in                                                (* D10 *)
    let X3 := t1-'Y3 in                                                (* D11 *)
    let Y3 := t1+'Y3 in                                                (* D12 *)
    let Y3 := X3*'Y3 in                                                (* D13 *)
    let X3 := t3*'X3 in                                                (* D14 *)
    let Z3 := eval (MontgomeryCurveSpecs.three_b_list bw n three_b)*'Z3 in (* D15 *)
    let t2 := eval (MontgomeryCurveSpecs.a_list bw n a)*'t2 in         (* D16 *)
    let t3 := t0-'t2 in                                                (* D17 *)
    let t3 := eval (MontgomeryCurveSpecs.a_list bw n a)*'t3 in         (* D18 *)
    let t3 := t3+'Z3 in                                                (* D19 *)
    let Z3 := t0+'t0 in                                                (* D20 *)
    let t0 := Z3+'t0 in                                                (* D21 *)
    let t0 := t0+'t2 in                                                (* D22 *)
    let t0 := t0*'t3 in                                                (* D23 *)
    let Y3 := Y3+'t0 in                                                (* D24 *)
    let t2 := Y*'Z in                                                  (* D25 *)
    let t2 := t2+'t2 in                                                (* D26 *)
    let t0 := t2*'t3 in                                                (* D27 *)
    let X3 := X3-'t0 in                                                (* D28 *)
    let Z3 := t2*'t1 in                                                (* D29 *)
    let Z3 := Z3+'Z3 in                                                (* D30 *)
    let Z3 := Z3+'Z3 in                                                (* D31 *)
    (evfrom outx, evfrom outy, evfrom outz) = (X3, Y3, Z3).

End DoubleZSpec.

(* ================================================================== *)
(* §2. F-chain -> Z-spec                                               *)
(* ================================================================== *)

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

  (** The eight premises: the Montgomery decodings of the six lists
      are the [F.to_Z] of the six field values, and the [eval] of the
      two constant partitions are the [F.to_Z] of the two constant
      field values.  Argument order after [Hm]:
        aF tbF X Y Z ox oy oz  lX lY lZ lox loy loz  (8 + 6 premises)
      i.e. 22 underscores before [Hgal] in a per-curve [refine].

      PORT-CHECK (Z): proof script is the addition script with the
      argument lists shortened; the [ring] goals are the three
      components of Algorithm 3 with every atom a generalized
      variable, as in the addition. *)
  Theorem rcb_double_general_gallina_to_Z
          (aF tbF X Y Z ox oy oz : F)
          (lX lY lZ lox loy loz : list Z) :
    evfrom lX = F.to_Z X -> evfrom lY = F.to_Z Y -> evfrom lZ = F.to_Z Z ->
    evfrom lox = F.to_Z ox -> evfrom loy = F.to_Z oy -> evfrom loz = F.to_Z oz ->
    eval (MontgomeryCurveSpecs.a_list bw n a) = F.to_Z aF ->
    eval (MontgomeryCurveSpecs.three_b_list bw n three_b) = F.to_Z tbF ->
    @rcb_double_general_gallina field_parameters aF tbF X Y Z
    = \<ox, oy, oz\> ->
    rcb_double_general_Z_spec m bw n m' a three_b lX lY lZ lox loy loz.
  Proof.
    intros HX HY HZ Hox Hoy Hoz Ha Htb Hgal.
    Timeout 600 cbv [rcb_double_general_Z_spec
                     MontgomeryCurveSpecs.my_mul MontgomeryCurveSpecs.my_add
                     MontgomeryCurveSpecs.my_sub].
    Timeout 600 rewrite HX, HY, HZ, Hox, Hoy, Hoz, Ha, Htb.
    Timeout 600 cbv [rcb_double_general_gallina nlet stack] in Hgal.
    pose proof (f_equal P2.car Hgal) as HX3.
    pose proof (f_equal (fun q => P2.car (P2.cdr q)) Hgal) as HY3.
    pose proof (f_equal (fun q => P2.cdr (P2.cdr q)) Hgal) as HZ3.
    Timeout 600 cbv [P2.car P2.cdr] in HX3.
    Timeout 600 cbv [P2.car P2.cdr] in HY3.
    Timeout 600 cbv [P2.car P2.cdr] in HZ3.
    clear Hgal.
    Timeout 600 rewrite <- HX3, <- HY3, <- HZ3.
    clear HX3 HY3 HZ3.
    Timeout 600 repeat first [ rewrite to_Z_mul_m | rewrite to_Z_add_m
                             | rewrite to_Z_sub_m ].
    (* every atom is now [F.to_Z v] for a variable [v]; name them *)
    generalize (F.to_Z aF) as ca; generalize (F.to_Z tbF) as cb;
    generalize (F.to_Z X) as x; generalize (F.to_Z Y) as y;
    generalize (F.to_Z Z) as z;
    intros z y x cb ca.
    Timeout 600 repeat first
      [ rewrite Zdiv.Zmult_mod_idemp_l | rewrite Zdiv.Zmult_mod_idemp_r
      | rewrite Zdiv.Zplus_mod_idemp_l | rewrite Zdiv.Zplus_mod_idemp_r
      | rewrite Zdiv.Zminus_mod_idemp_l | rewrite Zdiv.Zminus_mod_idemp_r ].
    Timeout 600 (apply pair_equal_spec; split; [apply pair_equal_spec; split|]).
    all: timeout 600 (f_equal; ring).
  Qed.

End GallinaToZ.
