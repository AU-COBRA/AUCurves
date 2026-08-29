(** * Group laws for the general-a RCB addition, up to projective equivalence.

    [rcb_add_general_gallina] (CurveAddGeneralA.v) is Algorithm 1 of
    Renes-Costello-Batina 2015, written as a Rupicola [let/n] chain over
    [F M_pos].  fiat-crypto's [Crypto.Curves.Weierstrass.Projective.add]
    is the *same* forty-operation dataflow, packaged as a function on the
    on-curve subset [Projective.point] and shipped with

      Projective.eq_iff_Weq    : eq P Q <-> W.eq (to_affine P) (to_affine Q)
      Projective.to_affine_add : W.eq (to_affine (add P Q e))
                                      (W.add (to_affine P) (to_affine Q))

    both proved for ARBITRARY [a]: fiat-crypto's Projective.v carries [a]
    as a section variable throughout and nothing in it assumes a = 0.
    This file therefore reproves no elliptic-curve group law; it
    transports fiat-crypto's affine [W.commutative_group] through that
    correspondence.

    The four generic wNAF files (wNAF_Single_HornerAlgebra.v,
    wNAF_Single_LoopBody.v, wNAF_Single_Proof.v,
    BLS12_wNAF_ProcessDigits.v) assume the same laws with LEIBNIZ
    equality on raw triples, which is false for RCB coordinates
    (BLS12_wNAF_PointOppInverse.v).  Section 5 below records, hypothesis
    by hypothesis, what each becomes once their invariant is restated
    with [pt_eq].  Those four files are NOT edited here.

    ** Honesty ledger **

    No [Admitted] and no [Axiom].  [not_exceptional_of_no_two_torsion]
    (§0b) derives fiat-crypto's [Projective.not_exceptional] side
    condition from "the curve has no F-rational point of order two"
    (2p = 2q => 2(p-q) = 0 => p-q = 0 when 2-torsion is trivial); the
    group rearrangement it needs is §0a, proved once over an abstract
    [Hierarchy.commutative_group] rather than against [W.add] / [W.opp].
    The main section still takes [Hexcept] as a HYPOTHESIS, so consumers
    are free to supply totality some other way.

    Everything in §0a-§4 is Qed.

    ** What is genuinely missing upstream (a =/= 0) **

    Nothing for the ADDITION itself: [Projective.add], [Projective.eq],
    [eq_iff_Weq], [to_affine_add] and [W.commutative_group] are all
    stated and proved with [a] arbitrary.  Two things ARE missing and are
    worked around here:

    - [Projective.to_affine_of_affine] does not exist in this fiat-crypto
      revision (only [Jacobian.to_affine_of_affine] does).  Consequences:
      (i) [Group.commutative_group_by_isomorphism] cannot be used off the
      shelf to give [Projective.point] a group structure, so each law is
      transported individually below; (ii)
      [src/Bedrock/Curve/P256Curve_G1_bedrock.v:94-95] cites it and so
      cannot compile as written, even though [src/Bedrock/dune] does not
      exclude that file.

    - [Projective.add] is PARTIAL: it takes [not_exceptional P Q].  That
      is not an artefact — RCB Algorithm 1 returns (0,0,0), which is not
      a projective point at all, exactly when P - Q has order two.  For a
      prime-order curve no such point exists, but fiat-crypto proves no
      such thing ([Curves/Weierstrass/P256.p256_mul_mod_n] is itself
      [Admitted]).  §0b reduces the side condition to the single
      arithmetic fact [no_two_torsion] (x^3 + a x + b has no root in F);
      what remains open is that fact for a NAMED curve, which is a
      number-theoretic statement about the concrete modulus, not
      anything about the addition law.

    ** Location **

    Under [src/Bedrock/] rather than [src/Theory/WordByWordMontgomery/]:
    [src/Theory/dune] declares [(theories Stdlib Crypto Coqprime)] and so
    a file there cannot Require [Bedrock.Group.CurveAdd.CurveAddGeneralA].
    This directory is the CurveAddGeneralA neighbourhood; the
    Projective/W neighbourhood ([src/Bedrock/Curve/P521Curve_G1.v],
    [P256Curve_G1_bedrock.v]) is the model for the instantiation style. *)

From Stdlib Require Import ZArith Znumtheory Lia.
From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.

Local Open Scope F_scope.

(* ================================================================== *)
(** ** 0a. Two rearrangements in an arbitrary abelian group            *)
(* ================================================================== *)

(** The only new algebra §0b needs.  It is done here, over an abstract
    [Hierarchy.commutative_group], so that the setoid rewrites run
    against the class projections instead of against [W.add] / [W.opp]
    (whose implicit arguments carry the curve constants, the field
    instance and the characteristic instance, and whose unfolding drags
    in the [abstract]ed obligations of [W.commutative_group]).  Nothing
    in this section knows about curves. *)

Section AbelianRearrangement.

  Context {T : Type} {Teq : T -> T -> Prop} {Top : T -> T -> T}
          {Tid : T} {Tinv : T -> T}
          {Tgroup : @Hierarchy.commutative_group T Teq Top Tid Tinv}.

  (** [(x*y)^2 = x^2 * y^2].  Five rewrites; the group is abelian. *)
  Lemma op_square (x y : T) :
    Teq (Top (Top x y) (Top x y)) (Top (Top x x) (Top y y)).
  Proof.
    rewrite <- (@Hierarchy.associative T Teq Top _ x y (Top x y)).
    rewrite (@Hierarchy.associative T Teq Top _ y x y).
    rewrite (@Hierarchy.commutative T Teq Top _ y x).
    rewrite <- (@Hierarchy.associative T Teq Top _ x y y).
    rewrite (@Hierarchy.associative T Teq Top _ x x (Top y y)).
    reflexivity.
  Qed.

  (** [2p = 2q  ->  2(p - q) = 0]. *)
  Lemma double_diff_id (p q : T) :
    Teq (Top p p) (Top q q) ->
    Teq (Top (Top p (Tinv q)) (Top p (Tinv q))) Tid.
  Proof.
    intro Hpq.
    rewrite (op_square p (Tinv q)).
    rewrite <- (@Crypto.Algebra.Group.inv_op T Teq Top Tid Tinv _ q q).
    rewrite Hpq.
    apply (@Hierarchy.right_inverse T Teq Top Tid Tinv _ (Top q q)).
  Qed.

  (** [p - q = 0  ->  p = q]. *)
  Lemma eq_of_diff_id (p q : T) :
    Teq (Top p (Tinv q)) Tid -> Teq p q.
  Proof.
    intro Hr.
    apply (proj1 (@Crypto.Algebra.Group.cancel_right
                    T Teq Top Tid Tinv _ (Tinv q) p q)).
    rewrite Hr. symmetry.
    apply (@Hierarchy.right_inverse T Teq Top Tid Tinv _ q).
  Qed.

  (** Doubling is injective as soon as the only element of order
      dividing two is the identity.  [Group.inv_unique] turns
      [r + r = 0] into [r = -r], which is the form §0b can read off
      affine coordinates. *)
  Lemma cancel_double (p q : T) :
    (forall r : T, Teq r (Tinv r) -> Teq r Tid) ->
    Teq (Top p p) (Top q q) -> Teq p q.
  Proof.
    intros Hord2 Hpq.
    apply eq_of_diff_id.
    apply Hord2.
    apply (@Crypto.Algebra.Group.inv_unique T Teq Top Tid Tinv _).
    apply double_diff_id. exact Hpq.
  Qed.

End AbelianRearrangement.

Section RcbProjectiveLaws.

  (* ================================================================ *)
  (** ** 0. The field, the curve, and the fiat-crypto instances        *)
  (* ================================================================ *)

  Context {field_parameters : FieldParameters}
          {field_parameters_ok : FieldParameters_ok}.

  Local Notation F := (F M_pos).

  (** [FieldParameters_ok.M_prime : prime M] with [M := Z.pos M_pos]. *)
  #[export] Instance prime_M_pos : Znumtheory.prime (Z.pos M_pos).
  Proof. exact M_prime. Qed.

  Add Ring Fp_ring : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  (** Characteristic bounds.  Every curve this file targets has a modulus
      far above 27; the three [Ring.char_ge] instances that
      [Projective.add] and [W.commutative_group] need follow from
      [F.char_gt]. *)
  Context (M_gt_27 : (27 < M_pos)%positive).

  #[export] Instance char_ge_3 :
    @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul 3%positive.
  Proof. intros n Hn. apply (@F.char_gt M_pos). lia. Qed.

  #[export] Instance char_ge_12 :
    @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul 12%positive.
  Proof. intros n Hn. apply (@F.char_gt M_pos). lia. Qed.

  #[export] Instance char_ge_21 :
    @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul 21%positive.
  Proof. intros n Hn. apply (@F.char_gt M_pos). lia. Qed.

  (** The curve y^2 = x^3 + a x + b and the constant [three_b] the RCB
      chain multiplies by: exactly the arguments [Projective.add] takes.
      [Hdisc] is written in the expanded form of Projective.v's local
      notations ([4 := 1+1+1+1], [27 := 4*4+4+4+1+1+1]) so that it is the
      very term fiat-crypto expects. *)
  Context (a b three_b : F).
  Context (Hthree_b : three_b = b + b + b).
  Context (Hdisc : id
    ((((1 + 1 + 1 + 1) * a * a * a
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) <> 0)%F)).

  Local Notation Wpoint := (@W.point F eq F.add F.mul a b).

  Local Notation Ppoint :=
    (@Projective.point F eq F.zero F.add F.mul a b).

  Local Notation Peq :=
    (@Projective.eq F eq F.zero F.add F.mul a b _).

  Local Notation Ptoaff :=
    (@Projective.to_affine F eq F.zero F.one F.opp F.add F.sub F.mul
       F.inv F.div a b _ _).

  Local Notation Pnot_exceptional :=
    (@Projective.not_exceptional F eq F.zero F.one F.opp F.add F.sub
       F.mul F.inv F.div a b _ char_ge_3 _).

  Local Notation Padd :=
    (@Projective.add F eq F.zero F.one F.opp F.add F.sub F.mul F.inv
       F.div a b _ char_ge_3 _ three_b Hthree_b Hdisc char_ge_21).

  (** The affine group.  [associative], [commutative], [left_identity],
      [right_identity], [left_inverse], [right_inverse] and
      [W.Proper_add] all come from here. *)
  #[export] Instance Wgroup : Hierarchy.commutative_group (T := Wpoint) :=
    W.commutative_group (a := a) (b := b) char_ge_3
      (char_ge_12 := char_ge_12) (discriminant_nonzero := Hdisc).

  (* ================================================================ *)
  (** ** 0b. Totality of [Projective.add]                              *)
  (* ================================================================ *)

  (** [Projective.not_exceptional P Q] says [2p = 2q -> p = q] for the
      affine images.  It fails exactly when [p - q] is an F-rational
      point of order two, i.e. when x^3 + a x + b has a root in F.  For
      the prime-order NIST curves there is no such root; that is a
      per-curve number-theoretic fact about the concrete modulus, and it
      is the hypothesis of [not_exceptional_of_no_two_torsion] below. *)
  Definition no_two_torsion : Prop :=
    forall x : F, ((x * x * x + a * x + b) <> 0)%F.

  (** Step 1 of the argument: an affine point equal to its own negative
      is the identity.  Reading coordinates, [r = inl (x,y)] and
      [r = -r] force [y = -y], hence [y = 0] (characteristic <> 2),
      hence [x^3 + a x + b = y^2 = 0], contradicting [no_two_torsion].
      The point at infinity is the identity outright. *)
  Lemma W_self_opp_zero (Hno : no_two_torsion) (r : Wpoint) :
    W.eq r (W.opp r) -> W.eq r W.zero.
  Proof.
    cbv [no_two_torsion] in Hno.
    destruct r as [[[x y] | []] Hr];
      cbv [W.eq W.opp W.zero W.coordinates proj1_sig] in *.
    - intros [_ Hy].
      assert (Hy0 : y = 0%F) by fsatz.
      apply (Hno x). fsatz.
    - intros _. exact I.
  Qed.

  (** Steps 2 and 3: [2p = 2q] gives [2(p - q) = 0] ([double_diff_id]),
      hence [p - q = -(p - q)] ([Group.inv_unique]), hence [p - q = 0]
      by step 1, hence [p = q] ([eq_of_diff_id]).  That chain is
      [cancel_double] of §0a, instantiated at the affine group
      [Wgroup]; [Projective.not_exceptional] IS its hypothesis-to-
      conclusion shape, by [cbv]/zeta over the two [let]s. *)
  Lemma not_exceptional_of_no_two_torsion :
    no_two_torsion -> forall P Q : Ppoint, Pnot_exceptional P Q.
  Proof.
    intros Hno P Q.
    cbv [Projective.not_exceptional].
    intro Hdbl.
    first
      [ exact (@cancel_double Wpoint _ _ _ _ Wgroup _ _
                 (W_self_opp_zero Hno) Hdbl)
      | eapply (cancel_double (Tgroup := Wgroup));
        [ exact (W_self_opp_zero Hno) | exact Hdbl ]
      | eapply cancel_double;
        [ exact (W_self_opp_zero Hno) | exact Hdbl ] ].
  Qed.

  (** The rest of the file is parametric in totality. *)
  Context (Hexcept : forall P Q : Ppoint, Pnot_exceptional P Q).

  Local Notation padd P Q := (Padd P Q (Hexcept P Q)).

  (* ================================================================ *)
  (** ** 1. The relation [pt_eq] and the on-curve predicate            *)
  (* ================================================================ *)

  (** [pt_eq] is [Projective.eq] read off raw triples; the two are
      convertible (see [pt_eq_Peq]).  It is an equivalence on ALL of
      [F*F*F], with no on-curve side condition. *)
  Definition pt_eq (P Q : F * F * F) : Prop :=
    match P, Q with
    | (X1, Y1, Z1), (X2, Y2, Z2) =>
      if dec (Z1 = 0%F) then Z2 = 0%F
      else if dec (Z2 = 0%F) then False
           else (X1 * Z2)%F = (X2 * Z1)%F /\ (Y1 * Z2)%F = (Y2 * Z1)%F
    end.

  (** The sig-predicate of [Projective.point], spelled out. *)
  Definition oncurve (P : F * F * F) : Prop :=
    let '(X, Y, Z) := P in
    (Y * Y * Z)%F
      = (X * (X * X) + a * X * (Z * Z) + b * (Z * (Z * Z)))%F
    /\ (Z = 0%F -> Y <> 0%F).

  Definition mkP (p : F * F * F) (H : oncurve p) : Ppoint := exist _ p H.

  Lemma pt_eq_refl P : pt_eq P P.
  Proof.
    destruct P as [[X Y] Z]; cbv [pt_eq].
    destruct (dec (Z = 0%F)) as [e | n]; [exact e | split; reflexivity].
  Qed.

  Lemma pt_eq_sym P Q : pt_eq P Q -> pt_eq Q P.
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2]; cbv [pt_eq].
    destruct (dec (Z1 = 0%F)) as [e1 | n1], (dec (Z2 = 0%F)) as [e2 | n2];
      intros H; try contradiction; try assumption.
    destruct H as [H1 H2]; split; symmetry; assumption.
  Qed.

  Lemma pt_eq_trans P Q R : pt_eq P Q -> pt_eq Q R -> pt_eq P R.
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2], R as [[X3 Y3] Z3];
      cbv [pt_eq].
    destruct (dec (Z1 = 0%F)) as [e1 | n1], (dec (Z2 = 0%F)) as [e2 | n2],
             (dec (Z3 = 0%F)) as [e3 | n3];
      intros H1 H2; try contradiction; try assumption.
    destruct H1 as [Hxa Hya], H2 as [Hxb Hyb]; split; fsatz.
  Qed.

  #[export] Instance pt_eq_Equivalence : Equivalence pt_eq.
  Proof.
    split; [exact pt_eq_refl | exact pt_eq_sym | exact pt_eq_trans].
  Qed.

  (** [pt_eq] IS [Projective.eq], by conversion. *)
  Lemma pt_eq_Peq (P Q : Ppoint) :
    pt_eq (proj1_sig P) (proj1_sig Q) <-> Peq P Q.
  Proof. split; exact (fun H => H). Qed.

  (** ... hence it is the pullback of [W.eq] along [to_affine]. *)
  Lemma pt_eq_iff_Weq (P Q : Ppoint) :
    pt_eq (proj1_sig P) (proj1_sig Q) <-> W.eq (Ptoaff P) (Ptoaff Q).
  Proof. exact (Projective.eq_iff_Weq P Q). Qed.

  Lemma toaff_congr (P Q : Ppoint) :
    proj1_sig P = proj1_sig Q -> W.eq (Ptoaff P) (Ptoaff Q).
  Proof.
    intro H. apply pt_eq_iff_Weq. rewrite H. apply pt_eq_refl.
  Qed.

  (* ================================================================ *)
  (** ** 2. [rcb_add_general_gallina] IS [Projective.add]              *)
  (* ================================================================ *)

  (** The chain's Gallina model on plain triples.  Syntactically the same
      definition as [NistWnafWrappers.curve_add_general_triple], repeated
      here so that this file does not depend on that (bedrock2-heavy)
      wrapper file. *)
  Definition cadd (P Q : F * F * F) : F * F * F :=
    let '(X1, Y1, Z1) := P in
    let '(X2, Y2, Z2) := Q in
    let '\<x, y, z\> :=
      @rcb_add_general_gallina _ a three_b X1 Y1 Z1 X2 Y2 Z2 in
    (x, y, z).

  (** As in [BLS12_wNAF_ProcessDigits.point_opp]. *)
  Definition point_opp_triple (P : F * F * F) : F * F * F :=
    let '(X, Y, Z) := P in (X, F.opp Y, Z).

  Definition id_pt : F * F * F := (0%F, 1%F, 0%F).

  (** The forty [let/n] steps of [rcb_add_general_gallina] are the forty
      [let]s of [Projective.add] in the same order, with a single
      difference: step S23 writes [outz + t1] where fiat-crypto writes
      [t1 + Z3].  [ring] closes the three resulting coordinate goals. *)
  Lemma cadd_is_Padd (P Q : Ppoint) :
    cadd (proj1_sig P) (proj1_sig Q) = proj1_sig (padd P Q).
  Proof.
    destruct P as [[[X1 Y1] Z1] HP], Q as [[[X2 Y2] Z2] HQ].
    cbv [cadd proj1_sig Projective.add rcb_add_general_gallina
         nlet stack P2.car P2.cdr].
    apply pair_equal_spec; split; [apply pair_equal_spec; split |]; ring.
  Qed.

  Lemma cadd_raw (p q : F * F * F) (Hp : oncurve p) (Hq : oncurve q) :
    cadd p q = proj1_sig (padd (mkP p Hp) (mkP q Hq)).
  Proof. exact (cadd_is_Padd (mkP p Hp) (mkP q Hq)). Qed.

  (* ================================================================ *)
  (** ** 3. Closure of the on-curve predicate                          *)
  (* ================================================================ *)

  Lemma oncurve_id : oncurve id_pt.
  Proof. cbv [oncurve id_pt]; split; [ring | intros _; fsatz]. Qed.

  Lemma oncurve_opp (p : F * F * F) :
    oncurve p -> oncurve (point_opp_triple p).
  Proof.
    destruct p as [[X Y] Z]; cbv [oncurve point_opp_triple];
      intros [H1 H2]; split.
    - rewrite <- H1; ring.
    - intros HZ HY; apply (H2 HZ); fsatz.
  Qed.

  Lemma oncurve_cadd (p q : F * F * F) (Hp : oncurve p) (Hq : oncurve q) :
    oncurve (cadd p q).
  Proof.
    rewrite (cadd_raw p q Hp Hq).
    exact (proj2_sig (padd (mkP p Hp) (mkP q Hq))).
  Qed.

  (* ================================================================ *)
  (** ** 4. Affine images, and the group laws up to [pt_eq]            *)
  (* ================================================================ *)

  Lemma cadd_toaff (p q : F * F * F) (Hp : oncurve p) (Hq : oncurve q) :
    W.eq (Ptoaff (mkP (cadd p q) (oncurve_cadd p q Hp Hq)))
         (W.add (Ptoaff (mkP p Hp)) (Ptoaff (mkP q Hq))).
  Proof.
    etransitivity;
      [ apply toaff_congr; exact (cadd_raw p q Hp Hq)
      | apply Projective.to_affine_add ].
  Qed.

  Lemma toaff_id : W.eq (Ptoaff (mkP id_pt oncurve_id)) W.zero.
  Proof.
    cbv [Projective.to_affine mkP id_pt proj1_sig W.eq W.zero
         W.coordinates].
    destruct (dec (@eq F 0%F 0%F)) as [_ | n]; cbn;
      [ exact I | exfalso; apply n; reflexivity ].
  Qed.

  Lemma toaff_opp (p : F * F * F) (Hp : oncurve p) :
    W.eq (Ptoaff (mkP (point_opp_triple p) (oncurve_opp p Hp)))
         (W.opp (Ptoaff (mkP p Hp))).
  Proof.
    destruct p as [[X Y] Z].
    cbv [Projective.to_affine mkP point_opp_triple proj1_sig W.opp W.eq
         W.coordinates].
    destruct (dec (Z = 0%F)) as [e | n]; cbn;
      [ exact I | split; [ reflexivity | fsatz ] ].
  Qed.

  (** *** 4a. [cadd] is a morphism for [pt_eq] on on-curve triples. *)
  Theorem cadd_Proper (p p' q q' : F * F * F) :
    oncurve p -> oncurve p' -> oncurve q -> oncurve q' ->
    pt_eq p p' -> pt_eq q q' -> pt_eq (cadd p q) (cadd p' q').
  Proof.
    intros Hp Hp' Hq Hq' Ep Eq.
    assert (H1 : W.eq (Ptoaff (mkP p Hp)) (Ptoaff (mkP p' Hp')))
      by (apply pt_eq_iff_Weq; exact Ep).
    assert (H2 : W.eq (Ptoaff (mkP q Hq)) (Ptoaff (mkP q' Hq')))
      by (apply pt_eq_iff_Weq; exact Eq).
    apply (proj2 (pt_eq_iff_Weq
                    (mkP (cadd p q) (oncurve_cadd p q Hp Hq))
                    (mkP (cadd p' q') (oncurve_cadd p' q' Hp' Hq')))).
    rewrite (cadd_toaff p q Hp Hq), (cadd_toaff p' q' Hp' Hq').
    rewrite H1, H2. reflexivity.
  Qed.

  (** *** 4a'. [point_opp_triple] is a morphism for [pt_eq].

      Needed by the quotiented chain: [digit_point] negates a table
      entry, so the table's [pt_eq] correctness has to survive
      negation.  The affine [W.opp] is a morphism because
      [Hierarchy.group] carries [group_inv_Proper]. *)
  Theorem point_opp_Proper (p p' : F * F * F) :
    oncurve p -> oncurve p' -> pt_eq p p' ->
    pt_eq (point_opp_triple p) (point_opp_triple p').
  Proof.
    intros Hp Hp' Ep.
    assert (H1 : W.eq (Ptoaff (mkP p Hp)) (Ptoaff (mkP p' Hp')))
      by (apply pt_eq_iff_Weq; exact Ep).
    apply (proj2 (pt_eq_iff_Weq
                    (mkP (point_opp_triple p) (oncurve_opp p Hp))
                    (mkP (point_opp_triple p') (oncurve_opp p' Hp')))).
    rewrite (toaff_opp p Hp), (toaff_opp p' Hp').
    rewrite H1. reflexivity.
  Qed.

  (** *** 4b. Commutativity. *)
  Theorem cadd_comm (p q : F * F * F) :
    oncurve p -> oncurve q -> pt_eq (cadd p q) (cadd q p).
  Proof.
    intros Hp Hq.
    apply (proj2 (pt_eq_iff_Weq
                    (mkP (cadd p q) (oncurve_cadd p q Hp Hq))
                    (mkP (cadd q p) (oncurve_cadd q p Hq Hp)))).
    rewrite (cadd_toaff p q Hp Hq), (cadd_toaff q p Hq Hp).
    apply Hierarchy.commutative.
  Qed.

  (** *** 4c. Associativity, in the chain's orientation. *)
  Theorem cadd_assoc (p q r : F * F * F) :
    oncurve p -> oncurve q -> oncurve r ->
    pt_eq (cadd p (cadd q r)) (cadd (cadd p q) r).
  Proof.
    intros Hp Hq Hr.
    apply (proj2 (pt_eq_iff_Weq
                    (mkP (cadd p (cadd q r))
                         (oncurve_cadd p (cadd q r) Hp
                            (oncurve_cadd q r Hq Hr)))
                    (mkP (cadd (cadd p q) r)
                         (oncurve_cadd (cadd p q) r
                            (oncurve_cadd p q Hp Hq) Hr)))).
    rewrite (cadd_toaff p (cadd q r) Hp (oncurve_cadd q r Hq Hr)).
    rewrite (cadd_toaff q r Hq Hr).
    rewrite (cadd_toaff (cadd p q) r (oncurve_cadd p q Hp Hq) Hr).
    rewrite (cadd_toaff p q Hp Hq).
    apply Hierarchy.associative.
  Qed.

  (** *** 4d. (0,1,0) is a two-sided identity. *)
  Theorem cadd_id_r (p : F * F * F) : oncurve p -> pt_eq (cadd p id_pt) p.
  Proof.
    intros Hp.
    apply (proj2 (pt_eq_iff_Weq
                    (mkP (cadd p id_pt) (oncurve_cadd p id_pt Hp oncurve_id))
                    (mkP p Hp))).
    rewrite (cadd_toaff p id_pt Hp oncurve_id), toaff_id.
    apply Hierarchy.right_identity.
  Qed.

  Theorem cadd_id_l (p : F * F * F) : oncurve p -> pt_eq (cadd id_pt p) p.
  Proof.
    intros Hp.
    apply (proj2 (pt_eq_iff_Weq
                    (mkP (cadd id_pt p) (oncurve_cadd id_pt p oncurve_id Hp))
                    (mkP p Hp))).
    rewrite (cadd_toaff id_pt p oncurve_id Hp), toaff_id.
    apply Hierarchy.left_identity.
  Qed.

  (** *** 4e. [point_opp_inverse]. *)
  Theorem point_opp_inverse (p : F * F * F) :
    oncurve p -> pt_eq (cadd p (point_opp_triple p)) id_pt.
  Proof.
    intros Hp.
    apply (proj2 (pt_eq_iff_Weq
                    (mkP (cadd p (point_opp_triple p))
                         (oncurve_cadd p (point_opp_triple p) Hp
                            (oncurve_opp p Hp)))
                    (mkP id_pt oncurve_id))).
    rewrite (cadd_toaff p (point_opp_triple p) Hp (oncurve_opp p Hp)).
    rewrite (toaff_opp p Hp), toaff_id.
    apply Hierarchy.right_inverse.
  Qed.

  Theorem point_opp_inverse_l (p : F * F * F) :
    oncurve p -> pt_eq (cadd (point_opp_triple p) p) id_pt.
  Proof.
    intros Hp.
    eapply pt_eq_trans;
      [ apply cadd_comm; [ apply oncurve_opp; exact Hp | exact Hp ]
      | apply point_opp_inverse; exact Hp ].
  Qed.

End RcbProjectiveLaws.

(* ================================================================== *)
(** ** 5. How the wNAF chain's Section hypotheses would be met         *)
(* ================================================================== *)

(** UPDATE: phase 2 has landed.  wNAF_Single_HornerAlgebra.v,
    wNAF_Single_LoopBody.v and wNAF_Single_Proof.v now take [pt_eq],
    [oncurve] and the closure/congruence hypotheses as Section
    parameters, and P256_wNAF_Instance.v §1b discharges them from this
    file.  wNAF_Single_LoadAndProcess.v was left Leibniz, as predicted
    below; it only lost its two (unused) group-law Contexts and gained
    the [opp_name] parameter of plan item G5.  The mapping recorded here
    is the one that was used.

    This section records the mapping.

    The chain's abstract interface (wNAF_Single_HornerAlgebra.v, Section
    SingleHornerAlgebra; mirrored in BLS12_wNAF_ProcessDigits.v and
    consumed by wNAF_Single_LoopBody.v / wNAF_Single_Proof.v /
    BN254_wNAF_Instance.wnaf_single_full) is

      Context {F : Type} (Fzero Fone : F).
      Let Point := (F * F * F)%type.
      Let id : Point := (Fzero, Fone, Fzero).
      Context (curve_add : Point -> Point -> Point).
      Context (point_opp : Point -> Point).
      Context (curve_add_id_r  : forall x y z, curve_add (x,y,z) id = (x,y,z)).
      Context (curve_add_id_l  : forall x y z, curve_add id (x,y,z) = (x,y,z)).
      Context (curve_add_assoc : forall P Q R,
                 curve_add P (curve_add Q R) = curve_add (curve_add P Q) R).
      Context (curve_add_comm  : forall P Q, curve_add P Q = curve_add Q P).
      Context (point_opp_inverse : forall P, curve_add P (point_opp P) = id).

    instantiated at [F := F M_pos], [Fzero := F.zero], [Fone := F.one],
    [curve_add := cadd] (= [NistWnafWrappers.curve_add_general_triple a
    three_b]), [point_opp := point_opp_triple].  Its [id] is literally
    [id_pt = (0,1,0)].

    Restating the invariant with [pt_eq] means: replace every [=] between
    POINTS in those five hypotheses (and in [sm], [sm_Z],
    [digit_point_local], [horner_step_single], and the loop invariants of
    wNAF_Single_LoopBody.v / _Proof.v) by [pt_eq], and carry an [oncurve]
    conjunct alongside every point-valued quantity.  The bedrock2
    postconditions of wNAF_Single_LoadAndProcess.v stay Leibniz: they
    describe the raw computation, not the group.

    Hypothesis-by-hypothesis:

    - [curve_add_id_r]  ->  [oncurve p -> pt_eq (cadd p id_pt) p]
                            discharged by [cadd_id_r].
    - [curve_add_id_l]  ->  [oncurve p -> pt_eq (cadd id_pt p) p]
                            discharged by [cadd_id_l].
    - [curve_add_assoc] ->  [oncurve p -> oncurve q -> oncurve r ->
                             pt_eq (cadd p (cadd q r)) (cadd (cadd p q) r)]
                            discharged by [cadd_assoc].
    - [curve_add_comm]  ->  [oncurve p -> oncurve q ->
                             pt_eq (cadd p q) (cadd q p)]
                            discharged by [cadd_comm].
    - [point_opp_inverse] -> [oncurve p ->
                             pt_eq (cadd p (point_opp_triple p)) id_pt]
                            discharged by [point_opp_inverse].
    - NEW, forced by the quotient: [Equivalence pt_eq] — discharged by
      [pt_eq_Equivalence]; congruence of [cadd] — discharged by
      [cadd_Proper]; on-curve closure — discharged by [oncurve_cadd],
      [oncurve_opp], [oncurve_id].

    Which of the chain's own lemmas become trivial, and which do not:

    - [add_id_r'], [add_id_l'], [sm_add], [point_opp_inverse_l],
      [sm_sub], [sm_Z_nonneg], [sm_Z_neg], [sm_Z_zero],
      [sm_Z_add_nonneg]: replay verbatim with [rewrite] replaced by
      [setoid_rewrite] under [pt_eq], once [sm] is known to be
      [pt_eq]-Proper and on-curve-preserving.  Both follow from
      [cadd_Proper] / [oncurve_cadd] by induction on the exponent; that
      induction is the only genuinely new proof obligation the chain
      acquires, and it is four lines.  [point_opp_inverse_l] is already
      proved above.

    - [point_opp_id], [curve_add_cancel_l], [point_opp_opp]: these use
      cancellation, which holds up to [pt_eq] for the same reason it
      holds in the affine group; the existing proofs replay.

    - [digit_point_is_sm_Z] and [horner_step_single]: replay, EXCEPT that
      their table hypothesis
        [forall i, (i < 4)%nat -> nth i table_entries id = sm (2*i+1) P]
      must become
        [forall i, (i < 4)%nat ->
           oncurve (nth i table_entries id_pt)
           /\ pt_eq (nth i table_entries id_pt) (sm (2*i+1) P)].
      This file does NOT discharge that.  The table is caller-supplied
      memory (nist_scalar_mult_plan.md, G7), so its correctness is a
      property of the producer (a verified [precompute_w4], or a
      hypothesis on the Rust caller's table), not of the addition
      formula.  It is the one hypothesis in the list that this file
      leaves open.

    - The [wnaf_single_full] conclusion changes from a Leibniz equation
      between the output triple and [scmul k P] to [pt_eq] between them,
      plus [oncurve] of the output.  A consumer needing a canonical
      representative must normalise (divide through by Z, or map Z = 0 to
      (0,1,0)); [pt_eq] is exactly the equivalence under which that
      normalisation is sound.

    One further consequence, for plan item G3: with the invariant
    quotiented, [CurveDoubleGeneralA]'s dedicated body becomes pluggable
    into the [curve_double] slot, because its output is [pt_eq] to
    [cadd P P] although not Leibniz-equal to it. *)
