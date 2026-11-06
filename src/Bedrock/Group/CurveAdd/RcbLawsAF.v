(** * Group laws of the a = 0 RCB formulas over an arbitrary field.

    [RcbProjectiveLaws.v] proves the laws for the general-a chain over the
    prime field [F M_pos].  fiat-crypto's [Projective.add] is stated over
    any [Hierarchy.field] with decidable equality and characteristic at
    least 3, so the same transport works over Fp2.  This file restates it
    for the two chains of [CurveAddAF.v] ([af_add_gallina],
    [af_double_gallina]) over an [AbstractField.FieldParameters] whose
    equality is Leibniz [eq], at a = 0:

    - [cadd_is_Padd]: the addition chain IS [Projective.add] (Leibniz
      equality of the triples), for every pair of on-curve points;
    - [cdbl_is_cadd]: on the curve, the doubling chain equals the
      addition chain on a repeated argument (Leibniz);
    - [not_exceptional_of_no_two_torsion]: [Projective.add] is total when
      x^3 + b has no root;
    - [pt_eq] (= [Projective.eq]) is an equivalence, [cadd] is a morphism,
      commutative, associative, with identity (0 : 1 : 0), all up to
      [pt_eq] on on-curve triples.

    The proofs are those of [RcbProjectiveLaws.v] (ported) and
    [PointDoubleA0.rcb_double_a0_eq_ladderstep] (ported); [ring] runs
    over the abstract field.  No Admitted, no Axiom. *)

From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import Rupicola.Lib.Api.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Affine.
Require Import Crypto.Curves.Weierstrass.AffineProofs.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Import Bedrock.Specs.AbstractField.
Require Import Bedrock.Group.CurveAdd.CurveAddAF.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.

Section RcbLawsAF.
  Context {F : Type} {fp : AbstractField.FieldParameters F}.

  Local Notation Fzero := (@AbstractField.Fzero F fp).
  Local Notation Fone := (@AbstractField.Fone F fp).
  Local Notation Fopp := (@AbstractField.Fopp F fp).
  Local Notation Fadd := (@AbstractField.Fadd F fp).
  Local Notation Fsub := (@AbstractField.Fsub F fp).
  Local Notation Fmul := (@AbstractField.Fmul F fp).
  Local Notation Finv := (@AbstractField.Finv F fp).
  Local Notation Fdiv := (@AbstractField.Fdiv F fp).

  Context {fld : @Hierarchy.field F eq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv}.
  Context {Feq_dec : DecidableRel (@eq F)}.
  Context {char_ge_3 : @Ring.char_ge F eq Fzero Fone Fopp Fadd Fsub Fmul
                         (BinNat.N.succ_pos BinNat.N.two)}.
  Context {char_ge_12 : @Ring.char_ge F eq Fzero Fone Fopp Fadd Fsub Fmul 12%positive}.
  Context {char_ge_21 : @Ring.char_ge F eq Fzero Fone Fopp Fadd Fsub Fmul 21%positive}.

  Local Infix "+" := Fadd. Local Infix "-" := Fsub. Local Infix "*" := Fmul.
  Local Notation "0" := Fzero. Local Notation "1" := Fone.

  Add Ring af_ring : (@Ring.ring_theory_for_stdlib_tactic F (@eq F) Fzero Fone Fopp Fadd Fsub Fmul _).

  Context (b three_b : F).
  Context (Hthree_b : three_b = b + b + b).
  Context (Hdisc : id
    (((1 + 1 + 1 + 1) * 0 * 0 * 0
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * b * b) <> 0)).

  Local Notation Wpoint := (@W.point F eq Fadd Fmul 0 b).
  Local Notation Ppoint := (@Projective.point F eq Fzero Fadd Fmul 0 b).
  Local Notation Peq := (@Projective.eq F eq Fzero Fadd Fmul 0 b _).
  Local Notation Ptoaff :=
    (@Projective.to_affine F eq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv 0 b _ _).
  Local Notation Pnot_exceptional :=
    (@Projective.not_exceptional F eq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv
       0 b _ char_ge_3 _).
  Local Notation Padd :=
    (@Projective.add F eq Fzero Fone Fopp Fadd Fsub Fmul Finv Fdiv 0 b _ char_ge_3 _
       three_b Hthree_b Hdisc char_ge_21).

  #[local] Instance Wgroup : Hierarchy.commutative_group (T := Wpoint) :=
    W.commutative_group (a := 0) (b := b) char_ge_3
      (char_ge_12 := char_ge_12) (discriminant_nonzero := Hdisc).

  (** ** Totality *)

  Definition no_two_torsion : Prop := forall x : F, x * x * x + 0 * x + b <> 0.

  Lemma W_self_opp_zero (Hno : no_two_torsion) (r : Wpoint) :
    W.eq r (W.opp r) -> W.eq r W.zero.
  Proof.
    cbv [no_two_torsion] in Hno.
    destruct r as [[[x y] | []] Hr];
      cbv [W.eq W.opp W.zero W.coordinates proj1_sig] in *.
    - intros [_ Hy].
      assert (Hy0 : y = 0) by fsatz.
      apply (Hno x). fsatz.
    - intros _. exact I.
  Qed.

  Lemma not_exceptional_of_no_two_torsion :
    no_two_torsion -> forall P Q : Ppoint, Pnot_exceptional P Q.
  Proof.
    intros Hno P Q.
    cbv [Projective.not_exceptional].
    intro Hdbl.
    exact (@cancel_double Wpoint _ _ _ _ Wgroup _ _ (W_self_opp_zero Hno) Hdbl).
  Qed.

  Context (Hexcept : forall P Q : Ppoint, Pnot_exceptional P Q).
  Local Notation padd P Q := (Padd P Q (Hexcept P Q)).

  (** ** [pt_eq], [oncurve] *)

  Definition pt_eq (P Q : F * F * F) : Prop :=
    match P, Q with
    | (X1, Y1, Z1), (X2, Y2, Z2) =>
      if dec (Z1 = 0) then Z2 = 0
      else if dec (Z2 = 0) then False
           else X1 * Z2 = X2 * Z1 /\ Y1 * Z2 = Y2 * Z1
    end.

  Definition oncurve (P : F * F * F) : Prop :=
    let '(X, Y, Z) := P in
    Y * Y * Z = X * (X * X) + 0 * X * (Z * Z) + b * (Z * (Z * Z))
    /\ (Z = 0 -> Y <> 0).

  Definition mkP (p : F * F * F) (H : oncurve p) : Ppoint := exist _ p H.

  Lemma pt_eq_refl P : pt_eq P P.
  Proof.
    destruct P as [[X Y] Z]; cbv [pt_eq].
    destruct (dec (Z = 0)) as [e | n]; [exact e | split; reflexivity].
  Qed.

  Lemma pt_eq_sym P Q : pt_eq P Q -> pt_eq Q P.
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2]; cbv [pt_eq].
    destruct (dec (Z1 = 0)) as [e1 | n1], (dec (Z2 = 0)) as [e2 | n2];
      intros H; try contradiction; try assumption.
    destruct H as [H1 H2]; split; symmetry; assumption.
  Qed.

  Lemma pt_eq_trans P Q R : pt_eq P Q -> pt_eq Q R -> pt_eq P R.
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2], R as [[X3 Y3] Z3];
      cbv [pt_eq].
    destruct (dec (Z1 = 0)) as [e1 | n1], (dec (Z2 = 0)) as [e2 | n2],
             (dec (Z3 = 0)) as [e3 | n3];
      intros H1 H2; try contradiction; try assumption.
    destruct H1 as [Hxa Hya], H2 as [Hxb Hyb]; split; fsatz.
  Qed.

  #[export] Instance pt_eq_Equivalence : Equivalence pt_eq.
  Proof. split; [exact pt_eq_refl | exact pt_eq_sym | exact pt_eq_trans]. Qed.

  Lemma pt_eq_iff_Weq (P Q : Ppoint) :
    pt_eq (proj1_sig P) (proj1_sig Q) <-> W.eq (Ptoaff P) (Ptoaff Q).
  Proof. exact (Projective.eq_iff_Weq P Q). Qed.

  Lemma toaff_congr (P Q : Ppoint) :
    proj1_sig P = proj1_sig Q -> W.eq (Ptoaff P) (Ptoaff Q).
  Proof. intro H. apply pt_eq_iff_Weq. rewrite H. apply pt_eq_refl. Qed.

  (** ** The chains on triples *)

  Definition cadd (P Q : F * F * F) : F * F * F :=
    let '(X1, Y1, Z1) := P in
    let '(X2, Y2, Z2) := Q in
    let '\<x, y, z\> := @af_add_gallina F fp three_b X1 X2 Y1 Y2 Z1 Z2 in
    (x, y, z).

  Definition cdbl (P : F * F * F) : F * F * F :=
    let '(X, Y, Z) := P in
    let '\<x, y, z\> := @af_double_gallina F fp three_b X Y Z in
    (x, y, z).

  Definition id_pt : F * F * F := (0, 1, 0).

  (** Algorithm 7 is [Projective.add] at a = 0: three ring identities. *)
  Lemma cadd_is_Padd (P Q : Ppoint) :
    cadd (proj1_sig P) (proj1_sig Q) = proj1_sig (padd P Q).
  Proof.
    destruct P as [[[X1 Y1] Z1] HP], Q as [[[X2 Y2] Z2] HQ].
    cbv [cadd proj1_sig Projective.add af_add_gallina nlet stack P2.car P2.cdr].
    apply pair_equal_spec; split; [apply pair_equal_spec; split |]; ring.
  Qed.

  Lemma cadd_raw (p q : F * F * F) (Hp : oncurve p) (Hq : oncurve q) :
    cadd p q = proj1_sig (padd (mkP p Hp) (mkP q Hq)).
  Proof. exact (cadd_is_Padd (mkP p Hp) (mkP q Hq)). Qed.

  Lemma sub_eq_zero_eq (x y : F) : x - y = 0 -> x = y.
  Proof. intros H. transitivity ((x - y) + y); [ | rewrite H ]; ring. Qed.

  (** Algorithm 9 is Algorithm 7 on a repeated argument, on the curve:
      cofactors 0, 6 * 3b * Z and 6 * Y against Y^2 Z - X^3 - b Z^3. *)
  Lemma cdbl_is_cadd (P : F * F * F) : oncurve P -> cdbl P = cadd P P.
  Proof.
    destruct P as [[X Y] Z]. intros [Hon _].
    assert (Hg : Y * Y * Z - (X * (X * X) + b * (Z * (Z * Z))) = 0).
    { transitivity (Y * Y * Z - (X * (X * X) + 0 * X * (Z * Z) + b * (Z * (Z * Z)))).
      - ring.
      - rewrite Hon. ring. }
    cbv [cdbl cadd af_double_gallina af_add_gallina nlet stack P2.car P2.cdr].
    rewrite Hthree_b.
    apply pair_equal_spec; split; [apply pair_equal_spec; split | ].
    - ring.
    - apply sub_eq_zero_eq.
      transitivity
        (((((b + b + b) * Z + (b + b + b) * Z)
           + ((b + b + b) * Z + (b + b + b) * Z)
           + ((b + b + b) * Z + (b + b + b) * Z)))
         * (Y * Y * Z - (X * (X * X) + b * (Z * (Z * Z))))).
      + ring.
      + rewrite Hg; ring.
    - apply sub_eq_zero_eq.
      transitivity
        ((((Y + Y) + (Y + Y) + (Y + Y)))
         * (Y * Y * Z - (X * (X * X) + b * (Z * (Z * Z))))).
      + ring.
      + rewrite Hg; ring.
  Qed.

  (** ** Closure and affine images *)

  Lemma oncurve_id : oncurve id_pt.
  Proof. cbv [oncurve id_pt]; split; [ring | intros _; fsatz]. Qed.

  Lemma oncurve_cadd (p q : F * F * F) (Hp : oncurve p) (Hq : oncurve q) :
    oncurve (cadd p q).
  Proof.
    rewrite (cadd_raw p q Hp Hq).
    exact (proj2_sig (padd (mkP p Hp) (mkP q Hq))).
  Qed.

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
    cbv [Projective.to_affine mkP id_pt proj1_sig W.eq W.zero W.coordinates].
    destruct (dec (@eq F 0 0)) as [_ | n]; cbn;
      [ exact I | exfalso; apply n; reflexivity ].
  Qed.

  (** ** Laws up to [pt_eq] *)

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

  Theorem cadd_assoc (p q r : F * F * F) :
    oncurve p -> oncurve q -> oncurve r ->
    pt_eq (cadd p (cadd q r)) (cadd (cadd p q) r).
  Proof.
    intros Hp Hq Hr.
    apply (proj2 (pt_eq_iff_Weq
                    (mkP (cadd p (cadd q r))
                         (oncurve_cadd p (cadd q r) Hp (oncurve_cadd q r Hq Hr)))
                    (mkP (cadd (cadd p q) r)
                         (oncurve_cadd (cadd p q) r (oncurve_cadd p q Hp Hq) Hr)))).
    rewrite (cadd_toaff p (cadd q r) Hp (oncurve_cadd q r Hq Hr)).
    rewrite (cadd_toaff q r Hq Hr).
    rewrite (cadd_toaff (cadd p q) r (oncurve_cadd p q Hp Hq) Hr).
    rewrite (cadd_toaff p q Hp Hq).
    apply Hierarchy.associative.
  Qed.

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

End RcbLawsAF.
