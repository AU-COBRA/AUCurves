(** * The P-256 wNAF table, built and discharged.

    [WnafTableBuild.rcb_table4_ok] (Qed, 0 [Admitted]) says that the
    four-entry odd-multiples table [rcb_build_table4 P] satisfies the
    chain's table obligation — [length = 4], and every entry is on the
    curve and [pt_eq] to the corresponding odd multiple — on the sole
    premise [oncurve P].  It is stated over the Section variables
    [a b three_b] of that file.

    This file instantiates it at the P-256 constants of
    [P256_wNAF_Instance] and restates the conclusion in the shape that
    file's [p256_table_ok] declares, so that a caller of
    [p256_wnaf_single_full] who supplies [p256_table4 P] as
    [table_entries] discharges the G7 table hypothesis from
    [oncurve P] alone.

    [P256_wNAF_Instance.v] is NOT edited: the corollary lives here and
    is applied by the caller.

    Contents:
      §1  Context: the five curve-level side conditions of
          [P256_wNAF_Instance] §1b, verbatim.
      §2  [p256_table4] and its correctness ([p256_rcb_table4_ok]).
      §3  The bridge to [P256_wNAF_Instance.p256_table_ok].
      §4  Totality of [Projective.add] at P-256 from [no_two_torsion].
      §5  What this discharges, and what remains.

    Honesty ledger: no [Admitted] and no [Axiom] in this file, and none
    inherited — RcbProjectiveLaws.v and WnafTableBuild.v are both
    [Admitted]-free.  Everything below is conditional on the five
    Section hypotheses of §1, exactly as [P256_wNAF_Instance] is. *)

From Stdlib Require Import ZArith Znumtheory Lia List.
From Stdlib Require Import RelationClasses Morphisms Setoid.
Require Import Rupicola.Lib.Api.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
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
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Bedrock.Field.Synthesis.Examples.p256_prime.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.ScalarMult.WnafTableBuild.
Require Import Bedrock.Group.ScalarMult.P256_wNAF_Instance.

Section P256_wNAF_Table.

  (* ================================================================ *)
  (** ** 1. Context                                                    *)
  (* ================================================================ *)

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    p256_field_parameters
    p256_field_parameters_ok
    p256_frep
    p256_frep_ok.

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).

  (** The five curve-level side conditions of [P256_wNAF_Instance] §1b.
      [p256_a_val] and [p256_three_b_val] are closed constants of that
      file (they are [feval] of the stored Montgomery felems), and
      [p256_b_val], [p256_M_gt_27], [p256_Hthree_b] and [p256_Hdisc] are
      now closed constants of it too — they are imported, not restated.
      Only [p256_Hexcept] below is still a hypothesis. *)

  Local Notation P256_Ppoint :=
    (@Projective.point F eq F.zero F.add F.mul p256_a_val p256_b_val).

  (** [RcbProjectiveLaws.char_ge_3 p256_M_gt_27] is what
      [P256_wNAF_Instance.p256_char_ge_3] is defined to be, and what
      [WnafTableBuild] §3 writes; spelling it out here keeps the three
      [Projective.not_exceptional] terms syntactically equal. *)
  Local Notation P256_not_exceptional :=
    (@Projective.not_exceptional F eq F.zero F.one F.opp F.add F.sub
       F.mul F.inv F.div p256_a_val p256_b_val _
       (RcbProjectiveLaws.char_ge_3 p256_M_gt_27) _).

  Context (p256_Hexcept :
    forall P Q : P256_Ppoint, P256_not_exceptional P Q).

  (** The RcbProjectiveLaws-level names at the P-256 constants.  These
      are what [P256_wNAF_Instance.p256_oncurve] / [p256_pt_eq] /
      [p256_scmul] unfold to; §2 is stated with them so that it does not
      depend on how Section discharge presents that file's wrappers. *)
  Local Notation Onc :=
    (RcbProjectiveLaws.oncurve p256_a_val p256_b_val).
  Local Notation Scm :=
    (BLS12_GLV_LoopInvariant.scmul Fzero Fone p256_curve_add).

  (* ================================================================ *)
  (** ** 2. The table and its correctness                              *)
  (* ================================================================ *)

  (** [1P; 3P; 5P; 7P], by three additions after one doubling.  Written
      with the parameter-free builder [WnafTableBuild.build_odd_table_gen]
      at the closed constant [P256_wNAF_Instance.p256_curve_add]; it is
      [WnafTableBuild.rcb_build_table4] at the P-256 constants (see
      [p256_table4_is_rcb_build_table4]). *)
  Definition p256_table4 (P : F * F * F) : list (F * F * F) :=
    build_odd_table_gen p256_curve_add 4%nat P.

  (** [Hexcept], [Hdisc], [Hthree_b] and [M_gt_27] are the proof
      arguments a discharged WnafTableBuild / RcbProjectiveLaws theorem
      takes besides [a], [b] and [three_b]. *)
  Local Ltac rcb_ctx :=
    first [ eassumption
          | exact p256_M_gt_27 | exact p256_Hthree_b
          | exact p256_Hdisc   | exact p256_Hexcept ].

  (** [rcb_table4_ok] at the P-256 constants.

      The [with (a := ...) (b := ...) (three_b := ...)] alternation is
      the §3a pattern of WnafTableBuild.v: a theorem of that file is
      generalised over every Section variable its PROOF TERM mentions,
      not only those in its statement, because [ring] / [fsatz] emit
      [abstract]ed subproofs generalised over the whole ambient context.
      A binding name absent from the discharged form makes its branch
      fail and the next one run. *)
  Theorem p256_rcb_table4_ok :
    forall P : F * F * F,
      Onc P ->
      length (p256_table4 P) = 4%nat
      /\ forall i, (i < 4)%nat ->
           Onc (nth i (p256_table4 P) RcbProjectiveLaws.id_pt)
           /\ RcbProjectiveLaws.pt_eq
                (nth i (p256_table4 P) RcbProjectiveLaws.id_pt)
                (Scm (2 * i + 1)%nat P).
  Proof.
    intros P HP.
    unfold p256_table4, p256_curve_add.
    first
      [ eapply rcb_table4_ok
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply rcb_table4_ok
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply rcb_table4_ok with (three_b := p256_three_b_val); rcb_ctx
      | eapply rcb_table4_ok with (b := p256_b_val); rcb_ctx
      | eapply rcb_table4_ok; rcb_ctx ].
  Qed.

  Corollary p256_table4_length : forall P, length (p256_table4 P) = 4%nat.
  Proof.
    intros P. unfold p256_table4. apply build_odd_table_gen_length.
  Qed.

  Corollary p256_table4_oncurve :
    forall P, Onc P -> Forall Onc (p256_table4 P).
  Proof.
    intros P HP.
    unfold p256_table4, p256_curve_add.
    first
      [ eapply rcb_build_table4_oncurve
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply rcb_build_table4_oncurve
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply rcb_build_table4_oncurve
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply rcb_build_table4_oncurve with (b := p256_b_val); rcb_ctx
      | eapply rcb_build_table4_oncurve; rcb_ctx ].
  Qed.

  (* ================================================================ *)
  (** ** 3. The bridge to [P256_wNAF_Instance.p256_table_ok]           *)
  (* ================================================================ *)

  (** The G7 table hypothesis of [p256_wnaf_single_full], discharged.
      A caller that passes [table_entries := p256_table4 (Px,Py,Pz)]
      needs only [oncurve (Px,Py,Pz)].

      [p256_table_ok] is a Section definition of [P256_wNAF_Instance]
      whose body mentions [p256_oncurve], hence the Section variable
      [p256_b_val]; after discharge it takes that variable first.  The
      two statements differ only by delta ([p256_oncurve],
      [p256_pt_eq], [p256_scmul], [RcbProjectiveLaws.id_pt] are all
      transparent), so [exact] closes it. *)
  Theorem p256_table_ok_of_oncurve :
    forall Px Py Pz : F,
      RcbProjectiveLaws.oncurve p256_a_val p256_b_val (Px, Py, Pz) ->
      p256_table_ok Px Py Pz (p256_table4 (Px, Py, Pz)).
  Proof.
    intros Px Py Pz HP.
    first
      [ exact (p256_rcb_table4_ok (Px, Py, Pz) HP)
      | (unfold p256_table_ok, p256_oncurve, p256_pt_eq, p256_scmul;
         exact (p256_rcb_table4_ok (Px, Py, Pz) HP))
      | (unfold p256_table_ok, p256_oncurve, p256_pt_eq, p256_scmul;
         apply (p256_rcb_table4_ok (Px, Py, Pz) HP))
      | apply (p256_rcb_table4_ok (Px, Py, Pz) HP) ].
  Qed.

  (** The same table, named as WnafTableBuild names it. *)
  Lemma p256_table4_is_rcb_build_table4 :
    forall P : F * F * F,
      p256_table4 P = rcb_build_table4 p256_a_val p256_three_b_val P.
  Proof. intros P. reflexivity. Qed.

  (* ================================================================ *)
  (** ** 4. Totality of [Projective.add] at P-256                      *)
  (* ================================================================ *)

  (** [p256_Hexcept] above (and the identical Section hypothesis of
      [P256_wNAF_Instance]) follows from the single arithmetic fact that
      x^3 + a x + b has no root in F — equivalently, that the curve has
      no F-rational point of order two.  This is
      [RcbProjectiveLaws.not_exceptional_of_no_two_torsion] (Qed) at the
      P-256 constants; it is stated here so that a consumer can see
      exactly which number-theoretic fact about the concrete modulus is
      still open.  Nothing in §2/§3 uses it. *)
  Lemma p256_Hexcept_of_no_two_torsion :
    RcbProjectiveLaws.no_two_torsion p256_a_val p256_b_val ->
    forall P Q : P256_Ppoint, P256_not_exceptional P Q.
  Proof.
    intros Hno P Q.
    first
      [ eapply RcbProjectiveLaws.not_exceptional_of_no_two_torsion
          with (a := p256_a_val) (b := p256_b_val)
               (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.not_exceptional_of_no_two_torsion
          with (b := p256_b_val) (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.not_exceptional_of_no_two_torsion
          with (three_b := p256_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.not_exceptional_of_no_two_torsion
          with (b := p256_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.not_exceptional_of_no_two_torsion;
        rcb_ctx ].
  Qed.

End P256_wNAF_Table.

(* ==================================================================== *)
(** ** 5. What this discharges, and what remains                         *)
(* ==================================================================== *)

(** *** Discharged

    [P256_wNAF_Instance.p256_wnaf_single_full] takes, among its G7
    caller obligations,

      p256_table_ok Px Py Pz table_entries

    i.e. [length table_entries = 4] together with, for each i < 4, that
    the entry is on the curve and [p256_pt_eq] to
    [p256_scmul (2*i+1) (Px,Py,Pz)].  [p256_table_ok_of_oncurve] above
    supplies that for [table_entries := p256_table4 (Px,Py,Pz)] from
    [oncurve (Px,Py,Pz)] alone.  Composed with §4, the whole G6/G7
    algebraic surface of the P-256 chain rests on: the curve constant
    [b] with 3b = [p256_three_b_val], the characteristic bound
    27 < M, non-vanishing of the discriminant, and
    [no_two_torsion] — no [Admitted], no [Axiom].

    *** NOT discharged: the memory-level obligation

    As in WnafTableBuild.v §4, this file is pure Gallina.  It does not
    claim that any bedrock2 function POPULATES the caller's table
    buffer, i.e. establishes [Table4 pT (p256_table4 P)] from an
    uninitialised buffer.  That is a separate weakest-precondition proof
    over a [precompute_w4] function that does not yet exist; the three
    [curve_add] calls and one [curve_double] call it needs already have
    specs ([P256_wNAF_Instance.p256_HCurveAddInplace],
    [p256_HCurveDouble]), so the missing part is the separation-logic
    frame, not the arithmetic.

    Nor does it claim [no_two_torsion] for the P-256 modulus.  That is
    the statement that
      x^3 - 3x + b  has no root modulo p256,
    which follows from #E(F_p) being prime (a curve of prime order has
    no point of order two) — a Pocklington-style certificate over the
    P-256 group order, not a fact about the addition law. *)
