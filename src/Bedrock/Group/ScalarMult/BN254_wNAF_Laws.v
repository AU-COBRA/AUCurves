(** * BN254 (and every a = 0 curve): the concrete RCB addition, its
      group laws, its wNAF table, and an unconditional
      [bn254_wnaf_single_full].

    ** What this file removes **

    [Bedrock.Field.Synthesis.Examples.BN254_wNAF_Instance] keeps its
    addition ABSTRACT:

      Context {curve_add : F * F * F -> F * F * F -> F * F * F}.
      Context (pt_eq ...) (pt_eq_equiv ...) (oncurve ...)
              (oncurve_id ...) (oncurve_curve_add ...)
              (curve_add_Proper ...) (curve_add_id_l ...)
              (curve_add_assoc ...)
              (Hhorner_step ...) (Hhorner_oncurve ...)

    so its [wnaf_single_full] is conditional on group laws that no file
    proves for BN254.  That Section stays parametric — BN256 and BN446
    share it — and this file adds the concrete layer alongside, exactly
    as [P256_wNAF_Instance.v] §1b does for P-256.

    ** The concrete addition **

    BN254's bedrock2 "curve_add" is [CurveAdd.ladderstep_body]
    ([BN254_G1.bn254_G1_add], and the in-place wrapper
    [BN254_CurveOps.bn254_curve_add_inplace]), whose Gallina model is
    [CurveAdd.ladderstep_gallina] — Algorithm 7 of Renes-Costello-Batina
    2015, the a = 0 specialisation, with the interleaved argument order
    [X1 X2 Y1 Y2 Z1 Z2].  §1 packages it as a function on triples,
    [bn254_curve_add], and proves

      bn254_curve_add three_b P Q = RcbProjectiveLaws.cadd 0 three_b P Q

    by [ring] on each coordinate.  The two chains are the same forty
    [let]s with the three [a]-terms (S19, S27, S31) dropped, so the
    coordinate polynomials agree identically; fiat-crypto's
    [Curves/Weierstrass/Projective.v] carries [a] as a section variable
    throughout and assumes nothing about it, which is why the general-a
    laws of [RcbProjectiveLaws.v] instantiate at a := 0 with no
    transport beyond that one equation.

    ** What is discharged, and by what **

      Equivalence pt_eq        pt_eq_refl / _sym / _trans   (RcbProjectiveLaws §1)
      oncurve_id               oncurve_id                   (§3)
      oncurve_curve_add        oncurve_cadd                 (§3)
      oncurve_point_opp        oncurve_opp                  (§3)
      curve_add_Proper         cadd_Proper                  (§4a)
      point_opp_Proper         point_opp_Proper             (§4a')
      curve_add_comm           cadd_comm                    (§4b)
      curve_add_assoc          cadd_assoc                   (§4c)
      curve_add_id_r / _l      cadd_id_r / cadd_id_l        (§4d)
      point_opp_inverse        point_opp_inverse            (§4e)
      Hhorner_step             horner_step_single           (wNAF_Single_HornerAlgebra)
      Hhorner_oncurve          digit_point_oncurve_full     (idem)
      the table hypothesis     build_odd_table_gen_correct  (WnafTableBuild §2)

    ** What is NOT discharged (parity with P-256 / P-384 / P-224) **

    The same five curve-level side conditions those three files carry,
    here specialised to a = 0:

      [bn254_b_val]      the curve constant b (the chain only sees 3b);
      [bn254_M_gt_27]    27 < M, for the three [Ring.char_ge] instances;
      [bn254_Hthree_b]   three_b = b + b + b;
      [bn254_Hdisc]      4a^3 + 27b^2 <> 0, i.e. 27b^2 <> 0 at a = 0,
                         in the expanded form Projective.v expects;
      [bn254_Hexcept]    totality of [Projective.add], equivalently:
                         the curve has no F-rational point of order two.

    For BN254 proper (b = 3, 3b = 9, [bn254_three_b.v]) the first four
    are routine computations over the concrete 254-bit modulus and the
    last is the genuine number-theoretic obligation; none is discharged
    here, and none is discharged in the three NIST files either.  The
    field parameters are left abstract for the same reason
    [BN254_wNAF_Instance.v] leaves them abstract: BN256 and BN446 are
    also a = 0 curves and reuse this file verbatim at their own
    [FieldParameters].

    Honesty ledger: no [Admitted], no [Axiom].  The callee specs
    ([HCurveDouble], [HCurveAddInplace], [HFelemCopy], [HOpp],
    [HOppInplace], [HStoreZero]) remain Section hypotheses, as in
    [BN254_wNAF_Instance.v]; wiring them to a BN254 function table is
    the [NistWnafWrappers.v] analogue that the BN side does not yet
    have ([BN254_wNAF_Extract.v] still aliases ladderstep directly for
    the in-place call). *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import RelationClasses.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoadAndProcess.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoopBody.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_Proof.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_HornerAlgebra.
Require Import Bedrock.Field.Synthesis.Examples.BN254_wNAF_Instance.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Import Bedrock.Group.CurveAdd.CurveAdd.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.ScalarMult.WnafTableBuild.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(* ==================================================================== *)
(** ** 1. BN254's concrete addition on triples, and its bridge to [cadd] *)
(* ==================================================================== *)

(** This section takes ONLY [field_parameters], so that
    [bn254_curve_add] discharges with exactly one implicit argument
    besides its explicit [three_b] — the same shape
    [RcbProjectiveLaws.cadd] has. *)

Section BN254Add.
  Context {field_parameters : FieldParameters}.

  Local Notation F := (F M_pos).

  Add Ring Fp_ring_bn254_add : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  (** [CurveAdd.ladderstep_gallina] returns a Rupicola tuple
      [\<X, Y, Z\>] and takes its six coordinates INTERLEAVED
      ([X1 X2 Y1 Y2 Z1 Z2]); the wNAF chain works with two [F * F * F]
      triples.  This is the only place the permutation happens. *)
  Definition bn254_curve_add (three_b_val : F) (P Q : F * F * F)
    : F * F * F :=
    let '(X1, Y1, Z1) := P in
    let '(X2, Y2, Z2) := Q in
    let '\<x, y, z\> :=
      @ladderstep_gallina _ three_b_val X1 X2 Y1 Y2 Z1 Z2 in
    (x, y, z).

  (** The a = 0 chain IS the general-a chain at a = 0.

      Step by step: the general chain's S19 ([outz := a*t4]), S27
      ([t2 := a*t2]) and S31 ([t2 := a*(t0 - a*t2)]) contribute zero,
      S21/S29/S32 then add zero, and S30 is the identity; every other
      step is literally the same operation on the same buffer.  After
      [cbv] both sides are polynomials in [X1 Y1 Z1 X2 Y2 Z2 three_b]
      and [ring] closes each coordinate.

      [Timeout] so that a regression reports a position instead of
      hanging: the three [ring] calls are on degree-4 polynomials in
      seven variables, which is the size [RcbProjectiveLaws.cadd_is_Padd]
      already discharges. *)
  Theorem bn254_curve_add_is_cadd (three_b_val : F) (P Q : F * F * F) :
    bn254_curve_add three_b_val P Q
    = RcbProjectiveLaws.cadd (@F.zero M_pos) three_b_val P Q.
  Proof.
    destruct P as [[X1 Y1] Z1], Q as [[X2 Y2] Z2].
    cbv [bn254_curve_add RcbProjectiveLaws.cadd
         ladderstep_gallina rcb_add_general_gallina
         nlet stack P2.car P2.cdr].
    apply pair_equal_spec; split;
      [ apply pair_equal_spec; split | ]; timeout 120 ring.
  Qed.

End BN254Add.

(* ==================================================================== *)
(** ** 2. The group laws, the table, and [bn254_wnaf_single_full]        *)
(* ==================================================================== *)

Section BN254_wNAF_Laws.

  (* ---------------------------------------------------------------- *)
  (** *** 2.0 Context: bedrock2, the field, and the curve              *)
  (* ---------------------------------------------------------------- *)

  (** The bedrock2 context of [BN254_wNAF_Instance.v], verbatim.  The
      algebraic lemmas below do not mention any of it, so Section
      discharge drops these variables from them. *)
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {mem: map.map word Byte.byte}.
  Context {locals: map.map string word}.
  Context {env: map.map string (list string * list string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals} {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.
  Context {field_parameters : FieldParameters}
          {field_representation : FieldRepresentation}.
  Context {field_parameters_ok : FieldParameters_ok}
          {field_representation_ok : FieldRepresentation_ok}.
  Context (Hbounds_eq : loose_bounds = tight_bounds).

  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  (** No local [prime] instance is declared here: [RcbProjectiveLaws]
      exports [prime_M_pos], and a second, opaque proof of the same Prop
      would make [F.field_modulo]'s instance argument differ from the one
      baked into that file's theorems — [Znumtheory.prime] is an ordinary
      Prop, so the two would not be convertible.  The ring below needs no
      primality; it exists only for the [ring] fallback of
      [bn254_oncurve_id]. *)
  Add Ring Fp_ring_bn254_laws : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  (** The five curve-level side conditions of [RcbProjectiveLaws],
      specialised to a = 0.  See the header for what each is and why it
      is not discharged here. *)
  Context (bn254_b_val bn254_three_b_val : F).
  Context (bn254_M_gt_27 : (27 < M_pos)%positive).
  Context (bn254_Hthree_b :
    bn254_three_b_val = (bn254_b_val + bn254_b_val + bn254_b_val)%F).
  Context (bn254_Hdisc : id
    ((((1 + 1 + 1 + 1) * Fzero * Fzero * Fzero
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * bn254_b_val * bn254_b_val)
      <> 0)%F)).

  Local Instance bn254_char_ge_3 :
    @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul 3%positive :=
    RcbProjectiveLaws.char_ge_3 bn254_M_gt_27.

  Local Notation BN254_Ppoint :=
    (@Projective.point F eq F.zero F.add F.mul Fzero bn254_b_val).

  Local Notation BN254_not_exceptional :=
    (@Projective.not_exceptional F eq F.zero F.one F.opp F.add F.sub
       F.mul F.inv F.div Fzero bn254_b_val _ bn254_char_ge_3 _).

  Context (bn254_Hexcept :
    forall P Q : BN254_Ppoint, BN254_not_exceptional P Q).

  (* ---------------------------------------------------------------- *)
  (** *** 2.1 The Gallina model                                        *)
  (* ---------------------------------------------------------------- *)

  (** The chain's [curve_add] at BN254: the a = 0 RCB chain that
      [CurveAdd.ladderstep_body] — BN254's bedrock2 "curve_add" — is
      derived from. *)
  Definition bn254_add : F * F * F -> F * F * F -> F * F * F :=
    bn254_curve_add bn254_three_b_val.

  Definition bn254_point_opp : F * F * F -> F * F * F :=
    RcbProjectiveLaws.point_opp_triple.

  Definition bn254_pt_eq : F * F * F -> F * F * F -> Prop :=
    RcbProjectiveLaws.pt_eq.

  Definition bn254_oncurve : F * F * F -> Prop :=
    RcbProjectiveLaws.oncurve Fzero bn254_b_val.

  (** [scmul] of BLS12_GLV_LoopInvariant.v, the chain's [scmul_s].
      Qualified: WNAFTable.v also exports a [scmul] whose [Fzero]/[Fone]
      are implicit, so the short name can resolve to the wrong one. *)
  Definition bn254_scmul : nat -> F * F * F -> F * F * F :=
    BLS12_GLV_LoopInvariant.scmul Fzero Fone bn254_add.

  Lemma bn254_add_eq : forall P Q,
    bn254_add P Q = RcbProjectiveLaws.cadd Fzero bn254_three_b_val P Q.
  Proof. intros P Q. apply bn254_curve_add_is_cadd. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 2.2 The group laws, from RcbProjectiveLaws at a := 0         *)
  (* ---------------------------------------------------------------- *)

  (** [rcb] first REWRITES the concrete addition into [cadd] (so the
      imported laws apply on the nose) and only then unfolds the
      wrappers.  Doing it the other way round would delete the redex the
      rewrite needs. *)
  Local Ltac rcb :=
    rewrite ?bn254_add_eq;
    unfold bn254_pt_eq, bn254_oncurve, bn254_add, bn254_point_opp in *.

  (** The curve constants [b] and [three_b] must be pinned by hand at
      every discharge below.  A [RcbProjectiveLaws] theorem is
      generalised over every Section variable its PROOF TERM mentions,
      not only those in its statement, and [ring] / [fsatz] emit
      [abstract]ed subproof constants that Coq generalises over the WHOLE
      ambient section context.  So e.g. [pt_eq_Equivalence], whose
      statement mentions neither [b] nor [three_b], still takes both —
      and [apply] / [eapply] cannot invent them ("Unable to find an
      instance for the variables b, three_b").

      The alternation tries the pinnings from most to least specific; a
      binding name absent from a given lemma makes that branch fail and
      the next one run.  The alternations are written out per lemma
      rather than factored into a tactic taking the lemma as an
      argument, because a [with (x := t)] binding name must be resolved
      against a concrete constant.  This is the §1b pattern of
      P256_wNAF_Instance.v and the §3a pattern of WnafTableBuild.v, both
      of which compile against the same file. *)
  Local Ltac rcb_ctx :=
    first [ eassumption
          | exact bn254_M_gt_27 | exact bn254_Hthree_b
          | exact bn254_Hdisc   | exact bn254_Hexcept ].

  Lemma bn254_pt_eq_refl : forall p, bn254_pt_eq p p.
  Proof.
    intros p. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_refl
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl; rcb_ctx ].
  Qed.

  Lemma bn254_pt_eq_sym : forall p q, bn254_pt_eq p q -> bn254_pt_eq q p.
  Proof.
    intros p q H. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_sym
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym; rcb_ctx ].
  Qed.

  Lemma bn254_pt_eq_trans : forall p q r,
    bn254_pt_eq p q -> bn254_pt_eq q r -> bn254_pt_eq p r.
  Proof.
    intros p q r H1 H2. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_trans
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans; rcb_ctx ].
  Qed.

  (** Assembled from the three individually-pinned laws rather than from
      the bundled [pt_eq_Equivalence] instance, whose discharged argument
      list is the least predictable of the four. *)
  Lemma bn254_pt_eq_equiv : Equivalence bn254_pt_eq.
  Proof.
    constructor;
      [ exact bn254_pt_eq_refl
      | exact bn254_pt_eq_sym
      | exact bn254_pt_eq_trans ].
  Qed.

  Lemma bn254_oncurve_id : bn254_oncurve (Fzero, Fone, Fzero).
  Proof.
    rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_id
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id; rcb_ctx
      | (* Independent of the discharge shape: [oncurve] and [id_pt] are
           plain definitions, so unfold and compute.  This is the script
           of [RcbProjectiveLaws.oncurve_id] itself. *)
        cbv [RcbProjectiveLaws.oncurve RcbProjectiveLaws.id_pt];
        split; [ ring | intros _; fsatz ] ].
  Qed.

  Lemma bn254_oncurve_curve_add : forall P Q,
    bn254_oncurve P -> bn254_oncurve Q -> bn254_oncurve (bn254_add P Q).
  Proof.
    intros P Q HP HQ. rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_cadd
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd; rcb_ctx ].
  Qed.

  Lemma bn254_oncurve_point_opp : forall P,
    bn254_oncurve P -> bn254_oncurve (bn254_point_opp P).
  Proof.
    intros P HP. rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_opp
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp; rcb_ctx ].
  Qed.

  Lemma bn254_curve_add_Proper : forall P P' Q Q',
    bn254_oncurve P -> bn254_oncurve P' ->
    bn254_oncurve Q -> bn254_oncurve Q' ->
    bn254_pt_eq P P' -> bn254_pt_eq Q Q' ->
    bn254_pt_eq (bn254_add P Q) (bn254_add P' Q').
  Proof.
    intros P P' Q Q' Hp Hp' Hq Hq' E1 E2. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_Proper
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper; rcb_ctx ].
  Qed.

  Lemma bn254_point_opp_Proper : forall P P',
    bn254_oncurve P -> bn254_oncurve P' -> bn254_pt_eq P P' ->
    bn254_pt_eq (bn254_point_opp P) (bn254_point_opp P').
  Proof.
    intros P P' Hp Hp' E. rcb.
    first
      [ eapply RcbProjectiveLaws.point_opp_Proper
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper with (b := bn254_b_val);
        rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper; rcb_ctx ].
  Qed.

  (** The identity laws in POINT form: this is the shape
      [WnafTableBuild]'s abstract telescope asks for, and the
      coordinate form the wNAF chain asks for follows by application. *)
  Lemma bn254_add_id_r_pt : forall p,
    bn254_oncurve p -> bn254_pt_eq (bn254_add p (Fzero, Fone, Fzero)) p.
  Proof.
    intros p Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_id_r
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r; rcb_ctx ].
  Qed.

  Lemma bn254_add_id_l_pt : forall p,
    bn254_oncurve p -> bn254_pt_eq (bn254_add (Fzero, Fone, Fzero) p) p.
  Proof.
    intros p Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_id_l
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l; rcb_ctx ].
  Qed.

  Lemma bn254_curve_add_id_r : forall x y z,
    bn254_oncurve (x, y, z) ->
    bn254_pt_eq (bn254_add (x, y, z) (Fzero, Fone, Fzero)) (x, y, z).
  Proof. intros x y z H. exact (bn254_add_id_r_pt (x, y, z) H). Qed.

  Lemma bn254_curve_add_id_l : forall x y z,
    bn254_oncurve (x, y, z) ->
    bn254_pt_eq (bn254_add (Fzero, Fone, Fzero) (x, y, z)) (x, y, z).
  Proof. intros x y z H. exact (bn254_add_id_l_pt (x, y, z) H). Qed.

  Lemma bn254_curve_add_assoc : forall P Q R,
    bn254_oncurve P -> bn254_oncurve Q -> bn254_oncurve R ->
    bn254_pt_eq (bn254_add P (bn254_add Q R))
                (bn254_add (bn254_add P Q) R).
  Proof.
    intros P Q R Hp Hq Hr. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_assoc
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc; rcb_ctx ].
  Qed.

  Lemma bn254_curve_add_comm : forall P Q,
    bn254_oncurve P -> bn254_oncurve Q ->
    bn254_pt_eq (bn254_add P Q) (bn254_add Q P).
  Proof.
    intros P Q Hp Hq. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_comm
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm with (b := bn254_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm; rcb_ctx ].
  Qed.

  Lemma bn254_point_opp_inverse : forall P,
    bn254_oncurve P ->
    bn254_pt_eq (bn254_add P (bn254_point_opp P)) (Fzero, Fone, Fzero).
  Proof.
    intros P Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.point_opp_inverse
          with (a := Fzero) (b := bn254_b_val)
               (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse
          with (b := bn254_b_val) (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse
          with (three_b := bn254_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse with (b := bn254_b_val);
        rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse; rcb_ctx ].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 2.3 The precomputed table                                     *)
  (* ---------------------------------------------------------------- *)

  (** [WnafTableBuild]'s abstract telescope orders the congruence's
      arguments equations-first; the wNAF chain orders them
      on-curve-first.  One shuffle, once. *)
  Lemma bn254_add_Proper_tbl : forall p p' q q',
    bn254_pt_eq p p' -> bn254_pt_eq q q' ->
    bn254_oncurve p -> bn254_oncurve p' ->
    bn254_oncurve q -> bn254_oncurve q' ->
    bn254_pt_eq (bn254_add p q) (bn254_add p' q').
  Proof.
    intros p p' q q' E1 E2 Hp Hp' Hq Hq'.
    apply bn254_curve_add_Proper; assumption.
  Qed.

  (** [build_odd_table_gen] and its two correctness theorems are
      TOP-LEVEL and parameter-free in [WnafTableBuild] §1/§2 (the
      abstract section has no [FieldParameters]), so the positional
      application below is exact — no [first] ladder is needed, and no
      Section variable of [RcbProjectiveLaws] enters. *)
  Definition bn254_table4 (P : F * F * F) : list (F * F * F) :=
    build_odd_table_gen bn254_add 4%nat P.

  Lemma bn254_table4_length : forall P, length (bn254_table4 P) = 4%nat.
  Proof. intros P. apply build_odd_table_gen_length. Qed.

  (** The chain's table hypothesis, discharged: three additions build
      [1P; 3P; 5P; 7P] from [P] alone. *)
  Theorem bn254_table4_ok : forall P : F * F * F,
    bn254_oncurve P ->
    length (bn254_table4 P) = 4%nat
    /\ forall i, (i < 4)%nat ->
         bn254_oncurve (nth i (bn254_table4 P) (Fzero, Fone, Fzero))
         /\ bn254_pt_eq (nth i (bn254_table4 P) (Fzero, Fone, Fzero))
                        (bn254_scmul (2 * i + 1)%nat P).
  Proof.
    intros P HP. split; [ apply bn254_table4_length | ].
    intros i Hi. unfold bn254_table4, bn254_scmul.
    exact (build_odd_table_gen_correct
             Fzero Fone bn254_add bn254_pt_eq bn254_oncurve
             bn254_pt_eq_refl bn254_pt_eq_sym bn254_pt_eq_trans
             bn254_oncurve_id bn254_oncurve_curve_add
             bn254_add_Proper_tbl
             bn254_curve_add_comm bn254_curve_add_assoc
             bn254_add_id_r_pt bn254_add_id_l_pt
             4%nat P i (Fzero, Fone, Fzero) HP Hi).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 2.4 The two Horner hypotheses                                 *)
  (* ---------------------------------------------------------------- *)

  (** [wNAF_Single_HornerAlgebra]'s [digit_point_local] is
      [BLS12_wNAF_ProcessDigits.digit_point] by conversion (same
      fixpoint, and [bn254_point_opp] is ProcessDigits' [point_opp]), so
      the instantiated statements below are the chain's hypotheses up to
      delta.  The argument order is the Section declaration order of
      [SingleHornerAlgebra]. *)

  Lemma bn254_digit_point_oncurve :
    forall (tab : list (F * F * F)) (d : Z),
      length tab = 4%nat ->
      (forall i, (i < 4)%nat ->
         bn254_oncurve (nth i tab (Fzero, Fone, Fzero))) ->
      (Z.odd d = true \/ d = 0) ->
      -7 <= d <= 7 ->
      bn254_oncurve (digit_point d tab).
  Proof.
    intros tab d Hlen4 Hentries Hodd Hb.
    pose proof (digit_point_oncurve_full
                  Fzero Fone bn254_add bn254_point_opp
                  bn254_pt_eq bn254_pt_eq_equiv bn254_oncurve
                  bn254_oncurve_id bn254_oncurve_curve_add
                  bn254_oncurve_point_opp
                  bn254_curve_add_Proper bn254_point_opp_Proper
                  bn254_curve_add_id_r bn254_curve_add_id_l
                  bn254_curve_add_assoc bn254_curve_add_comm
                  bn254_point_opp_inverse
                  tab d Hlen4 Hentries Hodd Hb) as Hdp.
    first [ exact Hdp | apply Hdp ].
  Qed.

  Theorem bn254_horner_step :
    forall (dk : list Z) (Px Py Pz : F) (tab : list (F * F * F)),
      bn254_oncurve (Px, Py, Pz) ->
      length tab = 4%nat ->
      (forall i, (i < 4)%nat ->
         bn254_oncurve (nth i tab (Fzero, Fone, Fzero))
         /\ bn254_pt_eq (nth i tab (Fzero, Fone, Fzero))
                        (bn254_scmul (2 * i + 1)%nat (Px, Py, Pz))) ->
      (forall i, (i < length dk)%nat ->
         Z.odd (nth i dk 0) = true \/ nth i dk 0 = 0) ->
      (forall i, (i < length dk)%nat -> -7 <= nth i dk 0 <= 7) ->
      (forall n, (n <= length dk)%nat ->
         0 <= weighted_sum (skipn n dk) 0) ->
      forall n (Ox Oy Oz : F),
        (n < length dk)%nat ->
        let ws_old := weighted_sum (skipn (S n) dk) 0 in
        bn254_oncurve (Ox, Oy, Oz) ->
        bn254_pt_eq (Ox, Oy, Oz)
                    (bn254_scmul (Z.to_nat (2 * ws_old)) (Px, Py, Pz)) ->
        let d := nth n dk 0 in
        bn254_pt_eq
          (if d =? 0 then (Ox, Oy, Oz)
           else bn254_add (Ox, Oy, Oz) (digit_point d tab))
          (bn254_scmul (Z.to_nat (weighted_sum (skipn n dk) 0))
                       (Px, Py, Pz)).
  Proof.
    intros dk Px Py Pz tab HPoc Hlen4 Hcorr Hodd Hb Hws
           n Ox Oy Oz Hn ws_old Hoc Hacc.
    pose proof (horner_step_single
                  Fzero Fone bn254_add bn254_point_opp
                  bn254_pt_eq bn254_pt_eq_equiv bn254_oncurve
                  bn254_oncurve_id bn254_oncurve_curve_add
                  bn254_oncurve_point_opp
                  bn254_curve_add_Proper bn254_point_opp_Proper
                  bn254_curve_add_id_r bn254_curve_add_id_l
                  bn254_curve_add_assoc bn254_curve_add_comm
                  bn254_point_opp_inverse
                  dk Px Py Pz tab
                  HPoc Hlen4 Hcorr Hodd Hb Hws
                  n Ox Oy Oz Hn Hoc Hacc) as Hstep.
    first [ exact Hstep | apply Hstep ].
  Qed.

  Theorem bn254_horner_oncurve :
    forall (dk : list Z) (tab : list (F * F * F)),
      length tab = 4%nat ->
      (forall i, (i < 4)%nat ->
         bn254_oncurve (nth i tab (Fzero, Fone, Fzero))) ->
      (forall i, (i < length dk)%nat ->
         Z.odd (nth i dk 0) = true \/ nth i dk 0 = 0) ->
      (forall i, (i < length dk)%nat -> -7 <= nth i dk 0 <= 7) ->
      forall n (Ox Oy Oz : F),
        (n < length dk)%nat ->
        bn254_oncurve (Ox, Oy, Oz) ->
        let d := nth n dk 0 in
        bn254_oncurve
          (if d =? 0 then (Ox, Oy, Oz)
           else bn254_add (Ox, Oy, Oz) (digit_point d tab)).
  Proof.
    intros dk tab Hlen4 Hentries Hodd Hb n Ox Oy Oz Hn Hoc.
    (* Reduce the [let d := ...] rather than introducing it, so that the
       [apply]s below see [nth n dk 0] literally instead of a local
       definition that only conversion relates to it. *)
    cbv zeta.
    assert (Hdoc : bn254_oncurve (digit_point (nth n dk 0) tab))
      by (apply bn254_digit_point_oncurve;
          [ exact Hlen4 | exact Hentries | apply Hodd; exact Hn
          | apply Hb; exact Hn ]).
    destruct (nth n dk 0 =? 0);
      [ exact Hoc | apply bn254_oncurve_curve_add; assumption ].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 2.5 The bedrock2 callee specs and the wNAF data              *)
  (* ---------------------------------------------------------------- *)

  (** Copied verbatim from [BN254_wNAF_Instance.v] with its abstract
      [curve_add] replaced by [bn254_add].  These are the hypotheses this
      file does NOT discharge: wiring them to a BN254 function table is
      the [NistWnafWrappers.v] analogue the BN side still lacks. *)

  Context (curve_add_name curve_double_name opp_name : string).

  Variable functions : map.rep (map := Semantics.env).

  Context (HCurveDouble : forall pX pY pZ
    (X Y Z : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pX X ⋆ FElem (Some tight_bounds) pY Y
     ⋆ FElem (Some tight_bounds) pZ Z ⋆ R0) m0 ->
    Semantics.call functions curve_double_name tr0 m0
      [pX; pY; pZ; pX; pY; pZ]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        let '(Xo, Yo, Zo) := bn254_add (X, Y, Z) (X, Y, Z) in
        (FElem (Some tight_bounds) pX Xo ⋆ FElem (Some tight_bounds) pY Yo
         ⋆ FElem (Some tight_bounds) pZ Zo ⋆ R0) m')).

  Context (HCurveAddInplace :
    forall pXo pX2 pYo pY2 pZo pZ2
      (X Y Z X2' Y2' Z2' : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pXo X ⋆ FElem (Some tight_bounds) pYo Y
     ⋆ FElem (Some tight_bounds) pZo Z ⋆ FElem (Some tight_bounds) pX2 X2'
     ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
     ⋆ R0) m0 ->
    WeakestPrecondition.call functions curve_add_name tr0 m0
      [pXo; pX2; pYo; pY2; pZo; pZ2; pXo; pYo; pZo]
      (fun tr' m' rets => rets = [] /\ (tr0 = tr' /\
        let '(Xo', Yo', Zo') := bn254_add (X, Y, Z) (X2', Y2', Z2') in
        (FElem (Some tight_bounds) pXo Xo' ⋆ FElem (Some tight_bounds) pYo Yo'
         ⋆ FElem (Some tight_bounds) pZo Zo' ⋆ FElem (Some tight_bounds) pX2 X2'
         ⋆ FElem (Some tight_bounds) pY2 Y2' ⋆ FElem (Some tight_bounds) pZ2 Z2'
         ⋆ R0) m'))).

  Context (HFelemCopy :
    forall pDst pSrc (v : F) (old : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pSrc v
     ⋆ FElem (Some tight_bounds) pDst old ⋆ R0) m0 ->
    Semantics.call functions felem_copy tr0 m0 [pDst; pSrc]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pSrc v
         ⋆ FElem (Some tight_bounds) pDst v ⋆ R0) m')).

  Context (HOpp :
    forall pOut pIn (Y : F) (Yold : F) R0 tr0 m0,
    (FElem (Some tight_bounds) pIn Y
     ⋆ FElem (Some tight_bounds) pOut Yold ⋆ R0) m0 ->
    Semantics.call functions opp_name tr0 m0 [pOut; pIn]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) pIn Y
         ⋆ FElem (Some tight_bounds) pOut (F.opp Y) ⋆ R0) m')).

  Context (HOppInplace :
    forall p (Y : F) R0 tr0 m0,
    (FElem (Some tight_bounds) p Y ⋆ R0) m0 ->
    Semantics.call functions opp_name tr0 m0 [p; p]
      (fun tr' m' rets => rets = [] /\ tr0 = tr' /\
        (FElem (Some tight_bounds) p (F.opp Y) ⋆ R0) m')).

  Context (HStoreZero : @StoreZero.spec_of_store_zero
    _ _ _ _ _ _ field_parameters field_representation functions).

  (** The caller's data (plan item G7).  [num_iters] is [length dk]
      throughout, so [BN254_wNAF_Instance]'s [Hlen] is [eq_refl] and no
      index conversion is needed anywhere below. *)
  Context (dk : list Z) (Px Py Pz : F).
  Context (Honcurve_P : bn254_oncurve (Px, Py, Pz)).
  Context (Hnbound : Z.of_nat (length dk) < 2 ^ width).
  Context (Hdigits_bounded :
    forall i, (i < length dk)%nat -> -7 <= nth i dk 0 <= 7).
  Context (Hdigits_odd :
    forall i, (i < length dk)%nat ->
      Z.odd (nth i dk 0) = true \/ nth i dk 0 = 0).
  Context (Hfs_pos : 0 < felem_size_in_bytes).
  Context (Hfs_small : 12 * felem_size_in_bytes < 2 ^ width).

  Context (table_entries : list (F * F * F)).
  Context (Htable_len : length table_entries = 4%nat).
  Context (Htable_corr : forall i, (i < 4)%nat ->
    bn254_oncurve (nth i table_entries (Fzero, Fone, Fzero))
    /\ bn254_pt_eq (nth i table_entries (Fzero, Fone, Fzero))
                   (bn254_scmul (2 * i + 1)%nat (Px, Py, Pz))).

  Context (Hdigit_load : forall (n : nat) (base : word) (m : mem) R,
    (n < length dk)%nat ->
    (@DigitArray _ word mem base dk ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk 0))).

  Context (Hws_nn :
    forall n, (n <= length dk)%nat -> 0 <= weighted_sum (skipn n dk) 0).

  (* ---------------------------------------------------------------- *)
  (** *** 2.6 The end-to-end theorem                                    *)
  (* ---------------------------------------------------------------- *)

  (** Same statement as [BN254_wNAF_Instance.wnaf_single_full], with the
      abstract [curve_add] replaced by BN254's concrete a = 0 RCB
      addition and every group hypothesis DISCHARGED rather than
      assumed.

      HONESTY: the conclusion is a projective equality, not a Leibniz
      one between triples.  A consumer needing a canonical representative
      must normalise (divide through by Z, mapping Z = 0 to (0,1,0));
      [bn254_pt_eq] is exactly the equivalence under which that
      normalisation is sound.  This is forced — Leibniz equality is
      FALSE for RCB coordinates ([BLS12_wNAF_PointOppInverse.v]). *)
  Theorem bn254_wnaf_single_full :
    forall k,
    wsum dk = k -> 0 <= k ->
    forall pOx pOy pOz pAx pAy pAz pT pDK
      (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F)
      (Rinner : mem -> Prop) tr m l,
    map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
    map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
    map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
    map.get l "table_P" = Some pT ->
    map.get l "digits_k" = Some pDK ->
    (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
     ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0
     ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
     ⋆ Rinner) m ->
    WeakestPrecondition.cmd functions
      (wnaf_single_func_body curve_add_name curve_double_name "store_zero"
         felem_copy opp_name (Z.of_nat (length dk)) felem_size_in_bytes
         "digits_k" "table_P")
      tr m l
      (fun t m' l' =>
        exists Rx Ry Rz Ax' Ay' Az',
        bn254_oncurve (Rx, Ry, Rz)
        /\ bn254_pt_eq (Rx, Ry, Rz) (bn254_scmul (Z.to_nat k) (Px, Py, Pz))
        /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
            ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
            ⋆ DigitArray pDK dk ⋆ Table4 pT table_entries
            ⋆ Rinner) m').
  Proof.
    intros k Hk Hknn.
    intros pOx pOy pOz pAx pAy pAz pT pDK
      Ox0 Oy0 Oz0 Ax0 Ay0 Az0 Rinner tr m l
      Hl_ox Hl_oy Hl_oz Hl_ax Hl_ay Hl_az Hl_t Hl_dk Hsep.

    (* Every hypothesis [wnaf_single_full] asks for, as a NAMED term in
       the context, so that the discharge below is [eassumption] and does
       not depend on the order in which Section discharge presents
       [wnaf_single_full]'s arguments.  This is the P256_wNAF_Instance.v
       recipe; the point of naming them first is that no [eapply] has to
       guess a felem-laden argument. *)
    pose proof Hbounds_eq as Hbe.
    (* the group interface, proved in §2.2 *)
    pose proof bn254_pt_eq_equiv as Heqv.
    pose proof bn254_oncurve_id as Hoid.
    pose proof bn254_oncurve_curve_add as Hoadd.
    pose proof bn254_curve_add_Proper as HcaP.
    pose proof bn254_curve_add_id_l as Hidl.
    pose proof bn254_curve_add_assoc as Hass.
    (* the two Horner hypotheses, proved in §2.4 *)
    pose proof (bn254_horner_step dk Px Py Pz table_entries
                  Honcurve_P Htable_len Htable_corr
                  Hdigits_odd Hdigits_bounded Hws_nn) as Hhs.
    pose proof (bn254_horner_oncurve dk table_entries
                  Htable_len
                  (fun i Hi => proj1 (Htable_corr i Hi))
                  Hdigits_odd Hdigits_bounded) as Hho.
    (* the digit-array length equation, at [num_iters := length dk] *)
    pose proof (eq_refl (length dk)) as Hlen.

    (* Expose the chain's [scmul]; [bn254_add] stays folded so that it
       matches the [curve_add := bn254_add] instantiation. *)
    unfold bn254_scmul in *.

    Timeout 120
      (first
        [ eapply wnaf_single_full
            with (curve_add_name := curve_add_name)
                 (curve_double_name := curve_double_name)
                 (opp_name := opp_name)
                 (curve_add := bn254_add)
                 (pt_eq := bn254_pt_eq)
                 (oncurve := bn254_oncurve)
                 (dk := dk)
                 (num_iters := length dk)
                 (table_entries := table_entries)
                 (Px := Px) (Py := Py) (Pz := Pz)
                 (k := k)
        | eapply wnaf_single_full
            with (curve_add := bn254_add)
                 (pt_eq := bn254_pt_eq)
                 (oncurve := bn254_oncurve)
                 (k := k)
        | eapply wnaf_single_full ]).

    all: try eassumption.
    all: try ecancel_assumption.
    all: try lia.
    all: try (unfold bn254_pt_eq, bn254_oncurve, bn254_add,
                     bn254_point_opp in *; eassumption).
    (* Anything left prints itself instead of surfacing as an opaque
       "incomplete proof" at [Qed]. *)
    all: lazymatch goal with
         | |- ?G => fail 99 "BN254-FULL-RESIDUAL" G
         end.
  Qed.

End BN254_wNAF_Laws.

(* ==================================================================== *)
(** ** 3. Inventory                                                      *)
(* ==================================================================== *)

(** Proved here, from [RcbProjectiveLaws] at a := 0:

      bn254_curve_add_is_cadd   the a=0 chain IS the general-a chain at 0
      bn254_pt_eq_equiv         Equivalence
      bn254_oncurve_id / _curve_add / _point_opp        closure
      bn254_curve_add_Proper, bn254_point_opp_Proper    congruence
      bn254_curve_add_id_l / _id_r (and the point forms)
      bn254_curve_add_assoc, bn254_curve_add_comm
      bn254_point_opp_inverse

    Proved here, from [WnafTableBuild] §2:

      bn254_table4_ok           length 4 and [1P;3P;5P;7P], on-curve and
                                [pt_eq], from [oncurve P] alone

    Proved here, from [wNAF_Single_HornerAlgebra]:

      bn254_horner_step         the chain's [Hhorner_step]
      bn254_horner_oncurve      the chain's [Hhorner_oncurve]

    Composed here:

      bn254_wnaf_single_full    [BN254_wNAF_Instance.wnaf_single_full]
                                with all ten algebraic hypotheses
                                discharged

    Still open for BN254, in decreasing order of routineness:

      bn254_M_gt_27, bn254_Hthree_b, bn254_Hdisc
          computations over the concrete modulus once this file is
          instantiated at [bn254_field_parameters] with
          [three_b := F.of_Z M_pos 9] and [b := F.of_Z M_pos 3]
          ([bn254_three_b.v]);
      bn254_Hexcept
          no F-rational point of order two — the same obligation
          P-256/P-384/P-224 carry, dischargeable from
          [RcbProjectiveLaws.not_exceptional_of_no_two_torsion] given
          irreducibility of x^3 + b over F;
      the six callee specs
          a BN254 function table plus the [NistWnafWrappers.v] wrapper
          lemmas ([curve_add_inplace_general_ok], [curve_double_general_ok],
          [opp_inplace_ok], [store_zero_from_word_ok]) restated over
          [ladderstep_body] rather than [curve_add_general];
      the memory half of G7
          that a verified bedrock2 [precompute_w4] POPULATES the table
          buffer with [bn254_table4 P]. *)
