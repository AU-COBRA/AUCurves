(** * secp256k1 single-scalar wNAF scalar multiplication over the Rupicola
      general-a RCB addition.

    The secp256k1 instance of the chain of [P256_wNAF_Instance.v]: the
    verified single-scalar wNAF chain ([BN254_wNAF_Instance.wnaf_single_full],
    Qed, Section-parametric) at fiat-crypto's secp256k1 field representation
    [Field256k1.frep256k1] (prefix "secp256k1_"), with the point addition
    [rcb_add_general_gallina] instantiated in [CurveAddGeneralA_Secp256k1.v]
    at a = 0, 3b = 21.  The file is the P-256 one with the field, the
    constants and the no-2-torsion certificate replaced; its proofs are
    unchanged.

    Layout:
      §1  Gallina model: [secp256k1_curve_add], [secp256k1_scmul], constants;
      §1b the group laws of [RcbProjectiveLaws.v] at y^2 = x^3 + 7, under
          side conditions proved here: b = 7 with 3b = 21, 27 < p, the
          discriminant 27 * 49 <> 0, and totality of [Projective.add] from
          [Secp256k1NoTwoTorsion.secp256k1_cubic_no_root] (x^3 + 7 has no
          root mod p);
      §2  the function table: the derived add, its two constant loaders, the
          wrappers of NistWnafWrappers.v, fiat-crypto's
          [Field256k1.secp256k1_felem_copy], and the wNAF driver
          [secp256k1_wnaf_single_func] (257 digits, w = 4);
      §3  arithmetic discharges at 257 digits and the digit-load lemma;
      §4  callee-spec discharges from the function table;
      §5  [secp256k1_wnaf_single_full]: under the function table and the field
          leaf specs, the driver computes [k * P] up to projective equality
          ([pt_eq]) for 0 <= k < 2^256, on the caller's digit array
          ([wnaf_digits 4 k 257]) and table (on-curve points [pt_eq] to
          [1P; 3P; 5P; 7P]).

    Honesty ledger (this file): 0 Admitted, 0 Axiom. *)

From Stdlib Require Import ZArith Lia List.
From Stdlib Require Import RelationClasses.
Require Import Rupicola.Lib.Api.
Import bedrock2.WeakestPrecondition.
Require Import coqutil.Word.Bitwidth64.
Require Import bedrock2.BasicC64Semantics.
Require Import bedrock2.Scalars.
Require Import bedrock2.Array.
Require Import Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Interface.Compilation2.
Require Import Crypto.Bedrock.Field.Interface.CompilationAbstract.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import Crypto.Bedrock.Secp256k1.Field256k1.
Require Import Bedrock.Field.Synthesis.Examples.wNAF.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_ScalarMult.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_GLV_Func.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_GLV_LoopInvariant.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_ProcessDigits.
Require Import Bedrock.Field.Synthesis.Examples.BLS12_wNAF_GLV_Instance.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoadAndProcess.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_LoopBody.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_Proof.
Require Import Bedrock.Field.Synthesis.Examples.wNAF_Single_HornerAlgebra.
Require Import Bedrock.Field.Synthesis.Examples.BN254_wNAF_Instance.
Require Import Crypto.Algebra.Hierarchy.
Require Import Crypto.Algebra.Ring.
Require Import Crypto.Algebra.Group.
Require Import Crypto.Algebra.Field.
Require Import Crypto.Spec.WeierstrassCurve.
Require Import Crypto.Curves.Weierstrass.Projective.
Require Import Crypto.Util.Decidable.
Require Import Bedrock.Group.CurveAdd.RcbProjectiveLaws.
Require Import Bedrock.Group.CurveAdd.Secp256k1NoTwoTorsion.
Require Import Bedrock.Group.CurveAdd.StoreZero.
Require Import Bedrock.Group.CurveAdd.WNAFTable.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA.
Require Import Bedrock.Group.CurveAdd.CurveAddGeneralA_Secp256k1.
Require Import Bedrock.Group.ScalarMult.NistWnafWrappers.
Import Syntax BinInt String List.ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

Local Notation function_t :=
  (String.string * (list String.string * list String.string * Syntax.cmd.cmd))%type.

Section Secp256k1_wNAF.

  Existing Instances
    Bitwidth64.BW64
    Defaults64.default_parameters
    Defaults64.default_parameters_ok
    Field256k1.field_parameters
    secp256k1_field_parameters_ok
    Field256k1.frep256k1
    Field256k1.frep256k1_ok.

  Local Notation word := BasicC64Semantics.word.
  Local Notation F := (F M_pos).
  Local Notation Fzero := (@F.zero M_pos).
  Local Notation Fone := (@F.one M_pos).
  Local Notation FElem := (Compilation2.FElem).
  Local Notation Point3 b px py pz X Y Z :=
    (FElem b px X ⋆ FElem b py Y ⋆ FElem b pz Z)%sep.

  (* ============================================================== *)
  (* §1. Gallina model                                               *)
  (* ============================================================== *)

  Definition secp256k1_a_val : F := feval (proj1_sig secp256k1_a_felem).
  Definition secp256k1_three_b_val : F := feval (proj1_sig secp256k1_three_b_felem).

  (** The chain's [curve_add] at secp256k1: the derived RCB formula on
      plain triples.  [RcbProjectiveLaws.cadd] is the same forty-step
      chain as [NistWnafWrappers.curve_add_general_triple] (see
      [secp256k1_curve_add_is_wrapper] below); it is used here so that the
      group laws of RcbProjectiveLaws.v apply without a transport. *)
  Definition secp256k1_curve_add : F * F * F -> F * F * F -> F * F * F :=
    RcbProjectiveLaws.cadd secp256k1_a_val secp256k1_three_b_val.

  Lemma secp256k1_curve_add_is_wrapper :
    secp256k1_curve_add = curve_add_general_triple secp256k1_a_val secp256k1_three_b_val.
  Proof. reflexivity. Qed.

  Definition secp256k1_point_opp : F * F * F -> F * F * F :=
    RcbProjectiveLaws.point_opp_triple.

  (* ============================================================== *)
  (* §1b. G6: the projective equivalence and the group laws          *)
  (* ============================================================== *)

  (** The side conditions of RcbProjectiveLaws.v.

      [secp256k1_b_val] is the curve constant b (the chain only ever sees
      [three_b]); [secp256k1_M_gt_27] is the characteristic bound the
      [Ring.char_ge] instances need; [secp256k1_Hdisc] is
      4a^3 + 27b^2 <> 0 in the expanded form Projective.v expects;
      [secp256k1_Hexcept] is totality of [Projective.add], equivalently that
      the curve has no F-rational point of order two.

      The first four are DISCHARGED here, not assumed: [b] is the NIST
      constant [CurveAddGeneralA_Secp256k1.secp256k1_b], and the three proofs are
      [vm_compute] checks on concrete field elements.  [secp256k1_Hdisc]
      follows the idiom of
      [Bedrock.Curve.Secsecp256k1k1Curve_G1_bedrock.secp_discriminant]
      ([F.eq_to_Z_iff] / [vm_compute] / [discriminate]) rather than
      [Decidable.vm_decide], because [M_pos] here is a
      [FieldParameters] projection.  [secp256k1_Hexcept] is derived below
      from [Secp256k1NoTwoTorsion.secp256k1_cubic_no_root]; nothing in this
      section is assumed. *)
  Definition secp256k1_b_val : F := F.of_Z M_pos secp256k1_b.

  Lemma secp256k1_M_gt_27 : (27 < M_pos)%positive.
  Proof. vm_compute. reflexivity. Qed.

  Lemma secp256k1_Hthree_b :
    secp256k1_three_b_val = (secp256k1_b_val + secp256k1_b_val + secp256k1_b_val)%F.
  Proof.
    unfold secp256k1_three_b_val, secp256k1_b_val.
    rewrite secp256k1_three_b_feval.
    apply ModularArithmeticTheorems.F.eq_to_Z_iff.
    vm_compute. reflexivity.
  Qed.

  Lemma secp256k1_Hdisc : id
    ((((1 + 1 + 1 + 1) * secp256k1_a_val * secp256k1_a_val * secp256k1_a_val
       + ((1 + 1 + 1 + 1) * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1)
          + (1 + 1 + 1 + 1) + 1 + 1 + 1) * secp256k1_b_val * secp256k1_b_val) <> 0)%F).
  Proof.
    cbv [id]. unfold secp256k1_a_val, secp256k1_b_val. rewrite secp256k1_a_feval.
    intro H. apply (f_equal F.to_Z) in H. vm_compute in H. discriminate H.
  Qed.

  Local Instance secp256k1_char_ge_3 :
    @Ring.char_ge F eq F.zero F.one F.opp F.add F.sub F.mul 3%positive :=
    RcbProjectiveLaws.char_ge_3 secp256k1_M_gt_27.

  Local Notation Secp256k1_Ppoint :=
    (@Projective.point F eq F.zero F.add F.mul secp256k1_a_val secp256k1_b_val).

  Local Notation Secp256k1_not_exceptional :=
    (@Projective.not_exceptional F eq F.zero F.one F.opp F.add F.sub
       F.mul F.inv F.div secp256k1_a_val secp256k1_b_val _ secp256k1_char_ge_3 _).

  (** No F-rational point of order two, equivalently: x^3 - 3x + b has
      no root modulo the secp256k1 prime.  Proved, not assumed:
      [Secp256k1NoTwoTorsion.secp256k1_cubic_no_root] instantiates the
      root-free certificate of
      [Bedrock.Group.CurveAdd.CubicNoRoot] at the secp256k1 constants.  Its
      two hypotheses read the coefficients back as canonical residues;
      both are [vm_compute] checks. *)
  Lemma secp256k1_no_two_torsion :
    RcbProjectiveLaws.no_two_torsion secp256k1_a_val secp256k1_b_val.
  Proof.
    unfold RcbProjectiveLaws.no_two_torsion.
    apply Secp256k1NoTwoTorsion.secp256k1_cubic_no_root.
    - unfold secp256k1_a_val. rewrite secp256k1_a_feval.
      rewrite ModularArithmeticTheorems.F.to_Z_of_Z.
      vm_compute. reflexivity.
    - unfold secp256k1_b_val.
      rewrite ModularArithmeticTheorems.F.to_Z_of_Z.
      vm_compute. reflexivity.
  Qed.

  (** Totality of [Projective.add] at secp256k1.  Fully applied rather than
      [eapply]d: [not_exceptional_of_no_two_torsion] is generalised over
      the whole ambient section context of RcbProjectiveLaws.v, and
      naming every argument avoids both the unresolved-variable failure
      and the search. *)
  Lemma secp256k1_Hexcept : forall P Q : Secp256k1_Ppoint, Secp256k1_not_exceptional P Q.
  Proof.
    exact (@RcbProjectiveLaws.not_exceptional_of_no_two_torsion
             Field256k1.field_parameters secp256k1_field_parameters_ok secp256k1_M_gt_27
             secp256k1_a_val secp256k1_b_val secp256k1_three_b_val
             secp256k1_Hthree_b secp256k1_Hdisc secp256k1_no_two_torsion).
  Qed.

  (** The chain's [pt_eq] and [oncurve] at secp256k1. *)
  Definition secp256k1_pt_eq : F * F * F -> F * F * F -> Prop :=
    RcbProjectiveLaws.pt_eq.

  Definition secp256k1_oncurve : F * F * F -> Prop :=
    RcbProjectiveLaws.oncurve secp256k1_a_val secp256k1_b_val.

  (** No local [prime] instance is declared here: RcbProjectiveLaws
      exports [prime_M_pos], and a second, opaque proof of the same
      Prop would make [F.field_modulo]'s instance argument differ from
      the one baked into that file's theorems — [Znumtheory.prime] is
      an ordinary Prop, so the two would not be convertible.  The ring
      below needs no primality; it exists only for the [ring] fallback
      of [secp256k1_oncurve_id]. *)
  Add Ring Fp_ring_secp256k1 : (F.ring_theory M_pos)
    (morphism (F.ring_morph M_pos),
     constants [F.is_constant],
     div (F.morph_div_theory M_pos),
     power_tac (F.power_theory M_pos) [F.is_pow_constant]).

  Local Ltac rcb :=
    unfold secp256k1_pt_eq, secp256k1_oncurve, secp256k1_curve_add, secp256k1_point_opp in *.

  (** The curve constants [b] and [three_b] must be pinned by hand at
      every discharge below.  A RcbProjectiveLaws theorem is generalised
      over every Section variable its PROOF TERM mentions, not only
      those in its statement, and [ring] / [fsatz] emit [abstract]ed
      subproof constants that Coq generalises over the WHOLE ambient
      section context.  So e.g. [pt_eq_Equivalence], whose statement
      mentions neither [b] nor [three_b], still takes both — and
      [apply] / [eapply] cannot invent them ("Unable to find an
      instance for the variables b, three_b").

      The alternation tries the pinnings from most to least specific; a
      binding name absent from a given lemma makes that branch fail and
      the next one run.  The alternations are written out per lemma
      rather than factored into a tactic taking the lemma as an
      argument, because a [with (x := t)] binding name must be resolved
      against a concrete constant.  This is the §3a pattern of
      WnafTableBuild.v, which compiles against the same file. *)
  Local Ltac rcb_ctx :=
    first [ eassumption
          | exact secp256k1_M_gt_27 | exact secp256k1_Hthree_b
          | exact secp256k1_Hdisc   | exact secp256k1_Hexcept ].

  Lemma secp256k1_pt_eq_refl : forall p, secp256k1_pt_eq p p.
  Proof.
    intros p. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_refl
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_refl; rcb_ctx ].
  Qed.

  Lemma secp256k1_pt_eq_sym : forall p q, secp256k1_pt_eq p q -> secp256k1_pt_eq q p.
  Proof.
    intros p q H. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_sym
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_sym; rcb_ctx ].
  Qed.

  Lemma secp256k1_pt_eq_trans : forall p q r,
    secp256k1_pt_eq p q -> secp256k1_pt_eq q r -> secp256k1_pt_eq p r.
  Proof.
    intros p q r H1 H2. rcb.
    first
      [ eapply RcbProjectiveLaws.pt_eq_trans
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.pt_eq_trans; rcb_ctx ].
  Qed.

  Lemma secp256k1_pt_eq_equiv : Equivalence secp256k1_pt_eq.
  Proof.
    constructor;
      [ exact secp256k1_pt_eq_refl | exact secp256k1_pt_eq_sym | exact secp256k1_pt_eq_trans ].
  Qed.

  Lemma secp256k1_oncurve_id : secp256k1_oncurve (Fzero,Fone,Fzero).
  Proof.
    rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_id
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_id; rcb_ctx
      | (* Independent of the discharge shape: [oncurve] and [id_pt] are
           plain definitions, so unfold and compute.  This is the script
           of [RcbProjectiveLaws.oncurve_id] itself. *)
        cbv [RcbProjectiveLaws.oncurve RcbProjectiveLaws.id_pt];
        split; [ ring | intros _; fsatz ] ].
  Qed.

  Lemma secp256k1_oncurve_curve_add : forall P Q,
    secp256k1_oncurve P -> secp256k1_oncurve Q -> secp256k1_oncurve (secp256k1_curve_add P Q).
  Proof.
    intros P Q HP HQ. rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_cadd
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_cadd; rcb_ctx ].
  Qed.

  Lemma secp256k1_oncurve_point_opp : forall P,
    secp256k1_oncurve P -> secp256k1_oncurve (secp256k1_point_opp P).
  Proof.
    intros P HP. rcb.
    first
      [ eapply RcbProjectiveLaws.oncurve_opp
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.oncurve_opp; rcb_ctx ].
  Qed.

  Lemma secp256k1_curve_add_Proper : forall P P' Q Q',
    secp256k1_oncurve P -> secp256k1_oncurve P' -> secp256k1_oncurve Q -> secp256k1_oncurve Q' ->
    secp256k1_pt_eq P P' -> secp256k1_pt_eq Q Q' ->
    secp256k1_pt_eq (secp256k1_curve_add P Q) (secp256k1_curve_add P' Q').
  Proof.
    intros P P' Q Q' Hp Hp' Hq Hq' E1 E2. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_Proper
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_Proper; rcb_ctx ].
  Qed.

  Lemma secp256k1_point_opp_Proper : forall P P',
    secp256k1_oncurve P -> secp256k1_oncurve P' -> secp256k1_pt_eq P P' ->
    secp256k1_pt_eq (secp256k1_point_opp P) (secp256k1_point_opp P').
  Proof.
    intros P P' Hp Hp' E. rcb.
    first
      [ eapply RcbProjectiveLaws.point_opp_Proper
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_Proper; rcb_ctx ].
  Qed.

  Lemma secp256k1_curve_add_id_r : forall x y z,
    secp256k1_oncurve (x,y,z) ->
    secp256k1_pt_eq (secp256k1_curve_add (x,y,z) (Fzero,Fone,Fzero)) (x,y,z).
  Proof.
    intros x y z Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_id_r
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_r; rcb_ctx ].
  Qed.

  Lemma secp256k1_curve_add_id_l : forall x y z,
    secp256k1_oncurve (x,y,z) ->
    secp256k1_pt_eq (secp256k1_curve_add (Fzero,Fone,Fzero) (x,y,z)) (x,y,z).
  Proof.
    intros x y z Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_id_l
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_id_l; rcb_ctx ].
  Qed.

  Lemma secp256k1_curve_add_assoc : forall P Q R,
    secp256k1_oncurve P -> secp256k1_oncurve Q -> secp256k1_oncurve R ->
    secp256k1_pt_eq (secp256k1_curve_add P (secp256k1_curve_add Q R))
               (secp256k1_curve_add (secp256k1_curve_add P Q) R).
  Proof.
    intros P Q R Hp Hq Hr. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_assoc
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_assoc; rcb_ctx ].
  Qed.

  Lemma secp256k1_curve_add_comm : forall P Q,
    secp256k1_oncurve P -> secp256k1_oncurve Q ->
    secp256k1_pt_eq (secp256k1_curve_add P Q) (secp256k1_curve_add Q P).
  Proof.
    intros P Q Hp Hq. rcb.
    first
      [ eapply RcbProjectiveLaws.cadd_comm
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm with (b := secp256k1_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.cadd_comm; rcb_ctx ].
  Qed.

  Lemma secp256k1_point_opp_inverse : forall P,
    secp256k1_oncurve P ->
    secp256k1_pt_eq (secp256k1_curve_add P (secp256k1_point_opp P)) (Fzero,Fone,Fzero).
  Proof.
    intros P Hp. rcb.
    first
      [ eapply RcbProjectiveLaws.point_opp_inverse
          with (a := secp256k1_a_val) (b := secp256k1_b_val)
               (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse
          with (b := secp256k1_b_val) (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse
          with (three_b := secp256k1_three_b_val); rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse with (b := secp256k1_b_val);
        rcb_ctx
      | eapply RcbProjectiveLaws.point_opp_inverse; rcb_ctx ].
  Qed.

  (** [scmul] of BLS12_GLV_LoopInvariant.v, the chain's [scmul_s].
      Qualified: WNAFTable.v (imported later) also exports a [scmul]
      whose [Fzero]/[Fone] are implicit, so the short name resolves to
      the wrong one. *)
  Definition secp256k1_scmul : nat -> F * F * F -> F * F * F :=
    BLS12_GLV_LoopInvariant.scmul Fzero Fone secp256k1_curve_add.

  (** wNAF parameters: 256-bit scalars, window 4, hence 257 digits
      (cf. 129 digits for 128-bit GLV halves in the BLS12 chain). *)
  Definition secp256k1_num_digits : nat := 257%nat.

  Lemma secp256k1_felem_size_in_bytes_eq : felem_size_in_bytes = 32.
  Proof. vm_compute. reflexivity. Qed.

  (* ============================================================== *)
  (* §2. Function table                                              *)
  (* ============================================================== *)

  Definition secp256k1_curve_add_inplace_func : function_t :=
    curve_add_inplace_general_func.
  Definition secp256k1_curve_double_func : function_t :=
    curve_double_general_func.
  Definition secp256k1_opp_inplace_func : function_t :=
    opp_inplace_func.
  Definition secp256k1_store_zero_func : function_t :=
    store_zero_from_word_func.

  (** The wNAF driver.  Same shape as [bn254_wnaf_single_func]
      (wNAF_GLV_Func.v) with 257 iterations; [felem_size_in_bytes]
      is kept symbolic so the body matches [wnaf_single_full]'s
      statement syntactically ([secp256k1_felem_size_in_bytes_eq] gives 32
      for extraction). *)
  Definition secp256k1_wnaf_single_func : function_t :=
    ("secp256k1_wnaf_single",
     (["outx"; "outy"; "outz";
       "table_P"; "digits_k";
       "auxx"; "auxy"; "auxz"],
      []%list,
      wnaf_single_func_body "curve_add" "curve_double" "store_zero"
        felem_copy "opp_inplace" (Z.of_nat secp256k1_num_digits)
        felem_size_in_bytes
        "digits_k" "table_P")).

  (** Function-table membership bundle used by the discharges below.
      The five field leaves (mul/add/sub/opp/from_word) are the
      fiat-crypto syntheses of secp256k1_prime.v and enter through their
      [spec_of_*] instances rather than by body. *)
  Definition secp256k1_wnaf_table_ok (functions : Semantics.env) : Prop :=
    map.get functions "curve_add_general" = Some secp256k1_curve_add_general_func
    /\ map.get functions "secp256k1_three_b" = Some secp256k1_three_b_func
    /\ map.get functions "secp256k1_a_const" = Some secp256k1_a_const_func
    /\ map.get functions "curve_add" = Some (snd secp256k1_curve_add_inplace_func)
    /\ map.get functions "curve_double" = Some (snd secp256k1_curve_double_func)
    /\ map.get functions "store_zero" = Some (snd secp256k1_store_zero_func)
    (* G5: the aliasing-tolerant negation wrapper the chain now calls *)
    /\ map.get functions "opp_inplace" = Some (snd secp256k1_opp_inplace_func)
    /\ map.get functions felem_copy = Some (snd Field256k1.secp256k1_felem_copy).

  Definition secp256k1_wnaf_leaf_specs (functions : Semantics.env) : Prop :=
    spec_of_BinOp bin_mul functions
    /\ spec_of_BinOp bin_add functions
    /\ spec_of_BinOp bin_sub functions
    /\ spec_of_UnOp un_opp functions
    /\ spec_of_from_word functions.

  (* ============================================================== *)
  (* §3. Arithmetic discharges at len = 257                          *)
  (* ============================================================== *)

  Definition secp256k1_digits (k : Z) : list Z := wnaf_digits 4 k secp256k1_num_digits.

  Lemma secp256k1_digits_length : forall k, length (secp256k1_digits k) = secp256k1_num_digits.
  Proof. intros. apply wnaf_digits_length. Qed.

  Lemma secp256k1_digits_wsum : forall k,
    0 <= k < 2 ^ 256 -> wsum (secp256k1_digits k) = k.
  Proof.
    intros k Hk. unfold secp256k1_digits, secp256k1_num_digits.
    apply wnaf_correct; [lia | lia |].
    replace (Z.of_nat (257 - 1)) with 256 by lia. exact Hk.
  Qed.

  Lemma secp256k1_digits_Hws_nn : forall k,
    0 <= k < 2 ^ 256 ->
    forall n, (n <= secp256k1_num_digits)%nat ->
    0 <= weighted_sum (skipn n (secp256k1_digits k)) 0.
  Proof.
    intros k Hk n Hn. unfold secp256k1_digits, secp256k1_num_digits in *.
    apply (weighted_sum_skipn_wnaf_nonneg 4 k 257 n);
      [lia | split; [lia|]; replace (Z.of_nat (257 - 1)) with 256 by lia; lia
       | exact Hn].
  Qed.

  Lemma secp256k1_digits_bounded : forall k,
    0 <= k ->
    forall i, (i < secp256k1_num_digits)%nat -> -7 <= nth i (secp256k1_digits k) 0 <= 7.
  Proof.
    intros k Hk i Hi. unfold secp256k1_digits, secp256k1_num_digits in *.
    assert (Hb : Z.abs (nth i (wnaf_digits 4 k 257) 0) < 2 ^ (Z.of_nat 4 - 1)).
    { apply (wnaf_digit_bound 4 k 257 i).
      - lia.
      - exact Hk.
      - apply nth_error_nth' with (d := 0). rewrite wnaf_digits_length. exact Hi. }
    change (Z.of_nat 4 - 1) with 3 in Hb. simpl (2^3) in Hb.
    apply Z.abs_lt in Hb. lia.
  Qed.

  (** Non-zero wNAF digits are odd (script of
      [BLS12_wNAF_GLV_Instance.wnaf_digits_odd] with 129 -> 257). *)
  Lemma secp256k1_digits_odd : forall k,
    0 <= k ->
    forall i, (i < secp256k1_num_digits)%nat ->
    Z.odd (nth i (secp256k1_digits k) 0) = true \/ nth i (secp256k1_digits k) 0 = 0.
  Proof.
    intros k Hk i Hi. unfold secp256k1_digits, secp256k1_num_digits in *.
    destruct (Z.eq_dec (nth i (wnaf_digits 4 k 257) 0) 0) as [Hz|Hnz].
    - right. exact Hz.
    - left.
      revert k Hk i Hi Hnz. induction (257)%nat as [|len IH]; intros k Hk i Hi Hnz.
      { exfalso. lia. }
      simpl wnaf_digits. destruct i as [|i'];
      [ simpl nth in Hnz |- *; unfold wnaf_digit in Hnz |- *;
        destruct (Z.odd k) eqn:Hok; [|exfalso; apply Hnz; reflexivity];
        set (m := k mod 2 ^ Z.of_nat 4) in *;
        assert (Hmodd : Z.odd m = true)
          by (subst m; pose proof (Z.div_mod k (2^Z.of_nat 4) ltac:(simpl;lia)) as Hkdm;
              assert (Z.odd (k mod 2^Z.of_nat 4) = Z.odd k)
                by (rewrite Hkdm at 2; rewrite Z.odd_add, Z.odd_mul; simpl; ring_simplify; reflexivity);
              congruence);
        destruct (m >=? 2 ^ (Z.of_nat 4 - 1));
        [ rewrite <- Z.negb_even, Z.even_sub; simpl (Z.even (2 ^ Z.of_nat 4));
          rewrite <- Z.negb_even in Hmodd; apply Bool.negb_true_iff in Hmodd;
          rewrite Hmodd; reflexivity
        | exact Hmodd ]
      | simpl nth in Hnz |- *;
        apply IH; [apply wnaf_shift_nonneg; lia | lia | exact Hnz] ].
  Qed.

  Lemma secp256k1_Hnbound : Z.of_nat secp256k1_num_digits < 2 ^ 64.
  Proof. vm_compute. reflexivity. Qed.

  Lemma secp256k1_Hfs_pos : 0 < felem_size_in_bytes.
  Proof. rewrite secp256k1_felem_size_in_bytes_eq. lia. Qed.

  Lemma secp256k1_Hfs_small : 12 * felem_size_in_bytes < 2 ^ 64.
  Proof. rewrite secp256k1_felem_size_in_bytes_eq. vm_compute. reflexivity. Qed.

  (** Digit load: the generic lemma of BLS12_wNAF_GLV_Instance.v §2
      already has the required shape (its [DigitArray] is the one of
      BLS12_wNAF_ProcessDigits.v used by the chain). *)
  Lemma secp256k1_Hdigit_load : forall (dk : list Z) (n : nat) (base : word)
      (m : BasicC64Semantics.mem) R,
    (n < length dk)%nat ->
    (@DigitArray _ word BasicC64Semantics.mem base dk ⋆ R) m ->
    Memory.load access_size.word m
      (word.add base (word.mul (word.of_Z (Z.of_nat n))
        (word.of_Z (Memory.bytes_per_word 64)))) =
    Some (encode_digit (nth n dk 0)).
  Proof.
    intros. eapply digit_load_from_array; eassumption.
  Qed.

  (* ============================================================== *)
  (* §4. Callee-spec discharges from the table                       *)
  (* ============================================================== *)

  (** The derived add meets its FElem-level spec
      (CurveAddGeneralA_Secp256k1.secp256k1_curve_add_general_full). *)
  Lemma secp256k1_rcb_add_general_spec :
    forall functions,
      secp256k1_wnaf_table_ok functions ->
      secp256k1_wnaf_leaf_specs functions ->
      spec_of_rcb_add_general secp256k1_three_b_felem secp256k1_a_felem functions.
  Proof.
    intros functions (Hadd & Htb & Ha & _ & _ & _ & _ & _) (Hmul & Hfadd & Hsub & _ & _).
    (* Explicit discharge, as in P384_wNAF_Instance.v: a fully applied term
       instead of [eapply ...; eassumption], whose cost is the conclusion
       unification rather than the assumption lookup. *)
    refine (secp256k1_curve_add_general_full functions _ Htb Ha Hmul Hfadd Hsub).
    exact Hadd.
  Qed.

  Lemma secp256k1_felem_copy_spec :
    forall functions,
      secp256k1_wnaf_table_ok functions ->
      spec_of_felem_copy functions.
  Proof.
    intros functions (_ & _ & _ & _ & _ & _ & _ & Hcopy).
    (* [secp256k1_felem_copy_ok : program_logic_goal_for_function! secp256k1_coord_felem_copy]
       unfolds to [map.get functions felem_copy = Some secp256k1_coord_felem_copy ->
       spec_of_felem_copy functions] (bedrock2 program_logic_goal_for). *)
    exact (Field256k1.secp256k1_felem_copy_correct functions Hcopy).
  Qed.

  (** [curve_add_g] of NistWnafWrappers.v at the secp256k1 constants is
      [secp256k1_curve_add] (both are [curve_add_general_triple] at
      [feval (proj1_sig secp256k1_a_felem)] / [feval (proj1_sig secp256k1_three_b_felem)]). *)
  Lemma secp256k1_curve_add_g_eq :
    curve_add_g secp256k1_three_b_felem secp256k1_a_felem = secp256k1_curve_add.
  Proof. reflexivity. Qed.

  Lemma secp256k1_HCurveAddInplace :
    forall functions,
      secp256k1_wnaf_table_ok functions ->
      secp256k1_wnaf_leaf_specs functions ->
      spec_of_curve_add_inplace_general secp256k1_three_b_felem secp256k1_a_felem functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & Hca & _ & _ & _ & _).
    eapply curve_add_inplace_general_ok;
      eauto using secp256k1_rcb_add_general_spec, secp256k1_felem_copy_spec.
  Qed.

  Lemma secp256k1_HCurveDouble :
    forall functions,
      secp256k1_wnaf_table_ok functions ->
      secp256k1_wnaf_leaf_specs functions ->
      spec_of_curve_double_general secp256k1_three_b_felem secp256k1_a_felem functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & _ & Hcd & _ & _ & _).
    eapply curve_double_general_ok;
      eauto using secp256k1_rcb_add_general_spec, secp256k1_felem_copy_spec.
  Qed.

  Lemma secp256k1_HStoreZero :
    forall functions,
      secp256k1_wnaf_table_ok functions ->
      secp256k1_wnaf_leaf_specs functions ->
      @StoreZero.spec_of_store_zero _ _ _ _ _ _
        Field256k1.field_parameters Field256k1.frep256k1 functions.
  Proof.
    intros functions (_ & _ & _ & _ & _ & Hsz & _ & _) (_ & _ & _ & _ & Hfw).
    (* After Section discharge [store_zero_from_word_ok] takes, before
       [functions]: 6 implicits (width, BW, word, mem, locals,
       ext_spec), the four ok-hypotheses (word.ok, map.ok mem,
       map.ok locals, ext_spec.ok), field_parameters +
       FieldParameters_ok, field_representation +
       FieldRepresentation_ok, the bounds equation, and the two
       constant felems of the Section (three_b, a_const — unused by
       this lemma's conclusion, so any well-typed felems serve).
       Hence the fully applied form below; [_] for the ten class
       arguments, which unification and the ambient Existing Instances
       resolve.  [secp256k1_store_zero_func] is [store_zero_from_word_func]
       at these instances, so [Hsz] matches the table premise by
       conversion. *)
    first
      [ exact (@store_zero_from_word_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 secp256k1_bounds_eq secp256k1_three_b_felem secp256k1_a_felem
                 functions Hsz Hfw)
      | eapply store_zero_from_word_ok with (functions := functions);
        [ solve [ typeclasses eauto | exact _ ] ..
        | exact secp256k1_bounds_eq
        | exact secp256k1_three_b_felem
        | exact secp256k1_a_felem
        | exact Hsz
        | exact Hfw ]
      | eapply store_zero_from_word_ok with (functions := functions);
        repeat first
          [ exact secp256k1_bounds_eq
          | exact secp256k1_three_b_felem
          | exact secp256k1_a_felem
          | exact Hsz
          | exact Hfw
          | solve [ typeclasses eauto | exact _ ] ] ].
  Qed.

  (** G5: both shapes of the negation the chain needs, at the wrapper
      name "opp_inplace".  [NistWnafWrappers.opp_inplace_ok] is Qed, so
      this is a discharge and not an assumption.  Same three-way
      alternation as [secp256k1_HStoreZero]: the Section variables of
      NistWnafWrappers' [Specs] section become leading arguments
      ([Hbounds_eq] and the two constant felems among them), and the
      alternation avoids committing to how many. *)
  Lemma secp256k1_HOppInplace_spec :
    forall functions,
      secp256k1_wnaf_table_ok functions ->
      secp256k1_wnaf_leaf_specs functions ->
      spec_of_opp_inplace functions.
  Proof.
    intros functions Htab Hleaf.
    pose proof Htab as (_ & _ & _ & _ & _ & _ & Hoi & _).
    pose proof Hleaf as (_ & _ & _ & Hopp & _).
    pose proof (secp256k1_felem_copy_spec functions Htab) as Hcopy.
    first
      [ exact (@opp_inplace_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 secp256k1_bounds_eq secp256k1_three_b_felem secp256k1_a_felem
                 functions Hoi Hopp Hcopy)
      | eapply opp_inplace_ok with (functions := functions);
        [ solve [ typeclasses eauto | exact _ ] ..
        | exact secp256k1_bounds_eq
        | exact secp256k1_three_b_felem
        | exact secp256k1_a_felem
        | exact Hoi
        | exact Hopp
        | exact Hcopy ]
      | eapply opp_inplace_ok with (functions := functions);
        repeat first
          [ exact secp256k1_bounds_eq
          | exact secp256k1_three_b_felem
          | exact secp256k1_a_felem
          | exact Hoi
          | exact Hopp
          | exact Hcopy
          | solve [ typeclasses eauto | exact _ ] ] ].
  Qed.

  (* ============================================================== *)
  (* §5. End-to-end statement                                        *)
  (* ============================================================== *)

  (** Table correctness, in the chain's quotiented form (plan G7).

      HONESTY: this is STRICTLY STRONGER than the Leibniz version it
      replaces on the [oncurve] conjunct, and strictly weaker on the
      equation ([pt_eq] instead of [=]).  Both changes are forced: the
      RCB table produced by any doubling/addition chain is only
      projectively equal to the odd multiples, and [oncurve] does not
      follow from [pt_eq] (e.g. [pt_eq (0,0,0) (0,1,0)] holds and
      (0,0,0) is not a projective point). *)
  Definition secp256k1_table_ok (Px Py Pz : F) (table_entries : list (F * F * F)) : Prop :=
    length table_entries = 4%nat /\
    forall i, (i < 4)%nat ->
      secp256k1_oncurve (nth i table_entries (Fzero,Fone,Fzero))
      /\ secp256k1_pt_eq (nth i table_entries (Fzero,Fone,Fzero))
                    (secp256k1_scmul (2 * i + 1) (Px, Py, Pz)).

  (** Horner step, from [wNAF_Single_HornerAlgebra.horner_step_single]
      (whose [sm] is definitionally [secp256k1_scmul] and whose
      [digit_point_local] is definitionally ProcessDigits' [digit_point]
      at [point_opp := secp256k1_point_opp]). *)
  Lemma secp256k1_Hhorner_step :
    forall k, 0 <= k < 2 ^ 256 ->
    forall Px Py Pz table_entries,
      secp256k1_oncurve (Px,Py,Pz) ->
      secp256k1_table_ok Px Py Pz table_entries ->
      forall n (Ox Oy Oz : F),
        (n < secp256k1_num_digits)%nat ->
        let ws_old := weighted_sum (skipn (S n) (secp256k1_digits k)) 0 in
        secp256k1_oncurve (Ox,Oy,Oz) ->
        secp256k1_pt_eq (Ox,Oy,Oz) (secp256k1_scmul (Z.to_nat (2 * ws_old)) (Px,Py,Pz)) ->
        let d := nth n (secp256k1_digits k) 0 in
        secp256k1_pt_eq
          (if d =? 0 then (Ox,Oy,Oz)
           else secp256k1_curve_add (Ox,Oy,Oz) (digit_point d table_entries))
          (secp256k1_scmul (Z.to_nat (weighted_sum (skipn n (secp256k1_digits k)) 0)) (Px,Py,Pz)).
  Proof.
    intros k Hk Px Py Pz tab HPoc Htab n Ox Oy Oz Hn ws_old Hoc Hacc d.
    destruct Htab as (Hlen4 & Hcorr).
    assert (Hlen : length (secp256k1_digits k) = secp256k1_num_digits)
      by apply secp256k1_digits_length.
    assert (Hn' : (n < length (secp256k1_digits k))%nat)
      by (rewrite Hlen; exact Hn).
    assert (Hodd : forall i, (i < length (secp256k1_digits k))%nat ->
              Z.odd (nth i (secp256k1_digits k) 0) = true \/ nth i (secp256k1_digits k) 0 = 0).
    { intros i Hi. apply secp256k1_digits_odd; [lia | rewrite <- Hlen; exact Hi]. }
    assert (Hb : forall i, (i < length (secp256k1_digits k))%nat ->
              -7 <= nth i (secp256k1_digits k) 0 <= 7).
    { intros i Hi. apply secp256k1_digits_bounded; [lia | rewrite <- Hlen; exact Hi]. }
    assert (Hws : forall j, (j <= length (secp256k1_digits k))%nat ->
              0 <= weighted_sum (skipn j (secp256k1_digits k)) 0).
    { intros j Hj. apply secp256k1_digits_Hws_nn; [exact Hk | rewrite <- Hlen; exact Hj]. }
    (* [sm] of wNAF_Single_HornerAlgebra.v is [secp256k1_scmul] and its
       [digit_point_local] is ProcessDigits' [digit_point] by
       conversion (same fixpoint / same [point_opp]), so the
       instantiated statement is the goal up to delta.  The argument
       order is the Section declaration order of [SingleHornerAlgebra]. *)
    pose proof (horner_step_single
                  Fzero Fone secp256k1_curve_add secp256k1_point_opp
                  secp256k1_pt_eq secp256k1_pt_eq_equiv secp256k1_oncurve
                  secp256k1_oncurve_id secp256k1_oncurve_curve_add
                  secp256k1_oncurve_point_opp
                  secp256k1_curve_add_Proper secp256k1_point_opp_Proper
                  secp256k1_curve_add_id_r secp256k1_curve_add_id_l
                  secp256k1_curve_add_assoc secp256k1_curve_add_comm
                  secp256k1_point_opp_inverse
                  (secp256k1_digits k) Px Py Pz tab
                  HPoc Hlen4 Hcorr Hodd Hb Hws
                  n Ox Oy Oz Hn' Hoc Hacc) as Hstep.
    first [ exact Hstep | apply Hstep ].
  Qed.

  (** On-curve closure of one Horner step: the [oncurve] half of the
      chain's [Hhorner_oncurve], from [digit_point_local_oncurve]. *)
  Lemma secp256k1_Hhorner_oncurve :
    forall k, 0 <= k ->
    forall Px Py Pz table_entries,
      secp256k1_table_ok Px Py Pz table_entries ->
      forall n (Ox Oy Oz : F),
        (n < secp256k1_num_digits)%nat ->
        secp256k1_oncurve (Ox,Oy,Oz) ->
        let d := nth n (secp256k1_digits k) 0 in
        secp256k1_oncurve
          (if d =? 0 then (Ox,Oy,Oz)
           else secp256k1_curve_add (Ox,Oy,Oz) (digit_point d table_entries)).
  Proof.
    intros k Hk Px Py Pz tab Htab n Ox Oy Oz Hn Hoc d.
    destruct Htab as (Hlen4 & Hcorr).
    assert (Hdoc : secp256k1_oncurve (digit_point d tab)).
    { assert (Hentries : forall i, (i < 4)%nat ->
                secp256k1_oncurve (nth i tab (Fzero,Fone,Fzero)))
        by (intros i Hi; exact (proj1 (Hcorr i Hi))).
      pose proof (digit_point_oncurve_full
                    Fzero Fone secp256k1_curve_add secp256k1_point_opp
                    secp256k1_pt_eq secp256k1_pt_eq_equiv secp256k1_oncurve
                    secp256k1_oncurve_id secp256k1_oncurve_curve_add
                    secp256k1_oncurve_point_opp
                    secp256k1_curve_add_Proper secp256k1_point_opp_Proper
                    secp256k1_curve_add_id_r secp256k1_curve_add_id_l
                    secp256k1_curve_add_assoc secp256k1_curve_add_comm
                    secp256k1_point_opp_inverse
                    tab d Hlen4 Hentries
                    (secp256k1_digits_odd k Hk n Hn)
                    (secp256k1_digits_bounded k Hk n Hn)) as Hdp.
      first [ exact Hdp | apply Hdp ]. }
    destruct (d =? 0); [exact Hoc | apply secp256k1_oncurve_curve_add; assumption].
  Qed.

  (** The citable statement.  Under the function table, the field leaf
      specs, and G7's caller-supplied data, the body of
      [secp256k1_wnaf_single_func] computes [k * P] in the chain's sense
      ([secp256k1_scmul (Z.to_nat k) P]) UP TO PROJECTIVE EQUIVALENCE, and
      the result is on the curve.

      HONESTY: the conclusion is weaker than a Leibniz equation between
      triples — it is [secp256k1_pt_eq], i.e. equality of the projective
      points the triples represent.  A consumer that needs a canonical
      representative must normalise (divide through by Z, mapping Z = 0
      to (0,1,0)); [pt_eq] is exactly the equivalence under which that
      normalisation is sound.  The G6 group laws are discharged, not assumed;
      the curve-level side conditions they rest on ([secp256k1_b_val],
      [secp256k1_M_gt_27], [secp256k1_Hthree_b], [secp256k1_Hdisc], [secp256k1_Hexcept])
      are all proved in §1b of this file. *)
  Theorem secp256k1_wnaf_single_full :
    forall functions,
      secp256k1_wnaf_table_ok functions ->
      secp256k1_wnaf_leaf_specs functions ->
      (* G5 is no longer a hypothesis: both shapes of the negation come
         from [secp256k1_HOppInplace_spec], i.e. from the function table's
         "opp_inplace" entry plus the field leaf specs. *)
      forall k, 0 <= k < 2 ^ 256 ->
      forall Px Py Pz table_entries,
        (* G7: the base point is on the curve *)
        secp256k1_oncurve (Px,Py,Pz) ->
        (* G7: the caller's table holds on-curve points ~ [1P;3P;5P;7P] *)
        secp256k1_table_ok Px Py Pz table_entries ->
      forall pOx pOy pOz pAx pAy pAz pT pDK
        (Ox0 Oy0 Oz0 Ax0 Ay0 Az0 : F)
        (Rinner : BasicC64Semantics.mem -> Prop) tr m l,
      map.get l "outx" = Some pOx -> map.get l "outy" = Some pOy ->
      map.get l "outz" = Some pOz -> map.get l "auxx" = Some pAx ->
      map.get l "auxy" = Some pAy -> map.get l "auxz" = Some pAz ->
      map.get l "table_P" = Some pT ->
      map.get l "digits_k" = Some pDK ->
      (* G7: the caller's digit array holds [wnaf_digits 4 k 257] *)
      (Point3 (Some tight_bounds) pOx pOy pOz Ox0 Oy0 Oz0
       ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax0 Ay0 Az0
       ⋆ DigitArray pDK (secp256k1_digits k) ⋆ Table4 pT table_entries
       ⋆ Rinner) m ->
      WeakestPrecondition.cmd functions
        (snd (snd secp256k1_wnaf_single_func))
        tr m l
        (fun t m' l' =>
          exists Rx Ry Rz Ax' Ay' Az',
          secp256k1_oncurve (Rx,Ry,Rz)
          /\ secp256k1_pt_eq (Rx,Ry,Rz) (secp256k1_scmul (Z.to_nat k) (Px,Py,Pz))
          /\ (Point3 (Some tight_bounds) pOx pOy pOz Rx Ry Rz
              ⋆ Point3 (Some tight_bounds) pAx pAy pAz Ax' Ay' Az'
              ⋆ DigitArray pDK (secp256k1_digits k) ⋆ Table4 pT table_entries
              ⋆ Rinner) m').
  Proof.
    intros functions Htab Hleaf k Hk Px Py Pz tab HPoc Htable.
    intros pOx pOy pOz pAx pAy pAz pT pDK
           Ox0 Oy0 Oz0 Ax0 Ay0 Az0 Rinner tr m l
           Hlox Hloy Hloz Hlax Hlay Hlaz Hlt Hldk Hsep.
    assert (Hknn : 0 <= k) by lia.

    (* Every hypothesis [wnaf_single_full] asks for, as a named term in
       the context, so that the discharge below is [eassumption] and
       does not depend on the order in which Section discharge presents
       [wnaf_single_full]'s arguments. *)
    pose proof secp256k1_bounds_eq as Hbe.
    (* G6: the group interface, proved in §1b from RcbProjectiveLaws.v *)
    pose proof secp256k1_pt_eq_equiv as Heqv.
    pose proof secp256k1_oncurve_id as Hoid.
    pose proof secp256k1_oncurve_curve_add as Hoadd.
    pose proof secp256k1_curve_add_Proper as HcaP.
    pose proof secp256k1_curve_add_id_l as Hidl.
    pose proof secp256k1_curve_add_assoc as Hass.
    (* callee specs, from the function table and the field leaves *)
    pose proof (secp256k1_HCurveDouble functions Htab Hleaf) as HDbl.
    pose proof (secp256k1_HCurveAddInplace functions Htab Hleaf) as HAdd.
    pose proof (felem_copy_HFelemCopy functions
                  (secp256k1_felem_copy_spec functions Htab)) as HCopy.
    pose proof (secp256k1_HOppInplace_spec functions Htab Hleaf) as HOI.
    cbv [spec_of_opp_inplace] in HOI.
    destruct HOI as [HOppNonAliased HOppAliased].
    pose proof (secp256k1_HStoreZero functions Htab Hleaf) as HSZ.
    (* data *)
    pose proof (secp256k1_digits_length k) as Hlen.
    pose proof secp256k1_Hnbound as Hnb.
    pose proof (secp256k1_digits_bounded k Hknn) as Hdb.
    pose proof secp256k1_Hfs_pos as Hfp.
    pose proof secp256k1_Hfs_small as Hfsm.
    pose proof (proj1 Htable) as Htl.
    pose proof (secp256k1_Hdigit_load (secp256k1_digits k)) as Hdl.
    pose proof (secp256k1_digits_Hws_nn k Hk) as Hws.
    pose proof (secp256k1_Hhorner_step k Hk Px Py Pz tab HPoc Htable) as Hhs.
    pose proof (secp256k1_Hhorner_oncurve k Hknn Px Py Pz tab Htable) as Hho.
    pose proof (secp256k1_digits_wsum k Hk) as Hwsum.

    (* The two callee specs are [Definition]s; unfold them so that
       [eassumption] meets the raw shape the chain declares. *)
    cbv [spec_of_curve_double_general spec_of_curve_add_inplace_general]
      in HDbl, HAdd.

    (* Expose the function body and the chain's [scmul]. *)
    cbv [secp256k1_wnaf_single_func snd].
    unfold secp256k1_scmul.

    first
      [ eapply wnaf_single_full
          with (curve_add_name := "curve_add")
               (curve_double_name := "curve_double")
               (opp_name := "opp_inplace")
               (curve_add := secp256k1_curve_add)
               (pt_eq := secp256k1_pt_eq)
               (oncurve := secp256k1_oncurve)
               (dk := secp256k1_digits k)
               (num_iters := secp256k1_num_digits)
               (table_entries := tab)
               (Px := Px) (Py := Py) (Pz := Pz)
               (k := k)
      | eapply wnaf_single_full
          with (curve_add := secp256k1_curve_add)
               (pt_eq := secp256k1_pt_eq)
               (oncurve := secp256k1_oncurve)
               (k := k)
      | eapply wnaf_single_full ].

    all: try eassumption.
    all: try ecancel_assumption.
    all: try lia.
    all: try (unfold secp256k1_pt_eq, secp256k1_oncurve, secp256k1_curve_add,
                     secp256k1_point_opp in *; eassumption).
    (* Anything left prints itself instead of surfacing as an opaque
       "incomplete proof" at [Qed]. *)
    all: lazymatch goal with
         | |- ?G => fail 99 "Secp256k1-FULL-RESIDUAL" G
         end.
  Qed.

End Secp256k1_wNAF.

(** * Adapter-lemma inventory

    NistWnafWrappers.v — proved
      felem_copy_HFelemCopy          spec_of_felem_copy (bytes dst) -> FElem-dst shape
      opp_HOpp                       spec_of_UnOp un_opp -> HOpp shape (loose->tight by Hbounds_eq)
      FElem2_elim_frame / _intro_frame   one-leaf transport across the FElem layers
    NistWnafWrappers.v — proved (all four wrapper bodies, be20f7b)
      curve_add_inplace_general_ok   spec_of_rcb_add_general + spec_of_felem_copy
                                      -> HCurveAddInplace shape at "curve_add"
      curve_double_general_ok        same inputs -> HCurveDouble shape at "curve_double"
      opp_inplace_ok                 spec_of_UnOp un_opp + spec_of_felem_copy
                                      -> both negation shapes at "opp_inplace"
      store_zero_from_word_ok        spec_of_from_word -> StoreZero.spec_of_store_zero
    This file
      §1b group laws                 PROVED from RcbProjectiveLaws.v, under the
                                      curve side conditions secp256k1_b_val /
                                      secp256k1_M_gt_27 / secp256k1_Hthree_b / secp256k1_Hdisc /
                                      secp256k1_Hexcept (all proved in §1b)
      secp256k1_HOppInplace_spec          PROVED from opp_inplace_ok (G5)
      secp256k1_Hhorner_step              proved from horner_step_single (quotiented)
      secp256k1_Hhorner_oncurve           proved from digit_point_oncurve_full
      secp256k1_wnaf_single_full          PROVED: composition into wnaf_single_full *)
